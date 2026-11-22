"""Compare the lazy initialization seen by pristine and patched writer forks."""
import hashlib
import marshal
import os
import sys
import types
import unittest
from time import monotonic

import state_watch
from import_state import Encoder

MISSING=object()


from functools import lru_cache

@lru_cache(1)
def pool_clients():
    import json
    from pathlib import Path
    return frozenset(json.loads(Path(__file__).with_name('pool_readers.json').read_bytes()))

def writer_runnable(test):
    from verify import runnable
    if runnable(test):
        return True
    # An optimizer file can contain independent unittest methods as well as
    # process-pool workloads. Both paired forks also audit attempted process starts.
    return test.startswith('tests/test_optimizer.py::') and test not in pool_clients() and runnable(test,inline_pool=True)


def namespaces():
    # Several dialect metaclasses create distinct nested classes with the same
    # __module__ and __qualname__. Keep their concrete owning bindings separate.
    roots={n:m for n,m in tuple(sys.modules.items()) if (n=="sqlglot" or n.startswith("sqlglot.")) and isinstance(m,types.ModuleType)}
    seen=set()
    def visit(cls,owner):
        if id(cls) in seen:return
        seen.add(id(cls));ns=vars(cls)
        yield ("cls_val",cls.__module__+"."+cls.__qualname__,owner),ns
        for name,val in sorted(ns.items()):
            if isinstance(val,type) and getattr(val,"__module__","").startswith("sqlglot"):
                yield from visit(val,owner+"."+name)
    for mod,root in sorted(roots.items()):
        yield ("mod_val",mod,mod),vars(root)
    bindings=[(val.__module__!=mod or val.__name__!=n,mod,n,val) for mod,root in roots.items() for n,val in tuple(vars(root).items()) if isinstance(val,type) and getattr(val,"__module__","").startswith("sqlglot")]
    for _,mod,name,val in sorted(bindings,key=lambda t:t[:3]):
        yield from visit(val,mod+"."+name)


def capture():
    from state_graph5 import Snapshot
    return Snapshot(namespaces(), state_watch.deep)


def token(enc,value):
    enc.opaque=False
    result=enc.token(value)
    return None if enc.opaque or result[0]=="opaque" else result


def cross_shape(key,value):
    return key[:2]==("mod_val","sqlglot.generator") and key[-1]=="_DISPATCH_CACHE" and type(value) is dict


def observation(suite,index,changes,indices,hot,writers,initial=None):
    from verify import Result,module_name
    needed=tuple(dict.fromkeys(module_name(suite.nodes[i][0]) for i in indices))
    fixtures,bypassed=suite._prepare_child(changes,hot,needed_modules=needed)
    cases={}
    for i in indices:
        path,cls,name=suite.nodes[i]
        kind=getattr(sys.modules[module_name(path)],cls)
        if not issubclass(kind,unittest.TestCase) or not callable(getattr(kind,name,None)):return None
        cases[kind(name)]=i
    previous=initial if initial is not None else capture()
    oldvals=previous.values
    initowners={k[:3] for k in previous.roots}
    trace=hashlib.sha256()
    readers=0
    def keep(key):
        nonlocal readers
        mask=index.binding_readers({(key[0],key[1],key[-1])})
        readers|=mask if mask is not None else index.all
    from sqlglot.dialects.dialect import Dialect
    from rules5 import facts
    registry_names=facts()["registry"]
    registry_snapshot=dict(Dialect._classes)
    def registry(key,v):
        if not (key[:2]==("cls_val","sqlglot.dialects.dialect._Dialect") and key[-1]=="_classes" and type(v) is dict and oldvals.get(key) is v):return False
        if any(v.get(k) is not c for k,c in registry_snapshot.items()):return False
        return all(type(k) is str and isinstance(c,type) and issubclass(c,Dialect) and registry_names.get(k)==(c.__module__,c.__qualname__) and vars(sys.modules[c.__module__]).get(c.__name__) is c for k,c in v.items() if k not in registry_snapshot)
    def check(i=None):
        nonlocal previous,oldvals
        if i is not None and not writers & (1<<i):return
        now=capture()
        values=now.values
        changeset=sorted(previous.changed(now))
        encoder=Encoder()
        pristine={}
        aliases={}
        # Changes to existing project state always keep their binding readers.
        # Only a newly initialized namespace and the derived generator dispatch
        # table can be compared relationally. A changed receiver in an already
        # existing class is a real mutation on either side.
        for key in changeset:
            v=values.get(key,MISSING)
            lazy=key[:3] not in initowners and key not in previous.roots and v is not MISSING
            cache=cross_shape(key,v) and key in previous.roots and oldvals[key] is v
            if not lazy and not cache and not registry(key,v):
                keep(key);continue
            if cache:
                from sqlglot.generator import Generator,_build_dispatch
                if not all(isinstance(c,type) and issubclass(c,Generator) and type(d) is dict and
                           d==_build_dispatch(c) for c,d in v.items()):
                    keep(key);continue
            if cache:
                # Function code is the intended hot replacement. _build_dispatch
                # above verifies every actual handler against the concrete class.
                value=("derived generator dispatch",tuple((c.__module__,c.__qualname__,tuple((x.__module__,x.__qualname__,f.__module__,f.__qualname__) for x,f in d.items())) for c,d in v.items()))
            elif registry(key,v):
                value=("derived registry",tuple((k,c.__module__,c.__qualname__) for k,c in v.items() if k not in registry_snapshot))
            else:
                value=token(encoder,v)
            if value is None:
                keep(key);continue
            pristine[key]=value
            if type(v) in state_watch.CONTAINERS:
                aliases.setdefault(id(v),[]).append(key)
        # An alias to an existing binding is meaningful even when both contents
        # compare equal. Include every root referring to an admitted container.
        for key,v in values.items():
            if id(v) in aliases and key not in pristine:
                aliases[id(v)].append(key)
        topology=sorted(tuple(sorted(keys)) for keys in aliases.values())
        trace.update(marshal.dumps((sorted(pristine.items()),topology),2))
        previous,oldvals=now,values
    class WriterResult(Result):
        def from_body(self, case, error):
            if (not error or case not in self.indices or
                    type(error[1]) not in (NameError,UnboundLocalError,AttributeError,KeyError,IndexError,TypeError,ValueError) or
                    not self.fixtures.files.keys() <= self.fixtures.seen):
                return False
            method=getattr(case,case._testMethodName,None)
            code=getattr(method,'__code__',None)
            production=False
            body=False
            trace=error[2]
            while trace is not None:
                frame=trace.tb_frame
                production|=frame.f_code.co_filename.startswith(str(suite.root/'sqlglot')+'/')
                body|=frame.f_code is code
                trace=trace.tb_next
            # A subTest inside a validator catches the exception before it can
            # reach the test method's traceback. The method is still on the same
            # thread's stack while unittest synchronously reports that subtest.
            frame=sys._getframe(1)
            while frame is not None and not body:
                body=frame.f_code is code and frame.f_locals.get('self') is case
                frame=frame.f_back
            return production and body

        def addSubTest(self,case,subtest,error):
            if self.from_body(case,error):
                self.observed|=1<<self.indices[case]
            super().addSubTest(case,subtest,error)

        def addError(self,case,error):
            before=self.incomplete
            accepted=self.from_body(case,error)
            super().addError(case,error)
            if accepted:
                bit=1<<self.indices[case]
                self.observed|=bit
                self.incomplete=(self.incomplete & ~bit)|(before & bit)

    result=WriterResult(cases,fixtures,check)
    unittest.TestSuite(cases).run(result)
    check()
    if bypassed() or result.invalid or fixtures.unfaithful or writers & ~(result.observed&~result.incomplete):
        return None
    return result.passed,readers,trace.hexdigest()


def run(suite,index,changes,indices,hot,writers,deadline,cap):
    from verify import cgroup_cpu,fork_reply_line
    def side(change,body,budget):
        def write(fd):
            record=observation(suite,index,change,indices,body,writers,initial)
            if record is not None:
                p,r,s=record
                os.write(fd,(format(p,"x")+" "+format(r,"x")+" "+s+"\n").encode())
        row=fork_reply_line(write,deadline,budget)
        if not row:return None
        parts=row.split()
        if len(parts)!=3 or len(parts[2])!=64:return None
        p,r=int(parts[0],16),int(parts[1],16)
        if p & ~index.all or r & ~index.all:return None
        return p,r,parts[2]
    if not suite.ready or not hot or not indices or not writers:return 0,index.all
    start=cgroup_cpu()
    # Both children inherit exactly this graph. Taking it in the warm parent
    # includes preparation and test construction in the first checkpoint.
    depth=bool(state_watch.deep)
    initial_by_depth=getattr(suite,'initial_pair_state',None)
    if initial_by_depth is None:initial_by_depth=suite.initial_pair_state={}
    if depth not in initial_by_depth:
        checkpoint=capture()
        # The frozen graph stores identities and scalar contents. Keep strong
        # references only for the two dictionaries whose identity is verified
        # relationally, so replacing a normal root cannot extend its lifetime.
        checkpoint.values={k:v for k,v in checkpoint.values.items()
                           if cross_shape(k,v) or k[:2]==('cls_val','sqlglot.dialects.dialect._Dialect') and k[-1]=='_classes'}
        initial_by_depth[depth]=checkpoint
    initial=initial_by_depth[depth]
    key=(tuple(indices),writers,depth)
    cache=getattr(suite,"pair_baselines",None)
    if cache is None:cache=suite.pair_baselines={}
    base=cache.get(key)
    if base is None:
        base=side([],(),cap)
        if base is None or writers&~base[0]:return 0,index.all
        cache[key]=base
    if base[1]==index.all:return 0,index.all
    now=cgroup_cpu()
    if now is None or start is None:return 0,index.all
    remain=cap-(now-start)
    if remain<=0.08:return 0,index.all
    test=side(changes,hot,remain)
    if test is None or test[2]!=base[2]:return 0,index.all
    # The writer itself stays selected, even when its isolated execution passed.
    owed=base[1]|test[1]
    if len(changes)==1:
        import ast
        from patching import parsed_source
        from bounds import facts
        ch=changes[0]
        def inner_edits(tree,pts):
            return {ast.dump(n) for n in ast.walk(tree) if isinstance(n,ast.Call) and n.lineno in pts and isinstance(n.func,ast.Attribute) and n.func.attr in ("insert","append","extend","update","pop","clear") and isinstance(n.func.value,ast.Subscript)}
        if inner_edits(parsed_source(ch.after),ch.added)-inner_edits(parsed_source(ch.before),ch.removed):owed|=facts()["resources"]
    return 0,owed
