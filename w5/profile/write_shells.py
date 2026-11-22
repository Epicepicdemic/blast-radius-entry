"""Track shell identity at pin stores and possible argument escapes across test boundaries."""
import ast
import builtins
import collections
import gc
import gzip
import json
import os
import sys
import types
import weakref
from pathlib import Path
import pytest
import slots as scopes

ROOT="/sqlglot/"
ATOMS=(str,int,bytes,bool,type(None),float,complex)
from enum import Enum
mutators={"append","extend","insert","remove","pop","popitem","clear","update","setdefault","add","discard",
          "sort","reverse","difference_update","intersection_update","symmetric_difference_update","set",
          "replace","add_comments","appendleft","extendleft","popleft"}
facts={}
pending=collections.defaultdict(dict)
shared={}

started=False
suspended=False
parent_pid=os.getpid()
pending_count=0
sensitive=set()

def graph():
    visited=set()
    todo=[]
    for name,mod in tuple(sys.modules.items()):
        if not isinstance(mod,types.ModuleType):continue
        namespace=vars(mod)
        if name in ("sqlglot","tests") or name.startswith(("sqlglot.","tests.")):
            todo.append(namespace)
        else:visited.add(id(namespace))
    result={}
    while todo:
        v=todo.pop();i=id(v)
        if i in visited:continue
        visited.add(i);t=type(v)
        if t in ATOMS:continue
        if isinstance(v,Enum):
            result[i]=v
            continue
        if isinstance(v,types.ModuleType):continue
        if isinstance(v,type) and not (v.__module__=="sqlglot" or v.__module__.startswith(("tests.","sqlglot."))):continue
        if t not in (tuple,frozenset):result[i]=v
        if isinstance(v,types.FunctionType):items=[v.__defaults__,v.__kwdefaults__,v.__closure__,vars(v)]
        else:items=gc.get_referents(v)
        todo.extend(items)
    return result

def record(site,obj):
    global pending_count
    if suspended or os.getpid()!=parent_pid:return obj
    typ=type(obj)
    value=facts.setdefault(site,[set(),False,False])
    cls=typ.__module__+"."+typ.__qualname__
    if len(value[0])<36:value[0].add(cls)
    else:value[0].add("*")
    if typ in ATOMS:return obj
    if isinstance(obj,(type,Enum,types.ModuleType)):
        value[1]=True
        return obj
    if not started:value[2]=True;return obj
    i=id(obj)
    if shared.get(i) is obj:
        value[1]=True
    elif not value[1] and not value[2]:
        bucket=pending[site]
        previous=bucket.get(i)
        if previous is not None and (previous[0]() if previous[1] else previous[0]) is obj:
            return obj
        if len(bucket)>=4096 or pending_count>=20000:
            value[2]=True
        else:
            try:
                handle=(weakref.ref(obj),True)
            except TypeError:
                handle=(obj,False)
            bucket[i]=handle
            pending_count+=1
    return obj

def global_attr(obj,name):
    if isinstance(obj,types.ModuleType):
        mod=vars(obj).get("__name__","")
        if mod.startswith("sqlglot."):external[mod,name].add(scopes.where())
    return getattr(obj,name)
external=collections.defaultdict(set)
class RW(ast.NodeTransformer):
    def addr(self,n):
        return f"{self.path}:{n.lineno}:{n.col_offset}:{n.end_lineno}:{n.end_col_offset}"
    def wrap(self,node):
        return ast.copy_location(ast.Call(ast.Name("_br5_shell",ast.Load()),[ast.Constant(self.addr(node)),node],[]),node)
    def visit_Call(self,n):
        self.generic_visit(n)
        f=n.func
        if isinstance(f,ast.Attribute) and f.attr in mutators:
            f.value=self.wrap(f.value)
            if f.attr in ('set','replace','add_comments','append','extend'):
                n.args=[self.wrap(a) if isinstance(a,(ast.Name,ast.Attribute,ast.IfExp,ast.Subscript)) else a for a in n.args]
        elif isinstance(f,ast.Attribute) and f.attr in ('find_all','find'):
            f.value=self.wrap(f.value)
        return n
    def visit_Attribute(self,n):
        self.generic_visit(n)
        if not isinstance(n.ctx,ast.Load):
            n.value=self.wrap(n.value)
        elif n.attr in self.imported and n.attr not in mutators:
            return ast.copy_location(ast.Call(ast.Name("_br5_global_attr",ast.Load()),[n.value,ast.Constant(n.attr)],[]),n)
        return n
    def visit_Subscript(self,n):
        self.generic_visit(n)
        if not isinstance(n.ctx,ast.Load):n.value=self.wrap(n.value)
        return n

class Source(scopes.Source):
    def get_code(self,name):
        path=self.get_filename(name);tree=ast.parse(self.get_data(path),path)
        rw=RW();rw.path=str(Path(path).relative_to("/sqlglot"));rw.imported=import_names
        return compile(ast.fix_missing_locations(rw.visit(tree)),path,"exec",dont_inherit=True)
class Finder(scopes.Finder):
    def find_spec(self,name,path,target=None):
        s=super().find_spec(name,path,target)
        if s:s.loader=Source(name,s.origin)
        return s
import_names=set()

def pytest_configure(config):
    scopes.pytest_configure(config)
    # The clean pin identifies timing and allocation tests. Run them with native
    # lifetimes and keep their contexts opaque when linking receiver evidence.
    import marshal
    resource_mask=marshal.loads(Path('/app/slots.bin').read_bytes())['resources']
    ids=json.load(open('/app/maps.json'))['ids']
    sensitive.update(t for i,t in enumerate(ids) if resource_mask & (1<<i))
    for f in Path("/sqlglot/sqlglot").rglob("*.py"):
        tree=ast.parse(f.read_bytes())
        for n in tree.body:
            if isinstance(n,ast.ImportFrom):
                import_names.update(a.asname or a.name for a in n.names)
    builtins._br5_shell=record
    builtins._br5_global_attr=global_attr
    sys.meta_path[0]=Finder()

def pytest_collection_finish(session):
    global shared,started
    scopes.pytest_collection_finish(session)
    shared=graph()
    started=True
@pytest.hookimpl(wrapper=True,tryfirst=True)
def pytest_runtest_protocol(item):
    global suspended,shared
    scopes.current=item.nodeid
    code=getattr(getattr(item,'obj',None),'__code__',None)
    suspended=item.nodeid in sensitive or bool(code and {'tracemalloc','weakref','getrefcount','get_objects','get_referents','get_referrers'} & set(code.co_names))
    if suspended:
        shared={}
        scopes.opaque.add(item.nodeid)
        builtins._br5_shell=ignore
        builtins._br5_global_attr=getattr
    try:
        return (yield)
    finally:
        builtins._br5_shell=record
        builtins._br5_global_attr=global_attr
        suspended=False
        scopes.current="@startup"

def ignore(site,obj):return obj
pytest_fixture_setup=scopes.pytest_fixture_setup
def pytest_runtest_logreport(report):
    scopes.pytest_runtest_logreport(report)
    if report.failed:
        print('pin failure',report.nodeid,str(report.longrepr)[-350:],file=sys.stderr,flush=True)

def pytest_runtest_logfinish(nodeid,location):
    global shared,pending_count
    current=graph()
    for k,objects in pending.items():
        for marker,(value,is_weak) in objects.items():
            candidate=value() if is_weak else value
            if candidate is not None and current.get(marker) is candidate:
                facts[k][1]=True
                break
    pending.clear()
    pending_count=0
    shared=current
def pytest_sessionfinish(session,exitstatus):
    if exitstatus:return
    ids=json.load(open("/app/maps.json"))["ids"];idx={n:i for i,n in enumerate(ids)}
    assert set(ids)==set(ids)&scopes.passed
    def encode(ctx):
        mask=0;mods=set()
        for t in ctx:
            if t in idx:mask|=1<<idx[t]
            elif t.startswith("@scope/"):
                mask|=sum(1<<idx[n] for n,ps in scopes.contexts.items() if n in idx and t[7:] in ps)
            elif t.startswith("@module/"):mods.add(t[8:])
            else:mask=(1<<len(ids))-1
        return [hex(mask),sorted(mods)]
    out=dict(ids=ids,passed=sorted(scopes.passed),opaque=encode(scopes.opaque),
        shells={k:[sorted(typ),esc,unk] for k,(typ,esc,unk) in sorted(facts.items())},
        external=[[list(k),encode(v)] for k,v in sorted(external.items())])
    Path("/tmp/write_shells.gz").write_bytes(gzip.compress(json.dumps(out,separators=(",",":")).encode(),mtime=0))
