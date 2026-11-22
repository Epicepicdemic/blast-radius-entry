"""Record actual keys consumed by generator and parser dispatch, including inherited tables."""
import ast
import builtins
import collections
import functools
import gzip
import json
from pathlib import Path
import sys
from enum import Enum
from concurrent.futures import ProcessPoolExecutor
import slots as scopes

FIELDS={"TRANSFORMS","PROPERTIES_LOCATION","FUNCTIONS","FUNCTION_PARSERS","NO_PAREN_FUNCTION_PARSERS","_dispatch"}
hits=collections.defaultdict(set)
def name(key):
    if isinstance(key,type):return key.__module__+"."+key.__qualname__
    if type(key) is str:return key
    if isinstance(key,Enum):return type(key).__module__+"."+type(key).__qualname__+"."+key.name
    return None
def mark(o,f,key=None):
    c=o if isinstance(o,type) else type(o)
    if c.__module__.startswith(("sqlglot.","tests.")):
        r="TRANSFORMS" if f=="_dispatch" else f
        hits[r,name(key)].add(scopes.where())
def at(o,f,method):
    obj=getattr(o,f)
    fn=getattr(obj,method) if method!="item" else obj.__getitem__
    def read(key,*args):
        mark(o,f,key)
        return fn(key,*args)
    return read
def whole(o,f):
    mark(o,f)
    return getattr(o,f)
def contains(k,o,f,neg):
    mark(o,f,k)
    v=k in getattr(o,f)
    return not v if neg else v
def functions_get(table,key,*d):
    hits["FUNCTIONS",name(key)].add(scopes.where())
    return table.get(key,*d)

class RW(ast.NodeTransformer):
    def call(self,at,fn,values):
        return ast.copy_location(ast.Call(ast.Name(fn,ast.Load()),values,[]),at)
    def visit_Call(self,n):
        f=n.func
        if isinstance(f,ast.Attribute) and f.attr in ("get","pop"):
            obj=f.value
            if isinstance(obj,ast.Attribute) and obj.attr in FIELDS:
                n.func=self.call(obj,"_br5_at",[self.visit(obj.value),ast.Constant(obj.attr),ast.Constant(f.attr)])
                n.args=[self.visit(a) for a in n.args]
                n.keywords=[self.visit(k) for k in n.keywords]
                return n
            if f.attr=="get" and self.special and isinstance(obj,ast.Name) and obj.id=="functions" and n.lineno in self.special:
                return self.call(n,"_br5_functions_get",[obj,*[self.visit(a) for a in n.args]])
        return self.generic_visit(n)
    def visit_Subscript(self,n):
        o=n.value
        if isinstance(o,ast.Attribute) and o.attr in FIELDS and isinstance(n.ctx,ast.Load):
            return ast.copy_location(ast.Call(self.call(o,"_br5_at",[self.visit(o.value),ast.Constant(o.attr),ast.Constant("item")]),[self.visit(n.slice)],[]),n)
        return self.generic_visit(n)
    def visit_Compare(self,n):
        if len(n.ops)==1 and isinstance(n.ops[0],(ast.In,ast.NotIn)):
            o=n.comparators[0]
            if isinstance(o,ast.Attribute) and o.attr in FIELDS:
                return self.call(n,"_br5_contains",[self.visit(n.left),self.visit(o.value),ast.Constant(o.attr),ast.Constant(isinstance(n.ops[0],ast.NotIn))])
        return self.generic_visit(n)
    def visit_Attribute(self,n):
        self.generic_visit(n)
        if n.attr in FIELDS and isinstance(n.ctx,ast.Load) and id(n) not in self.transparent:
            return self.call(n,"_br5_dispatch_whole",[n.value,ast.Constant(n.attr)])
        return n

def plan(tree,path):
    parents={c:n for n in ast.walk(tree) for c in ast.iter_child_nodes(n)}
    transparent=set();special=set()
    # Only copies into the same tracked table may forward provenance without
    # an immediate whole-table observer. Runtime consumers are unioned globally by key.
    for n in ast.walk(tree):
        if not isinstance(n,ast.Attribute) or n.attr not in FIELDS:continue
        p=parents.get(n);outer=parents.get(p)
        if isinstance(p,ast.Dict) and any(k is None and v is n for k,v in zip(p.keys,p.values)):
            ts=outer.targets if isinstance(outer,ast.Assign) else [outer.target] if isinstance(outer,ast.AnnAssign) else []
            if any(isinstance(t,ast.Name) and t.id==n.attr for t in ts):transparent.add(id(n))
        # A key-preserving projection/filter forwards a changed key only to
        # the same key of the derived table. Cross-key transforms keep the wildcard.
        comp=p
        while comp is not None and not isinstance(comp,(ast.DictComp,ast.stmt)):comp=parents.get(comp)
        if isinstance(comp,ast.DictComp) and len(comp.generators)==1:
            gen=comp.generators[0];d=parents.get(comp)
            if isinstance(d,ast.Dict) and any(k is None and v is comp for k,v in zip(d.keys,d.values)):d=parents.get(d)
            targets=d.targets if isinstance(d,ast.Assign) else [d.target] if isinstance(d,ast.AnnAssign) else []
            if any(isinstance(t,ast.Name) and t.id==n.attr for t in targets) and isinstance(comp.key,ast.Name):
                key=comp.key.id;target=gen.target
                items=isinstance(target,(ast.Tuple,ast.List)) and len(target.elts)==2 and isinstance(target.elts[0],ast.Name) and target.elts[0].id==key and isinstance(target.elts[1],ast.Name) and isinstance(comp.value,ast.Name) and comp.value.id==target.elts[1].id and isinstance(gen.iter,ast.Call) and not gen.iter.args and not gen.iter.keywords and isinstance(gen.iter.func,ast.Attribute) and gen.iter.func.value is n and gen.iter.func.attr=="items"
                keys=isinstance(target,ast.Name) and target.id==key and gen.iter is n and isinstance(comp.value,ast.Attribute) and (ast.unparse(comp.value)).startswith("exp.Properties.Location.")
                def local_predicate(f):
                    if isinstance(f,ast.BoolOp):return all(local_predicate(a) for a in f.values)
                    if not isinstance(f,ast.Compare) or len(f.ops)!=1 or not isinstance(f.left,ast.Name) or f.left.id!=key:return False
                    if not isinstance(f.ops[0],(ast.Eq,ast.NotEq,ast.In,ast.NotIn,ast.Is,ast.IsNot)):return False
                    return all(isinstance(v,(ast.Constant,ast.Tuple,ast.Set,ast.List,ast.Load,ast.Attribute,ast.Name)) for v in ast.walk(f.comparators[0]))
                if (items or keys) and all(local_predicate(f) for f in gen.ifs):transparent.add(id(n))
        if path=="sqlglot/generator.py" and n.attr=="TRANSFORMS" and isinstance(p,ast.Call) and ast.unparse(p)=="dict(cls.TRANSFORMS)":
            fn=p
            while fn is not None and not isinstance(fn,ast.FunctionDef):fn=parents.get(fn)
            if fn and fn.name=="_build_dispatch":transparent.add(id(n))
        if path=="sqlglot/generator.py" and n.attr=="_dispatch" and isinstance(n.ctx,ast.Store):transparent.add(id(n))
        if path=="sqlglot/parser.py" and n.attr=="FUNCTIONS" and isinstance(p,ast.Assign) and ast.unparse(p)=="functions = self.FUNCTIONS":
            fn=p
            while fn is not None and not isinstance(fn,ast.FunctionDef):fn=parents.get(fn)
            if fn:
                lookups=[x for x in ast.walk(fn) if isinstance(x,ast.Call) and isinstance(x.func,ast.Attribute) and
                         isinstance(x.func.value,ast.Name) and x.func.value.id=="functions" and x.func.attr=="get" and not x.keywords]
                if lookups:
                    transparent.add(id(n))
                    special.update(x.lineno for x in lookups)
    return transparent,special

class Source(scopes.Source):
    def get_code(self,name):
        path=self.get_filename(name);tree=ast.parse(self.get_data(path),path);rw=RW()
        rw.transparent,rw.special=plan(tree,str(Path(path).relative_to("/sqlglot")))
        return compile(ast.fix_missing_locations(rw.visit(tree)),path,"exec",dont_inherit=True)
class Finder(scopes.Finder):
    def find_spec(self,name,path,target=None):
        s=super().find_spec(name,path,target)
        if s:s.loader=Source(name,s.origin)
        return s
def install():
    builtins._br5_dispatch_whole=whole;builtins._br5_at=at
    builtins._br5_contains=contains;builtins._br5_functions_get=functions_get
folder=Path("/tmp/br5-dispatch-workers");counts=collections.Counter()
ids=json.load(open("/app/maps.json"))["ids"];idx={n:i for i,n in enumerate(ids)}
def task(key,fn,a,kw):
    hits.clear();ready=hasattr(builtins,"_br5_at") and any(type(f) is Finder for f in sys.meta_path)
    try:return fn(*a,**kw)
    finally:
        with gzip.open(folder/key,"wt") as f:json.dump(list(hits) if ready else None,f,separators=(",",":"))
def pytest_configure(config):
    scopes.pytest_configure(config);sys.meta_path[0]=Finder();install();folder.mkdir()
    orig=ProcessPoolExecutor.submit
    def submit(pool,fn,*a,**kw):
        ctx=scopes.where()
        if ctx not in idx:return orig(pool,fn,*a,**kw)
        counts[ctx]+=1
        return orig(pool,task,f"{idx[ctx]}.{counts[ctx]}.gz",fn,a,kw)
    ProcessPoolExecutor.submit=submit
pytest_collection_finish=scopes.pytest_collection_finish
pytest_runtest_protocol=scopes.pytest_runtest_protocol
pytest_fixture_setup=scopes.pytest_fixture_setup
pytest_runtest_logreport=scopes.pytest_runtest_logreport
def pytest_sessionfinish(session,exitstatus):
    assert not exitstatus and set(ids)<=scopes.passed
    opaque=set(scopes.opaque)
    for n,c in counts.items():
        for i in range(1,c+1):
            p=folder/f"{idx[n]}.{i}.gz"
            if not p.exists():break
            rows=json.load(gzip.open(p))
            if rows is None:break
            for k in rows:hits[tuple(k)].add(n)
        else:opaque.discard(n)
    anc=collections.defaultdict(int)
    for n,parents in scopes.contexts.items():
        if n in idx:
            for p in parents:anc[p]|=1<<idx[n]
    def encode(ts):
        m=0;mods=set()
        for t in ts:
            if t in idx:m|=1<<idx[t]
            elif t.startswith("@scope/"):m|=anc[t[7:]]
            elif t.startswith("@module/"):mods.add(t[8:])
            else:m=(1<<len(ids))-1
        return [hex(m),sorted(mods)]
    doc=dict(ids=ids,passed=sorted(scopes.passed),opaque=encode(opaque),tasks=sum(counts.values()),
             rows=[[list(k),encode(ts)] for k,ts in sorted(hits.items(),key=lambda r:repr(r[0]))])
    Path("/tmp/dispatch_uses.gz").write_bytes(gzip.compress(json.dumps(doc,separators=(",",":")).encode(),mtime=0))
