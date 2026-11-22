"""Profile class flags, optional expression argument keys, and arity tests at the clean pin."""
import ast
import builtins
import collections
import functools
import gzip
import json
import sys
import types
from enum import Enum
from pathlib import Path
from concurrent.futures import ProcessPoolExecutor
import slots as scopes

fields={"arg_types"}
for file in Path("/sqlglot/sqlglot").rglob("*.py"):
    tree=ast.parse(file.read_bytes())
    for cls in (n for n in ast.walk(tree) if isinstance(n,ast.ClassDef)):
        if any("Enum" in ast.unparse(b) for b in cls.bases):continue
        for st in cls.body:
            if isinstance(st,(ast.Assign,ast.AnnAssign)):
                for t in st.targets if isinstance(st,ast.Assign) else [st.target]:
                    if isinstance(t,ast.Name) and t.id.isupper():fields.add(t.id)

hits=collections.defaultdict(set)
@functools.lru_cache(None)
def lineage(cls):
    if issubclass(cls,Enum):return ()
    return tuple(b.__module__+"."+b.__qualname__ for b in type.__getattribute__(cls,"__mro__")
                 if b.__module__.startswith("sqlglot."))
def note(obj,field,op,key):
    cls=obj if isinstance(obj,type) else type(obj)
    if not cls.__module__.startswith(("sqlglot.","tests.")):return
    where=scopes.where()
    for q in lineage(cls):hits[q,field,op,key].add(where)

def read(obj,field):
    note(obj,field,"whole",None)
    return getattr(obj,field)
def member(key,obj,field,neg):
    note(obj,field,"member",key if type(key) is str else None)
    result=key in getattr(obj,field)
    return not result if neg else result
def arity(n,obj,field):
    note(obj,field,"arity",n)
    return n>len(getattr(obj,field))

def namespace(obj, kind, key):
    cls = obj if isinstance(obj,type) else type(obj)
    if not type.__getattribute__(cls,'__module__').startswith(('sqlglot.','tests.')):
        return obj
    mode = kind
    ordinary = not isinstance(obj,type) and type.__getattribute__(cls,'__getattribute__') is object.__getattribute__
    if kind in ('namespace','dictionary_key') and ordinary:
        desc = next((vars(base)['__dict__'] for base in type.__getattribute__(cls,'__mro__') if '__dict__' in vars(base)), None)
        if isinstance(desc,(types.GetSetDescriptorType,types.MemberDescriptorType)):
            mode = 'instance_namespace'
    if mode == 'dictionary_key' and (not isinstance(obj,type) or type.__getattribute__(type(obj),'__getattribute__') is not type.__getattribute__):
        mode = 'namespace'
    note(obj, '__namespace__', mode, key if type(key) is str else None)
    return obj


def lookup(func,obj,*args,**kwargs):
    if func in (getattr,hasattr,setattr,delattr) and args:
        key = args[0]
        if key in fields or key in ('__doc__','__annotations__','__code__','__signature__','__defaults__','__kwdefaults__'):
            namespace(obj, 'dynamic',key)
    elif getattr(func,'__module__',None)=='inspect' and getattr(func,'__name__',None)=='getdoc':
        namespace(obj,'dynamic','__doc__')
    elif func is vars:
        namespace(obj,'namespace',None)
    elif func is dir:
        namespace(obj,'dir',None)
    else:
        namespace(obj,'unknown',None)
    return func(obj,*args,**kwargs)


class RW(ast.NodeTransformer):
    def visit_Subscript(self,n):
        if (isinstance(n.value,ast.Attribute) and n.value.attr=='__dict__' and
                isinstance(n.slice,ast.Constant) and type(n.slice.value) is str):
            n.value.namespace_key=n.slice.value
        return self.generic_visit(n)
    def visit_Call(self,n):
        f=n.func
        if isinstance(f,ast.Attribute) and f.attr=='get' and isinstance(f.value,ast.Attribute) and f.value.attr=='__dict__' and n.args and isinstance(n.args[0],ast.Constant) and type(n.args[0].value) is str:
            f.value.namespace_key=n.args[0].value
        self.generic_visit(n)
        if n.args and (isinstance(n.func,ast.Name) and n.func.id in ('getattr','hasattr','setattr','delattr','vars','dir') or isinstance(n.func,ast.Attribute) and n.func.attr in ('getmembers','getattr_static','get_type_hints','getdoc')):
            if self.doc_copy and n.lineno in self.doc_copy and isinstance(n.func,ast.Name) and n.func.id in ('getattr','setattr'):
                # The pinned hook copies the effective docstring onto the freshly
                # created subclass. A later read is captured at its real consumer.
                return n
            return ast.copy_location(ast.Call(ast.Name('_br5_lookup',ast.Load()),[n.func,*n.args],n.keywords),n)
        return n
    def visit_Attribute(self,n):
        self.generic_visit(n)
        if isinstance(n.ctx,ast.Load) and n.attr=='__doc__':
            n.value=ast.copy_location(ast.Call(ast.Name('_br5_namespace',ast.Load()),[n.value,ast.Constant('dynamic'),ast.Constant('__doc__')],[]),n.value)
        if isinstance(n.ctx,ast.Load) and n.attr in ('__dict__','__globals__'):
            n.value=ast.copy_location(ast.Call(ast.Name('_br5_namespace',ast.Load()),[n.value,ast.Constant('dictionary_key' if hasattr(n,'namespace_key') else 'namespace' if n.attr=='__dict__' else 'unknown'),ast.Constant(getattr(n,'namespace_key',None))],[]),n.value)
        if isinstance(n.ctx,ast.Load) and n.attr in fields and n.lineno not in self.derived:
            return ast.copy_location(ast.Call(ast.Name("_br5_field",ast.Load()),[n.value,ast.Constant(n.attr)],[]),n)
        return n
    def visit_Compare(self,n):
        if (len(n.ops)==1 and isinstance(n.ops[0],(ast.In,ast.NotIn)) and
                isinstance(n.left,ast.Constant) and type(n.left.value) is str and
                isinstance(n.comparators[0],ast.Attribute) and n.comparators[0].attr=='__dict__'):
            n.comparators[0].namespace_key=n.left.value
        if len(n.ops)==1:
            rhs=n.comparators[0]
            if isinstance(n.ops[0],(ast.In,ast.NotIn)) and isinstance(rhs,ast.Attribute) and rhs.attr=="arg_types":
                return ast.copy_location(ast.Call(ast.Name("_br5_member",ast.Load()),[self.visit(n.left),self.visit(rhs.value),ast.Constant(rhs.attr),ast.Constant(isinstance(n.ops[0],ast.NotIn))],[]),n)
            if (self.core and isinstance(n.ops[0],ast.Gt) and isinstance(n.left,ast.Call) and
                isinstance(n.left.func,ast.Name) and n.left.func.id=="len" and isinstance(rhs,ast.Call) and
                isinstance(rhs.func,ast.Name) and rhs.func.id=="len" and len(rhs.args)==1 and not rhs.keywords and
                isinstance(rhs.args[0],ast.Attribute) and rhs.args[0].attr=="arg_types"):
                attr=rhs.args[0]
                return ast.copy_location(ast.Call(ast.Name("_br5_arity",ast.Load()),[self.visit(n.left),self.visit(attr.value),ast.Constant(attr.attr)],[]),n)
        return self.generic_visit(n)
class Source(scopes.Source):
    def get_code(self,name):
        p=self.get_filename(name);tree=ast.parse(self.get_data(p),p);rw=RW()
        rw.doc_copy = {n.lineno for n in ast.walk(tree) if isinstance(n,ast.Call) and
                       ast.unparse(n) == "setattr(cls, '__doc__', getattr(cls, '__doc__', None) or '')"} if p.endswith('/sqlglot/expressions/core.py') else set()
        rw.core=p=="/sqlglot/sqlglot/expressions/core.py";rw.derived=set()
        if rw.core:
            expr=ast.dump(ast.parse("cls.required_args = {k for k,v in cls.arg_types.items() if v}").body[0])
            rw.derived={n.lineno for c in tree.body if isinstance(c,ast.ClassDef) and c.name=="Expr"
                        for f in c.body if isinstance(f,ast.FunctionDef) and f.name=="__init_subclass__"
                        for n in f.body if ast.dump(n)==expr}
            assert len(rw.derived)==1
        return compile(ast.fix_missing_locations(rw.visit(tree)),p,"exec",dont_inherit=True)
class Finder(scopes.Finder):
    def find_spec(self,name,path,target=None):
        s=super().find_spec(name,path,target)
        if s:s.loader=Source(name,s.origin)
        return s
folder=Path("/tmp/br5-field-workers");count=collections.Counter()
ids=json.load(open("/app/maps.json"))["ids"];idx={t:i for i,t in enumerate(ids)}
def task(key,fn,args,kw):
    hits.clear()
    okay=hasattr(builtins,"_br5_field") and any(type(f) is Finder for f in sys.meta_path)
    try:return fn(*args,**kw)
    finally:
        with gzip.open(folder/key,"wt") as f:json.dump(list(hits) if okay else None,f,separators=(",",":"))
def pytest_configure(config):
    builtins._br5_lookup = lookup
    builtins._br5_namespace = namespace
    scopes.pytest_configure(config)
    sys.meta_path[0]=Finder()
    builtins._br5_field=read;builtins._br5_member=member;builtins._br5_arity=arity
    folder.mkdir()
    orig=ProcessPoolExecutor.submit
    def submit(pool,fn,*a,**kw):
        ctx=scopes.where()
        if ctx not in idx:return orig(pool,fn,*a,**kw)
        count[ctx]+=1
        return orig(pool,task,f"{idx[ctx]}.{count[ctx]}.gz",fn,a,kw)
    ProcessPoolExecutor.submit=submit
pytest_collection_finish=scopes.pytest_collection_finish
pytest_runtest_protocol=scopes.pytest_runtest_protocol
pytest_fixture_setup=scopes.pytest_fixture_setup
pytest_runtest_logreport=scopes.pytest_runtest_logreport
def pytest_sessionfinish(session,exitstatus):
    assert exitstatus==0 and set(ids)<=scopes.passed
    opaque=set(scopes.opaque)
    for n,c in count.items():
        for i in range(1,c+1):
            f=folder/f"{idx[n]}.{i}.gz"
            if not f.is_file():break
            rows=json.load(gzip.open(f))
            if rows is None:break
            for key in rows:hits[tuple(key)].add(n)
        else:
            opaque.discard(n)
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
    rows=[[list(k),encode(v)] for k,v in sorted(hits.items(),key=lambda kv:repr(kv[0]))]
    record=dict(ids=ids,passed=sorted(scopes.passed),fields=sorted(fields),tasks=sum(count.values()),opaque=encode(opaque),rows=rows)
    Path("/tmp/field_uses.gz").write_bytes(gzip.compress(json.dumps(record,separators=(",",":")).encode(),mtime=0))
