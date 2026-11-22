"""Record project module namespace escapes and dynamic class lookups in clean pytest."""
import ast
import builtins
import collections
import gzip
import json
import sys
import types
import slots as scopes

reads = collections.defaultdict(set)

def observe(value, operation, key=None):
    if isinstance(value, types.ModuleType):
        name = vars(value).get("__name__", "")
        if isinstance(name, str) and name.startswith("sqlglot"):
            reads[("module",name,key if type(key) is str else "*")].add(scopes.where())
    elif operation == "namespace" and type(value) is dict:
        name = value.get("__name__")
        if isinstance(name,str) and name.startswith("sqlglot"):
            reads[("module",name,"*")].add(scopes.where())
    elif operation != "namespace" and key is not None:
        cls = value if isinstance(value,type) else type(value)
        for base in type.__getattribute__(cls,"__mro__"):
            if base.__module__.startswith("sqlglot"):
                reads[("class",base.__module__+"."+base.__qualname__,key if type(key) is str else "*")].add(scopes.where())
    return value

def introspect(fn, obj, *args, **kw):
    observe(obj,"lookup",args[0] if fn in (getattr,hasattr,setattr,delattr) and args else "*")
    return fn(obj,*args,**kw)

class Rewrite(ast.NodeTransformer):
    def visit_Call(self,n):
        self.generic_visit(n)
        if isinstance(n.func,ast.Name) and n.func.id in ("globals","locals","vars") and not n.args and not n.keywords:
            return ast.copy_location(ast.Call(ast.Name("_br4_observe",ast.Load()),[n,ast.Constant("namespace")],[]),n)
        if n.args and (isinstance(n.func,ast.Name) and n.func.id in ("getattr","hasattr","setattr","delattr","vars","dir")
                       or isinstance(n.func,ast.Attribute) and n.func.attr in ("getmembers","getattr_static","get_type_hints")):
            return ast.copy_location(ast.Call(ast.Name("_br4_introspect",ast.Load()),[n.func,*n.args],n.keywords),n)
        return n
    def visit_Attribute(self,n):
        self.generic_visit(n)
        if isinstance(n.ctx,ast.Load) and n.attr in ("__dict__","__globals__"):
            n.value=ast.copy_location(ast.Call(ast.Name("_br4_observe",ast.Load()),[n.value,ast.Constant("lookup"),ast.Constant("*")],[]),n.value)
            return ast.copy_location(ast.Call(ast.Name("_br4_observe",ast.Load()),[n,ast.Constant("namespace")],[]),n)
        return n

class Source(scopes.Source):
    def get_code(self,name):
        path=self.get_filename(name)
        tree=ast.parse(self.get_data(path),path)
        return compile(ast.fix_missing_locations(Rewrite().visit(tree)),path,"exec",dont_inherit=True)

class Finder(scopes.Finder):
    def find_spec(self,name,path,target=None):
        s=super().find_spec(name,path,target)
        if s:s.loader=Source(name,s.origin)
        return s

submissions=collections.Counter()
worker_dir=__import__("pathlib").Path("/tmp/w4-namespaces")
def recorded_task(key,fn,args,kw):
    reads.clear()
    try:return fn(*args,**kw)
    finally:
        with gzip.open(worker_dir/key,"wt") as f:json.dump(list(reads),f,separators=(",",":"))

def pytest_collection_modifyitems(config,items):
    import os
    if not os.environ.get("W4_WORKERS"):return
    pool=set(json.load(open("/app/pool_readers.json")))
    selected=[x for x in items if x.nodeid in pool]
    config.hook.pytest_deselected(items=[x for x in items if x.nodeid not in pool])
    items[:]=selected
    assert {x.nodeid for x in selected}==pool

def pytest_configure(config):
    from concurrent.futures import ProcessPoolExecutor
    orig=ProcessPoolExecutor.submit
    scopes.pytest_configure(config)
    import os
    if os.environ.get("W4_WORKERS"):
        ids=json.load(open("/app/maps.json"))["ids"]
        worker_dir.mkdir(exist_ok=True)
        def submit(pool,fn,*args,**kwargs):
            item=scopes.where()
            i=ids.index(item)
            submissions[item]+=1
            return orig(pool,recorded_task,f"{i}.{submissions[item]}.gz",fn,args,kwargs)
        ProcessPoolExecutor.submit=submit
    builtins._br4_observe=observe
    builtins._br4_introspect=introspect
    sys.meta_path[0]=Finder()

pytest_fixture_setup=scopes.pytest_fixture_setup
pytest_collection_finish=scopes.pytest_collection_finish
pytest_runtest_protocol=scopes.pytest_runtest_protocol
pytest_runtest_logreport=scopes.pytest_runtest_logreport

def pytest_sessionfinish(session,exitstatus):
    ids=json.load(open("/app/maps.json"))["ids"]
    assert not exitstatus
    for item,count in submissions.items():
        i=ids.index(item)
        for k in range(1,count+1):
            file=worker_dir/f"{i}.{k}.gz"
            if not file.is_file():
                scopes.opaque.add(item)
                break
            for row in json.load(gzip.open(file)):reads[tuple(row)].add(item)
    unread=set(ids)-scopes.passed
    scopes.opaque.update(unread)
    idx={n:i for i,n in enumerate(ids)}
    anc=collections.defaultdict(int)
    for item,chain in scopes.contexts.items():
        if item in idx:
            for node in chain:anc[node]|=1<<idx[item]
    def encode(values):
        m=0
        mods=[]
        for s in values:
            if s in idx:m|=1<<idx[s]
            elif s.startswith("@scope/"):m|=anc[s[7:]]
            elif s.startswith("@module/"):mods.append(s[8:])
            else:m=(1<<len(ids))-1
        return hex(m),sorted(mods)
    import os
    assert len(unread)<8 or os.environ.get("W4_SPLIT")
    with gzip.open("/tmp/namespace.gz","wt") as f:
        json.dump(dict(ids=ids,passed=sorted(scopes.passed),pool=encode(scopes.opaque-unread),opaque=encode(scopes.opaque),rows=[[k,encode(v)] for k,v in reads.items()]),f,separators=(",",":"))
