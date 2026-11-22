"""Observe short-circuit prefixes and concrete receiver types on the unmodified program."""
import ast
import builtins
import collections
import gzip
import json
from pathlib import Path
import sys
from concurrent.futures import ProcessPoolExecutor
import slots as scopes

rows=collections.defaultdict(set)
where=scopes.where
basic=(bool,int,float,str,bytes,type(None),list,tuple,dict,set,frozenset)

def operand(site,obj):
    typ=type(obj)
    answer=('yes' if bool(obj) else 'no') if typ in basic else 'object'
    rows[site,answer].add(where())
    return obj

def receiver(site,obj):
    typ=type(obj)
    rows[site,typ.__module__+'.'+typ.__qualname__].add(where())
    return obj

class RW(ast.NodeTransformer):
    def mark(self,n,fn,key):
        return ast.copy_location(ast.Call(ast.Name(fn,ast.Load()),[ast.Constant(key),n],[]),n)
    def visit_BoolOp(self,n):
        self.generic_visit(n)
        for i,v in enumerate(n.values):
            n.values[i]=self.mark(v,'_br5_operand',f'{self.path}:{n.lineno}:{n.col_offset}:bool{i}')
        return n
    def visit_If(self,n):
        self.generic_visit(n)
        if isinstance(n.test,(ast.Name,ast.BoolOp,ast.Compare,ast.UnaryOp)):
            n.test=self.mark(n.test,'_br5_operand',f'{self.path}:{n.lineno}:{n.col_offset}:if')
        return n
    def visit_Call(self,n):
        f=n.func
        # Observe named receiver slots, including failed method lookups; the
        # interpreter still performs the original lookup and call in its original order.
        target=isinstance(f,ast.Attribute) and (f.attr in ('find_all','find','is_type','replace','set','add_comments','insert','extend','pop','append','get','_parse_id_var') and
               (any(isinstance(v,(ast.Attribute,ast.Starred,ast.Set,ast.List,ast.Subscript)) for a in n.args+[k.value for k in n.keywords] for v in ast.walk(a)) or f.attr in ('find_all','replace','set','insert')))
        self.generic_visit(n)
        if target:f.value=self.mark(f.value,'_br5_receiver',f'{self.path}:{n.lineno}:{n.col_offset}:call')
        return n

class Source(scopes.Source):
    def get_code(self,name):
        path=self.get_filename(name);tree=ast.parse(self.get_data(path),path);rw=RW();rw.path=str(Path(path).relative_to('/sqlglot'))
        if rw.path.startswith('sqlglot/'):rw.visit(tree)
        return compile(ast.fix_missing_locations(tree),path,'exec',dont_inherit=True)
class Finder(scopes.Finder):
    def find_spec(self,name,path,target=None):
        s=super().find_spec(name,path,target)
        if s:s.loader=Source(name,s.origin)
        return s
def install():
    builtins._br5_operand=operand;builtins._br5_receiver=receiver
folder=Path('/tmp/br5-prefix-workers');counts=collections.Counter()
ids=json.load(open('/app/maps.json'))['ids'];idx={n:i for i,n in enumerate(ids)}

def task(key,fn,a,kw):
    rows.clear();ready=hasattr(builtins,'_br5_operand') and any(type(f) is Finder for f in sys.meta_path)
    try:return fn(*a,**kw)
    finally:
        with gzip.open(folder/key,'wt') as f:json.dump(list(rows) if ready else None,f,separators=(',',':'))

def pytest_configure(config):
    scopes.pytest_configure(config);sys.meta_path[0]=Finder();install();folder.mkdir();orig=ProcessPoolExecutor.submit
    def submit(pool,fn,*a,**kw):
        ctx=where()
        if ctx not in idx:return orig(pool,fn,*a,**kw)
        counts[ctx]+=1
        return orig(pool,task,f'{idx[ctx]}.{counts[ctx]}.gz',fn,a,kw)
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
            p=folder/f'{idx[n]}.{i}.gz'
            if not p.exists():break
            records=json.load(gzip.open(p))
            if records is None:break
            for site,k in records:rows[site,k].add(n)
        else:opaque.discard(n)
    anc=collections.defaultdict(int)
    for n,parents in scopes.contexts.items():
        if n in idx:
            for p in parents:anc[p]|=1<<idx[n]
    def encode(ts):
        m=0;mods=set()
        for t in ts:
            if t in idx:m|=1<<idx[t]
            elif t.startswith('@scope/'):m|=anc[t[7:]]
            elif t.startswith('@module/'):mods.add(t[8:])
            else:m=(1<<len(ids))-1
        return [hex(m),sorted(mods)]
    doc=dict(ids=ids,passed=sorted(scopes.passed),opaque=encode(opaque),tasks=sum(counts.values()),rows=[[list(k),encode(ts)] for k,ts in sorted(rows.items())]);Path('/tmp/prefixes.gz').write_bytes(gzip.compress(json.dumps(doc,separators=(',',':')).encode(),mtime=0))
