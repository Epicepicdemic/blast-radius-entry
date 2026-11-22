"""Record lookup keys and complete-map observers of pinned parser and tokenizer dispatch tables."""
import ast
import builtins
import collections
import gzip
import json
import os
from pathlib import Path
import sys
import slots as scopes

hits=collections.defaultdict(set)
submitted=collections.Counter()

class Table(dict):
    def note(self,key=None):
        hits[self.owner,key if type(key) is str else None].add(scopes.where())
    def get(self,key,*default):
        self.note(key)
        return super().get(key,*default)
    def __getitem__(self,key):
        self.note(key)
        return super().__getitem__(key)
    def __contains__(self,key):
        self.note("@keys")
        return super().__contains__(key)

def watch_all(key):
    method=getattr(dict,key)
    def tracked(self,*args,**kwargs):
        self.note("@keys" if key in {"keys","__iter__","__reversed__","__len__"} else None)
        return method(self,*args,**kwargs)
    return tracked
for name in ('keys','items','values','copy','__iter__','__reversed__','__repr__','__str__','__eq__','__ne__','__len__','__or__','__ror__','__ior__','__reduce__','__reduce_ex__','pop','popitem','setdefault','update','clear','__setitem__','__delitem__'):
    setattr(Table,name,watch_all(name))

def table(name,value):
    out=Table(value)
    out.owner=name
    return out

class Source(scopes.Source):
    def get_code(self,name):
        path=self.get_filename(name)
        tree=ast.parse(self.get_data(path),path)
        def visit(body,parents):
            for s in body:
                if isinstance(s,ast.ClassDef):visit(s.body,parents+[s.name])
                elif parents and isinstance(s,(ast.Assign,ast.AnnAssign)):
                    target=s.targets[0] if isinstance(s,ast.Assign) and len(s.targets)==1 else getattr(s,'target',None)
                    if isinstance(target,ast.Name) and target.id in ('FUNCTIONS','KEYWORDS') and isinstance(s.value,ast.Dict):
                        tag='.'.join([name,*parents,target.id])
                        s.value=ast.copy_location(ast.Call(ast.Name('_br_dispatch_table',ast.Load()),[ast.Constant(tag),s.value],[]),s.value)
        visit(tree.body,[])
        return compile(ast.fix_missing_locations(tree),path,'exec',dont_inherit=True)

class Finder(scopes.Finder):
    def find_spec(self,name,path,target=None):
        s=super().find_spec(name,path,target)
        if s:s.loader=Source(name,s.origin)
        return s

def pool_task(key,fn,args,kwargs):
    hits.clear()
    try:return fn(*args,**kwargs)
    finally:
        with gzip.open(Path('/tmp/dispatch-workers')/key,'wt') as f:
            json.dump(list(hits),f,separators=(',',':'))

def pytest_configure(config):
    scopes.pytest_configure(config)
    builtins._br_dispatch_table=table
    sys.meta_path[0]=Finder()
    # Child workers import the instrumented pin via the same finder at startup.
    from concurrent.futures import ProcessPoolExecutor
    orig=ProcessPoolExecutor.submit
    ids=json.load(open('/app/maps.json'))['ids']
    Path('/tmp/dispatch-workers').mkdir(exist_ok=True)
    def submit(pool,fn,*args,**kwargs):
        case=scopes.where()
        if case not in ids:
            scopes.opaque.add(case)
            return orig(pool,fn,*args,**kwargs)
        submitted[case]+=1
        key=f'{ids.index(case)}-{submitted[case]}.gz'
        return orig(pool,pool_task,key,fn,args,kwargs)
    ProcessPoolExecutor.submit=submit

pytest_fixture_setup=scopes.pytest_fixture_setup
pytest_collection_finish=scopes.pytest_collection_finish
pytest_runtest_protocol=scopes.pytest_runtest_protocol
pytest_runtest_logreport=scopes.pytest_runtest_logreport

def pytest_sessionfinish(session,exitstatus):
    ids=json.load(open('/app/maps.json'))['ids']
    assert not exitstatus and set(ids)<=scopes.passed
    for case,count in submitted.items():
        i=ids.index(case)
        complete=True
        for j in range(1,count+1):
            p=Path('/tmp/dispatch-workers')/f'{i}-{j}.gz'
            if not p.is_file():
                complete=False
                break
            for owner,key in json.load(gzip.open(p)):hits[owner,key].add(case)
        # The child may start without the pytest import hook. Its successful return alone
        # does not certify its reads. Keep the existing opaque flag for these tests.
        if not complete:scopes.opaque.add(case)
    index={t:i for i,t in enumerate(ids)};masks=collections.defaultdict(int)
    for name,anc in scopes.contexts.items():
        if name in index:
            for q in anc:masks[q]|=1<<index[name]
    def encode(ctx):
        bits=0;mods=set()
        for s in ctx:
            if s in index:bits|=1<<index[s]
            elif s.startswith('@scope/'):bits|=masks[s[7:]]
            elif s.startswith('@module/'):mods.add(s[8:])
            else:bits=(1<<len(ids))-1
        return [hex(bits),sorted(mods)]
    rows=[[q,k,encode(v)] for (q,k),v in hits.items()]
    with gzip.open('/tmp/dispatch.gz','wt') as f:
        json.dump(dict(ids=ids,passed=len(scopes.passed),opaque=encode(scopes.opaque),rows=rows,submissions=sum(submitted.values())),f,separators=(',',':'))
