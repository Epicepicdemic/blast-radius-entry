"""Record exact builtin operands of comparisons to literals. All samples use the clean pin."""
import ast
import builtins
import collections
import gzip
import importlib.abc
import importlib.machinery
import json
from pathlib import Path
import sys
import pytest
import slots as scopes

values=collections.defaultdict(dict)
completed=set()
TYPES={bool,int,str,bytes,float,type(None)}

def observe(site,value):
    table=values[site]
    if type(value) in (int,bool,str,type(None)) and (type(value) is not str or len(value)<80) and (type(value) is not int or value.bit_length()<96):
        fact=(type(value).__name__,value)
        if len(table)>=48 and fact not in table:fact=("?",None)
    else:
        fact=("?",None)
    table.setdefault(fact,set()).add(scopes.where())
    return value

class Rewrite(ast.NodeTransformer):
    def visit_Compare(self,n):
        self.generic_visit(n)
        if len(n.ops)==1 and isinstance(n.comparators[0],ast.Constant) and type(n.comparators[0].value) in (int,bool,str,type(None)):
            key=f"{self.path}:{n.lineno}:{n.col_offset}"
            n.left=ast.copy_location(ast.Call(ast.Name("_w4_scalar",ast.Load()),[ast.Constant(key),n.left],[]),n.left)
        return n

class Loader(scopes.Source):
    def get_code(self,name):
        path=self.get_filename(name)
        tree=ast.parse(self.get_data(path),path)
        rw=Rewrite()
        rw.path=str(Path(path).relative_to(scopes.ROOT))
        return compile(ast.fix_missing_locations(rw.visit(tree)),path,"exec",dont_inherit=True)

class Finder(scopes.Finder):
    def find_spec(self,name,path,target=None):
        sp=super().find_spec(name,path,target)
        if sp:sp.loader=Loader(name,sp.origin)
        return sp

def pytest_configure(config):
    builtins._w4_scalar=observe
    scopes.pytest_configure(config)
    sys.meta_path[0]=Finder()

pytest_runtest_protocol=scopes.pytest_runtest_protocol
pytest_fixture_setup=scopes.pytest_fixture_setup
pytest_collection_finish=scopes.pytest_collection_finish
pytest_runtest_logreport=scopes.pytest_runtest_logreport

def pytest_sessionfinish(session,exitstatus):
    ids=json.load(open("/app/maps.json"))["ids"]
    assert not exitstatus
    missing=set(ids)-scopes.passed
    assert len(missing)<=8
    scopes.opaque.update(missing)
    index={s:i for i,s in enumerate(ids)}
    anc=collections.defaultdict(int)
    for n,chain in scopes.contexts.items():
        if n in index:
            for s in chain:anc[s]|=1<<index[n]
    def encode(seen):
        mask=0
        mods=[]
        for s in seen:
            if s in index:mask|=1<<index[s]
            elif s.startswith("@scope/"):mask|=anc[s[7:]]
            elif s.startswith("@module/"):mods.append(s[8:])
            else:mask=(1<<len(ids))-1
        return hex(mask),sorted(mods)
    doc=dict(ids=ids,opaque=encode(scopes.opaque),rows={k:[[t,v,encode(s)] for (t,v),s in tab.items()]
                for k,tab in values.items() if k.startswith("sqlglot/")})
    with gzip.open("/tmp/scalars.gz","wt") as f:json.dump(doc,f,separators=(",",":"))
