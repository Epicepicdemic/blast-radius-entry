"""Profile the unchanged pin. Attribute reads retain their collecting module or fixture scope."""
import ast
import builtins
import collections
import functools
import importlib.abc
import importlib.machinery
import json
import os
from pathlib import Path
import sys

import pytest

ROOT=Path("/sqlglot")
FIELDS={"arg_types","required_args","FUNCTIONS","FUNCTION_PARSERS","TRANSFORMS","TYPE_MAPPING","KEYWORDS","PROPERTIES"}
current="@startup"
loading=[]
hits=collections.defaultdict(set)
contexts={}
passed=set()
opaque=set()
original_getattr=getattr
pid=os.getpid()


def where():
    return ("@module/"+loading[-1]) if loading and current=="@startup" else current


@functools.lru_cache(None)
def inheritance(cls, field):
    if field=="required_args":
        field="arg_types"
    # A derived table may copy its base. Include every declaring ancestor.
    return tuple(base.__module__+"."+base.__qualname__+"."+field
                 for base in type.__getattribute__(cls,"__mro__")
                 if base.__module__.startswith("sqlglot.") and field in type.__getattribute__(base,"__dict__"))


def note(obj,field,key):
    cls=obj if isinstance(obj,type) else type(obj)
    try:
        names=inheritance(cls,field)
    except (TypeError,AttributeError):
        opaque.add(where())
        return
    for q in names:
        hits[q,key].add(where())


def attr(obj,field):
    note(obj,field,None)
    return original_getattr(obj,field)


def getmethod(obj,field):
    # Attribute resolution precedes argument evaluation in Python.
    method=original_getattr(obj,field).get
    def lookup(key,*args):
        note(obj,field,key if type(key) is str else None)
        return method(key,*args)
    return lookup


def inspect_call(fn,*args,**kw):
    if fn is builtins.vars and len(args)==1 or fn in (builtins.getattr,builtins.hasattr) and len(args)>1 and args[1]=="__dict__":
        for f in FIELDS:note(args[0],f,None)
    elif fn in (builtins.getattr,builtins.hasattr,builtins.setattr,builtins.delattr) and len(args)>1 and type(args[1]) is str and args[1] in FIELDS:
        note(args[0],args[1],None)
    return fn(*args,**kw)


class Reads(ast.NodeTransformer):
    def visit_ClassDef(self,node):
        return self.generic_visit(node)
    def visit_Attribute(self,node):
        # This single pinned metaclass comprehension materializes required_args.
        # Its readers are already joined to the source class by inheritance().
        if self.rel=="sqlglot/expressions/core.py" and node.lineno in self.derived and node.attr=="arg_types":
            return node
        if isinstance(node.ctx,ast.Load) and node.attr=="get" and isinstance(node.value,ast.Attribute) and node.value.attr in FIELDS:
            t=node.value
            return ast.copy_location(ast.Call(ast.Name("_w4_get",ast.Load()),[self.visit(t.value),ast.Constant(t.attr)],[]),node)
        self.generic_visit(node)
        if isinstance(node.ctx,ast.Load) and node.attr in FIELDS:
            return ast.copy_location(ast.Call(ast.Name("_w4_attr",ast.Load()),[node.value,ast.Constant(node.attr)],[]),node)
        if isinstance(node.ctx,ast.Load) and node.attr=="__dict__":
            return ast.copy_location(ast.Call(ast.Name("_w4_inspect",ast.Load()),[ast.Name("getattr",ast.Load()),node.value,ast.Constant("__dict__")],[]),node)
        return node
    def visit_Call(self,node):
        self.generic_visit(node)
        if isinstance(node.func,ast.Name) and node.func.id in ("getattr","hasattr","vars","setattr","delattr") and node.args:
            return ast.copy_location(ast.Call(ast.Name("_w4_inspect",ast.Load()),[node.func,*node.args],node.keywords),node)
        return node


class Source(importlib.machinery.SourceFileLoader):
    def get_code(self,name):
        path=self.get_filename(name)
        t=ast.parse(self.get_data(path),path)
        rw=Reads()
        rw.rel=str(Path(path).relative_to(ROOT))
        rw.derived=set()
        if rw.rel=="sqlglot/expressions/core.py":
            expected=ast.dump(ast.parse("cls.required_args = {k for k,v in cls.arg_types.items() if v}").body[0])
            rw.derived={n.lineno for c in t.body if isinstance(c,ast.ClassDef) and c.name=="Expr"
                        for m in c.body if isinstance(m,ast.FunctionDef) and m.name=="__init_subclass__"
                        for n in m.body if ast.dump(n)==expected}
            assert len(rw.derived)==1
        return compile(ast.fix_missing_locations(rw.visit(t)),path,"exec",dont_inherit=True)
    def exec_module(self,module):
        loading.append(str(Path(self.get_filename(module.__name__)).relative_to(ROOT)))
        try:
            super().exec_module(module)
        finally:
            loading.pop()


class Finder(importlib.abc.MetaPathFinder):
    def find_spec(self,name,path,target=None):
        if name.partition(".")[0] not in ("sqlglot","tests"):
            return None
        spec=importlib.machinery.PathFinder.find_spec(name,path)
        if spec and spec.origin and spec.origin.endswith(".py") and Path(spec.origin).is_relative_to(ROOT):
            spec.loader=Source(name,spec.origin)
            return spec
        return None


def pytest_configure(config):
    assert not any(k=="sqlglot" or k.startswith("sqlglot.") for k in sys.modules)
    builtins._w4_attr=attr
    builtins._w4_inspect=inspect_call
    builtins._w4_get=getmethod
    sys.meta_path.insert(0,Finder())
    from concurrent.futures import ProcessPoolExecutor
    submit=ProcessPoolExecutor.submit
    def child(self,*a,**kw):
        opaque.add(where())
        return submit(self,*a,**kw)
    ProcessPoolExecutor.submit=child


@pytest.hookimpl(wrapper=True,tryfirst=True)
def pytest_runtest_protocol(item):
    global current
    current=item.nodeid
    try:
        return (yield)
    finally:
        current="@startup"


@pytest.hookimpl(wrapper=True,tryfirst=True)
def pytest_fixture_setup(fixturedef, request):
    global current
    prev=current
    current="@scope/"+request.node.nodeid
    try:
        return (yield)
    finally:
        current=prev


def pytest_collection_finish(session):
    contexts.update((i.nodeid,[n.nodeid for n in i.listchain()]) for i in session.items)


def pytest_runtest_logreport(report):
    if report.when=="call" and report.passed and getattr(report,"context",None) is None:
        passed.add(report.nodeid)


def pytest_sessionfinish(session,exitstatus):
    if os.getpid()!=pid:return
    import gzip
    ids=json.load(open("/app/maps.json"))["ids"]
    assert not exitstatus and set(ids)<=passed
    paths={str(k):i for i,k in enumerate(ids)}
    scopes=collections.defaultdict(int)
    for name,ancestors in contexts.items():
        if name in paths:
            for key in ancestors:
                scopes[key]|=1<<paths[name]
    def encode(contexts):
        mask=0
        modules=set()
        for s in contexts:
            if s in paths:mask|=1<<paths[s]
            elif s.startswith("@scope/"):mask|=scopes[s[7:]]
            elif s.startswith("@module/"):modules.add(s[8:])
            else:mask=(1<<len(ids))-1
        return hex(mask),sorted(modules)
    result=dict(ids=ids,passed=len(passed),opaque=encode(opaque),rows=[[q,k,encode(v)] for (q,k),v in sorted(hits.items(),key=lambda x:(x[0][0],x[0][1] or ""))])
    with gzip.open("/tmp/slots.gz","wt") as f:json.dump(result,f,separators=(",",":"))
