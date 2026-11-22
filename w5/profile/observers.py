"""Record non-loader file reads and Python function metadata observers on the clean pin."""
import ast
import builtins
import collections
import functools
import gzip
import inspect
import json
import os
import sys
import types
from pathlib import Path
import slots as scope

opened=collections.defaultdict(set)
seen=collections.defaultdict(set)
get=builtins.getattr
FIELDS={"__defaults__", "__kwdefaults__", "__wrapped__", "__doc__", "__code__", "__annotations__", "__signature__"}
root="/sqlglot/"
def tag(obj,kind):
    if isinstance(obj,types.MethodType):obj=obj.__func__
    if isinstance(obj,staticmethod) or isinstance(obj,classmethod):obj=obj.__func__
    for _ in range(12):
        if type(obj) is not types.FunctionType:return
        code=obj.__code__
        if code.co_filename.startswith(root):
            seen[code.co_filename[len(root):],code.co_firstlineno,kind].add(scope.where())
        obj=vars(obj).get("__wrapped__")
        if obj is None:return

def attr(obj,name):
    tag(obj,name)
    return get(obj,name)

def trace_open(event,args):
    if event!="open" or not isinstance(args[0],(str,bytes)):return
    path=os.path.abspath(os.fsdecode(args[0]))
    if not path.startswith(root+"tests/") or not path.endswith(".py"):return
    frame=sys._getframe(1)
    # These operations parse/compile the very module being collected. Any
    # other open, including a custom loader, is an ordinary observable read.
    while frame and frame.f_globals.get("__name__") in ("pathlib","pathlib._local","pathlib._abc","_io","io","tokenize"):
        frame=frame.f_back
    if frame and (frame.f_code.co_filename=="<frozen importlib._bootstrap_external>" and frame.f_code.co_name=="get_data" or
                  frame.f_globals.get("__name__")=="_pytest.assertion.rewrite" and frame.f_code.co_name=="_rewrite_test"):
        return
    opened[path[len(root):]].add(scope.where())

class RW(ast.NodeTransformer):
    def visit_Attribute(self,node):
        self.generic_visit(node)
        if isinstance(node.ctx,ast.Load) and node.attr in FIELDS:
            return ast.copy_location(ast.Call(ast.Name("_br5_attr",ast.Load()),[node.value,ast.Constant(node.attr)],[]),node)
        return node

class Source(scope.Source):
    def get_code(self,name):
        path=self.get_filename(name)
        tree=RW().visit(ast.parse(self.get_data(path),path))
        return compile(ast.fix_missing_locations(tree),path,"exec",dont_inherit=True)
class Finder(scope.Finder):
    def find_spec(self,name,path,target=None):
        s=super().find_spec(name,path,target)
        if s:s.loader=Source(name,s.origin)
        return s

def pytest_configure(config):
    scope.pytest_configure(config)
    sys.meta_path[0]=Finder()
    builtins._br5_attr=attr
    def observe(fn,field):
        @functools.wraps(fn)
        def wrapped(obj,*a,**kw):
            tag(obj,field)
            return fn(obj,*a,**kw)
        return wrapped
    for name,field in (("signature","__defaults__"),("getfullargspec","__defaults__"),("getdoc","__doc__"),
                       ("getsource","__code__"),("getsourcelines","__code__"),("getcomments","__code__")):
        setattr(inspect,name,observe(get(inspect,name),field))
    sys.addaudithook(trace_open)

pytest_runtest_protocol=scope.pytest_runtest_protocol
pytest_fixture_setup=scope.pytest_fixture_setup
pytest_collection_finish=scope.pytest_collection_finish
pytest_runtest_logreport=scope.pytest_runtest_logreport

def pytest_sessionfinish(session,exitstatus):
    assert exitstatus==0
    ids=json.load(open("/app/maps.json"))["ids"]
    passed=set(ids)&scope.passed
    assert passed==set(ids)
    index={n:i for i,n in enumerate(ids)}
    ancestors=collections.defaultdict(int)
    for t,parents in scope.contexts.items():
        if t in index:
            for p in parents:ancestors[p]|=1<<index[t]
    def encode(tags):
        bits=0;mods=set()
        for t in tags:
            if t in index:bits|=1<<index[t]
            elif t.startswith("@scope/"):bits|=ancestors[t[7:]]
            elif t.startswith("@module/"):mods.add(t[8:])
            else:bits=(1<<len(ids))-1
        return [hex(bits),sorted(mods)]
    data=dict(ids=ids,passed=sorted(passed),opaque=encode(scope.opaque),files={p:encode(ts) for p,ts in sorted(opened.items())},
              observers=[[list(k),encode(v)] for k,v in sorted(seen.items())])
    Path("/tmp/observers.gz").write_bytes(gzip.compress(json.dumps(data,separators=(",",":")).encode(),mtime=0))
