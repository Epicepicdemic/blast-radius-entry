"""Pin-only pytest plugin for concrete expression-class metadata reads across inheritance."""
import ast
import builtins
import importlib.abc
import importlib.machinery
import json
import os
import sys
from collections import defaultdict
from pathlib import Path

import pytest

FIELDS = {"arg_types", "required_args"}
current = "@shared"
reads = defaultdict(set)
passed = set()
wild = set()
root = Path(os.environ.get("METADATA_ROOT", "/sqlglot")).resolve()
original_getattr = getattr
pid = os.getpid()

def owner(obj):
    cls = obj if isinstance(obj, type) else type(obj)
    mro = type.__getattribute__(cls, "__mro__")
    if not any(c.__module__ == "sqlglot.expressions.core" and c.__name__ == "Expr" for c in mro):
        return None
    for c in mro:
        if "arg_types" in type.__getattribute__(c, "__dict__"):
            return c.__module__ + "." + c.__qualname__
    return None

def observe(obj, name, frame):
    if name not in FIELDS and name != "__dict__": return
    try:
        declaring = owner(obj)
    except (TypeError, AttributeError):
        wild.add(current)
        return
    if declaring is None: return
    # The pin eagerly computes required_args from arg_types. Attribute a later read
    # of the derived set to the exact same owner. The compiler checks the assignment.
    if (name == "arg_types" and frame.f_code.co_qualname == "Expr.__init_subclass__"
            and frame.f_code.co_filename == str(root / "sqlglot/expressions/core.py")
            and frame.f_lineno in derivation):
        return
    for field in FIELDS if name == "__dict__" else (name,):
        reads[(declaring,field)].add(current)

def attr(obj, key):
    observe(obj,key,sys._getframe(1))
    return original_getattr(obj,key)

def introspect(fn, *args, **kwargs):
    if fn is builtins.vars and len(args)==1:
        observe(args[0],"__dict__",sys._getframe(1))
    if fn in (builtins.getattr,builtins.hasattr,builtins.setattr,builtins.delattr) and len(args)>=2 and type(args[1]) is str:
        observe(args[0],args[1],sys._getframe(1))
    return fn(*args, **kwargs)

class Rewrite(ast.NodeTransformer):
    def visit_Attribute(self,node):
        self.generic_visit(node)
        if isinstance(node.ctx,ast.Load) and node.attr in FIELDS|{"__dict__"}:
            return ast.copy_location(ast.Call(ast.Name("_w2_class_attr",ast.Load()),
                                     [node.value,ast.Constant(node.attr)],[]),node)
        return node
    def visit_Call(self,node):
        self.generic_visit(node)
        if (isinstance(node.func,ast.Name) and node.func.id in ("getattr","hasattr","vars","setattr","delattr")
                and node.args):
            return ast.copy_location(ast.Call(ast.Name("_w2_class_inspect",ast.Load()),
                                     [node.func,*node.args],node.keywords),node)
        return node

class Source(importlib.machinery.SourceFileLoader):
    def get_code(self,fullname):
        path=self.get_filename(fullname)
        tree=ast.parse(self.get_data(path),path)
        return compile(ast.fix_missing_locations(Rewrite().visit(tree)),path,"exec",dont_inherit=True)

class Projects(importlib.abc.MetaPathFinder):
    def find_spec(self,fullname,path,target=None):
        if fullname.split(".",1)[0] not in ("sqlglot","tests"):return None
        spec=importlib.machinery.PathFinder.find_spec(fullname,path)
        if spec and spec.origin and spec.origin.endswith(".py") and Path(spec.origin).is_relative_to(root):
            spec.loader=Source(fullname,spec.origin)
            return spec
        return None

def pytest_configure(config):
    global derivation
    target=root/"sqlglot/expressions/core.py"
    tree=ast.parse(target.read_bytes())
    proto=ast.parse("cls.required_args = {k for k,v in cls.arg_types.items() if v}").body[0]
    derivation={s.lineno for n in tree.body if isinstance(n,ast.ClassDef) and n.name=="Expr"
                for f in n.body if isinstance(f,ast.FunctionDef) and f.name=="__init_subclass__"
                for s in f.body if ast.dump(s)==ast.dump(proto)}
    if len(derivation)!=1:raise ValueError("unknown metadata derivation")
    builtins._w2_class_attr=attr
    builtins._w2_class_inspect=introspect
    if any(n=="sqlglot" or n.startswith("sqlglot.") for n in sys.modules):
        raise ValueError("pin loaded before instrumentation")
    sys.meta_path.insert(0,Projects())

@pytest.hookimpl(hookwrapper=True,tryfirst=True)
def pytest_runtest_call(item):
    global current
    previous=current
    current=item.nodeid
    try:yield
    finally:current=previous

def pytest_runtest_logreport(report):
    if report.when=="call" and report.passed and getattr(report,"context",None) is None:passed.add(report.nodeid)

def pytest_sessionfinish(session,exitstatus):
    if os.getpid()!=pid:return
    out=dict(status=int(exitstatus),passed=sorted(passed),wild=sorted(wild),
             readers={name+":"+field:sorted(nodes) for (name,field),nodes in reads.items()})
    Path(os.environ["METADATA_RESULT"]).write_text(json.dumps(out,separators=(",",":")))
