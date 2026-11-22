"""Observe values and concrete closure invocations on the unmodified Python pin."""
import ast
import builtins
from collections import defaultdict
import enum
import importlib.machinery
import json
import os
from pathlib import Path
import sys
from types import FunctionType

import pytest

ROOT = "/sqlglot/"
current = "@shared"
passed = set()
incomplete = set()
untraced = set()
domains = defaultdict(lambda: defaultdict(set))
origins = {}
calls = defaultdict(set)
declared = set()
reflections = defaultdict(set)
monitor = sys.monitoring
tool_id = monitor.PROFILER_ID


def record_operands(site, left, right):
    # Only record primitive data, never invoke a user comparison or conversion here.
    if type(left) is tuple and type(right) is tuple and all(type(x) is int for x in left + right):
        if max(len(left), len(right)) <= 8:
            fact = ("tuples", left, right)
        else:
            fact = ("unknown",)
    elif isinstance(right, enum.Enum) and type(left) is type(right):
        cls = type(right)
        cmp = (cls.__eq__, cls.__ne__)
        if cmp == (str.__eq__, str.__ne__) and isinstance(left, str):
            fact = ("strings", left is right, str.__str__(left), str.__str__(right))
        elif cmp == (object.__eq__, object.__ne__):
            fact = ("identity", left is right)
        else:
            fact = ("unknown",)
    elif right is None and (left is None or
            (type(left).__eq__ is object.__eq__ and type(left).__ne__ is object.__ne__)):
        fact = ("identity", left is right)
    else:
        fact = ("unknown",)
    domains[site][fact].add(current)
    return left, right


def tag_closure(site, value):
    if type(value) is FunctionType and value.__closure__:
        # Each closure gets its own PY_START subscription even when a factory shares code.
        code = value.__code__.replace()
        value.__code__ = code
        origins[id(code)] = (code, site)
        declared.add(site)
        monitor.set_local_events(tool_id, code, monitor.events.PY_START)
    return value


def entered(code, offset):
    origin = origins.get(id(code))
    if origin:
        calls[origin[1]].add(current)


def audit(event, args):
    if event == "object.__getattr__" and args[1] == "__code__" and type(args[0]) is FunctionType:
        # Avoid recursive access to __code__ inside the audit callback.
        if not audit.busy:
            audit.busy = True
            try:
                filename = args[0].__code__.co_filename
                if filename.startswith(ROOT):
                    reflections[filename[len(ROOT):]].add(current)
            finally:
                audit.busy = False

audit.busy = False


class Observe(ast.NodeTransformer):
    def __init__(self, path):
        self.path = path
        self.changed = False

    def visit_Compare(self, node):
        self.generic_visit(node)
        if len(node.ops) != 1:
            return node
        other = node.comparators[0]
        numeric_tuple = isinstance(other, ast.Tuple) and all(
            isinstance(x, ast.Constant) and type(x.value) is int for x in other.elts)
        member = isinstance(other, ast.Attribute) and isinstance(other.value, ast.Name) and other.attr.isupper()
        self_attr = isinstance(node.left, ast.Attribute) and isinstance(node.left.value, ast.Name) and node.left.value.id == "self"
        singleton = isinstance(other, ast.Constant) and other.value is None
        if not numeric_tuple and not (self_attr and (member or singleton) and isinstance(node.ops[0], (ast.Is, ast.IsNot))):
            return node
        site = f"{self.path}:{node.lineno}:{node.col_offset}"
        # A helper records the two inputs then applies the real operation once.
        operations = {ast.Eq:"eq", ast.NotEq:"ne", ast.Is:"is_", ast.IsNot:"is_not",
                      ast.Lt:"lt", ast.LtE:"le", ast.Gt:"gt", ast.GtE:"ge"}
        op = operations.get(type(node.ops[0]))
        if op is None:
            return node
        self.changed = True
        return ast.copy_location(ast.Call(ast.Name("_w2_compare", ast.Load()),
            [ast.Constant(site), ast.Constant(op), node.left, other], []), node)

    def visit_ClassDef(self, node):
        self.generic_visit(node)
        for stmt in node.body:
            if not isinstance(stmt, (ast.Assign, ast.AnnAssign)) or not isinstance(stmt.value, ast.Dict):
                continue
            for i, value in enumerate(stmt.value.values):
                if isinstance(value, ast.Call) and isinstance(value.func, ast.Name):
                    site = f"{self.path}:{value.lineno}:{value.col_offset}"
                    stmt.value.values[i] = ast.copy_location(ast.Call(ast.Name("_w2_tag", ast.Load()),
                        [ast.Constant(site), value], []), value)
                    self.changed = True
        return node


def install():
    import operator
    def compare(site, name, left, right):
        record_operands(site, left, right)
        return getattr(operator, name)(left, right)
    builtins._w2_compare = compare
    builtins._w2_tag = tag_closure
    monitor.use_tool_id(tool_id, "pin value observations")
    monitor.register_callback(tool_id, monitor.events.PY_START, entered)
    old = importlib.machinery.SourceFileLoader.get_code
    def code(loader, name):
        if loader.path.startswith(ROOT + "sqlglot/"):
            path = loader.path[len(ROOT):]
            tree = ast.parse(Path(loader.path).read_bytes(), loader.path)
            obs = Observe(path)
            obs.visit(tree)
            if obs.changed:
                return compile(ast.fix_missing_locations(tree), loader.path, "exec", dont_inherit=True)
        return old(loader, name)
    if "sqlglot" in sys.modules:
        raise RuntimeError("SQLGlot imported before collector")
    importlib.machinery.SourceFileLoader.get_code = code
    sys.addaudithook(audit)


def pytest_configure(config):
    install()
    from concurrent.futures import ProcessPoolExecutor
    submit = ProcessPoolExecutor.submit
    def submitting(*args, **kwargs):
        untraced.add(current)
        return submit(*args, **kwargs)
    ProcessPoolExecutor.submit = submitting


@pytest.hookimpl(wrapper=True, tryfirst=True)
def pytest_runtest_call(item):
    global current
    current = item.nodeid
    try:
        return (yield)
    finally:
        current = "@shared"


def pytest_runtest_logreport(report):
    if report.failed or report.skipped:
        incomplete.add(report.nodeid)
    if report.when == "call" and report.passed and getattr(report, "context", None) is None:
        passed.add(report.nodeid)


def snapshot():
    # pytest-xdist is deliberately disabled. A missing/failed test stays a candidate.
    def owners(table):
        return {k:sorted(v) for k,v in table.items()}
    result = dict(passed=sorted(passed-incomplete), untraced=sorted(untraced), reflected=owners(reflections),
                  closures={s:sorted(calls[s]) for s in declared},
                  domains={s:[[list(v),sorted(nodes)] for v,nodes in d.items()] for s,d in domains.items()})
    return result

def pytest_sessionfinish(session, exitstatus):
    Path(os.environ["W2_VALUE_OUT"]).write_text(json.dumps(snapshot(),separators=(",",":")))
