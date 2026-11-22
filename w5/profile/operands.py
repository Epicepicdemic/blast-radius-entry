"""Observe enum equality and passive scalar callbacks on the unchanged SQLGlot pin."""
import ast
import builtins
import collections
import enum
import functools
import gzip
import json
import os
import sys
from pathlib import Path

import slots as scopes

# Each site has fixed operands in the source. Identity and equality can disagree
# for string-backed enums when an actual is an ordinary string.
comparisons = collections.defaultdict(lambda: collections.defaultdict(set))
callbacks = collections.defaultdict(lambda: collections.defaultdict(set))
started = set()
monitor = sys.monitoring
tool = monitor.OPTIMIZER_ID


def compare(site, operation, a, b):
    equal_type = type(a) is type(b)
    if equal_type and isinstance(a, enum.Enum) and type(a).__eq__ in (str.__eq__, object.__eq__, int.__eq__):
        different = (a is b) != (a == b)
    elif a is None or b is None:
        different = None
    elif isinstance(b, enum.Enum) and type(a) in (str, int) and type(b).__eq__ in (str.__eq__, int.__eq__):
        different = (a is b) != (a == b)
    else:
        different = None
    comparisons[site][str(different)].add(scopes.where())
    if operation == "Eq":
        return a == b
    if operation == "NotEq":
        return a != b
    if operation == "Is":
        return a is b
    return a is not b


def capture(site, fn):
    @functools.wraps(fn)
    def call(*args, **kwargs):
        values = args + tuple(kwargs.values())
        if all(type(x) in (str, int, bool, type(None)) and
               (type(x) is not str or len(x) <= 160) and
               (type(x) is not int or x.bit_length() <= 96) for x in values):
            key = json.dumps([args, sorted(kwargs.items())], separators=(",", ":"))
            if key not in callbacks[site] and len(callbacks[site]) >= 2048:
                key = "?"
        else:
            key = "?"
        callbacks[site][key].add(scopes.where())
        return fn(*args, **kwargs)
    return call


class Rewrite(ast.NodeTransformer):
    def site(self, node):
        return f"{self.path}:{node.lineno}:{node.col_offset}"

    def visit_Compare(self, node):
        self.generic_visit(node)
        if len(node.ops) == 1 and isinstance(node.ops[0], (ast.Eq, ast.NotEq, ast.Is, ast.IsNot)):
            b = node.comparators[0]
            if isinstance(b, ast.Attribute) and b.attr.isupper() and isinstance(b.value, ast.Name):
                a = node.left
                return ast.copy_location(ast.Call(ast.Name("_br5_compare", ast.Load()),
                    [ast.Constant(self.site(node)), ast.Constant(type(node.ops[0]).__name__), a, b], []), node)
        return node

    def visit_Lambda(self, node):
        self.generic_visit(node)
        # A bounded scalar-language interpreter at selection time accepts only a
        # subset of these callbacks. The original callable always executes here.
        if node.args.defaults and not node.args.kwonlyargs and not node.args.vararg and not node.args.kwarg:
            return ast.copy_location(ast.Call(ast.Name("_br5_capture", ast.Load()),
                [ast.Constant(self.site(node)), node], []), node)
        return node


class Source(scopes.Source):
    def get_code(self, name):
        path = self.get_filename(name)
        rw = Rewrite()
        rw.path = str(Path(path).relative_to(scopes.ROOT))
        tree = ast.parse(self.get_data(path), path)
        if rw.path.startswith("sqlglot/"):
            tree = rw.visit(tree)
        return compile(ast.fix_missing_locations(tree), path, "exec", dont_inherit=True)


class Finder(scopes.Finder):
    def find_spec(self, name, path, target=None):
        spec = super().find_spec(name, path, target)
        if spec:
            spec.loader = Source(name, spec.origin)
        return spec


def entry(code, offset):
    prefix = "/sqlglot/tests/"
    if code.co_filename.startswith(prefix):
        started.add((code.co_filename[len("/sqlglot/"):], code.co_qualname, code.co_firstlineno))
    return monitor.DISABLE


def pytest_configure(config):
    scopes.pytest_configure(config)
    builtins._br5_compare = compare
    builtins._br5_capture = capture
    sys.meta_path[0] = Finder()
    monitor.use_tool_id(tool, "pinned test code")
    monitor.register_callback(tool, monitor.events.PY_START, entry)
    monitor.set_events(tool, monitor.events.PY_START)


pytest_runtest_protocol = scopes.pytest_runtest_protocol
pytest_fixture_setup = scopes.pytest_fixture_setup
pytest_collection_finish = scopes.pytest_collection_finish
pytest_runtest_logreport = scopes.pytest_runtest_logreport


def pytest_sessionfinish(session, exitstatus):
    assert exitstatus == 0
    ids = json.load(open("/app/maps.json"))["ids"]
    index = {t: i for i, t in enumerate(ids)}
    passed = set(ids) & scopes.passed
    ancestors = collections.defaultdict(int)
    for t, parents in scopes.contexts.items():
        if t in index:
            for parent in parents:
                ancestors[parent] |= 1 << index[t]

    def encode(seen):
        mask, modules = 0, set()
        for tag in seen:
            if tag in index:
                mask |= 1 << index[tag]
            elif tag.startswith("@scope/"):
                mask |= ancestors[tag[7:]]
            elif tag.startswith("@module/"):
                modules.add(tag[8:])
            else:
                mask = (1 << len(ids)) - 1
        return [hex(mask), sorted(modules)]

    def rows(table):
        return {k: {v: encode(c) for v, c in sorted(data.items())} for k, data in sorted(table.items())}

    record = dict(ids=ids, passed=sorted(passed), opaque=encode(scopes.opaque | (set(ids)-passed)),
                  comparisons=rows(comparisons), callbacks=rows(callbacks), test_entries=sorted(started))
    raw = json.dumps(record, separators=(",", ":")).encode()
    Path("/tmp/operands.gz").write_bytes(gzip.compress(raw, mtime=0))
