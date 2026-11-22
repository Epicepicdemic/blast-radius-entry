"""Record observed value dependence of literal class dictionaries on the pinned tree."""

import ast
import builtins
import collections
import functools
import importlib.machinery
import json
import os
from pathlib import Path

import pytest

context = "@boot"
hits = collections.defaultdict(set)
declarations = set()
scope = {}
passed = set()
pool = set()


class Traced(dict):
    def record(self, key=None):
        hits[context].add((self.site, key))

    def __getitem__(self, key):
        self.record(key if type(key) is str else None)
        return dict.__getitem__(self, key)

    def get(self, key, default=None):
        self.record(key if type(key) is str else None)
        return dict.get(self, key, default)

    def setdefault(self, key, default=None):
        self.record(key if type(key) is str else None)
        return dict.setdefault(self, key, default)

    def pop(self, key, *args):
        self.record(key if type(key) is str else None)
        return dict.pop(self, key, *args)

    def __iter__(self):
        self.record()
        return dict.__iter__(self)


def wide(name):
    original = getattr(dict, name)

    @functools.wraps(original)
    def call(self, *args, **kw):
        self.record()
        return original(self, *args, **kw)

    return call


for method in (
    "items",
    "values",
    "keys",
    "copy",
    "__eq__",
    "__ne__",
    "__repr__",
    "__str__",
    "__or__",
    "__ror__",
    "__ior__",
    "popitem",
    "__reduce__",
    "__reduce_ex__",
):
    setattr(Traced, method, wide(method))


def tracked(site, value):
    obj = Traced(value)
    obj.site = site
    declarations.add(site)
    return obj


def immutable(t):
    return type(t) in (int, str, bool, bytes, float, type(None)) or (
        type(t) is tuple and all(immutable(x) for x in t)
    )


def literal(node):
    try:
        value = ast.literal_eval(node)
    except (ValueError, TypeError, SyntaxError):
        return False
    return (
        type(value) is dict
        and value
        and all(type(k) is str and immutable(v) for k, v in value.items())
    )


def instrument(path, text):
    tree = ast.parse(text)
    any_change = False

    def classes(nodes, owner=""):
        nonlocal any_change
        for n in nodes:
            if isinstance(n, ast.ClassDef):
                classes(n.body, owner + n.name + ".")
            elif owner and isinstance(n, (ast.AnnAssign, ast.Assign)):
                target = n.target if isinstance(n, ast.AnnAssign) else n.targets[0]
                if (
                    isinstance(target, ast.Name)
                    and isinstance(n.value, ast.Dict)
                    and literal(n.value)
                ):
                    key = f"{path}:{owner}{target.id}"
                    n.value = ast.copy_location(
                        ast.Call(
                            ast.Name("__br_traced_table__", ast.Load()),
                            [ast.Constant(key), n.value],
                            [],
                        ),
                        n.value,
                    )
                    any_change = True

    classes(tree.body)
    return (
        compile(
            ast.fix_missing_locations(tree),
            "/sqlglot/" + path,
            "exec",
            dont_inherit=True,
        )
        if any_change
        else None
    )


def install_loader():
    builtins.__br_traced_table__ = tracked
    old = importlib.machinery.SourceFileLoader.get_code

    def locate(loader, name):
        if loader.path.startswith("/sqlglot/sqlglot/"):
            code = instrument(
                loader.path[len("/sqlglot/") :], Path(loader.path).read_bytes()
            )
            if code is not None:
                return code
        return old(loader, name)

    importlib.machinery.SourceFileLoader.get_code = locate


def pytest_configure(config):
    from concurrent.futures import ProcessPoolExecutor
    from _pytest.fixtures import FixtureDef

    install_loader()
    submit = ProcessPoolExecutor.submit

    def submitter(self, *args, **kwargs):
        pool.add(context)
        return submit(self, *args, **kwargs)

    ProcessPoolExecutor.submit = submitter
    finish = FixtureDef.finish

    def scoped(self, request):
        global context
        prev, context = context, "scope:" + request.node.nodeid
        try:
            return finish(self, request)
        finally:
            context = prev

    FixtureDef.finish = scoped


def pytest_collection_finish(session):
    scope.update(
        (item.nodeid, ["scope:" + n.nodeid for n in item.listchain()])
        for item in session.items
    )


@pytest.hookimpl(wrapper=True, tryfirst=True)
def pytest_runtest_protocol(item):
    global context
    prev, context = context, item.nodeid
    try:
        return (yield)
    finally:
        context = prev


@pytest.hookimpl(wrapper=True, tryfirst=True)
def pytest_fixture_setup(fixturedef, request):
    global context
    prev, context = context, "scope:" + request.node.nodeid
    try:
        return (yield)
    finally:
        context = prev


def pytest_runtest_logreport(report):
    if report.when == "call" and report.passed:
        passed.add(report.nodeid)


def pytest_sessionfinish(session, exitstatus):
    ids = json.loads(Path("/app/maps.json").read_bytes())["ids"]
    unknown = 0
    all_bits = (1 << len(ids)) - 1
    rows = collections.defaultdict(dict)

    # '*' is a reserved scope for iteration/opaque reads. Prefix every literal key.
    def add(site, key, bits):
        k = "*" if key is None else "k" + key
        rows[site][k] = rows[site].get(k, 0) | bits

    for site, key in hits["@boot"]:
        add(site, key, all_bits)
    for i, tid in enumerate(ids):
        cs = [tid, *scope.get(tid, [])]
        if tid not in passed or any(c in pool for c in cs):
            unknown |= 1 << i
        for c in cs:
            for site, key in hits[c]:
                add(site, key, 1 << i)
    out = dict(
        ids=ids,
        exitstatus=exitstatus,
        passed=len(passed),
        unknown=hex(unknown),
        rows={
            site: {k: hex(v) for k, v in rows[site].items()} for site in declarations
        },
    )
    Path(os.environ["KEY_OUT"]).write_text(json.dumps(out, separators=(",", ":")))
