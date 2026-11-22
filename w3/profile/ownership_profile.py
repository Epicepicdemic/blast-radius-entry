"""Observe runtime ownership at boolean copy-argument sites on the unmodified SQLGlot pin.

Run once as a pytest plugin. Each original call executes exactly once, with its original
arguments. No alternate flag is tried. The report contains operand facts and residuals.
"""
import ast
import builtins
from collections import Counter, defaultdict
import importlib.machinery
import inspect
import json
import os
from pathlib import Path
import sys
import types

import pytest

ROOT = Path("/sqlglot")
current = "@boot"
facts = defaultdict(lambda: defaultdict(set))
sites = {}
scope = {}
incomplete = set()
complete = set()
pooled = set()
steady = {}
consumers = {}
factories = set()
root_pid = os.getpid()
submitted = {}
finished = {}
worker_ready = False


def eligible(n):
    return (isinstance(n, ast.Call) and n.args and not isinstance(n.args[0], ast.Starred)
            and any(k.arg == "copy" and isinstance(k.value, ast.Constant)
                    and type(k.value.value) is bool for k in n.keywords))


def capture_factory(fn, /, *args, **kw):
    x = fn(*args, **kw)
    # These pure pinned builders construct their result entirely from scalar arguments.
    scalars = all(type(v) in (str, bool, type(None)) for v in (*args, *kw.values()))
    if scalars and any(fn is f for f in factories):
        return x, "owned:" + fn.__qualname__
    return x, "scalar" if type(x) is str else "unproven"


def capture_value(x, /):
    return x, "scalar" if type(x) is str else "unproven"


def call(site, fn, pair, /, *args, **kw):
    value, origin = pair
    rec = consumers.get(id(fn))
    stable = bool(rec and rec[0] is fn and
                  all(getattr(owner, attr) is original for owner, attr, original in steady.values()))
    contract = rec[1] if stable else "unproven"
    facts[current][site].add((contract, origin, type(value).__name__))
    return fn(value, *args, **kw)


class Instrument(ast.NodeTransformer):
    def __init__(self, path):
        self.path = path
        self.changed = False

    def visit_Call(self, node):
        if not eligible(node):
            return self.generic_visit(node)
        self.changed = True
        first = node.args[0]
        key = f"{self.path}:{node.lineno}:{node.col_offset}"
        sites[key] = (node.lineno, node.end_lineno)
        self.generic_visit(node)
        if isinstance(first, ast.Call):
            pair = ast.Call(ast.Name("__br_w3_factory", ast.Load()), [first.func,*first.args],first.keywords)
        else:
            pair = ast.Call(ast.Name("__br_w3_value", ast.Load()), [first], [])
        return ast.copy_location(ast.Call(ast.Name("__br_w3_call", ast.Load()),
            [ast.Constant(key), node.func, ast.copy_location(pair,first), *node.args[1:]],node.keywords), node)


def install_loader():
    # Trailing double underscores prevent Python's class name mangling.
    for key, fn in [("__br_w3_factory", capture_factory), ("__br_w3_value", capture_value), ("__br_w3_call", call)]:
        setattr(builtins, key+"__", fn)
    original = importlib.machinery.SourceFileLoader.get_code
    def code(loader, name):
        path = Path(loader.path)
        if str(path).startswith("/sqlglot/sqlglot/") and path.suffix == ".py":
            tree = ast.parse(path.read_bytes())
            transform = Instrument(str(path.relative_to(ROOT)))
            tree = transform.visit(tree)
            if transform.changed:
                for n in ast.walk(tree):
                    if isinstance(n, ast.Name) and n.id in ("__br_w3_factory", "__br_w3_value", "__br_w3_call"):
                        n.id += "__"
                return compile(ast.fix_missing_locations(tree),str(path),"exec",dont_inherit=True)
        return original(loader,name)
    importlib.machinery.SourceFileLoader.get_code = code


def init_contracts():
    from sqlglot import expressions as exp
    from sqlglot.expressions import builders, core
    # Derive consumers from code on the pin. The sole use of 'copy' must feed maybe_parse
    # on the first argument, which has no other consumer. Subsequent code uses its result.
    import textwrap
    for fn in vars(exp).values():
        if not isinstance(fn, types.FunctionType) or not fn.__module__.startswith("sqlglot.expressions"):
            continue
        if "copy" not in fn.__code__.co_varnames[:fn.__code__.co_argcount+fn.__code__.co_kwonlyargcount]:
            continue
        tree = ast.parse(textwrap.dedent(inspect.getsource(fn))).body[0]
        positional = tree.args.posonlyargs + tree.args.args
        if not positional:
            continue
        first = positional[0].arg
        uses = lambda name:[n for n in ast.walk(tree) if isinstance(n, ast.Name) and n.id == name]
        first_uses, flag_uses = uses(first), uses("copy")
        if len(first_uses) != 1 or len(flag_uses) != 1:
            continue
        body = tree.body[1:] if ast.get_docstring(tree) is not None else tree.body
        if not body or not isinstance(body[0], ast.Assign):
            continue
        v = body[0].value
        if (isinstance(v, ast.Call) and isinstance(v.func, ast.Name) and
                fn.__globals__.get(v.func.id) is core.maybe_parse and v.args == first_uses and
                any(k.arg == "copy" and k.value is flag_uses[0] for k in v.keywords)):
            consumers[id(fn)] = fn, "forward-to-parse"
    # The pinned table_ and to_identifier on strings/None allocate detached expression
    # trees. Direct plain expression constructors with scalar arguments do likewise.
    for fn, contract in ((core.maybe_parse, "parse"), (core.to_identifier, "identifier"),
                         (core.maybe_copy, "clone")):
        consumers[id(fn)] = fn, contract
    factories.add(builders.table_)
    factories.add(core.to_identifier)
    for cls in (exp.Table, exp.TableAlias, exp.Identifier):
        if cls.__init__ is exp.Expression.__init__ and cls.__new__ is object.__new__:
            factories.add(cls)
    # A test replacing a constructor, copy implementation, or forwarding helper invalidates
    # this witness. All comparisons are of actual objects in this process, not their names.
    for mod,attrs in [(builders,("to_identifier","Table","TableAlias")), (core,("maybe_parse","maybe_copy","Identifier")),
                      (exp.Expression,("copy","__deepcopy__","__init__","_set_parent","set","append"))]:
        for attr in attrs:
            steady[id(mod),attr] = (mod,attr,getattr(mod,attr))


def encode_facts():
    return {c:{site:sorted(vals) for site,vals in sites.items()} for c,sites in facts.items()}


def flush_worker():
    if finished:
        p=Path(os.environ["BR_OWNERSHIP_WORKERS"])/f"{os.getpid()}.json"
        p.write_text(json.dumps(dict(ready=worker_ready, tasks=finished, facts=encode_facts()),separators=(",",":")))


def worker_start():
    global worker_ready
    from multiprocessing.util import Finalize
    install_loader()
    init_contracts()
    worker_ready = True
    Finalize(None,flush_worker,exitpriority=0)


def tagged(num, owner, fn, args, kw):
    global current
    current = owner
    try:
        v = fn(*args, **kw)
        finished[num] = owner
        return v
    finally:
        current = "@boot"


def pytest_configure(config):
    install_loader()
    init_contracts()
    from concurrent.futures import ProcessPoolExecutor
    from _pytest.fixtures import FixtureDef
    submit = ProcessPoolExecutor.submit
    def record_submit(self, *args, **kwargs):
        pooled.add(current)
        fn, *rest = args
        num = len(submitted)
        submitted[num] = current
        return submit(self, tagged, num, current, fn, rest, kwargs)
    ProcessPoolExecutor.submit = record_submit
    finish = FixtureDef.finish
    def ended(self, request):
        global current
        prev, current = current, "scope:" + request.node.nodeid
        try: return finish(self,request)
        finally: current=prev
    FixtureDef.finish=ended


def pytest_collection_finish(session):
    for item in session.items:
        scope[item.nodeid] = [current for current in ("scope:"+p.nodeid for p in item.listchain())]


@pytest.hookimpl(wrapper=True, tryfirst=True)
def pytest_runtest_protocol(item):
    global current
    prev,current=current,item.nodeid
    try: return (yield)
    finally: current=prev


@pytest.hookimpl(wrapper=True, tryfirst=True)
def pytest_fixture_setup(fixturedef, request):
    global current
    prev,current=current,"scope:"+request.node.nodeid
    try: return (yield)
    finally: current=prev


def pytest_runtest_logreport(report):
    if report.failed or report.skipped:
        incomplete.add(report.nodeid)
    if report.when == "call" and report.passed:
        complete.add(report.nodeid)


def pytest_sessionfinish(session, exitstatus):
    if os.getpid()!=root_pid: return
    ids = json.loads(Path("/app/maps.json").read_bytes())["ids"]
    seen_tasks = Counter()
    for p in Path(os.environ["BR_OWNERSHIP_WORKERS"]).glob("*.json"):
        worker=json.loads(p.read_bytes())
        if not worker["ready"]:
            continue
        for num, owner in worker["tasks"].items():
            if submitted.get(int(num)) == owner:
                seen_tasks[int(num)]+=1
        owners = set(worker["tasks"].values())
        for ctx, observations in worker["facts"].items():
            for owner in (owners if ctx=="@boot" else {ctx}):
                for site, values in observations.items():
                    facts[owner][site].update(tuple(v) for v in values)
    residual = {owner for num,owner in submitted.items() if seen_tasks[num] != 1}
    rows=defaultdict(dict)
    opaque=0
    for i,tid in enumerate(ids):
        contexts=[tid,*scope.get(tid,[])]
        if tid not in complete or tid in incomplete or any(c in residual for c in contexts):
            opaque |= 1 << i
        for c in contexts:
            for site, observations in facts[c].items():
                for fact in observations:
                    rows[site][fact] = rows[site].get(fact,0) | (1 << i)
    all_bits = (1 << len(ids)) - 1
    for site, observations in facts["@boot"].items():
        for fact in observations:
            rows[site][fact] = all_bits
    result = dict(ids=ids, collected=len(scope), passed=len(complete-incomplete), exitstatus=exitstatus,
                  eligible_sites=len(sites), tasks=len(submitted), joined=sum(n==1 for n in seen_tasks.values()),
                  incomplete=hex(opaque), domains={k:[[*fact,hex(mask)] for fact,mask in sorted(v.items())]
                  for k,v in sorted(rows.items())}, consumers=sorted(f.__qualname__ for f,contract in consumers.values()))
    Path(os.environ["BR_OWNERSHIP_OUT"]).write_text(json.dumps(result,separators=(",",":")))
