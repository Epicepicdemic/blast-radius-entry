"""Generate one entry of heavy-reach.json from an entry image containing the pinned source.

Run this script in four fresh processes with tpc, max, scope, and generator as the
sole argument. Store their JSON outputs under those keys in heavy-reach.json.
Each process verifies its original result before publishing any observations.
"""

import ast
import builtins
import dis
from functools import cache
import json
import os
from pathlib import Path
import sys
import types

ROOT = Path("/sqlglot")
APP = Path("/app")
sys.path[:0] = [str(APP), str(ROOT)]
os.chdir(ROOT)
import micro_oracles
import slicer

mode = sys.argv[1]
mon = sys.monitoring
entered = set()
lines = {}
paths = set()
seen_tables = set()
read_tables = set()
external_globals = set()
watched = {}
raw = type.__getattribute__
value_reads = set()


@cache
def discarded_pops(path):
    # A discarded dict.pop(key, default) ignores the old value and tests no
    # property of it. For equal key sequences this read cannot distinguish replacements.
    if not path.startswith("/sqlglot/sqlglot/"):
        return {}
    tree = ast.parse(Path(path).read_bytes())
    return {
        (
            n.value.func.value.lineno,
            n.value.func.value.end_lineno,
            n.value.func.value.col_offset,
            n.value.func.value.end_col_offset,
        )
        for n in ast.walk(tree)
        if isinstance(n, ast.Expr)
        and isinstance(n.value, ast.Call)
        and isinstance(n.value.func, ast.Attribute)
        and n.value.func.attr == "pop"
        and isinstance(n.value.func.value, ast.Attribute)
        and len(n.value.args) == 2
        and not n.value.keywords
    }


@cache
def ignores_value(code, offset):
    return any(
        i.offset == offset
        and i.opname == "LOAD_ATTR"
        and tuple(i.positions) in discarded_pops(code.co_filename)
        for i in dis.get_instructions(code)
    )


def observe_class(cls, name):
    # The pinned base classes use type's normal attribute lookup.
    for base in raw(cls, "__mro__"):
        fields = watched.get(id(base))
        if fields:
            if name == "__dict__":
                read_tables.update(fields.values())
                value_reads.update(fields.values())
            elif name in fields:
                read_tables.add(fields[name])
                frame = sys._getframe(2)
                if not ignores_value(frame.f_code, frame.f_lasti):
                    value_reads.add(fields[name])


class ObservedType(type):
    def __dir__(cls):
        observe_class(cls, "__dict__")
        return super().__dir__()

    def __getattribute__(cls, name):
        observe_class(cls, name)
        return super().__getattribute__(name)


class ObservedModule(types.ModuleType):
    def __getattribute__(self, name):
        ns = types.ModuleType.__getattribute__(self, "__dict__")
        external_globals.add((ns["__name__"], name))
        return types.ModuleType.__getattribute__(self, name)


create = builtins.__build_class__


def build(body, name, *bases, **kw):
    mod = body.__module__ or ""
    root_class = (mod, name) in {("sqlglot.generator", "Generator"), ("sqlglot.parser", "Parser")}
    if root_class:
        assert not kw and (not bases or bases == (object,))
        kw["metaclass"] = ObservedType
    cls = create(body, name, *bases, **kw)
    if root_class:
        original = raw(cls, "__getattribute__")

        def read(self, attr):
            observe_class(type(self), attr)
            return original(self, attr)

        cls.__getattribute__ = read
        if mode == "generator":
            normal_dir = raw(cls, "__dir__")

            def instance_dir(self):
                observe_class(type(self), "__dict__")
                return normal_dir(self)

            cls.__dir__ = instance_dir
    if type(cls) is ObservedType:
        ns = raw(cls, "__dict__")
        # Only these two dispatch dictionaries have a supported patch grammar.
        fields = {
            n: (mod, raw(cls, "__qualname__"), n)
            for n in ("TRANSFORMS", "FUNCTIONS")
            if type(ns.get(n)) is dict
        }
        if (
            mode == "generator"
            and mod.startswith("sqlglot.parsers.")
            and not any(
                "__init_subclass__" in raw(base, "__dict__")
                for base in raw(cls, "__mro__")[1:]
                if base is not object
            )
        ):
            fields.update(
                {
                    name: (mod, raw(cls, "__qualname__"), name)
                    for name, value in ns.items()
                    if type(value) is types.FunctionType and not name.startswith("__")
                }
            )
        if fields:
            watched[id(cls)] = fields
            seen_tables.update(fields.values())
    return cls


@cache
def predicates(path):
    if not path.startswith("/sqlglot/sqlglot/optimizer/"):
        return set()
    tree = ast.parse(Path(path).read_bytes())
    return {
        f.name
        for f in tree.body
        if isinstance(f, ast.FunctionDef)
        and isinstance(f.returns, ast.Name)
        and f.returns.id == "bool"
        and len(f.args.args) == 1
        and not f.decorator_list
        and not f.args.vararg
        and not f.args.kwarg
    }


entry_keys = {}


def on_start(code, offset):
    if code.co_filename.startswith("/sqlglot/"):
        entered.add(code)
        if code.co_qualname in predicates(code.co_filename):
            frame = sys._getframe(1)
            key = code.co_filename[9:] + ":" + code.co_qualname
            if key in entry_keys and entry_keys[key] is None:
                return mon.DISABLE
            obj = frame.f_locals[code.co_varnames[0]]
            cls = type(obj)
            descriptor = next((vars(base)["args"] for base in cls.__mro__ if "args" in vars(base)), None)
            args = getattr(obj, "args", None) if type(descriptor) is types.MemberDescriptorType else None
            if (
                cls.__getattribute__ is not object.__getattribute__
                or type(args) is not dict
                or not all(type(k) is str for k in args)
                or any(name in frame.f_globals for name in ("all", "any"))
            ):
                entry_keys[key] = None
                return mon.DISABLE
            entry_keys.setdefault(key, set()).update(args)
            return None
        if code.co_name == "<module>":
            mod = sys._getframe(1).f_globals["__name__"]
            if mod.startswith("sqlglot.optimizer.") and type(sys.modules.get(mod)) is types.ModuleType:
                sys.modules[mod].__class__ = ObservedModule
    return mon.DISABLE


def audit(ev, args):
    if ev == "open" and isinstance(args[0], (str, bytes)):
        p = os.path.abspath(os.fsdecode(args[0]))
        if p.startswith("/sqlglot/"):
            paths.add(p[9:])


sys.addaudithook(audit)
builtins.__build_class__ = build
mon.use_tool_id(mon.PROFILER_ID, "pinned heavy calculation")
mon.register_callback(mon.PROFILER_ID, mon.events.PY_START, on_start)
events = mon.events.PY_START
if mode == "tpc":
    # Only TPC-DS has an exact fixed sequence of inputs and structural signatures.
    def on_line(code, lineno):
        if code.co_filename.startswith("/sqlglot/sqlglot/"):
            lines.setdefault(code.co_filename[9:], set()).add(lineno)
        return mon.DISABLE

    mon.register_callback(mon.PROFILER_ID, mon.events.LINE, on_line)
    events |= mon.events.LINE
mon.set_events(mon.PROFILER_ID, events)
if mode == "tpc":
    baseline = slicer.load_tpcds_baseline()
    assert baseline and slicer.compute_tpcds_mismatches(baseline) == (True, [])
elif mode == "generator":
    from tests.test_generator import TestGenerator

    case = TestGenerator("test_generator_memory")
    result = case.run()
    assert result.testsRun == 1 and result.wasSuccessful() and not result.skipped, result
elif mode == "scope":
    assert micro_oracles.check_test_scope()
elif mode == "max":
    assert micro_oracles.check_max_nodes()
else:
    raise ValueError(mode)
mon.set_events(mon.PROFILER_ID, 0)
builtins.__build_class__ = create

# Scanning the complete code object includes dormant branches. Module STORE_NAME
# defines a constant; a store alone is not a read.
names = {}
functions = {}
unsafe = {"globals", "eval", "exec", "getframe", "_getframe", "f_globals"}
for code in entered:
    path = code.co_filename[9:]
    paths.add(path)
    if path.startswith("sqlglot/"):
        functions.setdefault(path, set()).add(code.co_qualname)
    if path.startswith("sqlglot/optimizer/"):
        reads = names.setdefault(path, set())
        for ins in dis.get_instructions(code):
            if ins.opname in ("LOAD_NAME", "LOAD_GLOBAL", "LOAD_FROM_DICT_OR_GLOBALS"):
                reads.add(ins.argval)
        if unsafe.intersection(code.co_names):
            reads.add("*")
for mod, name in external_globals:
    path = mod.replace(".", "/") + ".py"
    names.setdefault(path, set()).add("*" if name == "__dict__" else name)
for mod, obj in sys.modules.copy().items():
    if mod == "sqlglot" or mod.startswith("sqlglot."):
        f = types.ModuleType.__getattribute__(obj, "__file__")
        if f and f.startswith("/sqlglot/"):
            paths.add(f[9:])

print(
    json.dumps(
        dict(
            **({"lines": {p: sorted(v) for p, v in lines.items()}} if mode == "tpc" else {}),
            paths=sorted(p for p in paths if p.endswith(".py")),
            functions={p: sorted(v) for p, v in functions.items()},
            entry_keys={k: sorted(v) for k, v in entry_keys.items() if v is not None},
            value_only=sorted(read_tables - value_reads),
            tables=sorted(seen_tables - read_tables),
            globals={
                p: sorted(n for n in ns if n == "*" or n.isupper()) for p, ns in sorted(names.items())
            },
        ),
        sort_keys=True,
        separators=(",", ":"),
    )
)
