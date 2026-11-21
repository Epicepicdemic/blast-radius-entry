"""Heap census collector (pytest plugin), run on the pinned tree only.

After collection and after every test it walks the objects reachable from the
SQLGlot and test modules (module dicts, class dicts, closures, defaults, caches)
and treats every mutable object found as shared (S). Deeply immutable values,
enum members, classes, functions and modules are not in S; the run also checks
that no class namespace or enum member changes once tests start.

For every SQLGlot function it records, per parameter, whether the bound object
(or, for an expression, list, tuple or dict, any direct child) was ever in S.
An object first seen during a test and in S when that test ends also counts.
Output: JSON at $CENSUS_OUT (one file per process).
"""
import enum
import gc
import json
import os
import sys
import types

ROOT = os.environ.get("CENSUS_ROOT", "/sqlglot")
PKG = os.path.join(ROOT, "sqlglot") + os.sep
OUT = os.environ.get("CENSUS_OUT", "/tmp/census.json")
TOOL = 5
NOSEEN = os.environ.get("CENSUS_NOSEEN") == "1"
NOWALK = os.environ.get("CENSUS_NOWALK") == "1"

ATOMS = frozenset({str, int, float, complex, bool, type(None), bytes, range, type(Ellipsis),
                   type(NotImplemented)})
SKIP_TYPES = (type, types.ModuleType, types.FunctionType, types.BuiltinFunctionType, types.CodeType,
              types.MethodDescriptorType, types.WrapperDescriptorType, types.GetSetDescriptorType,
              types.MemberDescriptorType, types.MethodWrapperType, types.ClassMethodDescriptorType,
              types.FrameType, types.CellType, staticmethod, classmethod, property, enum.Enum)


def immutable(v, depth=0):
    t = type(v)
    if t in ATOMS or isinstance(v, enum.Enum):
        return True
    if t in (tuple, frozenset) and depth < 4:
        return all(immutable(x, depth + 1) for x in v)
    return False


def own(name):
    return name == "sqlglot" or name.startswith("sqlglot.") or name == "tests" or name.startswith("tests.")


class Census:
    def __init__(self):
        self.S = set()
        self.seen = {}
        self.shared = set()
        self.opaque = set()
        self.calls = {}
        self.watch = {}
        self.class_prints = None
        self.written = set()
        self.Expression = None
        self.walks = 0
        self.max_s = 0
        self.child = None

    # -- shared set -------------------------------------------------------
    def roots(self):
        out, foreign = [], set()
        for name, mod in list(sys.modules.items()):
            d = getattr(mod, "__dict__", None)
            if d is None:
                continue
            if own(name):
                out.append(d)
            else:
                foreign.add(id(d))
        return out, foreign

    def walk(self):
        roots, foreign = self.roots()
        S = set()
        visited = set(foreign)
        stack = list(roots)
        for r in roots:
            visited.add(id(r))
        get = gc.get_referents
        while stack:
            obj = stack.pop()
            t = type(obj)
            if not isinstance(obj, SKIP_TYPES) and not immutable(obj):
                S.add(id(obj))
            if isinstance(obj, type) and not own(getattr(obj, "__module__", "") or ""):
                continue
            if isinstance(obj, types.ModuleType):
                continue
            if isinstance(obj, types.FunctionType):
                children = [obj.__defaults__, obj.__kwdefaults__, obj.__closure__, obj.__dict__]
            else:
                children = get(obj)
            for c in children:
                if c is None or type(c) in ATOMS:
                    continue
                i = id(c)
                if i in visited:
                    continue
                visited.add(i)
                stack.append(c)
        self.walks += 1
        self.max_s = max(self.max_s, len(S))
        return S

    def prints(self):
        out = {}
        for name, mod in list(sys.modules.items()):
            if not name.startswith("sqlglot"):
                continue
            for v in list(vars(mod).values()):
                if isinstance(v, type) and getattr(v, "__module__", "").startswith("sqlglot"):
                    out[f"{v.__module__}:{v.__qualname__}"] = tuple(sorted((k, id(x)) for k, x in vars(v).items()))
                    if issubclass(v, enum.Enum):
                        for m in v:
                            out[f"{v.__module__}:{v.__qualname__}.{m.name}"] = tuple(
                                sorted((k, id(x)) for k, x in vars(m).items()))
        return out

    def boundary(self):
        if NOWALK and self.S:
            return
        S = self.walk()
        for i, keys in self.seen.items():
            if i in S:
                self.shared.update(keys)
        self.seen = {}
        self.S = S
        now = self.prints()
        if self.class_prints is None:
            self.class_prints = now
        else:
            for k, v in now.items():
                if self.class_prints.get(k, v) != v:
                    self.written.add(k)
            self.class_prints.update(now)

    # -- parameter events ---------------------------------------------------
    def code_info(self, code):
        if not code.co_filename.startswith(PKG):
            return None
        n = code.co_argcount + code.co_kwonlyargcount
        n += bool(code.co_flags & 0x04) + bool(code.co_flags & 0x08)
        rel = os.path.relpath(code.co_filename, ROOT)
        key = f"{rel}:{code.co_qualname}:{code.co_firstlineno}"
        return key, code.co_varnames[:n]

    def note(self, v, key, name):
        if type(v) in ATOMS:
            return
        i = id(v)
        if i in self.S:
            self.shared.add((key, name))
            return True
        if NOSEEN:
            return False
        # Keep only the id: a reference would change what weak caches retain.
        # A reused id can only add a false "shared" mark.
        s = self.seen.get(i)
        if s is None:
            self.seen[i] = {(key, name)}
        else:
            s.add((key, name))
        return False

    def on_start(self, code, offset):
        try:
            return self._on_start(code, offset)
        except Exception:
            # Never disturb the traced code. Without evidence the code's
            # parameters count as opaque.
            info = self.watch.get(code)
            if info is not None:
                self.opaque.update((info[0], n) for n in info[1])
            return None

    def in_child(self, out=None):
        # A forked or spawned worker: its heap is not walked, so every function
        # it runs is recorded once and all of its parameters count as opaque.
        self.child = open(f"{out or OUT}.child.{os.getpid()}", "a")
        self.watch = {}

    def _on_start(self, code, offset):
        info = self.watch.get(code)
        if info is None:
            info = self.code_info(code)
            if info is None:
                return sys.monitoring.DISABLE
            self.watch[code] = info
            if self.child is not None:
                self.child.write(info[0] + "\n")
                self.child.flush()
        if self.child is not None:
            return sys.monitoring.DISABLE
        key, names = info
        self.calls[key] = self.calls.get(key, 0) + 1
        loc = sys._getframe(2).f_locals  # on_start, then the traced frame
        E = self.Expression
        for name in names:
            if (key, name) in self.shared or (key, name) in self.opaque:
                continue
            try:
                v = loc[name]
            except KeyError:
                continue
            if self.note(v, key, name):
                continue
            t = type(v)
            if t is list or t is tuple:
                children = v
            elif t is dict:
                children = v.values()
            elif E is not None and isinstance(v, E):
                a = getattr(v, "args", None)
                if a is None:
                    continue  # an expression still under construction
                children = a.values()
            else:
                # Other objects can reach shared state through their fields.
                if t not in ATOMS and not isinstance(v, enum.Enum):
                    self.opaque.add((key, name))
                continue
            for c in children:
                if type(c) is list:
                    for e in c:
                        if self.note(e, key, name):
                            break
                elif self.note(c, key, name):
                    break

    def start(self):
        import sqlglot.expressions as exp
        self.Expression = getattr(exp, "Expr", None) or getattr(exp, "Expression")
        mon = sys.monitoring
        mon.use_tool_id(TOOL, "census")
        mon.register_callback(TOOL, mon.events.PY_START, self.on_start)
        mon.set_events(TOOL, mon.events.PY_START)
        os.register_at_fork(after_in_child=self.in_child)
        # Spawned workers and subprocesses load builder/sitecustomize.py.
        os.environ["CENSUS_CHILD_OUT"] = OUT

    def dump(self):
        sys.monitoring.set_events(TOOL, 0)
        params = {}
        for key, n in self.calls.items():
            params[key] = {"calls": n, "shared": []}
        for key, name in self.shared:
            params.setdefault(key, {"calls": 0, "shared": []})["shared"].append(name)
        for key, name in self.opaque:
            params.setdefault(key, {"calls": 0, "shared": []}).setdefault("opaque", []).append(name)
        for v in params.values():
            v["shared"].sort()
            v.setdefault("opaque", []).sort()
        out = OUT
        worker = os.environ.get("PYTEST_XDIST_WORKER")
        if worker:
            out = f"{OUT}.{worker}"
        with open(out, "w") as f:
            json.dump({"params": params, "written": sorted(self.written), "walks": self.walks,
                       "max_shared": self.max_s}, f, sort_keys=True)


CENSUS = Census()


def child_process(out):
    CENSUS.in_child(out)
    mon = sys.monitoring
    mon.use_tool_id(TOOL, "census")
    mon.register_callback(TOOL, mon.events.PY_START, CENSUS.on_start)
    mon.set_events(TOOL, mon.events.PY_START)


def _controller(config):
    # The xdist controller only relays reports; workers run the tests.
    return getattr(config.option, "numprocesses", None) and not hasattr(config, "workerinput")


def pytest_collection_finish(session):
    if _controller(session.config):
        return
    CENSUS.boundary()
    CENSUS.start()
    CENSUS.started = True


def pytest_runtest_logfinish(nodeid, location):
    if getattr(CENSUS, "started", False):
        CENSUS.boundary()


def pytest_sessionfinish(session, exitstatus):
    if getattr(CENSUS, "started", False):
        CENSUS.boundary()
        CENSUS.dump()
