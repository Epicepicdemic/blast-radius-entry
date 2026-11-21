"""Heap census: which values reaching a call can be shared state at the pin.

Offline (pinned tree only, like maps.json): the `census` Docker target runs the
pinned suite under builder/census_plugin.py, which records the parameters ever
bound to a shared mutable object; `python census.py merge OUT_DIR
census_params.json` writes the committed parameter census.

Image build time (pinned tree only):
    python census.py build /sqlglot census_params.json /app/census.json
imports every SQLGlot module and classifies each module global and class
attribute (immutable value, container of immutable elements, class, function,
module or shared mutable object), then adds the parameter census.

Runtime: `Census.load(path).resolver(module, tree)` returns the callback used by
shared_writes.shared_write_effect. It answers True only when the argument value
provably holds no shared mutable object; anything else keeps the existing guard.
"""
import ast
import builtins
import json
import sys
from functools import cached_property
from pathlib import Path

# Builtin consumers that never mutate their arguments.
PURE_FUNCS = frozenset(
    "len iter isinstance issubclass sorted list dict tuple set frozenset str repr hash id min max "
    "sum any all enumerate zip map filter reversed next bool int float type callable".split())
# Read-only or storing container methods: they never mutate an argument.
# The receiver is checked separately by the shared-write guard.
SINK_METHODS = frozenset(
    "intersection union difference symmetric_difference issubset issuperset isdisjoint "
    "update extend append add insert setdefault startswith endswith join index count "
    "difference_update intersection_update symmetric_difference_update".split())
SINK_FUNCS = frozenset("re.sub re.match re.search re.fullmatch re.findall re.split re.compile".split())
FRESH_BUILTIN_VALUES = frozenset("str int float bool repr len id hash isinstance issubclass callable".split())
MAX_DEPTH = 8
EXPR_FIELDS = frozenset("this expression expressions args name alias alias_or_name output_name key".split())


def _kind(v):
    import enum
    import types
    if isinstance(v, types.ModuleType):
        return ["module", v.__name__]
    if isinstance(v, type):
        expr = False
        for base in getattr(v, "__mro__", ()):
            if base.__module__.startswith("sqlglot.expressions") and base.__name__ in ("Expr", "Expression"):
                expr = True
        return ["type", f"{v.__module__}:{v.__qualname__}", expr]
    if isinstance(v, (types.FunctionType, types.BuiltinFunctionType, types.MethodType, staticmethod,
                      classmethod, property, types.MethodDescriptorType, types.WrapperDescriptorType)):
        return ["func"]
    if _immutable(v):
        return ["imm"]
    if type(v) in (list, set, tuple, frozenset) and all(_immutable(x) for x in v):
        return ["elems"]
    if type(v) is dict and all(_immutable(k) and _immutable(x) for k, x in v.items()):
        return ["elems"]
    return ["mut"]


def _immutable(v, depth=0):
    import enum
    if type(v) in (str, int, float, complex, bool, type(None), bytes, range) or isinstance(v, enum.Enum):
        return True
    if type(v) in (tuple, frozenset) and depth < 4:
        return all(_immutable(x, depth + 1) for x in v)
    return False


def _qualnames(tree):
    """Map each FunctionDef node to its CPython __qualname__."""
    from shared_writes import statement_children
    out = {}

    def visit(node, prefix):
        for child in statement_children(node):
            if isinstance(child, (ast.FunctionDef, ast.AsyncFunctionDef)):
                q = prefix + child.name
                out[child] = q
                visit(child, q + ".<locals>.")
            elif isinstance(child, ast.ClassDef):
                visit(child, prefix + child.name + ".")
            else:
                visit(child, prefix)
    visit(tree, "")
    return out


def build(root, params_file, out):
    import enum
    import importlib
    import pkgutil
    root = Path(root)
    sys.path.insert(0, str(root))
    importlib.import_module("unittest")  # Match the warm verifier and SQLGlot.UNITTEST.
    import sqlglot
    names = ["sqlglot"] + [m.name for m in pkgutil.walk_packages(sqlglot.__path__, "sqlglot.")]
    modules, classes, attr_kinds, instance_attrs = {}, {}, {}, set()
    for name in sorted(set(names)):
        try:
            mod = importlib.import_module(name)
        except Exception:
            continue
        modules[name] = {k: _kind(v) for k, v in vars(mod).items() if not k.startswith("__")}
    seen = set()
    for name in list(sys.modules):
        mod = sys.modules[name]
        if not name.startswith("sqlglot"):
            continue
        stack = [v for v in vars(mod).values() if isinstance(v, type)]
        while stack:
            cls = stack.pop()
            if id(cls) in seen or not cls.__module__.startswith("sqlglot"):
                continue
            seen.add(id(cls))
            key = f"{cls.__module__}:{cls.__qualname__}"
            own = {}
            for k, v in vars(cls).items():
                if k.startswith("__") and k.endswith("__"):
                    continue
                own[k] = _kind(v)
                if isinstance(v, type):
                    stack.append(v)
            if issubclass(cls, enum.Enum):
                for m in cls:
                    own[m.name] = ["imm"]
            classes[key] = {"mro": [f"{b.__module__}:{b.__qualname__}" for b in cls.__mro__],
                            "attrs": own}
            for k, kind in own.items():
                attr_kinds.setdefault(k, set()).add(kind[0])
            stack.extend(type.__subclasses__(cls))
    # Attribute names ever stored through any receiver in the package.
    for path in sorted((root / "sqlglot").rglob("*.py")):
        for node in ast.walk(ast.parse(path.read_bytes())):
            if isinstance(node, ast.Attribute) and isinstance(node.ctx, (ast.Store, ast.Del)):
                instance_attrs.add(node.attr)
            elif (isinstance(node, ast.Call) and isinstance(node.func, ast.Name)
                  and node.func.id in ("setattr", "delattr")):
                instance_attrs.add("*")
    data = json.loads(Path(params_file).read_bytes())
    if data.get("disabled"):
        Path(out).write_text(json.dumps({"disabled": True}))
        print("census: parameter census disabled")
        return
    params, written, files = data["params"], data["written"], data["processes"]
    doc = {
        "modules": modules,
        "classes": classes,
        "attr_kinds": {k: sorted(v) for k, v in attr_kinds.items()},
        "instance_attrs": sorted(instance_attrs),
        "params": params,
        "written": sorted(written),
        "processes": files,
    }
    Path(out).write_text(json.dumps(doc, sort_keys=True, separators=(",", ":")))
    print(f"census: {len(modules)} modules, {len(classes)} classes, {len(params)} functions, "
          f"{sum(1 for v in params.values() if v['shared'])} with shared parameters, "
          f"{len(written)} written classes, {files} processes")


def merge(params_dir, out):
    """Merge the per-process files written by builder/census_plugin.py (offline)."""
    params_dir = Path(params_dir)
    if (params_dir / "FAILED").exists():
        Path(out).write_text(json.dumps({"disabled": True}) + "\n")
        raise SystemExit("census: the pinned suite failed under the census; wrote a disabled census")
    params, written, files = {}, set(), 0

    def entry(key):
        path, qual, _line = key.rsplit(":", 2)
        return params.setdefault(f"{path}:{qual}", {"calls": 0, "shared": set(), "opaque": set()})
    for f in sorted(params_dir.glob("census*.json.child.*")):
        # Functions seen in forked pool workers: no heap evidence.
        for line in f.read_text().split():
            e = entry(line)
            e["calls"] += 1
            e["opaque"].add("*")
    for f in sorted(p for p in params_dir.glob("census*.json*") if ".child." not in p.name):
        files += 1
        data = json.loads(f.read_bytes())
        written.update(data["written"])
        for key, v in data["params"].items():
            e = entry(key)
            e["calls"] += v["calls"]
            e["shared"].update(v["shared"])
            e["opaque"].update(v.get("opaque", ()))
    if not files:
        raise SystemExit("census: no parameter census files")
    doc = {"params": {k: {"calls": v["calls"], "shared": sorted(v["shared"]), "opaque": sorted(v["opaque"])}
                      for k, v in sorted(params.items())},
           "written": sorted(written), "processes": files}
    Path(out).write_text(json.dumps(doc, sort_keys=True, indent=0) + "\n")
    print(f"census: {len(params)} functions, {sum(1 for v in params.values() if v['shared'])} with shared "
          f"parameters, {len(written)} written classes, {files} processes")


class Census:
    def __init__(self, doc):
        self.modules = doc["modules"]
        self.classes = doc["classes"]
        self.attr_kinds = doc["attr_kinds"]
        self.instance_attrs = set(doc["instance_attrs"])
        self.params = doc["params"]
        self.written = set(doc["written"])
        self.methods = {k for k, kinds in self.attr_kinds.items() if "func" in kinds}

    @classmethod
    def load(cls, path):
        doc = json.loads(Path(path).read_bytes())
        return None if doc.get("disabled") else cls(doc)

    def resolver(self, module, path, tree):
        return _Resolver(self, module, path, tree)


def _scope_bindings(fn):
    """Names bound directly in a function scope, with their binding nodes."""
    out = {}

    def add(name, site):
        out.setdefault(name, []).append(site)

    args = fn.args
    for a in args.posonlyargs + args.args + args.kwonlyargs:
        add(a.arg, ("param", a))
    if args.vararg:
        add(args.vararg.arg, ("vararg", args.vararg))
    if args.kwarg:
        add(args.kwarg.arg, ("varkw", args.kwarg))

    def targets(t, site):
        if isinstance(t, ast.Name):
            add(t.id, site)
        elif isinstance(t, (ast.Tuple, ast.List)):
            for e in t.elts:
                targets(e, ("opaque", None))
        elif isinstance(t, ast.Starred):
            targets(t.value, ("opaque", None))

    stack = list(fn.body)
    while stack:
        node = stack.pop()
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
            add(node.name, ("opaque", None))
            stack.extend(node.decorator_list)
            continue
        if isinstance(node, (ast.Lambda, ast.ListComp, ast.SetComp, ast.DictComp, ast.GeneratorExp)):
            continue
        if isinstance(node, ast.Assign):
            for t in node.targets:
                targets(t, ("assign", node.value) if isinstance(t, ast.Name) else ("opaque", None))
        elif isinstance(node, ast.AnnAssign) and node.value is not None:
            targets(node.target, ("assign", node.value))
        elif isinstance(node, ast.AugAssign):
            targets(node.target, ("opaque", None))
        elif isinstance(node, ast.NamedExpr):
            targets(node.target, ("assign", node.value))
        elif isinstance(node, (ast.For, ast.AsyncFor)):
            targets(node.target, ("for", node.iter) if isinstance(node.target, ast.Name) else ("opaque", None))
        elif isinstance(node, (ast.With, ast.AsyncWith)):
            for item in node.items:
                if item.optional_vars is not None:
                    targets(item.optional_vars, ("opaque", None))
        elif isinstance(node, ast.ExceptHandler) and node.name:
            add(node.name, ("opaque", None))
        elif isinstance(node, (ast.Import, ast.ImportFrom)):
            for alias in node.names:
                add((alias.asname or alias.name).split(".")[0], ("opaque", None))
        elif isinstance(node, (ast.Global, ast.Nonlocal)):
            for n in node.names:
                add(n, ("opaque", None))
        elif isinstance(node, ast.Delete):
            for t in node.targets:
                targets(t, ("opaque", None))
        elif isinstance(node, ast.match_case):
            for sub in ast.walk(node.pattern):
                for attr in ("name", "rest"):
                    if isinstance(getattr(sub, attr, None), str):
                        add(getattr(sub, attr), ("opaque", None))
        stack.extend(ast.iter_child_nodes(node))
    return out


class _Resolver:
    def __init__(self, census, module, path, tree):
        self.c = census
        self.module = module
        self.path = path
        self.tree = tree
        self._bindings = {}
        self._parents = {}
        self.reasons = []

    @cached_property
    def quals(self):
        return _qualnames(self.tree)

    # The callback used by shared_write_effect.
    def __call__(self, arg, scope, cls, node, tree):
        if tree is not self.tree or not isinstance(scope, (ast.FunctionDef, ast.AsyncFunctionDef)):
            return self._no("not in a function", arg)
        if self.sink_call(node, scope):
            return True
        if self.safe(arg, scope, set(), 0):
            return True
        return self._no("unproven", arg)

    def _no(self, why, arg):
        self.reasons.append((why, ast.unparse(arg)[:80]))
        return False

    def loads_shared(self, nodes, scope):
        """True if any added node loads a shared mutable module or class binding."""
        for n in nodes:
            if isinstance(n, ast.Attribute) and isinstance(n.ctx, ast.Load):
                kind = self.resolve(n, scope)
                if kind is not None and kind[0] in ("mut", "elems"):
                    return True
                if isinstance(n.value, ast.Name) and kind is None:
                    kinds = self.c.attr_kinds.get(n.attr, ())
                    if "mut" in kinds or "elems" in kinds:
                        return True
            elif isinstance(n, ast.Name) and isinstance(n.ctx, ast.Load):
                kind = self.resolve(n, scope)
                if kind is not None and kind[0] in ("mut", "elems"):
                    return True
        return False

    def bindings(self, scope):
        b = self._bindings.get(scope)
        if b is None:
            b = self._bindings[scope] = _scope_bindings(scope)
        return b

    def module_kind(self, name):
        return self.c.modules.get(self.module, {}).get(name)

    def class_attr(self, key, attr):
        info = self.c.classes.get(key)
        if info is None:
            return None
        for base in info["mro"]:
            b = self.c.classes.get(base)
            if b is None:
                continue
            kind = b["attrs"].get(attr)
            if kind is not None:
                if kind[0] == "imm" and f"{base}.{attr}" in self.c.written:
                    return None
                return kind
        return None

    def type_ok(self, kind):
        return kind[1] not in self.c.written

    def resolve(self, e, scope):
        """Statically resolve module and class attribute chains to a census kind."""
        if isinstance(e, ast.Name):
            if e.id in self.bindings(scope) or self.enclosing_binds(scope, e.id):
                return None
            kind = self.module_kind(e.id)
            if kind is None and hasattr(builtins, e.id) and not self.module_binds(e.id):
                return ["builtin", e.id]
            return kind
        if isinstance(e, ast.Attribute):
            base = self.resolve(e.value, scope)
            if base is None:
                return None
            if base[0] == "module":
                mod = self.c.modules.get(base[1])
                if mod is not None:
                    return mod.get(e.attr)
                return ["foreign", f"{base[1]}.{e.attr}"]
            if base[0] == "type" and self.type_ok(base):
                return self.class_attr(base[1], e.attr)
        return None

    def module_binds(self, name):
        return name in self.c.modules.get(self.module, {})

    def enclosing_binds(self, scope, name):
        # A nested function may read a binding of an enclosing function.
        inner = self.quals.get(scope, "")
        if ".<locals>." not in inner:
            return False
        for fn, q in self.quals.items():
            if fn is not scope and q and inner.startswith(q + ".<locals>."):
                if name in self.bindings(fn):
                    return True
        return False

    def kind_safe(self, kind):
        if kind is None:
            return False
        if kind[0] in ("imm", "func", "builtin"):
            return True
        if kind[0] == "type":
            return self.type_ok(kind)
        return False

    def elems_safe(self, e, scope, seen, depth):
        """Every element produced by iterating e holds no shared object."""
        if depth > MAX_DEPTH:
            return False
        if isinstance(e, (ast.Tuple, ast.List, ast.Set)):
            return all(self.safe(x, scope, seen, depth + 1) for x in e.elts)
        kind = self.resolve(e, scope)
        if kind is not None:
            return kind[0] in ("imm", "elems")
        if isinstance(e, ast.Call) and isinstance(e.func, ast.Attribute) and not e.args and not e.keywords:
            if e.func.attr in ("keys", "values", "items"):
                return self.elems_safe(e.func.value, scope, seen, depth + 1)
        if isinstance(e, (ast.ListComp, ast.SetComp, ast.GeneratorExp)):
            return self.safe(e.elt, scope, seen, depth + 1)
        if isinstance(e, ast.DictComp):
            return self.safe(e.key, scope, seen, depth + 1)
        if isinstance(e, ast.Name):
            gen = self.comp_binding(e.id, e, scope)
            if gen is not None:
                return False
            sites = self.bindings(scope).get(e.id, ())
            if sites and all(k == "assign" for k, _ in sites):
                # A local fresh container: iterate what it was built from.
                if (e.id, id(scope)) in seen:
                    return True
                return all(self.elems_safe(v, scope, seen | {(e.id, id(scope))}, depth + 1) for _, v in sites)
            return self.param_safe(e.id, scope)
        return False

    def param_safe(self, name, scope):
        """A parameter never bound to S (directly or through a direct child)."""
        sites = self.bindings(scope).get(name, ())
        if not sites or any(s[0] != "param" for s in sites):
            return False
        q = self.quals.get(scope)
        entry = self.c.params.get(f"{self.path}:{q}") if q else None
        opaque = entry.get("opaque", ()) if entry else ()
        return bool(entry and entry["calls"] and name not in entry["shared"]
                    and name not in opaque and "*" not in opaque)

    def comp_binding(self, name, at, scope):
        """The iterable of the innermost comprehension around `at` that binds name."""
        parents = self._parents.get(scope)
        if parents is None:
            parents = self._parents[scope] = {c: p for p in ast.walk(scope) for c in ast.iter_child_nodes(p)}
        node = at
        while node is not None and node is not scope:
            if isinstance(node, (ast.ListComp, ast.SetComp, ast.DictComp, ast.GeneratorExp)):
                for gen in reversed(node.generators):
                    bound = {n.id for n in ast.walk(gen.target) if isinstance(n, ast.Name)}
                    if name in bound:
                        return gen
            node = parents.get(node)
        return None

    def name_safe(self, name, scope, seen, depth, at=None):
        if at is not None:
            gen = self.comp_binding(name, at, scope)
            if gen is not None:
                # Plain targets take whole elements; destructured ones need
                # statically immutable elements.
                if isinstance(gen.target, ast.Name):
                    return self.elems_safe(gen.iter, scope, seen, depth + 1)
                kind = self.resolve(gen.iter, scope)
                return bool(kind and kind[0] in ("imm", "elems"))
        sites = self.bindings(scope).get(name)
        if sites is None:
            if self.enclosing_binds(scope, name):
                return False
            return self.kind_safe(self.resolve(ast.Name(id=name, ctx=ast.Load()), scope))
        if (name, id(scope)) in seen:
            return True  # cycle: the other bindings decide
        seen = seen | {(name, id(scope))}
        for kind, value in sites:
            if kind == "param":
                if not self.param_safe(name, scope):
                    return False
            elif kind == "assign":
                if not self.safe(value, scope, seen, depth + 1):
                    return False
            elif kind == "for":
                if not self.elems_safe(value, scope, seen, depth + 1):
                    return False
            else:
                return False
        return True

    def sink_call(self, node, scope):
        fn = node.func
        if isinstance(fn, ast.Name):
            kind = self.resolve(fn, scope)
            return bool(kind and kind[0] == "builtin" and kind[1] in PURE_FUNCS)
        if isinstance(fn, ast.Attribute):
            kind = self.resolve(fn, scope)
            if kind and kind[0] == "foreign" and kind[1] in SINK_FUNCS:
                return True
            # A builtin container method of that name; no SQLGlot class may define it.
            return fn.attr in SINK_METHODS and fn.attr not in self.c.attr_kinds
        return False

    def safe(self, e, scope, seen, depth):
        """The value of e is not, and directly holds no, shared mutable object."""
        if depth > MAX_DEPTH:
            return False
        if isinstance(e, (ast.Constant, ast.JoinedStr, ast.Lambda)):
            return True
        if isinstance(e, ast.Name):
            return self.name_safe(e.id, scope, seen, depth, at=e)
        if isinstance(e, (ast.ListComp, ast.SetComp, ast.GeneratorExp)):
            # A fresh container whose elements are the element expression.
            return self.safe(e.elt, scope, seen, depth + 1)
        if isinstance(e, ast.DictComp):
            return self.safe(e.key, scope, seen, depth + 1) and self.safe(e.value, scope, seen, depth + 1)
        if isinstance(e, ast.Starred):
            return self.elems_safe(e.value, scope, seen, depth + 1)
        if isinstance(e, (ast.Tuple, ast.List, ast.Set)):
            return all(self.safe(x, scope, seen, depth + 1) for x in e.elts)
        if isinstance(e, ast.Dict):
            return all((k is None or self.safe(k, scope, seen, depth + 1))
                       and (self.elems_safe(v, scope, seen, depth + 1) if k is None
                            else self.safe(v, scope, seen, depth + 1))
                       for k, v in zip(e.keys, e.values))
        if isinstance(e, ast.IfExp):
            return self.safe(e.body, scope, seen, depth + 1) and self.safe(e.orelse, scope, seen, depth + 1)
        if isinstance(e, ast.BoolOp):
            return all(self.safe(v, scope, seen, depth + 1) for v in e.values)
        if isinstance(e, ast.Compare) or (isinstance(e, ast.UnaryOp) and isinstance(e.op, ast.Not)):
            return True
        if isinstance(e, ast.UnaryOp):
            return self.safe(e.operand, scope, seen, depth + 1)
        if isinstance(e, ast.BinOp):
            return self.safe(e.left, scope, seen, depth + 1) and self.safe(e.right, scope, seen, depth + 1)
        if isinstance(e, ast.Attribute):
            kind = self.resolve(e, scope)
            if kind is not None:
                return self.kind_safe(kind)
            # One level below a parameter whose direct children were never shared.
            if isinstance(e.value, ast.Name):
                return self.param_safe(e.value.id, scope) and self._expr_field(e.attr)
            return False
        if isinstance(e, ast.Call):
            return self.call_safe(e, scope, seen, depth)
        return False

    def _expr_field(self, attr):
        # The parameter is an expression, list, tuple or dict whose direct
        # children were checked. These fields read the node's own args.
        return attr in EXPR_FIELDS

    def call_safe(self, e, scope, seen, depth):
        fn = e.func
        args_ok = lambda: (all(self.safe(a, scope, seen, depth + 1) for a in e.args)
                           and all(self.safe(k.value, scope, seen, depth + 1) if k.arg is not None
                                   else self.elems_safe(k.value, scope, seen, depth + 1)
                                   for k in e.keywords))
        kind = self.resolve(fn, scope)
        if kind is not None:
            if kind[0] == "builtin" and kind[1] in FRESH_BUILTIN_VALUES:
                return True
            if kind[0] == "type" and len(kind) > 2 and kind[2] and self.type_ok(kind):
                return args_ok()  # a fresh expression node holding safe children
            return False
        if isinstance(fn, ast.Attribute) and fn.attr == "from_arg_list":
            base = self.resolve(fn.value, scope)
            if base and base[0] == "type" and len(base) > 2 and base[2] and self.type_ok(base):
                return args_ok()
        if isinstance(fn, ast.Attribute) and fn.attr == "copy" and not e.args and not e.keywords:
            return self.safe(fn.value, scope, seen, depth + 1)
        return False


if __name__ == "__main__":
    if sys.argv[1] == "build":
        build(sys.argv[2], sys.argv[3], sys.argv[4])
    elif sys.argv[1] == "merge":
        merge(sys.argv[2], sys.argv[3])
