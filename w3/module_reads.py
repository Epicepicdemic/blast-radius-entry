"""Bound a module-level edit by the pinned readers of its module.

A test that never imports a module, in its own isolated pinned run, cannot
read anything the module defines. The pinned ``users`` table records exactly
that set, including the transitive import graph, collection, lazy registry
loads and spawned interpreters. The bound therefore holds for an edit whose
import-time effects stay inside the module's own namespace and classes.

The static guard below admits only such edits. It rejects anything that can
publish state outside the module at import time: calls other than a few pure
builtins, subscripts (``__getitem__`` can insert into a foreign default dict),
attribute or subscript stores, deletes, augmented assignment, loops, ``with``
and ``try`` blocks, decorator calls, new import targets, added, removed or
re-headed classes (metaclass and ``__init_subclass__`` registration), and
module ``__getattr__``/``__dir__``/``__all__`` changes. Function and lambda
bodies are not run at import, so they are not inspected here. Their readers
are importers of the module, which the bound already contains.
"""
import ast
import os

PURE_BUILTINS = frozenset((
    "frozenset", "set", "tuple", "list", "dict", "len", "sorted", "min", "max",
    "str", "int", "bool", "float", "bytes", "range", "reversed", "enumerate", "zip",
    "isinstance", "issubclass", "repr", "abs", "any", "all", "sum", "ord", "chr",
))
MODULE_HOOKS = frozenset(("__getattr__", "__dir__", "__all__", "__path__", "__spec__", "__loader__"))


def enabled():
    val = os.environ.get("MODULE_READERS")
    if val is None or not val.strip():
        return True
    return val.strip().lower() not in ("0", "false", "no", "off")


def _bound_names(tree):
    names = set()
    for node in ast.walk(tree):
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
            names.add(node.name)
        elif isinstance(node, ast.Name) and isinstance(node.ctx, (ast.Store, ast.Del)):
            names.add(node.id)
        elif isinstance(node, ast.alias):
            names.add((node.asname or node.name).split(".")[0])
        elif isinstance(node, (ast.Global, ast.Nonlocal)):
            names.update(node.names)
        elif isinstance(node, ast.arg):
            names.add(node.arg)
    return names


def _future_annotations(tree):
    return any(isinstance(n, ast.ImportFrom) and n.module == "__future__"
               and any(a.name == "annotations" for a in n.names) for n in tree.body)


def _import_targets(tree, package):
    """Modules the pinned module imports eagerly, at its own top level."""
    out = set()
    for node in tree.body:
        if isinstance(node, ast.Import):
            out.update(a.name for a in node.names)
        elif isinstance(node, ast.ImportFrom):
            out.add(_resolve(node, package))
    return out


def _resolve(node, package):
    if not node.level:
        return node.module or ""
    base = package.split(".")
    if node.level > 1:
        base = base[:len(base) - (node.level - 1)]
    return ".".join(base + ([node.module] if node.module else []))


class _Guard:
    def __init__(self, shadowed, future, known_imports, package):
        self.shadowed = shadowed
        self.future = future
        self.known_imports = known_imports
        self.package = package
        self.calls_identical = False

    def with_calls(self):
        other = _Guard(self.shadowed, self.future, self.known_imports, self.package)
        other.calls_identical = True
        return other

    def expr(self, node):
        """True when evaluating ``node`` at import time cannot write foreign state."""
        if node is None:
            return True
        if isinstance(node, ast.Call) and self.calls_identical:
            return True
        if isinstance(node, ast.Lambda):
            return all(self.expr(d) for d in node.args.defaults + [d for d in node.args.kw_defaults if d])
        if isinstance(node, ast.Call):
            func = node.func
            pure = (isinstance(func, ast.Name) and func.id in PURE_BUILTINS and func.id not in self.shadowed) or (
                isinstance(func, ast.Attribute) and func.attr == "fromkeys"
                and isinstance(func.value, ast.Name) and func.value.id == "dict" and "dict" not in self.shadowed)
            if not pure:
                return False
            return all(self.expr(a) for a in node.args) and all(self.expr(k.value) for k in node.keywords)
        if isinstance(node, (ast.Subscript, ast.Await, ast.Yield, ast.YieldFrom, ast.NamedExpr)):
            return False
        if isinstance(node, (ast.Name, ast.Attribute)):
            if not isinstance(node.ctx, ast.Load):
                return False
            return self.expr(node.value) if isinstance(node, ast.Attribute) else True
        if isinstance(node, (ast.Constant, ast.JoinedStr, ast.FormattedValue, ast.Tuple, ast.List, ast.Set,
                             ast.Dict, ast.Starred, ast.BinOp, ast.UnaryOp, ast.BoolOp, ast.Compare,
                             ast.IfExp, ast.ListComp, ast.SetComp, ast.DictComp, ast.GeneratorExp,
                             ast.comprehension, ast.keyword, ast.Slice)):
            return all(self.expr(c) for c in ast.iter_child_nodes(node)
                       if not isinstance(c, (ast.expr_context, ast.operator, ast.unaryop, ast.boolop, ast.cmpop)))
        return False

    def annotation(self, node):
        return node is None or self.future or self.expr(node)

    def function(self, node):
        if node.name in MODULE_HOOKS:
            return False
        for d in node.decorator_list:
            if isinstance(d, ast.Call) or not self.expr(d):
                return False
        args = node.args
        defaults = args.defaults + [d for d in args.kw_defaults if d is not None]
        if not all(self.expr(d) for d in defaults):
            return False
        every = args.posonlyargs + args.args + args.kwonlyargs + [a for a in (args.vararg, args.kwarg) if a]
        return all(self.annotation(a.annotation) for a in every) and self.annotation(node.returns)

    def statement(self, node, in_class):
        if isinstance(node, (ast.Import, ast.ImportFrom)):
            if isinstance(node, ast.ImportFrom) and node.module == "__future__":
                return False
            targets = ([a.name for a in node.names] if isinstance(node, ast.Import)
                       else [_resolve(node, self.package)])
            if any(a.name == "*" for a in node.names):
                return False
            if any((a.asname or a.name) in MODULE_HOOKS for a in node.names):
                return False
            return all(t in self.known_imports for t in targets)
        if isinstance(node, ast.Pass):
            return True
        if isinstance(node, ast.Expr):
            return isinstance(node.value, ast.Constant) and isinstance(node.value.value, str)
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            return self.function(node)
        if isinstance(node, ast.Assign):
            if not all(isinstance(t, ast.Name) for t in node.targets):
                return False
            if not in_class and any(t.id in MODULE_HOOKS for t in node.targets):
                return False
            return self.expr(node.value)
        if isinstance(node, ast.AnnAssign):
            if not isinstance(node.target, ast.Name) or (not in_class and node.target.id in MODULE_HOOKS):
                return False
            return self.annotation(node.annotation) and self.expr(node.value)
        if isinstance(node, ast.If) and not in_class and _type_checking(node.test) and not node.orelse:
            # The body never runs. Its imports only satisfy static checkers.
            return True
        return False


def _type_checking(test):
    return ((isinstance(test, ast.Name) and test.id == "TYPE_CHECKING")
            or (isinstance(test, ast.Attribute) and test.attr == "TYPE_CHECKING"
                and isinstance(test.value, ast.Name) and test.value.id in ("t", "typing")))


def _changed(left, right, equal):
    start = 0
    while start < min(len(left), len(right)) and equal(left[start], right[start]):
        start += 1
    end, stop = len(left), len(right)
    while min(end, stop) > start and equal(left[end - 1], right[stop - 1]):
        end -= 1
        stop -= 1
    return left[start:end], right[start:stop]


def _same_header(a, b, equal):
    return (a.name == b.name and equal(a.bases, b.bases) and equal(a.keywords, b.keywords)
            and equal(a.decorator_list, b.decorator_list))


def _body_ok(left, right, equal, guards, in_class):
    old, new = _changed(left, right, equal)
    if len(old) == len(new):
        # Descend into classes whose headers are unchanged. Class creation then
        # publishes the same registry keys; only the class's own values move.
        pairs = list(zip(old, new))
        if all(isinstance(a, ast.ClassDef) and isinstance(b, ast.ClassDef) and _same_header(a, b, equal)
               for a, b in pairs):
            return all(_body_ok(a.body, b.body, equal, guards, True) for a, b in pairs)
    if any(isinstance(n, ast.ClassDef) for n in old + new):
        return False
    old_guard, new_guard = guards
    if len(old) == len(new) and all(_same_assignment(a, b, equal) for a, b in zip(old, new)):
        # The same calls with the same arguments run in the same order in both
        # versions, so their import-time effects on foreign state are identical.
        # Only the call-free parts of the value (keys, names, constants, lambdas)
        # differ, and those cannot write outside the module.
        old_guard, new_guard = (g.with_calls() for g in guards)
    return (all(old_guard.statement(n, in_class) for n in old)
            and all(new_guard.statement(n, in_class) for n in new))


def _calls(node):
    found = [n for n in ast.walk(node) if isinstance(n, ast.Call)]
    found.sort(key=lambda n: (n.lineno, n.col_offset, -n.end_lineno, -n.end_col_offset))
    return [ast.dump(n) for n in found]


def _same_assignment(a, b, equal):
    if type(a) is not type(b) or not isinstance(a, (ast.Assign, ast.AnnAssign)):
        return False
    targets = (a.targets, b.targets) if isinstance(a, ast.Assign) else ([a.target], [b.target])
    if not equal(*targets) or a.value is None or b.value is None:
        return False
    return _calls(a.value) == _calls(b.value)


def module_bounded(change, equal, module):
    """True when every import-time effect of the edit stays inside ``module``."""
    if not enabled() or not change.path.startswith("sqlglot/") or not change.path.endswith(".py"):
        return False
    try:
        before = ast.parse(change.before)
        after = ast.parse(change.after)
    except (SyntaxError, ValueError):
        return False
    package = module if change.path.endswith("/__init__.py") else module.rpartition(".")[0]
    for raw in (change.before, change.after):
        text = raw.decode("utf-8", "replace") if isinstance(raw, bytes) else raw
        if "importlib" in text or "__import__" in text or "sys.modules" in text:
            return False
    known = _import_targets(before, package)
    guards = tuple(_Guard(_bound_names(tree), _future_annotations(tree), known, package)
                   for tree in (before, after))
    if _future_annotations(before) != _future_annotations(after):
        return False
    return _body_ok(before.body, after.body, equal, guards, False)
