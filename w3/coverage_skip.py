"""Narrow a plan to the pinned line coverage of edits confined to plain function bodies.

The pinned per-test line map (maps.json "lines"/"masks") records which tests executed
each line of the unmodified source. When every edit in a patch stays inside the body
of an ordinary function and leaves the rest of the module's syntax tree unchanged, a
test that executed none of the changed lines (or insertion neighbours) runs the same
code as on the pinned commit. Such a test cannot change outcome, so it may be dropped
from any plan. Anything this module cannot prove returns None, and the plan is kept.

The proof is deliberately narrow. It refuses edits whose effect can reach a test that
never executed the edited line: default arguments and other header fields, decorators,
closures and nested definitions created at call time, generator bodies, global or
nonlocal rebinding, class-creation hooks and metaclass methods, and lines the pinned
census marked as order dependent or warm-unknown.
"""

import ast
import os
import re

# Decorators that do not wrap or cache the function object.
PLAIN_DECORATORS = frozenset({"staticmethod", "classmethod", "property"})
# Methods that run during class creation or attribute binding, not when a test calls them.
CREATION_HOOKS = frozenset({
    "__init_subclass__", "__set_name__", "__class_getitem__", "__prepare__",
    "__instancecheck__", "__subclasscheck__", "__getattr__", "__getattribute__",
    "__del__", "__reduce__", "__reduce_ex__", "__getstate__", "__setstate__",
})
# Text on a changed line that can change behaviour outside the executed line itself.
RISKY_TEXT = re.compile(
    rb"\b(?:yield|await|async|nonlocal|global|lambda|def|class|locals|globals|vars|exec|eval"
    rb"|__class__|__code__|__defaults__|__kwdefaults__|__closure__|__dict__|_getframe|inspect|setattr|delattr)\b"
    rb"|^\s*@"
)
NESTED = (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef, ast.Lambda)
# Calls that mutate their receiver. Through an alias the receiver may be shared
# class or module state that later tests read without executing this line.
MUTATING_METHODS = frozenset({
    "append", "extend", "insert", "update", "setdefault", "pop", "popitem", "remove", "clear",
    "add", "discard", "sort", "reverse", "__setitem__", "__delitem__", "__setattr__", "__delattr__",
    "difference_update", "intersection_update", "symmetric_difference_update", "appendleft",
    "extendleft", "popleft", "rotate", "register", "move_to_end",
})
SCOPE_EFFECTS = (ast.Yield, ast.YieldFrom, ast.Await, ast.Global, ast.Nonlocal)


def _decorator_name(node):
    return node.id if isinstance(node, ast.Name) else None


def _functions(tree):
    """Yield (qualname, function, chain) for every def, with its enclosing nodes."""
    stack = [(tree, (), ())]
    while stack:
        node, prefix, chain = stack.pop()
        for child in ast.iter_child_nodes(node):
            if isinstance(child, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
                name = prefix + (child.name,)
                if not isinstance(child, ast.ClassDef):
                    yield name, child, chain
                stack.append((child, name, chain + (child,)))
            elif not isinstance(child, ast.Lambda):
                stack.append((child, prefix, chain))


def _plain_function(fn, chain):
    if not isinstance(fn, ast.FunctionDef) or fn.name in CREATION_HOOKS:
        return False
    if any(_decorator_name(d) not in PLAIN_DECORATORS for d in fn.decorator_list):
        return False
    for outer in chain:
        # A def inside another function is created at call time (a closure).
        if not isinstance(outer, ast.ClassDef) or outer.decorator_list or outer.keywords:
            return False
        if any(isinstance(b, ast.Name) and b.id in ("type", "ABCMeta") or
               isinstance(b, ast.Attribute) and b.attr in ("type", "ABCMeta") for b in outer.bases):
            return False
    for stmt in fn.body:
        for node in ast.walk(stmt):
            if isinstance(node, NESTED) or isinstance(node, SCOPE_EFFECTS):
                return False
    return True


# Names whose mere use can write state: reflective setters, operator-module
# mutators, namespace dictionaries and import machinery.
WRITE_NAMES = frozenset({
    "setattr", "delattr", "exec", "eval", "compile", "__import__", "vars", "globals", "locals",
    "operator", "builtins", "object", "importlib", "sys", "copyreg", "ctypes", "gc", "inspect",
    "setitem", "delitem", "iadd", "iand", "iconcat", "ifloordiv", "ilshift", "imatmul", "imod",
    "imul", "ior", "ipow", "irshift", "isub", "itruediv", "ixor", "attrgetter", "methodcaller",
})
WRITE_ATTRS = frozenset({
    "__dict__", "__setattr__", "__delattr__", "__setitem__", "__delitem__", "__class__",
    "__globals__", "__code__", "__defaults__", "__kwdefaults__", "__closure__", "__builtins__",
    "__new__", "__init_subclass__", "__set_name__", "__iadd__", "__ior__", "__iand__",
})
# Builtins that neither call back into user code with side effects nor write state.
PURE_CALLS = frozenset({
    "len", "isinstance", "issubclass", "str", "int", "float", "bool", "list", "tuple", "dict",
    "set", "frozenset", "min", "max", "sum", "sorted", "reversed", "enumerate", "zip", "range",
    "any", "all", "abs", "round", "repr", "hash", "id", "getattr", "hasattr", "callable", "divmod",
    "ord", "chr", "format", "bytes", "slice", "iter", "next",
})


def _writes(node):
    """True when the node can write state that outlives the call."""
    for sub in ast.walk(node):
        if isinstance(sub, (ast.Subscript, ast.Attribute)) and isinstance(sub.ctx, (ast.Store, ast.Del)):
            return True
        if isinstance(sub, (ast.NamedExpr, ast.Import, ast.ImportFrom, ast.Global, ast.Nonlocal)):
            return True
        if isinstance(sub, ast.Attribute) and sub.attr in WRITE_ATTRS:
            return True
        if isinstance(sub, ast.Name) and sub.id in WRITE_NAMES:
            return True
        if isinstance(sub, ast.Call) and isinstance(sub.func, ast.Attribute) and sub.func.attr in MUTATING_METHODS:
            return True
    return False


def _overlaps(node, changed_lines):
    first = getattr(node, "lineno", None)
    last = getattr(node, "end_lineno", first)
    return first is not None and any(first <= n <= last for n in changed_lines)


COMPOUND = (ast.If, ast.While, ast.For, ast.AsyncFor, ast.With, ast.AsyncWith, ast.Try, ast.Match)
if hasattr(ast, "TryStar"):
    COMPOUND += (ast.TryStar,)


def _changed_nodes(fn, changed_lines):
    """Simple statements and every expression or pattern overlapping a changed line.

    Compound statements contribute their header expressions (tests, iterables,
    context managers, except types, case patterns and guards) through the
    expression walk, without pulling in their unchanged bodies.
    """
    for node in ast.walk(fn):
        if node is fn:
            continue
        if isinstance(node, ast.stmt):
            if not isinstance(node, COMPOUND) and _overlaps(node, changed_lines):
                yield node
        elif isinstance(node, (ast.expr, ast.pattern)) and _overlaps(node, changed_lines):
            yield node


def _call_key(func):
    """Dotted text of a call target built from names and attributes, else None."""
    parts = []
    while isinstance(func, ast.Attribute):
        parts.append(func.attr)
        func = func.value
    if not isinstance(func, ast.Name):
        return None
    parts.append(func.id)
    return ".".join(reversed(parts))


def _call_keys(nodes):
    keys = set()
    for node in nodes:
        for sub in ast.walk(node):
            if isinstance(sub, ast.Call):
                keys.add(_call_key(sub.func))
    return keys


def _changed_edit_is_contained(old_fn, new_fn, removed, added, same_calls=True):
    """No changed node writes state, and the changed lines call nothing new or dropped."""
    old_nodes = list(_changed_nodes(old_fn, removed))
    new_nodes = list(_changed_nodes(new_fn, added))
    if any(_writes(n) for n in old_nodes + new_nodes):
        return False
    if not same_calls:
        return True
    # A call target that the other version of the body never calls may run code
    # (an existing helper, a metaclass method) that writes shared state.
    old_all = _call_keys(old_fn.body)
    new_all = _call_keys(new_fn.body)
    for key in _call_keys(new_nodes):
        if key is None or (key not in old_all and key not in PURE_CALLS):
            return False
    for key in _call_keys(old_nodes):
        if key is None or (key not in new_all and key not in PURE_CALLS):
            return False
    return True


def _blank(tree, names):
    """Dump the tree with the bodies of the named functions replaced."""
    for name, fn, _ in list(_functions(tree)):
        if name in names:
            fn.body = [ast.Pass()]
    return ast.dump(tree, include_attributes=False)


def _body_span(fn):
    return fn.body[0].lineno, fn.end_lineno


def change_mask(index, change):
    """Coverage mask (over index.ids) for one change, or None when it cannot be proven."""
    path = change.path
    if not (path.startswith("sqlglot/") and path.endswith(".py")):
        return None
    lines = index.data.get("lines", {}).get(path)
    if not lines or path not in index.data.get("layout", {}):
        return None
    warm = index.data.get("warm_unknown", {})
    if path in warm.get("users", ()) or path in warm.get("opens", ()):
        return None
    if not change.removed and not change.insertions:
        return None
    points = set(change.removed) | set(change.insertions) | {i + 1 for i in change.insertions}
    blocked = set(index.data.get("order_dependent_lines", {}).get(path, ())) | set(warm.get("lines", {}).get(path, ()))
    if points & blocked:
        return None
    old_lines = change.before.splitlines()
    new_lines = change.after.splitlines()
    removed_text = [old_lines[n - 1] for n in change.removed if 0 < n <= len(old_lines)]
    added_text = [new_lines[n - 1] for n in change.added if 0 < n <= len(new_lines)]
    if any(RISKY_TEXT.search(t) for t in removed_text + added_text):
        return None
    try:
        compile(change.after, path, "exec", dont_inherit=True)
        before = ast.parse(change.before, type_comments=True)
        after = ast.parse(change.after, type_comments=True)
    except (SyntaxError, ValueError):
        return None
    old_fns = {name: (fn, chain) for name, fn, chain in _functions(before)}
    new_fns = {name: (fn, chain) for name, fn, chain in _functions(after)}
    if len(old_fns) != len(list(_functions(before))) or old_fns.keys() != new_fns.keys():
        return None  # duplicate or renamed definitions

    # Every point must sit strictly inside the body of one plain function.
    owners = {}
    for point in points:
        best = None
        for name, (fn, chain) in old_fns.items():
            first, last = _body_span(fn)
            if first <= point <= last and (best is None or fn.lineno > old_fns[best][0].lineno):
                best = name
        if best is None:
            return None
        owners[point] = best
    for insertion in change.insertions:
        if owners.get(insertion) != owners.get(insertion + 1):
            return None
    touched = set(owners.values())
    spans = {name: _body_span(old_fns[name][0]) for name in touched}
    for name in touched:
        old_fn, old_chain = old_fns[name]
        new_fn, new_chain = new_fns[name]
        if not (_plain_function(old_fn, old_chain) and _plain_function(new_fn, new_chain)):
            return None
    # A changed line that writes through a subscript, attribute, walrus or mutating
    # call can change shared state that tests read without executing that line.
    same_calls = os.environ.get("COV_CALLS", "same") != "any"
    for name in touched:
        if not _changed_edit_is_contained(old_fns[name][0], new_fns[name][0], set(change.removed),
                                          set(change.added), same_calls=same_calls):
            return None
    # Outside the touched bodies, both modules must be the same syntax tree.
    if _blank(before, touched) != _blank(after, touched):
        return None

    masks = index.masks
    mask = 0
    for point in points:
        pointer = lines.get(str(point))
        if pointer is not None:
            mask |= masks[pointer]
            continue
        # A blank, comment or continuation line: use every executed line of the body.
        first, last = spans[owners[point]]
        for n in range(first, last + 1):
            pointer = lines.get(str(n))
            if pointer is not None:
                mask |= masks[pointer]
    return mask


def patch_mask(index, changes):
    """Union of change masks, or None if any change is outside the proof."""
    if not changes:
        return None
    mask = 0
    for change in changes:
        part = change_mask(index, change)
        if part is None:
            return None
        mask |= part
    return mask
