"""Look for writes with potentially shared receivers on either side of a diff."""
import ast
import operator
from collections import Counter, OrderedDict, defaultdict, deque
from functools import cache
from types import MappingProxyType

FUNCTIONS = (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda)
FRESH_BUILTINS = {"dict", "list", "set", "bytearray"}

# Start with the actual method inventories. Immutable counterparts supply the
# read-only operations common to both. Keep explicit in-place protocols even
# when an immutable counterpart exposes them (mappingproxy has __ior__).
CONTAINERS = (dict, list, set, bytearray, deque, OrderedDict, defaultdict, Counter)
READ_ONLY = set.union(*(set(dir(t)) for t in (MappingProxyType, tuple, frozenset, bytes)))
READ_ONLY.update(("__alloc__", "__copy__", "__neg__", "__pos__", "elements",
                  "fromkeys", "most_common", "total"))
MUTATORS = frozenset(
    name for container in CONTAINERS for name in dir(container)
    if callable(getattr(container, name))
    and (name not in READ_ONLY or name.startswith(("__i", "__set", "__del"))
         or name.endswith("_update") or name == "__getitem__")  # defaultdict can insert
)
OPERATOR_WRITES = frozenset(
    name for name in dir(operator)
    if callable(getattr(operator, name)) and name.strip("_").startswith("i")
) | {"setitem", "delitem", "__setitem__", "__delitem__"}
PURE_BUILTINS = frozenset(
    "len iter isinstance sorted list dict tuple set frozenset str repr hash id min max "
    "sum any all enumerate zip map filter getattr hasattr type".split()
)
PURE_CALLS = {f"builtins.{name}" for name in PURE_BUILTINS}
OPERATOR_CALLS = {f"operator.{name}" for name in OPERATOR_WRITES}


def bindings(tree):
    """Overcount nested bindings: ambiguity can only withdraw a local exemption."""
    sites = {}
    for node in ast.walk(tree):
        names = ()
        if isinstance(node, ast.Name) and isinstance(node.ctx, (ast.Store, ast.Del)):
            names = (node.id,)
        elif isinstance(node, (ast.ClassDef, ast.FunctionDef, ast.AsyncFunctionDef,
                               ast.ExceptHandler, ast.MatchAs, ast.MatchStar)):
            names = (node.name,)
        elif isinstance(node, ast.MatchMapping):
            names = (node.rest,)
        elif isinstance(node, ast.arg):
            names = (node.arg,)
        elif isinstance(node, ast.alias):
            names = (node.asname or node.name.split(".")[0],)
        elif isinstance(node, (ast.Global, ast.Nonlocal)):
            names = node.names
        for name in names:
            sites.setdefault(name, []).append(node)
    return sites


def body_nodes(fn):
    pending = list(fn.body) if isinstance(fn.body, list) else [fn.body]
    while pending:
        node = pending.pop()
        yield node
        if not isinstance(node, (*FUNCTIONS, ast.ClassDef)):
            pending.extend(ast.iter_child_nodes(node))


def has_shared_write(tree, changed):
    if not changed:
        return False

    # These caches live for one side of one patch.
    bound = cache(bindings)

    def builtin(name):
        names = bound(tree)
        return name not in names and "*" not in names

    @cache
    def imported_names():
        imports = {}
        for node in ast.walk(tree):
            if isinstance(node, ast.Import):
                imports.update((alias, alias.name) for alias in node.names)
            elif isinstance(node, ast.ImportFrom) and node.level == 0:
                imports.update((alias, f"{node.module}.{alias.name}") for alias in node.names)
        return imports

    def qualified_name(fn):
        if isinstance(fn, ast.Attribute) and isinstance(fn.value, ast.Name):
            module = qualified_name(fn.value)
            return f"{module}.{fn.attr}" if module else None
        if isinstance(fn, ast.Name):
            if fn.id in PURE_BUILTINS and builtin(fn.id):
                return f"builtins.{fn.id}"
            sites = bound(tree).get(fn.id, ())
            if sites and "*" not in bound(tree):
                names = {imported_names().get(site) for site in sites}
                if len(names) == 1:
                    return names.pop()
        return None

    @cache
    def ordinary_class(cls):
        # A metaclass instance is itself a class. Unknown base classes may
        # inherit from type. Follow unambiguous, preceding local definitions.
        for base in cls.bases:
            if not isinstance(base, ast.Name):
                return False
            if base.id == "object" and builtin("object"):
                continue
            sites = bound(tree).get(base.id, ())
            if len(sites) != 1 or not isinstance(sites[0], ast.ClassDef):
                return False
            parent = sites[0]
            if parent.lineno >= cls.lineno or parent.decorator_list or not ordinary_class(parent):
                return False
        return True

    @cache
    def private_names(fn, cls):
        # Only fresh containers and the direct receiver of an instance method
        # have evidence of local ownership. A parameter or alias can hold a class.
        safe = set()
        args = fn.args.posonlyargs + fn.args.args
        if cls and args and fn.name not in {"__new__", "__init_subclass__", "__class_getitem__"}:
            if not fn.decorator_list and ordinary_class(cls):
                safe.add(args[0])
        for stmt in body_nodes(fn):
            if not isinstance(stmt, (ast.Assign, ast.AnnAssign)):
                continue
            value = stmt.value
            fresh = isinstance(value, (ast.Dict, ast.List, ast.Set, ast.DictComp,
                                       ast.ListComp, ast.SetComp))
            if isinstance(value, ast.Call) and isinstance(value.func, ast.Name):
                fresh = value.func.id in FRESH_BUILTINS and builtin(value.func.id)
            if fresh:
                safe.update(stmt.targets if isinstance(stmt, ast.Assign) else (stmt.target,))
        return {name for name, sites in bound(fn).items() if all(site in safe for site in sites)}

    def private(obj, scope, cls):
        return (isinstance(obj, ast.Name) and isinstance(scope, FUNCTIONS)
                and obj.id in private_names(scope, cls))

    def shared_target(target, scope, cls):
        if isinstance(target, (ast.Tuple, ast.List)):
            return any(shared_target(t, scope, cls) for t in target.elts)
        if isinstance(target, ast.Starred):
            return shared_target(target.value, scope, cls)
        if isinstance(target, ast.Name):
            if isinstance(scope, ast.Module):
                return True
            # Ordinary class namespace declarations have their own reader maps.
            return any(isinstance(site, (ast.Global, ast.Nonlocal))
                       for site in bound(scope).get(target.id, ()))
        if isinstance(target, (ast.Attribute, ast.Subscript)):
            return not private(target.value, scope, cls)
        return False

    def shared_argument(arg, scope, cls, unpacked=False):
        # An expression may return an alias even when the name holding it is
        # local. Exempt only known private receivers, literals and fresh displays
        # whose contents are also private. Fields of an instance may be inherited.
        if isinstance(arg, ast.Constant):
            return False
        if isinstance(arg, ast.Name):
            # Unpacking passes the elements. A private list can contain aliases.
            return unpacked or not private(arg, scope, cls)
        if isinstance(arg, ast.Starred):
            return shared_argument(arg.value, scope, cls, unpacked=True)
        if isinstance(arg, (ast.Tuple, ast.List, ast.Set)):
            return any(shared_argument(item, scope, cls) for item in arg.elts)
        if isinstance(arg, ast.Dict):
            return any((key is not None and shared_argument(key, scope, cls))
                       or shared_argument(value, scope, cls, unpacked=key is None)
                       for key, value in zip(arg.keys, arg.values))
        if isinstance(arg, ast.Call) and not arg.args and not arg.keywords:
            if isinstance(arg.func, ast.Name) and arg.func.id in FRESH_BUILTINS:
                return not builtin(arg.func.id)
        return True

    def walk(node, scope, cls=None):
        if getattr(node, "end_lineno", None) is not None and not any(node.lineno <= n <= node.end_lineno for n in changed):
            # Function/class ranges start at 'def'/'class', below decorators.
            return any(walk(d, scope, cls) for d in getattr(node, "decorator_list", ()))
        if isinstance(node, (ast.Assign, ast.Delete)):
            if any(shared_target(t, scope, cls) for t in node.targets):
                return True
        elif isinstance(node, (ast.AnnAssign, ast.AugAssign, ast.NamedExpr)):
            if shared_target(node.target, scope, cls):
                return True
            # An in-place operator can modify an inherited field before storing it.
            if isinstance(node, ast.AugAssign) and not private(node.target, scope, cls):
                return True
        elif isinstance(node, (ast.Attribute, ast.Subscript)) and isinstance(node.ctx, ast.Store):
            if shared_target(node, scope, cls):  # also for 'for' and 'with' targets
                return True
        elif isinstance(node, ast.Call):
            fn = node.func
            callee = qualified_name(fn)
            name = fn.id if isinstance(fn, ast.Name) else getattr(fn, "attr", None)
            if callee in OPERATOR_CALLS or name in ("setattr", "delattr"):
                if not node.args or not private(node.args[0], scope, cls):
                    return True
            elif isinstance(fn, ast.Attribute) and fn.attr in MUTATORS:
                if not private(fn.value, scope, cls):
                    return True
            if callee not in PURE_CALLS:
                if any(shared_argument(arg, scope, cls) for arg in node.args):
                    return True
                if any(shared_argument(kw.value, scope, cls, unpacked=kw.arg is None) for kw in node.keywords):
                    return True

        if isinstance(node, (*FUNCTIONS, ast.ClassDef)):
            # Defaults, annotations, bases and decorators run in the outer scope.
            for field, value in ast.iter_fields(node):
                children = value if isinstance(value, list) else (value,)
                for child in children:
                    if not isinstance(child, ast.AST):
                        continue
                    if field == "body":
                        method = isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef))
                        owner = scope if method and isinstance(scope, ast.ClassDef) else None
                        if walk(child, node, owner):
                            return True
                    elif walk(child, scope, cls):
                        return True
            return False
        return any(walk(child, scope, cls) for child in ast.iter_child_nodes(node))

    return walk(tree, tree)
