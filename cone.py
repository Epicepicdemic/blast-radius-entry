"""Extend the pinned selector with candidates for runtime verification."""
import ast
import os
from functools import lru_cache

from change_shapes import align_directives
from patching import overlaps
from shared_writes import MUTATORS, OPERATOR_CALLS
from state_watch import DEEP_STATE, DEEP_WATCH


def flag(name, default=True):
    val = os.environ.get(name)
    if val is None or not val.strip():
        return default
    return val.strip().lower() not in ("0", "false", "no", "off")


HEADER_EDITS = flag("HEADER_EDITS")
# Needs the verifier's deep fingerprint to observe in-place changes of objects.
CALL_WRITES = flag("CALL_WRITES", False) and DEEP_STATE
# Decorators whose change only alters how an existing call binds the function.
# The body still runs only in tests that called it at the pin.
REBINDING_DECORATORS = frozenset(("staticmethod", "classmethod", "cache", "lru_cache"))
# Attribute names through which code can observe a function header without calling it.
# SQLGlot reads __doc__ and __dict__ only on classes, and its two signature
# readers either always call the function afterwards (optimizer rules) or are
# excluded below (executor env's null_if_any can skip the call).
HEADER_READS = ("__code__", "__defaults__", "__kwdefaults__", "__annotations__", "__wrapped__",
                "__signature__", "__closure__")
HEADER_EXCLUDED_PATHS = frozenset(("sqlglot/executor/env.py",))


def _decorator_name(node):
    if isinstance(node, ast.Call):
        node = node.func
    if isinstance(node, ast.Attribute):
        return node.attr
    return node.id if isinstance(node, ast.Name) else None


def _dump(node):
    return ast.dump(node) if node is not None else None


def _plain_default(node):
    """A default whose evaluation at definition time cannot fail or share state."""
    if isinstance(node, ast.Constant):
        return True
    if isinstance(node, (ast.Tuple, ast.List, ast.Set)):
        return all(_plain_default(e) for e in node.elts)
    if isinstance(node, ast.Dict):
        return all(k is not None and _plain_default(k) and _plain_default(v) for k, v in zip(node.keys, node.values))
    if isinstance(node, ast.UnaryOp) and isinstance(node.op, (ast.USub, ast.UAdd)):
        return _plain_default(node.operand)
    return False


def header_change_allowed(old, new, deferred_annotations):
    """Signature, return and decorator changes that only alter calls of this function.

    Defaults run at definition time: each must be unchanged or a plain literal.
    Annotations run at definition time unless postponed by the future import.
    Decorators run at definition time: both lists must be equal or consist only
    of rebinding decorators. A property changes attribute reads into calls, so
    it is never admitted.
    """
    if type(old) is not type(new) or old.name != new.name:
        return False
    if [_dump(d) for d in old.decorator_list] != [_dump(d) for d in new.decorator_list]:
        names = [_decorator_name(d) for d in old.decorator_list + new.decorator_list]
        if not all(n in REBINDING_DECORATORS for n in names):
            return False
        for d in old.decorator_list + new.decorator_list:
            call = d if isinstance(d, ast.Call) else None
            if call and not all(_plain_default(a) for a in call.args + [k.value for k in call.keywords]):
                return False
    if [_dump(t) for t in getattr(old, "type_params", [])] != [_dump(t) for t in getattr(new, "type_params", [])]:
        return False
    old_defaults = {_dump(d) for d in old.args.defaults + [d for d in old.args.kw_defaults if d is not None]}
    for d in new.args.defaults + [d for d in new.args.kw_defaults if d is not None]:
        if _dump(d) not in old_defaults and not _plain_default(d):
            return False
    if not deferred_annotations:
        def annotations(fn):
            args = fn.args.posonlyargs + fn.args.args + fn.args.kwonlyargs + [a for a in (fn.args.vararg, fn.args.kwarg) if a]
            return [_dump(a.annotation) for a in args], _dump(fn.returns)
        old_ann, new_ann = annotations(old), annotations(new)
        # Each evaluated annotation must be an expression the old header already evaluated.
        known = set(old_ann[0]) | {old_ann[1]}
        if any(a is not None and a not in known for a in new_ann[0] + [new_ann[1]]):
            return False
    return True


def deferred_annotations(tree):
    return any(isinstance(n, ast.ImportFrom) and n.module == "__future__"
               and any(a.name == "annotations" for a in n.names) for n in tree.body)


def header_changed(old, new):
    return ([_dump(d) for d in old.decorator_list] != [_dump(d) for d in new.decorator_list]
            or _dump(old.args) != _dump(new.args) or _dump(old.returns) != _dump(new.returns))


@lru_cache(maxsize=32)
def functions(source):
    tree = ast.parse(source, type_comments=True)
    owners = {}

    def collect(body, prefix):
        for pos, node in enumerate(body):
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                owners[(*prefix, pos, node.name)] = node
            elif isinstance(node, ast.ClassDef):
                collect(node.body, (*prefix, pos, node.name))

    collect(tree.body, ())
    return tree, owners


def body_changes(change, equal):
    """Match complete module/class headers before using original function coverage."""
    original, left = functions(change.before)
    patched, right = functions(change.after)
    patched = align_directives(original, patched, change)
    if left.keys() != right.keys():
        return None
    # Mask only the named definitions we can match. Generic header comparison
    # also masks definitions inside an if/try block, which have no entry here.
    saved = [(new, new.body, new.args, new.decorator_list, new.returns) for new in right.values()]
    headers = set()
    if HEADER_EDITS and change.path not in HEADER_EXCLUDED_PATHS:
        deferred = deferred_annotations(original) and deferred_annotations(patched)
        removed, added = sorted(change.removed | change.insertions), sorted(change.added)
        for key, new in right.items():
            old = left[key]
            if not (overlaps(removed, first_line(old), old.body[0].lineno)
                    or overlaps(added, first_line(new), new.body[0].lineno)):
                continue  # Untouched header lines; the equality check still covers them.
            if header_changed(old, new) and header_change_allowed(old, new, deferred):
                headers.add(key)
    try:
        for key, new in right.items():
            new.body = left[key].body
            if key in headers:
                new.args, new.decorator_list, new.returns = left[key].args, left[key].decorator_list, left[key].returns
        if not equal(original, patched):
            return None
    finally:
        for new, body, args, decorators, returns in saved:
            new.body, new.args, new.decorator_list, new.returns = body, args, decorators, returns
    removed, added = sorted(change.removed), sorted(change.added)
    return [(".".join(key[1::2]), fn, right[key]) for key, fn in left.items()
            if (overlaps(removed, fn.lineno, fn.end_lineno)
                or overlaps(added, right[key].lineno, right[key].end_lineno))
            and (not equal(fn.body, right[key].body) or key in headers)]


def referenced_state(node):
    """Names visible in a potential shared write, including mutation through calls."""
    names = set()
    for child in ast.walk(node):
        if isinstance(child, ast.Name):
            names.add(child.id)
        elif isinstance(child, ast.Attribute):
            names.add(child.attr)
        elif isinstance(child, ast.Constant) and isinstance(child.value, str) and child.value.isidentifier():
            names.add(child.value)
    return names


def write_targets(fn):
    """Follow simple local aliases to names that a write might expose to later tests."""
    targets = []
    names = set()
    aliases = {}
    for node in ast.walk(fn):
        if isinstance(node, ast.Nonlocal):
            return None
        if isinstance(node, ast.Global):
            names.update(node.names)
        if isinstance(node, (ast.Assign, ast.AnnAssign, ast.NamedExpr)):
            lhs = node.targets if isinstance(node, ast.Assign) else [node.target]
            for target in lhs:
                if isinstance(target, ast.Name) and node.value is not None:
                    aliases.setdefault(target.id, []).append(node.value)
        if isinstance(node, ast.Call):
            f = node.func
            if isinstance(f, ast.Attribute) and f.attr in MUTATORS:
                targets.append(f.value)
            elif ((isinstance(f, ast.Name) and f.id in ("setattr", "delattr"))
                  or (isinstance(f, ast.Attribute) and isinstance(f.value, ast.Name)
                      and f.value.id + "." + f.attr in OPERATOR_CALLS)):
                targets.extend(node.args[:2])
        if isinstance(node, (ast.Subscript, ast.Attribute)) and isinstance(node.ctx, (ast.Store, ast.Del)):
            targets.append(node)
    while targets:
        target = targets.pop()
        if isinstance(target, ast.Subscript):
            targets.append(target.value)
        elif isinstance(target, ast.Attribute):
            names.add(target.attr)
            targets.append(target.value)
        elif isinstance(target, ast.Name):
            names.add(target.id)
            targets.extend(aliases.pop(target.id, ()))
        elif isinstance(target, ast.Call):
            # Mutating a call result may write into an arbitrary shared container.
            return None
        elif isinstance(target, ast.Constant) and isinstance(target.value, str):
            names.add(target.value)
    return names


def first_line(fn):
    return min([fn.lineno] + [d.lineno for d in fn.decorator_list])


def serialization_edit(change):
    if change.path == "sqlglot/serde.py":
        return True
    if not change.path.endswith(".py"):
        return False
    protocols = {"__reduce__", "__reduce_ex__", "__getstate__", "__setstate__"}
    for source, points in ((change.before, change.removed), (change.after, change.added)):
        if not any(name.encode() in source for name in protocols):
            continue
        lines = sorted(points)
        if any(fn.name in protocols and overlaps(lines, fn.lineno, fn.end_lineno)
               for fn in functions(source)[1].values()):
            return True
    return False


def literal_initializer(change, equal):
    old, _ = functions(change.before)
    new, _ = functions(change.after)
    if len(old.body) != len(new.body):
        return False
    for a, b in zip(old.body, new.body):
        if equal(a, b):
            continue
        if not (isinstance(a, ast.Assign) and isinstance(b, ast.Assign)
                and all(isinstance(t, ast.Name) for t in a.targets)
                and equal(a.targets, b.targets)
                and isinstance(a.value, ast.Constant) and isinstance(b.value, ast.Constant)):
            return False
    return True


def analyze(index, changes, equal, shared=None):
    effects = {}
    original, _ = index.select_changes(changes, effects=effects)
    protected = 0
    for readers in effects.values():
        if readers is not None:
            protected |= readers
    writers = 0
    watches = set()
    if not original:
        return 0, 0, (), (), 0
    hot = []
    cone = 0
    for change in changes:
        path = change.path
        readers = index.bits("opens", path)
        if path.startswith("tests/fixtures/") and path.endswith(".sql"):
            # Readers must positively observe the memory-backed fixture during
            # their own test before a pass can remove them.
            if path in index.warm_unknown.get("opens", ()):
                return index.all, index.all, (), (), 0
            cone |= readers or index.all
            hot = None  # Collection may have cached the original fixture.
            continue
        if not path.startswith("sqlglot/") or not path.endswith(".py"):
            # Native readers and spawned interpreters can bypass a Python importer.
            return original, original, (), (), 0
        if path in index.warm_unknown.get("users", ()) or path not in index.data["layout"]:
            return index.all, index.all, (), (), 0
        points = change.removed | change.insertions | {i+1 for i in change.insertions}
        if points.intersection(index.data.get("order_dependent_lines", {}).get(path, ())):
            return index.all, index.all, (), (), 0
        compile(change.after, path, "exec", dont_inherit=True)
        edits = body_changes(change, equal)
        protected |= readers
        if edits is None:
            if original == index.all:
                # An opaque initializer can publish state outside its importers.
                users = index.bits("users", path) or index.all
                if users != index.all and literal_initializer(change, equal):
                    cone |= users
                    protected |= users
                else:
                    return index.all, index.all, (), (), 0
            hot = None
            continue
        users = 0
        for name, before, after in edits:
            if HEADER_EDITS and (header_changed(before, after)
                                 or ast.get_docstring(before, clean=False) != ast.get_docstring(after, clean=False)):
                # Code that inspects a function without calling it.
                for attr in HEADER_READS:
                    readers |= index.bits("attributes", attr)
                hot = None
            if hot is not None:
                if (any(not isinstance(d, ast.Name) or d.id not in ("classmethod", "staticmethod")
                        for d in before.decorator_list)
                        or ast.get_docstring(before, clean=False) != ast.get_docstring(after, clean=False)):
                    hot = None
                else:
                    hot.append((path, name, first_line(before), first_line(after)))
            first, last = before.body[0].lineno, before.end_lineno
            unknown = index.warm_unknown.get("lines", {}).get(path, ())
            if any(first <= n <= last for n in unknown):
                return index.all, index.all, (), (), 0
            called = index.range_users(index.data["lines"].get(path, {}), first, last)
            # A function never reached in the trace lacks a usable bound.
            users |= called or index.bits("users", path) or index.all
            if path in effects and effects[path] is None:
                writers |= called or index.bits("users", path) or index.all
            if original == index.all:
                if shared is None:
                    return index.all, index.all, (), (), 0
                sinks_old, sinks_new = write_targets(before), write_targets(after)
                if sinks_old is None or sinks_new is None:
                    if not CALL_WRITES:
                        return index.all, index.all, (), (), 0
                    # A write through a call result has no nameable sink. Every
                    # test reaching the function becomes a writer that the
                    # verifier must observe in pristine and patched children.
                    writers |= called or index.bits("users", path) or index.all
                    watches.add(DEEP_WATCH)
                    sinks_old, sinks_new = sinks_old or set(), sinks_new or set()
                # A writer can be absent, skipped, or outside the run budget.
                # Keep its known persistent readers even if this fork stays clean.
                for sink in sinks_old | sinks_new:
                    protected |= shared.get(sink, 0)
            watches.update(referenced_state(before) | referenced_state(after))
        cone |= users | readers | index.bits("attributes", "__code__") | index.bits("attributes", "__closure__")
    return (cone if original == index.all else original) | protected, protected, tuple(sorted(watches)), hot, writers
