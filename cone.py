"""Extend the pinned selector with candidates for runtime verification."""
import ast
from functools import lru_cache

from change_shapes import align_directives
from patching import overlaps
from shared_writes import MUTATORS, OPERATOR_CALLS


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
    saved = [(new, new.body) for new in right.values()]
    try:
        for key, new in right.items():
            new.body = left[key].body
        if not equal(original, patched):
            return None
    finally:
        for new, body in saved:
            new.body = body
    removed, added = sorted(change.removed), sorted(change.added)
    return [(".".join(key[1::2]), fn, right[key]) for key, fn in left.items()
            if (overlaps(removed, fn.lineno, fn.end_lineno)
                or overlaps(added, right[key].lineno, right[key].end_lineno))
            and not equal(fn.body, right[key].body)]


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
                    return index.all, index.all, (), (), 0
                # A writer can be absent, skipped, or outside the run budget.
                # Keep its known persistent readers even if this fork stays clean.
                for sink in sinks_old | sinks_new:
                    protected |= shared.get(sink, 0)
            watches.update(referenced_state(before) | referenced_state(after))
        cone |= users | readers | index.bits("attributes", "__code__") | index.bits("attributes", "__closure__")
    return (cone if original == index.all else original) | protected, protected, tuple(sorted(watches)), hot, writers
