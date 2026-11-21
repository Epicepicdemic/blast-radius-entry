"""Structural admission rules. Certificates always describe a complete file edit."""
import ast
import builtins
import importlib
import json
import re
import sys
from bisect import bisect_left
from functools import lru_cache
from pathlib import Path

from mutation_summaries import module_name
from patching import overlaps
from shared_writes import bindings, has_shared_write

from table_readers import target_of


def align_directives(before, after, change):
    """Normalize only directives on the very same surviving physical source line."""
    old, new = before.type_ignores, after.type_ignores
    if len(old) != len(new) or not any(a.lineno != b.lineno for a, b in zip(old, new)):
        return after
    removed, added = sorted(change.removed), sorted(change.added)
    for a, b in zip(old, new):
        if (a.tag != b.tag or a.lineno in change.removed or b.lineno in change.added
                or a.lineno - bisect_left(removed, a.lineno) != b.lineno - bisect_left(added, b.lineno)):
            return after
    return ast.Module(body=after.body, type_ignores=old)


@lru_cache(maxsize=1)
def pinned_table_readers():
    path = Path(__file__).with_name("table_readers.json")
    if not path.is_file():
        return {}
    return {name: tuple(int(mask, 16) for mask in pair)
            for name, pair in json.loads(path.read_bytes()).items()}


def table_at(tree, points):
    if not points:
        return None
    low, high = min(points), max(points)

    def visit(body):
        for stmt in body:
            if not isinstance(stmt, ast.ClassDef) or not stmt.lineno < low <= high <= stmt.end_lineno:
                continue
            for field in stmt.body:
                table = getattr(field, "value", None)
                if (isinstance(target_of(field), ast.Name) and isinstance(table, (ast.Dict, ast.List, ast.Tuple))
                        and table.lineno <= low <= high <= table.end_lineno):
                    return field, table
            return visit(stmt.body)
        return None

    return visit(tree.body)


def imports_back(index, source, path):
    origin = index.project.data["modules"].get(source)
    if not origin or "imports" not in index.data:
        return True
    seen, stack = set(), [origin]
    while stack:
        item = stack.pop()
        if item == path:
            return True
        if item not in seen:
            seen.add(item)
            stack.extend(index.data["imports"].get(item, ()))
    return False


def passive(value, tree, declaration, index, path):
    if isinstance(value, ast.Constant):
        return True
    if isinstance(value, ast.Tuple):
        return all(passive(item, tree, declaration, index, path) for item in value.elts)
    if isinstance(value, ast.Lambda):
        return (not value.args.defaults and not any(value.args.kw_defaults)
                and not any(isinstance(n, (ast.Yield, ast.YieldFrom))
                            or isinstance(n, ast.Name) and n.id in ("__class__", "super")
                            for n in ast.walk(value.body)))
    # Require an unconditional preceding binding for evaluated names.
    if not isinstance(value, (ast.Name, ast.Attribute)):
        return False
    ref = value
    while isinstance(ref, ast.Attribute):
        ref = ref.value
    if not isinstance(ref, ast.Name):
        return False
    for owner in (n for n in ast.walk(tree) if isinstance(n, ast.ClassDef)
                  and n.lineno < declaration.lineno <= n.end_lineno):
        for stmt in owner.body:
            if stmt.lineno >= declaration.lineno:
                break
            if ref.id in bindings(stmt):
                return False
    found = False
    for stmt in reversed(tree.body):
        if stmt.lineno >= declaration.lineno:
            continue
        if isinstance(stmt, (ast.Import, ast.ImportFrom)) and any(
                (a.asname or a.name.split(".")[0]) == ref.id for a in stmt.names):
            found = True
            break
        if isinstance(stmt, ast.FunctionDef) and stmt.name == ref.id:
            found = True
            break
        if any(isinstance(n, ast.Name) and n.id == ref.id and isinstance(n.ctx, (ast.Del, ast.Store))
               for n in ast.walk(stmt)):
            return False
    if not found or value is ref:
        return found
    binding = f"m/{module_name(path)}:{ref.id}"
    # Only module dictionaries on the receiver chain. An attribute on an
    # instance or metaclass can execute a descriptor even without a Call.
    if index.project is None:
        return False
    parts = []
    while isinstance(value, ast.Attribute):
        parts.append(value.attr)
        value = value.value
    for attr in reversed(parts):
        parent = index.project.resolve(binding)
        if not parent or not parent.startswith("m/") or imports_back(index, parent[2:], path):
            return False
        binding += ":" + attr
    resolved = index.project.resolve(binding)
    return bool(resolved and resolved.startswith(("m/", "c/", "f/")))


def table_entry_mask(index, change, old, new, equal):
    left, right = table_at(old, change.removed), table_at(new, change.added)
    if not left or not right:
        return None
    decl, table = left
    new_decl, new_table = right
    if type(table) is not type(new_table):
        return None
    name = target_of(decl).id
    if isinstance(table, ast.Dict):
        if not equal(table.keys, new_table.keys):
            return None
        a, b = table.values, new_table.values
    else:
        a, b = table.elts, new_table.elts
    if len(a) != len(b):
        return None
    changed = [i for i, (v, w) in enumerate(zip(a, b)) if not equal(v, w)]
    if not changed:
        return None
    # Every difference must be a value, never an unpacked mapping or key.
    for i in changed:
        if (isinstance(table, ast.Dict) and table.keys[i] is None
                or not passive(a[i], old, decl, index, change.path)
                or not passive(b[i], new, new_decl, index, change.path)):
            return None
    saved = [(i, b[i]) for i in changed]
    for i in changed:
        b[i] = a[i]
    try:
        if not equal(old, new):
            return None
    finally:
        for i, value in saved:
            b[i] = value

    def non_null(expr):
        if isinstance(expr, (ast.Lambda, ast.Tuple)):
            return True
        if isinstance(expr, ast.Constant):
            return expr.value is not None
        if isinstance(expr, ast.Name) and index.project is not None:
            binding = index.project.resolve(f"m/{module_name(change.path)}:{expr.id}")
            return bool(binding and binding.startswith(("f/", "c/")))
        return False

    mask = 0
    for i in changed:
        v, w = a[i], b[i]
        if isinstance(table, ast.Dict):
            key = table.keys[i]
            if isinstance(key, ast.Attribute):
                mask |= index.bits("keys", "." + key.attr)
            elif isinstance(key, ast.Constant):
                mask |= index.bits("keys", repr(key.value))
            else:
                return None
        if isinstance(v, ast.Lambda) and isinstance(w, ast.Lambda) and equal(v.args, w.args):
            entries = index.point("entries", change.path, v.lineno)
            if entries:
                # Copies retain the very same function object, including in
                # subclasses. No lookup of the unchanged key executes its body.
                mask |= entries | index.bits("raw_class_reads", "*")
                continue
        record = pinned_table_readers().get(name)
        if record is None:
            return None
        readers, nullable = record
        if not (non_null(v) and non_null(w)):
            readers |= nullable
        if not readers:
            return None
        mask |= readers
    return mask


def enclosing_function(tree, added, anchors):
    """Identify a single ordinary def around every physical edit on this side."""
    points = added | anchors
    if not points:
        return None
    low, high = min(points), max(points)
    body = tree.body
    while True:
        owner = next((n for n in body if isinstance(n, (ast.ClassDef, ast.FunctionDef))
                      and n.lineno <= low and high <= n.end_lineno), None)
        if isinstance(owner, ast.FunctionDef):
            if low < owner.body[0].lineno - bool(anchors and low in anchors):
                return None
            return owner
        if owner is None:
            return None
        body = owner.body


_READ_CALLS = frozenset(("bool", "isinstance", "issubclass", "len", "zip", "enumerate",
                         "tuple", "list", "set", "dict", "str", "int", "float", "range"))
_READ_NODES = (ast.Assign, ast.AnnAssign, ast.Return, ast.If, ast.Pass, ast.Expr, ast.Name, ast.Attribute,
               ast.Subscript, ast.Slice, ast.Tuple, ast.List, ast.Set, ast.Dict, ast.Starred,
               ast.Constant, ast.Compare, ast.BoolOp, ast.UnaryOp, ast.BinOp, ast.IfExp,
               ast.ListComp, ast.SetComp, ast.DictComp, ast.comprehension, ast.Call,
               ast.keyword, ast.JoinedStr, ast.FormattedValue, ast.Load, ast.Store,
               ast.operator, ast.boolop, ast.cmpop, ast.unaryop)


def read_only_checker(fn, tree):
    """Check candidate statements against the bindings of this particular function."""
    local = {n.arg for n in ast.walk(fn.args) if isinstance(n, ast.arg)}
    local.update(n.id for n in ast.walk(fn) if isinstance(n, ast.Name) and isinstance(n.ctx, ast.Store))
    module = set()
    for stmt in tree.body:
        if isinstance(stmt, (ast.ImportFrom, ast.Import)):
            module.update(a.asname or a.name.split(".")[0] for a in stmt.names)
        elif isinstance(stmt, (ast.ClassDef, ast.FunctionDef)):
            module.add(stmt.name)
        elif isinstance(target_of(stmt), ast.Name):
            module.add(target_of(stmt).id)
    available = local | module | vars(builtins).keys()
    shadowed = None

    def check(statements):
        nonlocal shadowed
        nodes = [n for stmt in statements for n in ast.walk(stmt)]
        if any(not isinstance(n, _READ_NODES) for n in nodes):
            return False
        names = {n.id for n in nodes if isinstance(n, ast.Name) and isinstance(n.ctx, ast.Load)}
        if names - available:
            return False
        for n in nodes:
            if isinstance(n, ast.AnnAssign) and not isinstance(n.target, ast.Name):
                return False
            if isinstance(n, ast.Attribute) and (n.attr.startswith("__") or isinstance(n.ctx, ast.Store)):
                return False
            if isinstance(n, ast.Subscript) and isinstance(n.ctx, ast.Store):
                return False
            if isinstance(n, ast.Call):
                if shadowed is None:
                    shadowed = bindings(tree)
                if (not isinstance(n.func, ast.Name) or n.func.id not in _READ_CALLS
                        or n.func.id in shadowed or "*" in shadowed):
                    return False
        return True

    return check


def changed_body(old, new, equal):
    """Return both changed slices of statements, descending through unchanged if tests."""
    i = 0
    while i < min(len(old), len(new)) and equal(old[i], new[i]):
        i += 1
    j, k = len(old), len(new)
    while i < min(j, k) and equal(old[j-1], new[k-1]):
        j -= 1
        k -= 1
    a, b = old[i:j], new[i:k]
    # A header that stays identical preserves the execution of the original
    # suite. Compare the inner edit without counting untouched sibling effects.
    if a and b and type(a[-1]) is type(b[-1]) and isinstance(a[-1], (ast.If, ast.For, ast.While)):
        x, y = a[-1], b[-1]
        header_equal = all(equal(getattr(x, f), getattr(y, f)) for f in x._fields
                           if f not in ("body", "orelse"))
        if header_equal:
            l_body, r_body = changed_body(x.body, y.body, equal)
            l_else, r_else = changed_body(x.orelse, y.orelse, equal)
            if isinstance(x, (ast.For, ast.While)) and any(
                    isinstance(n, ast.Return) for stmt in l_body + r_body for n in ast.walk(stmt)):
                # An early exit skips later iterations, their header effects,
                # and the loop's else suite. Check them even when unchanged.
                def iteration(loop):
                    header = [loop.iter, loop.target] if isinstance(loop, ast.For) else [loop.test]
                    return header + loop.body + loop.orelse
                l_body, r_body = iteration(x), iteration(y)
            a, b = a[:-1] + l_body + l_else, b[:-1] + r_body + r_else
        elif isinstance(x, ast.For) and equal(x.body, y.body) and equal(x.orelse, y.orelse):
            # enumerate adds a private index but preserves order and values.
            # read_only checks the actual builtin binding on the changed side.
            def numbered(plain, numbered):
                call = numbered.iter
                unpack = numbered.target
                return (isinstance(call, ast.Call) and isinstance(call.func, ast.Name)
                        and call.func.id == "enumerate" and len(call.args) == 1 and not call.keywords
                        and equal(plain.iter, call.args[0]) and isinstance(unpack, ast.Tuple)
                        and len(unpack.elts) == 2 and isinstance(unpack.elts[0], ast.Name)
                        and equal(plain.target, unpack.elts[1])
                        and not any(isinstance(n, ast.Name) and n.id == unpack.elts[0].id
                                    for stmt in plain.body + plain.orelse for n in ast.walk(stmt)))
            if numbered(x, y):
                a, b = a[:-1] + [x.iter], b[:-1] + [y.iter, y.target.elts[0]]
            elif numbered(y, x):
                a, b = a[:-1] + [x.iter, x.target.elts[0]], b[:-1] + [y.iter]
    # An earlier return can bypass an unchanged shared write. Inspect anything
    # downstream of the changed control flow before certifying this slice.
    if any(isinstance(n, ast.Return) for stmt in a + b for n in ast.walk(stmt)):
        a, b = a + old[j:], b + new[k:]
    return a, b


def private_local_flow(changed, fn, tree, read_only):
    """Follow changed local bindings into surviving statements before admitting a body."""

    edited = {n for part in changed for n in ast.walk(part)}
    influenced = {n.id for n in edited if isinstance(n, ast.Name) and isinstance(n.ctx, ast.Store)}
    if not influenced:
        return True
    pending = []
    for stmt in ast.walk(fn):
        if stmt is fn or stmt in edited or not isinstance(stmt, ast.stmt):
            continue
        # Conditions can change whether any statement in the suite runs.
        header = [child for child in ast.iter_child_nodes(stmt) if not isinstance(child, ast.stmt)]
        reads = {n.id for item in header for n in ast.walk(item)
                 if isinstance(n, ast.Name) and isinstance(n.ctx, ast.Load)}
        pending.append((reads, stmt))
    while True:
        unresolved = []
        previous = len(influenced)
        for reads, stmt in pending:
            if influenced.isdisjoint(reads):
                unresolved.append((reads, stmt))
                continue
            if (isinstance(stmt, ast.If) and any(isinstance(n, ast.Return) for n in ast.walk(stmt))
                    and not read_only(fn.body)):
                # The edit can change which path returns, skipping an effect
                # outside this otherwise read-only conditional.
                return False
            if not read_only([stmt]):
                # A local dict assembled in the function may be filled before
                # returning it. Reuse the existing private-receiver proof.
                target = target_of(stmt)
                if (not isinstance(target, ast.Subscript) or not isinstance(target.value, ast.Name)
                        or not read_only([target.slice, stmt.value])
                        or has_shared_write(tree, {target.lineno})):
                    return False
            influenced.update(n.id for n in ast.walk(stmt)
                              if isinstance(n, ast.Name) and isinstance(n.ctx, ast.Store))
        if len(influenced) == previous:
            return True
        pending = unresolved


def function_body_mask(index, change, old, new, equal, *, local_scope=False):
    # The patch reader's balanced add/remove blocks have synthetic anchors.
    # A pure insertion at the very end of a def has only an old-side anchor.
    a = enclosing_function(old, change.removed, change.insertions)
    b = enclosing_function(new, change.added, change.deletions)
    if not a or not b or ast.get_docstring(a, clean=False) != ast.get_docstring(b, clean=False):
        return None
    saved = b.body
    b.body = a.body
    try:
        if not equal(old, new):
            return None
    finally:
        b.body = saved
    if any(isinstance(n, (ast.Global, ast.Nonlocal, ast.Yield, ast.YieldFrom))
           for fn in (a, b) for n in ast.walk(fn)):
        return None
    left, right = changed_body(a.body, b.body, equal)
    for parts, fn, tree in ((left, a, old), (right, b, new)):
        read_only = read_only_checker(fn, tree)
        if not read_only(parts) or not private_local_flow(parts, fn, tree, read_only):
            return None
    if local_scope:
        def names(fn, ctx):
            return {n.id for n in ast.walk(fn) if isinstance(n, ast.Name) and isinstance(n.ctx, ctx)}
        old_names, new_names = names(a, ast.Store), names(b, ast.Store)
        if (new_names - old_names) & names(a, ast.Load) or (old_names - new_names) & names(b, ast.Load):
            return None
    # Include the entire body, even paths that never executed a replaced line.
    # The first executable line can share a line number with a one-line def.
    first, last = a.body[0].lineno, a.end_lineno
    if any(first <= n <= last for n in index.warm_unknown.get("lines", {}).get(change.path, ())):
        return None
    return index.range_users(index.data["lines"].get(change.path, {}), first, last) or None


def unchanged_call_arguments(old, new, change, equal):
    """Pair argument slots only when the surrounding syntax and call target agree."""
    removed, added = sorted(change.removed), sorted(change.added)
    left, right = set(), set()

    def aligned(a, b):
        if type(a) is not type(b):
            return False
        if isinstance(a, list):
            return len(a) == len(b) and all(aligned(v, w) for v, w in zip(a, b))
        if not isinstance(a, ast.AST):
            return equal(a, b)
        if (getattr(a, "end_lineno", None) is not None
                and not getattr(a, "decorator_list", None)
                and not overlaps(removed, a.lineno, a.end_lineno)
                and not overlaps(added, b.lineno, b.end_lineno)):
            return True
        if isinstance(a, ast.Call):
            if (not equal(a.func, b.func)
                    or any(isinstance(x, ast.Starred) for call in (a, b) for x in call.args)
                    or any(k.arg is None for call in (a, b) for k in call.keywords)):
                return False
            old_kw = {k.arg: k.value for k in a.keywords}
            new_kw = {k.arg: k.value for k in b.keywords}
            common = old_kw.keys() & new_kw.keys()
            if [k for k in old_kw if k in common] != [k for k in new_kw if k in common]:
                return False
            pairs = list(zip(a.args, b.args)) + [(old_kw[k], new_kw[k]) for k in common]
            identical = [(v, w) for v, w in pairs if equal(v, w)]
            if (len(identical) < len(pairs) or len(a.args) != len(b.args)
                    or old_kw.keys() != new_kw.keys()):
                # Even an unchanged argument can see a different object if an
                # earlier argument rebinds a name during left-to-right evaluation.
                if any(isinstance(x, (ast.NamedExpr, ast.Yield, ast.Await))
                       for call in (a, b) for x in ast.walk(call)):
                    return False
                left.update(v for v, _ in identical)
                right.update(w for _, w in identical)
            return True
        return all(aligned(getattr(a, k), getattr(b, k)) for k in a._fields)
    if not removed or not added or not aligned(old, new):
        return set(), set()
    return left, right


@lru_cache(maxsize=1)
def pinned_imports():
    p = Path(__file__).with_name("import_readers.json")
    return json.loads(p.read_bytes()) if p.exists() else None


def import_mask(index, change, before, after, equal):
    """One unused alias added or removed, with no newly executed module initializer."""
    data = pinned_imports()
    if not data or not equal(before.type_ignores, after.type_ignores):
        return None
    module = module_name(change.path)
    left, right = before.body, after.body
    start = 0
    while start < min(len(left), len(right)) and equal(left[start], right[start]):
        start += 1
    end, stop = len(left), len(right)
    while min(end, stop) > start and equal(left[end-1], right[stop-1]):
        end -= 1
        stop -= 1

    def aliases(nodes):
        result = []
        for n in nodes:
            if isinstance(n, ast.ImportFrom) and not n.level and n.module != "__future__":
                result.extend((n.module, a.name, a.asname or a.name) for a in n.names)
            elif isinstance(n, ast.Import):
                result.extend((a.name, None, a.asname or a.name.split(".")[0]) for a in n.names)
            else:
                return None
        return result
    a, b = aliases(left[start:end]), aliases(right[start:stop])
    if a is None or b is None or abs(len(a)-len(b)) != 1:
        return None
    more, fewer = (a, b) if len(a) > len(b) else (b, a)
    delta = [x for x in more if x not in fewer]
    if len(delta) != 1 or [x for x in more if x not in delta] != fewer:
        return None
    source, symbol, name = delta[0]
    if name.startswith("_") or name == "*" or any(x[2] == name for x in fewer):
        return None
    mention = re.compile(r"(?<!\w)" + re.escape(name) + r"(?!\w)")
    unchanged = left[:start] + left[end:]
    for stmt in unchanged:
        for n in ast.walk(stmt):
            if ((isinstance(n, ast.Name) and n.id in (name, "globals", "locals", "exec", "eval", "vars"))
                    or isinstance(n, ast.alias) and (n.name == "*" or (n.asname or n.name.split(".")[0]) == name)
                    or getattr(n, "name", None) in (name, "__getattr__", "__dir__")
                    or isinstance(n, ast.Constant) and isinstance(n.value, str) and mention.search(n.value)
                    and not (isinstance(target_of(stmt), ast.Name) and target_of(stmt).id == "__all__")):
                return None
    # Only expand eager imports from predecessors that have already returned.
    # A module in the import cycle can still be partially initialized.
    prev = set()
    for n in left[:start]:
        if isinstance(n, ast.Import):
            prev.update(alias.name for alias in n.names)
        if isinstance(n, ast.ImportFrom) and n.level == 0:
            prev.add(n.module)

    def closure(roots):
        seen = set()
        stack = list(roots)
        while stack:
            m = stack.pop()
            if m == module or m in seen:
                continue
            seen.add(m)
            stack.extend(data["eager"].get(m, ()))
        return seen
    resident = source in closure(prev) or any(x[0] == source for x in fewer)
    # These built-in standard modules have no user initializer or dynamic
    # exports. Inspect their pinned interpreter's actual module dictionary.
    if source in ("itertools", "sys", "builtins") and source in sys.builtin_module_names:
        if symbol is not None and symbol not in vars(importlib.import_module(source)):
            return None
    elif not resident:
        return None
    elif symbol:
        # Removing a fromlist member can skip an implicit submodule import.
        # Require an existing definition before granting either direction.
        if symbol not in data["exports"].get(source, ()):
            return None
        # A cyclic import can expose a partially initialized module. Follow
        # the pinned overapproximation (including conditional imports) here.
        if (not index.project or not index.project.resolve(f"m/{source}:{symbol}")
                or imports_back(index, source, change.path)):
            return None
    mask = index.bits("attributes", name) | index.bits("raw_class_reads", "*")
    for key in (name, "*"):
        mask |= int(data["from"].get(module + ":" + key, "0"), 16)
    return mask
