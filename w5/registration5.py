"""Class creation can publish a dialect or run inherited hooks without an explicit store."""
import ast
from functools import lru_cache
import re

REASON = 'class creation or registration hook'
FUNCTIONS = (ast.FunctionDef, ast.AsyncFunctionDef)
FACTORIES = {'type', '__build_class__', 'new_class', 'prepare_class', '_Dialect', 'DialectType'}
HOOKS = {'__init_subclass__', '__mro_entries__', '__set_name__'}
CREATION_TEXT = re.compile(rb'\b(?:class|metaclass|type|new_class|prepare_class|__build_class__|__class__|__new__|__init_subclass__|__mro_entries__|__set_name__|_Dialect|DialectType)\b')


def leaf(node):
    return node.id if isinstance(node, ast.Name) else node.attr if isinstance(node, ast.Attribute) else None


def metaclass_call(call):
    """An explicit construction hook can register a class through a computed receiver."""
    function = call.func
    name = leaf(function)
    if name in HOOKS | {'__new__', '__build_class__', 'new_class', 'prepare_class'}:
        return True
    if isinstance(function, ast.Call) and leaf(function.func) == 'getattr':
        if len(function.args) >= 2 and isinstance(function.args[1], ast.Constant):
            return function.args[1].value in HOOKS | {'__new__', '__call__', '__class__'}
    if name in ('__class__', '__call__') and isinstance(function, ast.Attribute):
        return any(isinstance(n, ast.Call) and leaf(n.func) == 'type' or
                   isinstance(n, ast.Attribute) and n.attr == '__class__' for n in ast.walk(function.value))
    return False


def sites(tree):
    """Find eager class headers, their base bindings and delayed registration sites."""
    parents = {c: n for n in ast.walk(tree) for c in ast.iter_child_nodes(n)}
    ranges = set()
    dependencies = set()
    aliases = set(FACTORIES)
    aliases.update(n.name for n in parents if isinstance(n, ast.ClassDef) and any(leaf(b) in ('type', 'ABCMeta') for b in n.bases))
    invoked = set()
    named = []
    for n in parents:
        if isinstance(n, ast.ImportFrom):
            for alias in n.names:
                if alias.name in aliases:
                    aliases.add(alias.asname or alias.name)
        if isinstance(n, (ast.Assign, ast.AnnAssign)):
            targets = n.targets if isinstance(n, ast.Assign) else [n.target]
            named.extend((t.id, n.value) for t in targets if isinstance(t, ast.Name) and n.value)
    while True:
        size = len(aliases)
        for name, value in named:
            obj = value.func if isinstance(value, ast.Call) else value
            if (isinstance(obj, ast.Name) and obj.id in aliases or isinstance(obj, ast.Attribute) and (obj.attr in ('new_class', '_Dialect', 'DialectType') or isinstance(obj.value,ast.Name) and obj.value.id=='builtins' and obj.attr=='type')):
                aliases.add(name)
        if len(aliases) == size:
            break

    def add(node, end=None):
        ranges.add((node.lineno, end if end is not None else node.end_lineno))

    def enclosing(node):
        # Any change to control flow in a function that performs registration
        # can change whether later tests see a class in the global registry.
        child = node
        while child in parents:
            parent = parents[child]
            if isinstance(parent, FUNCTIONS):
                add(parent)
                break
            if isinstance(parent, (ast.If, ast.While, ast.For, ast.AsyncFor, ast.With, ast.AsyncWith, ast.Try, ast.TryStar, ast.Match)):
                body = getattr(parent, 'body', None)
                if body:
                    add(parent, max(parent.lineno, body[0].lineno - 1))
                else:
                    add(parent, parent.lineno)
            child = parent

    for node in parents:
        if isinstance(node, ast.ClassDef) and (node.bases or node.keywords or node.decorator_list):
            headers = [*node.bases, *node.keywords, *node.decorator_list, *getattr(node, 'type_params', ())]
            header_end = max([node.lineno] + [h.end_lineno for h in headers])
            add(node, header_end)
            for h in headers:
                dependencies.update(n.id for n in ast.walk(h) if isinstance(n, ast.Name))
                add(h)
            enclosing(node)
        elif isinstance(node, FUNCTIONS):
            owner = parents.get(node)
            if node.name in HOOKS or (node.name in ('__new__', '__init__', '__prepare__') and isinstance(owner, ast.ClassDef) and owner.name in aliases):
                add(node)
        elif isinstance(node, ast.Call):
            target = leaf(node.func)
            if (metaclass_call(node) or
                    target in aliases and (len(node.args) >= 2 or node.keywords or any(isinstance(a, ast.Starred) for a in node.args)) or
                    isinstance(node.func, ast.Call) and leaf(node.func.func) in aliases):
                if target in aliases:
                    invoked.add(target)
                add(node)
                enclosing(node)
    # Rebinding a base or an alias can activate a different inherited metaclass.
    names = dependencies | (invoked - FACTORIES)
    for node, parent in parents.items():
        if (isinstance(node, ast.Name) and isinstance(node.ctx, (ast.Store, ast.Del)) and node.id in names or
                isinstance(node, ast.alias) and (node.asname or node.name.split('.')[0]) in names):
            if isinstance(parent, (ast.Assign, ast.AnnAssign, ast.Import, ast.ImportFrom)):
                add(parent)
    return tuple(sorted(ranges)), tuple(sorted(aliases - FACTORIES))


@lru_cache(32)
def pin_sites(source):
    from patching import parsed_source
    return sites(parsed_source(source))


def intersects(points, ranges):
    return any(start <= n <= end for n in points for start, end in ranges)


def changes_registry(ch):
    if not ch.path.endswith('.py'):
        return False
    cached = getattr(ch, '_registration_guard', None)
    if cached is not None:
        return cached
    from rules5 import facts
    from impact import physical_lines
    from patching import parsed_source
    from hashlib import sha256
    data = facts()
    pin = data['registration_sites'].get(ch.path) if data['digest'].get(ch.path) == sha256(ch.before).digest() else None
    if pin is None:
        pin = pin_sites(ch.before)
    old, aliases = pin
    flagged = intersects(ch.removed, old)
    if not flagged and ch.added:
        lines = physical_lines(ch.after)
        edited = '\n'.join(lines[n-1] for n in ch.added).encode()
        if (CREATION_TEXT.search(edited) or any(re.search(rb'\b' + re.escape(a.encode()) + rb'\b', edited) for a in aliases) or
                intersects(ch.insertions, old)):
            flagged = intersects(ch.added, sites(parsed_source(ch.after))[0])
    ch._registration_guard = flagged
    return flagged

def registration_bound(ix, changes):
    """Keep class publication global. An isolated missing import has a cold-family certificate."""
    if not any(changes_registry(ch) for ch in changes):
        return None
    if len(changes) == 1:
        from namespaces import deletion_bound, removed_names
        from patching import parsed_source
        ch = changes[0]
        bound = deletion_bound(ix, ch)
        if bound is not None:
            old, new = parsed_source(ch.before), parsed_source(ch.after)
            removed, _ = removed_names(old, new)
            names = {name for _, name, provider, _, _ in removed if provider}
            # Never certify a removed or rebound base, decorator or factory.
            if names and len(names) == len(removed) and '*' not in names:
                headers = [v for c in ast.walk(old) if isinstance(c, ast.ClassDef)
                           for v in (*c.bases, *c.keywords, *c.decorator_list)]
                references = {v.id for h in headers for v in ast.walk(h) if isinstance(v, ast.Name)}
                if names.isdisjoint(references | FACTORIES):
                    from bounds import facts
                    return bound | facts()['import_stress'], 'removed import and cold registry readers'
    return ix.all, REASON
