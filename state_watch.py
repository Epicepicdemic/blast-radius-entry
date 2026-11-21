"""Watch project-owned bindings that an edited function can reach by name."""
from collections import Counter, OrderedDict, defaultdict, deque
import sys
from types import ModuleType

MAPPINGS = (dict, defaultdict, OrderedDict, Counter)
CONTAINERS = MAPPINGS + (list, tuple, set, frozenset, bytearray, deque)
SCALARS = (str, bytes, int, bool, type(None), float, complex)


def fingerprint(value, seen):
    kind = type(value)
    if kind in SCALARS:
        return (kind, value)
    if kind not in CONTAINERS:
        return (kind, id(value))
    marker = id(value)
    if marker in seen:
        return (kind, marker)
    seen.add(marker)
    if kind in MAPPINGS:
        content = tuple((fingerprint(k, seen), fingerprint(v, seen)) for k, v in value.items())
        if kind is defaultdict:
            content = (id(value.default_factory), content)
    elif kind is bytearray:
        content = bytes(value)
    elif kind in (set, frozenset):
        content = frozenset(fingerprint(v, seen) for v in value)
    else:
        content = tuple(fingerprint(v, seen) for v in value)
    return (kind, marker, hash(content))


def namespaces():
    visited = set()
    def visit(owner, tag):
        if id(owner) in visited:
            return
        visited.add(id(owner))
        namespace = vars(owner)
        yield tag, namespace
        for val in tuple(namespace.values()):
            if isinstance(val, type) and getattr(val, "__module__", "").startswith("sqlglot"):
                yield from visit(val, ("cls_val", val.__module__ + "." + val.__qualname__))
    for mod, value in tuple(sys.modules.items()):
        if (mod == "sqlglot" or mod.startswith("sqlglot.")) and isinstance(value, ModuleType):
            yield from visit(value, ("mod_val", mod))


def persistent_readers(index):
    readers = {}
    for tag, namespace in namespaces():
        for name, value in namespace.items():
            if not name.startswith("__") and type(value) in CONTAINERS + SCALARS:
                mask = index.binding_readers({(*tag, name)})
                readers[name] = readers.get(name, 0) | (index.all if mask is None else mask)
    return readers


def snapshot(names):
    state = {}
    if names is None or names:
        for tag, namespace in namespaces():
            keys = (n for n in namespace if not n.startswith("__")) if names is None else names.intersection(namespace)
            for name in keys:
                val = namespace[name]
                if type(val) in CONTAINERS + SCALARS:
                    state[tag, name] = fingerprint(val, set())
    return state


def changed_readers(index, before, after):
    result = 0
    for tag, name in before.keys() | after.keys():
        if before.get((tag, name)) != after.get((tag, name)):
            mask = index.binding_readers({(*tag, name)})
            if mask is None:
                return index.all
            result |= mask
    return result
