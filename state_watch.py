"""Watch project-owned bindings that an edited function can reach by name."""
from collections import Counter, OrderedDict, defaultdict, deque
import sys
from types import ModuleType

MAPPINGS = (dict, defaultdict, OrderedDict, Counter)
CONTAINERS = MAPPINGS + (list, tuple, set, frozenset, bytearray, deque)
SCALARS = (str, bytes, int, bool, type(None), float, complex)


import os

DEEP_STATE = os.environ.get("DEEP_STATE", "1").strip().lower() not in ("0", "false", "no", "off")
DEEP_WATCH = "<deep state>"  # Cone marker: a writer without a nameable sink.
deep = False  # Set by the parent for one verification; inherited by its forks.


def _project_object(kind):
    module = getattr(kind, "__module__", "") or ""
    return module == "sqlglot" or module.startswith("sqlglot.")


def _fields(value):
    """Instance fields of a project-owned object: __dict__ and slots."""
    fields = []
    d = getattr(value, "__dict__", None)
    if isinstance(d, dict):
        fields.extend(d.items())
    for klass in type(value).__mro__:
        for slot in klass.__dict__.get("__slots__", ()) or ():
            if isinstance(slot, str) and slot not in ("__dict__", "__weakref__"):
                try:
                    fields.append((slot, object.__getattribute__(value, slot)))
                except AttributeError:
                    pass
    return fields


def fingerprint(value, seen):
    kind = type(value)
    if kind in SCALARS:
        return (kind, value)
    if kind not in CONTAINERS:
        if deep and _project_object(kind) and not isinstance(value, type):
            # An expression or other project object held in shared state can be
            # changed in place (args, parent, comments, cached type, meta).
            marker = id(value)
            if marker in seen:
                return (kind, marker)
            seen.add(marker)
            parts = []
            for name, field in _fields(value):
                if name == "parent":  # Follow the tree downwards only.
                    parts.append((name, id(field)))
                else:
                    parts.append((name, fingerprint(field, seen)))
            return (kind, marker, hash(tuple(parts)))
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
                if type(val) in CONTAINERS + SCALARS or (
                        deep and _project_object(type(val)) and not isinstance(val, type)):
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
