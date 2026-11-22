"""Take one identity graph of all watched roots and attribute changes through aliases."""
from collections import defaultdict

from state_watch import CONTAINERS, MAPPINGS, SCALARS, _fields, _project_object


class Snapshot:
    def __init__(self, namespaces, deep):
        self.values = {}
        self.roots = {}
        self.nodes = {}
        self.parents = defaultdict(set)
        self.owners = defaultdict(list)
        pending = []
        seen = set()
        classes = {}
        scalar_types = frozenset(SCALARS)
        container_types = frozenset(CONTAINERS)
        mappings = frozenset(MAPPINGS)
        allowed = scalar_types | container_types

        def plain(kind):
            if kind in allowed:
                return True
            if kind not in classes:
                classes[kind] = _project_object(kind)
            return classes[kind]

        def reference(value, parent=None):
            kind = type(value)
            if kind in scalar_types:
                return (kind, value)
            marker = id(value)
            if kind in container_types or (deep and plain(kind) and not isinstance(value, type)):
                if parent is not None:
                    self.parents[marker].add(parent)
                if marker not in seen:
                    seen.add(marker)
                    pending.append(value)
            return (id(kind), marker)

        for tag, namespace in namespaces:
            for name, value in tuple(namespace.items()):
                if name.startswith('__'):
                    continue
                kind = type(value)
                if not plain(kind) or kind not in allowed and isinstance(value, type):
                    continue
                key = (*tag, name)
                self.values[key] = value
                self.roots[key] = reference(value)
                if kind not in scalar_types:
                    self.owners[id(value)].append(key)

        while pending:
            value = pending.pop()
            marker = id(value)
            kind = type(value)
            if kind in mappings:
                local = tuple((reference(k, marker), reference(v, marker)) for k, v in value.items())
                if kind is defaultdict:
                    local = id(value.default_factory), local
            elif kind is bytearray:
                local = bytes(value)
            elif kind in (set, frozenset):
                local = frozenset(reference(v, marker) for v in value)
            elif kind in container_types:
                local = tuple(reference(v, marker) for v in value)
            else:
                # Parent links on expression trees are watched by identity. Their
                # downward edges already belong to the corresponding tree roots.
                local = tuple((key, id(v) if key == 'parent' else reference(v, marker))
                              for key, v in _fields(value))
            self.nodes[marker] = (id(kind), local)

    def changed(self, other):
        keys = {k for k in self.roots.keys() | other.roots.keys()
                if self.roots.get(k) != other.roots.get(k)}
        dirty = [i for i in self.nodes.keys() | other.nodes.keys()
                 if self.nodes.get(i) != other.nodes.get(i)]
        seen = set(dirty)
        while dirty:
            marker = dirty.pop()
            for graph in (self, other):
                keys.update(graph.owners.get(marker, ()))
                for parent in graph.parents.get(marker, ()):
                    if parent not in seen:
                        seen.add(parent)
                        dirty.append(parent)
        return keys
