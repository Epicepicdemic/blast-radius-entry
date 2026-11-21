"""Canonical import state of the pinned SQLGlot modules, including copied tables."""
import abc
from collections import Counter, OrderedDict, defaultdict, deque
from contextlib import contextmanager
import enum
import functools
import hashlib
import marshal
import operator
import re
import sys
import types
import weakref

PROJECT = "sqlglot"


def project(name):
    return isinstance(name, str) and (name == PROJECT or name.startswith(PROJECT + "."))


def symbol(obj):
    return (getattr(obj, "__module__", None), getattr(obj, "__qualname__", type(obj).__qualname__))


def digest(value):
    return hashlib.blake2b(marshal.dumps(value, 2), digest_size=16).digest()


SCALARS = (str, bytes, int, bool, type(None))
MAPPINGS = (dict, OrderedDict, defaultdict, Counter, types.MappingProxyType)
DESCRIPTORS = (types.WrapperDescriptorType, types.MethodDescriptorType, types.GetSetDescriptorType,
               types.MemberDescriptorType, types.ClassMethodDescriptorType)


@functools.lru_cache(maxsize=4096)
def slot_fields(kind):
    if not project(kind.__module__):
        return ()
    return tuple((base.__qualname__ + '.' + name, attr) for base in kind.__mro__
                 for name, attr in vars(base).items() if type(attr) is types.MemberDescriptorType)


MISSING = object()


def slots_of(obj, fields):
    values = []
    for _, field in fields:
        try:
            values.append(field.__get__(obj))
        except AttributeError:
            values.append(MISSING)
    return tuple(values)


def mutable_edges(obj):
    """Immediate mutable fields. Immutable parents are invalidated through their children."""
    kind = type(obj)
    if kind in MAPPINGS:
        return (tuple(obj.keys()), tuple(obj.values()),
                (obj.default_factory,) if kind is defaultdict else ())
    if kind in (list, deque, set):
        return (tuple(obj),)
    if kind is bytearray:
        return bytes(obj)
    if kind is types.FunctionType:
        return ((obj.__code__, obj.__defaults__, obj.__kwdefaults__, obj.__annotations__,
                 obj.__dict__, obj.__module__, obj.__qualname__, obj.__name__,
                 obj.__doc__, obj.__type_params__),)
    if kind is types.CellType:
        try:
            return ((obj.cell_contents,),)
        except ValueError:
            return ((),)
    if kind is property:
        return ((obj.__doc__, getattr(obj, '__name__', None)),)
    if kind in (classmethod, staticmethod, functools.partial):
        return ((obj.__dict__,),)
    if kind is weakref.ReferenceType:
        return ((obj(),),)
    if kind.__module__ in ('typing', 'typing_extensions', 'types') and hasattr(obj, '__origin__'):
        return ((obj.__origin__, getattr(obj, '__args__', None)),)
    if kind in (tuple, frozenset, types.CodeType, types.MethodType,
                types.BuiltinFunctionType, re.Pattern) + DESCRIPTORS:
        return None
    fields = slot_fields(kind)
    if fields:
        return (slots_of(obj, fields), (getattr(obj, '__dict__', None),))
    try:
        attrs = object.__getattribute__(obj, '__dict__')
    except (TypeError, AttributeError):
        return None
    return ((attrs,),)


def unchanged_edges(obj, previous):
    kind = type(obj)
    if kind in MAPPINGS:
        keys, values, factory = previous
        if len(obj) != len(keys) or (factory and obj.default_factory is not factory[0]):
            return False
        return not keys or (all(map(operator.is_, obj, keys))
                            and all(map(operator.is_, obj.values(), values)))
    if kind in (list, deque, set):
        items = previous[0]
        return len(obj) == len(items) and all(map(operator.is_, obj, items))
    edges = mutable_edges(obj)
    if isinstance(edges, bytes):
        return edges == previous
    return all(len(prior) == len(now) and all(map(operator.is_, prior, now))
               for prior, now in zip(previous, edges))


class Encoder:
    def __init__(self, track=False):
        self.memo = {}
        self.active = set()
        self.tables = {}
        self.classes = {}
        self.opaque = False
        self.track = track
        self.parents = defaultdict(set)
        self.stack = []
        self.stamps = {}
        self.opaque_bindings = {}
        self.native_objects = None

    def token(self, obj):
        kind = type(obj)
        if kind in SCALARS:
            return kind.__name__, obj
        if kind is float or kind is complex:
            return kind.__name__, marshal.dumps(obj, 2)
        if isinstance(obj, type):
            name = symbol(obj)
            if project(name[0]):
                self.classes[name] = obj
            return 'class', name
        if isinstance(obj, enum.Enum):
            return 'enum', (kind.__module__, kind.__qualname__, obj.name)
        if isinstance(obj, types.ModuleType):
            return 'module', obj.__name__
        if obj is Ellipsis or obj is NotImplemented:
            return kind.__name__, None
        key = id(obj)
        if self.track and self.stack:
            self.parents[key].add(self.stack[-1])
        cached = self.memo.get(key)
        if cached is not None:
            # Keep a reference as properties can return temporary objects.
            self.opaque |= cached[2]
            return cached[1]
        if key in self.active:
            return 'cycle', symbol(kind)
        self.active.add(key)
        if self.track:
            self.stack.append(key)
        outer = self.opaque
        self.opaque = False
        try:
            tag, data = self.encode(obj, kind)
            out = tag, digest(data)
            self.memo[key] = obj, out, self.opaque
            return out
        finally:
            self.opaque |= outer
            self.active.remove(key)
            if self.track:
                self.stack.pop()

    def seal(self):
        self.track = False
        self.native_objects = {key: obj for key, (obj, token, _) in self.memo.items()
                               if token[0] == 'opaque'}
        for key, (obj, _, _) in self.memo.items():
            edges = mutable_edges(obj)
            if edges is not None:
                self.stamps[key] = edges  # Strong references prevent address reuse in the fork.

    def refresh(self, reloaded):
        dirty = {key for key, prior in self.stamps.items()
                 if not unchanged_edges(self.memo[key][0], prior)}
        pending = list(dirty)
        while pending:
            more = self.parents.get(pending.pop(), set()) - dirty
            dirty.update(more)
            pending.extend(more)
        for key in dirty:
            self.memo.pop(key, None)
        self.classes = {key: cls for key, cls in self.classes.items() if key[0] not in reloaded}

    def encode(self, obj, kind):
        token = self.token
        if kind in MAPPINGS:
            pairs = tuple((token(k), token(v)) for k, v in obj.items())
            factory = token(obj.default_factory) if kind is defaultdict else None
            content = kind.__name__, factory, pairs
            self.tables[digest(content)] = (factory, pairs)
            return 'dict', content
        if kind in (tuple, list, deque):
            return kind.__name__, tuple(map(token, obj))
        if kind in (set, frozenset):
            return kind.__name__, tuple(sorted(map(token, obj), key=marshal.dumps))
        if kind is bytearray:
            return 'bytes', bytes(obj)
        if kind is types.CodeType:
            return 'code', (obj.co_name, obj.co_qualname, obj.co_argcount, obj.co_posonlyargcount,
                            obj.co_kwonlyargcount, obj.co_flags, obj.co_code, obj.co_exceptiontable,
                            obj.co_names, obj.co_varnames, obj.co_freevars, obj.co_cellvars,
                            tuple(map(token, obj.co_consts)))
        if kind is types.FunctionType:
            return 'function', (symbol(obj), obj.__name__, token(obj.__doc__), token(obj.__type_params__),
                                token(obj.__code__), token(obj.__defaults__),
                                token(obj.__kwdefaults__), token(obj.__annotations__), token(obj.__dict__),
                                tuple(map(token, obj.__closure__ or ())))
        if kind is types.CellType:
            try:
                return 'cell', token(obj.cell_contents)
            except ValueError:
                return 'empty-cell', None
        if kind in (classmethod, staticmethod):
            return kind.__name__, (token(obj.__func__), token(obj.__dict__))
        if kind is property:
            return 'property', tuple(map(token, (obj.fget, obj.fset, obj.fdel, obj.__doc__,
                                                 getattr(obj, '__name__', None))))
        if kind is types.MethodType:
            return 'method', (token(obj.__func__), token(obj.__self__))
        if kind in DESCRIPTORS:
            return 'descriptor', (kind.__name__, symbol(obj.__objclass__), obj.__name__)
        if kind is types.BuiltinFunctionType:
            receiver = obj.__self__
            return 'builtin', (symbol(obj), token(receiver))
        if kind is re.Pattern:
            return 'pattern', (obj.pattern, obj.flags)
        if kind is functools.partial:
            return 'partial', tuple(map(token, (obj.func, obj.args, obj.keywords, obj.__dict__)))
        if kind is weakref.ReferenceType:
            return 'weakref', token(obj())
        if kind.__module__ in ('typing', 'typing_extensions', 'types') and hasattr(obj, '__origin__'):
            return 'typing', (symbol(kind), token(obj.__origin__), token(getattr(obj, '__args__', ())))
        fields = slot_fields(kind)
        if fields:
            # A native base can keep further state outside Python member slots.
            self.opaque |= any(base is not object and base.__module__ == 'builtins'
                               for base in kind.__mro__)
            slots = tuple(('missing', None) if v is MISSING else token(v) for v in slots_of(obj, fields))
            return 'instance', (symbol(kind), tuple(name for name, _ in fields), slots,
                                token(getattr(obj, '__dict__', None)))
        # Unknown native objects retain an importer obligation.
        self.opaque = True
        try:
            attrs = object.__getattribute__(obj, '__dict__')
        except (TypeError, AttributeError):
            attrs = None
        rebound = self.native_objects is not None and self.native_objects.get(id(obj)) is not obj
        return 'opaque', (symbol(kind), rebound, token(attrs) if type(attrs) is dict else None)


def capture(modules, encoder=None):
    enc = encoder if encoder is not None else Encoder()
    state = {}
    aliases = defaultdict(list)
    enc.opaque_bindings = {}
    def namespace(mod, owner, obj):
        for name, value in tuple(vars(obj).items()):
            enc.opaque = False
            if owner is None and name == '__builtins__':
                entry = ('builtins', None)  # Watched as process state.
            elif owner is None and name in ('__loader__', '__spec__', '__cached__'):
                # The memory loader intentionally replaces the pinned loader.
                spec = vars(obj).get('__spec__')
                entry = ('loader', (mod, getattr(spec, 'origin', None)))
            elif name == '_abc_impl' and isinstance(obj, abc.ABCMeta):
                registry, positive, negative, _ = abc._get_dump(obj)
                sets = tuple(tuple(sorted((symbol(ref()) for ref in refs if ref() is not None),
                                          key=marshal.dumps)) for refs in (registry, positive, negative))
                entry = ('abc-registry', digest(sets))
            else:
                entry = enc.token(value)
            loc = mod, owner, name
            state[loc] = (entry, enc.opaque)
            if enc.opaque:
                enc.opaque_bindings[loc] = value
            if type(value) in (dict, list, set, deque, defaultdict, OrderedDict, Counter, bytearray):
                aliases[id(value)].append(loc)
    for mod, obj in modules:
        namespace(mod, None, obj)
    visited = set()
    while enc.classes.keys() - visited:
        for name in tuple(enc.classes.keys() - visited):
            cls = enc.classes[name]
            # A consumer can retain a previous class with the same qualified
            # name following a partial reload. Prefer its defining namespace.
            owner = sys.modules.get(name[0])
            for part in name[1].split('.'):
                owner = vars(owner).get(part) if isinstance(owner, (types.ModuleType, type)) else None
            if isinstance(owner, type) and symbol(owner) == name:
                cls = owner
            visited.add(name)
            namespace(*name, cls)
            if isinstance(cls, enum.EnumMeta):
                enc.opaque = False
                members = tuple((n, m.name, enc.token(m.value)) for n, m in cls.__members__.items())
                state[*name, '<enum-values>'] = (('enum-values', digest(members)), enc.opaque)
            state[*name, '<bases>'] = (('bases', tuple(map(symbol, cls.__bases__))), False)
    for group in aliases.values():
        if len(group) > 1:
            identity = digest(sorted(group, key=lambda k: (k[0], k[1] or '', k[2])))
            for mod, owner, name in group:
                state[mod, owner, '<alias>' + name] = (('alias', identity), False)
    return state, enc.tables


def modules():
    return [(n, m) for n, m in tuple(sys.modules.items()) if project(n) and isinstance(m, types.ModuleType)]


@contextmanager
def observe_initializers(graph):
    """Record runtime dependencies of module bodies, including eager helper calls."""
    import builtins
    import importlib
    from importlib.util import resolve_name
    initializers = []
    original_import = builtins.__import__
    previous_profile = sys.getprofile()

    def edge(name):
        if initializers and name in graph:
            owner = initializers[-1].f_globals['__name__']
            if name != owner:
                graph[owner].add(name)

    def profile(frame, event, result):
        if event == 'call':
            name = frame.f_globals.get('__name__')
            if name in graph:
                edge(name)
                if frame.f_code.co_name == '<module>':
                    initializers.append(frame)
        elif event == 'return':
            if frame.f_code is importlib.import_module.__code__ and isinstance(result, types.ModuleType):
                edge(result.__name__)
            if initializers and initializers[-1] is frame:
                initializers.pop()

    def observe(name, globals=None, locals=None, fromlist=(), level=0):
        result = original_import(name, globals, locals, fromlist, level)
        if initializers:
            if level:
                package = (globals or {}).get('__package__')
                if package:
                    name = resolve_name('.' * level + name, package)
            edge(name)
            for symbol in fromlist or ():
                edge(name + '.' + symbol)
        return result

    try:
        builtins.__import__ = observe
        sys.setprofile(profile)
        yield
    finally:
        sys.setprofile(previous_profile)
        builtins.__import__ = original_import


def build(path):
    import json
    from pathlib import Path
    from verify import WarmSuite
    root = Path('/sqlglot')
    maps = json.loads(Path('/app/maps.json').read_bytes())
    ids = maps['ids']
    graph = {mod: set(deps) for mod, deps in import_graph(root, maps["layout"]).items()}
    with observe_initializers(graph):
        WarmSuite(root, ids).warm()
        from sqlglot import Dialect
        list(Dialect.classes.values())
    state, tables = capture(modules())
    dependencies = {mod: sorted(deps) for mod, deps in graph.items()}
    Path(path).write_bytes(marshal.dumps((state, tables, dependencies), 4))
    print(f"Import snapshot: {len(state)} bindings, {len(tables)} distinct mappings")


def import_graph(root, paths):
    """Edges that can run during definition or module initialization."""
    import ast
    from importlib.util import resolve_name
    from mutation_summaries import module_name
    names = {module_name(p): p for p in paths if p.startswith('sqlglot/')}
    graph = {}
    for mod, path in names.items():
        package = mod if path.endswith('/__init__.py') else mod.rpartition('.')[0]
        tree = ast.parse((root / path).read_bytes())
        dependencies = set()
        stack = [tree]
        while stack:
            node = stack.pop()
            if isinstance(node, ast.Import):
                dependencies.update(a.name for a in node.names)
            elif isinstance(node, ast.ImportFrom):
                try:
                    origin = resolve_name('.' * node.level + (node.module or ''), package)
                except ImportError:
                    continue
                dependencies.add(origin)
                dependencies.update(origin + '.' + a.name for a in node.names)
            elif isinstance(node, (ast.AsyncFunctionDef, ast.FunctionDef, ast.Lambda)):
                stack.extend(ast.iter_child_nodes(node.args))
                stack.extend(getattr(node, 'decorator_list', ()))
                if getattr(node, 'returns', None):
                    stack.append(node.returns)
            else:
                stack.extend(ast.iter_child_nodes(node))
        graph[mod] = sorted((dependencies & names.keys()) - {mod})
    return graph


if __name__ == '__main__':
    build(sys.argv[1])
