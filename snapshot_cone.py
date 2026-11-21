"""Import patched modules in a warm fork and map state deltas to test IDs."""
import abc
import ast
import atexit
import builtins
import copyreg
import importlib
from itertools import chain
import marshal
import os
from pathlib import Path
import signal
import sys
import warnings
import threading
import gc

from cone import functions
from import_state import Encoder, capture, modules, project
from mutation_summaries import module_name
from verify import Overlay, fork_masks
from shared_writes import shared_write_effect


def outer_functions(tree):
    """Match delayed bodies, including conditional and repeated declarations."""
    from collections import Counter
    result, counts = {}, Counter()

    def visit(node, prefix):
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            name = (*prefix, node.name)
            counts[name] += 1
            result[name, counts[name]] = node
            return
        if isinstance(node, ast.ClassDef):
            prefix = (*prefix, node.name)
        for child in ast.iter_child_nodes(node):
            visit(child, prefix)

    visit(tree, ())
    return result


def runtime_readers(index, changes, equal):
    """Preserve runtime write and coverage obligations beside an import edit."""
    parsed = []
    header_edit = False
    for c in changes:
        if not (c.path.startswith('sqlglot/') and c.path.endswith('.py') and c.path in index.data['layout']):
            return None
        points = c.removed | c.insertions | {i + 1 for i in c.insertions}
        if points.intersection(index.data.get('order_dependent_lines', {}).get(c.path, ())):
            return None
        old, _ = functions(c.before)
        new, _ = functions(c.after)
        header_edit |= not equal(old, new, headers_only=True)
        # A newly inserted import can shift positions of all existing definitions.
        left, right = outer_functions(old), outer_functions(new)
        parsed.append((c, old, left, new, right))
    if not header_edit:
        return None
    eager_importers = required = 0
    patched = None
    census = index.census if index.census_args and len(changes) == 1 else None
    for c, old, left, new, right in parsed:
        resolvers = {pristine: census.resolver(module_name(c.path), c.path, tree) if census else None
                     for pristine, tree in ((True, old), (False, new))}
        # Eager calls may touch opaque native caches or objects through aliases.
        # A visible change elsewhere cannot certify the absence of that effect.
        for tree, points in ((old, c.removed), (new, c.added)):
            stack = list(tree.body)
            while stack:
                node = stack.pop()
                if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda)):
                    stack.extend(node.args.defaults)
                    stack.extend(x for x in node.args.kw_defaults if x is not None)
                    stack.extend(getattr(node, 'decorator_list', ()))
                    continue
                if (isinstance(node, (ast.Call, ast.AugAssign, ast.Delete)) or
                        isinstance(node, (ast.Attribute, ast.Subscript)) and isinstance(node.ctx, ast.Store)):
                    if any(node.lineno <= line <= node.end_lineno for line in points):
                        eager_importers |= index.import_users(c.path)
                        break
                stack.extend(ast.iter_child_nodes(node))
        for name in left.keys() | right.keys():
            a, b = left.get(name), right.get(name)
            if a and b and equal(a.body, b.body):
                continue
            for fn, tree, pristine in ((a, old, True), (b, new, False)):
                if not fn:
                    continue
                first, last = fn.body[0].lineno, fn.end_lineno
                if not pristine and patched is None and index.project is not None:
                    patched = index.project.patched(changes, on_demand=index.fast)
                unbounded, bindings = shared_write_effect(
                    tree, range(first, last + 1), index.project if pristine else patched,
                    module_name(c.path), index.narrow_shared_args, index.root,
                    fresh_literals=index.touched_arguments, pinned=pristine and index.fast, census=resolvers[pristine])
                readers = index.binding_readers(bindings)
                if unbounded or readers is None:
                    return None
                required |= readers
                if pristine:
                    required |= index.range_users(index.data['lines'].get(c.path, {}), first, last)
            if a is None:
                required |= index.import_users(c.path)
    return eager_importers, required


def process_state():
    # Exclude import machinery's project-module turnover from the comparison.
    return (tuple(sorted(os.environ.items())), os.getcwd(),
            tuple((k, id(v)) for k, v in vars(sys).items() if k not in ('modules', 'path_importer_cache')),
            tuple(tuple((k, id(v)) for k, v in vars(mod).items())
                  for mod in (builtins, os, os.path, warnings, copyreg, threading, signal, gc)),
            tuple(sys.path), tuple(sys.argv), tuple(sys.warnoptions), tuple(map(id, sys.meta_path)),
            tuple(map(id, sys.path_hooks)), tuple((k, id(v)) for k, v in sys.path_importer_cache.items()),
            tuple((k, id(v)) for k, v in sys.modules.copy().items() if not project(k)),
            tuple(copyreg.dispatch_table.items()), tuple(warnings.filters), warnings.showwarning,
            atexit._ncallbacks(), threading.excepthook, threading.gettrace(), threading.getprofile(),
            abc.get_cache_token(), tuple(gc.callbacks), gc.get_threshold(), sys.getrecursionlimit(), sys.getswitchinterval(),
            sys.get_int_max_str_digits(), sys.gettrace(), sys.getprofile(),
            tuple((i, signal.getsignal(i)) for i in signal.valid_signals()))


def key_site(key):
    kind, value = key
    if kind in ('class', 'enum'):
        return '.' + value[-1].split('.')[-1]
    if kind in ('str', 'int', 'bytes', 'bool', 'NoneType'):
        return repr(value)
    return None


class ImportSnapshot:
    def __init__(self, index, root):
        self.index, self.root = index, root
        self.paths = {module_name(p): p for p in index.data['layout'] if p.startswith('sqlglot/')}
        self.ready = False

    def prepare(self, artifact=None):
        from sqlglot import Dialect
        list(Dialect.classes.values())
        artifact = artifact or Path(__file__).with_name('base_state.bin')
        built, self.tables, graph = marshal.loads(artifact.read_bytes())
        # Unordered pin inputs can construct the same dictionary in different
        # orders across interpreters. Anchor these bindings before any patch.
        self.encoder = Encoder(track=True)
        live, live_tables = capture(modules(), self.encoder)
        self.encoder.seal()
        self.base = built
        self.drift = {k: live.get(k) for k in built.keys() | live.keys() if built.get(k) != live.get(k)}
        for location, value in self.drift.items():
            if value is None:
                self.base.pop(location, None)
            else:
                self.base[location] = value
        self.tables.update(live_tables)
        self.opaque_bindings = self.encoder.opaque_bindings
        self.reverse = {m: set() for m in graph}
        for parent, deps in graph.items():
            for child in deps:
                self.reverse.setdefault(child, set()).add(parent)
        self.inherited = self.inherited_readers()
        self.order = tuple(n for n, _ in modules())
        self.ready = True

    def inherited_readers(self):
        """Project recorded receiver reads onto their pinned class hierarchy."""
        census = getattr(self.index, 'census', None)
        if census is None:
            return {}
        classes = {name.replace(':', '.'): entry for name, entry in census.classes.items()}
        readers = {}
        for key in self.index.data.get('class_reads', {}):
            receiver, attr = (key, None) if key in classes else (key.rpartition('.')[0], key.rpartition('.')[2])
            if receiver not in classes:  # Includes ordinary declaration records.
                continue
            bits = self.index.bits('class_reads', key)
            for base in classes[receiver]['mro']:
                location = (base.replace(':', '.'), attr)
                readers[location] = readers.get(location, 0) | bits
        return readers

    def users(self, mod):
        path = self.paths.get(mod)
        return self.index.import_users(path) if path is not None else self.changed_users

    def readers(self, location, keys, opaque):
        mod, owner, attr = location
        index = self.index
        users = self.users(mod)
        qualified = mod + '.' + owner if owner else mod
        field = 'arg_types' if attr == 'required_args' else attr
        direct = index.bits('class_reads', qualified + '.' + field)
        explicit = direct | index.bits('class_reads', qualified)
        generic = (index.bits('dialect_reads', attr) | index.bits('attributes', attr)
                   | index.bits('raw_class_reads', attr))
        wildcard = index.bits('raw_class_reads', '*') | index.bits('dialect_reads', '*')
        # An unqualified name or key hit alone cannot resolve the receiver.
        # The users table already includes the transitive import graph,
        # collection scopes and observed dynamic use of the defining module.
        found = explicit | (generic & users) | wildcard
        found |= self.inherited.get((qualified, field), 0) | self.inherited.get((qualified, None), 0)
        if opaque or not direct or attr.startswith('__'):
            found |= users
        for k in keys:
            name = key_site(k)
            if name is None:
                found |= users
            else:
                found |= index.bits('keys', name) & users
        return found

    def compare(self, data, tables, changed):
        mask = 0
        removed = ((loc, None) for loc in self.base if loc not in data)
        for loc, new in chain(data.items(), removed):
            old = self.base.get(loc)
            if old == new:
                if loc in self.opaque_bindings and self.opaque_bindings[loc] is not self.encoder.opaque_bindings.get(loc):
                    mask |= self.users(loc[0])
                continue
            opaque = not old or not new or old[1] or new[1]
            keys = set()
            pending = [(old[0] if old else None, new[0] if new else None)]
            visited = set()
            while pending:
                a, b = pending.pop()
                if (a, b) in visited:
                    continue
                visited.add((a, b))
                left_table = self.tables[a[1]] if a and a[0] == 'dict' else (None, ())
                right_table = tables[b[1]] if b and b[0] == 'dict' else (None, ())
                old_factory, before = left_table
                new_factory, after = right_table
                left, right = dict(before), dict(after)
                if old_factory != new_factory or tuple(left) != tuple(right):
                    opaque = True  # Iteration and default-factory readers.
                for k in left.keys() | right.keys():
                    previous, current = left.get(k), right.get(k)
                    if previous != current:
                        keys.add(k)
                        if (previous and previous[0] == 'dict') or (current and current[0] == 'dict'):
                            pending.append((previous, current))
            mask |= self.readers(loc, keys, opaque)
            if mask == self.index.all:
                break
        # Source readers and re-exports may observe physically changed text or
        # an edit to code whose Python-visible return value is unchanged.
        for mod in changed:
            mask |= self.index.bits('opens', self.paths[mod])
        return mask

    def execute(self, changes):
        changed = {module_name(c.path) for c in changes}
        self.changed_users = 0
        for c in changes:
            self.changed_users |= self.index.import_users(c.path)
        reload = set(changed)
        pending = list(changed)
        while pending:
            more = self.reverse.get(pending.pop(), set()) - reload
            reload.update(more)
            pending.extend(more)
        if 'sqlglot' in reload:
            reload.update(self.order)
        overlay = Overlay(self.root, changes)
        sys.meta_path.insert(0, overlay)
        before = process_state()
        invalid = False
        def audit(event, args):
            nonlocal invalid
            if event in ('os.putenv', 'os.unsetenv', 'sys.addaudithook', 'sys.settrace', 'sys.setprofile',
                         'os.system', 'os.fork', 'os.exec', 'os.posix_spawn', 'subprocess.Popen',
                         'socket.connect', 'os.chdir', 'os.remove', 'os.rename'):
                invalid = True
                raise RuntimeError('process-wide import effect')
            if event == 'open' and isinstance(args[2], int) and args[2] & (os.O_WRONLY | os.O_RDWR | os.O_CREAT):
                invalid = True
                raise RuntimeError('import writes outside memory')
        sys.addaudithook(audit)
        for mod in reload:
            prev = sys.modules.pop(mod, None)
            parent, _, attr = mod.rpartition('.')
            ns = vars(sys.modules[parent]) if parent in sys.modules else {}
            if prev is not None and ns.get(attr) is prev:
                del ns[attr]
        if 'sqlglot' in reload:
            importlib.import_module('sqlglot')
        for mod in self.order:
            if mod in reload and mod not in sys.modules:
                importlib.import_module(mod)
        for mod in sorted(changed):
            importlib.import_module(mod)
        from sqlglot import Dialect
        list(Dialect.classes.values())
        if invalid or process_state() != before:
            return self.index.all, self.index.all
        self.encoder.refresh(reload)
        state, tables = capture(modules(), self.encoder)
        protected = self.index.bits('attributes', '__code__') | self.index.bits('attributes', '__closure__')
        for mod in changed:
            protected |= self.index.bits('opens', self.paths[mod])
        return self.compare(state, tables, changed) | protected, protected

    def select(self, changes, deadline, cap):
        fallback = self.index.all, self.index.all
        return fork_masks(lambda: self.execute(changes), fallback, deadline, cap)
