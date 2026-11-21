"""Build and query argument-mutation summaries without importing SQLGlot or a patch.

References keep their import path until lookup. This lets the patched view resolve
even an unchanged caller against a replaced or newly shadowed dependency.
The JSON graph uses m/ for modules, c/ and f/ for definitions at source
coordinates, b/ for builtins and colon-separated attribute lookups. A mask's
bits follow parameters(signature), including the two variadic parameters.
"""
import ast
from collections import defaultdict, deque
import json
from pathlib import Path
import time

from shared_writes import FUNCTIONS, MUTATORS, PURE_BUILTINS
from patching import overlaps

SCOPES = (*FUNCTIONS, ast.ClassDef)
MISSING = object()
RETAINING_BUILTINS = frozenset("iter sorted list dict tuple set frozenset min max sum "
                               "enumerate zip map filter getattr type".split())


MAX_PARAMETERS = 128
FUNCTION_WORK = 65_536
PATCH_WORK = 250_000


class AnalysisLimit(ValueError):
    pass


class WorkBudget:
    """Bound AST visits, alias expansions and graph propagation independently of timing."""

    def __init__(self, limit):
        self.remaining = limit

    def spend(self, units):
        self.remaining -= units
        if self.remaining < 0:
            raise AnalysisLimit("mutation analysis work limit")

    def visit(self, nodes):
        for node in nodes:
            self.spend(1)
            yield node


def module_name(path):
    parts = Path(path).with_suffix("").parts
    return ".".join(parts[:-1] if parts[-1] == "__init__" else parts)


def members(node):
    """Yield this scope's nodes, visiting nested headers but not nested bodies."""
    body = node.body if isinstance(node.body, list) else [node.body]
    pending = list(body)
    while pending:
        child = pending.pop()
        yield child
        if isinstance(child, SCOPES):
            for field, value in ast.iter_fields(child):
                if field != "body":
                    pending.extend(item for item in (value if isinstance(value, list) else [value])
                                   if isinstance(item, ast.AST))
        else:
            pending.extend(ast.iter_child_nodes(child))


def signature(fn):
    args = fn.args
    return ([a.arg for a in args.posonlyargs + args.args], len(args.posonlyargs),
            [a.arg for a in args.kwonlyargs], args.vararg and args.vararg.arg,
            args.kwarg and args.kwarg.arg, len(args.defaults),
            [a.arg for a, default in zip(args.kwonlyargs, args.kw_defaults) if default is None])


def parameters(sig):
    positional, _, named, star, double_star = sig[:5]
    return positional + named + [n for n in (star, double_star) if n is not None]


def actuals(call):
    for arg in call.args:
        yield ("*", arg.value) if isinstance(arg, ast.Starred) else ("", arg)
    for kw in call.keywords:
        yield kw.arg or "**", kw.value


def bind(sig, arguments):
    """For each actual, return the bitset of slots it can reach. Never guess an unpack."""
    positional, posonly, named, star, double_star, defaults, required_keys = sig
    names = parameters(sig)
    if len(names) > MAX_PARAMETERS:
        return None
    varargs = 1 << names.index(star) if star else 0
    kwargs = 1 << names.index(double_star) if double_star else 0
    keyword_slots = {name: 1 << i for i, name in enumerate(positional + named) if i >= posonly}
    cursor = 0
    shifted = expanded = False
    given = 0
    result = []
    for kind, value in arguments:
        if kind in ("", "*"):
            if kind == "*" or shifted:
                slots = ((1 << len(positional)) - (1 << min(cursor, len(positional)))) | varargs
                shifted = True
            elif cursor < len(positional):
                slots = 1 << cursor
                given |= slots
            else:
                slots = varargs
            if kind == "":
                cursor += 1
        elif kind == "**":
            slots = sum(keyword_slots.values()) | kwargs
            expanded = True
        else:
            slots = keyword_slots.get(kind, kwargs)
            if slots & given:
                return None
            if kind in keyword_slots:
                given |= slots
        if not slots:
            return None
        result.append((value, slots))
    required = ((1 << (len(positional) - defaults)) - 1) | sum(keyword_slots[k] for k in required_keys)
    if not (shifted or expanded) and required & ~given:
        return None
    return result


def combine(values):
    mask = 0
    for value in values:
        mask |= value
    return mask


class Source:
    """Lexical bindings and syntax of one file in one version of the project."""

    def __init__(self, module, tree, package=False, budget=None):
        self.module = module
        self.tree = tree
        self.package = module if package else module.rpartition(".")[0]
        self.parents = {}
        self.scopes = {}
        self.functions = {}
        self.namespaces = {}
        # A write declared in a descendant can replace a binding in an ancestor.
        self.indirect = set()
        self.attribute_writes = set()
        opaque = False
        nodes = ast.walk(tree)
        for node in budget.visit(nodes) if budget is not None else nodes:
            if isinstance(node, (ast.Global, ast.Nonlocal)):
                self.indirect.update(node.names)
            elif isinstance(node, ast.Attribute) and isinstance(node.ctx, (ast.Store, ast.Del)):
                self.attribute_writes.add(node.attr)
            elif isinstance(node, ast.Call):
                name = (node.func.id if isinstance(node.func, ast.Name)
                        else getattr(node.func, "attr", None))
                if name in ("exec", "globals", "locals"):
                    opaque = True
                if name in ("setattr", "delattr", "__setattr__", "__delattr__"):
                    # Bound dunders take the name first. For an unbound dunder
                    # either candidate can be dynamic; withdraw the proof.
                    index = 1 if name in ("setattr", "delattr") else 0
                    arg = node.args[index] if len(node.args) > index else None
                    self.attribute_writes.add(arg.value if isinstance(arg, ast.Constant)
                                              and isinstance(arg.value, str) else "*")
            elif isinstance(node, ast.Subscript) and isinstance(node.ctx, (ast.Store, ast.Del)):
                if isinstance(node.value, ast.Attribute) and node.value.attr in (
                        "__dict__", "__globals__", "modules"):
                    self.attribute_writes.add("*")
        if self.attribute_writes.intersection({"__code__", "__class__", "__bases__",
                                               "__defaults__", "__kwdefaults__"}):
            self.attribute_writes.add("*")
        self._scope(tree, None, "m/" + module)
        self.scopes[tree].update(dict.fromkeys(self.indirect))
        if opaque:
            self.scopes[tree]["<dynamic>"] = None
        for scope, names in self.scopes.items():
            for name, ref in names.items():
                if isinstance(ref, ast.AST):
                    names[name] = self.reference(ref, scope, {(scope, name)})

    def _scope(self, scope, parent, key):
        self.parents[scope] = parent
        names = {}
        self.scopes[scope] = names
        if isinstance(scope, (ast.Module, ast.ClassDef)):
            self.namespaces[key] = names
        if isinstance(scope, FUNCTIONS):
            names.update(dict.fromkeys(parameters(signature(scope))))
        for param in getattr(scope, "type_params", ()):
            names[param.name] = None
        body = set(scope.body) if isinstance(scope.body, list) else {scope.body}

        simple_aliases = {n.targets[0]: n.value for n in body if isinstance(n, ast.Assign)
                          and len(n.targets) == 1 and isinstance(n.targets[0], ast.Name)
                          and isinstance(n.value, (ast.Name, ast.Attribute, ast.Lambda))}

        def add(name, ref=None):
            if name:
                if name in self.indirect or (name in names and names[name] != ref):
                    ref = None
                names[name] = ref

        for node in members(scope):
            if isinstance(node, SCOPES):
                is_class = isinstance(node, ast.ClassDef)
                child_key = f"{'c' if is_class else 'f'}/{self.module}@{node.lineno},{node.col_offset}"
                if not is_class:
                    self.functions[child_key] = node
                if not isinstance(node, ast.Lambda):
                    # Custom metaclasses and inherited descriptors make even a
                    # class-qualified method lookup dynamic.
                    direct = node in body and not node.decorator_list
                    if is_class and (node.bases or node.keywords):
                        direct = False
                    add(node.name, child_key if direct else None)
                self._scope(node, scope, child_key)
            elif isinstance(node, ast.Import):
                for alias in node.names:
                    name = alias.asname or alias.name.split(".")[0]
                    module = alias.name if alias.asname else name
                    add(name, "m/" + module if node in body else None)
            elif isinstance(node, ast.ImportFrom):
                parts = self.package.split(".") if self.package else []
                valid = node.level <= len(parts)
                prefix = parts[:len(parts) - node.level + 1] if node.level and valid else []
                module = ".".join(prefix + ([node.module] if node.module else []))
                for alias in node.names:
                    if alias.name == "*":
                        names.setdefault("*", []).append(module if node in body and valid else "")
                    else:
                        add(alias.asname or alias.name,
                            f"m/{module}:{alias.name}" if node in body and valid else None)
            elif isinstance(node, ast.Name) and isinstance(node.ctx, (ast.Store, ast.Del)):
                ref = simple_aliases.get(node)
                if isinstance(ref, ast.Lambda):
                    ref = f"f/{self.module}@{ref.lineno},{ref.col_offset}"
                add(node.id, ref)
            elif isinstance(node, (ast.ExceptHandler, ast.MatchAs, ast.MatchStar)):
                add(node.name)
            elif isinstance(node, ast.MatchMapping):
                add(node.rest)
            elif isinstance(node, (ast.Global, ast.Nonlocal)):
                for name in node.names:
                    add(name)

    def reference(self, expr, scope, seen=frozenset()):
        if len(seen) >= 64:
            return None
        attrs = []
        while isinstance(expr, ast.Attribute):
            if len(attrs) >= 64:
                return None
            attrs.append(expr.attr)
            expr = expr.value
        if not isinstance(expr, ast.Name) or expr.id in self.indirect:
            return None
        name = expr.id
        local = scope
        while local is not self.tree:
            names = self.scopes[local]
            if name in names:
                # Class-body comprehensions can skip the class namespace.
                ref = None if isinstance(local, ast.ClassDef) else names[name]
                if isinstance(ref, ast.AST):
                    if (local, name) in seen:
                        return None
                    ref = self.reference(ref, local, seen | {(local, name)})
                break
            local = self.parents[local]
            while isinstance(local, ast.ClassDef):
                local = self.parents[local]
        else:
            names = self.scopes[self.tree]
            if name in PURE_BUILTINS and name not in names and "*" not in names and "<dynamic>" not in names:
                ref = "b/" + name
            else:
                ref = "m/" + self.module + ":" + name
        return ":".join([ref, *reversed(attrs)]) if ref else None


def stored_names(target):
    if isinstance(target, ast.Name):
        yield target.id
    elif isinstance(target, ast.Starred):
        yield from stored_names(target.value)
    elif isinstance(target, (ast.Tuple, ast.List)):
        for item in target.elts:
            yield from stored_names(item)


def function_facts(source, fn, patch_budget=None):
    """An oversized function has an opaque summary for every parameter."""
    sig = signature(fn)
    count = len(parameters(sig))
    if count <= MAX_PARAMETERS:
        budget = WorkBudget(FUNCTION_WORK)
        try:
            return _function_facts(source, fn, sig, budget)
        except AnalysisLimit:
            pass
        finally:
            if patch_budget is not None:
                patch_budget.spend(FUNCTION_WORK - budget.remaining)
    return [sig, (1 << count) - 1, []]


def _function_facts(source, fn, sig, budget):
    """Direct writes and call constraints, in terms of the caller's parameters."""
    initial = {name: 1 << i for i, name in enumerate(parameters(sig))}
    aliases = defaultdict(set)
    reads = {}

    def references(node):
        if node not in reads:
            reads[node] = {n.id for n in budget.visit(ast.walk(node)) if isinstance(n, ast.Name)
                           and isinstance(n.ctx, ast.Load)} if node is not None else set()
        return reads[node]

    effects = set()
    calls = []
    # Flow-insensitive union preserves alternatives at joins and around loops.
    def assign(target, rhs):
        for name in stored_names(target):
            budget.spend(1 + len(rhs))
            aliases[name].update(rhs)
            if name in source.indirect:
                effects.update(rhs)
        if any(isinstance(n, (ast.Attribute, ast.Subscript)) and isinstance(n.ctx, ast.Store)
               for n in budget.visit(ast.walk(target))):
            # An alias stored into another object can subsequently escape or be
            # retrieved under a different name.
            effects.update(rhs)

    def returned_names(value):
        if isinstance(value, ast.IfExp):
            return returned_names(value.body) | returned_names(value.orelse)
        if isinstance(value, ast.BoolOp):
            return set().union(*(returned_names(v) for v in value.values))
        if isinstance(value, ast.Attribute) and value.attr in (
                "__dict__", "__self__", "__globals__", "__closure__"):
            return references(value)
        if isinstance(value, (ast.Call, ast.Compare, ast.Attribute, ast.Subscript)):
            # Calls have their own escape summaries, including opaque callees.
            return set()
        return references(value)

    if isinstance(fn, ast.AsyncFunctionDef):
        effects.update(initial)  # The coroutine retains its frame.
    if isinstance(fn, ast.Lambda):
        effects.update(returned_names(fn.body))
    for node in budget.visit(members(fn)):
        if isinstance(node, ast.Call):
            ref = source.reference(node.func, fn)
            receiver = references(node.func)
            args = [(kind, references(arg)) for kind, arg in actuals(node)]
            calls.append((ref, receiver, args))
            if isinstance(node.func, ast.Attribute) and node.func.attr in MUTATORS:
                effects.update(receiver)
            if isinstance(node.func, ast.Name) and node.func.id in {"exec", "eval", "locals", "vars"}:
                effects.update(initial)
        elif isinstance(node, (ast.Attribute, ast.Subscript)) and isinstance(node.ctx, (ast.Store, ast.Del)):
            effects.update(references(node.value))
        elif isinstance(node, ast.AugAssign):
            effects.update(stored_names(node.target))
            assign(node.target, references(node.value))
        elif isinstance(node, ast.Assign):
            for target in node.targets:
                assign(target, references(node.value))
        elif isinstance(node, (ast.AnnAssign, ast.NamedExpr)) and node.value is not None:
            assign(node.target, references(node.value))
        elif isinstance(node, (ast.For, ast.AsyncFor, ast.comprehension)):
            assign(node.target, references(node.iter))
        elif isinstance(node, ast.withitem):
            effects.update(references(node.context_expr))  # dynamic enter/exit
            if node.optional_vars:
                assign(node.optional_vars, references(node.context_expr))
        elif isinstance(node, ast.Match):
            for case in node.cases:
                for pattern in budget.visit(ast.walk(case.pattern)):
                    name = getattr(pattern, "name", None) or getattr(pattern, "rest", None)
                    if isinstance(name, str):
                        rhs = references(node.subject)
                        budget.spend(len(rhs))
                        aliases[name].update(rhs)
        elif isinstance(node, ast.Return):
            # A direct getter lends the selected element/field to its caller.
            # It does not hand out the input container. The caller still tracks
            # the result as a potential alias on any subsequent write or escape.
            effects.update(returned_names(node.value))
        elif isinstance(node, (ast.List, ast.Tuple, ast.Set, ast.Dict, ast.ListComp,
                               ast.SetComp, ast.DictComp, ast.GeneratorExp)):
            if isinstance(getattr(node, "ctx", ast.Load()), ast.Load):
                effects.update(references(node))
        elif isinstance(node, (ast.Yield, ast.YieldFrom)):
            effects.update(initial)  # Suspended generator frames retain arguments.
        elif isinstance(node, (*SCOPES, ast.Raise, ast.Await)):
            effects.update(references(node))

    origins = initial.copy()
    queue = deque(initial)
    users = defaultdict(set)
    for dest, inputs in aliases.items():
        for name in inputs:
            users[name].add(dest)
    while queue:
        name = queue.popleft()
        budget.spend(len(users[name]))
        for dest in users[name]:
            old = origins.get(dest, 0)
            new = old | origins[name]
            if new != old:
                origins[dest] = new
                queue.append(dest)

    def mask(names):
        budget.spend(len(names))
        return combine(origins.get(n, 0) for n in names)

    direct = mask(effects)
    constraints = []
    for ref, receiver, args in calls:
        passed = [(kind, mask(names)) for kind, names in args]
        implicit = mask(receiver)
        possible = implicit | combine(value for _, value in passed)
        if possible & ~direct:
            if ref:
                constraints.append((ref, implicit, passed))
            else:
                direct |= possible
    return [sig, direct, constraints]


class Project:
    """A pinned index, optionally overlaid with all reconstructed files in one diff."""

    def __init__(self, data, edits=None):
        self.data = data
        self.edits = edits or {}
        self.budget = WorkBudget(PATCH_WORK) if edits else None
        self.sources = {}
        self.facts = {}
        self.resolved = {}
        self.solved = {}
        self.attribute_writes = {name for module, writes in data["writes"].items()
                                 if module not in self.edits for name in writes}

    @classmethod
    def load(cls, path):
        return cls(json.loads(Path(path).read_bytes()))

    def patched(self, changes, *, on_demand=False):
        production = [c for c in changes if c.path.startswith("sqlglot/") and c.path.endswith(".py")]
        patch = Project(self.data, {module_name(c.path): c.after for c in production})
        roots = []
        for change in production:
            # All old definitions already have summaries in the pinned map.
            # Index all new bindings first, then solve against the entire patch.
            source = patch.source(module_name(change.path))
            if on_demand:
                # arguments_at_risk solves the complete reachable call graph
                # on first use. Register every edited namespace/write first.
                continue
            points = sorted(change.added | change.deletions | {n + 1 for n in change.deletions})
            for key, fn in source.functions.items():
                start = min((d.lineno for d in getattr(fn, "decorator_list", ())), default=fn.lineno)
                if overlaps(points, start, fn.end_lineno):
                    roots.append(key)
        if roots:
            patch.solve(roots)
        return patch

    def source(self, module, tree=None):
        source = self.sources.get(module)
        if source is None or (tree is not None and source.tree is not tree):
            if tree is None:
                tree = ast.parse(self.edits[module], type_comments=True)
            source = Source(module, tree, module in self.data["packages"], self.budget)
            self.sources[module] = source
            self.attribute_writes.update(source.attribute_writes)
        return source

    def namespace(self, key):
        module = key[2:].partition("@")[0]
        if module in self.edits:
            return self.source(module).namespaces.get(key, {})
        return self.data["namespaces"].get(key, {})

    def member(self, key, name, seen):
        if name in self.attribute_writes:
            return None
        if key == "m/builtins":
            return "b/" + name if name in PURE_BUILTINS else None
        module = key[2:].partition("@")[0]
        if module not in self.data["modules"]:
            return None
        names = self.namespace(key)
        if "<dynamic>" in names:
            return None
        alternatives = set()
        if name in names:
            alternatives.add(self.resolve(names[name], seen))
        for star in names.get("*", ()):
            imported = "m/" + star
            # An explicit/dynamic __all__ may change which names are exported.
            if star not in self.data["modules"] or "__all__" in self.namespace(imported):
                return None
            if not name.startswith("_"):
                target = self.resolve(imported + ":" + name, seen, allow_missing=True)
                if target is not MISSING:
                    alternatives.add(target)
        child = module + "." + name
        if key.startswith("m/") and child in self.data["modules"] and alternatives:
            alternatives.add("m/" + child)
        if len(alternatives) == 1:
            return alternatives.pop()
        if alternatives or "__getattr__" in names:
            return None
        if key.startswith("m/") and child in self.data["modules"]:
            return "m/" + child
        return MISSING

    def resolve(self, ref, seen=frozenset(), allow_missing=False):
        if not ref or ref in seen or len(seen) >= 64 or "*" in self.attribute_writes:
            return None
        if ref not in self.resolved:
            if self.budget is not None:
                self.budget.spend(1)
            key, colon, name = ref.rpartition(":")
            if not colon:
                return None if ref.startswith("b/") and ref[2:] in self.attribute_writes else ref
            key = self.resolve(key, seen | {ref})
            target = (self.member(key, name, seen | {ref})
                      if key and key.startswith(("m/", "c/")) else None)
            self.resolved[ref] = target
        target = self.resolved[ref]
        return None if target is MISSING and not allow_missing else target

    def record(self, key):
        module = key[2:].partition("@")[0]
        if module in self.edits:
            if key not in self.facts:
                source = self.source(module)
                self.facts[key] = function_facts(source, source.functions[key], self.budget)
            return self.facts[key]
        return self.data["functions"][key]

    def solve(self, roots):
        """Build reverse parameter-flow edges, then propagate writes to a fixed point."""
        pending = list(roots)
        masks = {}
        dependents = defaultdict(list)
        while pending:
            key = pending.pop()
            if key in masks:
                continue
            _, direct, calls = self.record(key)
            masks[key] = direct
            for ref, implicit, args in calls:
                if self.budget is not None:
                    self.budget.spend(1 + len(args))
                target = self.resolve(ref)
                if target and target.startswith("b/"):
                    # These builtins can retain arguments or yield one back.
                    if target[2:] in RETAINING_BUILTINS:
                        masks[key] |= combine(value for _, value in args)
                    continue
                if not target or not target.startswith("f/"):
                    masks[key] |= implicit | combine(value for _, value in args)
                    continue
                binding = bind(self.record(target)[0], args)
                if binding is None:
                    masks[key] |= implicit | combine(value for _, value in args)
                    continue
                slots = [(value, slots) for value, slots in binding if value]
                if target in self.solved:
                    masks[key] |= combine(value for value, slot in slots if self.solved[target] & slot)
                elif slots:
                    dependents[target].append((key, slots))
                    pending.append(target)
        queue = deque(key for key in masks if masks[key])
        while queue:
            target = queue.popleft()
            for caller, slots in dependents[target]:
                if self.budget is not None:
                    self.budget.spend(1 + len(slots))
                propagated = combine(value for value, slot in slots if masks[target] & slot)
                if propagated & ~masks[caller]:
                    masks[caller] |= propagated
                    queue.append(caller)
        self.solved.update(masks)

    def arguments_at_risk(self, module, tree, scope, call):
        # A single cached baseline source may have been parsed independently of
        # this caller's AST. Bind lexical scope using the actual tree.
        source = self.source(module, tree)
        target = self.resolve(source.reference(call.func, scope))
        if target and target.startswith("b/"):
            return []
        if not target or not target.startswith("f/"):
            return None
        if self.edits:
            if target not in self.solved:
                self.solve([target])
            mask = self.solved[target]
        else:
            mask = self.data["masks"][target]
        arguments = [(kind, (arg, kind in ("*", "**"))) for kind, arg in actuals(call)]
        binding = bind(self.record(target)[0], arguments)
        return None if binding is None else [actual for actual, slots in binding if slots & mask]


def build(paths):
    data = {"modules": {}, "packages": [], "namespaces": {}, "functions": {}, "writes": {}}
    for path, raw in paths:
        module = module_name(path)
        package = Path(path).name == "__init__.py"
        data["modules"][module] = path
        if package:
            data["packages"].append(module)
        source = Source(module, ast.parse(raw, type_comments=True), package)
        data["namespaces"].update(source.namespaces)
        data["writes"][module] = sorted(source.attribute_writes)
        for key, fn in source.functions.items():
            data["functions"][key] = function_facts(source, fn)
    project = Project(data)
    project.solve(data["functions"])
    data["masks"] = project.solved
    return data


if __name__ == "__main__":
    import sys
    root, output = map(Path, sys.argv[1:])
    started = time.perf_counter()
    cpu = time.process_time()
    data = build((p.relative_to(root).as_posix(), p.read_bytes())
                 for p in sorted((root / "sqlglot").rglob("*.py")))
    output.write_text(json.dumps(data, separators=(",", ":"), sort_keys=True))
    print(f"Mutation summaries: {len(data['functions'])} functions in {len(data['modules'])} modules, "
          f"{time.perf_counter() - started:.3f} s wall, {time.process_time() - cpu:.3f} s process CPU")
