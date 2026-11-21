"""Look for writes with potentially shared receivers on either side of a diff."""
import ast
import builtins
import operator
import sys
from collections import Counter, OrderedDict, defaultdict, deque
from functools import cache, lru_cache
from types import MappingProxyType

from patching import MAX_CHANGED_LINES, overlaps

FUNCTIONS = (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda)
SCOPES = (*FUNCTIONS, ast.ClassDef)
FRESH_BUILTINS = {"dict", "list", "set", "bytearray"}

# Start with the actual method inventories. Immutable counterparts supply the
# read-only operations common to both. Keep explicit in-place protocols even
# when an immutable counterpart exposes them (mappingproxy has __ior__).
CONTAINERS = (dict, list, set, bytearray, deque, OrderedDict, defaultdict, Counter)
READ_ONLY = set.union(*(set(dir(t)) for t in (MappingProxyType, tuple, frozenset, bytes)))
READ_ONLY.update(("__alloc__", "__copy__", "__neg__", "__pos__", "elements",
                  "fromkeys", "most_common", "total"))
MUTATORS = frozenset(
    name for container in CONTAINERS for name in dir(container)
    if callable(getattr(container, name))
    and (name not in READ_ONLY or name.startswith(("__i", "__set", "__del"))
         or name.endswith("_update") or name == "__getitem__")  # defaultdict can insert
)
OPERATOR_WRITES = frozenset(
    name for name in dir(operator)
    if callable(getattr(operator, name)) and name.strip("_").startswith("i")
) | {"setitem", "delitem", "__setitem__", "__delitem__"}
PURE_BUILTINS = frozenset(
    "len iter isinstance sorted list dict tuple set frozenset str repr hash id min max "
    "sum any all enumerate zip map filter getattr hasattr type".split()
)
PURE_CALLS = {f"builtins.{name}" for name in PURE_BUILTINS}
OPERATOR_CALLS = {f"operator.{name}" for name in OPERATOR_WRITES}


def scope_members(sc):
    """Walk one lexical scope, including nested headers and excluding nested bodies."""
    body = sc.body if isinstance(sc.body, list) else [sc.body]
    pending = list(body)
    while pending:
        child = pending.pop()
        yield child
        if isinstance(child, SCOPES):
            for field, value in ast.iter_fields(child):
                if field != "body":
                    pending.extend(
                        item for item in (value if isinstance(value, list) else [value])
                        if isinstance(item, ast.AST)
                    )
        else:
            pending.extend(ast.iter_child_nodes(child))



def _class_qualnames(parents, module):
    names = {}
    for node in parents:
        if isinstance(node, ast.ClassDef):
            chain = [node.name]
            parent = parents[node]
            while isinstance(parent, ast.ClassDef):
                chain.append(parent.name)
                parent = parents[parent]
            local = '.'.join(reversed(chain))
            names[node] = f'{module}.{local}' if module else local
    return names


def _hierarchy(tree, module):
    parents = {tree: None}
    scopes = [tree]
    while scopes:
        scope = scopes.pop()
        for child in scope_members(scope):
            if isinstance(child, SCOPES):
                parents[child] = scope
                scopes.append(child)
    return parents, _class_qualnames(parents, module)


_pinned_hierarchy = lru_cache(maxsize=32)(_hierarchy)


def statement_children(node):
    """Statement suites can contain imports and declarations. Expressions cannot."""
    for field in ('body', 'orelse', 'handlers', 'finalbody', 'cases'):
        children = getattr(node, field, ())
        if isinstance(children, list):
            yield from children


def bindings(tree):
    """Overcount nested bindings: ambiguity can only withdraw a local exemption."""
    sites = {}
    for node in ast.walk(tree):
        names = ()
        if isinstance(node, ast.Name) and isinstance(node.ctx, (ast.Store, ast.Del)):
            names = (node.id,)
        elif isinstance(node, (ast.ClassDef, ast.FunctionDef, ast.AsyncFunctionDef,
                               ast.ExceptHandler, ast.MatchAs, ast.MatchStar)):
            names = (node.name,)
        elif isinstance(node, ast.MatchMapping):
            names = (node.rest,)
        elif isinstance(node, ast.arg):
            names = (node.arg,)
        elif isinstance(node, ast.alias):
            names = (node.asname or node.name.split(".")[0],)
        elif isinstance(node, (ast.Global, ast.Nonlocal)):
            names = node.names
        for name in names:
            sites.setdefault(name, []).append(node)
    return sites


ALL_BUILTINS = frozenset(dir(builtins))
STDLIB_MODULES = getattr(sys, "stdlib_module_names", frozenset())


def _stored_names(target):
    if isinstance(target, ast.Name):
        yield target.id
    elif isinstance(target, ast.Starred):
        yield from _stored_names(target.value)
    elif isinstance(target, (ast.Tuple, ast.List)):
        for item in target.elts:
            yield from _stored_names(item)


def body_nodes(fn):
    pending = list(fn.body) if isinstance(fn.body, list) else [fn.body]
    while pending:
        node = pending.pop()
        yield node
        if not isinstance(node, (*FUNCTIONS, ast.ClassDef)):
            pending.extend(ast.iter_child_nodes(node))


def has_shared_write(tree, changed, project=None, module=None, narrow_shared_args=False, root=None):
    full, bindings = shared_write_effect(
        tree,
        changed,
        project=project,
        module=module,
        narrow_shared_args=narrow_shared_args,
        root=root,
    )
    return full or bool(bindings)


_pinned_bindings = lru_cache(maxsize=32)(bindings)


def shared_write_effect(tree, changed, project=None, module=None, narrow_shared_args=False, root=None,
                        *, fresh_literals=False, unchanged=(), pinned=False, census=None):
    if len(changed) > MAX_CHANGED_LINES:
        return True, set()
    if not changed:
        return False, set()
    points = sorted(changed)

    # These caches live for one side of one patch.
    bound = _pinned_bindings if pinned else cache(bindings)

    def builtin(name):
        names = bound(tree)
        return name not in names and "*" not in names

    @cache
    def imported_names():
        imports = {}
        pending = [tree]
        while pending:
            node = pending.pop()
            pending.extend(statement_children(node))
            if isinstance(node, ast.Import):
                imports.update((alias, alias.name) for alias in node.names)
            elif isinstance(node, ast.ImportFrom) and node.level == 0:
                imports.update((alias, f"{node.module}.{alias.name}") for alias in node.names)
        return imports

    def qualified_name(fn):
        if isinstance(fn, ast.Attribute) and isinstance(fn.value, ast.Name):
            mod = qualified_name(fn.value)
            return f"{mod}.{fn.attr}" if mod else None
        if isinstance(fn, ast.Name):
            if fn.id in PURE_BUILTINS and builtin(fn.id):
                return f"builtins.{fn.id}"
            sites = bound(tree).get(fn.id, ())
            if sites and "*" not in bound(tree):
                names = {imported_names().get(site) for site in sites}
                if len(names) == 1:
                    return names.pop()
        return None

    @cache
    def ordinary_class(cls):
        # A metaclass instance is itself a class. Unknown base classes may
        # inherit from type. Follow unambiguous, preceding local definitions.
        for base in cls.bases:
            if not isinstance(base, ast.Name):
                return False
            if base.id == "object" and builtin("object"):
                continue
            sites = bound(tree).get(base.id, ())
            if len(sites) != 1 or not isinstance(sites[0], ast.ClassDef):
                return False
            parent = sites[0]
            if parent.lineno >= cls.lineno or parent.decorator_list or not ordinary_class(parent):
                return False
        return True

    @cache
    def private_names(fn, cls):
        # Only fresh containers and the direct receiver of an instance method
        # have evidence of local ownership. A parameter or alias can hold a class.
        safe = set()
        args = fn.args.posonlyargs + fn.args.args
        if cls and args and fn.name not in {"__new__", "__init_subclass__", "__class_getitem__"}:
            if not fn.decorator_list and ordinary_class(cls):
                safe.add(args[0])
        for stmt in body_nodes(fn):
            if not isinstance(stmt, (ast.Assign, ast.AnnAssign)):
                continue
            value = stmt.value
            fresh = isinstance(value, (ast.Dict, ast.List, ast.Set, ast.DictComp,
                                       ast.ListComp, ast.SetComp))
            if isinstance(value, ast.Call) and isinstance(value.func, ast.Name):
                fresh = value.func.id in FRESH_BUILTINS and builtin(value.func.id)
            if fresh:
                safe.update(stmt.targets if isinstance(stmt, ast.Assign) else (stmt.target,))
        return {name for name, sites in bound(fn).items() if all(site in safe for site in sites)}

    def private(obj, scope, cls):
        return (isinstance(obj, ast.Name) and isinstance(scope, FUNCTIONS)
                and obj.id in private_names(scope, cls))

    def shared_target(target, scope, cls):
        if isinstance(target, (ast.Tuple, ast.List)):
            return any(shared_target(t, scope, cls) for t in target.elts)
        if isinstance(target, ast.Starred):
            return shared_target(target.value, scope, cls)
        if isinstance(target, ast.Name):
            if isinstance(scope, ast.Module):
                return True
            # Ordinary class namespace declarations have their own reader maps.
            return any(isinstance(site, (ast.Global, ast.Nonlocal))
                       for site in bound(scope).get(target.id, ()))
        if isinstance(target, (ast.Attribute, ast.Subscript)):
            return not private(target.value, scope, cls)
        return False

    def shared_argument(arg, scope, cls, unpacked=False):
        # An expression may return an alias even when the name holding it is
        # local. Exempt only known private receivers, literals and fresh displays
        # whose contents are also private. Fields of an instance may be inherited.
        if isinstance(arg, ast.Constant) or (fresh_literals and isinstance(arg, ast.JoinedStr)):
            return False
        if fresh_literals:
            if isinstance(arg, ast.UnaryOp) and isinstance(arg.op, ast.Not):
                return False
            if isinstance(arg, ast.Compare) and all(isinstance(op, (ast.Is, ast.IsNot, ast.In, ast.NotIn))
                                                    for op in arg.ops):
                return False
            if isinstance(arg, ast.IfExp):
                return (shared_argument(arg.body, scope, cls, unpacked)
                        or shared_argument(arg.orelse, scope, cls, unpacked))
        if isinstance(arg, ast.Name):
            # Unpacking passes the elements. A private list can contain aliases.
            return unpacked or not private(arg, scope, cls)
        if isinstance(arg, ast.Starred):
            return shared_argument(arg.value, scope, cls, unpacked=True)
        if isinstance(arg, (ast.Tuple, ast.List, ast.Set)):
            return any(shared_argument(item, scope, cls) for item in arg.elts)
        if isinstance(arg, ast.Dict):
            return any((key is not None and shared_argument(key, scope, cls))
                       or shared_argument(value, scope, cls, unpacked=key is None)
                       for key, value in zip(arg.keys, arg.values))
        if isinstance(arg, ast.Call) and not arg.args and not arg.keywords:
            if isinstance(arg.func, ast.Name) and arg.func.id in FRESH_BUILTINS:
                return not builtin(arg.func.id)
        return True

    @cache
    def _scope_tree():
        source = getattr(project, 'sources', {}).get(module)
        if source is not None and source.tree is tree:
            return source.parents, _class_qualnames(source.parents, module)
        hierarchy = _pinned_hierarchy if pinned else _hierarchy
        return hierarchy(tree, module)

    def _resolve_relative(level, mod_name):
        if level == 0:
            return mod_name
        if not module:
            return None
        is_pkg = project is not None and module in project.data["packages"]
        package = module if is_pkg else module.rpartition(".")[0]
        parts = package.split(".") if package else []
        if level > len(parts):
            return None
        prefix = parts[:len(parts) - level + 1]
        return ".".join(prefix + ([mod_name] if mod_name else []))

    @cache
    def _scope_info(sc):
        params = set()
        first_param = None
        if isinstance(sc, FUNCTIONS):
            args = sc.args
            all_args = [
                *(a.arg for a in args.posonlyargs + args.args + args.kwonlyargs),
                *([args.vararg.arg] if args.vararg else ()),
                *([args.kwarg.arg] if args.kwarg else ()),
            ]
            params.update(all_args)
            pos = args.posonlyargs + args.args
            if pos:
                first_param = pos[0].arg
        for tp in getattr(sc, "type_params", ()):
            params.add(tp.name)
        globals_ = set()
        nonlocals_ = set()
        imports = {}
        star_imports = []
        defs = defaultdict(list)
        has_dynamic = False

        for node in scope_members(sc):
            if isinstance(node, ast.Global):
                globals_.update(node.names)
            elif isinstance(node, ast.Nonlocal):
                nonlocals_.update(node.names)
            elif isinstance(node, ast.Import):
                for alias in node.names:
                    local_name = alias.asname or alias.name.split(".")[0]
                    full_mod = alias.name if alias.asname else local_name
                    imports[local_name] = ("import", full_mod, None)
            elif isinstance(node, ast.ImportFrom):
                imp_mod = _resolve_relative(node.level, node.module)
                for alias in node.names:
                    if alias.name == "*":
                        star_imports.append(imp_mod)
                    else:
                        imports[alias.asname or alias.name] = ("from", imp_mod, alias.name)
            elif isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                defs[node.name].append(("func", node))
            elif isinstance(node, ast.ClassDef):
                defs[node.name].append(("class", node))
            elif isinstance(node, ast.Assign):
                for t in node.targets:
                    if isinstance(t, ast.Name):
                        defs[t.id].append(("expr", node.value))
                    else:
                        for nm in _stored_names(t):
                            defs[nm].append(("unpack", node.value))
            elif isinstance(node, ast.AnnAssign):
                if node.value is not None:
                    if isinstance(node.target, ast.Name):
                        defs[node.target.id].append(("expr", node.value))
                    else:
                        for nm in _stored_names(node.target):
                            defs[nm].append(("unpack", node.value))
            elif isinstance(node, ast.NamedExpr):
                defs[node.target.id].append(("expr", node.value))
            elif isinstance(node, (ast.For, ast.AsyncFor)):
                for nm in _stored_names(node.target):
                    defs[nm].append(("iter", node.iter))
            elif isinstance(node, (ast.With, ast.AsyncWith)):
                for item in node.items:
                    if item.optional_vars is not None:
                        for nm in _stored_names(item.optional_vars):
                            defs[nm].append(("expr", item.context_expr))
            elif isinstance(node, ast.ExceptHandler):
                if node.name:
                    defs[node.name].append(("local", node))
            elif isinstance(node, ast.Match):
                for case in node.cases:
                    for pat in ast.walk(case.pattern):
                        nm = getattr(pat, "name", None) or getattr(pat, "rest", None)
                        if isinstance(nm, str):
                            defs[nm].append(("unpack", node.subject))
            elif isinstance(node, ast.AugAssign) and isinstance(node.target, ast.Name):
                defs[node.target.id].append(("aug", None))
            elif isinstance(node, ast.Delete):
                for t in node.targets:
                    if isinstance(t, ast.Name):
                        defs[t.id].append(("del", None))
            elif isinstance(node, ast.Call):
                cname = node.func.id if isinstance(node.func, ast.Name) else getattr(node.func, "attr", None)
                if cname in ("exec", "eval", "globals", "locals"):
                    has_dynamic = True
        return params, first_param, globals_, nonlocals_, imports, star_imports, defs, has_dynamic

    @cache
    def _module_ast(mod_name):
        if project is None:
            return None
        if mod_name in project.edits:
            return project.source(mod_name).tree
        rel = project.data["modules"].get(mod_name)
        if not rel or root is None:
            return None
        path = root / rel
        if not path.is_file():
            return None
        try:
            return ast.parse(path.read_bytes(), type_comments=True)
        except (OSError, ValueError, SyntaxError):
            return None

    def _is_class_or_func_in_mod(mod_name, sym_name):
        mtree = _module_ast(mod_name)
        if mtree is None:
            return None
        for node in scope_members(mtree):
            if isinstance(node, ast.ClassDef) and node.name == sym_name:
                return "class"
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)) and node.name == sym_name:
                return "func"
        return None

    def _is_metaclass(cls_node):
        for base in getattr(cls_node, "bases", ()):
            if isinstance(base, ast.Name) and base.id in ("type", "ABCMeta"):
                return True
        return False

    def _is_classmethod_or_meta(fn, cls_node):
        if getattr(fn, "name", None) in ("__new__", "__init_subclass__", "__class_getitem__"):
            return True
        for d in getattr(fn, "decorator_list", ()):
            if isinstance(d, ast.Name) and d.id == "classmethod":
                return True
        return _is_metaclass(cls_node)

    def _is_staticmethod(fn):
        return any(isinstance(d, ast.Name) and d.id == "staticmethod"
                   for d in getattr(fn, "decorator_list", ()))

    def _resolve_mod_symbol(mod_name, sym_name, seen_syms):
        if (mod_name, sym_name) in seen_syms or len(seen_syms) >= 64:
            return None
        if mod_name == module:
            _, _, _, _, imports, star_imports, defs, has_dynamic = _scope_info(tree)
            if has_dynamic:
                return None
            if not star_imports:
                if sym_name in imports:
                    kind, tgt_mod, orig = imports[sym_name]
                    if kind == "import":
                        return {("module", tgt_mod)}
                    if tgt_mod is None:
                        return None
                    return _resolve_mod_symbol(tgt_mod, orig, seen_syms | {(mod_name, sym_name)})
                if sym_name in defs:
                    _, class_q = _scope_tree()
                    entries = defs[sym_name]
                    if all(k == "class" for k, _ in entries):
                        return {("class", class_q.get(node), node.name) for _, node in entries}
                    if all(k == "func" for k, _ in entries):
                        return {("func", mod_name, sym_name)}
                    return {("mod_val", mod_name, sym_name)}
                if sym_name in ALL_BUILTINS:
                    return {"local"}
                if project is not None and mod_name and f"{mod_name}.{sym_name}" in project.data["modules"]:
                    return {("module", f"{mod_name}.{sym_name}")}
                return None
            if project is None:
                return None

        if project is None or not mod_name:
            return None
        if mod_name not in project.data["modules"] and mod_name not in project.edits:
            if mod_name in STDLIB_MODULES or mod_name.split(".")[0] in STDLIB_MODULES:
                return {("stdlib", mod_name, sym_name)}
            return None

        ns = project.namespace("m/" + mod_name)
        if "<dynamic>" in ns:
            return None
        resolved = project.resolve(f"m/{mod_name}:{sym_name}")
        if resolved is not None:
            if resolved.startswith("m/"):
                return {("module", resolved[2:])}
            if resolved.startswith("f/"):
                return {("func", mod_name, sym_name)}
            if resolved.startswith("c/"):
                c_mod = resolved[2:].partition("@")[0]
                return {("class", f"{c_mod}.{sym_name}", sym_name)}
        if "*" not in ns and sym_name in ns:
            val = ns[sym_name]
            if isinstance(val, str) and val.startswith("m/") and ":" in val:
                tgt_mod, _, tgt_sym = val[2:].rpartition(":")
                return _resolve_mod_symbol(tgt_mod, tgt_sym, seen_syms | {(mod_name, sym_name)})
            kind = _is_class_or_func_in_mod(mod_name, sym_name)
            if kind == "class":
                return {("class", f"{mod_name}.{sym_name}", sym_name)}
            if kind == "func":
                return {("func", mod_name, sym_name)}
            return {("mod_val", mod_name, sym_name)}
        if "*" in ns:
            matches = set()
            for star_mod in ns["*"]:
                if (not star_mod
                        or (star_mod not in project.data["modules"] and star_mod not in project.edits)
                        or "__all__" in project.namespace("m/" + star_mod)):
                    return None
                if not sym_name.startswith("_"):
                    star_ns = project.namespace("m/" + star_mod)
                    if sym_name in star_ns or "*" in star_ns:
                        res = _resolve_mod_symbol(star_mod, sym_name, seen_syms | {(mod_name, sym_name)})
                        if res is None:
                            return None
                        matches.update(res)
            if len(matches) == 1:
                return matches
            if matches or sym_name in ns:
                return None
        if f"{mod_name}.{sym_name}" in project.data["modules"]:
            return {("module", f"{mod_name}.{sym_name}")}
        if sym_name in ALL_BUILTINS and "*" not in ns:
            return {"local"}
        return None

    def _resolve_name(name, sc, seen, comp_vars):
        if comp_vars and name in comp_vars:
            iter_expr, c_sc, c_comp = comp_vars[name]
            return _resolve_obj(iter_expr, c_sc, seen, c_comp)
        if len(seen) >= 64:
            return None
        parents, class_q = _scope_tree()

        cur = sc
        # Class body scopes can read local class members or outer non-class scopes;
        # function bodies skip enclosing ClassDef scopes when resolving free vars.
        if isinstance(cur, ast.ClassDef):
            _, _, globals_, nonlocals_, imports, _, defs, has_dynamic = _scope_info(cur)
            if has_dynamic:
                return None
            if name in globals_:
                cur = tree
            elif name in imports:
                kind, tgt_mod, orig = imports[name]
                if kind == "import":
                    return {("module", tgt_mod)}
                if tgt_mod is None:
                    return None
                return _resolve_mod_symbol(tgt_mod, orig, frozenset())
            elif name in defs:
                return {("cls_val", class_q.get(cur), name)}
            else:
                cur = parents.get(cur, tree)

        while cur is not None and cur is not tree:
            if isinstance(cur, ast.ClassDef):
                cur = parents.get(cur, tree)
                continue
            params, first_param, globals_, nonlocals_, imports, _, defs, has_dynamic = _scope_info(cur)
            if has_dynamic:
                return None
            if name in globals_:
                break
            if name in nonlocals_:
                # Search strictly enclosing FUNCTIONS (skipping ClassDef)
                enc = parents.get(cur, tree)
                found_enc = None
                while enc is not None and enc is not tree:
                    if isinstance(enc, FUNCTIONS):
                        e_params, _, e_glob, e_nonloc, e_imp, _, e_defs, _ = _scope_info(enc)
                        if (name in e_params or name in e_imp or name in e_defs) and name not in e_glob and name not in e_nonloc:
                            found_enc = enc
                            break
                    enc = parents.get(enc)
                if found_enc is None:
                    return None
                cur = found_enc
                continue
            if name in params or name in imports or name in defs:
                if (cur, name) in seen:
                    return set()
                next_seen = seen | {(cur, name)}
                out = set()
                if name in imports:
                    kind, tgt_mod, orig = imports[name]
                    if kind == "import":
                        out.add(("module", tgt_mod))
                    elif tgt_mod is None:
                        return None
                    else:
                        r = _resolve_mod_symbol(tgt_mod, orig, frozenset())
                        if r is None:
                            return None
                        out.update(r)
                if name in params:
                    parent_sc = parents.get(cur)
                    if (name == first_param
                            and isinstance(cur, (ast.FunctionDef, ast.AsyncFunctionDef))
                            and isinstance(parent_sc, ast.ClassDef)
                            and not _is_staticmethod(cur)):
                        cq = class_q.get(parent_sc)
                        if _is_classmethod_or_meta(cur, parent_sc):
                            out.add(("class", cq, parent_sc.name))
                        else:
                            out.add(("self_inst", cq, parent_sc.name))
                    else:
                        out.add("local")
                for kind, val in defs.get(name, ()):
                    if kind in ("func", "class", "local"):
                        out.add("local")
                    elif kind in ("expr", "unpack", "iter"):
                        r = _resolve_obj(val, cur, next_seen, None)
                        if r is None:
                            return None
                        out.update(r)
                    elif kind in ("aug", "del"):
                        out.add("local")
                return out if out else {"local"}
            cur = parents.get(cur, tree)

        return _resolve_mod_symbol(module, name, frozenset())

    def _attr_targets(recv_targets, attr_name):
        if recv_targets is None:
            return None
        out = set()
        for t in recv_targets:
            if t == "local":
                out.add("local")
            elif isinstance(t, tuple):
                tag = t[0]
                if tag in ("self_inst", "class"):
                    out.add(("cls_val", t[1], attr_name))
                elif tag == "module":
                    res = _resolve_mod_symbol(t[1], attr_name, frozenset())
                    if res is None:
                        return None
                    out.update(res)
                elif tag == "mod_val":
                    q = f"{t[1]}.{t[2]}" if t[1] else None
                    out.add(("cls_val", q, attr_name))
                elif tag == "cls_val":
                    out.add(("cls_val", None, attr_name))
                    out.add(t)
                elif tag == "stdlib":
                    out.add(("stdlib", f"{t[1]}.{t[2]}", attr_name))
                else:
                    return None
            else:
                return None
        return out

    def _resolve_obj(expr, sc, seen=frozenset(), comp_vars=None):
        if expr is None or len(seen) >= 64:
            return None
        if isinstance(expr, ast.Constant):
            return {"local"}
        if isinstance(expr, ast.Name):
            return _resolve_name(expr.id, sc, seen, comp_vars)
        if isinstance(expr, ast.Attribute):
            recv = _resolve_obj(expr.value, sc, seen, comp_vars)
            return _attr_targets(recv, expr.attr)
        if isinstance(expr, ast.Subscript):
            return _resolve_obj(expr.value, sc, seen, comp_vars)
        if isinstance(expr, ast.Starred):
            return _resolve_obj(expr.value, sc, seen, comp_vars)
        if isinstance(expr, (ast.Tuple, ast.List, ast.Set)):
            out = set()
            for elt in expr.elts:
                r = _resolve_obj(elt, sc, seen, comp_vars)
                if r is None:
                    return None
                out.update(r)
            return out or {"local"}
        if isinstance(expr, ast.Dict):
            out = set()
            for k, v in zip(expr.keys, expr.values):
                if k is not None:
                    rk = _resolve_obj(k, sc, seen, comp_vars)
                    if rk is None:
                        return None
                    out.update(rk)
                rv = _resolve_obj(v, sc, seen, comp_vars)
                if rv is None:
                    return None
                out.update(rv)
            return out or {"local"}
        if isinstance(expr, ast.IfExp):
            rb = _resolve_obj(expr.body, sc, seen, comp_vars)
            ro = _resolve_obj(expr.orelse, sc, seen, comp_vars)
            if rb is None or ro is None:
                return None
            return rb | ro
        if isinstance(expr, ast.BoolOp):
            out = set()
            for v in expr.values:
                rv = _resolve_obj(v, sc, seen, comp_vars)
                if rv is None:
                    return None
                out.update(rv)
            return out or {"local"}
        if isinstance(expr, ast.UnaryOp):
            return _resolve_obj(expr.operand, sc, seen, comp_vars)
        if isinstance(expr, ast.BinOp):
            rl = _resolve_obj(expr.left, sc, seen, comp_vars)
            rr = _resolve_obj(expr.right, sc, seen, comp_vars)
            if rl is None or rr is None:
                return None
            return rl | rr
        if isinstance(expr, ast.Compare):
            return {"local"}
        if isinstance(expr, ast.Call):
            fn = expr.func
            if isinstance(fn, ast.Name) and builtin(fn.id) and _is_builtin_unshadowed(fn.id, sc, _scope_tree()[0]):
                if fn.id == "getattr":
                    if len(expr.args) >= 2 and isinstance(expr.args[1], ast.Constant) and isinstance(expr.args[1].value, str):
                        recv = _resolve_obj(expr.args[0], sc, seen, comp_vars)
                        return _attr_targets(recv, expr.args[1].value)
                    return None
                if fn.id in FRESH_BUILTINS:
                    if not expr.args and not expr.keywords:
                        return {"local"}
                    out = set()
                    for a in expr.args:
                        ra = _resolve_obj(a, sc, seen, comp_vars)
                        if ra is None:
                            return None
                        out.update(ra)
                    for kw in expr.keywords:
                        rk = _resolve_obj(kw.value, sc, seen, comp_vars)
                        if rk is None:
                            return None
                        out.update(rk)
                    return out or {"local"}
            if isinstance(fn, ast.Attribute):
                recv = _resolve_obj(fn.value, sc, seen, comp_vars)
                if recv is None:
                    return None
                out = set()
                for t in recv:
                    if t == "local":
                        out.add("local")
                    elif isinstance(t, tuple) and t[0] in ("self_inst", "module", "class", "func", "stdlib"):
                        out.add("local")
                    elif isinstance(t, tuple) and t[0] in ("mod_val", "cls_val"):
                        out.add(t)
                    else:
                        return None
                return out or {"local"}
            rf = _resolve_obj(fn, sc, seen, comp_vars)
            if rf is None:
                return None
            return {"local"}
        if isinstance(expr, (ast.ListComp, ast.SetComp, ast.DictComp)):
            cur_comp = dict(comp_vars or {})
            for gen in expr.generators:
                iter_targets = _resolve_obj(gen.iter, sc, seen, cur_comp)
                if iter_targets is None:
                    return None
                for nm in _stored_names(gen.target):
                    cur_comp[nm] = (gen.iter, sc, dict(cur_comp))
            if isinstance(expr, ast.DictComp):
                rk = _resolve_obj(expr.key, sc, seen, cur_comp)
                rv = _resolve_obj(expr.value, sc, seen, cur_comp)
                if rk is None or rv is None:
                    return None
                return rk | rv
            return _resolve_obj(expr.elt, sc, seen, cur_comp)
        return None

    def _is_builtin_unshadowed(name, sc, parents):
        cur = sc
        while cur is not None:
            if isinstance(cur, ast.ClassDef):
                cur = parents.get(cur)
                continue
            if cur is tree:
                _, _, _, _, imports, star_imports, defs, has_dynamic = _scope_info(tree)
                return not has_dynamic and not star_imports and name not in imports and name not in defs
            params, _, globals_, nonlocals_, imports, _, defs, has_dynamic = _scope_info(cur)
            if has_dynamic:
                return False
            if name in globals_:
                cur = tree
                continue
            if name in params or name in imports or name in defs:
                return False
            cur = parents.get(cur)
        return True

    def _classify_arg(arg, sc, comp_vars):
        targets = _resolve_obj(arg, sc, frozenset(), comp_vars)
        if targets is None:
            return None
        bindings_out = set()
        for t in targets:
            if t == "local" or (isinstance(t, tuple) and t[0] in ("self_inst", "func")):
                continue
            if isinstance(t, tuple) and t[0] in ("mod_val", "cls_val", "class"):
                bindings_out.add(t)
            else:
                return None
        return bindings_out

    def unchanged_private(arg, scope, comp_vars):
        # A changed flag can still affect mutation of a shared actual in the
        # same slot. Keep the guard for shared/opaque bindings and known writers.
        if arg not in unchanged or not isinstance(scope, FUNCTIONS):
            return False
        if isinstance(arg, ast.Name):
            sites = bound(scope).get(arg.id, ())
            if sites and all(isinstance(site, ast.arg) for site in sites):
                return True
        return project is not None and _classify_arg(arg, scope, comp_vars) == set()

    found_bindings = set()

    def walk(node, scope, cls=None, comp_vars=None):
        if getattr(node, "end_lineno", None) is not None and not overlaps(points, node.lineno, node.end_lineno):
            # Function/class ranges start at 'def'/'class', below decorators.
            return any(walk(d, scope, cls, comp_vars) for d in getattr(node, "decorator_list", ()))
        if isinstance(node, (ast.Assign, ast.Delete)):
            if any(shared_target(t, scope, cls) for t in node.targets):
                return True
        elif isinstance(node, (ast.AnnAssign, ast.AugAssign, ast.NamedExpr)):
            if shared_target(node.target, scope, cls):
                return True
            # An in-place operator can modify an inherited field before storing it.
            if isinstance(node, ast.AugAssign) and not private(node.target, scope, cls):
                return True
        elif isinstance(node, (ast.Attribute, ast.Subscript)) and isinstance(node.ctx, ast.Store):
            if shared_target(node, scope, cls):  # also for 'for' and 'with' targets
                return True
        elif isinstance(node, ast.Call):
            fn = node.func
            callee = qualified_name(fn)
            name = fn.id if isinstance(fn, ast.Name) else getattr(fn, "attr", None)
            if callee in OPERATOR_CALLS or name in ("setattr", "delattr"):
                if not node.args or not private(node.args[0], scope, cls):
                    return True
            elif isinstance(fn, ast.Attribute) and fn.attr in MUTATORS:
                if not private(fn.value, scope, cls):
                    return True
            if callee not in PURE_CALLS:
                arguments = [(arg, False) for arg in node.args]
                arguments.extend((kw.value, kw.arg is None) for kw in node.keywords)
                if any(shared_argument(arg, scope, cls, unpacked) for arg, unpacked in arguments):
                    at_risk = (project.arguments_at_risk(module, tree, scope, node)
                               if project is not None else None)
                    risky = arguments if at_risk is None else at_risk
                    shared_risky = [(arg, unpacked) for arg, unpacked in risky
                                    if shared_argument(arg, scope, cls, unpacked)
                                    and not (at_risk is None and unchanged_private(arg, scope, comp_vars))]
                    if shared_risky:
                        if not narrow_shared_args:
                            return True
                        for arg, _ in shared_risky:
                            classified = _classify_arg(arg, scope, comp_vars)
                            if classified is None:
                                # The heap census can show that this value is
                                # never a shared object at the pin.
                                if census is not None and census(arg, scope, cls, node, tree):
                                    continue
                                return True
                            found_bindings.update(classified)

        if isinstance(node, (ast.ListComp, ast.SetComp, ast.DictComp, ast.GeneratorExp)):
            cur_comp = dict(comp_vars or {})
            for gen in node.generators:
                if walk(gen.iter, scope, cls, cur_comp):
                    return True
                next_comp = dict(cur_comp)
                for nm in _stored_names(gen.target):
                    next_comp[nm] = (gen.iter, scope, cur_comp)
                cur_comp = next_comp
                for cond in gen.ifs:
                    if walk(cond, scope, cls, cur_comp):
                        return True
            if isinstance(node, ast.DictComp):
                return walk(node.key, scope, cls, cur_comp) or walk(node.value, scope, cls, cur_comp)
            return walk(node.elt, scope, cls, cur_comp)

        if isinstance(node, (*FUNCTIONS, ast.ClassDef)):
            # Defaults, annotations, bases and decorators run in the outer scope.
            for field, value in ast.iter_fields(node):
                children = value if isinstance(value, list) else (value,)
                for child in children:
                    if not isinstance(child, ast.AST):
                        continue
                    if field == "body":
                        method = isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef))
                        owner = scope if method and isinstance(scope, ast.ClassDef) else None
                        if walk(child, node, owner, None):
                            return True
                    elif walk(child, scope, cls, comp_vars):
                        return True
            return False
        return any(walk(child, scope, cls, comp_vars) for child in ast.iter_child_nodes(node))

    full = walk(tree, tree)
    return full, (set() if full else found_bindings)
