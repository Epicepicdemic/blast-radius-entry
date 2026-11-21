"""Prove where a changed instruction, delayed value or class binding can first be observed."""
import ast
import dis
from functools import lru_cache
import json
import marshal
from pathlib import Path
import re
import types


def literal_delta(a, b, parents=()):
    """Find a single changed, bounded primitive literal, preserving all other AST fields."""
    if type(a) is not type(b):
        raise ValueError
    if isinstance(a, ast.Constant):
        if type(a.value) is not type(b.value) or a.kind != b.kind:
            raise ValueError
        if marshal.dumps(a.value, 2) != marshal.dumps(b.value, 2):
            if type(a.value) is str:
                if max(len(a.value), len(b.value)) > 256:
                    raise ValueError
            elif type(a.value) not in (int, bool) or max(a.value.bit_length(), b.value.bit_length()) > 63:
                raise ValueError
            yield parents + (a,)
    elif isinstance(a, ast.AST):
        for key in a._fields:
            yield from literal_delta(getattr(a, key), getattr(b, key), parents + (a,))
    elif isinstance(a, list):
        if len(a) != len(b):
            raise ValueError
        for left, right in zip(a, b):
            yield from literal_delta(left, right, parents)
    elif a != b:
        raise ValueError


def top_binding(tree, name):
    """Reject duplicate, conditional and locally shadowed bindings."""
    imports = []
    for node in ast.walk(tree):
        if isinstance(node, ast.alias) and node.name == "*":
            return None
        if isinstance(node, ast.alias) and (node.asname or node.name) == name:
            imports.append(node)
        if ((isinstance(node, ast.Name) and isinstance(node.ctx, (ast.Store, ast.Del)) and node.id == name)
            or (isinstance(node, (ast.FunctionDef, ast.ClassDef, ast.AsyncFunctionDef)) and node.name == name)
            or (isinstance(node, ast.arg) and node.arg == name)):
            return None
    if len(imports) != 1:
        return None
    for node in tree.body:
        if isinstance(node, ast.ImportFrom) and node.level == 0 and imports[0] in node.names:
            return node.module, imports[0].name
    return None


def dictionary_readers(index, change, chain):
    classes = [n for n in chain if isinstance(n, ast.ClassDef)]
    if not classes or not isinstance(chain[1], ast.ClassDef):
        return None
    owner = classes[-1]
    declaration = next((n for n in chain if isinstance(n, ast.Assign) and n in owner.body), None)
    if (not declaration or len(declaration.targets) != 1 or not isinstance(declaration.targets[0], ast.Name)
            or not isinstance(declaration.value, ast.Dict) or owner.decorator_list or owner.keywords
            or len(owner.bases) != 1):
        return None
    mapping = declaration.value
    if any(not isinstance(k, ast.Constant) or type(k.value) is not str for k in mapping.keys):
        return None
    if len({k.value for k in mapping.keys}) != len(mapping.keys):
        return None
    if not any(v in chain for v in mapping.values):
        return None
    name = declaration.targets[0].id
    if any(isinstance(n, ast.Name) and isinstance(n.ctx, ast.Load)
           and n.id in (name, "vars", "locals", "exec", "eval") for n in ast.walk(owner)):
        return None
    qualname = ".".join([change.path[:-3].replace("/", ".")] + [c.name for c in classes])
    key = qualname + "." + name
    if not index.bits("class_reads", "decl:" + key):
        return None
    affected = [name]
    if (len(classes) == 1 and owner.body == [declaration] and name == "arg_types"
            and isinstance(owner.bases[0], ast.Name) and owner.bases[0].id == "Expression"
            and all(isinstance(v, ast.Constant) and type(v.value) is bool for v in mapping.values)):
        affected.append("required_args")
        label = "expression schema"
    elif (len(classes) == 2 and owner.name == "Tokenizer" and name.isupper()
          and isinstance(owner.bases[0], ast.Attribute) and owner.bases[0].attr == "Tokenizer"
          and name not in index.data["tokenizer_init_names"]
          and all(isinstance(v, ast.Tuple) and all(isinstance(e, ast.Constant) and type(e.value) is int
                                                   for e in v.elts) for v in mapping.values)):
        label = "tokenizer dictionary"
    else:
        return None
    mask = index.bits("class_reads", key) | index.bits("class_reads", qualname) | index.bits("raw_class_reads", "*")
    for attr in affected:
        mask |= index.bits("raw_class_reads", attr)
    return label, mask


def delayed_literal(index, before, after, change):
    if len(change.removed) != 1 or change.insertions:
        return None
    try:
        changes = list(literal_delta(before, after))
    except ValueError:
        return None
    if len(changes) != 1:
        return None
    chain = changes[0]
    schema = dictionary_readers(index, change, chain)
    if schema:
        return schema
    # A literal in a lambda default is evaluated at construction.
    for i, node in enumerate(chain[:-1]):
        if isinstance(node, ast.Lambda) and chain[i + 1] is node.body:
            mask = index.point("entries", change.path, node.lineno)
            return ("lambda calls", mask) if mask else None

    if len(chain) >= 3 and isinstance(chain[-2], ast.keyword):
        arg = chain[-3]
    else:
        arg = chain[-2]
    if isinstance(arg, ast.Call) and isinstance(arg.func, ast.Name) and any(isinstance(n, ast.Dict) for n in chain):
        binding = top_binding(before, arg.func.id)
        if binding:
            factory = index.data["factories"].get(".".join(binding))
            if factory:
                path, first, last = factory
                mask = index.range_users(index.data["lines"].get(path, {}), first, last)
                if mask:
                    return "deferred closure calls", mask

    # For an ordinary assignment directly in an audited Dialect subclass,
    # importing the numeric literal can affect Python only through its binding.
    assignment = next((n for n in reversed(chain) if isinstance(n, ast.Assign)), None)
    if not assignment or len(assignment.targets) != 1 or not isinstance(assignment.targets[0], ast.Name):
        return None
    if not (isinstance(assignment.value, ast.Constant) or
            isinstance(assignment.value, ast.UnaryOp) and isinstance(assignment.value.op, (ast.USub, ast.UAdd))
            and isinstance(assignment.value.operand, ast.Constant)):
        return None
    if type(chain[-1].value) not in (int, bool):
        return None
    name = assignment.targets[0].id
    owner = chain[1] if len(chain) > 1 else None
    if not (name.isupper() and name.isidentifier() and isinstance(owner, ast.ClassDef)
            and assignment in owner.body and not owner.keywords and not owner.decorator_list
            and len(owner.bases) == 1 and isinstance(owner.bases[0], ast.Name)
            and top_binding(before, owner.bases[0].id) == ("sqlglot.dialects.dialect", "Dialect")
            and change.path.startswith("sqlglot/dialects/")):
        return None
    if any(isinstance(n, ast.Name) and n.id in ("locals", "exec", "eval") for n in ast.walk(owner)):
        return None
    mask = (index.bits("attributes", name) | index.bits("dialect_reads", name)
            | index.bits("dialect_reads", "*") | index.bits("raw_class_reads", name)
            | index.bits("raw_class_reads", "*"))
    return ("scalar attribute reads", mask) if mask else None


def comparison_candidate(change):
    # Cheap admission filter only; the full bytecode comparison decides.
    line = change.before.split(b"\n")[next(iter(change.removed)) - 1]
    return any(op in line for op in (b"==", b"!=", b"<", b">"))


@lru_cache(maxsize=16)
def baseline_code(source, path):
    return compile(source, path, "exec", dont_inherit=True)


def opcode_lines(old, new, hits):
    """Align entire code trees; account for every changed instruction."""
    attributes = ("co_name", "co_qualname", "co_firstlineno", "co_flags", "co_argcount",
                  "co_posonlyargcount", "co_kwonlyargcount", "co_names", "co_varnames",
                  "co_freevars", "co_cellvars", "co_exceptiontable", "co_stacksize")
    if any(getattr(old, k) != getattr(new, k) for k in attributes) or len(old.co_consts) != len(new.co_consts):
        return False
    for a, b in zip(old.co_consts, new.co_consts):
        if isinstance(a, types.CodeType) and isinstance(b, types.CodeType):
            if not opcode_lines(a, b, hits):
                return False
        elif type(a) is not type(b) or marshal.dumps(a, 2) != marshal.dumps(b, 2):
            return False
    if old.co_code == new.co_code:
        return True
    if not old.co_flags & 1 or list(old.co_lines()) != list(new.co_lines()):
        return False
    left, right = list(dis.get_instructions(old)), list(dis.get_instructions(new))
    if len(left) != len(right):
        return False
    for a, b in zip(left, right):
        if a.offset != b.offset or a.opname != b.opname:
            return False
        if a.arg == b.arg:
            continue
        # Changing an existing comparison operand leaves all jump targets,
        # exception ranges, locals, constants and instruction boundaries intact.
        if a.opname != "COMPARE_OP":
            return False
        line = next((n for start, end, n in old.co_lines() if start <= a.offset < end), None)
        if line is None:
            return False
        hits.add(line)
    return True


def scope_changed(old, new, *, ignore_locals=False):
    # Binding a name anywhere in a function can change an untouched earlier
    # load. Generator and coroutine flags can likewise change the call itself.
    fields = ("co_qualname", "co_flags", "co_freevars", "co_cellvars")
    if not ignore_locals:
        fields += ("co_varnames",)
    if any(getattr(old, key) != getattr(new, key) for key in fields):
        return True
    children = lambda code: [c for c in code.co_consts if isinstance(c, types.CodeType)]
    left, right = children(old), children(new)
    return len(left) != len(right) or any(scope_changed(a, b, ignore_locals=ignore_locals) for a, b in zip(left, right))


_EQUIV_CMP_PAIRS = {
    (ast.Is, ast.Eq),
    (ast.Eq, ast.Is),
    (ast.IsNot, ast.NotEq),
    (ast.NotEq, ast.IsNot),
}
_RAW_CACHE = {}
_AST_CACHE = {}
_FACTS_CACHE = {}
_PREBUILT_CACHE = {}
FACTS_FILE = Path(__file__).with_name("proof_facts.json")


def _ast_equal(a, b):
    if type(a) is not type(b):
        return False
    if isinstance(a, ast.AST):
        return all(_ast_equal(getattr(a, k, None), getattr(b, k, None)) for k in a._fields)
    if isinstance(a, list):
        return len(a) == len(b) and all(_ast_equal(x, y) for x, y in zip(a, b))
    if isinstance(a, (float, complex)):
        return marshal.dumps(a, 2) == marshal.dumps(b, 2)
    return a == b


def _compare_op_delta(a, b, parents=()):
    if type(a) is not type(b):
        raise ValueError
    if isinstance(a, ast.Compare):
        if (len(a.ops) == 1 and len(b.ops) == 1
                and len(a.comparators) == 1 and len(b.comparators) == 1
                and (type(a.ops[0]), type(b.ops[0])) in _EQUIV_CMP_PAIRS):
            if _ast_equal(a.left, b.left) and _ast_equal(a.comparators[0], b.comparators[0]):
                yield parents + (a,)
                return
    if isinstance(a, ast.AST):
        for key in a._fields:
            yield from _compare_op_delta(getattr(a, key, None), getattr(b, key, None), parents + (a,))
    elif isinstance(a, list):
        if len(a) != len(b):
            raise ValueError
        for left, right in zip(a, b):
            yield from _compare_op_delta(left, right, parents)
    elif isinstance(a, (float, complex)):
        if marshal.dumps(a, 2) != marshal.dumps(b, 2):
            raise ValueError
    elif a != b:
        raise ValueError


def _repo_bytes(root):
    key = str(root)
    if key not in _RAW_CACHE:
        _RAW_CACHE[key] = [(p, p.read_bytes()) for p in sorted(Path(root).rglob("*.py"))]
    return _RAW_CACHE[key]


def _parse_matching(root, tokens):
    hits = []
    for p, raw in _repo_bytes(root):
        if any(tok in raw for tok in tokens):
            tree = _AST_CACHE.get(p)
            if tree is None:
                tree = ast.parse(raw, type_comments=True)
                _AST_CACHE[p] = tree
            hits.append((p, tree))
    return hits


def _scan_tree(tree):
    has_unknown_setattr = False
    setattr_names = set()
    mock_unparsed = []
    class_bases = {}
    attr_stores = {}
    call_names = set()
    single_writes = {}
    for node in ast.walk(tree):
        t = type(node)
        if t is ast.Call:
            fn = node.func
            if type(fn) is ast.Name:
                fid = fn.id
                call_names.add(fid)
                if fid in ("setattr", "delattr"):
                    if (fid == "delattr" or len(node.args) < 2
                            or type(node.args[1]) is not ast.Constant
                            or type(node.args[1].value) is not str):
                        has_unknown_setattr = True
                    else:
                        setattr_names.add(node.args[1].value)
            if _call_name_has(node, ("patch", "Mock")):
                mock_unparsed.append(ast.unparse(node))
        elif t is ast.ClassDef:
            for base in node.bases:
                if type(base) is ast.Name:
                    class_bases.setdefault(base.id, []).append(node)
        elif t is ast.Attribute and type(node.ctx) in (ast.Store, ast.Del):
            attr_stores.setdefault(node.attr, []).append(
                (type(node.ctx) is ast.Del, node.lineno, node.col_offset)
            )
        elif t is ast.Assign and len(node.targets) == 1:
            t0 = node.targets[0]
            if type(t0) is ast.Name:
                single_writes.setdefault(t0.id, []).append(node.value)
            elif type(t0) is ast.Attribute:
                single_writes.setdefault(t0.attr, []).append(node.value)
        elif t is ast.AnnAssign and node.value is not None:
            t0 = node.target
            if type(t0) is ast.Name:
                single_writes.setdefault(t0.id, []).append(node.value)
            elif type(t0) is ast.Attribute:
                single_writes.setdefault(t0.attr, []).append(node.value)
    return (has_unknown_setattr, setattr_names, mock_unparsed,
            class_bases, attr_stores, call_names, single_writes)


def _full_facts(p, raw=None):
    tree = _AST_CACHE.get(p)
    if tree is None:
        if raw is None:
            raw = p.read_bytes()
        tree = ast.parse(raw, type_comments=True)
        _AST_CACHE[p] = tree
    facts = _FACTS_CACHE.get(p)
    if facts is None:
        facts = _scan_tree(tree)
        _FACTS_CACHE[p] = facts
    return tree, facts


def _prebuilt(root):
    key = str(root)
    if key in _PREBUILT_CACHE:
        return _PREBUILT_CACHE[key]
    if key != "/sqlglot" or not FACTS_FILE.is_file():
        _PREBUILT_CACHE[key] = None
        return None
    raw = json.loads(FACTS_FILE.read_bytes())
    loaded = []
    base = Path(root)
    for rel, row in raw.items():
        (has_unk, sat, mocks, cb_names, attr_stores, call_names, sw_keys) = row
        loaded.append((
            base / rel,
            (
                bool(has_unk),
                set(sat),
                mocks,
                set(cb_names),
                {k: [tuple(x) for x in v] for k, v in attr_stores.items()},
                set(call_names),
                set(sw_keys),
            ),
        ))
    _PREBUILT_CACHE[key] = loaded
    return loaded


def build_facts(root="/sqlglot", out_path=FACTS_FILE):
    base = Path(root)
    entries = {}
    for p in sorted(base.rglob("*.py")):
        tree = ast.parse(p.read_bytes(), type_comments=True)
        (has_unk, sat, mocks, class_bases, attr_stores, call_names, single_writes) = _scan_tree(tree)
        entries[str(p.relative_to(base))] = [
            has_unk,
            sorted(sat),
            mocks,
            sorted(class_bases),
            {k: [list(x) for x in v] for k, v in attr_stores.items()},
            sorted(call_names),
            sorted(single_writes),
        ]
    Path(out_path).write_text(json.dumps(entries, separators=(",", ":")))


def _matching_facts(root, tokens):
    hits = []
    for p, raw in _repo_bytes(root):
        if any(tok in raw for tok in tokens):
            tree, facts = _full_facts(p, raw)
            hits.append((p, tree, facts))
    return hits


def _resolve_import_symbol(tree, current_path, root, name):
    """Resolve a class/symbol defined in tree or imported from a local sqlglot module."""
    for node in tree.body:
        if isinstance(node, ast.ClassDef) and node.name == name:
            return current_path, tree, node
    # Check module-level and TYPE_CHECKING imports
    candidates = []
    for node in ast.walk(tree):
        if isinstance(node, ast.ImportFrom) and node.module and node.level == 0:
            for alias in node.names:
                if (alias.asname or alias.name) == name:
                    candidates.append((node.module, alias.name))
    if len(candidates) != 1:
        return None
    mod_name, orig_name = candidates[0]
    mod_path = Path(root) / (mod_name.replace(".", "/") + ".py")
    if not mod_path.is_file():
        mod_path = Path(root) / mod_name.replace(".", "/") / "__init__.py"
    if not mod_path.is_file():
        return None
    raw = mod_path.read_bytes()
    mtree = _AST_CACHE.get(mod_path)
    if mtree is None:
        mtree = ast.parse(raw, type_comments=True)
        _AST_CACHE[mod_path] = mtree
    for node in mtree.body:
        if isinstance(node, ast.ClassDef) and node.name == orig_name:
            return mod_path, mtree, node
    return None


def _has_unsafe_dunders(cls_node, extra_names=()):
    forbidden = {"__setattr__", "__delattr__", "__getattr__", "__getattribute__", *extra_names}
    for item in cls_node.body:
        if isinstance(item, (ast.FunctionDef, ast.AsyncFunctionDef)) and item.name in forbidden:
            return True
        if isinstance(item, ast.Assign):
            for tgt in item.targets:
                if isinstance(tgt, ast.Name) and tgt.id in extra_names:
                    return True
        elif isinstance(item, ast.AnnAssign) and isinstance(item.target, ast.Name) and item.target.id in extra_names:
            return True
    return False


def _call_name_has(node, needles):
    cur = node.func
    while isinstance(cur, ast.Attribute):
        if any(w in cur.attr for w in needles):
            return True
        cur = cur.value
    return isinstance(cur, ast.Name) and any(w in cur.id for w in needles)


def _closed_world_safety(root, protected_names, owner_node, owner_path, extra_write_attrs=()):
    """Check closed-world invariants for writes, subclasses, metaclasses, setattr, and mocks."""
    owner_name = owner_node.name
    owner_store_coords = {
        (n.lineno, n.col_offset) for item in owner_node.body
        if isinstance(item, (ast.FunctionDef, ast.AsyncFunctionDef))
        for n in ast.walk(item)
        if isinstance(n, ast.Attribute) and isinstance(n.ctx, (ast.Store, ast.Del))
    }
    check_attrs = {extra_write_attrs} if isinstance(extra_write_attrs, str) else set(extra_write_attrs)
    all_protected = protected_names | check_attrs
    mock_re = re.compile(r"\b(?:" + "|".join(re.escape(x) for x in sorted(all_protected)) + r")\b")
    prebuilt = _prebuilt(root)
    rel_owner = str(owner_path)
    subclasses = []
    if prebuilt is not None:
        for p, sfacts in prebuilt:
            (has_unknown_setattr, setattr_names, mock_unparsed,
             cb_names, attr_stores, _call_names, _sw_keys) = sfacts
            if has_unknown_setattr or not setattr_names.isdisjoint(all_protected):
                return False, subclasses
            for text in mock_unparsed:
                if mock_re.search(text):
                    return False, subclasses
            if owner_name in cb_names:
                _, full_facts = _full_facts(p)
                for sub_cls in full_facts[3].get(owner_name, ()):
                    subclasses.append((p, sub_cls))
            same_file = (str(p) == rel_owner)
            for attr in check_attrs:
                for is_del, lineno, col_offset in attr_stores.get(attr, ()):
                    if not same_file or is_del or (lineno, col_offset) not in owner_store_coords:
                        return False, subclasses
        return True, subclasses
    tokens = tuple({b"setattr", b"delattr", b"__setattr__", b"__delattr__", b"__getattr__",
                    b"__getattribute__", b"patch", b"Mock", *(n.encode() for n in all_protected)})
    files = _matching_facts(root, tokens)
    for p, _tree, facts in files:
        (has_unknown_setattr, setattr_names, mock_unparsed,
         class_bases, attr_stores, _call_names, _single_writes) = facts
        if has_unknown_setattr or not setattr_names.isdisjoint(all_protected):
            return False, subclasses
        for text in mock_unparsed:
            if mock_re.search(text):
                return False, subclasses
        for sub_cls in class_bases.get(owner_name, ()):
            subclasses.append((p, sub_cls))
        same_file = (str(p) == rel_owner)
        for attr in check_attrs:
            for is_del, lineno, col_offset in attr_stores.get(attr, ()):
                if not same_file or is_del or (lineno, col_offset) not in owner_store_coords:
                    return False, subclasses
    return True, subclasses


def _check_unique_enum(enum_path, enum_tree, enum_cls, root):
    """Verify enum_cls inherits Enum (or AutoName(Enum)) without custom __eq__/__ne__ and with unique values."""
    if _has_unsafe_dunders(enum_cls, ("__eq__", "__ne__")):
        return None
    for base in enum_cls.bases:
        if isinstance(base, ast.Name) and base.id in ("str", "int", "Enum"):
            continue
        if isinstance(base, ast.Name):
            res = _resolve_import_symbol(enum_tree, enum_path, root, base.id)
            if not res:
                return None
            _, _, base_cls = res
            if _has_unsafe_dunders(base_cls, ("__eq__", "__ne__")):
                return None
            if not any(isinstance(b, ast.Name) and b.id == "Enum" for b in base_cls.bases):
                return None
        else:
            return None
    if not enum_cls.bases:
        return None
    members = set()
    values = set()
    for stmt in enum_cls.body:
        if isinstance(stmt, ast.Expr) and isinstance(stmt.value, ast.Constant) and isinstance(stmt.value.value, str):
            continue
        if isinstance(stmt, ast.Assign) and len(stmt.targets) == 1 and isinstance(stmt.targets[0], ast.Name):
            m = stmt.targets[0].id
            if m in members or m.startswith("_"):
                return None
            if isinstance(stmt.value, ast.Call) and isinstance(stmt.value.func, ast.Name) and stmt.value.func.id == "auto" and not stmt.value.args and not stmt.value.keywords:
                val = ("auto", m)
            elif isinstance(stmt.value, ast.Constant) and type(stmt.value.value) in (str, int):
                val = (type(stmt.value.value), stmt.value.value)
            else:
                return None
            if val in values:
                return None
            members.add(m)
            values.add(val)
        else:
            return None
    return members if members else None


def identity_equivalence(change, before, after, root_dir="/sqlglot"):
    """Prove `is` <-> `==` / `is not` <-> `!=` equivalence under closed-world invariants."""
    try:
        diffs = list(_compare_op_delta(before, after))
    except ValueError:
        return None
    if len(diffs) != 1:
        return None
    chain = diffs[0]
    cmp_node = chain[-1]
    classes = [n for n in chain if isinstance(n, ast.ClassDef)]
    funcs = [n for n in chain if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef))]
    if len(classes) != 1 or not funcs:
        return None
    owner = classes[0]
    fn = funcs[-1]
    if not fn.args.args:
        return None
    self_name = fn.args.args[0].arg
    for node in ast.walk(fn):
        if isinstance(node, ast.Name) and node.id == self_name and isinstance(node.ctx, (ast.Store, ast.Del)):
            return None

    left, right = cmp_node.left, cmp_node.comparators[0]
    is_none_pair = False
    enum_info = None
    if isinstance(right, ast.Constant) and right.value is None:
        expr_side, is_none_pair = left, True
    elif isinstance(left, ast.Constant) and left.value is None:
        expr_side, is_none_pair = right, True
    elif isinstance(right, ast.Attribute) and isinstance(right.value, ast.Name):
        expr_side, enum_info = left, (right.value.id, right.attr)
    elif isinstance(left, ast.Attribute) and isinstance(left.value, ast.Name):
        expr_side, enum_info = right, (left.value.id, left.attr)
    else:
        return None

    if not (isinstance(expr_side, ast.Attribute) and isinstance(expr_side.value, ast.Name)
            and expr_side.value.id == self_name):
        return None
    attr_name = expr_side.attr
    root = Path(root_dir)
    owner_path = root / change.path
    if _has_unsafe_dunders(owner, (attr_name,)):
        return None

    # Gather all assignments to self.<attr_name> inside owner methods
    self_writes = []
    for item in owner.body:
        if not isinstance(item, (ast.FunctionDef, ast.AsyncFunctionDef)):
            continue
        m_self = item.args.args[0].arg if item.args.args else None
        for node in ast.walk(item):
            if isinstance(node, ast.Attribute) and node.attr == attr_name and isinstance(node.ctx, (ast.Store, ast.Del)):
                if not (isinstance(node.ctx, ast.Store) and m_self and isinstance(node.value, ast.Name) and node.value.id == m_self):
                    return None
            if isinstance(node, ast.AugAssign) and isinstance(node.target, ast.Attribute) and node.target.attr == attr_name:
                return None
            if isinstance(node, ast.Assign):
                for tgt in node.targets:
                    if isinstance(tgt, ast.Attribute) and tgt.attr == attr_name:
                        self_writes.append((item, node.value))
            elif isinstance(node, ast.AnnAssign) and isinstance(node.target, ast.Attribute) and node.target.attr == attr_name:
                if node.value is not None:
                    self_writes.append((item, node.value))
    if not self_writes:
        return None

    if is_none_pair:
        if owner.bases or owner.keywords:
            return None
        # Every write must be None or list(self.<c_attr>.values())[0] where elements are a pure object.__eq__ class
        container_attrs = set()
        for fn_node, rhs in self_writes:
            if isinstance(rhs, ast.Constant) and rhs.value is None:
                continue
            if (isinstance(rhs, ast.Subscript)
                    and isinstance(rhs.slice, ast.Constant) and rhs.slice.value == 0
                    and isinstance(rhs.value, ast.Call) and isinstance(rhs.value.func, ast.Name) and rhs.value.func.id == "list"
                    and len(rhs.value.args) == 1 and not rhs.value.keywords
                    and isinstance(rhs.value.args[0], ast.Call)
                    and isinstance(rhs.value.args[0].func, ast.Attribute) and rhs.value.args[0].func.attr == "values"
                    and not rhs.value.args[0].args and not rhs.value.args[0].keywords
                    and isinstance(rhs.value.args[0].func.value, ast.Attribute)
                    and isinstance(rhs.value.args[0].func.value.value, ast.Name)
                    and fn_node.args.args and rhs.value.args[0].func.value.value.id == fn_node.args.args[0].arg):
                container_attrs.add(rhs.value.args[0].func.value.attr)
            else:
                return None
        if len(container_attrs) != 1:
            return None
        c_attr = next(iter(container_attrs))
        # Verify container_attr is only initialized once in owner.__init__ with dict[..., ElemClass]
        init_fn = next((f for f in owner.body if isinstance(f, ast.FunctionDef) and f.name == "__init__"), None)
        if not init_fn:
            return None
        elem_names = set()
        c_writes = 0
        for item in owner.body:
            if isinstance(item, (ast.FunctionDef, ast.AsyncFunctionDef)):
                for node in ast.walk(item):
                    if isinstance(node, ast.Attribute) and node.attr == c_attr and isinstance(node.ctx, (ast.Store, ast.Del)):
                        c_writes += 1
        if c_writes != 1:
            return None
        for node in init_fn.body:
            if isinstance(node, ast.Assign) and len(node.targets) == 1 and isinstance(node.targets[0], ast.Attribute) and node.targets[0].attr == c_attr and isinstance(node.value, ast.Name):
                param = next((a for a in init_fn.args.args if a.arg == node.value.id), None)
                if param and isinstance(param.annotation, ast.Subscript) and len(getattr(param.annotation.slice, "elts", [])) == 2:
                    val_type = param.annotation.slice.elts[1]
                    if isinstance(val_type, ast.Name):
                        elem_names.add(val_type.id)
        if len(elem_names) != 1:
            return None
        elem_name = next(iter(elem_names))
        elem_res = _resolve_import_symbol(before, owner_path, root, elem_name)
        if not elem_res:
            return None
        elem_path, _, elem_cls = elem_res
        if elem_cls.bases or elem_cls.keywords or _has_unsafe_dunders(elem_cls, ("__eq__", "__ne__")):
            return None
        ok, subclasses = _closed_world_safety(
            root, {owner.name, attr_name, c_attr, elem_name}, owner, owner_path, {attr_name}
        )
        if not ok or subclasses:
            return None
        # Ensure elem_cls has no subclasses or external mocks and owner(...) is only called with real elem_cls tables
        prebuilt = _prebuilt(root)
        if prebuilt is not None:
            for p, sfacts in prebuilt:
                cb_names, call_names = sfacts[3], sfacts[5]
                if elem_name in cb_names:
                    tree, _ = _full_facts(p)
                    b_res = _resolve_import_symbol(tree, p, root, elem_name)
                    if not b_res or (b_res[0], b_res[2].name, b_res[2].lineno) == (elem_path, elem_cls.name, elem_cls.lineno):
                        return None
                if owner.name in call_names and not str(p).startswith(str(root / "sqlglot/executor/")):
                    return None
        else:
            for p, tree, facts in _matching_facts(root, (elem_name.encode(), owner.name.encode())):
                class_bases, call_names = facts[3], facts[5]
                if elem_name in class_bases:
                    b_res = _resolve_import_symbol(tree, p, root, elem_name)
                    if not b_res or (b_res[0], b_res[2].name, b_res[2].lineno) == (elem_path, elem_cls.name, elem_cls.lineno):
                        return None
                if owner.name in call_names:
                    # All callers must live in modules that do not construct fake objects for tables
                    if not str(p).startswith(str(root / "sqlglot/executor/")):
                        return None
        return "identity none equivalence", 0

    # Unique-value Enum equivalence
    enum_name, member_name = enum_info
    enum_res = _resolve_import_symbol(before, owner_path, root, enum_name)
    if not enum_res:
        return None
    enum_path, enum_tree, enum_cls = enum_res
    members = _check_unique_enum(enum_path, enum_tree, enum_cls, root)
    if not members or member_name not in members:
        return None
    # Check metaclass on owner if present
    meta_name = None
    for kw in owner.keywords:
        if kw.arg == "metaclass" and isinstance(kw.value, ast.Name):
            meta_name = kw.value.id
            meta_res = _resolve_import_symbol(before, owner_path, root, meta_name)
            if not meta_res or _has_unsafe_dunders(meta_res[2], (attr_name,)):
                return None

    class_attrs = set()
    for fn_node, rhs in self_writes:
        if isinstance(rhs, ast.Call) and isinstance(rhs.func, ast.Name) and rhs.func.id == enum_name:
            continue
        if (isinstance(rhs, ast.Attribute) and isinstance(rhs.value, ast.Name)
                and fn_node.args.args and rhs.value.id == fn_node.args.args[0].arg):
            class_attrs.add(rhs.attr)
        else:
            return None
    protected = {owner.name, attr_name, enum_name, *class_attrs}
    if meta_name:
        protected.add(meta_name)
    ok, subclasses = _closed_world_safety(root, protected, owner, owner_path, {attr_name})
    if not ok:
        return None
    for _, sub_cls in subclasses:
        if _has_unsafe_dunders(sub_cls, (attr_name,)):
            return None
    # Verify every write/declaration to class_attrs across the entire repo is strictly EnumClass.<MEMBER>
    if class_attrs:
        prebuilt = _prebuilt(root)
        if prebuilt is not None:
            write_files = [
                (p, *_full_facts(p))
                for p, sfacts in prebuilt
                if not class_attrs.isdisjoint(sfacts[6])
            ]
        else:
            write_files = _matching_facts(root, tuple(ca.encode() for ca in class_attrs))
        for p, tree, facts in write_files:
            # Check EnumClass is bound cleanly in this file if any class_attr write appears
            single_writes = facts[6]
            writes_here = [v for ca in class_attrs for v in single_writes.get(ca, ())]
            if writes_here:
                local_enum = _resolve_import_symbol(tree, p, root, enum_name)
                if not local_enum or (local_enum[0], local_enum[2].name, local_enum[2].lineno) != (enum_path, enum_cls.name, enum_cls.lineno):
                    return None
                for val in writes_here:
                    if not (isinstance(val, ast.Attribute) and isinstance(val.value, ast.Name)
                            and val.value.id == enum_name and val.attr in members):
                        return None
    return "identity enum equivalence", 0


if __name__ == "__main__":
    import sys
    build_facts(sys.argv[1], sys.argv[2])

