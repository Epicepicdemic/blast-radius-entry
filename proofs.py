"""Prove where a changed instruction, delayed value or class binding can first be observed."""
import ast
import dis
from functools import lru_cache
import marshal
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


def scope_changed(old, new):
    # Binding a name anywhere in a function can change an untouched earlier
    # load. Generator and coroutine flags can likewise change the call itself.
    fields = ("co_qualname", "co_flags", "co_varnames", "co_freevars", "co_cellvars")
    if any(getattr(old, key) != getattr(new, key) for key in fields):
        return True
    children = lambda code: [c for c in code.co_consts if isinstance(c, types.CodeType)]
    left, right = children(old), children(new)
    return len(left) != len(right) or any(scope_changed(a, b) for a, b in zip(left, right))
