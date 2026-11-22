"""Pin-only bounds for edits to keyed dispatch dictionaries and ordinary function bodies."""
import ast

from impact import family_path
from patching import compiled_source

def literal_key(node):
    return isinstance(node, ast.Constant) and type(node.value) is str

def passive_handler(node):
    # Constructing a default-free lambda has no eager name resolution. Constrain
    # its eventual calls to fixed expression constructors and the pinned list accessor.
    if not isinstance(node, ast.Lambda) or node.args.defaults or any(node.args.kw_defaults):
        return False
    args = {arg.arg for arg in node.args.args + node.args.posonlyargs}
    def value(n):
        if isinstance(n, ast.Name):
            return n.id in args
        if isinstance(n, ast.Constant):
            return True
        if not isinstance(n, ast.Call):
            return False
        func = n.func
        getter = isinstance(func, ast.Name) and func.id == "seq_get"
        ctor = (isinstance(func, ast.Attribute) and isinstance(func.value, ast.Name)
                and func.value.id == "exp" and func.attr[:1].isupper())
        return (getter or ctor) and all(value(a) for a in n.args) and all(
            kw.arg is not None and value(kw.value) for kw in n.keywords)
    return value(node.body)


def deferred_rows(d):
    """Strip only inert string-keyed delayed callbacks. Preserve other evaluation order."""
    if not isinstance(d, ast.Dict):
        return None
    eager = []
    for key, v in zip(d.keys, d.values):
        if literal_key(key) and passive_handler(v):
            continue
        if key is None and isinstance(v, ast.Call) and len(v.args) == 2 and not v.keywords:
            f = v.func
            if (isinstance(f, ast.Attribute) and f.attr == "fromkeys" and
                    isinstance(f.value, ast.Name) and f.value.id == "dict" and
                    isinstance(v.args[0], ast.Tuple) and all(literal_key(k) for k in v.args[0].elts)
                    and passive_handler(v.args[1])):
                continue
        eager.append((None if key is None else ast.dump(key), ast.dump(v)))
    return eager


def deferred_table(index, ch, name, old, new):
    if (not family_path(ch.path) or not ch.path.startswith("sqlglot/parsers/") or
            name.rsplit(".", 1)[-1] != "FUNCTIONS"):
        return None
    # All new delayed ASTs must already exist in the old table. A new spelling/key may
    # choose an existing parser, but the patch cannot introduce a novel effectful handler.
    if not isinstance(old, ast.Dict) or not isinstance(new, ast.Dict):
        return None
    old_handlers = {ast.dump(n) for n in ast.walk(old) if isinstance(n, ast.Lambda)}
    if any(ast.dump(n) not in old_handlers for n in ast.walk(new) if isinstance(n, ast.Lambda)):
        return None
    if deferred_rows(old) != deferred_rows(new):
        return None
    # Builtins and the expression module must not be shadowed. Whole-module parsing also
    # rejects a fragment that changes the syntax outside the original class assignment.
    from patching import parsed_source
    for tree in (parsed_source(ch.before), parsed_source(ch.after)):
        if any(isinstance(n, ast.Name) and n.id == "dict" and isinstance(n.ctx, (ast.Store, ast.Del))
               or isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)) and n.name == "dict"
               or isinstance(n, ast.alias) and (n.asname or n.name.split(".")[0]) == "dict" for n in ast.walk(tree)):
            return None
    return index.family(ch.path)


def coverage_bound(index, ix, changes, hot, writers, protected):
    # The branch's plain-body checks are additional to release scope, writer and source
    # checks. A coverage mask never discharges a protected reader or an unknown writer.
    if len(changes) != 1 or hot is None or writers or protected == ix.all:
        return None
    import coverage_skip
    from proofs import baseline_code, scope_changed
    ch = changes[0]
    section = ix.section(ch.path)
    if section is None or scope_changed(baseline_code(ch.before, ch.path), compiled_source(ch.after, ch.path)):
        return None
    mask = coverage_skip.patch_mask(index, changes)
    if mask is None:
        return None
    # Include cold execution of the whole touched function. This preserves callers with
    # alternate initialization paths, plus any source and code-object inspectors.
    cold = 0
    for path, name, old_line, _ in hot:
        if path != ch.path:
            return None
        region = section["functions"].get(name)
        if region is None:
            return None
        for n in range(region[1], region[2]+1):
            ptr = section["cold_lines"].get(n)
            if ptr is not None:
                cold |= ix.bits(ptr)
    return mask | cold | protected | ix.hit(section, "opens") | ix.reflect(ch.path)


def stress_obligation(ix, changes):
    """Key-set changes can change tokenizer trie size and trigger independent resource limits."""
    from impact import physical_lines
    from regions import changed_declaration
    for ch in changes:
        section = ix.section(ch.path)
        if not section:
            continue
        points = ch.removed | ch.insertions
        names = ix.meta["token_tables"]
        touched = [row for row in section.get("regions", ()) if row[2].split(".")[-1] in names
                   and any(row[0] <= n <= row[1] for n in points)]
        if touched:
            try:
                row = changed_declaration(ch, section, physical_lines(ch.before), physical_lines(ch.after))
                if row and row[0].split(".")[-1] in names:
                    a,b=row[1:3]
                    if isinstance(a,ast.Dict) and isinstance(b,ast.Dict):
                        keys = lambda d: [ast.dump(k) if k is not None else None for k in d.keys]
                        if keys(a)==keys(b):
                            continue
            except (ValueError, SyntaxError):
                pass
            return ix.bits(ix.meta["stress"])
    return 0
