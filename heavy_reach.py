"""Use observations from the pinned heavy calculation to avoid an identical replay."""

import ast
from copy import copy
from functools import lru_cache
import importlib
import json
from pathlib import Path

from patching import parsed_source
from selector import equal_trees


@lru_cache(maxsize=1)
def footprints():
    try:
        return json.loads(Path(__file__).with_name("heavy-reach.json").read_bytes())
    except (OSError, ValueError):
        return {}


def string(node):
    return isinstance(node, ast.Constant) and type(node.value) is str


def no_defaults(node):
    return isinstance(node, ast.Lambda) and not node.args.defaults and not any(node.args.kw_defaults)


def simple_key(node):
    return string(node) or (
        isinstance(node, ast.Attribute)
        and isinstance(node.value, ast.Name)
        and node.value.id == "exp"
        and not node.attr.startswith("_")
    )


def inert_pair(key, value):
    if key is None:
        # The only expanded entries we admit allocate a plain dictionary from literal keys.
        return (
            isinstance(value, ast.Call)
            and not value.keywords
            and len(value.args) == 2
            and isinstance(value.func, ast.Attribute)
            and value.func.attr == "fromkeys"
            and isinstance(value.func.value, ast.Name)
            and value.func.value.id == "dict"
            and isinstance(value.args[0], ast.Tuple)
            and all(string(k) for k in value.args[0].elts)
            and no_defaults(value.args[1])
        )
    return simple_key(key) and (
        no_defaults(value)
        or isinstance(value, (ast.Name, ast.Constant))
        or isinstance(value, ast.Attribute)
        and isinstance(value.value, ast.Name)
        and value.value.id in ("exp", "TokenType")
        and not value.attr.startswith("_")
    )


def field_change(old, new):
    """Locate a single changed statement, preserving every surrounding declaration."""
    if len(old) != len(new):
        return None
    diffs = [(a, b) for a, b in zip(old, new) if not equal_trees(a, b)]
    return diffs[0] if len(diffs) == 1 else None


def same_header(a, b):
    return type(a) is type(b) and all(
        equal_trees(getattr(a, f), getattr(b, f)) for f in a._fields if f != "body"
    )


def table_change(change, old, new, rules, *, absent=False):
    classes = field_change(old.body, new.body)
    if not classes:
        return False
    cls, other = classes
    if not isinstance(cls, ast.ClassDef) or not same_header(cls, other):
        return False
    names = [cls.name]
    while True:
        statements = field_change(cls.body, other.body)
        if not statements:
            return False
        lhs, rhs = statements
        if not isinstance(lhs, ast.ClassDef):
            break
        if not absent or not same_header(lhs, rhs):
            return False
        cls, other = lhs, rhs
        names.append(cls.name)
    if not (
        isinstance(lhs, ast.Assign)
        and isinstance(rhs, ast.Assign)
        and len(lhs.targets) == 1
        and isinstance(lhs.targets[0], ast.Name)
        and equal_trees(lhs.targets, rhs.targets)
        and lhs.type_comment == rhs.type_comment
        and isinstance(lhs.value, ast.Dict)
        and isinstance(rhs.value, ast.Dict)
    ):
        return False
    attr = lhs.targets[0].id
    if attr not in ("TRANSFORMS", "FUNCTIONS", "KEYWORDS"):
        return False
    location = [change.path[:-3].replace("/", "."), ".".join(names), attr]
    if not absent and location not in rules["tables"]:
        if location not in rules["value_only"] or not equal_trees(lhs.value.keys, rhs.value.keys):
            return False
    for stmt in cls.body[cls.body.index(lhs) + 1 :]:
        if not any(
            isinstance(n, ast.Name) and isinstance(n.ctx, ast.Load) and n.id == attr for n in ast.walk(stmt)
        ):
            continue
        call = stmt.value if isinstance(stmt, ast.Expr) else None
        if not (
            isinstance(call, ast.Call)
            and isinstance(call.func, ast.Attribute)
            and call.func.attr == "pop"
            and isinstance(call.func.value, ast.Name)
            and call.func.value.id == attr
            and 1 <= len(call.args) <= 2
            and string(call.args[0])
            and not call.keywords
            and equal_trees(lhs.value.keys, rhs.value.keys)
        ):
            return False

    # Unchanged entries can contain arbitrary setup code. Only changed entries must be inert.
    def entries(node):
        return [(ast.dump(k) if k else "", ast.dump(v)) for k, v in zip(node.keys, node.values)]

    from difflib import SequenceMatcher

    a, b = lhs.value, rhs.value
    for tag, i, j, k, l in SequenceMatcher(None, entries(a), entries(b), autojunk=False).get_opcodes():
        if tag != "equal" and not all(
            inert_pair(key, val)
            for node, start, end in ((a, i, j), (b, k, l))
            for key, val in zip(node.keys[start:end], node.values[start:end])
        ):
            return False
    return True


def unused_parser_method(change, old, new, rules):
    pair = field_change(old.body, new.body)
    if not pair or not isinstance(pair[0], ast.ClassDef) or not same_header(*pair):
        return False
    cls, changed = pair
    if len(cls.body) != len(changed.body) + 1:
        return False
    deferred = any(
        isinstance(n, ast.ImportFrom)
        and n.module == "__future__"
        and any(a.name == "annotations" for a in n.names)
        for n in old.body
    )
    module = change.path[:-3].replace("/", ".")
    for i, fn in enumerate(cls.body):
        if not (
            isinstance(fn, ast.FunctionDef)
            and not fn.decorator_list
            and deferred
            and not fn.args.defaults
            and not any(fn.args.kw_defaults)
            and [module, cls.name, fn.name] in rules["tables"]
        ):
            continue
        if any(
            isinstance(n, ast.Name) and n.id == fn.name
            for stmt in cls.body[i + 1 :]
            for n in ast.walk(stmt)
        ):
            return False
        if equal_trees(cls.body[:i] + cls.body[i + 1 :], changed.body):
            return True
    return False


def unread_constant(change, old, new, rules, *, absent=False):
    reads = rules["globals"].get(change.path)
    if len(old.body) != len(new.body) + 1 or (not absent and (reads is None or "*" in reads)):
        return False
    for i, stmt in enumerate(old.body):
        if (
            isinstance(stmt, ast.Assign)
            and len(stmt.targets) == 1
            and isinstance(stmt.targets[0], ast.Name)
            and stmt.targets[0].id.isupper()
            and (absent or stmt.targets[0].id not in reads)
            and isinstance(stmt.value, ast.Tuple)
            and all(
                isinstance(v, ast.Attribute) and isinstance(v.value, ast.Name) and v.value.id == "exp"
                for v in stmt.value.elts
            )
            and equal_trees(old.body[:i] + old.body[i + 1 :], new.body)
        ):
            return True
    return False


def argument_key(node, arg):
    if (
        isinstance(node, ast.Call)
        and len(node.args) == 1
        and string(node.args[0])
        and not node.keywords
        and isinstance(node.func, ast.Attribute)
        and node.func.attr == "get"
        and isinstance(node.func.value, ast.Attribute)
        and node.func.value.attr == "args"
        and isinstance(node.func.value.value, ast.Name)
        and node.func.value.value.id == arg
    ):
        return node.args[0].value
    return None


class FoldAbsent(ast.NodeTransformer):
    """Fold only local names with a known None value and builtin boolean identities."""

    def __init__(self, absent):
        self.absent = absent

    def visit_Name(self, node):
        if isinstance(node.ctx, ast.Load) and node.id in self.absent:
            return ast.Constant(None)
        return node

    # Nested scopes may shadow the function's locals. Leave them intact.
    def visit_Lambda(self, node):
        return node

    visit_GeneratorExp = visit_ListComp = visit_SetComp = visit_DictComp = visit_Lambda

    def visit_Compare(self, node):
        node = self.generic_visit(copy(node))
        if (
            len(node.ops) == 1
            and isinstance(node.ops[0], (ast.Is, ast.IsNot))
            and all(
                isinstance(v, ast.Constant) and v.value is None for v in (node.left, node.comparators[0])
            )
        ):
            return ast.Constant(isinstance(node.ops[0], ast.Is))
        return node

    def visit_BoolOp(self, node):
        parts = []
        for value in node.values:
            v = self.visit(value)
            if isinstance(node.op, ast.And) and isinstance(v, ast.Constant) and v.value is False:
                parts.append(v)
                break
            parts.append(v)
        if (
            isinstance(node.op, ast.Or)
            and len(parts) == 2
            and isinstance(parts[1], ast.Constant)
            and parts[1].value is False
            and isinstance(parts[0], ast.Call)
            and isinstance(parts[0].func, ast.Name)
            and parts[0].func.id in ("any", "all")
        ):
            return parts[0]  # Both unshadowed builtins return an exact bool.
        return parts[0] if len(parts) == 1 else ast.BoolOp(op=node.op, values=parts)


def predicate_body(fn, observed_keys):
    from copy import deepcopy

    # Keep the proof in the read-only prefix. No other statement can mutate the
    # argument before these dictionary reads. An arbitrary final expression must match exactly.
    if (
        not fn.body
        or not isinstance(fn.body[-1], ast.Return)
        or len(fn.args.args) != 1
        or fn.args.args[0].arg in ("any", "all")
        or fn.args.posonlyargs
        or fn.args.kwonlyargs
    ):
        return None
    arg = fn.args.args[0].arg
    absent = set()
    prefix = []
    defined = set()
    for stmt in fn.body[:-1]:
        if (
            isinstance(stmt, ast.Assign)
            and len(stmt.targets) == 1
            and isinstance(stmt.targets[0], ast.Name)
            and stmt.targets[0].id not in (arg, "any", "all")
        ):
            key = argument_key(stmt.value, arg)
            if key is None:
                return None
            name = stmt.targets[0].id
            if name in defined:
                return None
            defined.add(name)
            if key not in observed_keys:
                absent.add(name)
                prefix.append(ast.Assign(targets=stmt.targets, value=ast.Constant(None)))
            else:
                absent.discard(name)
                prefix.append(stmt)
        elif (
            isinstance(stmt, ast.If)
            and not stmt.orelse
            and len(stmt.body) == 1
            and isinstance(stmt.body[0], ast.Return)
            and isinstance(stmt.body[0].value, ast.Constant)
        ):
            key = argument_key(stmt.test, arg)
            if key is None or key in observed_keys:
                return None
        else:
            return None
    expression = fn.body[-1].value
    # Avoid assignments or local namespace reflection in the expression being compared.
    if any(
        isinstance(n, ast.NamedExpr)
        or isinstance(n, ast.Name)
        and n.id in {"locals", "globals", "vars", "eval", "exec", "sys", "inspect"}
        for n in ast.walk(expression)
    ):
        return None
    folded = FoldAbsent(absent).visit(deepcopy(expression))
    referenced = {n.id for n in ast.walk(folded) if isinstance(n, ast.Name)}
    prefix = [
        stmt for stmt in prefix if stmt.targets[0].id not in absent or stmt.targets[0].id in referenced
    ]
    return [*prefix, ast.Return(value=folded)]


def unchanged_predicate(change, old, new, rules):
    pair = field_change(old.body, new.body)
    if not pair or not isinstance(pair[0], ast.FunctionDef) or not same_header(*pair):
        return False
    fn, other = pair
    keys = rules["entry_keys"].get(change.path + ":" + fn.name)
    if keys is None:
        return False
    left, right = predicate_body(fn, keys), predicate_body(other, keys)
    return left is not None and right is not None and equal_trees(left, right)


def edits_in_cold_arms(old, new, lines):
    """Admit edits only inside existing, untaken arms of unchanged if tests."""
    from bisect import bisect_left

    if equal_trees(old, new):
        return True
    if type(old) is not type(new):
        return False
    if isinstance(old, list):
        return len(old) == len(new) and all(edits_in_cold_arms(a, b, lines) for a, b in zip(old, new))
    if isinstance(old, ast.If):
        if not equal_trees(old.test, new.test):
            return False
        for before, after in ((old.body, new.body), (old.orelse, new.orelse)):
            if equal_trees(before, after):
                continue
            # The first statement must execute a line when this arm is taken.
            # A bare literal, pass, or optimized-away assert would not suffice.
            if before and after:
                first = before[0]
                runs = (
                    isinstance(first, (ast.Assign, ast.Return, ast.Raise))
                    or isinstance(first, ast.Expr)
                    and isinstance(first.value, ast.Call)
                )
                i = bisect_left(lines, first.lineno)
                if runs and (i == len(lines) or lines[i] > before[-1].end_lineno):
                    continue
            if not edits_in_cold_arms(before, after, lines):
                return False
        return True
    if isinstance(old, ast.AST):
        return all(edits_in_cold_arms(getattr(old, k), getattr(new, k), lines) for k in old._fields)
    return False


def unchanged(task, changes, hot, *, screened_import=False):
    if len(changes) != 1:
        return False
    change = changes[0]
    path = change.path
    if not path.startswith("sqlglot/") or not path.endswith(".py"):
        return False
    rules = footprints().get(task)
    if not rules:
        return False
    absent = path not in rules["paths"]
    optimizer = path.startswith("sqlglot/optimizer/")
    dialect_table = path.startswith(("sqlglot/generators/", "sqlglot/parsers/", "sqlglot/dialects/"))
    module_name = path[:-3].replace("/", ".").removesuffix(".__init__")
    if task == "generator":
        # The pinned original test ran every dialect. Reuse it only for a
        # parser-local declaration that none of those generator loops consulted.
        if not path.startswith("sqlglot/parsers/") or absent:
            return False
        old, new = parsed_source(change.before), parsed_source(change.after)
        if not equal_trees(old.type_ignores, new.type_ignores):
            return False
        if not (unused_parser_method(change, old, new, rules) or table_change(change, old, new, rules)):
            return False
        importlib.import_module(module_name)
        return True
    if absent and screened_import and hot is None:
        # The import snapshot has checked process state and collection. This fresh
        # phase-one child has not loaded the file, and the pinned check never opens it.
        import sys

        if module_name not in sys.modules:
            return True
    if not absent and hot and all(edit[0] == path for edit in hot):
        calls = rules["functions"].get(path)
        cold = calls is not None and all(name not in calls for _, name, _, _ in hot)
        if not cold and calls is not None and task == "tpc" and path in rules["lines"]:
            from cone import functions

            original = functions(change.before)[1]
            patched = functions(change.after)[1]
            cold = all(
                name in original
                and name in patched
                and same_header(original[name], patched[name])
                and (
                    name not in calls
                    or edits_in_cold_arms(original[name].body, patched[name].body, rules["lines"][path])
                )
                for _, name, _, _ in hot
            )
        if cold:
            from patching import compiled_source
            from proofs import baseline_code, scope_changed

            if not scope_changed(baseline_code(change.before, path), compiled_source(change.after, path)):
                importlib.import_module(module_name)
                return True
    if absent and hot and all(edit[0] == path for edit in hot):
        known = True
    elif optimizer or dialect_table:
        old, new = parsed_source(change.before), parsed_source(change.after)
        if not equal_trees(old.type_ignores, new.type_ignores):
            return False
        if optimizer:
            known = unread_constant(change, old, new, rules, absent=absent) or (
                hot and unchanged_predicate(change, old, new, rules)
            )
        else:
            known = table_change(change, old, new, rules, absent=absent)
    else:
        return False
    if known:
        # Even a private edit can make collection fail. This check runs in the
        # bounded overlay child before the parent can accept its receipt.
        importlib.import_module(path[:-3].replace("/", ".").removesuffix(".__init__"))
    return bool(known)
