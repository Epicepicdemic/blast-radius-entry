"""Follow writes through unpacking, iteration, and fields before applying shell exemptions."""
import ast
from collections import defaultdict
from functools import lru_cache


def identity(node):
    if isinstance(node, ast.Name):
        return ('name', node.id)
    if isinstance(node, ast.Attribute):
        # Even a different receiver can refer to the same instance.
        return ('field', node.attr)
    return None


@lru_cache(64)
def sources(fn):
    result = defaultdict(list)

    def record(target, value, projected=False):
        if isinstance(target, (ast.Tuple, ast.List)):
            items = value.elts if isinstance(value, (ast.Tuple, ast.List)) else ()
            determined = len(items) == len(target.elts) and not any(isinstance(i, ast.Starred) for i in (*items, *target.elts))
            for index, child in enumerate(target.elts):
                record(child, items[index] if determined else None, True)
        elif isinstance(target, ast.Starred):
            record(target.value, None, True)
        elif identity(target) and (projected or isinstance(target, ast.Attribute)):
            result[identity(target)].append(value)

    for node in ast.walk(fn):
        if isinstance(node, (ast.For, ast.AsyncFor, ast.comprehension)):
            items = node.iter.elts if isinstance(node.iter, (ast.Tuple, ast.List, ast.Set)) else ()
            if items and not any(isinstance(x, ast.Starred) for x in items):
                for item in items:
                    record(node.target, item, True)
            else:
                # The iterator may yield a shared object distinct from its own shell.
                record(node.target, None, True)
        if isinstance(node, (ast.Assign, ast.AnnAssign, ast.NamedExpr)):
            for target in node.targets if isinstance(node, ast.Assign) else (node.target,):
                record(target, node.value)
        if isinstance(node, (ast.With, ast.AsyncWith)):
            for item in node.items:
                if item.optional_vars:
                    record(item.optional_vars, None, True)
    return result
