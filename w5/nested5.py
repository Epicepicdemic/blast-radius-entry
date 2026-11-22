"""Localize a delayed edit when the enclosing closure bindings are stable."""
import ast
from types import CodeType

from frontier import digests, frontier, same


def codes(fn):
    root = ast.Module(body=[fn], type_ignores=[])
    return next(c for c in compile(root, '<scope>', 'exec', dont_inherit=True).co_consts
                if isinstance(c, CodeType))


def lexical(code):
    return (code.co_cellvars, code.co_freevars, code.co_flags,
            code.co_argcount, code.co_posonlyargcount, code.co_kwonlyargcount)


def closure_ranges(old, new):
    """Return old lines dominating the changed behavior or defer to the existing bound."""
    if not any(isinstance(n, ast.FunctionDef) for stmt in old.body for n in ast.walk(stmt)):
        return None
    disallowed = (ast.ClassDef, ast.AsyncFunctionDef, ast.Global, ast.Yield, ast.YieldFrom)
    if any(isinstance(n, disallowed) for fn in (old, new) for st in fn.body for n in ast.walk(st)):
        return None
    if digests(old) != digests(new) or len(old.body) != len(new.body):
        return None
    before, after = codes(old), codes(new)
    if lexical(before) != lexical(after):
        return None
    differences = [(a, b) for a, b in zip(old.body, new.body) if not same(a, b)]
    if not differences:
        return None
    changed_nested = [(a, b) for a, b in differences
                      if isinstance(a, ast.FunctionDef) or isinstance(b, ast.FunctionDef)]
    if changed_nested:
        if len(differences) != 1:
            return None
        a, b = changed_nested[0]
        if not (isinstance(a, ast.FunctionDef) and isinstance(b, ast.FunctionDef)
                and not a.decorator_list and digests(a) == digests(b)
                and ast.get_docstring(a, clean=False) == ast.get_docstring(b, clean=False)):
            return None
        if any(isinstance(n, ast.FunctionDef) for fn in (a, b) for stmt in fn.body for n in ast.walk(stmt)):
            return None
        if any(sum(isinstance(n, ast.FunctionDef) and n.name == a.name for n in ast.walk(fn)) != 1
               for fn in (old, new)):
            return None
        def child(parent, fn):
            return next((c for c in parent.co_consts if isinstance(c, CodeType)
                         and c.co_name == fn.name and c.co_firstlineno == fn.lineno), None)
        ac, bc = child(before, a), child(after, b)
        if ac is None or bc is None or lexical(ac) != lexical(bc):
            return None
        if frozenset(ac.co_varnames) != frozenset(bc.co_varnames):
            return [(a.body[0].lineno, a.end_lineno)]
        return frontier(a, b)
    if before.co_varnames != after.co_varnames:
        return None
    for a, b in differences:
        for tree in (a, b):
            for n in ast.walk(tree):
                if isinstance(n, (ast.FunctionDef, ast.Nonlocal)):
                    return None
                if (isinstance(n, ast.Name) and not isinstance(n.ctx, ast.Load) and
                        n.id in (*before.co_cellvars, *before.co_freevars)):
                    return None
    return frontier(old, new)
