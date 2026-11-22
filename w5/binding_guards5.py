"""A name may be missing only if neither the pin nor the complete postimage binds it."""
import ast
import builtins

from shared_writes import bindings


def unbound(node, scope, census):
    if (not census or census.module not in census.c.modules or
            not isinstance(scope, (ast.FunctionDef, ast.AsyncFunctionDef)) or
            not isinstance(node, ast.Name) or not isinstance(node.ctx, ast.Load) or
            node.id in vars(builtins)):
        return False
    if (node.id in census.bindings(scope) or census.enclosing_binds(scope, node.id) or
            census.module_binds(node.id)):
        return False
    names = getattr(census, 'postimage_names', None)
    if names is None:
        # The shared-write collector includes import aliases, function, async function,
        # class and pattern bindings, even in mutually exclusive lexical scopes.
        names = set(bindings(census.tree))
        from rules5 import facts
        names.update(facts()['dynamic_names'])
        for candidate in ast.walk(census.tree):
            if isinstance(candidate, ast.Name) and candidate.id in {
                'exec', 'eval', 'globals', 'locals', 'vars', 'setattr', '__builtins__', '__dict__'
            }:
                names.add('*')
            if isinstance(candidate, ast.Attribute) and candidate.attr in {'__dict__', 'f_globals', 'f_locals'}:
                names.add('*')
        census.postimage_names = names
    return '*' not in names and node.id not in names


def new_callable(call, scope, census):
    """A newly introduced Python binding has no pinned effect summary."""
    if not census or not isinstance(call.func, ast.Name) or not isinstance(scope, (ast.FunctionDef, ast.AsyncFunctionDef)):
        return False
    name = call.func.id
    if name in vars(builtins) or census.module_binds(name):
        return False
    table = getattr(census, 'callable_bindings5', None)
    if table is None:
        table = set()
        for n in ast.walk(census.tree):
            if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
                table.add(n.name)
            elif isinstance(n, ast.alias):
                table.add(n.asname or n.name.partition('.')[0])
        census.callable_bindings5 = table
    return name in table or '*' in table
