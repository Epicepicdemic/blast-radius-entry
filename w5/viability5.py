"""Decline a live verification attempt for structural failures likely to survive it."""
import ast
from frontier import same
from impact import physical_lines
from patching import parsed_source


def dependency_cycle(ix, change, old, new):
    imports = ix.section('@imports') or {}
    existing = {ast.dump(n) for n in old.body if isinstance(n, (ast.Import, ast.ImportFrom))}
    for node in new.body:
        if isinstance(node, (ast.ClassDef, ast.FunctionDef, ast.AsyncFunctionDef)):
            break
        if not isinstance(node, ast.ImportFrom) or node.level or not node.module or ast.dump(node) in existing:
            continue
        start = node.module.replace('.', '/') + '.py'
        pending = [start]
        visited = set()
        while pending:
            path = pending.pop()
            if path == change.path:
                return True
            if path not in visited:
                visited.add(path)
                pending.extend(imports.get(path, ()))
    return False


def removed_slot(old, new, change):
    added_lines = change.added
    for owner in old.body:
        if not isinstance(owner, ast.ClassDef):
            continue
        other = next((n for n in new.body if isinstance(n,ast.ClassDef) and n.name==owner.name), None)
        if other is None:
            continue
        def slots(cls):
            for st in cls.body:
                if (isinstance(st,ast.Assign) and len(st.targets)==1 and
                        isinstance(st.targets[0],ast.Name) and st.targets[0].id=='__slots__' and
                        isinstance(st.value,(ast.Tuple,ast.List)) and
                        all(isinstance(v,ast.Constant) and type(v.value) is str for v in st.value.elts)):
                    return st, {v.value for v in st.value.elts}
            return None,set()
        before,names = slots(owner)
        after,keep = slots(other)
        if before and after and names-keep and all(before.lineno<=i<=before.end_lineno for i in change.removed) and all(after.lineno<=i<=after.end_lineno for i in added_lines):
            if any(isinstance(n,ast.Attribute) and n.attr in names-keep and isinstance(n.ctx,ast.Store) for n in ast.walk(other)):
                return True
    return False


def broken_keyword(ch):
    if not ch.path.endswith('.py') or not ch.added or not ch.removed or len(ch.added)+len(ch.removed)>6:
        return False
    left = physical_lines(ch.before)
    if not any(':' in left[i-1] and '=' in left[i-1] for i in ch.removed):
        return False
    old,new=parsed_source(ch.before),parsed_source(ch.after)
    for x,y in zip(old.body,new.body):
        if not (isinstance(x,ast.FunctionDef) and isinstance(y,ast.FunctionDef) and x.name==y.name and not x.decorator_list and not y.args.kwarg):
            continue
        if not all(x.lineno<=i<=x.body[0].lineno for i in ch.removed):
            continue
        removed = {t.arg for t in (*x.args.args,*x.args.kwonlyargs)} - {t.arg for t in (*y.args.args,*y.args.kwonlyargs)}
        if not removed or not same(x.body,y.body):
            continue
        direct=[n for n in ast.walk(new) if isinstance(n,ast.Call) and isinstance(n.func,ast.Name) and n.func.id==y.name]
        if direct and all(any(k.arg in removed for k in n.keywords) for n in direct):
            return True
    return False


def decline(ix, changes, whole, small):
    if len(changes)!=1:
        return False
    ch,=changes
    if not ch.path.startswith('sqlglot/') or not ch.path.endswith('.py'):
        return False
    if small and broken_keyword(ch):
        return True
    if not whole:
        return False
    left,right=physical_lines(ch.before),physical_lines(ch.after)
    if any(right[n-1].startswith('from sqlglot') for n in ch.added):
        return dependency_cycle(ix,ch,parsed_source(ch.before),parsed_source(ch.after))
    if ch.removed and len(ch.removed)+len(ch.added)<12 and all(left[i-1].lstrip().startswith(('"',"'")) for i in ch.removed):
        return removed_slot(parsed_source(ch.before),parsed_source(ch.after),ch)
    return False
