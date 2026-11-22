"""Forward propagation from the first differing statement, with explicit loop backedges."""
import ast
from frontier import frontier

LOOPS=(ast.For,ast.AsyncFor,ast.While)
OPAQUE=(ast.Try,ast.TryStar,ast.With,ast.AsyncWith,ast.Match)
def suffix(old,new):
    focus=set(frontier(old,new))
    if not focus:return None
    edges={};parts={};owners={}
    def owner(n,root):
        for sub in ast.walk(n):
            if isinstance(sub,ast.stmt):owners[sub.lineno,sub.end_lineno]=root
    def suite(stmts,after,brk,cont):
        target=after
        for n in reversed(stmts):
            owners[n.lineno,n.end_lineno]=n
            parts[n]=(n,)
            if isinstance(n,ast.If):
                parts[n]=(n.test,)
                edges[n]=[suite(n.body,target,brk,cont),suite(n.orelse,target,brk,cont)]
            elif isinstance(n,LOOPS):
                parts[n]=(n.test,) if isinstance(n,ast.While) else (n.target,n.iter)
                edges[n]=[suite(n.body,n,target,n),suite(n.orelse,target,brk,cont)]
            elif isinstance(n,ast.Break):edges[n]=[brk]
            elif isinstance(n,ast.Continue):edges[n]=[cont]
            elif isinstance(n,(ast.Return,ast.Raise)):edges[n]=[]
            elif isinstance(n,OPAQUE):
                # A changed expression in a try/with may reach a handler, a
                # finally, or a containing loop edge. Keep the entire construct.
                owner(n,n);edges[n]=[target,brk,cont]
            else:edges[n]=[target]
            target=n
        return target
    entry=suite(old.body,None,None,None)
    todo=[entry if pair==(old.lineno,old.end_lineno) else owners.get(pair) for pair in focus]
    if any(n is None for n in todo):return None
    visited=set();nodes=[]
    while todo:
        n=todo.pop()
        if n is None or n in visited:continue
        visited.add(n);nodes.extend(parts[n]);todo.extend(edges[n])
    return ast.Module(body=nodes,type_ignores=[])
