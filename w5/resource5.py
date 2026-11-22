"""Bound unrelated resource-test obligations for non-publishing loop refactors."""
import ast
from collections import Counter
from functools import lru_cache


def signatures(fn):
    calls = Counter()
    stores = Counter()
    loops = Counter()
    for n in ast.walk(fn):
        if isinstance(n, ast.Call):
            calls[ast.dump(n.func)] += 1
        if isinstance(n, (ast.Attribute, ast.Subscript)) and isinstance(n.ctx, (ast.Store, ast.Del)):
            stores[ast.dump(n)] += 1
        if isinstance(n, (ast.Raise, ast.YieldFrom, ast.Await, ast.While, ast.FunctionDef, ast.ClassDef, ast.Import, ast.ImportFrom, ast.Global, ast.Nonlocal)) and n is not fn:
            loops[ast.dump(n)] += 1
    return calls, stores, loops


def obligation(ix,ch,info,root_readers):
    from bounds import timing_obligation
    _,called,_,old,new,_,_,_=info
    ordinary=timing_obligation(ix,old,new)
    if not ordinary:
        return 0
    oc,os,ol=signatures(old);nc,ns,nl=signatures(new)
    if ns-os or nl-ol or nc-oc:
        return ordinary
    # Only removing a traversal, or inlining its previously evaluated iterator
    # at the same lexical depth, can withdraw the unrelated stress obligation.
    # Moving a computation into an inner loop or dropping a guard can increase
    # work even if the multiset of callee names is unchanged.
    def control(fn):
        frequencies=Counter()
        def visit(n,depth,guards):
            if isinstance(n,(ast.For,ast.AsyncFor,ast.comprehension)):
                if hasattr(n,'iter'):visit(n.iter,depth,guards)
                for child in ast.iter_child_nodes(n):
                    if child is not n.iter:visit(child,depth+1,guards)
                return
            if isinstance(n,(ast.If,ast.IfExp)):
                visit(n.test,depth,guards)
                for branch,sign in ((n.body,True),(n.orelse,False)):
                    for child in branch if isinstance(branch,list) else [branch]:
                        visit(child,depth,guards+((ast.dump(n.test),sign),))
                return
            if isinstance(n,ast.Call):
                frequencies[ast.dump(n.func),depth,guards]+=1
            for child in ast.iter_child_nodes(n):visit(child,depth,guards)
        visit(fn,0,())
        return frequencies
    if control(new)-control(old):
        return ordinary
    # The original effect proof separately maps any named shared writes to all
    # their readers. A resource check that uses the routine remains mandatory.
    # Keep the broad allocation guard on the core parser, lexer and expression
    # path, which supplies the million-node stress workloads themselves.
    from heavy_reach import footprints
    profile=footprints().get('max')
    functions=ix.section(ch.path).get('functions',{})
    if not profile or set(profile['functions'].get(ch.path,())) & functions.keys():
        return ordinary
    return (called|root_readers)&ordinary
