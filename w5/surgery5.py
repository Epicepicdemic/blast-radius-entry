"""Identify impossible calls and unchanged, independently evaluated constructor arguments."""
import ast
from functools import lru_cache

from frontier import same
from rules5 import facts


from binding_guards5 import unbound


def unreachable(scope,census):
    if not census or not isinstance(scope,ast.FunctionDef):return frozenset()
    cache=getattr(census,"impossible5",None)
    if cache is None:cache=census.impossible5={}
    if scope in cache:return cache[scope]
    dead=set()
    def truth(x):
        if isinstance(x,ast.Constant):return {bool(x.value)}
        if isinstance(x,ast.Name) and unbound(x,scope,census):return set()
        if isinstance(x,ast.UnaryOp) and isinstance(x.op,ast.Not):return {not a for a in truth(x.operand)}
        if isinstance(x,ast.BoolOp):
            expected=isinstance(x.op,ast.And);possible={expected}
            for v in x.values:
                if expected not in possible:break
                possible=(possible-{expected})|truth(v)
            return possible
        if isinstance(x,ast.Compare) and (not truth(x.left) or (x.comparators and not truth(x.comparators[0]))):return set()
        return {True,False}
    def suite(seq):
        for v in seq:
            if isinstance(v,ast.If):
                options=truth(v.test)
                for branch,key in ((v.body,True),(v.orelse,False)):
                    if key not in options:
                        for st in branch:dead.update(ast.walk(st))
                    else:suite(branch)
            elif isinstance(v,(ast.For,ast.While,ast.With,ast.Match,ast.Try,ast.TryStar)):
                for f in ("body","orelse","finalbody"):suite(getattr(v,f,()))
                for h in getattr(v,"handlers",()):suite(h.body)
                for c in getattr(v,"cases",()):suite(c.body)
    suite(scope.body)
    cache[scope]=dead
    return dead


def ctor_shell(obj,scope,census):
    if not census or not isinstance(scope,ast.FunctionDef):return False
    from type_flow5 import fresh
    if fresh(obj,scope,census):return True
    def result(n):
        if not isinstance(n,ast.Call):return False
        kind=census.resolve(n.func,scope)
        return bool(kind and kind[0]=="type" and len(kind)>2 and kind[2] and census.type_ok(kind)
                    and kind[1].replace(":",".") in facts()["ordinary_expressions"])
    if isinstance(obj,ast.Name):
        defs=census.bindings(scope).get(obj.id,())
        return bool(defs and all(k=="assign" and result(n) for k,n in defs))
    return result(obj)


def immutable_result(arg,scope,node,census):
    if not census or not isinstance(scope,ast.FunctionDef) or not isinstance(arg,ast.Name):return False
    if not (isinstance(node.func,ast.Attribute) and isinstance(node.func.value,ast.Attribute)):return False
    owner=census.resolve(node.func.value,scope)
    if not owner or owner[0]!="type" or owner[1].replace(":",".") not in facts()["ordinary_expressions"]:return False
    # A dominating straight-line assignment before the call can replace an
    # earlier non-scalar binding. Inside a branch it does not dominate a sibling.
    parents={c:p for p in ast.walk(scope) for c in ast.iter_child_nodes(p)}
    here=node
    while here in parents and not isinstance(here,ast.stmt):here=parents[here]
    parent=parents.get(here)
    if parent is None:return False
    seq=next((v for _,v in ast.iter_fields(parent) if isinstance(v,list) and here in v),None)
    if not seq:return False
    defined=set()
    def scalar(v):
        if isinstance(v,ast.Constant):return type(v.value) in (str,int,bool,float,type(None))
        if isinstance(v,ast.JoinedStr):return True
        if isinstance(v,ast.Compare):return all(isinstance(op,(ast.Is,ast.IsNot,ast.In,ast.NotIn)) for op in v.ops)
        if isinstance(v,ast.IfExp):return scalar(v.body) and scalar(v.orelse)
        if isinstance(v,ast.Name):return v.id in defined
        # Both the name property and sql method must return strings for every
        # project implementation. Concrete receiver facts are checked at build time.
        if isinstance(v,ast.Attribute) and v.attr=="name":
            return (isinstance(v.value,ast.Name) and v.value.id==arg.id and "name" in facts()["str_members"])
        if isinstance(v,ast.Call) and isinstance(v.func,ast.Attribute) and isinstance(v.func.value,ast.Name):
            return v.func.value.id=="self" and v.func.attr in facts()["str_members"] and v.func.attr=="sql"
        return False
    for st in seq[:seq.index(here)]:
        target=st.targets[0] if isinstance(st,ast.Assign) and len(st.targets)==1 else getattr(st,"target",None)
        if isinstance(target,ast.Name) and isinstance(st,(ast.AnnAssign,ast.Assign)) and scalar(st.value):defined.add(target.id)
        else:
            for q in ast.walk(st):
                if isinstance(q,ast.Name) and not isinstance(q.ctx,ast.Load):defined.discard(q.id)
    return arg.id in defined
