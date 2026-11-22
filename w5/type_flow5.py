"""Transfer closed pin types through unmodified assignments and ordinary expression fields."""
import ast
from functools import lru_cache
from rules5 import facts

SCALARS=(str,int,bool,float,bytes,type(None))

def exprkind(kind):
    return bool(kind and kind[0]=='type' and kind[1].replace(':','.') in facts()['ordinary_expressions'])

@lru_cache(128)
def parents(fn):return {c:n for n in ast.walk(fn) for c in ast.iter_child_nodes(n)}

def assigned(name,fn,at):
    """Last necessarily executed definition inside the current straight-line block."""
    par=parents(fn);n=at
    while n in par:
        up=par[n]
        seq=next((v for _,v in ast.iter_fields(up) if isinstance(v,list) and n in v),None)
        if seq and isinstance(n,ast.stmt):
            for st in reversed(seq[:seq.index(n)]):
                ts=st.targets if isinstance(st,ast.Assign) else [st.target] if isinstance(st,ast.AnnAssign) else []
                if len(ts)==1 and isinstance(ts[0],ast.Name) and ts[0].id==name:return st.value
                if any(isinstance(v,ast.Name) and v.id==name and not isinstance(v.ctx,ast.Load) for v in ast.walk(st)):return None
        n=up
    return None

@lru_cache(256)
def assignments(fn):
    out={}
    for n in ast.walk(fn):
        if isinstance(n,(ast.Assign,ast.AnnAssign,ast.NamedExpr,ast.For,ast.comprehension)):
            val=n.iter if isinstance(n,(ast.For,ast.comprehension)) else n.value
            targets=n.targets if isinstance(n,ast.Assign) else [n.target]
            for t in targets:
                for v in ast.walk(t):
                    if isinstance(v,ast.Name) and isinstance(v.ctx,ast.Store):
                        out.setdefault(v.id,[]).append((ast.dump(t),type(n).__name__,val))
        elif isinstance(n,ast.arg):out.setdefault(n.arg,[]).append(('','arg',n.annotation))
        elif isinstance(n,(ast.ExceptHandler,ast.MatchAs,ast.MatchStar)) and n.name:
            out.setdefault(n.name,[]).append(('','opaque',None))
        elif isinstance(n,ast.AugAssign) and isinstance(n.target,ast.Name):out.setdefault(n.target.id,[]).append(('','opaque',None))
    return out

def origin(fn,start):
    table=assignments(fn);todo=[start];seen=set();rows=[]
    while todo:
        key=todo.pop()
        if key in seen:continue
        if len(seen)>=45:return None
        seen.add(key)
        for target,kind,v in table.get(key,()):
            if kind=='opaque':return None
            rows.append((key,target,kind,ast.dump(v) if v else ''))
            if kind!='arg' and v is not None:todo.extend(n.id for n in ast.walk(v) if isinstance(n,ast.Name) and n.id in table)
    return tuple(sorted(rows))

def stable(base,fn,census):
    from effects5 import active
    if not active or not isinstance(base,ast.Name) or not census or census.path!=active[0] or census.quals.get(fn)!=active[1]:return False
    if base.id not in census.bindings(fn):return False
    left=origin(active[2],base.id)
    return left is not None and left==origin(active[3],base.id)

def seen_type(obj,scope,census):
    from effects5 import active
    if not active:return set()
    root=obj
    while isinstance(root,(ast.Attribute,ast.Subscript)):root=root.value
    if not stable(root,scope,census):return set()
    return facts()['shell_types'].get((active[0],active[1],ast.dump(obj)),set())

def constructor(n,scope,census):
    if not isinstance(n,ast.Call):return False
    kind=census.resolve(n.func,scope)
    if exprkind(kind) and kind[2] and census.type_ok(kind):return True
    if not isinstance(n.func,ast.Attribute):return False
    group=census.resolve(n.func.value,scope)
    # The module binding and exact functions are verified on the clean pin.
    if group and group[0]=='module' and (group[1],n.func.attr) in facts()['factories']:
        return not any(isinstance(x,ast.Starred) for x in n.args) and all(kw.arg is not None for kw in n.keywords)
    # A foreign sequence can disagree between len() and iteration. A native
    # sequence passed to the checked reducing constructor has a consistent length.
    return bool(exprkind(group) and (group[1].replace(':','.'),n.func.attr) in facts()['factories']
                and len(n.args)==1 and not n.keywords and isinstance(n.args[0],(ast.List,ast.Tuple)))

def fresh(obj,scope,census,seen=frozenset()):
    if constructor(obj,scope,census):return True
    if isinstance(obj,ast.Name) and obj.id not in seen:
        vs=census.bindings(scope).get(obj.id,())
        return bool(vs and all(k=='assign' and fresh(v,scope,census,seen|{obj.id}) for k,v in vs))
    if isinstance(obj,ast.Attribute) and obj.attr in ('args','meta'):
        return fresh(obj.value,scope,census,seen)
    return False

def receiver_expr(obj,scope,census,seen=frozenset()):
    if constructor(obj,scope,census):return True
    kinds=seen_type(obj,scope,census)
    if kinds and kinds<=facts()['ordinary_expressions']:return True
    if isinstance(obj,ast.IfExp):return receiver_expr(obj.body,scope,census,seen) and receiver_expr(obj.orelse,scope,census,seen)
    if isinstance(obj,ast.Attribute) and obj.attr in ('this','expression','left','right','parent'):
        return receiver_expr(obj.value,scope,census,seen)
    if isinstance(obj,ast.Name) and obj.id not in seen:
        if filtered_value(obj,scope,census,seen):return True
        v=assigned(obj.id,scope,obj)
        if v is not None:return receiver_expr(v,scope,census,seen|{obj.id})
    return False

def scalar(n,scope,census,seen=frozenset()):
    if isinstance(n,ast.Constant):return type(n.value) in SCALARS
    if isinstance(n,ast.Tuple):return all(scalar(v,scope,census,seen) for v in n.elts)
    if isinstance(n,(ast.IfExp,ast.BoolOp)):
        return all(scalar(v,scope,census,seen) for v in ([n.body,n.orelse] if isinstance(n,ast.IfExp) else n.values))
    if isinstance(n,ast.JoinedStr):return True
    if isinstance(n,ast.Compare) and all(isinstance(v,(ast.Is,ast.IsNot,ast.In,ast.NotIn)) for v in n.ops):return True
    if isinstance(n,ast.Attribute):
        k=census.resolve(n.value,scope)
        if n.attr in ('name','alias_or_name') and receiver_expr(n.value,scope,census):return True
    if isinstance(n,ast.Call) and isinstance(n.func,ast.Attribute):
        recv=n.func.value
        # Parser's Token.text slot is initialized by the pinned lexer. The
        # following builtin string operations return a detached immutable string.
        if n.func.attr in ('upper','lower','casefold') and not n.args and not n.keywords and isinstance(recv,ast.Attribute) and recv.attr=='text' and isinstance(recv.value,ast.Attribute) and recv.value.attr in ('_prev','_curr','_next') and isinstance(recv.value.value,ast.Name) and recv.value.value.id=='self':
            return census.module+'.'+census.quals.get(scope,'').split('.')[0] in facts()['parser_types']
    if isinstance(n,ast.Name) and n.id not in seen:
        vals=census.bindings(scope).get(n.id,());s=seen|{n.id}
        if not vals:
            kind=census.resolve(n,scope);return bool(kind and kind[0]=='imm' and (census.module,n.id) in facts()['scalar_globals'])
        def elem(v):
            if isinstance(v,(ast.Tuple,ast.List,ast.Set)):return all(scalar(x,scope,census,s) for x in v.elts)
            k=census.resolve(v,scope)
            return bool(k and k[0]=='elems' and isinstance(v,ast.Name) and (census.module,v.id) in facts()['scalar_iterables'])
        return all(k=='assign' and scalar(v,scope,census,s) or k=='for' and elem(v) for k,v in vals)
    return False

def argument(arg,scope,node,census):
    from effects5 import active
    if not active or not census or not isinstance(scope,ast.FunctionDef):return False
    if scalar(arg,scope,census):return True
    if isinstance(arg,(ast.Set,ast.List)) and all(scalar(v,scope,census) for v in arg.elts):return True
    f=node.func
    if isinstance(f,ast.Attribute) and f.attr in ('set','replace','add_comments') and receiver_expr(f.value,scope,census):
        from effects5 import observed_shell
        if fresh(arg,scope,census) or observed_shell(arg,scope,census):
            # Pinned expression mutators attach their AST argument by updating
            # its own parent slots. An independently owned argument has no shared
            # binding to protect. The receiver's writes are analyzed separately.
            if isinstance(arg,ast.Name) or fresh(arg,scope,census):return True
    if isinstance(f,ast.Attribute):
        recv=f.value
        if f.attr in ('get','getattr') and isinstance(recv,ast.Attribute) and recv.attr=='args' and receiver_expr(recv.value,scope,census):
            # dict.get cannot publish or modify a key. Unknown hash methods
            # still require a read-only scalar or pinned enum key.
            if isinstance(arg,ast.Name):
                for c in ast.walk(scope):
                    if isinstance(c,ast.comprehension) and isinstance(c.target,ast.Name) and c.target.id==arg.id and (census.elems_safe(c.iter,scope,set(),0) or isinstance(c.iter,ast.Name) and __import__('surgery5').unbound(c.iter,scope,census)):return True
        k=census.resolve(arg,scope)
        if exprkind(k) and census.type_ok(k) and f.attr in ('find_all','find'):
            first=facts()['variadic_types'].get('.'+f.attr)
            if first is not None and arg in node.args and node.args.index(arg)>=first and receiver_expr(recv,scope,census):return True
    return False


def checked_expression(name, at, fn, census):
    """A positive isinstance branch or a preceding returning rejection narrows a name."""
    par=parents(fn)
    def test(expr):
        if isinstance(expr,ast.BoolOp) and isinstance(expr.op,ast.And):return any(test(n) for n in expr.values)
        if not (isinstance(expr,ast.Call) and isinstance(expr.func,ast.Name) and expr.func.id=='isinstance' and len(expr.args)==2 and not expr.keywords and isinstance(expr.args[0],ast.Name) and expr.args[0].id==name):return False
        if census.resolve(expr.func,fn) != ['builtin','isinstance']:return False
        t=expr.args[1];choices=t.elts if isinstance(t,ast.Tuple) else [t]
        return bool(choices and all(exprkind(census.resolve(c,fn)) for c in choices))
    def writes(n):
        from shared_writes import bindings
        return name in bindings(n)
    cursor=at
    while cursor in par:
        parent=par[cursor]
        if isinstance(parent,(ast.FunctionDef,ast.AsyncFunctionDef,ast.Lambda)) and parent is not fn:return False
        if isinstance(parent,ast.If) and cursor in parent.body and not writes(parent.test) and test(parent.test):return True
        siblings=next((v for _,v in ast.iter_fields(parent) if isinstance(v,list) and cursor in v),None)
        if siblings and isinstance(cursor,ast.stmt):
            for earlier in reversed(siblings[:siblings.index(cursor)]):
                if isinstance(earlier,ast.If) and earlier.orelse and isinstance(earlier.orelse[-1],(ast.Return,ast.Raise,ast.Continue)) and test(earlier.test) and not writes(earlier.test) and not any(writes(q) for q in earlier.body):return True
                if writes(earlier):return False
        cursor=parent
    return False


def filtered_value(obj,fn,census,seen):
    """Follow an Expr type filter and non-escaping local lists of projected tuples."""
    if not isinstance(obj,ast.Name) or obj.id in seen:return False
    if checked_expression(obj.id,obj,fn,census):return True
    par=parents(fn);cursor=obj;seen=seen|{obj.id}
    while cursor in par:
        parent=par[cursor]
        if isinstance(parent,(ast.FunctionDef,ast.AsyncFunctionDef,ast.Lambda)) and parent is not fn:return False
        if isinstance(parent,ast.For) and cursor in parent.body:
            from shared_writes import bindings
            if any(obj.id in bindings(st) for st in parent.body):return False
            t=parent.target;it=parent.iter
            if isinstance(t,ast.Name) and t.id==obj.id and isinstance(it,ast.Call) and isinstance(it.func,ast.Attribute) and it.func.attr=='find_all' and it.args:
                if facts()['checked_find'] and not it.keywords and all(exprkind(census.resolve(a,fn)) for a in it.args):
                    return receiver_expr(it.func.value,fn,census,seen)
            if isinstance(t,(ast.Tuple,ast.List)) and isinstance(it,ast.Name):
                pos=[j for j,a in enumerate(t.elts) if isinstance(a,ast.Name) and a.id==obj.id]
                if len(pos)==1:
                    definitions=census.bindings(fn).get(it.id,())
                    if len(definitions)!=1 or definitions[0][0]!='assign' or not isinstance(definitions[0][1],ast.List) or definitions[0][1].elts:return False
                    values=[]
                    for ref in ast.walk(fn):
                        if not (isinstance(ref,ast.Name) and ref.id==it.id and isinstance(ref.ctx,ast.Load)):continue
                        owner=par.get(ref)
                        if isinstance(owner,ast.Attribute) and owner.value is ref and owner.attr=='append':
                            call=par.get(owner)
                            if not isinstance(call,ast.Call) or len(call.args)!=1 or call.keywords or not isinstance(call.args[0],(ast.Tuple,ast.List)) or len(call.args[0].elts)!=len(t.elts):return False
                            values.append(call.args[0].elts[pos[0]])
                        elif isinstance(owner,(ast.For,ast.comprehension)) and owner.iter is ref:continue
                        elif isinstance(owner,ast.Call) and isinstance(owner.func,ast.Name) and owner.func.id in ('len','bool') and census.resolve(owner.func,fn)==['builtin',owner.func.id] and len(owner.args)==1 and not owner.keywords:continue
                        else:return False
                    return bool(values and all((isinstance(v,ast.Name) and checked_expression(v.id,v,fn,census))
                                               or receiver_expr(v,fn,census,seen) for v in values))
        cursor=parent
    return False
