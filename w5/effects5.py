"""Positive ownership facts for typed predicates and fresh container shells."""
import ast
from functools import lru_cache
from read_effects import slot
from rules5 import facts


def qualified(expr):
    if isinstance(expr,ast.Name):return expr.id
    if isinstance(expr,ast.Attribute):
        owner=qualified(expr.value)
        return owner+"."+expr.attr if owner else ""
    return ""


def predicate(arg,scope,node,census):
    if not census or not isinstance(scope,(ast.FunctionDef,ast.AsyncFunctionDef)):
        return False
    from type_flow5 import argument
    if argument(arg,scope,node,census):return True
    f=node.func
    if not isinstance(f,ast.Attribute):return False
    kind=census.resolve(f,scope)
    if kind and kind[0]=="foreign" and kind[1]=="typing.cast" and len(node.args)==2 and not node.keywords:
        # cast returns its second operand by identity. Later mutation of the
        # result remains a separate write at the consuming expression.
        return True
    # A closed type-observer contract on every same-named implementation.
    # Resolve concrete receiver values from the unchanged expression-tree API.
    k=census.resolve(arg,scope)
    if k and k[0]=="type" and census.type_ok(k) and k[1].replace(":",".") in facts()["ordinary_expressions"]:
        first=facts()["variadic_types"].get("."+f.attr)
        if first is not None and arg in node.args and node.args.index(arg)>=first and not any(isinstance(v,ast.Starred) for v in node.args):
            if expression_receiver(f.value,scope,census):return True
    if isinstance(f.value,ast.Name) and f.value.id=="self" and active:
        mode=None
        for i,z in enumerate(node.args):
            if isinstance(z,ast.Starred):break
            if z is arg:mode=("p",i);break
        for kw in node.keywords:
            if kw.value is arg and kw.arg:mode=("k",kw.arg)
        contract=facts()["contracts"].get(("."+f.attr,mode))
        if contract and active[1].rsplit(".",1)[-1] not in contract[1]:
            uses=contract[0]
            if uses<={"truth","identity","compare"} and isinstance(arg,ast.Attribute) and isinstance(arg.value,ast.Name):
                if arg.value.id=="self" and arg.attr in facts()["transparent_fields"]:return True
                owner=census.resolve(arg.value,scope)
                if owner and owner[0]=="type" and (owner[1],arg.attr) in facts()["enums"]:return True
    if not isinstance(f.value,ast.Name) or f.value.id!="self":return False
    params=scope.args.posonlyargs+scope.args.args
    owner=census.quals.get(scope,"").split(".")
    if len(owner)!=2 or not params or params[0].arg!="self" or scope.decorator_list:return False
    data=facts()
    if census.module+"."+owner[0] not in data["members"]:return False
    method="."+f.attr
    spec,modes=data["roles"].get(method,(([],[],None),{}))
    role=modes.get(slot(node,arg,spec))
    if role is None:return False
    role=set(role)
    if not role:return True
    if role<={"invoke"}:
        return (isinstance(arg,ast.Attribute) and isinstance(arg.value,ast.Name) and arg.value.id=="self"
                and "."+arg.attr in data["method_names"])
    kind=census.resolve(arg,scope)
    if role<={"identity","type"} and kind and kind[0]=="type" and census.type_ok(kind):return True
    if not role<={"identity","truth","compare"}:return False
    def immutable(n):
        if isinstance(n,ast.Constant):return type(n.value) in (str,int,bool,type(None))
        if isinstance(n,(ast.Set,ast.Tuple,ast.List)):return all(immutable(z) for z in n.elts)
        if isinstance(n,ast.Attribute):
            owner=census.resolve(n.value,scope)
            return bool(owner and owner[0]=="type" and (owner[1],n.attr) in data["enums"])
        return False
    return immutable(arg)


def factory_kind(x):
    if isinstance(x,ast.List):return "list"
    if isinstance(x,ast.Set):return "set"
    if isinstance(x,ast.Dict):return "dict"
    return None


def nested_shell(expr,fn,tree):
    """Only admit dictionaries created locally with a builtin empty-value factory."""
    if not isinstance(expr,ast.Subscript) or not isinstance(expr.value,ast.Name):return None
    key=expr.value.id
    assignments=[]
    for n in ast.walk(fn):
        if isinstance(n,(ast.Global,ast.Nonlocal)) and key in n.names:return None
        if isinstance(n,ast.arg) and n.arg==key:return None
        if isinstance(n,(ast.AnnAssign,ast.Assign)):
            targets=n.targets if isinstance(n,ast.Assign) else [n.target]
            if any(isinstance(t,ast.Name) and t.id==key for t in targets):
                if len(targets)!=1:return None
                assignments.append((targets[0],n.value))
    if len(assignments)!=1:return None
    target,call=assignments[0]
    if not (isinstance(call,ast.Call) and not call.keywords and len(call.args)==1 and
            isinstance(call.args[0],ast.Name) and call.args[0].id in ("list","dict","set") and
            isinstance(call.func,ast.Name)):return None
    factory=call.args[0].id
    importer=call.func.id
    imports=[a for n in tree.body if isinstance(n,ast.ImportFrom) and n.level==0 and n.module=="collections"
             for a in n.names if a.name=="defaultdict" and (a.asname or a.name)==importer]
    if len(imports)!=1:return None
    for n in ast.walk(tree):
        if ((isinstance(n,ast.Name) and n.id in (factory,importer) and not isinstance(n.ctx,ast.Load)) or
            isinstance(n,ast.arg) and n.arg in (factory,importer) or
            isinstance(n,(ast.FunctionDef,ast.ClassDef)) and n.name in (factory,importer) or
            isinstance(n,ast.alias) and n is not imports[0] and (n.asname or n.name.split(".")[0]) in (factory,importer) or
            isinstance(n,ast.ImportFrom) and any(a.name=="*" for a in n.names)):return None
    parents={kid:n for n in ast.walk(fn) for kid in ast.iter_child_nodes(n)}
    for n in ast.walk(fn):
        if not isinstance(n,ast.Name) or n.id!=key or n is target:continue
        p=parents.get(n)
        if not isinstance(n.ctx,ast.Load):return None
        if isinstance(p,ast.Subscript) and p.value is n and isinstance(p.ctx,ast.Load):continue
        if isinstance(p,ast.Attribute) and p.value is n and p.attr in ("items","values","keys","get"):continue
        if isinstance(p,(ast.For,ast.comprehension)) and p.iter is n:continue
        return None
    return factory


def owned_store(obj,scope,cls,census,tree):
    if not census or not isinstance(scope,ast.FunctionDef):return False
    if isinstance(obj,ast.Subscript) and nested_shell(obj,scope,tree):return True
    if isinstance(obj,ast.Name):
        # The existing per-parameter heap census includes post-test escapes.
        return census.param_safe(obj.id,scope)
    return False

active=None
def configure(changes):
    global active
    active=None
    if len(changes)!=1:return
    ch=changes[0]
    if not ch.path.startswith("sqlglot/") or not ch.path.endswith(".py"):return
    from patching import parsed_source
    from cone import body_changes
    from selector import equal_trees
    edits=body_changes(ch,equal_trees)
    if not edits or len(edits)!=1:return
    name,a,b=edits[0]
    from bounds import obvious_hazard
    if obvious_hazard(a,b):return
    # These objects can publish arbitrary shared state independently of a local
    # container. Keep the original analyzer for altered reflective/operator use.
    banned={"__dict__","__class__","__globals__","__setitem__","setitem","delitem","setattr","delattr",
            "globals","locals","vars","eval","exec","cache_clear","setdefault","__subclasses__"}
    def seen(fn):
        return [ast.dump(n) for n in ast.walk(fn) if isinstance(n,(ast.Global,ast.Nonlocal,ast.Import,ast.ImportFrom)) or
                isinstance(n,ast.Name) and n.id in banned or isinstance(n,ast.Attribute) and n.attr in banned]
    if seen(a)!=seen(b):return
    active=(ch.path,name,a,b)


def observed_shell(obj,scope,census):
    if not active or census is None or not isinstance(scope,ast.FunctionDef):return False
    path,name,old,new=active
    if census.path!=path or census.quals.get(scope)!=name:return False
    row=facts()["shells"].get((path,name,ast.dump(obj)))
    if not row:return False
    if not (row<={"builtins.list","builtins.set","builtins.dict","collections.defaultdict"} or
            all(t in facts()["ordinary_expressions"] for t in row)):return False
    from surgery5 import ctor_shell
    if ctor_shell(obj,scope,census):return True
    base=obj
    while isinstance(base,(ast.Attribute,ast.Subscript)):base=base.value
    if not isinstance(base,ast.Name):return False
    bindings=census.bindings(scope)
    if base.id not in bindings:return False
    # Every reaching assignment and its transitive local inputs must agree
    # syntactically. Do not transfer an ownership observation to a changed source.
    from census import _scope_bindings
    def origin(fn,who):
        table=_scope_bindings(fn);todo=[who];seen=set();result=[]
        while todo:
            k=todo.pop()
            if k in seen:continue
            seen.add(k)
            if len(seen)>32:return None
            vals=table.get(k,())
            for typ,v in vals:
                if typ not in ("assign","param","for") or v is None:return None
                result.append((k,typ,ast.dump(v)))
                if typ=="param":continue
                todo.extend(n.id for n in ast.walk(v) if isinstance(n,ast.Name) and n.id in table)
        return sorted(result)
    from frontier import same
    if not (scope is old or same(scope,old)):
        result=origin(old,base.id)
        if result is None or result!=origin(new,base.id):return False
        # Storing the receiver or its child in shared state can invalidate an
        # observation without rebinding the local variable itself.
        def escapes(fn):
            uses=[]
            for n in ast.walk(fn):
                if isinstance(n,ast.Call):parts=[*n.args,*(v.value for v in n.keywords)]
                elif isinstance(n,(ast.Assign,ast.AnnAssign,ast.NamedExpr,ast.AugAssign)):
                    parts=[n.value]
                    targets=n.targets if isinstance(n,ast.Assign) else [n.target]
                    parts.extend(t for t in targets if isinstance(t,(ast.Attribute,ast.Subscript)))
                else:continue
                if any(isinstance(r,ast.Name) and r.id==base.id for v in parts if v for r in ast.walk(v)):
                    uses.append(ast.dump(n))
            return uses
        if escapes(old)!=escapes(new):return False
    # A direct class/module receiver or class attribute must never acquire an
    # instance ownership exemption. Inherited dict copies are persistent too.
    if isinstance(obj,ast.Attribute):
        if obj.attr.isupper() or obj.attr.startswith("__"):return False
        if isinstance(obj.value,ast.Name) and obj.value.id=="self":
            clsname=scope.name
            if name.count(".")!=1:return False
            owner=census.module+"."+name.split(".")[0]
            if not (owner,obj.attr) in facts()["private_fields"]:return False
    if not isinstance(obj,(ast.Name,ast.Attribute,ast.Subscript)):return False
    return True

def expression_receiver(x,scope,census,seen=frozenset()):
    if isinstance(x,ast.IfExp):return expression_receiver(x.body,scope,census,seen) and expression_receiver(x.orelse,scope,census,seen)
    if isinstance(x,ast.Attribute) and x.attr in ("this","expression","left","right","parent"):
        return expression_receiver(x.value,scope,census,seen)
    if isinstance(x,ast.Call):
        k=census.resolve(x.func,scope)
        if k and k[0]=="type" and k[1].replace(":",".") in facts()["ordinary_expressions"]:return True
        return isinstance(x.func,ast.Attribute) and x.func.attr in ("copy","unnest","unalias") and expression_receiver(x.func.value,scope,census,seen)
    if isinstance(x,ast.Name) and x.id not in seen:
        defs=census.bindings(scope).get(x.id,())
        if not defs:return False
        def origin(k,v):
            if k=="param" and v.annotation:
                refs=[census.resolve(n,scope) for n in ast.walk(v.annotation) if isinstance(n,(ast.Name,ast.Attribute))]
                return bool(any(a and a[0]=="type" and a[1].replace(":",".") in facts()["ordinary_expressions"] for a in refs))
            if k=="for" and isinstance(v,ast.Call) and isinstance(v.func,ast.Attribute) and v.func.attr in ("find_all","walk","iter_expressions"):
                return expression_receiver(v.func.value,scope,census,seen|{x.id})
            if k=="assign":return expression_receiver(v,scope,census,seen|{x.id})
            return False
        if all(origin(k,v) for k,v in defs):return True
        from type_flow5 import checked_expression
        return checked_expression(x.id,x,scope,census)
    return False
