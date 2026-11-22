"""Recognize equivalent positional callbacks in a copied dispatch table at the immutable pin."""
import ast
from collections import Counter, defaultdict

def expression_key(args,body):
    """A closed return expression with parameters renamed by position and no executable header."""
    params=args.posonlyargs+args.args
    if args.defaults or args.kwonlyargs or args.vararg or args.kwarg or not params:
        return None
    if any(not isinstance(n,(ast.Call,ast.Name,ast.Attribute,ast.Constant,ast.Load,ast.keyword))
           for n in ast.walk(body)):return None
    local={a.arg:i for i,a in enumerate(params)}
    def form(n):
        if isinstance(n,ast.Name):
            if n.id not in local:raise ValueError("free name")
            return ("arg",local[n.id])
        if isinstance(n,ast.Attribute):
            if n.attr.startswith("__"):raise ValueError("reflective call")
            return ("attr",form(n.value),n.attr)
        if isinstance(n,ast.Constant):return ("constant",type(n.value).__name__,repr(n.value))
        if isinstance(n,ast.Call):
            if any(k.arg is None for k in n.keywords):raise ValueError("dynamic arguments")
            return ("call",form(n.func),tuple(form(a) for a in n.args),tuple((k.arg,form(k.value)) for k in n.keywords))
        raise ValueError("unsupported callback")
    try:return len(params),form(body)
    except ValueError:return None

def source_name(path):
    mod=path.removesuffix(".py").replace("/",".")
    return mod.removesuffix(".__init__")

def table_assignment(value, parents):
    parent=parents.get(value)
    # A copy can pass through an explicit dictionary unpack into a derived table.
    if isinstance(parent,ast.Dict) and any(k is None and v is value for k,v in zip(parent.keys,parent.values)):
        value,parent=parent,parents.get(parent)
    if not isinstance(parent,(ast.Assign,ast.AnnAssign)) or parent.value is not value:
        return False
    targets=parent.targets if isinstance(parent,ast.Assign) else [parent.target]
    return (len(targets)==1 and isinstance(targets[0],ast.Name) and targets[0].id=="TRANSFORMS"
            and isinstance(parents.get(parent),ast.ClassDef))

def copied_table(table,parents):
    if table.attr!="TRANSFORMS":return False
    if table_assignment(table,parents):return True
    container=parents.get(table)
    if isinstance(container,ast.Dict) and any(k is None and v is table for k,v in zip(container.keys,container.values)):
        table=container
    items=parents.get(table)
    call=parents.get(items)
    loop=parents.get(call)
    comp=parents.get(loop)
    if not (isinstance(items,ast.Attribute) and items.attr=="items" and isinstance(call,ast.Call)
            and call.func is items and not call.args and not call.keywords and isinstance(loop,ast.comprehension)
            and loop.iter is call and not loop.is_async and isinstance(comp,ast.DictComp)
            and comp.generators==[loop] and table_assignment(comp,parents)):
        return False
    target=loop.target
    if not (isinstance(target,ast.Tuple) and len(target.elts)==2 and all(isinstance(x,ast.Name) for x in target.elts)):
        return False
    key,value=(x.id for x in target.elts)
    if not (key!=value and isinstance(comp.key,ast.Name) and comp.key.id==key
            and isinstance(comp.value,ast.Name) and comp.value.id==value):
        return False
    def literal_key(n):
        if isinstance(n,ast.Constant):return True
        if isinstance(n,ast.Attribute):
            while isinstance(n,ast.Attribute):
                if n.attr.startswith("__"):return False
                n=n.value
            return isinstance(n,ast.Name) and n.id not in (key,value)
        if isinstance(n,(ast.Tuple,ast.List,ast.Set)):return all(literal_key(v) for v in n.elts)
        return False
    def passive_filter(cond):
        if not (isinstance(cond,ast.Compare) and len(cond.ops)==1 and isinstance(cond.left,ast.Name)):
            return False
        op,other=cond.ops[0],cond.comparators[0]
        if cond.left.id==value:
            # Both witnessed callbacks are function objects, so this filter preserves both.
            return isinstance(op,(ast.Is,ast.IsNot)) and isinstance(other,ast.Constant) and other.value is None
        return (cond.left.id==key and isinstance(op,(ast.Eq,ast.NotEq,ast.In,ast.NotIn,ast.Is,ast.IsNot))
                and literal_key(other))
    return all(passive_filter(cond) for cond in loop.ifs)

def binding_counts(body):
    counts=Counter()
    def walk(n):
        if isinstance(n,(ast.FunctionDef,ast.AsyncFunctionDef,ast.ClassDef)):
            counts[n.name]+=1
            return
        if isinstance(n,(ast.Import,ast.ImportFrom)):
            counts.update(a.asname or a.name.split(".")[0] for a in n.names)
            return
        if isinstance(n,ast.Name) and isinstance(n.ctx,(ast.Store,ast.Del)):
            counts[n.id]+=1
        if not isinstance(n,(ast.Lambda,ast.DictComp,ast.SetComp,ast.ListComp,ast.GeneratorExp)):
            for c in ast.iter_child_nodes(n):walk(c)
    for n in body:walk(n)
    return counts

def freeze(pin,paths,exposure,warm,cold,ids,intern):
    defs={};scopes={};risk=defaultdict(int);all_bits=(1<<len(ids))-1
    warm_masks=[int(x,16) for x in warm["masks"]]
    cold_masks=[int(x,16) for x in cold["masks"]]
    # Capture all general raw lookups. Literal dictionary copies and discarded deletion
    # results propagate the same callable or never observe it. Late dispatch has an additional audit below.
    def line_users(path,n):
        a=warm.get("lines",{}).get(path,{}).get(str(n))
        b=cold.get("lines",{}).get(path,{}).get(str(n))
        return (warm_masks[a] if a is not None else 0)|(cold_masks[b] if b is not None else 0)
    for path in sorted(set(paths)|{t.split("::")[0] for t in ids}):
        tree=ast.parse((pin/path).read_bytes())
        mod=source_name(path);imports={}
        for n in tree.body:
            if isinstance(n,ast.ImportFrom) and n.module and not n.level:
                imports.update((a.asname or a.name,n.module+"."+a.name) for a in n.names if a.name!="*")
            elif isinstance(n,ast.FunctionDef) and not n.decorator_list:
                body=n.body[1:] if ast.get_docstring(n) is not None else n.body
                if len(body)!=1 or not isinstance(body[0],ast.Return):continue
                key=expression_key(n.args,body[0].value)
                if key is not None:
                    count=exposure["rows"].get(path,{}).get(n.name+":"+str(n.lineno),"0")
                    defs[mod+"."+n.name]=(key,intern(int(count,16)))
                    imports[n.name]=mod+"."+n.name
        counts=binding_counts(tree.body)
        shadowed=set()
        for cls in (n for n in ast.walk(tree) if isinstance(n,ast.ClassDef)):
            shadowed.update(binding_counts(cls.body))
        scopes[path]={k:v for k,v in imports.items() if counts[k]==1 and k not in shadowed and not counts["*"]}
        for name in imports:
            if counts[name]!=1:defs.pop(mod+"."+name,None)
        parents={c:n for n in ast.walk(tree) for c in ast.iter_child_nodes(n)}
        for n,p in parents.items():
            if not isinstance(n,ast.Attribute) or n.attr not in ("TRANSFORMS","_dispatch") or not isinstance(n.ctx,ast.Load):continue
            if copied_table(n,parents):continue
            if isinstance(p,ast.Call) and isinstance(p.func,ast.Name) and p.func.id=="dict" and p.args==[n] and not p.keywords:
                # There is a single cache builder for the generator's derived dispatch table.
                if path=="sqlglot/generator.py" and any(isinstance(f,ast.FunctionDef) and f.name=="_build_dispatch"
                        and f.lineno<=n.lineno<=f.end_lineno for f in tree.body):continue
            if isinstance(p,ast.Attribute) and p.attr=="pop" and isinstance(parents.get(parents.get(p)),ast.Expr):continue
            if (n.attr=="_dispatch" and isinstance(p,ast.Attribute) and p.attr=="get" and path=="sqlglot/generator.py"):
                # Verify the local consumers of the resulting handler are calls or a truth test.
                get_call=parents.get(p);stmt=parents.get(get_call)
                if isinstance(stmt,ast.Assign) and len(stmt.targets)==1 and isinstance(stmt.targets[0],ast.Name):
                    local=stmt.targets[0].id
                    enclosing=next((fn for fn in ast.walk(tree) if isinstance(fn,ast.FunctionDef) and fn.lineno<=n.lineno<=fn.end_lineno),None)
                    if enclosing is not None:
                        uses=[(v,parents[v]) for v in ast.walk(enclosing) if isinstance(v,ast.Name) and v.id==local and isinstance(v.ctx,ast.Load)]
                        if uses and all((isinstance(owner,ast.Call) and owner.func is v and not owner.keywords) or
                                        (isinstance(owner,ast.If) and owner.test is v) for v,owner in uses):continue
            mask=line_users(path,n.lineno)
            if path.startswith("tests/") and not mask:
                mask=sum(1<<i for i,t in enumerate(ids) if t.split("::")[0]==path)
            risk["generator"]|=mask
    return dict(defs=defs,scopes={p:{k:v for k,v in names.items() if v in defs} for p,names in scopes.items() if p.startswith("sqlglot/generators/")},
                observers=intern(risk["generator"]))

def witness(index,section,path,name,a,b,line_offset=0):
    if not path.startswith("sqlglot/generators/") or name.rsplit(".",1)[-1]!="TRANSFORMS":return None
    if not isinstance(a,ast.Dict) or not isinstance(b,ast.Dict):return None
    keys=lambda n:tuple(ast.dump(k) if k else None for k in n.keys)
    if keys(a)!=keys(b):return None
    registry=index.section("@callbacks")
    if not registry:return None
    mask=index.bits(registry["observers"])|index.reflect(path)|index.hit(section,"opens")|index.registry
    def describe(v):
        if isinstance(v,ast.Name):
            qualified=registry["scopes"].get(path,{}).get(v.id)
            pair=registry["defs"].get(qualified)
            if pair:return pair[0],index.bits(pair[1])
        if isinstance(v,ast.Lambda):
            form=expression_key(v.args,v.body)
            if form is not None:
                raw=section.get("lambda_calls",{}).get(v.lineno+line_offset)
                return form,index.bits(raw) if raw is not None else 0
        return None
    changed=False
    for old,new in zip(a.values,b.values):
        if ast.dump(old)==ast.dump(new):continue
        before,after=describe(old),describe(new)
        if before is None or after is None or before[0]!=after[0]:return None
        # Global pin callers of the replaced callback cover raw alternate call conventions
        # and consumers which can distinguish stack frames while that callback executes.
        mask|=before[1]
        changed=True
    return mask if changed else None
