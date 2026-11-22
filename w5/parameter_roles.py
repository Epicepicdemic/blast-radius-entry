"""Solve interprocedural read-only argument contracts over the pin's closed Python sources."""
import ast
import collections

def analyze(fn_rows,sources):
    # A role describes only how the formal itself is consumed. A separate
    # check restricts actual arguments to transparent builtin/enum operands.
    defs={}
    ids=collections.defaultdict(list)
    for mod,imports in sources.items():
        from pathlib import Path
        p=Path("/sqlglot").joinpath(*mod.split(".")).with_suffix(".py")
        if not p.is_file():p=Path("/sqlglot").joinpath(*mod.split("."),"__init__.py")
        if not p.is_file():continue
        tree=ast.parse(p.read_bytes())
        for n in tree.body:
            fs=[(None,n)] if isinstance(n,ast.FunctionDef) else [(n.name,m) for m in n.body if isinstance(m,ast.FunctionDef)] if isinstance(n,ast.ClassDef) else []
            for cls,fn in fs:
                key=(mod,cls,fn.name,fn.lineno)
                defs[key]=fn
                ids["."+fn.name if cls else mod+"."+fn.name].append(key)
    forms={};rules={}
    for key,fn in defs.items():
        mod,cls,_,_=key;a=fn.args
        pos=[v.arg for v in a.posonlyargs+a.args][int(bool(cls)):]
        kw=pos+[v.arg for v in a.kwonlyargs]
        star=a.vararg.arg if a.vararg else None
        forms[key]=(pos,kw,star)
        if fn.decorator_list and not all(isinstance(n,ast.Name) and n.id=="staticmethod" for n in fn.decorator_list):continue
        nodes=[v for s in fn.body for v in ast.walk(s)];parents={c:p for p in nodes for c in ast.iter_child_nodes(p)}
        if any(isinstance(n,(ast.Global,ast.Nonlocal)) or isinstance(n,ast.Name) and n.id in ("locals","vars","eval","exec","_getframe","currentframe") for n in nodes):continue
        for param in set(kw+([star] if star else [])):
            alias={param};changed=True
            while changed:
                changed=False
                for n in nodes:
                    if isinstance(n,ast.Assign) and len(n.targets)==1 and isinstance(n.targets[0],ast.Name) and isinstance(n.value,ast.Name) and n.value.id in alias and n.targets[0].id not in alias:
                        alias.add(n.targets[0].id);changed=True
            deps=set();uses=set();safe=True
            for n in nodes:
                if not isinstance(n,ast.Name) or n.id not in alias:continue
                p=parents.get(n);v=n
                if not isinstance(n.ctx,ast.Load):
                    if isinstance(p,ast.Assign) and n.id!=param and isinstance(p.value,ast.Name) and p.value.id in alias:continue
                    safe=False;break
                if isinstance(p,ast.Assign) and p.value is n and len(p.targets)==1 and isinstance(p.targets[0],ast.Name):continue
                # Short-circuit and conditional values are forwarded unchanged.
                while isinstance(p,(ast.BoolOp,ast.IfExp)) and not (isinstance(p,ast.IfExp) and p.test is v):
                    uses.add("truth");v,p=p,parents.get(p)
                if isinstance(p,(ast.Compare,ast.If,ast.While,ast.UnaryOp)):
                    if isinstance(p,ast.Compare) and all(isinstance(z,(ast.Is,ast.IsNot)) for z in p.ops):uses.add("identity")
                    elif not isinstance(p,ast.UnaryOp) or isinstance(p.op,ast.Not):uses.add("compare")
                    else:safe=False;break
                    continue
                if isinstance(p,ast.IfExp) and p.test is v:uses.add("truth");continue
                if isinstance(p,ast.Call) and p.func is v:uses.add("invoke");continue
                if isinstance(p,ast.Starred):v,p=p,parents.get(p)
                keyword=None
                if isinstance(p,ast.keyword):keyword=p.arg;v,p=p,parents.get(p)
                if not isinstance(p,ast.Call):safe=False;break
                f=p.func
                if isinstance(f,ast.Name) and f.id in ("isinstance","issubclass") and len(p.args)==2 and p.args[1] is v:uses.add("type");continue
                if isinstance(f,ast.Name) and f.id in ("len","bool") and len(p.args)==1 and p.args[0] is v:uses.add("truth");continue
                if isinstance(f,ast.Attribute) and isinstance(f.value,ast.Name) and f.value.id=="self":
                    keyname="."+f.attr
                elif isinstance(f,ast.Name):keyname=sources.get(mod,{}).get(f.id,mod+"."+f.id)
                else:safe=False;break
                if keyword is not None:mode=("k",keyword)
                elif v in p.args and not any(isinstance(x,ast.Starred) for x in p.args[:p.args.index(v)]):
                    mode=("s" if isinstance(v,ast.Starred) else "p",p.args.index(v))
                else:safe=False;break
                deps.add((keyname,mode))
            if safe:rules[key,param]=(uses,deps)
    slots={}
    for name,keys in ids.items():
        maxpos=max(len(forms[k][0]) for k in keys)
        modes=[("p",i) for i in range(maxpos+1)]+[("s",i) for i in range(maxpos+1)]
        modes+=[("k",q) for q in set().union(*(forms[k][1] for k in keys))]
        for mode,val in modes:
            req=[]
            for k in keys:
                pos,kw,star=forms[k]
                if mode=="k":param=val if val in kw else None
                elif mode=="p":param=pos[val] if val<len(pos) else star
                else:param=star if val>=len(pos) else None
                if param is None or (k,param) not in rules:break
                req.append((k,param))
            else:slots[name,(mode,val)]=req
    resolved={}
    for _ in range(18):
        added=False
        for target,req in slots.items():
            if target in resolved:continue
            rows=[rules[v] for v in req]
            if not all(dep in resolved for _,deps in rows for dep in deps):continue
            kinds=set().union(*(u for u,_ in rows));dependency={key[2] for key,_ in req}
            for _,ds in rows:
                for dep in ds:
                    kinds.update(resolved[dep][0]);dependency.update(resolved[dep][1])
            resolved[target]=(kinds,dependency);added=True
        if not added:break
    return resolved
