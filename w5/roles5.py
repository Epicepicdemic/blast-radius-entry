"""Check that a variadic formal is used only as the class operand of type tests."""
import ast

def build(rows,sources):
    # keys can address a module-level helper or union every concrete project
    # implementation of a same-named method. A single uncertain use rejects it.
    roles={}
    for _ in range(12):
        before=len(roles)
        for key,fs in rows.items():
            if key in roles:continue
            claims=[]
            for fn,method in fs:
                if fn.decorator_list or not fn.args.vararg:break
                name=fn.args.vararg.arg
                nodes=[n for s in fn.body for n in ast.walk(s)]
                if any(isinstance(n,(ast.Global,ast.Nonlocal)) or isinstance(n,ast.Name) and n.id in ("exec","eval","locals","vars","_getframe","currentframe") for n in nodes):break
                parents={c:n for n in nodes for c in ast.iter_child_nodes(n)}
                okay=True
                for n in nodes:
                    if not isinstance(n,ast.Name) or n.id!=name:continue
                    p=parents.get(n)
                    if isinstance(n.ctx,ast.Load) and isinstance(p,ast.Call) and isinstance(p.func,ast.Name) and p.func.id in ("isinstance","issubclass") and len(p.args)==2 and p.args[1] is n:continue
                    if isinstance(p,ast.Starred):
                        call=parents.get(p)
                        if isinstance(call,ast.Call) and isinstance(call.func,ast.Name):
                            # If several modules define a helper of that name,
                            # all candidates must have the same established slot.
                            hits=[v for k,v in roles.items() if not k.startswith(".") and k.rsplit(".",1)[-1]==call.func.id]
                            candidates=[k for k in rows if not k.startswith(".") and k.rsplit(".",1)[-1]==call.func.id]
                            if hits and len(hits)==len(candidates) and p in call.args and all(call.args.index(p)>=a for a in hits):continue
                    okay=False;break
                if not okay:break
                claims.append(len(fn.args.posonlyargs+fn.args.args)-int(method))
            else:
                if claims and len(set(claims))==1:roles[key]=claims[0]
        if len(roles)==before:break
    return roles
