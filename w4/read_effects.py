"""Discharge argument escapes only when the callee uses that argument as a predicate."""
import ast
import builtins
from functools import lru_cache
from pathlib import Path
import marshal

@lru_cache(1)
def data():
    return marshal.loads(Path(__file__).with_name("read-effects.bin").read_bytes())

def localname(n):
    return n.id if isinstance(n,ast.Name) else n.attr if isinstance(n,ast.Attribute) else None

def slot(call, arg, args):
    pos,named,star=args
    for i,value in enumerate(call.args):
        if isinstance(value,ast.Starred):
            if value.value is arg and i>=len(pos) and star:return star
            return None
        if value is arg:return pos[i] if i<len(pos) else star
    for kw in call.keywords:
        if kw.value is arg and kw.arg is not None and kw.arg in pos+named:return kw.arg
    return None

def build(root):
    funcs={}
    targets={}
    sources={}
    for path in (root/"sqlglot").rglob("*.py"):
        module=".".join(path.relative_to(root).with_suffix("").parts).removesuffix(".__init__")
        tree=ast.parse(path.read_bytes())
        refs={}
        for n in tree.body:
            if isinstance(n,ast.ImportFrom) and n.module and not n.level:
                refs.update((a.asname or a.name,n.module+"."+a.name) for a in n.names)
            if isinstance(n,ast.FunctionDef):refs[n.name]=module+"."+n.name
        sources[module]=refs
        def reg(fn,owner=None):
            name=module+"."+(owner+"." if owner else "")+fn.name
            ps=[a.arg for a in fn.args.posonlyargs+fn.args.args]
            targets[name]=(ps[1:] if owner else ps,[a.arg for a in fn.args.kwonlyargs],fn.args.vararg.arg if fn.args.vararg else None)
            funcs[name]=(module,owner,fn)
        for n in tree.body:
            if isinstance(n,ast.FunctionDef):reg(n)
            if isinstance(n,ast.ClassDef):
                for m in n.body:
                    if isinstance(m,ast.FunctionDef):reg(m,n.name)
    # Grow a least fixed point. Calls to unresolved/recursive consumers retain the argument.
    safe={}
    for count in range(5):
        changed=False
        for name,(module,owner,fn) in funcs.items():
            if name in safe and len(safe[name])==len(set(sum((list(v) if isinstance(v,list) else [v] if v else [] for v in targets[name]),[]))):continue
            nodes=[n for st in fn.body for n in ast.walk(st)]
            if fn.decorator_list or any(isinstance(n,(ast.Global,ast.Nonlocal)) or isinstance(n,ast.Name) and n.id in ("locals","globals","eval","exec","vars","_getframe") for n in nodes):continue
            parents={child:n for n in nodes for child in ast.iter_child_nodes(n)}
            pos,named,star=targets[name]
            for param in [*pos,*named,*([star] if star else [])]:
                if param in safe.get(name,set()):continue
                usages=[n for n in nodes if isinstance(n,ast.Name) and n.id==param]
                if not usages:continue
                for n in usages:
                    p=parents.get(n)
                    if not isinstance(n.ctx,ast.Load):break
                    if isinstance(p,ast.Call) and isinstance(p.func,ast.Name) and p.func.id in ("isinstance","issubclass") and len(p.args)==2 and p.args[1] is n:continue
                    if isinstance(p,ast.Compare) and all(isinstance(op,(ast.Is,ast.IsNot)) for op in p.ops):continue
                    if isinstance(p,ast.Starred):p=parents.get(p)
                    if not isinstance(p,ast.Call) or not isinstance(p.func,ast.Name):break
                    tgt=sources[module].get(p.func.id)
                    if tgt not in targets or slot(p,n,targets[tgt]) not in safe.get(tgt,set()):break
                else:
                    safe.setdefault(name,set()).add(param);changed=True
        if not changed:break
    return {k:(targets[k],v) for k,v in safe.items()},sources

def readonly(arg,scope,node,census):
    if census is None or not isinstance(scope,(ast.FunctionDef,ast.AsyncFunctionDef)) or not isinstance(node.func,ast.Name):return False
    kind=census.resolve(arg,scope)
    # The permitted observation of a type object is isinstance/issubclass or
    # identity. Never relax a mutation on an ordinary shared mutable argument.
    if not kind or kind[0]!="type" or not census.type_ok(kind):return False
    roles,sources=data()
    name=node.func.id
    if name in census.bindings(scope) or census.enclosing_binds(scope,name):return False
    target=sources.get(census.module,{}).get(name)
    if target not in roles:return False
    # Exact imported functions only; the single changed module may not replace the implementation.
    if target.rpartition(".")[0]==census.module:return False
    spec,allowed=roles[target]
    return slot(node,arg,spec) in allowed

def missing_call(node,scope,census):
    if not census or not isinstance(scope,(ast.FunctionDef,ast.AsyncFunctionDef)):return False
    if census.module not in census.c.modules:return False
    def missing(n):
        if not isinstance(n,ast.Name) or n.id in vars(builtins):return False
        return (not any(isinstance(x,(ast.Global,ast.Nonlocal)) or isinstance(x,ast.Name) and x.id in ("exec","globals","eval","setattr","__builtins__") for x in ast.walk(scope))
                and n.id not in census.bindings(scope) and not census.enclosing_binds(scope,n.id)
                and not census.module_binds(n.id) and n.id not in {x.id for x in ast.walk(census.tree)
                    if isinstance(x,ast.Name) and isinstance(x.ctx,(ast.Store,ast.Del))})
    def compulsory(n):
        if missing(n):return True
        if isinstance(n,ast.Attribute):return compulsory(n.value)
        if isinstance(n,(ast.GeneratorExp,ast.ListComp,ast.SetComp,ast.DictComp)) and n.generators:
            return compulsory(n.generators[0].iter)
        if isinstance(n,(ast.List,ast.Tuple,ast.Set)):return any(compulsory(x) for x in n.elts)
        if isinstance(n,ast.Call):return compulsory(n.func) or any(compulsory(a) for a in n.args) or any(compulsory(k.value) for k in n.keywords)
        return False
    return any(compulsory(a) for a in [node.func,*node.args,*[k.value for k in node.keywords]])
