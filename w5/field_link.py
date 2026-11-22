"""Link class-MRO readers, dynamic namespace observers and inert initializer operands."""
import ast, collections, enum, gzip, importlib, inspect, json, types
from pathlib import Path

def build(ix,root,index,dyn,unseen,expand,sources,external,classes):
    record=json.load(gzip.open(Path("/w5/profile/field_uses.json.gz")))
    assert record["ids"]==ix.ids and set(record["passed"])==set(ix.ids)
    reads=collections.defaultdict(dict)
    for (owner,field,mode,key),ctx in record["rows"]:
        r=reads[owner,field];r[mode,key]=r.get((mode,key),0)|expand(ctx)
    scoped=set()
    forwarded={}
    from class_copies import forward
    for (owner,field,mode,key),ctx in record['rows']:
        if ctx[1] or int(ctx[0],16)==ix.all:scoped.add((owner,field,mode,key))
        if field.isupper() and mode=='whole' and ctx[1]:
            cold=[p for p in ctx[1] if not forward(root,p,owner,field)]
            forwarded[owner,field,mode,key]=expand([ctx[0],cold])
    fields=set(record["fields"])
    bare=set();passives={};inherited={};ordinary=set();expressions=set();members=set()
    from sqlglot import exp
    for mod in sorted(index.census.modules):
        file=root.joinpath(*mod.split(".")).with_suffix(".py")
        if not file.exists():file=root.joinpath(*mod.split("."),"__init__.py")
        if not file.exists() or not mod.startswith("sqlglot"):continue
        try:module=importlib.import_module(mod)
        except (ImportError,RuntimeError):continue
        tree=ast.parse(file.read_bytes());ns=vars(module)
        for n in ast.walk(tree):
            if isinstance(n,ast.Name) and isinstance(n.ctx,ast.Load) and n.id in fields:bare.add((mod,n.id))
        safe=set()
        def is_safe(val):
            return isinstance(val,(enum.Enum,type)) or type(val) in (str,int,bool,float,type(None),bytes)
        for st in tree.body:
            if not isinstance(st,ast.ClassDef):continue
            cls=ns.get(st.name)
            if not isinstance(cls,type) or cls.__module__!=mod:continue
            q=mod+"."+st.name
            if cls.__module__+"."+cls.__qualname__!=q:continue
            ordinary.add(q)
            if issubclass(cls,exp.Expr):
                expressions.add(q)
                for base in cls.__mro__[1:]:
                    if "arg_types" in vars(base):
                        d=vars(base)["arg_types"]
                        if type(d) is dict:inherited[q]=dict(d)
                        break
            for stmt in st.body:
                if not isinstance(stmt,(ast.Assign,ast.AnnAssign)):continue
                for n in ast.walk(stmt.value) if stmt.value is not None else ():
                    if isinstance(n,ast.Name) and n.id in ns and is_safe(ns[n.id]):safe.add(n.id)
                    if isinstance(n,ast.Attribute) and isinstance(n.value,ast.Name) and n.value.id in ns:
                        obj=ns[n.value.id]
                        if isinstance(obj,(types.ModuleType,type)) and n.attr in vars(obj) and is_safe(vars(obj)[n.attr]):safe.add(n.value.id+"."+n.attr)
        passives[mod]=safe
    base_names = {}
    for q in ordinary:
        module, _, name = q.rpartition('.')
        cls = vars(importlib.import_module(module))[name]
        base_names[q] = set().union(*(vars(b).keys() for b in cls.__mro__[1:]))
    dynamic={(owner,k):m for (kind,owner,k),m in dyn.items() if kind=="class"}
    return dict(reads=dict(reads),scoped=scoped,forwarded=forwarded,base_names=base_names,dynamic=dynamic,opaque=expand(record["opaque"])|unseen,bare=bare,
                attrs=dict(external),inherited=inherited,tracked=fields),passives,ordinary,expressions
