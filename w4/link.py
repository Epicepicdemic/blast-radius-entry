"""Link concrete class receivers to independent cold loads and pin test scopes."""
import gzip,json,marshal,sys
from pathlib import Path
sys.path.insert(0,"/app")
from impact import Observations
app=Path("/app")
root=Path("/sqlglot")
ix=Observations(app/"impact.bin")
src=Path(__file__).parent/"profile/slots.json.gz"
p=json.load(gzip.open(src))
assert p["ids"]==ix.ids and p["passed"]==len(ix.ids)
def expand(record):
    mask=int(record[0],16)
    for mod in record[1]:
        s=ix.section(mod)
        if s and "cold" in s:
            mask|=ix.hit(s,"cold")|ix.hit(s,"observed")
        else:
            mask|=ix.all
    return mask
pool_ids=set(json.loads((app/"pool_readers.json").read_bytes()))
pool=sum(1<<i for i,t in enumerate(ix.ids) if t in pool_ids)
tables={}
for ns,key,record in p["rows"]:
    tables.setdefault(ns,{})[key]=expand(record)
# Resource-sensitive tests are derived from pinned pytest markers/explicit limits,
# plus long integration schedules. No failing test lists enter the image.
import ast
resources=0
by_file={}
for i,tid in enumerate(ix.ids):
    path,*qual=tid.split("::")
    if len(qual)==2:by_file.setdefault(path,{})[tuple(qual)]=i
for path,ids in by_file.items():
    tree=ast.parse((Path("/sqlglot")/path).read_bytes())
    for cls in tree.body:
        if not isinstance(cls,ast.ClassDef):continue
        for fn in cls.body:
            if not isinstance(fn,ast.FunctionDef) or (cls.name,fn.name) not in ids:continue
            tokens={n.attr for n in ast.walk(fn) if isinstance(n,ast.Attribute)}
            vals={v for n in ast.walk(fn) if isinstance(n,ast.Constant) and type(v:=n.value) is str}
            if any(isinstance(n,ast.keyword) and n.arg=="max_nodes" for n in ast.walk(fn)) or any("tpcds" in t.lower() for t in tokens) or tokens&{"timeout","setrecursionlimit","get_traced_memory","monotonic","perf_counter"} or any("tpcds" in x.lower().replace("-","").replace("_","") for x in vals):
                resources |= 1<<ids[cls.name,fn.name]
sys.path.insert(0,str(Path(__file__).parent))
from ownership_effects import leaf_index
leaf=leaf_index(Path("/sqlglot"))
(app/"slots.bin").write_bytes(marshal.dumps(dict(tables=tables,leaf=leaf,opaque=expand(p["opaque"]),pool=pool,resources=resources)))
print("linked slots",len(tables),"resource-sensitive",resources.bit_count())
p=json.load(gzip.open(src.with_name("scalars.json.gz")))
assert p["ids"]==ix.ids
sites={}
for key,vals in p["rows"].items():
    path,line,col=key.rsplit(":",2)
    sites.setdefault((path,int(line)),{})[int(col)]=[(t,v,expand(ctx)) for t,v,ctx in vals]
(app/"scalars.bin").write_bytes(marshal.dumps(dict(opaque=expand(p["opaque"]),sites=sites)))

from read_effects import build as read_roles
(app/"read-effects.bin").write_bytes(marshal.dumps(read_roles(Path("/sqlglot"))))
from collections import defaultdict
from impact import disjoint_ranges
import pkgutil,importlib
sys.path.insert(0,"/sqlglot")
import sqlglot
modules={}
dynamic=set()
for module in sorted({"sqlglot",*(m.name for m in pkgutil.walk_packages(sqlglot.__path__,"sqlglot."))}):
    if module.endswith(".__main__"):continue
    try:obj=importlib.import_module(module)
    except ImportError:continue
    modules[module]=set(vars(obj))
    if "__getattr__" in vars(obj) or "__path__" in vars(obj):dynamic.add(module)
baseline=json.load(gzip.open(src.with_name("pool-lines.json.gz")))
assert baseline["ids"]==ix.ids
proved=int(baseline["proved"],16)
workers={p:{int(k):int(v,16) for k,v in m.items()} for p,m in baseline["rows"].items()}
(app/"workers.bin").write_bytes(marshal.dumps({"lines":workers,"unproved":pool & ~proved}))
import symbols
p=json.load(gzip.open(src.with_name("namespace.json.gz")))
assert p["ids"]==ix.ids
dynamic_reads=defaultdict(int)
for k,v in p["rows"]:dynamic_reads[tuple(k)]|=expand(v)
unread=expand(p["opaque"])
for companion in (src.with_name("namespace-rest.json.gz"),src.with_name("namespace-workers.json.gz")):
    if not companion.exists():continue
    rp=json.load(gzip.open(companion))
    assert rp["ids"]==ix.ids
    for k,v in rp["rows"]:dynamic_reads[tuple(k)]|=expand(v)
    done=sum(1<<ix.ids.index(t) for t in rp["passed"])
    unread=(unread & ~done)|expand(rp["pool"])
raw=symbols.link(ix,Path("/sqlglot"))
def names(k,m):
    path,name=k
    mod=path[:-3].replace("/",".")
    return m|dynamic_reads["module",mod,"*"]|dynamic_reads["module",mod,name]|unread|ix.inspected
globals_={k:names(k,m) for k,m in raw.items()}
s=marshal.loads((app/"slots.bin").read_bytes());s["globals"]=globals_
# Resource suite stress workloads use explicit nontrivial construction sizes in the pin.
stress=resources
for path,ids in by_file.items():
    t=ast.parse((root/path).read_bytes())
    for cls in t.body:
        if not isinstance(cls,ast.ClassDef):continue
        for fn in cls.body:
            if not isinstance(fn,ast.FunctionDef) or (cls.name,fn.name) not in ids:continue
            if any(isinstance(n,ast.BinOp) and isinstance(n.op,ast.Mult) and isinstance(n.right,ast.Constant) and type(n.right.value) is int and n.right.value>=10000 for n in ast.walk(fn)):
                stress|=1<<ids[cls.name,fn.name]
s["import_stress"]=stress
(app/"slots.bin").write_bytes(marshal.dumps(s))

# Direct calls only. Bound early aliases, properties, class/init reads, multiple
# implementations, dunder methods, and reflective readers have explicit fallback.
sites=defaultdict(list)
definitions=defaultdict(list)
unsafe=set()
root=Path("/sqlglot")
for parent in ("tests","sqlglot"):
    for file in (root/parent).rglob("*.py"):
        path=file.relative_to(root).as_posix()
        tree=ast.parse(file.read_bytes())
        parents={c:n for n in ast.walk(tree) for c in ast.iter_child_nodes(n)}
        for n in ast.walk(tree):
            if isinstance(n,ast.FunctionDef) and isinstance(parents.get(n),ast.ClassDef):
                owner=parents[n].name
                definitions[n.name].append((path,owner,n))
            if isinstance(n,ast.Constant) and type(n.value) is str and n.value.isidentifier():unsafe.add(n.value)
            if isinstance(n,ast.Attribute) and n.attr.startswith("_"):
                call=parents.get(n)
                if not isinstance(call,ast.Call) or call.func is not n or call.args or call.keywords:
                    unsafe.add(n.attr)
                else:sites[n.attr].append((path,n.lineno))
methods={}
for name,defs in definitions.items():
    if len(defs)!=1 or name in unsafe or not name.startswith("_") or name.startswith("__") or not sites[name]:continue
    path,cls,fn=defs[0]
    if fn.decorator_list or len(fn.args.args)!=1 or fn.args.defaults or fn.args.kwonlyargs or fn.args.vararg or fn.args.kwarg:continue
    if not path.startswith(("sqlglot/parsers/","sqlglot/generators/")):continue
    # Guard private method removal against a body with independent global effects.
    if any(isinstance(n,(ast.Global,ast.Nonlocal,ast.Import,ast.ImportFrom)) or isinstance(n,(ast.Attribute,ast.Subscript)) and not isinstance(n.ctx,ast.Load) for n in ast.walk(fn)):continue
    sec=ix.section(path); region=sec["functions"].get(cls+"."+name)
    if not region:continue
    mask=disjoint_ranges(sec,[(region[1],region[2])],ix)
    for cp,line in sites[name]:
        f=ix.section(cp)
        if not f or "lines" not in f or line in f["warm_unknown"] or line in f["order"]:
            mask=ix.all;break
    mod=path[:-3].replace("/","."); owner=mod+"."+cls
    methods[owner+"."+name]=mask|dynamic_reads["class",owner,"*"]|dynamic_reads["class",owner,name]|(unread & ix.family(path))|ix.inspected
(app/"names.bin").write_bytes(marshal.dumps(dict(modules=modules,dynamic_modules=dynamic,methods=methods)))
p=json.load(gzip.open(src.with_name("class-values.json.gz")))
assert p["ids"]==ix.ids
from selector import load_index
index=load_index(root)
exact={}
value_trees={}
for q,receipt in p["rows"].items():
    owner,_,field=q.rpartition(".")
    mod,_,cls=owner.rpartition(".")
    module_file=Path(*mod.split(".")).with_suffix(".py")
    if not (root/module_file).is_file():continue
    if mod not in value_trees:
        value_trees[mod]=ast.parse((root/module_file).read_bytes())
    tree=value_trees[mod]
    # A bare class-body read may embed the scalar in another declaration.
    if any(isinstance(n,ast.Name) and n.id==field and isinstance(n.ctx,ast.Load) for n in ast.walk(tree)):continue
    legacy=index.binding_readers({("cls_val",owner,field)})
    if legacy is None:continue
    exact[q]=expand(receipt)|dynamic_reads["class",owner,"*"]|dynamic_reads["class",owner,field]|(expand(p["opaque"]) & legacy)|ix.inspected
(app/"class-values.bin").write_bytes(marshal.dumps(exact))

raw=json.load(gzip.open(src.with_name("tpc-rows.json.gz")))
assert raw["rows"]>0
(app/"signature-lines.bin").write_bytes(marshal.dumps({p:{int(k):v for k,v in rows.items()} for p,rows in raw["lines"].items()}))

p=json.load(gzip.open(src.with_name("guards.json.gz")))
assert p["ids"]==ix.ids
guards={}
for k,values_ in p["sites"].items():
    path,line,col,slot=k.rsplit(":",3)
    guards.setdefault((path,int(line)),{})[(int(col),int(slot))]={tag:expand(ctx) for tag,ctx in values_.items()}
(app/"guards.bin").write_bytes(marshal.dumps(dict(sites=guards,opaque=expand(p["opaque"]))))

# A bulk reader can inspect all values. Keys-only readers can distinguish shape.
from sqlglot.tokens import TokenType
dispatch=json.load(gzip.open(src.with_name("dispatch.json.gz")))
assert dispatch["ids"]==ix.ids and dispatch["passed"]==len(ix.ids)
dispatch_tables={}
for owner,key,receipt in dispatch["rows"]:
    dispatch_tables.setdefault(owner,{})[key]=expand(receipt)
# A copied parent table can be consulted entirely through the child's plain
# dictionary. Require a closed leaf and reject explicit class-qualified consumers.
import inspect
def resolve_static(module,expr):
    if isinstance(expr,ast.Name):return vars(module).get(expr.id)
    if isinstance(expr,ast.Attribute):
        value=resolve_static(module,expr.value)
        if isinstance(value,(type,type(sys))):
            return inspect.getattr_static(value,expr.attr,None)
    return None
classes={}
def register(cls):
    if not cls.__module__.startswith("sqlglot") or id(cls) in known:return
    known.add(id(cls))
    classes[cls.__module__+"."+cls.__qualname__]=cls
    for member in vars(cls).values():
        if isinstance(member,type):register(member)
known=set()
for mod in modules:
    for member in tuple(vars(sys.modules[mod]).values()):
        if isinstance(member,type):register(member)
exported=set()
for mod in modules:
    obj=sys.modules[mod]
    path=getattr(obj,"__file__",None)
    if not path or not path.endswith(".py"):continue
    for node in ast.walk(ast.parse(Path(path).read_bytes())):
        if not isinstance(node,ast.Attribute) or node.attr not in ("FUNCTIONS","KEYWORDS"):continue
        owner=resolve_static(obj,node.value)
        if isinstance(owner,type):
            exported.add(owner.__module__+"."+owner.__qualname__+"."+node.attr)
for table in tuple(dispatch_tables):
    cls=classes.get(table.rpartition(".")[0])
    if cls is None or type.__subclasses__(cls) or table in exported:
        del dispatch_tables[table]
(app/"dispatch.bin").write_bytes(marshal.dumps(dict(tables=dispatch_tables,tokens=set(TokenType.__members__),
    opaque=expand(dispatch["opaque"])|pool)))
