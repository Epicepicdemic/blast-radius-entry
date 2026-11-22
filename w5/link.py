"""Build bytecode use sites and immutable argument-use summaries from the unmodified pin."""
import ast
import collections
import dis
import gzip
import hashlib
import importlib.util
import json
import marshal
import sys
import types
from pathlib import Path

app, pin = Path("/app"), Path("/sqlglot")
sys.path.insert(0, str(app))
from impact import Observations, disjoint_ranges
from bounds import pool_facts
from frontier import same
from mutation_summaries import module_name
from read_effects import slot

ix = Observations(app / "impact.bin")
profile = Path("/w4/profile")
workers = pool_facts()
aliases = collections.defaultdict(int)
imports = collections.defaultdict(int)
external = collections.defaultdict(int)
by_symbol = {}
doc_readers = 0
test_files = {}
fixed_dispatch = {}
all_mentions = collections.Counter()
permitted = collections.Counter()
metadata = 0
fn_rows = collections.defaultdict(list)
sources = {}
from registration5 import sites as registration_sites
registration = {}
source_sha = {}
self_members = {}
pool = workers["unproved"]

def expand_context(row):
    mask = int(row[0], 16)
    for path in row[1]:
        sec = ix.section(path)
        mask |= ix.hit(sec, "observed") | ix.hit(sec, "cold") if sec and "cold" in sec else ix.all
    return mask

def instructions(code, eager=True):
    for op in dis.get_instructions(code):
        yield op, eager, code
    for c in code.co_consts:
        if isinstance(c, types.CodeType):
            yield from instructions(c, eager and not (c.co_flags & 1))

dyn = collections.defaultdict(int)
unseen = ix.all
for name in ("namespace", "namespace-rest", "namespace-workers"):
    row = json.load(gzip.open(profile/(name+".json.gz")))
    for tag, ctx in row["rows"]:
        dyn[tuple(tag)] |= expand_context(ctx)
    if name == "namespace":
        unseen = expand_context(row["opaque"])
    else:
        unseen &= ~sum(1 << ix.ids.index(t) for t in row["passed"])
        unseen |= expand_context(row["pool"])

exp=json.load(gzip.open("/w3/profile/exposure.json.gz"))
startups=set(map(tuple,exp["startup"]))
def entry_mask(path,code):
    if (path,code.co_qualname,code.co_firstlineno) in startups:return ix.all
    rows=exp["rows"].get(path,{})
    return int(rows.get(code.co_qualname+":"+str(code.co_firstlineno),"0"),16)|int(exp["unknown"],16)
for file in sorted([*(pin/"sqlglot").rglob("*.py"), *(pin/"tests").rglob("*.py")]):
    path = file.relative_to(pin).as_posix()
    mod = module_name(path)
    raw = file.read_bytes()
    source_sha[path] = hashlib.sha256(raw).digest()
    sec = ix.section(path)
    tree = ast.parse(raw)
    registration[path] = registration_sites(tree)
    pyc = compile(raw, "/sqlglot/"+path, "exec", dont_inherit=True)
    def bits(line):
        if not sec or "lines" not in sec:
            # Test-only files without a warm line table may still be imported by another test.
            if path.startswith("tests/") and sec and "cold" in sec:
                return ix.hit(sec, "cold")
            return ix.all
        if line in sec["warm_unknown"] or line in sec["order"]:
            return ix.all
        return (disjoint_ranges(sec, [(line,line)], ix) |
                workers["lines"].get(path, {}).get(line, 0))
    top = {a.asname or a.name for n in tree.body if isinstance(n, ast.ImportFrom) for a in n.names}
    uses = {name: 0 for name in top}
    for ins, eager, scope_code in instructions(pyc):
        line = ins.positions.lineno
        if ins.opname in ("LOAD_GLOBAL","LOAD_NAME","LOAD_FROM_DICT_OR_GLOBALS") and ins.argval in top:
            uses[ins.argval] |= ix.all if eager or not line else bits(line)&entry_mask(path,scope_code)
        if ins.argval in ("__defaults__","__kwdefaults__","__wrapped__","getfullargspec","signature") and ins.opname in ("LOAD_ATTR","LOAD_GLOBAL","LOAD_NAME"):
            metadata |= bits(line) if line else ix.all
        if ins.opname in ("LOAD_ATTR","LOAD_METHOD","LOAD_SUPER_ATTR"):
            external[ins.argval] |= bits(line) if line else ix.all
        if ins.opname in ("LOAD_GLOBAL","LOAD_NAME","LOAD_ATTR") and ins.argval in ("__doc__", "getdoc", "DocTestSuite", "getmembers", "signature", "getannotations"):
            doc_readers |= bits(line) if line else ix.all
    for n in ast.walk(tree):
        if isinstance(n,ast.Attribute):all_mentions[n.attr]+=1
        if isinstance(n,ast.Constant) and type(n.value) is str and n.value.isidentifier():all_mentions[n.value]+=1
        if isinstance(n, ast.ImportFrom):
            provider = n.module or ""
            if n.level:
                pkg = mod if file.name == "__init__.py" else mod.rpartition(".")[0]
                try:
                    provider = importlib.util.resolve_name("."*n.level+provider,pkg)
                except (ValueError, ImportError):
                    provider = "*"
            for a in n.names:
                imports[provider,a.name] |= bits(n.lineno)
    by_symbol[path] = uses
    if path.startswith("tests/"):
        test_files[path] = {n.name: (n.lineno,n.end_lineno) for n in tree.body if isinstance(n,ast.FunctionDef)}
    sources[mod] = {a.asname or a.name: n.module+"."+a.name for n in tree.body
                    if isinstance(n,ast.ImportFrom) and n.module and not n.level for a in n.names}
    for n in tree.body:
        if isinstance(n, ast.FunctionDef):
            sources[mod][n.name] = mod+"."+n.name
            fn_rows[mod+"."+n.name].append((n,False))
        if not isinstance(n, ast.ClassDef):
            continue
        self_members[mod+"."+n.name] = {m.name for m in n.body if isinstance(m, ast.FunctionDef)}
        for m in n.body:
            if isinstance(m,ast.FunctionDef):
                fn_rows["."+m.name].append((m,True))
            if isinstance(m,(ast.Assign,ast.AnnAssign)) and any(isinstance(t,ast.Name) and t.id=="FUNCTION_PARSERS" for t in (m.targets if isinstance(m,ast.Assign) else [m.target])) and isinstance(m.value,ast.Dict):
                for key,value in zip(m.value.keys,m.value.values):
                    if not (isinstance(key,ast.Constant) and type(key.value) is str and isinstance(value,ast.Lambda)
                            and len(value.args.args)==1 and not value.args.defaults):continue
                    c = value.body
                    if (isinstance(c,ast.Call) and not c.args and not c.keywords and isinstance(c.func,ast.Attribute)
                            and isinstance(c.func.value,ast.Name) and c.func.value.id==value.args.args[0].arg):
                        fixed_dispatch.setdefault((path,n.name,c.func.attr),set()).add(key.value)
                        permitted[c.func.attr]+=1

names = {}
for path, uses in by_symbol.items():
    mod = module_name(path)
    for name, mask in uses.items():
        m = (mask | external[name] | imports[mod,name] | imports[mod,"*"] | imports["*",name] |
             dyn["module",mod,name] | dyn["module",mod,"*"] | unseen | pool)
        if m != ix.all:
            names[path,name] = m

def arg_spec(fn, method):
    args = fn.args
    pos = [a.arg for a in args.posonlyargs+args.args]
    return (pos[1:] if method else pos, [a.arg for a in args.kwonlyargs], args.vararg.arg if args.vararg else None)

def use_modes(fn, param):
    """Track exactly how an argument is observed. Reject reassignment, aliasing and unknown escapes."""
    if fn.decorator_list or fn.args.kwarg:
        return None
    nodes=[n for st in fn.body for n in ast.walk(st)]
    if any(isinstance(n,(ast.Global,ast.Nonlocal)) or isinstance(n,ast.Name) and n.id in
           ("locals","vars","eval","exec","globals","_getframe","currentframe") for n in nodes):
        return None
    parents={child:n for n in nodes for child in ast.iter_child_nodes(n)}
    uses=set()
    for n in nodes:
        if not isinstance(n, ast.Name) or n.id!=param:continue
        p=parents.get(n)
        if not isinstance(n.ctx,ast.Load):return None
        if isinstance(p,ast.Call) and p.func is n:
            uses.add("invoke")
        elif isinstance(p,ast.Call) and isinstance(p.func,ast.Name) and p.func.id in ("isinstance","issubclass") and len(p.args)==2 and p.args[1] is n:
            uses.add("type")
        elif isinstance(p,ast.Compare):
            if all(isinstance(op,(ast.Is,ast.IsNot)) for op in p.ops):uses.add("identity")
            elif all(isinstance(op,(ast.Eq,ast.NotEq,ast.In,ast.NotIn)) for op in p.ops):uses.add("compare")
            else:return None
        elif isinstance(p,(ast.If,ast.While)) and p.test is n:
            uses.add("truth")
        else:return None
    return tuple(sorted(uses))

# Multiple implementations require agreement about the positional contract and all
# their possible uses. Unknown receivers are restricted again by the runtime rule.
roles = {}
for name, rows in fn_rows.items():
    spec = arg_spec(*rows[0])
    if any(arg_spec(*r)!=spec for r in rows[1:]):continue
    modes = {}
    for param in [*spec[0],*spec[1],*([spec[2]] if spec[2] else [])]:
        vals=[use_modes(fn,param) for fn,_ in rows]
        if all(v is not None for v in vals):modes[param] = tuple(sorted(set().union(*vals)))
    if modes:roles[name]=spec,modes

operands = json.load(gzip.open(Path(__file__).parent/"profile/operands.json.gz"))
assert operands["ids"]==ix.ids and set(operands["passed"])==set(ix.ids)
def operand_rows(rows):
    out={}
    for site, vals in rows.items():
        path,line,col=site.rsplit(":",2)
        out.setdefault((path,int(line)),{})[int(col)]={k:expand_context(v) for k,v in vals.items()}
    return out
exp=json.load(gzip.open("/w3/profile/exposure.json.gz"))
callback_exposure={}
for path,rows in exp["rows"].items():
    for key,v in rows.items():
        fn,ln=key.rsplit(":",1)
        if fn.endswith("<lambda>"):
            k=(path,int(ln))
            callback_exposure[k]=callback_exposure.get(k,0)|int(v,16)
for path,fn,line in exp["startup"]:
    if fn.endswith("<lambda>"):callback_exposure[path,line]=ix.all
from selector import load_index
sys.path.insert(0,str(pin))
pin_index=load_index(pin)
enum_members=set()
for c,row in pin_index.census.classes.items():
    import enum
    if not any(base in ("enum.Enum","enum.IntEnum","enum.StrEnum") for base in row["mro"]):continue
    for key in row["attrs"]:
        if key.isupper():enum_members.add((c,key))
# Census MROs truncate at foreign classes. Resolve known project types at build
# time and store only standard comparison/identity enum members.
import enum, importlib
for module,rows in pin_index.census.modules.items():
    if not module.startswith("sqlglot"):continue
    for k,entry in rows.items():
        if entry[0]!="type" or not entry[1].startswith(module+"."):continue
        if entry[1] not in pin_index.census.classes:continue
        try:cls=getattr(importlib.import_module(module),k)
        except (ImportError,AttributeError):continue
        if isinstance(cls,type) and issubclass(cls,enum.Enum) and cls.__eq__ in (str.__eq__,int.__eq__,object.__eq__):
            enum_members.update((entry[1],m) for m in cls.__members__)
obsfile=Path(__file__).parent/"profile/observers.json.gz"
observer=json.load(gzip.open(obsfile))
assert observer["ids"]==ix.ids and set(observer["passed"])==set(ix.ids)
observers={tuple(k):expand_context(v) for k,v in observer["observers"]}
files={k:expand_context(v) for k,v in observer["files"].items()}
errmod=importlib.import_module("sqlglot.errors")
errors={errmod.__name__+"."+n for n,x in vars(errmod).items() if isinstance(x,type) and issubclass(x,Exception)
        and x.__new__ is BaseException.__new__ and x.__init__ in (BaseException.__init__,Exception.__init__)}
wr=json.load(gzip.open(Path(__file__).parent/"profile/operand_workers.json.gz"))
assert wr["ids"]==ix.ids
def merged_sites(what):
    both=operand_rows(operands[what])
    for site,values in wr[what].items():
        path,ln,col=site.rsplit(":",2)
        at=both.setdefault((path,int(ln)),{}).setdefault(int(col),{})
        for val,mask in values.items():at[val]=at.get(val,0)|int(mask,16)
    return both
from field_link import build as field_index
fd,passive,ordinary,expressions=field_index(ix,pin,pin_index,dyn,unseen,expand_context,sources,external,self_members)
from shell_link import build as shell_index
shells,shell_types,actual_external,shell_unknown,shell_sites=shell_index(pin,ix,expand_context)
if actual_external is not None:
    names={}
    for path,uses in by_symbol.items():
        mod=module_name(path)
        for name,mask in uses.items():
            m=mask|actual_external.get((mod,name),0)|imports[mod,name]|imports[mod,"*"]|imports["*",name]|dyn["module",mod,name]|dyn["module",mod,"*"]|unseen|pool|(shell_unknown & external[name])
            if m!=ix.all:names[path,name]=m
private_fields=set()
class_trees={}
for q in ordinary:
    mod,_,cls=q.rpartition(".")
    file=pin.joinpath(*mod.split(".")).with_suffix(".py")
    if not file.exists():continue
    if mod not in class_trees:class_trees[mod]=ast.parse(file.read_bytes())
    tree=class_trees[mod]
    cs=next((c for c in tree.body if isinstance(c,ast.ClassDef) and c.name==cls),None)
    if cs is None:continue
    def target_name(x):
        return x.attr if isinstance(x,ast.Attribute) and isinstance(x.value,ast.Name) and x.value.id=="self" else None
    assigned=collections.defaultdict(list)
    for n in ast.walk(cs):
        if isinstance(n,(ast.Assign,ast.AnnAssign)):
            for t in n.targets if isinstance(n,ast.Assign) else [n.target]:
                if target_name(t):assigned[target_name(t)].append(n.value)
    info=pin_index.census.classes.get(mod+":"+cls,{})
    for k,vals in assigned.items():
        if not all(isinstance(v,(ast.Dict,ast.DictComp,ast.List,ast.ListComp,ast.Set,ast.SetComp)) for v in vals):continue
        if any(k in pin_index.census.classes.get(base,{}).get("attrs",{}) and
               pin_index.census.classes[base]["attrs"][k][0] in ("mut","elems") for base in info.get("mro",())):continue
        private_fields.add((q,k))
fmt_returns=set()
for key,rows in fn_rows.items():
    if not key.startswith("."):continue
    if all(isinstance(fn.returns,ast.Name) and fn.returns.id=="str" for fn,_ in rows):fmt_returns.add(key[1:])
# Explicitly audit stock project exception constructors that initialize only
# their own fields and Exception's message.
for n,c in vars(errmod).items():
    if not isinstance(c,type) or not issubclass(c,Exception) or c.__new__ is not Exception.__new__:continue
    try:src=ast.parse(__import__("textwrap").dedent(__import__("inspect").getsource(c.__init__))).body[0]
    except (OSError,TypeError):continue
    if all((isinstance(z,ast.Expr) and isinstance(z.value,ast.Call) and ast.unparse(z.value.func)=="super().__init__" and all(isinstance(a,ast.Name) for a in z.value.args)) or
        isinstance(z,ast.Assign) and all(isinstance(a,ast.Attribute) and isinstance(a.value,ast.Name) and a.value.id=="self" for a in z.targets) and
        all(isinstance(a,(ast.Name,ast.BoolOp,ast.Or,ast.List,ast.Load,ast.Constant)) for a in ast.walk(z.value)) for z in src.body):
        errors.add(errmod.__name__+"."+n)
from roles5 import build as type_routines
variadic_types=type_routines(fn_rows,sources)
from parameter_roles import analyze as param_roles
contracts=param_roles(fn_rows,sources)
transparent_fields=set()
from enum import Enum
def immutable_members(v):
    if type(v) in (str,int,bool,type(None)):return True
    if isinstance(v,Enum):return type(v).__eq__ in (str.__eq__,int.__eq__,object.__eq__)
    if type(v) in (set,frozenset,tuple,list):return all(type(x) in (str,int,bool,type(None)) or isinstance(x,Enum) for x in v)
    return False
all_values=collections.defaultdict(list)
for q in ordinary:
    mod,cls=q.rsplit(".",1)
    obj=getattr(sys.modules.get(mod),cls,None)
    if not isinstance(obj,type):continue
    for field,v in vars(obj).items():
        if field.isupper():all_values[field].append(v)
transparent_fields={k for k,vals in all_values.items() if all(immutable_members(v) for v in vals)}
from sqlglot.dialects.dialect import Dialect
registry={k:(c.__module__,c.__qualname__) for k,c in Dialect.classes.items()}
from sqlglot import exp as expression_namespace
exprkeys={n:v.__module__+"."+v.__qualname__ for n,v in vars(expression_namespace).items() if isinstance(v,type) and issubclass(v,expression_namespace.Expr)}
locations={"exp.Properties.Location."+s for s in expression_namespace.Properties.Location.__members__}
dispatch_file=json.load(gzip.open(Path(__file__).parent/"profile/dispatch_uses.json.gz"))
assert dispatch_file['ids']==ix.ids and set(dispatch_file['passed'])==set(ix.ids)
dispatch={tuple(k):expand_context(v) for k,v in dispatch_file['rows']}
dispatch_dynamic=collections.defaultdict(int)
dispatch_owners={}
for q in ordinary:
    mod,cn=q.rsplit(".",1);c=vars(sys.modules[mod]).get(cn)
    if isinstance(c,type):dispatch_owners[q]={f for f in ("TRANSFORMS","PROPERTIES_LOCATION","FUNCTIONS","FUNCTION_PARSERS","NO_PAREN_FUNCTION_PARSERS") if any(f in vars(b) for b in c.__mro__)}
for (owner,k),m in fd['dynamic'].items():
    if k in {"TRANSFORMS","PROPERTIES_LOCATION","FUNCTIONS","FUNCTION_PARSERS","NO_PAREN_FUNCTION_PARSERS","*"}:
        for table in {k} if k!='*' else {"TRANSFORMS","PROPERTIES_LOCATION","FUNCTIONS","FUNCTION_PARSERS","NO_PAREN_FUNCTION_PARSERS"}:
            if table in dispatch_owners.get(owner,()):dispatch_dynamic[table]|=m
from sqlglot.parser import Parser
parser_types={q for q in ordinary if isinstance((c:=vars(sys.modules[q.rsplit(".",1)[0]]).get(q.rsplit(".",1)[1])),type) and issubclass(c,Parser)}
# These pin factories return newly allocated AST shells. Resolve every public
# alias to the actual function object before making the contract available.
import inspect
factories=set()
factory_values=(expression_namespace.column,)
for mod in pin_index.census.modules:
    m=sys.modules.get(mod)
    if m:
        for n,v in vars(m).items():
            if any(v is f for f in factory_values):factories.add((mod,n))
factories.add((expression_namespace.Dot.__module__+"."+expression_namespace.Dot.__qualname__,"build"))
import inspect
forward={};invalid_calls=0
runtime_classes = {cl for q in ordinary if (cl:=vars(sys.modules[q.rpartition('.')[0]]).get(q.rpartition('.')[2])) and isinstance(cl,type)}
for q in ordinary:
    mod,cn=q.rsplit(".",1);c=vars(sys.modules[mod]).get(cn)
    if not isinstance(c,type) or q in {"sqlglot.generator.Generator","sqlglot.parser.Parser"}:continue
    source=vars(c).get('__init__')
    if not isinstance(source,types.FunctionType) or not source.__code__.co_filename.startswith('/sqlglot/'):continue
    targets={next((vars(base)['__init__'] for base in d.__mro__[d.__mro__.index(c)+1:] if '__init__' in vars(base)),None) for d in runtime_classes if c in d.__mro__}
    if len(targets)!=1:continue
    dest=targets.pop()
    if not isinstance(dest,types.FunctionType):continue
    try:aa=inspect.signature(source);bb=inspect.signature(dest)
    except (TypeError,ValueError):continue
    if [(x.name,x.kind) for x in aa.parameters.values()]!=[(x.name,x.kind) for x in bb.parameters.values()]:continue
    if any(x.default is not y.default or not (x.default is inspect.Parameter.empty or type(x.default) in (str,int,bool,float,type(None)) or isinstance(x.default,Enum)) for x,y in zip(aa.parameters.values(),bb.parameters.values())):continue
    try:fn=ast.parse(__import__('textwrap').dedent(inspect.getsource(source))).body[0]
    except (ValueError,OSError,SyntaxError):continue
    forward[q]=ast.dump(fn.args)
for file in (pin/'tests').rglob('test_*.py'):
    path=file.relative_to(pin).as_posix();tree=ast.parse(file.read_bytes());methods={n.name for n in ast.walk(tree) if isinstance(n,ast.FunctionDef) and any(isinstance(z,ast.Name) and z.id=='TypeError' for z in ast.walk(n))}
    for i,t in enumerate(ix.ids):
        if t.startswith(path+'::') and t.rsplit('::',1)[-1] in methods:invalid_calls|=1<<i
def observed_profile(name):
    doc=json.load(gzip.open(Path(__file__).parent/'profile'/(name+'.json.gz')))
    assert doc['ids']==ix.ids and set(doc['passed'])==set(ix.ids)
    return doc,expand_context(doc['opaque'])
prefix_doc,prefix_opaque=observed_profile('prefixes');prefix=collections.defaultdict(dict)
for (site,key),ctx in prefix_doc['rows']:
    path,ln,col,tag=site.rsplit(':',3);prefix[path,int(ln),int(col),tag][key]=expand_context(ctx)
parser_tree=ast.parse((pin/'sqlglot/parser.py').read_bytes());pc=next(n for n in parser_tree.body if isinstance(n,ast.ClassDef) and n.name=='Parser');pf={n.name:n for n in pc.body if isinstance(n,ast.FunctionDef)}
consumer=pf['_add_comments'];match=pf['_match'];comment_contract=None
if len(consumer.body)==1 and isinstance(consumer.body[0],ast.If) and ast.unparse(consumer.body[0].test)=='expression and self._prev_comments' and not consumer.body[0].orelse and [ast.unparse(n) for stt in match.body for n in ast.walk(stt) if isinstance(n,ast.Call) and any(isinstance(z,ast.Name) and z.id=='expression' for z in ast.walk(n))]==['self._add_comments(expression)'] and all(not any(n in cls.__dict__ for n in ('_add_comments','_match')) for cls in Parser.__subclasses__()):
    comment_contract=consumer.body[0].body[0].lineno,consumer.body[0].body[-1].end_lineno
passive_data=None;passive_sites=None;len_bindings={};passive_opaque=0
if (Path(__file__).parent/'profile/passive_ops.json.gz').exists():
    pd,passive_opaque=observed_profile('passive_ops');passive_data={};passive_sites=set()
    invalid_calls={'*':passive_opaque}
    shape_values={}
    for key,ctx in pd['rows']:
        if key.startswith(('@keyword/','@copy-opaque/','@copy-read/')):
            group,_,name=key[1:].partition('/')
            shape_values[group,name]=expand_context(ctx);continue
        if key.startswith('@argument-error'):
            name=key.partition('/')[2] or '*'
            invalid_calls[name]=invalid_calls.get(name,0)|expand_context(ctx);continue
        path,ln,v=key.rsplit(':',2);passive_data[path,int(ln),v if v=='error' else int(v)]=expand_context(ctx)
    sys.path[:0]=[str(Path(__file__).parent/'profile'),'/w4/profile'];from passive_ops import sites
    for file in (pin/'sqlglot').rglob('*.py'):
        path=file.relative_to(pin).as_posix();tree=ast.parse(file.read_bytes());valid=sites(tree)
        passive_sites.update((path,n.lineno,n.col_offset) for n in ast.walk(tree) if id(n) in valid and hasattr(n,'lineno'))
        len_bindings[path]=not any(isinstance(n,ast.Name) and not isinstance(n.ctx,ast.Load) and n.id=='len' or isinstance(n,ast.arg) and n.arg=='len' or isinstance(n,ast.alias) and (n.asname or n.name) in ('len','*') or isinstance(n,(ast.ClassDef,ast.FunctionDef)) and n.name=='len' for n in ast.walk(tree))
pool_operands=json.load(gzip.open(Path(__file__).parent/'profile/operand_workers.json.gz'))
entry_proved=int(pool_operands['proved'],16) if 'test_entries' in pool_operands else 0
no_process=int(pool_operands.get('no_process','0'),16)
for i,nodeid in enumerate(ix.ids):
    if not no_process & (1<<i):continue
    # The earlier pool census also classifies pure pickle tests as potential workers.
    # Discharge only this file-local serialization case when the audit observed no
    # child or submitted task. Files that use another process or thread API stay opaque.
    source=(pin/nodeid.partition('::')[0]).read_bytes()
    if b'pickle' in source and not any(word in source for word in (
            b'concurrent', b'rocessing', b'rocessPool', b'hread', b'fork', b'subprocess',
            b'spawn', b'os.system', b'os.exec', b'pytest_xdist')):
        entry_proved |= 1<<i
pool_entries=set(map(tuple,pool_operands.get('test_entries',())))
# Every expression implementation must either raise or yield the positively
# checked local. A type assertion cannot be inferred from the method's name.
import textwrap
def checked_find_all():
    import inspect
    from sqlglot import exp
    kinds = {getattr(vars(sys.modules[q.rpartition('.')[0]])[q.rpartition('.')[2]], 'find_all', None) for q in expressions}
    for method in kinds:
        if method is None:return False
        fn = ast.parse(textwrap.dedent(inspect.getsource(method))).body[0]
        body=[st for st in fn.body if not (isinstance(st,ast.Expr) and isinstance(st.value,ast.Constant))]
        if len(body)==1 and isinstance(body[0],ast.Raise):continue
        if len(body)!=1 or not isinstance(body[0],ast.For) or len(body[0].body)!=1:return False
        loop=body[0]
        if loop.orelse or not isinstance(loop.target,ast.Name) or not fn.args.vararg:return False
        cond=loop.body[0]
        if not isinstance(cond,ast.If) or cond.orelse or len(cond.body)!=1:return False
        check=cond.test;out=cond.body[0]
        if not (isinstance(check,ast.Call) and isinstance(check.func,ast.Name) and check.func.id=='isinstance' and len(check.args)==2
                and not check.keywords and all(isinstance(a,ast.Name) for a in check.args) and check.args[0].id==loop.target.id and check.args[1].id==fn.args.vararg.arg
                and isinstance(out,ast.Expr) and isinstance(out.value,ast.Yield) and isinstance(out.value.value,ast.Name) and out.value.value.id==loop.target.id):return False
        if method.__globals__.get('isinstance',isinstance) is not isinstance:return False
    return bool(kinds)
checked_find=checked_find_all()

atomic=(str,bytes,int,bool,float,complex,type(None),range)
def immutable_value(value):
    return type(value) in atomic or type(value) in (tuple,frozenset) and all(immutable_value(v) for v in value)
scalar_globals=set();scalar_iterables=set()
for module in pin_index.census.modules:
    obj=sys.modules.get(module)
    if obj is None:continue
    for name,value in vars(obj).items():
        if immutable_value(value):scalar_globals.add((module,name))
        if type(value) in (tuple,list,set,frozenset,dict) and all(immutable_value(v) for v in value):scalar_iterables.add((module,name))
from sqlglot.tokens import Tokenizer, TokenType
from sqlglot import exp
import inspect,types
copy_atoms=set();copy_slots=set()
for mod in pin_index.census.modules:
    m=sys.modules.get(mod)
    if m is not None:
        for name,value in vars(m).items():
            if type(value) in (frozenset,tuple) and value and all(isinstance(t,type) and t in (str,bytes,bool,int,float,type(None)) for t in value):
                treefile=getattr(m,'__file__','')
                if treefile and treefile.startswith('/sqlglot/'):copy_atoms.add((treefile[len('/sqlglot/'):],name))
for q in expressions:
    mod,_,name=q.rpartition('.');cls=vars(sys.modules[mod])[name]
    method=vars(cls).get('__deepcopy__')
    if not inspect.isfunction(method):continue
    visited={cls};pending=[cls]
    while pending:
        typ=pending.pop()
        for sub in type.__subclasses__(typ):
            if sub not in visited:visited.add(sub);pending.append(sub)
    for field in ('_meta',):
        if all(c.__setattr__ is object.__setattr__ and isinstance(inspect.getattr_static(c,field,None),types.MemberDescriptorType) for c in visited):
            copy_slots.add((method.__code__.co_filename.removeprefix('/sqlglot/'),method.__qualname__,field))
# Eligibility is restricted to keys covered by the installed collector.
token_scopes={};token_dynamic=fd['opaque']
token_words=set(pd.get('keyword_inventory',())) if passive_data is not None else set()

for path in source_sha:
    sec=ix.section(path)
    if not sec:continue
    mod=sys.modules.get(module_name(path))
    if not mod:continue
    for _,_,field,_ in sec.get('regions',()):
        if not field.endswith('.KEYWORDS') or vars(mod).get('TokenType') is not TokenType:continue
        obj=mod
        for part in field.split('.')[:-1]:
            obj=getattr(obj,part,None)
            if obj is None:break
        if isinstance(obj,type) and issubclass(obj,Tokenizer) and type(getattr(obj,'KEYWORDS',None)) is dict:
            token_scopes[path,field]=True
for (q,field),items in fd['reads'].items():
    if field!='__namespace__':continue
    if q.rsplit('.',1)[-1].endswith(('Tokenizer','TokenizerBase','TokenizerCore')):
        for (mode,key),m in items.items():
            if mode in ('namespace','unknown') or key in ('KEYWORDS','keywords','_KEYWORD_TRIE'):token_dynamic|=m
native_dict_bases=set()
for q in ordinary:
    mod,_,name=q.rpartition('.')
    cls=vars(sys.modules[mod])[name]
    for member in set().union(*(vars(c).keys() for c in cls.__mro__[1:])):
        if member.isupper():
            v=next(vars(c)[member] for c in cls.__mro__[1:] if member in vars(c))
            if type(v) is dict:native_dict_bases.add((q,member))
from table_flow5 import closed
closed_dispatch_fields={name for name in ('FUNCTIONS',) if closed(pin,name)}
out=dict(closed_dispatch_fields=closed_dispatch_fields,token_words=token_words,token_scopes=token_scopes,token_dynamic=token_dynamic,shape_values=shape_values,copy_slots=copy_slots,copy_atoms=copy_atoms,native_dict_bases=native_dict_bases,scalar_globals=scalar_globals,scalar_iterables=scalar_iterables,checked_find=checked_find,entry_proved=entry_proved,pool_entries=pool_entries,prefixes=dict(prefix),prefix_opaque=prefix_opaque,parser_comment_contract=comment_contract,passive_ops=passive_data,passive_opaque=passive_opaque,passive_sites=passive_sites,builtin_len=len_bindings,forward=forward,forward_exceptions=invalid_calls,factories=factories,parser_types=parser_types,expression_keys=exprkeys,locations=locations,dispatch=dispatch,dispatch_dynamic=dict(dispatch_dynamic),dispatch_opaque=expand_context(dispatch_file['opaque'])|fd['opaque'],registry=registry,contracts=contracts,transparent_fields=transparent_fields,variadic_types=variadic_types,ordinary_expressions=expressions,ordinary_classes=ordinary,private_fields=private_fields,str_members=fmt_returns,
    dynamic_names=set(all_mentions),shells=shells,shell_types=shell_types,shell_sites=shell_sites,shell_unknown=shell_unknown,passive=passive,field_data=fd,worker_proved=int(wr["proved"],16),exception_types=errors,observers=observers,source_files=files,enums=enum_members,method_names=set(fn_rows),metadata=metadata,callback_exposure=callback_exposure,names=names, roles=roles, imports=sources, members=self_members,
         registration_sites=registration, test_files=test_files, test_entries=set(map(tuple,operands["test_entries"])),
         known_methods={k for k in fixed_dispatch if permitted[k[2]]==all_mentions[k[2]]}, doc_readers=doc_readers,
         opaque=expand_context(operands["opaque"]), digest=source_sha,
         comparisons=merged_sites("comparisons"), callbacks=merged_sites("callbacks"))
(app/"receipts5.bin").write_bytes(marshal.dumps(out))
print("linked pin use sites",len(names),"argument summaries",len(roles),"enum sites",len(out["comparisons"]))
