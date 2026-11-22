"""Bound inert dispatch-table edits by the pin's key, shape and bulk readers."""
import ast
import marshal
from functools import lru_cache
from pathlib import Path
from impact import family_path
from patching import compiled_source,parsed_source

@lru_cache(1)
def linked():
    return marshal.loads(Path(__file__).with_name("dispatch.bin").read_bytes())

def token_enum(tree):
    bindings=[]
    for n in ast.walk(tree):
        if isinstance(n,ast.ImportFrom):
            for a in n.names:
                if (a.asname or a.name)=="TokenType":
                    bindings.append(n.level==0 and n.module in ("sqlglot.tokens","sqlglot.tokenizer_core") and a.name=="TokenType" and n in tree.body)
                if a.name=="*":return False
        elif isinstance(n,ast.Name) and n.id=="TokenType" and not isinstance(n.ctx,ast.Load):
            return False
        elif isinstance(n,(ast.FunctionDef,ast.ClassDef)) and n.name=="TokenType":
            return False
    return bindings==[True]

def segments(node):
    groups=[[]];barriers=[]
    for k,v in zip(node.keys,node.values):
        if isinstance(k,ast.Constant) and type(k.value) is str:
            groups[-1].append((k.value,ast.dump(v),v))
        elif k is None and isinstance(v,ast.Call) and not v.keywords and len(v.args)==2 and isinstance(v.func,ast.Attribute) and v.func.attr=="fromkeys" and isinstance(v.func.value,ast.Name) and v.func.value.id=="dict" and isinstance(v.args[0],ast.Tuple) and all(isinstance(x,ast.Constant) and type(x.value) is str for x in v.args[0].elts):
            groups[-1].extend((x.value,ast.dump(v.args[1]),v.args[1]) for x in v.args[0].elts)
        else:
            barriers.append((ast.dump(k) if k is not None else None,ast.dump(v)))
            groups.append([])
    return groups,barriers

def dispatch_bound(ix,ch,sec,field,old,new):
    if not family_path(ch.path) or not isinstance(old,ast.Dict) or not isinstance(new,ast.Dict):return None
    table=field.rsplit(".",1)[-1]
    if table not in ("FUNCTIONS","KEYWORDS"):return None
    owner=ch.path[:-3].replace("/",".")+"."+field
    data=linked()
    profile=data["tables"].get(owner)
    if not profile:return None
    a,fixed=segments(old);b,fixed_new=segments(new)
    if fixed!=fixed_new:return None
    changed=set();order=False;operands=[]
    for left,right in zip(a,b):
        lk=[x[0] for x in left];rk=[x[0] for x in right]
        if len(set(lk))!=len(lk) or len(set(rk))!=len(rk):return None
        order |= lk!=rk
        lv={k:(v,n) for k,v,n in left};rv={k:(v,n) for k,v,n in right}
        for k in lv.keys()|rv.keys():
            if lv.get(k,(None,))[0]!=rv.get(k,(None,))[0]:
                changed.add(k)
                operands.extend(d[k][1] for d in (lv,rv) if k in d)
    if not changed or changed & {"@keys"}:return None
    if table=="KEYWORDS":
        if order or not token_enum(parsed_source(ch.before)):return None
        if not all(isinstance(n,ast.Attribute) and isinstance(n.value,ast.Name) and n.value.id=="TokenType" and n.attr in data["tokens"] for n in operands):return None
    else:
        # The release proves the changed eager operations inert and all new callbacks
        # already present. The key trace adds a bound within its family obligation.
        from static_bounds import deferred_table
        if deferred_table(ix,ch,field,old,new) is None:return None
    compiled_source(ch.after,ch.path)
    keep=profile.get(None,0)|data["opaque"]|ix.hit(sec,"opens")|ix.inspected|ix.reflect(ch.path)
    if order:keep|=profile.get("@keys",0)
    for k in changed:keep|=profile.get(k,0)
    return (keep & ix.family(ch.path))|ix.hit(sec,"opens")|ix.reflect(ch.path)
