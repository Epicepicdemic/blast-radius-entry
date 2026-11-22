"""Track the mutable shell reached by a write, separately from objects stored inside it."""
import ast
from collections import defaultdict
from functools import lru_cache
from patching import parsed_source

FRESH = {ast.List:"list", ast.ListComp:"list", ast.Dict:"dict", ast.DictComp:"dict",
         ast.Set:"set", ast.SetComp:"set"}
BUILTINS = {"list","set","dict","tuple","frozenset"}
FN = (ast.FunctionDef, ast.AsyncFunctionDef)
MUTATORS = {"append","extend","insert","pop","remove","clear","reverse","sort","add",
            "discard","update","difference_update","intersection_update","setdefault",
            "symmetric_difference_update","popitem"}

def assignments(fn):
    values=defaultdict(list)
    for node in ast.walk(fn):
        if isinstance(node,(ast.Assign,ast.AnnAssign,ast.NamedExpr)):
            for target in node.targets if isinstance(node,ast.Assign) else [node.target]:
                if isinstance(target,ast.Name) and node.value is not None:
                    values[target.id].append(node.value)
        elif isinstance(node,(ast.For,ast.comprehension)):
            for target in ast.walk(node.target):
                if isinstance(target,ast.Name):values[target.id].append(None)
        elif isinstance(node,ast.AugAssign) and isinstance(node.target,ast.Name):
            values[node.target.id].append(None)
    for arg in ast.walk(fn.args):
        if isinstance(arg,ast.arg):values[arg.arg].append(None)
    return values

def unshadowed(fn,tree):
    bound=set()
    for n in [*tree.body,*ast.walk(fn)]:
        if isinstance(n,ast.Name) and not isinstance(n.ctx,ast.Load):bound.add(n.id)
        if isinstance(n,(ast.FunctionDef,ast.AsyncFunctionDef,ast.ClassDef)):bound.add(n.name)
        if isinstance(n,ast.arg):bound.add(n.arg)
        if isinstance(n,ast.alias):bound.add(n.asname or n.name.split(".")[0])
        if isinstance(n,(ast.Assign,ast.AnnAssign)):
            for v in n.targets if isinstance(n,ast.Assign) else [n.target]:
                if isinstance(v,ast.Name):bound.add(v.id)
        if isinstance(n,ast.ImportFrom) and any(a.name=="*" for a in n.names):return set()
    # A locally or globally rebound collection factory is not a proof of ownership.
    # Restrict the special case to the builtins with no alternate lexical binding.
    for n in ast.walk(tree):
        if isinstance(n,ast.alias):bound.add(n.asname or n.name.split(".")[0])
        if isinstance(n,ast.Name) and not isinstance(n.ctx,ast.Load):bound.add(n.id)
        if isinstance(n,ast.ImportFrom) and any(a.name=="*" for a in n.names):return set()
    return BUILTINS-bound

def shell(expr,values,allowed,methods,seen=frozenset()):
    if type(expr) in FRESH:return FRESH[type(expr)]
    if isinstance(expr,ast.IfExp):
        a=shell(expr.body,values,allowed,methods,seen);b=shell(expr.orelse,values,allowed,methods,seen)
        return a if a==b else None
    if isinstance(expr,ast.Name) and expr.id not in seen:
        sources=values.get(expr.id,())
        kinds={shell(v,values,allowed,methods,seen|{expr.id}) for v in sources}
        return next(iter(kinds)) if len(kinds)==1 and None not in kinds else None
    if isinstance(expr,ast.Call):
        fn=expr.func
        if isinstance(fn,ast.Name) and fn.id in allowed:return fn.id
        if isinstance(fn,ast.Attribute) and fn.attr=="fromkeys" and isinstance(fn.value,ast.Name) and fn.value.id=="dict" and "dict" in allowed:return "dict"
        if isinstance(fn,ast.Attribute) and not expr.args and not expr.keywords:
            if isinstance(fn.value,ast.Name) and fn.value.id=="self" and fn.attr in methods:
                return methods[fn.attr]
            if fn.attr=="copy":
                k=shell(fn.value,values,allowed,methods,seen)
                if k in {"list","dict","set"}:return k
    return None

def method_shells(ix,ch,fn_name):
    if "." not in fn_name:return {}
    owner=fn_name.rsplit(".",1)[0]
    tree=parsed_source(ch.before)
    cls=next((n for n in tree.body if isinstance(n,ast.ClassDef) and n.name==owner),None)
    if cls is None:return {}
    module=ch.path[:-3].replace("/",".")
    # Exclude dynamically replaced or overridden implementations. Missing class
    # ancestry evidence does not grant an exact-receiver proof.
    from bounds import facts
    safe=facts()["leaf"]
    methods={}
    for fn in cls.body:
        if not isinstance(fn,FN) or fn.decorator_list or (module,owner,fn.name) not in safe:continue
        vals=assignments(fn)
        allowed=unshadowed(fn,tree)
        returns=[n.value for n in ast.walk(fn) if isinstance(n,ast.Return)]
        kinds={shell(v,vals,allowed,{}) for v in returns}
        if len(kinds)==1 and None not in kinds:methods[fn.name]=kinds.pop()
    return methods

def roots(ix,ch,fn,name,fragment,shared):
    """Resolve every explicit possibly persistent write in the reachable suffix."""
    from cone import MUTATORS as other, OPERATOR_CALLS
    vals=assignments(fn)
    allowed=unshadowed(fn,parsed_source(ch.before))
    methods=method_shells(ix,ch,name)
    mask=0
    def read(target,seen=frozenset(),inner=False):
        if not inner and shell(target,vals,allowed,methods):
            return 0
        if isinstance(target,ast.Name):
            if target.id in seen:return 0
            m=shared.get(target.id,0)
            for v in vals.get(target.id,()):
                if v is not None:
                    x=read(v,seen|{target.id},inner)
                    if x is None:return None
                    m|=x
            return m
        if isinstance(target,ast.Attribute):
            base=read(target.value,seen,True)
            return None if base is None else base|shared.get(target.attr,0)
        if isinstance(target,ast.Subscript):
            return read(target.value,seen,True)
        if isinstance(target,ast.Constant):
            return shared.get(target.value,0) if type(target.value) is str else 0
        if isinstance(target,(ast.List,ast.Tuple,ast.Dict,ast.Set,ast.DictComp,ast.SetComp,ast.ListComp)):
            return None if inner else 0
        return None
    for node in ast.walk(fragment):
        targets=[]
        if isinstance(node,(ast.Global,ast.Nonlocal)):return None
        if isinstance(node,(ast.Subscript,ast.Attribute)) and isinstance(node.ctx,(ast.Store,ast.Del)):
            # Assignment to a fresh dictionary key changes the shell, not the stored element.
            targets=[node.value]
            if isinstance(node,ast.Attribute):mask|=shared.get(node.attr,0)
        if isinstance(node,ast.Call):
            f=node.func
            if isinstance(f,ast.Attribute) and f.attr in other:targets=[f.value]
            elif isinstance(f,ast.Name) and f.id in {"setattr","delattr"} or (
                isinstance(f,ast.Attribute) and isinstance(f.value,ast.Name) and f.value.id+"."+f.attr in OPERATOR_CALLS):
                return None
        for target in targets:
            m=read(target)
            if m is None:return None
            mask|=m
    return mask

def leaf_index(root):
    """Only singly defined private methods on classes never subclassed in the pin."""
    import collections
    classes=[]
    inherited=set()
    replaced=set()
    for directory in ("sqlglot","tests"):
        for file in (root/directory).rglob("*.py"):
            tree=ast.parse(file.read_bytes())
            mod=".".join(file.relative_to(root).with_suffix("").parts)
            for n in ast.walk(tree):
                if isinstance(n,ast.ClassDef):
                    for b in n.bases:
                        if isinstance(b,ast.Name):inherited.add(b.id)
                        elif isinstance(b,ast.Attribute):inherited.add(b.attr)
                    if mod.startswith("sqlglot."):classes.append((mod,n))
                if isinstance(n,ast.Attribute) and not isinstance(n.ctx,ast.Load):replaced.add(n.attr)
                if isinstance(n,ast.Constant) and type(n.value) is str and n.value.isidentifier():replaced.add(n.value)
    out=set()
    for mod,cls in classes:
        if cls.name in inherited:continue
        names=collections.Counter(n.name for n in cls.body if isinstance(n,FN))
        out.update((mod,cls.name,n) for n,num in names.items() if num==1 and n.startswith("_") and n not in replaced)
    return out
