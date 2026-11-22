"""Validate isolated declarations with an inert prefix and an eager undefined reference."""
import ast
from functools import lru_cache
from pathlib import Path
import marshal
from frontier import same
from impact import family_path
from patching import parsed_source,compiled_source

@lru_cache(1)
def profile():
    return marshal.loads(Path(__file__).with_name("names.bin").read_bytes())

def fixed_rows(src):
    from regions import changed_declaration
    from impact import physical_lines
    return physical_lines(src)

def bindings(tree):
    names=set()
    for n in tree.body:
        if isinstance(n,(ast.FunctionDef,ast.ClassDef,ast.AsyncFunctionDef)):names.add(n.name)
        elif isinstance(n,(ast.Import,ast.ImportFrom)):
            for a in n.names:names.add(a.asname or a.name.partition(".")[0])
        elif isinstance(n,(ast.Assign,ast.AnnAssign)):
            for x in n.targets if isinstance(n,ast.Assign) else [n.target]:
                if isinstance(x,ast.Name):names.add(x.id)
    return names

def inert(n):
    return isinstance(n,ast.Constant) or isinstance(n,ast.Lambda) and not n.args.defaults and not any(n.args.kw_defaults)

def dead_factory(ix,ch):
    if not family_path(ch.path) or not ch.removed:return None
    from regions import changed_declaration
    r=changed_declaration(ch,ix.section(ch.path),fixed_rows(ch.before),fixed_rows(ch.after))
    if not r:return None
    field,a,b,*_=r
    if not isinstance(a,ast.Dict) or not isinstance(b,ast.Dict) or not same(a.keys,b.keys):return None
    changed=[(l,v) for l,v in zip(a.values,b.values) if not same(l,v)]
    if not changed:return None
    module=ch.path[:-3].replace("/",".")
    ns=profile()["modules"].get(module)
    if ns is None:return None
    import builtins
    tree=parsed_source(ch.after)
    if any(isinstance(n,ast.ImportFrom) and any(k.name=="*" for k in n.names) for n in tree.body):return None
    if any(isinstance(n,ast.Name) and n.id in {"exec","globals","locals","__builtins__","eval"} for n in ast.walk(tree)):return None
    cls_name=field.split(".")[0]
    cls=next((n for n in tree.body if isinstance(n,ast.ClassDef) and n.name==cls_name),None)
    if not cls:return None
    bound=bindings(cls)|bindings(tree)|ns|set(vars(builtins))
    def unresolved(v):
        if isinstance(v,ast.Name):return v.id not in bound
        if isinstance(v,(ast.Tuple,ast.List)):return any(unresolved(n) for n in v.elts)
        if isinstance(v,ast.Call):
            if unresolved(v.func):return True
            if not (isinstance(v.func,ast.Attribute) and isinstance(v.func.value,ast.Name) and v.func.value.id in bound):return False
            return not v.keywords and any(unresolved(n) for n in v.args) and all(isinstance(n,(ast.Name,ast.List,ast.Tuple,ast.Constant)) for n in v.args)
        return False
    if not all((inert(l) or isinstance(l,ast.Call) and isinstance(l.func,ast.Attribute) and l.func.attr=="preprocess") and unresolved(v) for l,v in changed):return None
    compiled_source(ch.after,ch.path)
    return ix.family(ch.path)|ix.hit(ix.section(ch.path),"opens")|ix.reflect(ch.path)

def unbound_import(ix,ch):
    if not family_path(ch.path) or not ch.added:return None
    a,b=parsed_source(ch.before),parsed_source(ch.after)
    if len(a.body)!=len(b.body):return None
    pairs=[(x,y) for x,y in zip(a.body,b.body) if not same(x,y)]
    if len(pairs)!=1:return None
    x,y=pairs[0]
    if not isinstance(x,ast.ImportFrom) or not isinstance(y,ast.ImportFrom) or x.module!=y.module or x.level or y.level or x.module not in profile()["modules"]:return None
    prev={(v.name,v.asname) for v in x.names}
    after={(v.name,v.asname) for v in y.names}
    new=after-prev
    if not prev<=after or not new or not all(n not in profile()["modules"][x.module] and n!="*" for n,_ in new):return None
    if x.module in profile()["dynamic_modules"] or x.module+".__init__" in profile()["modules"]:return None
    compiled_source(ch.after,ch.path)
    return ix.family(ch.path)|ix.reflect(ch.path)|ix.hit(ix.section(ch.path),"opens")

def sole_lookup(ix,ch):
    """A deleted plain method with exclusively zero-argument direct call sites."""
    if not ch.removed or ch.added or not family_path(ch.path):return None
    left,right=parsed_source(ch.before),parsed_source(ch.after)
    if len(left.body)!=len(right.body):return None
    pair=[(x,y) for x,y in zip(left.body,right.body) if not same(x,y)]
    if len(pair)!=1:return None
    a,b=pair[0]
    if not isinstance(a,ast.ClassDef) or not isinstance(b,ast.ClassDef) or not all(same(getattr(a,k),getattr(b,k)) for k in a._fields if k!="body"):return None
    new={m.name for m in b.body if isinstance(m,ast.FunctionDef)}
    removed=[m for m in a.body if isinstance(m,ast.FunctionDef) and m.name not in new]
    if not removed or not same([m for m in a.body if m not in removed],b.body):return None
    module=ch.path[:-3].replace("/",".")
    limits=profile()["methods"]
    mask=0
    for m in removed:
        k=module+"."+a.name+"."+m.name
        if k not in limits:return None
        mask|=limits[k]
    compiled_source(ch.after,ch.path)
    return mask|ix.reflect(ch.path)|ix.hit(ix.section(ch.path),"opens")

def uncalled_test_helper(ix,ch):
    if not ch.path.startswith("tests/test_") or not ch.path.endswith(".py"):return None
    from impact import physical_lines,disjoint_ranges
    sec=ix.section(ch.path)
    if not sec or not sec.get("functions") or ch.path in ix.meta.get("unknown_opens",()):return None
    if ix.hit(sec,"opens")==ix.all:return None
    left,right=physical_lines(ch.before),physical_lines(ch.after)
    delta=len(right)-len(left)
    for name,(start,body,end,ptr) in sec["functions"].items():
        if "." in name or name.startswith(("test","pytest_")):continue
        if not ch.removed or not all(body<=n<=end for n in ch.removed) or not all(body<=n<=end+delta for n in ch.added):continue
        if left[:start-1]!=right[:start-1] or left[end:]!=right[end+delta:]:continue
        a=ast.parse("\n".join(left[start-1:end])).body;b=ast.parse("\n".join(right[start-1:end+delta])).body
        if len(a)!=len(b) or len(a)!=1 or not isinstance(a[0],ast.FunctionDef) or not isinstance(b[0],ast.FunctionDef):continue
        if a[0].decorator_list or not all(same(getattr(a[0],k),getattr(b[0],k)) for k in a[0]._fields if k!="body"):continue
        if ast.get_docstring(a[0],clean=False)!=ast.get_docstring(b[0],clean=False):continue
        if any(body<=n<=end for n in sec["warm_unknown"]+sec["order"]):continue
        if ix.bits(ptr) or disjoint_ranges(sec,[(body,end)],ix):continue
        compiled_source(ch.after,ch.path)
        # Keep source readers and opaque worker clients. Body changes do not alter
        # collection names, default expressions, annotations, decorators, or fixtures.
        from bounds import facts
        return ix.hit(sec,"opens")|ix.reflect(ch.path)|facts()["pool"]
    return None

def removed_eager(ix,ch):
    """A passive declaration vanishes and an unchanged eager initializer demands it."""
    from symbols import inert_definition
    import builtins
    if not family_path(ch.path) or not ch.removed:return None
    a,b=parsed_source(ch.before),parsed_source(ch.after)
    def deferred(tree):
        return any(isinstance(n,ast.ImportFrom) and n.module=="__future__" and any(k.name=="annotations" for k in n.names) for n in tree.body)
    i=0;removed=set()
    for old in a.body:
        if i<len(b.body) and same(old,b.body[i]):i+=1;continue
        n=inert_definition(old,deferred(a))
        if not n or n in vars(builtins):return None
        removed.add(n)
    if i!=len(b.body) or not removed or removed & bindings(b):return None
    def eager(n):
        if n is None:return set()
        if isinstance(n,ast.Name):return {n.id}
        if isinstance(n,(ast.Lambda,ast.ListComp,ast.DictComp,ast.SetComp,ast.GeneratorExp,ast.IfExp,ast.BoolOp)):return set()
        if isinstance(n,(ast.Call,ast.Tuple,ast.List,ast.Set,ast.Dict,ast.Attribute,ast.Subscript,ast.keyword)):
            return set().union(*(eager(x) for x in ast.iter_child_nodes(n)))
        return set()
    def initializer(body):
        for n in body:
            if isinstance(n,ast.ClassDef):yield from initializer(n.body)
            if isinstance(n,(ast.Assign,ast.AnnAssign)):yield eager(n.value)
    if not any(removed & values for values in initializer(b.body)):return None
    compiled_source(ch.after,ch.path)
    return ix.family(ch.path)|ix.hit(ix.section(ch.path),"opens")|ix.reflect(ch.path)
