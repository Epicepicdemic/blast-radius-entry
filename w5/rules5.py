"""Pin-derived limits for delayed lookups, passive defaults, and observed operands."""
import ast
import hashlib
import json
import marshal
from functools import lru_cache
from pathlib import Path

from frontier import same
from impact import physical_lines
from patching import compiled_source, parsed_source


@lru_cache(1)
def facts():
    return marshal.loads(Path(__file__).with_name("receipts5.bin").read_bytes())


def observations(ix, path, scope=None):
    section = ix.section(path)
    indirect = ix.reflect(path, scope)
    if section and "opens" in section:
        return indirect | ix.hit(section, "opens")
    return indirect | (ix.all if path in ix.meta.get("unknown_opens", ()) else 0)


def exclusive_dispatch(ix, ch):
    from delayed import sole_lookup
    if not ch.path.startswith("sqlglot/parsers/") or ch.added or not ch.removed:
        return None
    src = physical_lines(ch.before)
    if not any(src[i-1].lstrip().startswith("def ") for i in ch.removed):
        return None
    mask = sole_lookup(ix, ch)
    if mask is None:
        return None
    tree = parsed_source(ch.before)
    deleted = [(cls, fn) for cls in tree.body if isinstance(cls, ast.ClassDef)
               for fn in cls.body if isinstance(fn, ast.FunctionDef) and fn.lineno in ch.removed]
    for cls, fn in deleted:
        ret = fn.returns
        if not (isinstance(ret, ast.Attribute) and isinstance(ret.value, ast.Name) and
                ret.value.id == "exp" and ret.attr in ("Expr", "Expression") and
                (ch.path, cls.name, fn.name) in facts()["known_methods"]):
            return None
    return mask if deleted else None


def late_import(ix, ch):
    from namespaces import deletion_bound, removed_names
    if not ch.removed or len(ch.removed) > 20:
        return None
    left = physical_lines(ch.before)
    if not any("import " in left[i-1] or left[i-1].strip().removesuffix(",").isidentifier() for i in ch.removed):
        return None
    previous = deletion_bound(ix, ch)
    if previous is None:
        return None
    removed, _ = removed_names(parsed_source(ch.before), parsed_source(ch.after))
    mask = observations(ix, ch.path)
    for _, name, provider, original, _ in removed:
        if not provider or provider == "import":
            return None
        use = facts()["names"].get((ch.path, name))
        if use is None:
            return None
        mask |= use
    return mask & previous


def dormant_test(ix, ch):
    data = facts()
    if data["digest"].get(ch.path) != hashlib.sha256(ch.before).digest():
        return None
    if not ch.removed or ch.path not in data["test_files"]:
        return None
    before, after = parsed_source(ch.before), parsed_source(ch.after)
    if len(before.body) != len(after.body):
        return None
    pairs = [(a,b) for a,b in zip(before.body,after.body) if not same(a,b)]
    if len(pairs) != 1:
        return None
    a,b = pairs[0]
    if not (isinstance(a,ast.FunctionDef) and isinstance(b,ast.FunctionDef) and not a.decorator_list
            and not a.name.startswith(("test","pytest_","__","setup","teardown")) and
            all(same(getattr(a,k),getattr(b,k)) for k in a._fields if k!="body") and
            ast.get_docstring(a,clean=False)==ast.get_docstring(b,clean=False)):
        return None
    if (ch.path,a.name,a.lineno) in data["test_entries"] or (ch.path,a.name,a.lineno) in data["pool_entries"]:
        return None
    compiled_source(ch.after,ch.path)
    from bounds import pool_facts
    # Child workers that were not observed can call test helpers independently.
    from bounds import facts as v4
    mask = ix.reflect(ch.path) | data["source_files"].get(ch.path,0) | (pool_facts()["unproved"] & ~data["entry_proved"])
    # A different collected test in the same file does not observe an unentered
    # helper unless it reads its source, frame or code object.
    for attr in ('__code__','__doc__','__annotations__','__defaults__','__kwdefaults__','__wrapped__'):
        mask |= data['observers'].get((ch.path,a.lineno,attr),0)
    return mask


def site_change(ch, kind, restore):
    """Equality of both complete modules after restoring the single changed AST node."""
    import copy
    if len(ch.removed)!=1 or ch.removed!=ch.added:
        return None
    line,=ch.removed
    a=parsed_source(ch.before)
    b=copy.deepcopy(parsed_source(ch.after))
    rows=lambda tree:[n for n in ast.walk(tree) if isinstance(n,kind) and n.lineno==line]
    old,new=rows(a),rows(b)
    if len(old)!=len(new):
        return None
    diff=[(x,y) for x,y in zip(old,new) if not same(x,y)]
    if len(diff)!=1:
        return None
    x,y=diff[0]
    data=restore(x,y)
    if data is None or not same(a,b):
        return None
    compiled_source(ch.after,ch.path)
    return x,data


def enum_bound(ix,ch):
    line,=ch.removed
    sites=facts()["comparisons"].get((ch.path,line))
    if not sites:
        return None
    def restore(x,y):
        if len(x.ops)!=1 or len(y.ops)!=1 or {type(x.ops[0]),type(y.ops[0])}!={ast.Is,ast.Eq}:
            return None
        y.ops=x.ops
        return True
    pair=site_change(ch,ast.Compare,restore)
    if not pair:return None
    x,_=pair
    row=sites.get(x.col_offset)
    if not row:return None
    possible=row.get("True",0)|row.get("None",0)
    sec=ix.section(ch.path)
    from bounds import pool_facts
    from impact import disjoint_ranges
    reached=disjoint_ranges(sec,[(line,line)],ix)
    accounted=0
    for mask in row.values():accounted|=mask
    possible|=reached&~accounted
    possible|=pool_facts()["lines"].get(ch.path,{}).get(line,0) & ~facts()["worker_proved"]
    possible|=facts()["opaque"] & reached & ~facts()["worker_proved"]
    return observations(ix,ch.path) if not possible else None


def callback_default(ix,ch):
    line,=ch.removed
    sites=facts()["callbacks"].get((ch.path,line))
    if not sites:return None
    def restore(x,y):
        ds=x.args.defaults
        es=y.args.defaults
        if (not ds or len(ds)!=len(es) or x.args.posonlyargs or x.args.kwonlyargs or x.args.vararg or x.args.kwarg or
            not all(isinstance(z,ast.Constant) and type(z.value) in (str,type(None)) for z in ds+es)):
            return None
        if not (isinstance(x.body,ast.Call) and isinstance(x.body.func,ast.Attribute) and
                isinstance(x.body.func.value,ast.Name) and x.body.func.attr in ("strip","lstrip","rstrip") and
                len(x.body.args)==1 and isinstance(x.body.args[0],ast.Name) and not x.body.keywords):
            return None
        result=[z.value for z in es]
        y.args.defaults=x.args.defaults
        return result
    pair=site_change(ch,ast.Lambda,restore)
    if not pair:return None
    x,defaults=pair
    par={n:t for t in ast.walk(parsed_source(ch.before)) for n in ast.iter_child_nodes(t)}
    call=par[x]
    if (not isinstance(call,ast.Call) or not isinstance(call.func,ast.Name) or
        call.func.id!="null_if_any" or call.args!=[x] or call.keywords or
        not isinstance(par.get(call),ast.Dict) or ch.path!="sqlglot/executor/env.py"):
        return None
    row=sites.get(x.col_offset)
    if not row:return None
    names=[a.arg for a in x.args.args]
    def resolve(raw, ds):
        pos,kw=json.loads(raw)
        if len(pos)>len(names):raise ValueError()
        bind=dict(zip(names[-len(ds):],ds))
        bind.update(zip(names,pos))
        for k,v in kw:
            if k not in names or k in names[:len(pos)]:raise ValueError()
            bind[k]=v
        value=bind[x.body.func.value.id]
        chars=bind[x.body.args[0].id]
        if type(value) is not str or type(chars) not in (str,type(None)):raise ValueError()
        return getattr(str,x.body.func.attr)(value,chars)
    keep=observations(ix,ch.path)
    for field in ("__defaults__","__kwdefaults__","__wrapped__","__code__","__signature__"):
        keep|=facts()["observers"].get((ch.path,line,field),0)
    for key,mask in row.items():
        try:different=resolve(key,[d.value for d in x.args.defaults])!=resolve(key,defaults)
        except (TypeError,ValueError,KeyError):different=True
        if different:keep|=mask
    # Process workers do not inherit the collector. Keep all opaque worker
    # clients whose pin code executed this backend, including deferred callbacks.
    sec=ix.section(ch.path)
    from bounds import pool_facts
    workers=pool_facts()
    keep|=workers["lines"].get(ch.path,{}).get(line,0) | workers["unproved"]
    keep|=facts()["opaque"] & facts()["callback_exposure"].get((ch.path,line),ix.all)
    return keep


def early(ix,ch):
    if ch.path.startswith("tests/test_") and ch.path.endswith(".py"):
        value=dormant_test(ix,ch)
        return None if value is None else (value,"unentered test helper")
    if not ch.path.startswith("sqlglot/") or not ch.path.endswith(".py"):return None
    sec=ix.section(ch.path)
    if not sec or hashlib.sha256(ch.before).digest()!=sec["digest"]:return None
    if len(ch.removed)==1 and ch.removed==ch.added:
        line,=ch.removed
        text=physical_lines(ch.before)[line-1]
        if "lambda" in text:
            value=callback_default(ix,ch)
            if value is not None:return value,"passive callback defaults"
        if " == " in text or " is " in text:
            value=enum_bound(ix,ch)
            if value is not None:
                from value_bounds import compare_site
                row=compare_site(ix,sec,ch,physical_lines(ch.before),physical_lines(ch.after)) if sec.get("domains") else None
                if row is not None and not row[0]:value &= observations(ix,ch.path,row[1])
                return value,"observed enum comparison"
    from shape_rules import keyword, map_copy
    for proof,reason in ((keyword,'observed tokenizer key reads'),(map_copy,'native dictionary copy equivalence')):
        mask=proof(ix,ch)
        if mask is not None:return mask,reason
    from compiled5 import annotation
    if ch.path.endswith(".py") and min(ch.removed or {0})>0 and len(ch.removed)+len(ch.added)<=28:
        v=annotation(ix,ch)
        if v is not None:return v,"identical executable code"
    from front5 import doc,unfolded_handler
    changed=ch.removed
    if changed and len(changed)<=16:
        ls=physical_lines(ch.before)
        if any("except " in ls[i-1] for i in changed):
            value=unfolded_handler(ix,ch)
            if value is not None:return value,"exception translation reach"
        if any(not ls[i-1].lstrip().startswith(("def ","if ","return ","self.","class ","import ","from ")) for i in changed):
            value=doc(ix,ch)
            if value is not None:return value,"function documentation observers"
    from forwarding5 import bound as forwarded
    value=forwarded(ix,ch)
    if value is not None:return value,"equivalent superclass argument forwarding"
    from dispatch5 import bound as keyed
    value=keyed(ix,ch)
    if value is not None:return value,"keyed dispatch consumers"
    value=exclusive_dispatch(ix,ch)
    if value is not None:return value,"fixed function-parser dispatch"
    from declarations5 import class_bound
    value=class_bound(ix,ch)
    if value is not None:
        from bounds import scalar_field
        from impact import classify,family_path
        if family_path(ch.path):
            scalar=scalar_field(ix,ch,sec)
            if scalar is not None:
                # The existing two-stage route intersects the scalar profile with
                # lineage, table aliases, and refined module scope.
                return None
        return value,"concrete class declaration observers"
    value=late_import(ix,ch)
    if value is not None:return value,"deferred import use sites"
    return None

@lru_cache(1)
def census_index():
    import json
    from census import Census
    return Census.load(Path(__file__).with_name("census.json"))

@lru_cache(3)
def resolver_for(path,source):
    from mutation_summaries import module_name
    return census_index().resolver(module_name(path),path,parsed_source(source))
