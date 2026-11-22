"""Independent bounds that keep the release's shared-state and cold-reader obligations."""
import ast
import marshal
from functools import lru_cache
from pathlib import Path

from frontier import body_info, same
from impact import physical_lines
from namespaces import deletion_bound
from patching import compiled_source,parsed_source
from regions import changed_declaration


@lru_cache(1)
def facts():
    return marshal.loads(Path(__file__).with_name("slots.bin").read_bytes())


@lru_cache(1)
def pool_facts():
    return marshal.loads(Path(__file__).with_name("workers.bin").read_bytes())

def slot_bound(ix,ch,sec):
    if not ch.removed and not ch.added:
        return None
    left,right=physical_lines(ch.before),physical_lines(ch.after)
    value=changed_declaration(ch,sec,left,right)
    if not value:
        return None
    field,a,b,*_=value
    owner=ch.path[:-3].replace("/",".")+"."+field
    profile=facts()["tables"].get(owner)
    if profile is None or not isinstance(a,ast.Dict) or not isinstance(b,ast.Dict):
        return None
    short=field.rsplit(".",1)[-1]
    if short not in ("arg_types","TYPE_MAPPING","FUNCTIONS","FUNCTION_PARSERS","TRANSFORMS","PROPERTIES"):
        return None
    def key(n):
        if isinstance(n,ast.Constant) and type(n.value) is str:
            return n.value
        return None
    def entries(table):
        return [(key(k), ast.dump(k) if k else None, ast.dump(v),v) for k,v in zip(table.keys,table.values)]
    before,after=entries(a),entries(b)
    i=0
    while i<min(len(before),len(after)) and before[i][:3]==after[i][:3]:
        i+=1
    j,l=len(before),len(after)
    while j>i and l>i and before[j-1][:3]==after[l-1][:3]:
        j-=1
        l-=1
    diff=before[i:j]+after[i:l]
    keys={r[0] for r in diff}
    if not diff or None in keys:
        return None
    if short=="arg_types":
        if (not ch.path.startswith("sqlglot/expressions/") or not all(type(r[3]) is ast.Constant and
                         type(r[3].value) is bool and r[0] is not None for r in before+after)):
            return None
    else:
        # Only scalar literal values have no hidden executable or mutation effects.
        # Deferred callable changes have their own stronger release certificates.
        if not all(isinstance(r[3],ast.Constant) for r in diff):return None
    compiled_source(ch.after,ch.path)
    keep=profile.get(None,0)|facts()["opaque"]|ix.hit(sec,"opens")|ix.reflect(ch.path)
    if short=="arg_types" and [r[0] for r in before]!=[r[0] for r in after]:
        keep|=ix.bits(ix.meta["stress"])|facts()["resources"]
    for k in keys: keep|=profile.get(k,0)
    return keep


def obvious_hazard(a,b):
    # A patch may enable a different store even when its text moves inside a guard.
    unsafe={"__dict__","__class__","__globals__","__builtins__","__getattribute__","__setattr__",
            "globals","locals","getattr","setattr","delattr","vars","eval","exec","compile",
            "sys","os","builtins","subprocess","threading","open","settrace","setprofile"}
    def risks(fn):
        return [ast.dump(n) for n in ast.walk(fn) if isinstance(n,(ast.Global,ast.Nonlocal,ast.Import,ast.ImportFrom))
                or isinstance(n,ast.Name) and n.id in unsafe or isinstance(n,ast.Attribute) and n.attr in unsafe]
    return risks(a)!=risks(b)


def timing_obligation(ix,a,b):
    # A moved or introduced inner traversal can change contention and timeout
    # behavior, even for a different long-running test in another pytest worker.
    def loops(fn):
        return [(type(n).__name__,ast.dump(n.test if isinstance(n,ast.While) else n.iter))
                for n in ast.walk(fn) if isinstance(n,(ast.For,ast.While,ast.comprehension))]
    if loops(a)==loops(b):
        return 0
    return facts()["resources"]


def residue_bound(ix,team,shared,ch,info,effects):
    """A reachable opaque store widens. Ignore stores strictly before divergence
    when control cannot flow back to them. Preserve all resolved persistent roots."""
    from cone import write_targets
    name,called,cap,a,b,start,body,end=info
    if obvious_hazard(a,b):return None
    if ch.path in effects and effects[ch.path] is None:return None
    root_readers=effects.get(ch.path,0)
    if root_readers==ix.all:return None
    # Both sides' protected roots have already been resolved by the release's
    # interprocedural changed-argument guard over every edited source line.
    from flow import suffix
    for fn,other in ((a,b),(b,a)):
        fragment=suffix(fn,other)
        if fragment is None:return None
        from ownership_effects import roots
        readers=roots(ix,ch,fn,name,fragment,shared)
        if readers is None:return None
        root_readers|=readers
    return root_readers|timing_obligation(ix,a,b)


def bound(selector,ch,selected,protected,hot,writers,effects):
    ix=selector.ix
    sec=ix.section(ch.path)
    if not sec or not ch.path.startswith("sqlglot/") or not ch.path.endswith(".py"):
        return None
    points=ch.removed|ch.insertions|{n+1 for n in ch.insertions}
    if points.intersection(sec["order"]) or points.intersection(sec["warm_unknown"]):
        return None
    if not selected:return None
    from guard_bounds import guard
    g=guard(ix,ch)
    if g is not None:
        active,owed=g
        if not active:return owed,"unchanged short-circuit path",owed
        if protected!=ix.all and not writers and hot:
            return active|protected|owed,"short-circuit path",protected|owed
    if selected.bit_count()>=16:
        from compact import local_rename
        exact=local_rename(ix,selector.team,ch)
        if exact is not None and selected & ~exact:return exact,"equivalent local bytecode",exact
    if not writers and selected.bit_count()>=16:
        from delayed import sole_lookup,dead_factory,unbound_import,removed_eager
        from symbols import private_global
        for fn,why in ((removed_eager,"removed eager dependency"),(private_global,"private namespace reads"),(sole_lookup,"private method lookup"),(dead_factory,"unresolved eager table operand"),(unbound_import,"unresolved eager import")):
            result=fn(ix,ch)
            if result is not None and selected & ~result:return result,why
    if not writers:
        field=scalar_field(ix,ch,sec)
        if field is not None and selected & ~field:return field,"concrete scalar class readers"
    if selected==ix.all and not writers:
        candidate=deletion_bound(ix,ch)
        if candidate is not None and candidate!=ix.all:
            return candidate,"removed namespace binding"
        candidate=slot_bound(ix,ch,sec)
        if candidate is not None and candidate!=ix.all:
            return candidate,"concrete class-table reads"
    if writers and (ch.path in effects and effects[ch.path] is None):return None
    if not writers and protected!=ix.all and hot:
        from scalar_bounds import scalar_bound
        scalar=scalar_bound(ix,ch,sec)
        if scalar is not None:
            return scalar[0]|scalar[1]|protected, "scalar predicate divergence"
    info=body_info(ix,ch)
    if not info:return None
    name,called,cap,a,b,start,body,end=info
    if protected==ix.all or writers:
        keep=residue_bound(ix,selector.team,selector.shared,ch,info,effects)
        if keep is None:return None
        why="forward shared-store bound"
    elif hot is not None and hot:
        keep=protected
        why="two-sided control-flow frontier"
    else:
        return None
    # Relative line numbers and instructions may be read without entering a body.
    keep|=ix.hit(sec,"opens")|ix.reflect(ch.path)
    limit=keep|cap
    # This upper bound replaces a universal shared-state obligation. An ordinary
    # passing test or a row-level micro-check cannot certify that the original
    # obligation disappeared in another worker or integration schedule.
    return limit,why,limit if protected==ix.all or writers else keep


def scalar_field(ix,ch,sec):
    from impact import family_path
    if not family_path(ch.path) or len(ch.removed)!=1 or ch.removed!=ch.added:return None
    row=changed_declaration(ch,sec,physical_lines(ch.before),physical_lines(ch.after))
    if not row:return None
    field,a,b,*_=row
    mod=ch.path[:-3].replace("/",".")
    if "." not in field:return None
    key=mod+"."+field
    by_class=values()
    if key not in by_class:return None
    try:old,new=ast.literal_eval(a),ast.literal_eval(b)
    except (ValueError,TypeError):return None
    if type(old) is not type(new) or type(old) not in (bool,int,float,str):return None
    compiled_source(ch.after,ch.path)
    return by_class[key]|ix.reflect(ch.path)|ix.hit(sec,"opens")

@lru_cache(1)
def values():
    return marshal.loads(Path(__file__).with_name("class-values.bin").read_bytes())
