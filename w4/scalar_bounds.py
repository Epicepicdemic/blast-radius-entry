"""Compare a changed predicate only on exact builtin operands observed on the pin."""
import ast
import marshal
import operator
import textwrap
from functools import lru_cache
from pathlib import Path
from impact import physical_lines
from patching import compiled_source
from frontier import same

OPS={ast.Eq:operator.eq,ast.NotEq:operator.ne,ast.Lt:operator.lt,ast.LtE:operator.le,
     ast.Gt:operator.gt,ast.GtE:operator.ge,ast.Is:operator.is_,ast.IsNot:operator.is_not}

@lru_cache(1)
def facts():
    return marshal.loads(Path(__file__).with_name("scalars.bin").read_bytes())

def scalar_bound(ix,ch,section):
    if len(ch.removed)!=1 or ch.added!=ch.removed or ch.insertions:
        return None
    line,=ch.removed
    sites=facts()["sites"].get((ch.path,line))
    if not sites:return None
    left,right=physical_lines(ch.before),physical_lines(ch.after)
    for name,(start,body,end,ptr) in section["functions"].items():
        if not body<=line<=end:continue
        def parse(lines):
            part=textwrap.dedent("\n".join(lines[start-1:end]))
            return ast.parse(part),len(lines[line-1].encode())-len(part.split("\n")[line-start].encode())
        a,indent=parse(left)
        b,other=parse(right)
        if indent!=other:return None
        l=[n for n in ast.walk(a) if isinstance(n,ast.Compare)]
        r=[n for n in ast.walk(b) if isinstance(n,ast.Compare)]
        if len(l)!=len(r):return None
        delta=[(x,y) for x,y in zip(l,r) if not same(x,y)]
        if len(delta)!=1:return None
        x,y=delta[0]
        if not (x.lineno==x.end_lineno==y.lineno==y.end_lineno==line-start+1 and len(x.ops)==len(y.ops)==1
                and type(x.ops[0]) in OPS and type(y.ops[0]) in OPS and same(x.left,y.left)
                and isinstance(x.comparators[0],ast.Constant) and isinstance(y.comparators[0],ast.Constant)):
            return None
        old,new=x.comparators[0].value,y.comparators[0].value
        if type(old) not in (bool,str,int,type(None)) or type(new) not in (bool,str,int,type(None)):return None
        if any(isinstance(op,(ast.Is,ast.IsNot)) and not (v is None or type(v) is bool)
               for op,v in ((x.ops[0],old),(y.ops[0],new))):return None
        oldop,newop=OPS[type(x.ops[0])],OPS[type(y.ops[0])]
        y.ops,y.comparators=x.ops,x.comparators
        if not same(a,b):return None
        data=sites.get(x.col_offset+indent)
        if not data:return None
        # A whole cold/worker path missing from the scalar trace is still owed.
        reached=0
        for tab in ("lines","cold_lines"):
            p=section[tab].get(line)
            if p is not None:reached|=ix.bits(p)
        from bounds import pool_facts
        workers=pool_facts()
        reached|=workers["lines"].get(ch.path,{}).get(line,0)
        observed=diverged=0
        for tag,v,mask in data:
            observed|=mask
            try:
                different=tag=="?" or oldop(v,old)!=newop(v,new)
            except (TypeError,ValueError):different=True
            if different:diverged|=mask
        unknown=facts()["opaque"]
        compiled_source(ch.after,ch.path)
        return (diverged | reached & (unknown|~observed),ix.hit(section,"opens")|ix.reflect(ch.path,name))
    return None
