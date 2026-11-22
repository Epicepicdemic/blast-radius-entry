"""When a pure short-circuit prefix vanishes, the old short-circuited tests can diverge."""
import ast
import marshal
from functools import lru_cache
from pathlib import Path
from frontier import body_info,same
from impact import physical_lines,disjoint_ranges
from patching import compiled_source

@lru_cache(1)
def profiles():
    return marshal.loads(Path(__file__).with_name("guards.bin").read_bytes())

def guard(ix,ch):
    if len(ch.removed)!=1 or ch.removed!=ch.added:return None
    line,=ch.removed
    if (ch.path,line) not in profiles()["sites"]:return None
    info=body_info(ix,ch)
    if not info:return None
    name,called,cap,a,b,start,body,end=info
    raw=physical_lines(ch.before)
    old=[n for n in ast.walk(a) if isinstance(n,ast.BoolOp) and n.lineno+start-1==line and len(n.values)==2]
    if not old:return None
    def pure(n):
        if isinstance(n,(ast.Name,ast.Constant)):return True
        if isinstance(n,ast.Compare):
            return len(n.ops)==1 and isinstance(n.ops[0],(ast.Is,ast.IsNot)) and all(isinstance(k,(ast.Name,ast.Constant)) for k in [n.left,*n.comparators])
        return isinstance(n,ast.BoolOp) and all(pure(x) for x in n.values)
    for expr in old:
        prefix=expr.values[0]
        if not pure(prefix):continue
        # Erasing a name load cannot suppress a NameError. Only arguments and
        # locals definitely assigned in the straight-line prefix qualify.
        safe={arg.arg for arg in [*a.args.args,*a.args.kwonlyargs,*a.args.posonlyargs]}
        for st in a.body:
            if st.end_lineno>=expr.lineno:break
            if isinstance(st,(ast.Assign,ast.AnnAssign)):
                for t in st.targets if isinstance(st,ast.Assign) else [st.target]:
                    if isinstance(t,ast.Name) and st.value is not None:safe.add(t.id)
        if any(n.id not in safe for n in ast.walk(prefix) if isinstance(n,ast.Name)):continue
        if any(isinstance(n,ast.Delete) or isinstance(n,ast.ExceptHandler) and n.name in safe for n in ast.walk(a)):continue
        # Only comparison/identity prefixes have intrinsically side-effect-free
        # truth conversion. Bare objects in boolean expressions can call __bool__.
        if any(isinstance(n,ast.Name) and not any(n is c for v in ast.walk(prefix) if isinstance(v,ast.Compare) for c in [v.left,*v.comparators]) for n in ast.walk(prefix)):continue
        class Strip(ast.NodeTransformer):
            def visit_BoolOp(self,n):
                return n.values[1] if n is expr else self.generic_visit(n)
        import copy
        # Never mutate source-cache ASTs. body_info parsed a private function.
        candidate=Strip().visit(copy.deepcopy(a, {id(expr):expr}))
        if not same(candidate,b):continue
        indent=len(raw[start-1])-len(raw[start-1].lstrip())
        facts=profiles()["sites"][(ch.path,line)].get((expr.col_offset+indent,0))
        if facts is None:continue
        from bounds import pool_facts
        section=ix.section(ch.path)
        reached=disjoint_ranges(section,[(line,line)],ix)|pool_facts()["lines"].get(ch.path,{}).get(line,0)
        allowed=facts.get("True" if isinstance(expr.op,ast.And) else "False",0)
        blocked=facts.get("False" if isinstance(expr.op,ast.And) else "True",0)|facts.get("None",0)
        affected=blocked|(reached & (profiles()["opaque"]|~allowed))
        return affected,ix.hit(section,"opens")|ix.reflect(ch.path)
    return None
