"""Structural first divergence for local annotations, docstrings and removed handlers."""
import ast
import copy

from frontier import same
from impact import disjoint_ranges,physical_lines
from patching import compiled_source,parsed_source
from rules5 import facts,observations


def local_assignments(fn):
    class Erase(ast.NodeTransformer):
        def visit_FunctionDef(self,n):return n
        def visit_AsyncFunctionDef(self,n):return n
        def visit_ClassDef(self,n):return n
        def visit_AnnAssign(self,n):
            if n.simple and isinstance(n.target,ast.Name) and n.value is not None:
                return ast.copy_location(ast.Assign(targets=[n.target],value=n.value),n)
            return n
    if not any(isinstance(n,ast.AnnAssign) for st in fn.body for n in ast.walk(st)):
        return fn
    out=copy.deepcopy(fn)
    out.body=[Erase().visit(st) for st in out.body]
    return out


def doc(ix,ch):
    if not ch.removed or len(ch.removed)>12:return None
    sec=ix.section(ch.path)
    if not sec:return None
    left,right=physical_lines(ch.before),physical_lines(ch.after)
    for name,(st,body,end,ptr) in sec.get("functions",{}).items():
        if not (body<=min(ch.removed)<=max(ch.removed)<=end):continue
        if not left[body-1].lstrip().startswith(('"""',"'''")):continue
        delim=left[body-1].lstrip()[:3]
        doc_end=body
        if delim not in left[body-1].lstrip()[3:]:
            doc_end=next((i for i in range(body+1,end+1) if delim in left[i-1]),body)
        if max(ch.removed)>doc_end:continue
        import textwrap
        delta=len(right)-len(left)
        if left[:st-1]!=right[:st-1] or left[end:]!=right[end+delta:]:continue
        def parse(src,hi):
            a=ast.parse(textwrap.dedent("\n".join(src[st-1:hi]))).body
            return a[0] if len(a)==1 and isinstance(a[0],ast.FunctionDef) else None
        a,b=parse(left,end),parse(right,end+delta)
        if (not a or not b or a.decorator_list or ast.get_docstring(a,clean=False) is None or
                ast.get_docstring(b,clean=False) is None):continue
        b.body[0]=a.body[0]
        if not same(a,b):continue
        compiled_source(ch.after,ch.path)
        from bounds import pool_facts
        mask=observations(ix,ch.path,name)|pool_facts()["unproved"]
        for field in ("__doc__","__code__","__wrapped__"):
            mask|=facts()["observers"].get((ch.path,st,field),0)
        return mask
    return None


def unfolded_handler(ix,ch):
    # With an identical unconditional return in the try body, deleting only
    # the exception translation changes execution at the handler entry.
    if not ch.removed or len(ch.removed)>16:return None
    ls=physical_lines(ch.before)
    if not any(ls[i-1].lstrip().startswith("except ") for i in ch.removed):return None
    src=parsed_source(ch.before)
    parent={child:n for n in ast.walk(src) for child in ast.iter_child_nodes(n)}
    for tr in ast.walk(src):
        if not isinstance(tr,ast.Try) or tr.lineno not in ch.removed or tr.finalbody or tr.orelse:continue
        if len(tr.body)!=1 or not isinstance(tr.body[0],ast.Return) or not tr.handlers:continue
        def pure(n):
            if isinstance(n,(ast.Name,ast.Constant)):return True
            if isinstance(n,ast.JoinedStr):return all(pure(z) for z in n.values)
            if isinstance(n,ast.FormattedValue):return pure(n.value) and n.format_spec is None
            if isinstance(n,ast.Call) and isinstance(n.func,ast.Name) and not n.keywords:
                # Pinned lexical message helpers must be a single pure f-string return.
                defs=[f for f in ast.walk(src) if isinstance(f,ast.FunctionDef) and f.name==n.func.id]
                return (len(defs)==1 and not defs[0].decorator_list and len(defs[0].body)==1 and
                    isinstance(defs[0].body[0],ast.Return) and isinstance(defs[0].body[0].value,ast.JoinedStr) and
                    all(isinstance(z,(ast.JoinedStr,ast.Constant,ast.FormattedValue,ast.Name,ast.Load))
                        for z in ast.walk(defs[0].body[0].value)) and all(pure(z) for z in n.args))
            return False
        def translation(h):
            if not isinstance(h.type,ast.Name) or h.type.id not in ("TypeError","ValueError","IndexError","KeyError") or len(h.body)!=1:return False
            n=h.body[0]
            if not isinstance(n,ast.Raise) or n.cause is not None or not isinstance(n.exc,ast.Call):return False
            f=n.exc.func
            if not isinstance(f,ast.Name) or n.exc.keywords or not all(pure(z) for z in n.exc.args):return False
            from builtins import __dict__ as bi
            k=bi.get(f.id)
            if isinstance(k,type) and issubclass(k,Exception):return True
            return facts()["imports"].get(ch.path[:-3].replace("/","."),{}).get(f.id) in facts()["exception_types"]
        if not all(translation(h) for h in tr.handlers):continue
        old=copy.deepcopy(src)
        for n in ast.walk(old):
            for key,val in ast.iter_fields(n):
                if not isinstance(val,list):continue
                for j,v in enumerate(val):
                    if isinstance(v,ast.Try) and v.lineno==tr.lineno:val[j:j+1]=v.body
        if not same(old,parsed_source(ch.after)):continue
        compiled_source(ch.after,ch.path)
        from bounds import pool_facts
        sec=ix.section(ch.path)
        points=[(h.body[0].lineno,h.body[0].end_lineno) for h in tr.handlers]
        if any(l<=n<=r for l,r in points for n in sec["order"]+sec["warm_unknown"]):return None
        workers=pool_facts()
        mask=disjoint_ranges(sec,points,ix)|observations(ix,ch.path)
        for l,r in points:
            for n in range(l,r+1):mask|=workers["lines"].get(ch.path,{}).get(n,0)
        return mask|workers["unproved"]
    return None
