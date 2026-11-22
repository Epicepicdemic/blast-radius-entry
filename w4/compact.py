"""Source readers survive ordinary comments and renames of unobserved function locals."""
import ast
import types
from functools import lru_cache
from patching import compiled_source
from impact import physical_lines

def equal_codes(a,b):
    if type(a) is not types.CodeType or type(b) is not types.CodeType:
        import marshal
        return type(a) is type(b) and marshal.dumps(a)==marshal.dumps(b)
    attrs=("co_name","co_qualname","co_code","co_argcount","co_posonlyargcount","co_kwonlyargcount",
           "co_flags","co_nlocals","co_stacksize","co_exceptiontable","co_names","co_freevars","co_cellvars")
    if any(getattr(a,v)!=getattr(b,v) for v in attrs):return False
    formals=a.co_argcount+a.co_kwonlyargcount+bool(a.co_flags&4)+bool(a.co_flags&8)
    if a.co_varnames[:formals]!=b.co_varnames[:formals]:return False
    if a.co_varnames!=b.co_varnames and ({"locals","vars","exec","eval","_getframe","currentframe","f_locals","format_map","__code__"} & set(a.co_names)):return False
    return len(a.co_consts)==len(b.co_consts) and all(equal_codes(x,y) for x,y in zip(a.co_consts,b.co_consts))

def trivia(ix,ch):
    if not ch.path.startswith("sqlglot/") or not ch.path.endswith(".py"):return None
    s=ix.section(ch.path)
    if s is None:return None
    left,right=physical_lines(ch.before),physical_lines(ch.after)
    rows=[left[i-1] for i in ch.removed]+[right[i-1] for i in ch.added]
    if not rows or not all(not row.strip() or row.lstrip().startswith("#") for row in rows):return None
    if not equal_codes(compiled_source(ch.before,ch.path),compiled_source(ch.after,ch.path)):return None
    return ix.hit(s,"opens")|ix.reflect(ch.path)

def local_rename(ix,team,ch):
    if not ch.removed or not ch.added or len(ch.removed)!=len(ch.added) or ch.removed!=ch.added:return None
    l,r=physical_lines(ch.before),physical_lines(ch.after)
    # Cheap negative test before compiling a large file. Only identifier tokens may differ.
    import re
    seen=False
    for n in ch.removed:
        a,b=l[n-1],r[n-1]
        if re.sub(r"[A-Za-z_]\w*","N",a)!=re.sub(r"[A-Za-z_]\w*","N",b):return None
        seen |= a!=b
    if not seen:return None
    a=compiled_source(ch.before,ch.path);b=compiled_source(ch.after,ch.path)
    if not equal_codes(a,b):return None
    sec=ix.section(ch.path)
    if not sec:return None
    return (ix.hit(sec,"opens")|ix.reflect(ch.path)|team.bits("attributes","f_locals")|
            team.bits("attributes","co_varnames")|team.bits("attributes","__code__"))
