"""Require identical executable code for annotation-only changes in a function."""
import ast,types
from patching import compiled_source
from impact import physical_lines
from rules5 import observations

def same_code(x,y):
    if type(x) is not type(y):return False
    if type(x) is not types.CodeType:
        import marshal
        return marshal.dumps(x,2)==marshal.dumps(y,2)
    fields=("co_name","co_qualname","co_code","co_argcount","co_posonlyargcount","co_kwonlyargcount",
            "co_flags","co_nlocals","co_stacksize","co_exceptiontable","co_names","co_varnames","co_freevars","co_cellvars")
    return all(getattr(x,k)==getattr(y,k) for k in fields) and len(x.co_consts)==len(y.co_consts) and all(same_code(a,b) for a,b in zip(x.co_consts,y.co_consts))
def annotation(ix,ch):
    if not ch.removed or not ch.added:return None
    lines=physical_lines(ch.before)
    if not any(":" in lines[n-1] and ("[" in lines[n-1] or "=" in lines[n-1]) for n in ch.removed):return None
    if not same_code(compiled_source(ch.before,ch.path),compiled_source(ch.after,ch.path)):return None
    return observations(ix,ch.path)
