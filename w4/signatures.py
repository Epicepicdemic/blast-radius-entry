"""Reuse the pin's TPC-DS structural signatures only when all queries and setup miss the edit."""
import ast
import importlib
import marshal
from functools import lru_cache
from pathlib import Path
from frontier import body_info,frontier,local_kinds

@lru_cache(1)
def index():
    from impact import Observations
    return Observations(Path(__file__).with_name("impact.bin"))

@lru_cache(1)
def footprints():
    return marshal.loads(Path(__file__).with_name("signature-lines.bin").read_bytes())

def unchanged(changes,hot):
    if len(changes)!=1 or not hot or len(hot)!=1:return False
    ch=changes[0]
    info=body_info(index(),ch)
    if not info or (ch.path,info[0])!=tuple(hot[0][:2]):return False
    name,_,_,a,b,start,body,end=info
    if any(isinstance(n,(ast.Lambda,ast.FunctionDef,ast.AsyncFunctionDef,ast.ClassDef,ast.Global,ast.Nonlocal))
           for fn in (a,b) for st in fn.body for n in ast.walk(st)):return False
    if local_kinds(a)!=local_kinds(b):return False
    # Any observed bit includes a row or the unnumbered setup. We do not reorder
    # rows, skip warming prefixes, or infer anything about backend execution.
    rows=footprints().get(ch.path,{})
    for lo,hi in frontier(a,b):
        if any(n in rows for n in range(start+lo-1,start+hi)):return False
    importlib.import_module(ch.path[:-3].replace("/",".").removesuffix(".__init__"))
    return True
