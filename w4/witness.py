"""A complete, bounded group of first-divergence writers can discharge an unknown shared root."""
import ast
from bounds import obvious_hazard
from frontier import body_info
from state_watch import DEEP_WATCH

def candidate(ix,ch):
    info=body_info(ix,ch)
    if not info:return None
    name,called,cap,a,b,start,body,end=info
    if "." in name and name.split(".")[-1].startswith("__"):return None
    f=ix.section(ch.path)
    if any(body<=n<=end for n in f.get("warm_unknown",())):return None
    if obvious_hazard(a,b):return None
    hazards={"__dict__","__class__","__globals__","__getattribute__","__subclasses__","setattr","delattr",
             "getattr","globals","locals","exec","eval","settrace","setprofile","os","sys","random","time",
             "socket","multiprocessing","threading","builtins","inspect","pathlib","gc","atexit"}
    def exposures(fn):
        return [ast.dump(n) for n in ast.walk(fn) if isinstance(n,(ast.Global,ast.Nonlocal,ast.Import,ast.ImportFrom))
                or isinstance(n,ast.Name) and n.id in hazards or isinstance(n,ast.Attribute) and n.attr in hazards]
    if exposures(a)!=exposures(b):return None
    # An inherited/read-only first-divergence proof retains source/code readers.
    owed=ix.hit(f,"opens")|ix.reflect(ch.path)
    if not cap:return 0,owed,()
    if cap.bit_count()>8:return None
    return cap,owed,((ch.path,name,start,start),)
