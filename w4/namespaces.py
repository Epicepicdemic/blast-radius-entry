"""Pin-derived lexical binding and import dependency bounds for removed declarations."""
import ast
from functools import lru_cache
from impact import family_path
from patching import compiled_source, parsed_source
from frontier import same


def imports(node):
    if isinstance(node,ast.Import):
        return [("import", a.name,a.asname) for a in node.names]
    if isinstance(node,ast.ImportFrom) and node.module and not node.level and node.module!="__future__":
        return [(node.module,a.name,a.asname) for a in node.names]
    return None


def pure(n):
    if isinstance(n,ast.Constant):
        return True
    if isinstance(n,(ast.Name,ast.Attribute)):
        return not (n.id if isinstance(n,ast.Name) else n.attr).startswith("__") and (
               isinstance(n,ast.Name) or pure(n.value))
    if isinstance(n,(ast.List,ast.Set,ast.Tuple)):
        return all(pure(x) for x in n.elts)
    if isinstance(n,ast.Dict):
        return all(k is not None and pure(k) and pure(v) for k,v in zip(n.keys,n.values))
    return False


def removed_names(old,new):
    def unpack(t):
        fixed=[]
        bindings=[]
        for idx,n in enumerate(t.body):
            links=imports(n)
            if links is not None and all(name!="*" for _,name,_ in links):
                for provider,name,alias in links:
                    bindings.append((len(fixed),alias or name.partition(".")[0],provider,name,alias))
            elif isinstance(n,(ast.Assign,ast.AnnAssign)):
                dest=n.targets[0] if isinstance(n,ast.Assign) and len(n.targets)==1 else getattr(n,"target",None)
                if isinstance(dest,ast.Name) and dest.id.isupper() and pure(n.value):
                    bindings.append((len(fixed),dest.id,None,ast.dump(n),None))
                else:
                    fixed.append(n)
            else:
                fixed.append(n)
        return fixed,bindings
    a,ab=unpack(old)
    b,bb=unpack(new)
    if not same(a,b):
        return None
    removed=[]
    i=0
    for link in ab:
        if i<len(bb) and bb[i]==link:
            i+=1
        else:
            removed.append(link)
    if i!=len(bb) or not removed:
        return None
    # A changed provider's own import-time effects must already be accounted for.
    # For a from-list whose last member disappears, require a guaranteed eager
    # provider (checked separately using pin metadata).
    return removed,{(r[0],r[2]) for r in bb}


def deletion_bound(ix,ch):
    if not family_path(ch.path) or ch.added and not ch.removed:
        return None
    sec=ix.section(ch.path)
    if not sec or not ch.removed or min(ch.removed)>max([n.end_lineno for n in parsed_source(ch.before).body if imports(n)] or [0]):
        return None
    old,new=parsed_source(ch.before),parsed_source(ch.after)
    delta=removed_names(old,new)
    if not delta:
        return None
    removed,stay=delta
    eager=set(ix.meta["eager"])
    for pos,name,provider,orig,alias in removed:
        if provider=="import":
            if orig not in eager and orig not in ("re","typing","sys","os"):
                return None
        elif provider and (pos,provider) not in stay and provider not in eager:
            return None
        if name.startswith("__"):
            return None
    compiled_source(ch.after,ch.path)
    # A deleted reference may fail during import/collection, including an
    # inherited class-body initializer. Keep all cold module users, observed
    # receivers and registry observers. No new executable code is admitted.
    return ix.family(ch.path)|ix.reflect(ch.path)|ix.hit(sec,"opens")
