"""Link a deleted private global to LOAD_GLOBAL clients, external imports and namespace observers."""
import ast
import builtins
from functools import lru_cache
from pathlib import Path
from frontier import same
from namespaces import pure
from patching import compiled_source,parsed_source
from impact import disjoint_ranges


def inert_definition(n, deferred):
    if isinstance(n,ast.FunctionDef):
        if n.decorator_list or n.type_params or n.name.startswith("__"):return None
        if not all(isinstance(x,ast.Constant) for x in [*n.args.defaults,*(x for x in n.args.kw_defaults if x)]):
            return None
        if not deferred and (n.returns or any(a.annotation for a in ast.walk(n.args) if isinstance(a,ast.arg))):
            return None
        return n.name
    if isinstance(n,(ast.Assign,ast.AnnAssign)) and pure(n.value):
        dest=n.targets[0] if isinstance(n,ast.Assign) and len(n.targets)==1 else getattr(n,"target",None)
        if isinstance(dest,ast.Name) and dest.id.isupper():return dest.id
    return None


def deleted(ch):
    if ch.added or not ch.removed:return None
    old,new=parsed_source(ch.before),parsed_source(ch.after)
    if len(old.body)!=len(new.body)+1:return None
    i=next((i for i,n in enumerate(old.body) if n.lineno<=min(ch.removed)<=n.end_lineno),None)
    if i is None:return None
    n=old.body[i]
    future=any(isinstance(v,ast.ImportFrom) and v.module=="__future__" and
               any(a.name=="annotations" for a in v.names) for v in old.body)
    name=inert_definition(n,future)
    if name and name not in vars(builtins) and same(old.body[:i]+old.body[i+1:],new.body):
        return name
    return None


def private_global(ix,ch):
    from bounds import facts
    name=deleted(ch)
    if not name:return None
    row=facts()["globals"].get((ch.path,name))
    if not row:return None
    compiled_source(ch.after,ch.path)
    return row|ix.hit(ix.section(ch.path),"opens")|ix.reflect(ch.path)


def link(ix,pin):
    # Index closed, private module names. A pin test or package file re-exporting a
    # name, a star import, or an eager lookup forfeits the lexical-only shortcut.
    from collections import defaultdict
    import dis, types
    refs=defaultdict(set)
    internal={}
    stars=set()
    observation=0
    for path in ix.meta["paths"]:
        if not path.endswith(".py") or path.startswith("@"):continue
        file=pin/path
        if not file.is_file():continue
        sec=ix.section(path)
        if "lines" not in sec:continue
        tree=ast.parse(file.read_bytes())
        mod=path[:-3].replace("/",".").removesuffix(".__init__")
        class Scan(ast.NodeVisitor):
            def visit_ImportFrom(self,n):
                if n.module:
                    for a in n.names:
                        if a.name=="*":stars.add(n.module)
                        else:refs[a.name].add(path)
            def visit_Attribute(self,n):
                refs[n.attr].add(path)
                self.generic_visit(n)
            def visit_Constant(self,n):
                if type(n.value) is str and n.value.isidentifier():refs[n.value].add(path)
        Scan().visit(tree)
        targets={name for n in tree.body if (name:=inert_definition(n,True))}
        ptrs=defaultdict(int)
        for name in targets:
            if name.startswith("_") or name.isupper():internal[(path,name)]=[mod,0]
        def visit(code,eager):
            for ins in dis.get_instructions(code):
                if ins.opname not in ("LOAD_GLOBAL","LOAD_NAME") or ins.argval not in targets:continue
                key=(path,ins.argval)
                if key not in internal:continue
                if eager or not ins.positions.lineno:
                    internal[key][1]=ix.all
                else:
                    # Use the entire containing statement line, including warm/cold
                    # fixtures. A lookup cannot fail before this point is reached.
                    l=ins.positions.lineno
                    internal[key][1]|=disjoint_ranges(sec,[(l,l)],ix)
            for c in code.co_consts:
                if isinstance(c,types.CodeType):
                    visit(c,eager and not bool(c.co_flags & 1))
        visit(compile(file.read_bytes(),str(file),"exec",dont_inherit=True),True)
    return {k:m for k,(mod,m) in internal.items()
            if m and m!=ix.all and mod not in stars and not (refs[k[1]]-{k[0]})}
