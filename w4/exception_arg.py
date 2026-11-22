"""A changed scalar BaseException argument affects the newly constructed exception."""
import ast
from frontier import body_info,same
from bounds import pool_facts
from patching import compiled_source,parsed_source

def exception_bound(ix,ch):
    if len(ch.removed)!=1 or ch.removed!=ch.added:return None
    line,=ch.removed
    sec=ix.section(ch.path)
    if not sec:return None
    if not any(name.endswith(".__init__") and body<=line<=end for name,(st,body,end,ptr) in sec["functions"].items()):return None
    tree=parsed_source(ch.before)
    classes={c.name:c for c in tree.body if isinstance(c,ast.ClassDef)}
    def exception(cls,seen):
        if cls.name in seen or len(cls.bases)!=1 or not isinstance(cls.bases[0],ast.Name) or cls.decorator_list or cls.keywords:return False
        if any(isinstance(v,ast.FunctionDef) and v.name=="__new__" for v in cls.body):return False
        base=cls.bases[0].id
        if base in {"Exception","BaseException"}:
            return not any(isinstance(n,(ast.FunctionDef,ast.ClassDef)) and n.name==base or isinstance(n,ast.Name) and n.id==base and not isinstance(n.ctx,ast.Load) for n in tree.body)
        return base in classes and not any(isinstance(v,ast.FunctionDef) and v.name=="__init__" for v in classes[base].body) and exception(classes[base],seen|{cls.name})
    info=body_info(ix,ch)
    if not info:return None
    name,called,cap,a,b,st,body,end=info
    owner,_,method=name.rpartition(".")
    if method!="__init__" or owner not in classes or not exception(classes[owner],set()):return None
    if len(a.body)!=len(b.body):return None
    changes=[(x,y) for x,y in zip(a.body,b.body) if not same(x,y)]
    if len(changes)!=1:return None
    def arg(st):
        if not isinstance(st,ast.Expr) or not isinstance(st.value,ast.Call):return None
        c=st.value
        if c.keywords or len(c.args)!=1 or not isinstance(c.func,ast.Attribute) or c.func.attr!="__init__":return None
        f=c.func.value
        if not isinstance(f,ast.Call) or f.args or f.keywords or not isinstance(f.func,ast.Name) or f.func.id!="super":return None
        return c.args[0]
    old,new=map(arg,changes[0])
    params={v.arg for v in a.args.args}
    if not isinstance(old,ast.Name) or old.id not in params or not isinstance(new,ast.Constant) or type(new.value) is not str:return None
    if any(isinstance(n,(ast.Global,ast.Nonlocal)) for n in ast.walk(a)):return None
    return called|cap|ix.hit(sec,"opens")|ix.reflect(ch.path)
