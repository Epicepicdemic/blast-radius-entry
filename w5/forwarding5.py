"""Recognize an ordinary subclass forwarding its parent's exact argument contract."""
import ast
from frontier import same
from patching import parsed_source,compiled_source
from rules5 import facts,observations


def bound(ix,ch):
    from impact import physical_lines
    if not ch.removed or not ch.added:return None
    text=physical_lines(ch.after)
    if not any('**' in text[i-1] and '*' in text[i-1] for i in ch.added):return None
    from declarations5 import changed_class
    pair=changed_class(ch)
    if not pair:return None
    q,old,new=pair
    different=[(a,b) for a,b in zip(old.body,new.body) if not same(a,b)]
    if len(old.body)!=len(new.body) or len(different)!=1:return None
    a,b=different[0]
    if not isinstance(a,ast.FunctionDef) or not isinstance(b,ast.FunctionDef) or a.name!=b.name or a.name!='__init__' or a.decorator_list or b.decorator_list:return None
    if a.args.vararg or a.args.kwarg or a.args.posonlyargs or a.args.kwonlyargs or not a.args.args:return None
    if len(b.args.args)!=1 or b.args.posonlyargs or b.args.kwonlyargs or b.args.defaults or not b.args.vararg or not b.args.kwarg:return None
    if a.args.args[0].arg!=b.args.args[0].arg or not same(a.body[1:],b.body[1:]):return None
    if not a.body or not b.body:return None
    def delegation(st):
        if not isinstance(st,ast.Expr) or not isinstance(st.value,ast.Call):return None
        c=st.value;f=c.func
        return c if isinstance(f,ast.Attribute) and f.attr==a.name and isinstance(f.value,ast.Call) and isinstance(f.value.func,ast.Name) and f.value.func.id=='super' and not f.value.args and not f.value.keywords else None
    x,y=delegation(a.body[0]),delegation(b.body[0]);params=[v.arg for v in a.args.args[1:]]
    if not x or not y or x.args or [k.arg for k in x.keywords]!=params or not all(isinstance(k.value,ast.Name) and k.value.id==k.arg for k in x.keywords):return None
    if len(y.args)!=1 or not isinstance(y.args[0],ast.Starred) or not isinstance(y.args[0].value,ast.Name) or y.args[0].value.id!=b.args.vararg.arg:return None
    if len(y.keywords)!=1 or y.keywords[0].arg is not None or not isinstance(y.keywords[0].value,ast.Name) or y.keywords[0].value.id!=b.args.kwarg.arg:return None
    if any(isinstance(n,ast.Name) and n.id in set(params)|{b.args.vararg.arg,b.args.kwarg.arg,'locals','vars','eval','exec','super'} for st in a.body[1:] for n in ast.walk(st)):return None
    # Every observed MRO has the same immediate callee, and its scalar/enum
    # defaults agree by identity. Invalid calls and signature observers remain owed.
    if facts()['forward'].get(q)!=ast.dump(a.args):return None
    compiled_source(ch.after,ch.path)
    data=facts();m=observations(ix,ch.path)|data['field_data']['dynamic'].get((q,'__init__'),0)|data['field_data']['dynamic'].get((q,'*'),0)
    for key in ('__defaults__','__signature__','__code__','__kwdefaults__','__annotations__','__doc__'):
        m|=data['observers'].get((ch.path,a.lineno,key),0)
    # The binding of bad argument lists can change TypeError provenance. All
    # clients that exercise exceptional argument binding stay in the plan.
    errors=data['forward_exceptions']
    if not isinstance(errors,dict):return m|errors
    return m|errors.get('*',0)|errors.get(q.rpartition('.')[2]+'.__init__',0)
