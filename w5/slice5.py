"""Refine first divergence inside matched boolean prefixes and erased local bookkeeping."""
import ast
from functools import lru_cache
from frontier import same
from impact import disjoint_ranges,physical_lines
from rules5 import facts


def index_profile(ix,ch,st,end):
    sec=ix.section(ch.path);data=facts();p=ch.path
    from bounds import pool_facts
    w=pool_facts();lines=w['lines'].get(p,{})
    def reached(ln):
        if ln in sec['warm_unknown'] or ln in sec['order']:return ix.all
        return disjoint_ranges(sec,[(ln,ln)],ix)|lines.get(ln,0)
    offset=len(physical_lines(ch.before)[st-1])-len(physical_lines(ch.before)[st-1].lstrip())
    def point(n,kind=None):
        ln=st+n.lineno-1;col=offset+n.col_offset
        return (p,ln,col,kind) if kind is not None else (p,ln,col)
    return reached,point,w['unproved']

def common_conditions(ix,ch,info):
    name,called,cap,a,b,st,body,end=info;data=facts();signals=data['prefixes'];reached,point,unknown=index_profile(ix,ch,st,end)
    def prefix(x,y):
        if not (isinstance(x,ast.BoolOp) and isinstance(y,ast.BoolOp) and type(x.op) is type(y.op)):
            return None
        n=0
        while n<min(len(x.values),len(y.values)) and same(x.values[n],y.values[n]):n+=1
        if not n or n==len(x.values)==len(y.values):return None
        # A receipt for the differing operand is absent if that operand raises.
        # Instead use the last common operand, just before its truth test.
        row=signals.get(point(x,'bool'+str(n-1)))
        if not row:return None
        onward='yes' if isinstance(x.op,ast.And) else 'no'
        result=(unknown | data['prefix_opaque']) & called
        for kind,mask in row.items():
            if kind in (onward,'object'):result|=mask
        return result
    def locate(x,y):
        if same(x,y):return 0
        if isinstance(x,list) and isinstance(y,list) and len(x)==len(y):
            pairs=[(l,r) for l,r in zip(x,y) if not same(l,r)]
            if len(pairs)==1:return locate(*pairs[0])
        if type(x) is not type(y) or not isinstance(x,ast.AST):return None
        if isinstance(x,ast.BoolOp):
            m=prefix(x,y)
            if m is not None:return m
        if isinstance(x,ast.If) and isinstance(x.test,ast.BoolOp):
            off_same=same(x.orelse,y.orelse) if isinstance(x.test.op,ast.And) else same(x.body,y.body)
            if off_same:
                m=prefix(x.test,y.test)
                if m is not None:return m
        fields=[k for k in x._fields if not same(getattr(x,k),getattr(y,k))]
        if len(fields)==1:return locate(getattr(x,fields[0]),getattr(y,fields[0]))
        return None
    if any(isinstance(n,ast.NamedExpr) for fn in (a,b) for st in fn.body for n in ast.walk(st)):
        from nested5 import codes,lexical
        left,right=codes(a),codes(b)
        if lexical(left)!=lexical(right) or set(left.co_varnames)!=set(right.co_varnames):return None
    return locate(a.body,b.body)


def optional_argument(ix,ch,info):
    name,called,cap,a,b,start,body,end=info
    # A dropped argument to an ordinary bound method has an effect only where
    # its sole guarded consumer entered its non-default arm. The call and all
    # other argument evaluations must be identical.
    if ch.path!='sqlglot/parser.py' or not ch.removed or len(ch.removed)>3:return None
    import copy
    pairs=[]
    def compare(x,y):
        if same(x,y):return True
        if type(x) is not type(y):return False
        if isinstance(x,(list,tuple)):return len(x)==len(y) and all(compare(l,r) for l,r in zip(x,y))
        if not isinstance(x,ast.AST):return False
        if isinstance(x,ast.Call) and isinstance(x.func,ast.Attribute) and x.func.attr=='_match' and isinstance(x.func.value,ast.Name) and x.func.value.id=='self' and same(x.func,y.func) and same(x.args,y.args):
            extras=[v for v in x.keywords if v.arg=='expression']
            if len(extras)==1 and same([v for v in x.keywords if v not in extras],y.keywords):
                v=extras[0].value
                if isinstance(v,ast.IfExp) and isinstance(v.body,ast.Name) and isinstance(v.orelse,ast.Constant) and v.orelse.value is None and isinstance(v.test,ast.Call) and isinstance(v.test.func,ast.Name) and v.test.func.id=='isinstance' and len(v.test.args)==2 and not v.test.keywords and same(v.test.args[0],v.body) and ast.unparse(v.test.args[1]) in ('exp.Expr','exp.Expression'):
                    pairs.append(x);return True
        return all(compare(getattr(x,k),getattr(y,k)) for k in x._fields)
    if not compare(a,b) or len(pairs)!=1 or not facts()['parser_comment_contract']:return None
    reached,point,unknown=index_profile(ix,ch,start,end);sec=ix.section(ch.path)
    # All actual executions of the consumer's observable arm are included,
    # across unrelated call sites and every concrete dialect implementation.
    lo,hi=facts()['parser_comment_contract'];m=0
    for line in range(lo,hi+1):m|=reached(line)
    return cap & (m|unknown)


def erased(ix,ch,info):
    name,called,cap,a,b,start,body,end=info
    data=facts();observed=data.get('passive_ops');sites=data.get('passive_sites')
    if observed is None or sites is None:return None
    if any(isinstance(n,(ast.Global,ast.Nonlocal,ast.Yield,ast.YieldFrom)) or isinstance(n,ast.Name) and n.id in ('locals','vars','eval','exec','_getframe','currentframe') for fn in (a,b) for s in fn.body for n in ast.walk(s)):return None
    reached,point,unknown=index_profile(ix,ch,start,end);rest=set();removed=[]
    def locate(x,y):
        if same(x,y):return True
        if isinstance(x,list) and isinstance(y,list):
            i=0
            while i<min(len(x),len(y)) and same(x[i],y[i]):i+=1
            j=len(x);k=len(y)
            while j>i and k>i and same(x[j-1],y[k-1]):j-=1;k-=1
            l,r=x[i:j],y[i:k]
            if not r and l and all(isinstance(s,ast.stmt) for s in l):removed.extend(l);return True
            if len(l)>=2 and len(r)==1 and isinstance(r[0],ast.Return) and isinstance(l[0],ast.Assign) and len(l[0].targets)==1 and isinstance(l[0].targets[0],ast.Name) and isinstance(l[-1],ast.Return) and same(l[-1].value,ast.Name(l[0].targets[0].id,ast.Load())) and same(l[0].value,r[0].value):
                removed.extend(l[1:-1]);rest.add(l[0].targets[0].id);return True
            return len(l)==len(r)==1 and locate(l[0],r[0])
        if type(x) is not type(y) or not isinstance(x,ast.AST):return False
        fs=[k for k in x._fields if not same(getattr(x,k),getattr(y,k))]
        return len(fs)==1 and locate(getattr(x,fs[0]),getattr(y,fs[0]))
    if not locate(a.body,b.body) or not removed:return None
    killed={id(n) for s in removed for n in ast.walk(s)}
    used={n.id for n in ast.walk(a) if id(n) not in killed and isinstance(n,ast.Name) and isinstance(n.ctx,ast.Load)}|rest
    mask=(unknown|data['passive_opaque'])&called
    def bad(n):
        nonlocal mask
        for ln in range(start+n.lineno-1,start+n.end_lineno):mask|=observed.get((ch.path,ln,'error'),0)
    def pure(n):
        nonlocal mask
        if n is None:return True
        if isinstance(n,(ast.Load,ast.Store,ast.Name,ast.Constant,ast.Slice,ast.List,ast.Tuple,ast.Set,ast.Not,ast.And,ast.Or,ast.Is,ast.IsNot,ast.Eq,ast.NotEq,ast.In,ast.NotIn,ast.Lt,ast.LtE,ast.Gt,ast.GtE,ast.USub,ast.UAdd)):
            # Construction of a set can hash user-defined objects.
            if isinstance(n,ast.Set) and not all(isinstance(v,ast.Constant) for v in n.elts):return False
        elif isinstance(n,ast.UnaryOp):
            if not (isinstance(n.op,(ast.UAdd,ast.USub)) and isinstance(n.operand,ast.Constant) and type(n.operand.value) in (int,float)):return False
        elif isinstance(n,ast.comprehension):
            if n.is_async or n.ifs or not isinstance(n.target,ast.Name):return False
        elif isinstance(n,(ast.Attribute,ast.Subscript,ast.BoolOp,ast.Compare,ast.Call,ast.ListComp)):
            if point(n) not in sites:return False
            if isinstance(n,ast.Call) and not (isinstance(n.func,ast.Name) and n.func.id=='len' and len(n.args)==1 and not n.keywords and facts()['builtin_len'].get(ch.path)):return False
            if isinstance(n,ast.Compare) and len(n.ops)!=1:return False
            mask|=observed.get(point(n),0)
            if isinstance(n,ast.ListComp):
                for gen in n.generators:mask|=observed.get(point(gen.iter),0)
        else:return False
        return all(pure(v) for v in ast.iter_child_nodes(n))
    def visit(n):
        nonlocal mask
        if isinstance(n,ast.If) and point(n.test) in sites and pure(n.test):
            mask|=observed.get(point(n),0);bad(n.test)
            for s in [*n.body,*n.orelse]:visit(s)
        elif isinstance(n,(ast.Assign,ast.AnnAssign)) and all(isinstance(t,ast.Name) and t.id not in used for t in (n.targets if isinstance(n,ast.Assign) else [n.target])) and pure(n.value):bad(n)
        else:
            for ln in range(start+n.lineno-1,start+n.end_lineno):mask|=reached(ln)
    for st in removed:visit(st)
    return cap&mask

def refine(ix,ch,info):
    if not info:return info
    cap=info[2]
    for fn in (common_conditions,optional_argument,erased):
        m=fn(ix,ch,info)
        if m is not None:cap &= m
    return info[:2]+(cap,)+info[3:]
