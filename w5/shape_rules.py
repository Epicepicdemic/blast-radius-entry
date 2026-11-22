"""Select contexts that can distinguish native map copying or an existing tokenizer key."""
import ast
from functools import lru_cache
from frontier import same
from impact import physical_lines
from patching import compiled_source,parsed_source
from rules5 import facts,observations


def map_copy(ix,ch):
    if not ch.removed or not ch.added:
        return None
    old=physical_lines(ch.before);new=physical_lines(ch.after)
    if not (any('deepcopy(' in old[i-1] for i in ch.removed) and any('deepcopy(' in new[i-1] for i in ch.added)):
        return None
    from frontier import body_info
    info=body_info(ix,ch)
    if not info:return None
    name,called,cap,a,b,start,body,end=info
    from rules5 import resolver_for
    r=resolver_for(ch.path,ch.before)
    scope=next((fn for fn,q in r.quals.items() if q==name),None)
    if scope is None or any(r.resolve(ast.Name(k,ast.Load()),scope)!=['builtin',k] for k in ('dict','type')):return None
    doc=parsed_source(ch.before)
    if not any(isinstance(n,ast.ImportFrom) and n.module=='copy' and not n.level and any(t.name=='deepcopy' and not t.asname for t in n.names) for n in doc.body):return None
    if 'deepcopy' in r.bindings(scope) or r.enclosing_binds(scope,'deepcopy'):return None
    # Match the complete two-statement implementation, including the target
    # object and the native immutable-type predicate used to skip a value.
    positions=[]
    def compare(x,y):
        if same(x,y):return True
        if isinstance(x,list) and isinstance(y,list):
            i=0
            while i<min(len(x),len(y)) and same(x[i],y[i]):i+=1
            j,k=len(x),len(y)
            while j>i and k>i and same(x[j-1],y[k-1]):j-=1;k-=1
            left,right=x[i:j],y[i:k]
            if len(left)==2 and len(right)==1 and isinstance(left[0],ast.Assign) and isinstance(left[1],ast.For) and isinstance(right[0],ast.Assign):
                alloc,loop=left;rew=right[0]
                if len(alloc.targets)!=2 or not isinstance(alloc.targets[0],ast.Name) or len(rew.targets)!=1 or not same(alloc.targets[1],rew.targets[0]):return False
                one,two=alloc.value,rew.value
                if not (isinstance(one,ast.Call) and isinstance(two,ast.Call) and isinstance(one.func,ast.Name) and one.func.id=='dict' and isinstance(two.func,ast.Name) and two.func.id=='deepcopy' and len(one.args)==1 and same(one.args,two.args) and not one.keywords and not two.keywords):return False
                if not (isinstance(loop.target,ast.Tuple) and len(loop.target.elts)==2 and all(isinstance(t,ast.Name) for t in loop.target.elts) and len(loop.body)==1 and not loop.orelse):return False
                tmp=alloc.targets[0].id;kname,vname=[v.id for v in loop.target.elts]
                cond=loop.body[0]
                if not isinstance(cond,ast.If) or cond.orelse or len(cond.body)!=1:return False
                guard=cond.test
                if not isinstance(guard,ast.Compare) or len(guard.comparators)!=1 or not isinstance(guard.comparators[0],ast.Name):return False
                types=guard.comparators[0].id
                template=ast.parse(f'for {kname}, {vname} in {tmp}.items():\n if type({vname}) not in {types}:\n  {tmp}[{kname}] = deepcopy({vname})').body[0]
                if not same(loop,template) or (ch.path,types) not in facts()['copy_atoms']:return False
                parents={v:n for n in ast.walk(b) for v in ast.iter_child_nodes(n)}
                for n in ast.walk(b):
                    if not isinstance(n,ast.Name) or not isinstance(n.ctx,ast.Load):continue
                    if n.id in ('locals','vars','eval','exec','_getframe','currentframe',tmp):return False
                    if n.id in (kname,vname):
                        cursor=n
                        while cursor in parents:
                            parent=parents[cursor]
                            if isinstance(parent,ast.For) and cursor in parent.body and any(isinstance(t,ast.Name) and t.id==n.id for t in ast.walk(parent.target)):break
                            cursor=parent
                        else:return False
                if not isinstance(rew.targets[0],ast.Attribute) or not isinstance(rew.targets[0].value,ast.Name):return False
                # Only plain slots of the pin's ordinary Expression copy loop are admitted.
                if (ch.path,name,rew.targets[0].attr) not in facts()['copy_slots']:return False
                offset=len(old[start-1])-len(old[start-1].lstrip())
                positions.append(f'{ch.path}:{start+one.lineno-1}:{offset+one.col_offset}')
                return True
            return len(left)==len(right)==1 and compare(left[0],right[0])
        if type(x) is not type(y) or not isinstance(x,ast.AST):return False
        return all(compare(getattr(x,k),getattr(y,k)) for k in x._fields)
    if not compare(a,b) or len(positions)!=1:return None
    p=positions[0];d=facts()['shape_values']
    if ('copy-read',p) not in d:return None
    from bounds import facts as inherited
    return observations(ix,ch.path,name)|facts()['passive_opaque']|d.get(('copy-opaque',p),0)|(inherited()['resources'] & d['copy-read',p])


def keyword(ix,ch):
    if not ch.removed or not ch.path.endswith('.py'):return None
    sec=ix.section(ch.path)
    if not sec or not any(v.rsplit('.',1)[-1]=='KEYWORDS' and any(lo<=n<=hi for n in ch.removed|ch.insertions) for lo,hi,v,indent in sec.get('regions',())):return None
    from regions import changed_declaration
    row=changed_declaration(ch,sec,physical_lines(ch.before),physical_lines(ch.after))
    if not row:return None
    field,a,b=row[:3]
    if field.rsplit('.',1)[-1]!='KEYWORDS' or not isinstance(a,ast.Dict) or not isinstance(b,ast.Dict):return None
    # Delete existing direct literal entries, preserving every other operand
    # and its evaluation order, including inherited dictionary expansions.
    kept=list(zip(b.keys,b.values));i=0;removed=[]
    for k,v in zip(a.keys,a.values):
        if i<len(kept) and same(k,kept[i][0]) and same(v,kept[i][1]):i+=1;continue
        if not isinstance(k,ast.Constant) or type(k.value) is not str or not isinstance(v,ast.Attribute) or not isinstance(v.value,ast.Name) or v.value.id!='TokenType':return None
        removed.append(k.value)
    if i!=len(kept) or not removed or any(k not in facts()['token_words'] for k in removed):return None
    # The same literal cannot be consumed from a table with another binding.
    if not facts()['token_scopes'].get((ch.path,field)):return None
    data=facts()['shape_values']
    if ('keyword','*') not in data and not any(r[0]=='keyword' for r in data):return None
    mask=observations(ix,ch.path)|facts()['passive_opaque']|facts()['token_dynamic']|data.get(('keyword','*'),0)
    for word in removed:mask|=data.get(('keyword',word),0)
    compiled_source(ch.after,ch.path)
    return mask
