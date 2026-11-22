"""Bound an inert table edit by the union of keyed consumers through all inherited copies."""
import ast
from frontier import same
from impact import physical_lines
from patching import compiled_source,parsed_source
from rules5 import facts,observations

FIELDS={"TRANSFORMS","PROPERTIES_LOCATION","FUNCTIONS","FUNCTION_PARSERS","NO_PAREN_FUNCTION_PARSERS"}

def bound(ix,ch):
    from regions import changed_declaration
    from declarations5 import changed_class,identifier
    from static_bounds import passive_handler
    sec=ix.section(ch.path)
    if not sec or not any(name.rsplit('.',1)[-1] in FIELDS and any(lo<=n<=hi for n in ch.removed|ch.insertions) for lo,hi,name,indent in sec.get('regions',())):return None
    decl=changed_declaration(ch,sec,physical_lines(ch.before),physical_lines(ch.after))
    if not decl:return None
    field,old,new=decl[:3];table=field.rsplit('.',1)[-1]
    if table not in FIELDS or not all(isinstance(x,ast.Dict) for x in (old,new)):return None
    change=changed_class(ch)
    if change is None:return None
    owner,a,b=change
    if owner not in facts()['ordinary_classes']:return None
    if not same([v for v in a.body if identifier(v)!=table],[v for v in b.body if identifier(v)!=table]):return None
    if any(sum(identifier(v)==table for v in cls.body)!=1 for cls in (a,b)):return None
    if (ch.path[:-3].replace('/','.'),table) in facts()['field_data']['bare']:return None
    types=facts()['expression_keys'];legal=facts()['passive'].get(ch.path[:-3].replace('/','.'),())
    def key(n):
        if isinstance(n,ast.Constant) and type(n.value) is str:return n.value
        if isinstance(n,ast.Attribute) and isinstance(n.value,ast.Name) and n.value.id=='exp' and 'exp.'+n.attr in legal:return types.get(n.attr)
        return None
    def partition(d):
        rows=[{}];barriers=[]
        for k,v in zip(d.keys,d.values):
            name=key(k)
            if name is None:
                barriers.append((ast.dump(k) if k else None,ast.dump(v)));rows.append({})
            else:
                if name in rows[-1]:return None
                rows[-1][name]=v
        return rows,barriers
    l,r=partition(old),partition(new)
    if l is None or r is None or l[1]!=r[1]:return None
    if not all(any(isinstance(t,ast.ImportFrom) and t.module=='sqlglot' and any(i.name=='exp' and i.asname is None for i in t.names) for t in tree.body) for tree in (parsed_source(ch.before),parsed_source(ch.after))):return None
    def safe(v):
        if table=='PROPERTIES_LOCATION' and isinstance(v,ast.Attribute):return ast.unparse(v) in facts()['locations']
        if table=='FUNCTIONS':
            if passive_handler(v):return True
            return isinstance(v,ast.Attribute) and v.attr=='from_arg_list' and key(v.value) in types.values()
        return False
    changed=set()
    for before,after in zip(l[0],r[0]):
        for k in before.keys()|after.keys():
            if k in before and k in after and same(before[k],after[k]):continue
            if not all(safe(side[k]) for side in (before,after) if k in side):return None
            changed.add(k)
    if not changed:return None
    keep=observations(ix,ch.path)|facts()['dispatch_opaque']|facts()['dispatch_dynamic'].get(table,0)
    rows=facts()['dispatch'];consumers=rows.get((table,None),0)
    for k in changed:consumers|=rows.get((table,k),0)
    from table_flow5 import receiver_mask
    keep|=consumers & receiver_mask(ix,owner,table)
    compiled_source(ch.after,ch.path)
    return keep
