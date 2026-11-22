"""Fast conservative prices for changes to individually indexed declarations."""
import ast
import textwrap
from functools import lru_cache

FN=(ast.FunctionDef,ast.AsyncFunctionDef)

def pin_regions(tree, module, factories):
    """Record only statements whose unchanged file surroundings delimit their scope."""
    rows=[]
    imports={}
    for n in tree.body:
        if isinstance(n,ast.ImportFrom) and n.level==0 and n.module:
            for a in n.names:
                q=n.module+"."+a.name
                if q in factories: imports[a.asname or a.name]=q
        if isinstance(n,ast.FunctionDef) and module+"."+n.name in factories:
            imports[n.name]=module+"."+n.name
    def visit(body,owner):
        counts={}
        for n in body:
            target=n.targets[0] if isinstance(n,ast.Assign) and len(n.targets)==1 else getattr(n,"target",None)
            if isinstance(target,ast.Name):counts[target.id]=counts.get(target.id,0)+1
        for n in body:
            if isinstance(n,ast.ClassDef):
                visit(n.body,owner+n.name+".")
            elif isinstance(n,(ast.Assign,ast.AnnAssign)):
                target=n.targets[0] if isinstance(n,ast.Assign) and len(n.targets)==1 else getattr(n,"target",None)
                if isinstance(target,ast.Name) and counts[target.id]==1 and n.value is not None:
                    rows.append((n.lineno,n.end_lineno,owner+target.id,n.col_offset))
    visit(tree.body,"")
    return rows,imports

@lru_cache(maxsize=256)
def declaration(fragment):
    nodes=ast.parse(textwrap.dedent(fragment),type_comments=True).body
    if len(nodes)!=1:return None
    n=nodes[0]
    target=n.targets[0] if isinstance(n,ast.Assign) and len(n.targets)==1 else getattr(n,"target",None)
    if not isinstance(target,ast.Name) or not isinstance(n,(ast.Assign,ast.AnnAssign)):
        return None
    signature=(type(n),target.id,ast.dump(n.annotation) if isinstance(n,ast.AnnAssign) else n.type_comment)
    return signature,n.value

def changed_declaration(ch,f,left,right):
    """The admitted fragment has exactly one assignment on each side, at identical indentation."""
    if not ch.removed and not ch.insertions:return None
    lo=min(ch.removed or ch.insertions)
    hi=max(ch.removed or ch.insertions)
    shift=len(right)-len(left)
    for start,end,name,indent in f.get("regions",()):
        if not start<=lo<=hi<=end or any(n<start-1 or n>end for n in ch.insertions):continue
        if any(n<start or n>end+shift for n in ch.added):continue
        if start-1>=len(right) or end+shift<start:continue
        if left[start-1][:indent]!=right[start-1][:indent]:continue
        if len(right[start-1])-len(right[start-1].lstrip())!=indent:continue
        old=declaration("\n".join(left[start-1:end]))
        new=declaration("\n".join(right[start-1:end+shift]))
        if not old or not new or old[0]!=new[0]:continue
        if ast.dump(old[1])==ast.dump(new[1]):continue
        return name,old[1],new[1],start,indent
    return None

def read_expression(n):
    if isinstance(n,ast.Constant):return True
    if isinstance(n,ast.Name):return not n.id.startswith("__")
    if isinstance(n,ast.Attribute):return not n.attr.startswith("__") and read_expression(n.value)
    if isinstance(n,(ast.Set,ast.List,ast.Tuple)):return all(read_expression(x) for x in n.elts)
    if isinstance(n,ast.UnaryOp):return isinstance(n.op,(ast.UAdd,ast.USub)) and read_expression(n.operand)
    return False

def passive_entry(n,factories):
    if read_expression(n):return True
    if isinstance(n,ast.Lambda):
        if n.args.defaults or any(n.args.kw_defaults):return False
        # Keep unknown effects on the guarded route. SQL renderers ordinarily return
        # literals, formatted fragments, or compose the existing generator API.
        for x in ast.walk(n.body):
            if isinstance(x,(ast.NamedExpr,ast.Yield,ast.YieldFrom,ast.Await)):return False
            if isinstance(x,ast.Call) and not (isinstance(x.func,ast.Attribute)
                    and x.func.attr in ("sql","func","expression","cast","var","string","number")
                    and read_expression(x.func.value)):return False
            if isinstance(x,ast.Attribute) and x.attr.startswith("__"):return False
        return True
    if isinstance(n,ast.Call) and isinstance(n.func,ast.Name) and n.func.id in factories:
        return all(read_expression(x) for x in n.args) and all(k.arg and read_expression(k.value) for k in n.keywords)
    return False

def passive_dict(a,b,factories):
    if not isinstance(a,ast.Dict) or not isinstance(b,ast.Dict):return False
    def entries(d):
        return [(ast.dump(k) if k else None,ast.dump(v),k,v) for k,v in zip(d.keys,d.values)]
    x,y=entries(a),entries(b)
    head=0
    while head<min(len(x),len(y)) and x[head][:2]==y[head][:2]:head+=1
    x,y=x[head:],y[head:]
    while x and y and x[-1][:2]==y[-1][:2]:
        x.pop();y.pop()
    return bool(x or y) and all(k is not None and read_expression(k) and passive_entry(v,factories)
                                for _,_,k,v in x+y)

def passive_deletion(ch,section,lines):
    if ch.added or not ch.removed:return None
    # Deleting a complete existing binding plus surrounding blank lines preserves
    # the enclosing suite. The caller checks that the new module still compiles.
    nonblank={n for n in ch.removed if lines[n-1].strip()}
    if not nonblank:return None
    for start,end,name,indent in section.get("regions",()):
        if start!=min(nonblank) or end!=max(nonblank):continue
        if any(n not in ch.removed and lines[n-1].strip() for n in range(start,end+1)):continue
        old=declaration("\n".join(lines[start-1:end]))
        if not old:return None
        value=old[1]
        if read_expression(value) or (isinstance(value,ast.Dict) and
                all(k is not None and read_expression(k) and read_expression(v) for k,v in zip(value.keys,value.values))):
            return name
    return None

def fallback(index,ch,section,left,right):
    """Bound a change confined to a passive binding. Unknown eager evaluation widens."""
    from impact import family_path, key_receipt
    from patching import compiled_source
    family=family_path(ch.path)
    deletion=passive_deletion(ch,section,left)
    if deletion and (family or ("." not in deletion and deletion.isupper())):
        compiled_source(ch.after,ch.path)
        field=deletion.rsplit(".",1)[-1]
        if field.startswith("__"):return None
        mask=index.family(ch.path)
        if field in index.meta["token_tables"]:mask |= index.bits(index.meta["stress"])
        return mask, True, "removed passive binding"
    change=changed_declaration(ch,section,left,right)
    if not change:return None
    name,a,b,start,indent=change
    field=name.rsplit(".",1)[-1]
    if field.startswith("__"):return None
    compiled_source(ch.after,ch.path)
    if family:
        if field=="TRANSFORMS":
            from callback_equivalence import witness
            callback=witness(index,section,ch.path,name,a,b,start-1)
            if callback is not None and callback!=index.all:
                return callback,False,"equivalent positional dispatch callback"
        exact=key_receipt(index,section,ch.path,name,a,b)
        if exact is not None:
            return exact,False,"observed immutable table value"
        from static_bounds import deferred_table
        parser_mask = deferred_table(index, ch, name, a, b)
        if parser_mask is not None:
            return parser_mask, True, "deferred parser table rows"
        if passive_dict(a,b,section["factories"]) or (read_expression(a) and read_expression(b)):
            mask=index.family(ch.path)
            if field in index.meta["token_tables"]:
                mask |= index.bits(index.meta["stress"])
            return mask,True,"localized dialect declaration"
    return None
