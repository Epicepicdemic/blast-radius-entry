"""Causal reads of passive class fields, preserving shape observers and inherited copies."""
import ast
from functools import lru_cache
from frontier import same
from impact import physical_lines
from patching import compiled_source,parsed_source
from rules5 import facts,observations


def identifier(node):
    if isinstance(node,ast.Assign) and len(node.targets)==1:target=node.targets[0]
    elif isinstance(node,ast.AnnAssign):target=node.target
    else:return None
    return target.id if isinstance(target,ast.Name) else None


def changed_class(ch):
    def compare(a,b,parent):
        if len(a)!=len(b):return None
        pairs=[(x,y) for x,y in zip(a,b) if not same(x,y)]
        if len(pairs)!=1:return None
        x,y=pairs[0]
        if not (isinstance(x,ast.ClassDef) and isinstance(y,ast.ClassDef) and
                all(same(getattr(x,k),getattr(y,k)) for k in x._fields if k!="body")):return None
        owner=parent+"."+x.name
        return compare(x.body,y.body,owner) or (owner,x,y)
    mod=ch.path[:-3].replace("/",".").removesuffix(".__init__")
    return compare(parsed_source(ch.before).body,parsed_source(ch.after).body,mod)


def passive(n,module,local):
    if n is None:return True
    if isinstance(n,ast.Constant):return type(n.value) in (str,int,bool,float,type(None),bytes)
    if isinstance(n,(ast.Tuple,ast.List,ast.Set)):return all(passive(i,module,local) for i in n.elts)
    if isinstance(n,ast.Dict):return all(k is not None and passive(k,module,local) and passive(v,module,local) for k,v in zip(n.keys,n.values))
    if isinstance(n,ast.UnaryOp) and isinstance(n.op,(ast.USub,ast.UAdd)) and isinstance(n.operand,ast.Constant):
        return type(n.operand.value) in (int,float)
    if isinstance(n,(ast.Name,ast.Attribute)):
        from effects5 import qualified
        ref=qualified(n)
        return ref.split(".")[0] not in local and ref in facts()["passive"].get(module,())
    return False


def members(cls):
    keep=[];decls={};position=0
    for i,st in enumerate(cls.body):
        if isinstance(st,ast.Pass) or isinstance(st,ast.Expr) and isinstance(st.value,ast.Constant) and type(st.value.value) is str:
            continue
        key=identifier(st)
        if key and (key=="arg_types" or key.isupper()):
            if key in decls:return None
            decls[key]=(position,st)
        else:
            keep.append(st);position+=1
    return keep,decls


def class_bound(ix,ch):
    if not ch.path.endswith(".py") or not ch.path.startswith("sqlglot/") or not (ch.removed or ch.added):return None
    left,right=physical_lines(ch.before),physical_lines(ch.after)
    # Avoid walking a large module for edits wholly inside an ordinary method.
    ls=[left[n-1] for n in ch.removed]+[right[n-1] for n in ch.added]
    if not any(('=' in t and (t.lstrip().partition('=')[0].strip().split(':')[0].isupper() or 'arg_types' in t))
               or t.lstrip().startswith(('"',"'")) for t in ls):return None
    pair=changed_class(ch)
    if pair is None:return None
    owner,a,b=pair;module=ch.path[:-3].replace("/",".").removesuffix(".__init__")
    if owner not in facts()["ordinary_classes"]:return None
    x,y=members(a),members(b)
    if x is None or y is None or not same(x[0],y[0]):return None
    lm,rm=x[1],y[1]
    changed=[k for k in lm.keys()|rm.keys() if k not in lm or k not in rm or not same(lm[k][1],rm[k][1])]
    if not changed:return None
    # Relative order and lexical region of every unchanged initializer is preserved.
    if [(k,n) for k,(n,_) in lm.items() if k not in changed]!=[(k,n) for k,(n,_) in rm.items() if k not in changed]:return None
    data=facts();mask=observations(ix,ch.path);doc_changed=ast.get_docstring(a,clean=False)!=ast.get_docstring(b,clean=False)
    df=data["field_data"];resources=False
    namespace=df['reads'].get((owner,'__namespace__'),{})
    def readers(key, shape=False):
        mask = namespace.get(('unknown',None),0)|namespace.get(('namespace',None),0)|df['opaque']
        for kind in ('dynamic','dictionary_key'):
            mask |= namespace.get((kind,key),0)
        if shape and key not in df['base_names'].get(owner,()):
            mask |= namespace.get(('dir',None),0)
        return mask
    if doc_changed:
        mask |= readers('__doc__')
    from delayed import bindings
    for k in changed:
        l=lm.get(k,(None,None))[1];r=rm.get(k,(None,None))[1]
        if (module,k) in df["bare"]:return None
        lv=l.value if l else None;rv=r.value if r else None
        if k!="arg_types":
            def option(v):
                if v is None or isinstance(v,ast.Constant):return True
                if isinstance(v,ast.Tuple):return all(isinstance(el,(ast.Name,ast.Attribute,ast.Constant)) for el in v.elts)
                if isinstance(v,ast.Dict):
                    return all(isinstance(key,ast.Attribute) and isinstance(val,ast.Attribute) and val.attr.isupper() and
                               isinstance(key.value,ast.Name) and key.value.id=="exp" and key.attr[:1].isupper()
                               for key,val in zip(v.keys,v.values))
                return False
            if not option(lv) or not option(rv):return None
        if not passive(lv,module,bindings(a)) or not passive(rv,module,bindings(b)):return None
        if isinstance(l,ast.AnnAssign) or isinstance(r,ast.AnnAssign):
            if not any(isinstance(n,ast.ImportFrom) and n.module=="__future__" and any(t.name=="annotations" for t in n.names) for n in parsed_source(ch.before).body):return None
            mask |= readers('__annotations__')
        mask |= readers(k,(l is None)!=(r is None))
        if k not in df["tracked"]:
            mask|=df["attrs"].get(k,0)
        row=df["reads"].get((owner,k),{})
        if k!="arg_types":
            # Changing a declaration cannot mutate a pre-existing table in place.
            # A class-body use that materialized a derived constant remains owed.
            shared_dict=all(isinstance(v,ast.Dict) for v in (lv,rv) if v is not None)
            if lv is None or rv is None:
                # Removing this binding exposes the next value in the pin MRO.
                shared_dict &= (owner,k) in data['native_dict_bases']
            for (mode,key),m in row.items():
                mask|=df['forwarded'].get((owner,k,mode,key),m) if shared_dict else m
            continue
        if not ch.path.startswith("sqlglot/expressions/") or owner not in data["ordinary_expressions"]:return None
        try:
            old=ast.literal_eval(lv) if lv is not None else df["inherited"][owner]
            new=ast.literal_eval(rv) if rv is not None else df["inherited"][owner]
        except (KeyError,ValueError,TypeError):return None
        if any(type(v) is not dict or any(type(n) is not str or type(b) is not bool for n,b in v.items()) for v in (old,new)):return None
        if {s for s in old if old[s]}!={s for s in new if new[s]}:return None
        # required_args is identical on both sides of the pin's checked derivation.
        if list(old.items())==list(new.items()):
            # Identity of the table and namespace ownership can still be observed.
            if (lv is None)!=(rv is None):mask|=row.get(("whole",None),0)
            continue
        keys=old.keys()^new.keys()
        for (mode,value),m in row.items():
            if mode=="whole" or mode=="member" and (value is None or value in keys) or mode=="arity" and (value>len(old))!=(value>len(new)):
                mask|=m
                if mode=="member" and value in old and value not in new and m:
                    # A cold import can amplify a validation error across workers.
                    # A local validation keeps every observed caller, including any
                    # stress or pool case that actually constructs this argument.
                    resources |= ((owner,k,mode,value) in df['scoped'] or bool(m & df['opaque']))
    if mask.bit_count()>len(ix.ids)//4:resources=True
    if resources:
        from bounds import facts as w4facts
        mask|=w4facts()["resources"]
    compiled_source(ch.after,ch.path)
    return mask
