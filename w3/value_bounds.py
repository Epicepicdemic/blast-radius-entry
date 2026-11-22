"""Specialize pin observations only when the entire patched construct matches the contract."""
import ast
import operator
import textwrap

OPS = {ast.Is:operator.is_, ast.IsNot:operator.is_not, ast.Eq:operator.eq, ast.NotEq:operator.ne,
       ast.Lt:operator.lt, ast.LtE:operator.le, ast.Gt:operator.gt, ast.GtE:operator.ge}

def comparison_delta(old, new):
    if type(old) is not type(new) or len(old.ops) != 1 or len(new.ops) != 1:
        return False
    return (type(old.ops[0]) is not type(new.ops[0])
            and ast.dump(old.left) == ast.dump(new.left)
            and ast.dump(old.comparators[0]) == ast.dump(new.comparators[0]))

def same_result(fact, old, new):
    if fact[0] == "tuples" and old not in (ast.Is,ast.IsNot) and new not in (ast.Is,ast.IsNot):
        a,b=tuple(fact[1]),tuple(fact[2])
        return OPS[old](a,b) == OPS[new](a,b)
    if fact[0] in ("identity","strings"):
        answers={ast.Is:fact[1],ast.IsNot:not fact[1]}
        eq=fact[1] if fact[0]=="identity" else fact[2]==fact[3]
        answers.update({ast.Eq:eq, ast.NotEq:not eq})
        return old in answers and new in answers and answers[old] == answers[new]
    return False

def compare_site(index, section, ch, old_lines, new_lines):
    if len(ch.removed)!=1 or ch.removed!=ch.added or ch.insertions:
        return None
    line=next(iter(ch.removed))
    sites=section.get("domains",{}).get(line)
    if not sites:
        return None
    for name,(start,body,end,_) in section["functions"].items():
        if not body <= line <= end:
            continue
        left="\n".join(old_lines[start-1:end])
        right="\n".join(new_lines[start-1:end])
        a,b=ast.parse(textwrap.dedent(left)),ast.parse(textwrap.dedent(right))
        old=[n for n in ast.walk(a) if isinstance(n,ast.Compare)]
        new=[n for n in ast.walk(b) if isinstance(n,ast.Compare)]
        if len(old)!=len(new):
            return None
        different=[(x,y) for x,y in zip(old,new) if comparison_delta(x,y)]
        if len(different)!=1:
            return None
        x,y=different[0]
        if x.lineno+start-1!=line or x.end_lineno!=x.lineno or x.lineno!=y.lineno:
            return None
        indent=len(old_lines[line-1].encode())-len(textwrap.dedent(left).split("\n")[x.lineno-1].encode())
        facts=sites.get(x.col_offset+indent)
        oldop,newop=type(x.ops[0]),type(y.ops[0])
        if not facts or oldop not in OPS or newop not in OPS:
            return None
        y.ops=x.ops
        if ast.dump(a)!=ast.dump(b):
            return None
        unknown=index.bits(index.meta["value_unknown"])
        observed=0
        for fact,mask in facts:
            if not same_result(fact,oldop,newop):
                observed |= index.bits(mask)
        reached=0
        for table in ("lines","cold_lines"):
            ptr=section[table].get(line)
            if ptr is not None:
                reached |= index.bits(ptr)
        return observed | (unknown & reached), name
    return None

def closure_readers(index,section,ch,old,new):
    if not isinstance(old,ast.Dict) or not isinstance(new,ast.Dict) or len(old.keys)!=len(new.keys):
        return None
    def dump(n):return None if n is None else ast.dump(n)
    if list(map(dump,old.keys))!=list(map(dump,new.keys)):
        return None
    delta=[(a,b) for a,b in zip(old.values,new.values) if dump(a)!=dump(b)]
    if len(delta)!=1:
        return None
    a,b=delta[0]
    if not (isinstance(a,ast.Call) and isinstance(b,ast.Call) and isinstance(a.func,ast.Name)
            and dump(a.func)==dump(b.func)):
        return None
    key=(a.lineno,a.col_offset)
    if key not in section.get("closures",{}):
        return None
    # The release's delayed-literal proof checks the pin factory and its capture. It also
    # bounds callers in uninstrumented processes. Only specialize a successful proof.
    from patching import parsed_source
    from proofs import delayed_literal
    proof=delayed_literal(index.team,parsed_source(ch.before),parsed_source(ch.after),ch)
    if not proof or proof[0]!="deferred closure calls":
        return None
    users=index.bits(section["closures"][key])
    unknown=index.bits(index.meta["value_unknown"])
    return users | (unknown & proof[1]) | index.reflect(ch.path) | index.hit(section,"opens")

def schema_readers(index,ch,name,old,new):
    if not (index.meta.get("has_schema") and name.endswith(".arg_types")
            and ch.path.startswith("sqlglot/expressions/") and isinstance(old,ast.Dict)
            and isinstance(new,ast.Dict) and hasattr(index,"team")):
        return None
    try:
        left,right=ast.literal_eval(old),ast.literal_eval(new)
    except (ValueError,TypeError):
        return None
    if list(left)!=list(right) or len(left)!=len(old.keys) or len(right)!=len(new.keys):
        return None
    if any(type(k) is not str or type(left[k]) is not bool or type(right[k]) is not bool for k in left):
        return None
    from proofs import delayed_literal
    from patching import parsed_source
    proof=delayed_literal(index.team,parsed_source(ch.before),parsed_source(ch.after),ch)
    if not proof or proof[0]!="expression schema":
        return None
    owner=ch.path[:-3].replace("/",".")+"."+name.rsplit(".",1)[0]
    table=(index.section("@schema") or {}).get(owner,{})
    mask=index.bits(index.meta["schema_unknown"]) & proof[1]
    for key in ["*",*("k"+k for k in left if left[k]!=right[k])]:
        if key in table:
            mask|=index.bits(table[key])
    return mask|index.reflect(ch.path)|index.hit(index.section(ch.path),"opens")
