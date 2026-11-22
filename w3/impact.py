"""First-divergence bounds over pinned node observations; no patch code is evaluated here."""
import ast
import gzip
import hashlib
import marshal
import mmap
import struct
import types
import textwrap
import zlib
from bisect import bisect_left
from functools import lru_cache
from pathlib import Path

from value_bounds import compare_site, closure_readers
from callback_equivalence import witness as equivalent_callback
from patching import compiled_source, parsed_source, read_patch

FAMILIES = {"dialects","parsers","generators","tokenizers","typing"}
CORE = {"dialect","parser","generator","tokenizer","__init__"}
SAFE_VALUE = (ast.Constant,ast.Tuple,ast.List,ast.Set,ast.Dict,ast.Name,ast.Attribute,ast.Load,
              ast.UnaryOp,ast.USub,ast.UAdd)
FN = (ast.FunctionDef,ast.AsyncFunctionDef)

class Observations:
    def __init__(self, filename):
        with Path(filename).open("rb") as stream:
            self.data=mmap.mmap(stream.fileno(),0,access=mmap.ACCESS_READ)
        if self.data[:8]!=b"BRCOLD2\0":
            raise ValueError("invalid observation format")
        size=struct.unpack_from("<I",self.data,8)[0]
        self.start=12+size
        self.meta=marshal.loads(self.data[12:self.start])
        assert self.meta["format"]==2
        self.width=self.meta["width"]
        self.offset=self.start+self.meta["mask_offset"]
        self.ids=self.meta["ids"]
        self.all=self.bits(self.meta["all"])
        self.inspected=self.bits(self.meta["reflection"])|self.bits(self.meta["unknown"])
        self.registry=self.bits(self.meta["registry"])
    @lru_cache(maxsize=320)
    def section(self,name):
        loc=self.meta["paths"].get(name)
        if loc is None:return None
        a,n=loc
        a+=self.start
        return marshal.loads(zlib.decompress(self.data[a:a+n]))
    @lru_cache(maxsize=16384)
    def bits(self,idx):
        a=self.offset+self.width*idx
        return int.from_bytes(self.data[a:a+self.width],"little")
    def reflect(self,path,scope=None):
        if "reflection_residual" not in self.meta:
            return self.inspected
        key=path if scope is None else path+":"+scope
        ptr=self.meta["reflections"].get(key)
        return self.bits(self.meta["reflection_residual"]) | (self.bits(ptr) if ptr is not None else 0)
    def hit(self,section,name):
        return self.bits(section[name])
    @lru_cache(maxsize=128)
    def family(self,path):
        """Include concrete receiver ancestry, isolated imports, published registries and module re-exports."""
        f=self.section(path)
        mask=self.hit(f,"cold")|self.hit(f,"observed")|self.hit(f,"opens")|self.inspected|self.registry
        name=path.replace("/",".").removesuffix(".py")
        bases=self.section("@bases")
        roots={q for q in bases if q.startswith(name+".")}
        # Resolve a simple base only when all same-spelled classes agree; ambiguous
        # names union more client classes. Keep runtime method receipts for each descendant.
        tails={q.rsplit(".",1)[-1] for q in roots}
        direct=self.section("@imports")
        for child,edges in direct.items():
            if path not in edges or child==path:continue
            other=self.section(child)
            if other is None:continue
            for q,parents in bases.items():
                if not q.startswith(child.removesuffix(".py").replace("/",".")+"."):continue
                if any(parent.rsplit(".",1)[-1] in tails for parent in parents):
                    mask|=self.hit(other,"cold")|self.hit(other,"observed")
                    break
        return mask

def span(node):
    return (min([node.lineno]+[d.lineno for d in getattr(node,"decorator_list",())]),node.end_lineno)

def family_path(path):
    parts=path.split("/")
    return (len(parts)==3 and parts[0]=="sqlglot" and parts[1] in FAMILIES
            and path.endswith(".py") and parts[2][:-3] not in CORE)

def direct_members(tree):
    """Do not descend through branches or callable bodies when checking eager bindings."""
    def visit(body,scope):
        for n in body:
            if isinstance(n,ast.ClassDef):
                yield from visit(n.body,scope+n.name+".")
            elif isinstance(n, (ast.Assign,ast.AnnAssign)) and scope:
                dests=n.targets if isinstance(n,ast.Assign) else [n.target]
                if len(dests)==1 and isinstance(dests[0],ast.Name):
                    yield scope+dests[0].id,n
    return dict(visit(tree.body,""))

def changing_pair(ch,a,b):
    """Require actual edit lines inside the compared physical spans on both sources."""
    l,h=span(a);r,t=span(b)
    return (all(l<=n<=h for n in ch.removed) and all(r<=n<=t for n in ch.added)
            and bool(ch.added or ch.removed))

def one_declaration(ch,before,after):
    left,right=direct_members(before),direct_members(after)
    if left.keys()!=right.keys():return None
    for name,a in left.items():
        b=right[name]
        if not changing_pair(ch,a,b) or not a.value or not b.value:continue
        if type(a)!=type(b) or ast.dump(a.value)==ast.dump(b.value):continue
        # Prove the entire AST outside this value is identical. Parse a private copy
        # of the new tree so cached parse objects can safely serve subsequent patches.
        private=ast.parse(ch.after)
        member=direct_members(private)[name]
        member.value=a.value
        if ast.dump(private)==ast.dump(before):
            return name,a.value,b.value
    return None

def key_receipt(index,section,path,name,a,b):
    """Same ordered keys and immutable types; include reads of the complete table and absent-key probes."""
    profile=section["keys"].get(name)
    if profile is None or not isinstance(a,ast.Dict) or not isinstance(b,ast.Dict):return None
    try:
        old,new=ast.literal_eval(a),ast.literal_eval(b)
    except (ValueError,TypeError):return None
    if (list(old)!=list(new) or len(old)!=len(a.keys) or len(new)!=len(b.keys)
        or any(type(k) is not str for k in old)):return None
    def shape(value):
        if type(value) is tuple:return tuple,tuple(shape(v) for v in value)
        if type(value) not in (str,bytes,int,float,bool,type(None)):raise ValueError("mutable payload")
        return type(value)
    mask=index.hit(section,"opens")|index.reflect(path)
    if "*" in profile:mask|=index.bits(profile["*"])
    for k,x,y in zip(old,a.values,b.values):
        if shape(old[k])!=shape(new[k]):return None
        if ast.dump(x)!=ast.dump(y) and "k"+k in profile:
            mask|=index.bits(profile["k"+k])
    return mask

def pure_value(node):
    return all(isinstance(v,SAFE_VALUE) and not (isinstance(v,ast.Attribute) and v.attr.startswith("__"))
               for v in ast.walk(node))

def import_form(tree):
    result=[]
    for n in tree.body:
        if isinstance(n,ast.ImportFrom):
            if n.module=="__future__" or n.level or not n.module:
                result.append(("keep",ast.dump(n)))
            else:
                result.append(("from",n.module,tuple((a.name,a.asname) for a in n.names)))
        else:
            result.append(("keep",ast.dump(n)))
    return result

def import_delta(a,b,eager,exports):
    """A binding list may change. Adding/removing a provider requires the pin's unconditional import."""
    old,new=import_form(a),import_form(b)
    def skeleton(rows):
        return [r if r[0]!="from" else ("from",r[1]) for r in rows if r[0]!="from" or r[1] not in eager]
    if skeleton(old)!=skeleton(new) or old==new:return False
    for row in old+new:
        if row[0]!="from":continue
        if any(name=="*" or name.startswith("__") for name,_ in row[2]):return False
    old_names={(r[1],name,alias) for r in old if r[0]=="from" for name,alias in r[2]}
    new_names={(r[1],name,alias) for r in new if r[0]=="from" for name,alias in r[2]}
    changed=old_names^new_names
    if any(name not in exports.get(provider,()) for provider,name,alias in changed):return False
    bindings={alias or name for _,name,alias in changed}
    def eager_reads(tree):
        future=any(isinstance(s,ast.ImportFrom) and s.module=="__future__" and
                   any(alias.name=="annotations" for alias in s.names) for s in tree.body)
        stack=list(tree.body)
        while stack:
            n=stack.pop()
            if isinstance(n,FN):
                stack.extend(n.decorator_list+n.args.defaults+[v for v in n.args.kw_defaults if v])
                if not future:
                    stack.extend([v.annotation for v in n.args.posonlyargs+n.args.args+n.args.kwonlyargs if v.annotation])
                    stack.extend([v for v in (n.returns, getattr(n.args.vararg,"annotation",None),
                                              getattr(n.args.kwarg,"annotation",None)) if v])
            elif isinstance(n,ast.Lambda):stack.extend(n.args.defaults+[v for v in n.args.kw_defaults if v])
            elif isinstance(n,ast.AnnAssign) and future:
                if n.value:stack.append(n.value)
            elif isinstance(n,ast.Name) and isinstance(n.ctx,ast.Load) and n.id in bindings:return True
            else:stack.extend(ast.iter_child_nodes(n))
        return False
    return bool(changed) and not eager_reads(a) and not eager_reads(b)

def passive_rows(a,b):
    if pure_value(a) and pure_value(b):return True
    if not isinstance(a,ast.Dict) or not isinstance(b,ast.Dict):return False
    def pairs(d):
        return [(ast.dump(k) if k is not None else None,ast.dump(v),k,v) for k,v in zip(d.keys,d.values)]
    before,after=pairs(a),pairs(b)
    while before and after and before[0][:2]==after[0][:2]:
        before.pop(0);after.pop(0)
    while before and after and before[-1][:2]==after[-1][:2]:
        before.pop();after.pop()
    return all(k is not None and pure_value(k) and pure_value(v) for _,_,k,v in before+after)

def sole_definition(old,new):
    """Only delayed, undecorated definitions with inert headers and no apparent nonlocal writes."""
    def strip(tree):
        classes=[]
        signatures={}
        def flatten(body,prefix):
            result=[]
            for n in body:
                if isinstance(n,FN):
                    key=prefix+n.name
                    if key in signatures:raise ValueError("ambiguous duplicate")
                    signatures[key]=n
                    result.append(("def",key))
                elif isinstance(n,ast.ClassDef):
                    result.append(("class",n.name,tuple(ast.dump(x) for x in n.bases+n.keywords+n.decorator_list),
                                   flatten(n.body,prefix+n.name+".")))
                else:result.append(("stmt",ast.dump(n)))
            return result
        return flatten(tree.body,""),signatures
    ls,l=strip(old);rs,r=strip(new)
    different=l.keys()^r.keys()
    if len(different)!=1 or any(ast.dump(l[k])!=ast.dump(r[k]) for k in l.keys()&r.keys()):return False
    name=next(iter(different));fn=l.get(name) or r[name]
    def drop(entries):
        result=[]
        for e in entries:
            if e==("def",name):continue
            result.append((*e[:-1],drop(e[-1])) if e[0]=="class" else e)
        return result
    if drop(ls)!=drop(rs) or fn.name.startswith("__") or fn.decorator_list:return False
    if any(not isinstance(v,ast.Constant) for v in fn.args.defaults+[v for v in fn.args.kw_defaults if v]):return False
    return all(not isinstance(v,(ast.Global,ast.Nonlocal,ast.With,ast.AsyncWith,ast.Yield,ast.YieldFrom,
                                ast.Import,ast.ImportFrom,ast.Delete,ast.AugAssign,ast.Call))
               and not (isinstance(v,(ast.Subscript,ast.Attribute)) and isinstance(v.ctx,ast.Store))
               for v in ast.walk(fn))

def equivalent(a,b):
    """Exact code tree including location and exception tables, typed constants and all variable bindings."""
    if not isinstance(a,types.CodeType) or not isinstance(b,types.CodeType):
        return type(a) is type(b) and marshal.dumps(a)==marshal.dumps(b)
    return (a.co_name==b.co_name and a.co_qualname==b.co_qualname and a.co_code==b.co_code
            and a.co_flags==b.co_flags and a.co_names==b.co_names and a.co_varnames==b.co_varnames
            and a.co_cellvars==b.co_cellvars and a.co_freevars==b.co_freevars
            and a.co_argcount==b.co_argcount and a.co_posonlyargcount==b.co_posonlyargcount
            and a.co_kwonlyargcount==b.co_kwonlyargcount and a.co_firstlineno==b.co_firstlineno
            and a.co_linetable==b.co_linetable and a.co_exceptiontable==b.co_exceptiontable
            and len(a.co_consts)==len(b.co_consts) and all(equivalent(x,y) for x,y in zip(a.co_consts,b.co_consts)))

def statement_ranges(a,b):
    """Return old statements that dominate all possible first divergences. A new sibling widens to its parent."""
    result=[]
    def visit(x,y,anchor):
        if not isinstance(x,ast.AST) or type(x) is not type(y):
            if x!=y:result.append(anchor)
            return
        if isinstance(x,ast.stmt):
            anchor=x
        for k,left in ast.iter_fields(x):
            right=getattr(y,k)
            if isinstance(left,list):
                if len(left)!=len(right):
                    result.append(anchor)
                else:
                    for o,n in zip(left,right):visit(o,n,anchor)
            elif isinstance(left,ast.AST):visit(left,right,anchor)
            elif left!=right:result.append(anchor)
    visit(a,b,a)
    return {span(s) for s in result}

def disjoint_ranges(section,ranges,idx):
    mask=0
    for name in ("lines","cold_lines"):
        tab=section[name]
        for a,b in ranges:
            for n in range(a,b+1):
                pointer=tab.get(n)
                if pointer is not None:mask|=idx.bits(pointer)
    return mask

@lru_cache(maxsize=96)
def functions(source):
    result={}
    def visit(body,prefix):
        for v in body:
            if isinstance(v,ast.ClassDef):
                visit(v.body,prefix+v.name+".")
            elif isinstance(v,FN):
                name=prefix+v.name
                if name in result:result[name]=None
                else:result[name]=v
    visit(parsed_source(source).body,"")
    return result

@lru_cache(maxsize=128)
def physical_lines(source):
    return source.decode("utf8").split("\n")

def body_certificate(index,ch,f):
    if not ch.removed:return None
    lo,hi=min(ch.removed),max(ch.removed)
    left=physical_lines(ch.before)
    right=physical_lines(ch.after)
    shift=len(right)-len(left)
    for key,(start,body,end,code_mask) in f["functions"].items():
        if not body<=lo<=hi<=end or not all(body<=n<=end+shift for n in ch.added):continue
        if ch.insertions and any(n<body-1 or n>end for n in ch.insertions):continue
        def get(lines,last):
            fragment=textwrap.dedent("\n".join(lines[start-1:last]))
            parsed=ast.parse(fragment,type_comments=True)
            if len(parsed.body)!=1 or not isinstance(parsed.body[0],FN):return None
            return parsed.body[0]
        try:a,b=get(left,end),get(right,end+shift)
        except (SyntaxError,IndentationError):return None
        if a is None or b is None or a.decorator_list or b.decorator_list:return None
        if a.name!=b.name or ast.dump(a.args)!=ast.dump(b.args) or ast.get_docstring(a)!=ast.get_docstring(b):return None
        forbidden=(ast.Global,ast.Nonlocal,ast.Yield,ast.YieldFrom,ast.NamedExpr)
        if any(isinstance(n,forbidden) for fn in (a,b) for n in ast.walk(fn)):return None
        bindings=lambda fn:{v.id for v in ast.walk(fn) if isinstance(v,ast.Name) and isinstance(v.ctx,(ast.Store,ast.Del))}
        if bindings(a)!=bindings(b):return None
        ranges={(l+start-1,r+start-1) for l,r in statement_ranges(a,b)}
        if not ranges:return None
        mask=disjoint_ranges(f,ranges,index)|index.hit(f,"opens")|index.reflect(ch.path)
        return "guarded",mask,0,"two-sided statement boundary"
    return None

def classify(index,ch):
    """Return (route, upper bound, mandatory mask, diagnostic). None delegates to the team selector."""
    f=index.section(ch.path)
    if f is None or hashlib.sha256(ch.before).digest()!=f["digest"]:return None
    if ch.path.startswith("tests/fixtures/") and ch.path.endswith(".sql"):
        if ch.path in index.meta.get("unknown_opens",()):return None
        mask=index.hit(f,"opens")|index.bits(index.meta["unknown"])
        return ("direct",mask,0,"SQL fixture readers") if mask else None
    if not ch.path.endswith(".py") or not ch.path.startswith("sqlglot/"):return None
    points=ch.removed|ch.insertions|{x+1 for x in ch.insertions}
    if points.intersection(f["order"]) or points.intersection(f["warm_unknown"]):return None
    # The fork that decides whether this bound is admissible separately verifies a matching
    # module-level, old-and-new code swap. Preflight parses only the touched function.
    result=compare_site(index,f,ch,physical_lines(ch.before),physical_lines(ch.after)) if f.get("domains") else None
    if result is not None:
        possible,scope=result
        if possible and not ch.insertions:
            from proofs import identity_equivalence
            proof=identity_equivalence(ch,parsed_source(ch.before),parsed_source(ch.after))
            if proof is not None:
                possible=0
        if not possible:
            return "direct",index.reflect(ch.path,scope)|index.hit(f,"opens"),0,"unchanged comparison on pin operands"
    local=body_certificate(index,ch,f)
    if local:return local
    if not family_path(ch.path):
        # A comment-looking line in a multiline string is still executable data. Compare the
        # complete compiled modules for apparent trivia, then keep any explicit source readers.
        trivia=all(not physical_lines(src)[n-1].strip() or physical_lines(src)[n-1].lstrip().startswith("#")
                   for src,points in ((ch.before,ch.removed),(ch.after,ch.added)) for n in points)
        if not trivia:return None
    old_code=compiled_source(ch.before,ch.path)
    new_code=compiled_source(ch.after,ch.path)
    if old_code==new_code and equivalent(old_code,new_code):
        return "direct",index.hit(f,"opens")|index.inspected,0,"identical compiled code"
    old,new=parsed_source(ch.before),parsed_source(ch.after)
    if family_path(ch.path):
        declaration=one_declaration(ch,old,new)
        if declaration:
            name,a,b=declaration
            if name.split(".")[-1].startswith("__"):return None
            closure=closure_readers(index,f,ch,a,b) if hasattr(index,"team") else None
            if closure is not None:
                return "direct",closure,0,"concrete dispatch closure calls"
            callback=equivalent_callback(index,f,ch.path,name,a,b)
            if callback is not None and callback!=index.all:
                return "direct",callback,0,"equivalent positional dispatch callback"
            exact=key_receipt(index,f,ch.path,name,a,b)
            if exact is not None and exact!=index.all:
                return "direct",exact,0,"observed immutable table value"
            if passive_rows(a,b):
                field=name.rsplit(".",1)[-1]
                stress=0
                if field in index.meta["token_tables"] and isinstance(a,ast.Dict) and isinstance(b,ast.Dict):
                    keys=lambda d:[ast.dump(k) if k else None for k in d.keys]
                    if keys(a)!=keys(b):stress=index.bits(index.meta["stress"])
                return "family",index.family(ch.path),stress,"passive dialect declaration"
        # An import-only proof requires touching a top-level import. Avoid dumping every
        # function in large dialect modules for edits wholly outside those statements.
        def touches_import(tree,points):
            return any(isinstance(n,ast.ImportFrom) and any(n.lineno<=line<=n.end_lineno for line in points)
                       for n in tree.body)
        if ((touches_import(old,ch.removed) or touches_import(new,ch.added))
                and import_delta(old,new,index.meta["eager"],index.section("@exports") or {})):
            return "family",index.family(ch.path),0,"import names on existing providers"
        defs_changed=any(physical_lines(source)[n-1].lstrip().startswith(("def ","async def "))
                         for source,points in ((ch.before,ch.removed),(ch.after,ch.added)) for n in points)
        if defs_changed and sole_definition(old,new):
            names=lambda t:{n.name for n in ast.walk(t) if isinstance(n,FN)}
            masks=index.section("@callers") or {}
            readers=0
            for n in names(old)^names(new):
                if n in masks:readers|=index.bits(masks[n])
            return "family",index.family(ch.path)|readers,0,"passive definition addition/removal"

    return None
