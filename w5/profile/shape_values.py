"""Observe existing keyword reads and native dictionary copy operands on the unchanged pin."""
import ast
import builtins
from pathlib import Path

def keyword_inventory(root):
    names=set()
    for file in sorted((root/'sqlglot').rglob('*.py')):
        tree=ast.parse(file.read_bytes())
        for n in ast.walk(tree):
            if not isinstance(n,(ast.Assign,ast.AnnAssign)) or not isinstance(n.value,ast.Dict):continue
            dest=n.targets if isinstance(n,ast.Assign) else (n.target,)
            if any(isinstance(t,ast.Name) and t.id=='KEYWORDS' for t in dest):
                names.update(k.value for k in n.value.keys if isinstance(k,ast.Constant) and type(k.value) is str)
    return {k for k in names if k.isascii() and k.isidentifier() and k.isupper()}

words = keyword_inventory(Path('/sqlglot'))
atoms = (str, bytes, bool, int, float, type(None))
emit = None


def dictionary(site, value):
    # Native disjoint trees give the same object sharing when each top-level
    # value is copied separately and when one memo is used for the dictionary.
    seen = set()
    def passive(obj, depth):
        if type(obj) in atoms:
            return True
        if depth > 24 or len(seen) > 100 or id(obj) in seen:
            return False
        if type(obj) not in (list, dict, tuple):
            return False
        seen.add(id(obj))
        if type(obj) is dict:
            return all(type(k) in atoms and passive(v, depth+1) for k,v in obj.items())
        return all(passive(v, depth+1) for v in obj)
    emit('@copy-read/'+site)
    if type(value) is not dict or not passive(value,0):
        emit('@copy-opaque/'+site)
    return value


def key(value):
    if type(value) is not str:
        emit('@keyword/*')
    elif value in words:
        emit('@keyword/'+value)
    return value


def bulk(value):
    emit('@keyword/*')
    return value


def setup(record):
    global emit
    emit=record
    builtins._br5_copy_dict=dictionary
    builtins._br5_token_key=key
    builtins._br5_token_bulk=bulk


def rewrite(tree,path):
    parents={c:n for n in ast.walk(tree) for c in ast.iter_child_nodes(n)}
    core=path=='sqlglot/tokenizer_core.py'
    wrapper=path=='sqlglot/tokens.py'
    seen=set()
    def tracked(node):
        return isinstance(node,ast.Attribute) and (node.attr=='KEYWORDS' or core and node.attr=='keywords')
    def wrap(node,func):
        return ast.copy_location(ast.Call(ast.Name(func,ast.Load()),[node],[]),node)
    # A plain local table alias is observed at every use before it can escape.
    aliases=set()
    if core:
        for n in ast.walk(tree):
            if isinstance(n,ast.Assign) and tracked(n.value) and len(n.targets)==1 and isinstance(n.targets[0],ast.Name):
                aliases.add(n.targets[0].id);seen.add(id(n.value))
    def table(n):
        return tracked(n) or isinstance(n,ast.Name) and (n.id=='KEYWORDS' or core and n.id in aliases)
    for n in list(ast.walk(tree)):
        if isinstance(n,ast.Subscript) and table(n.value):
            n.slice=wrap(n.slice,'_br5_token_key');seen.add(id(n.value))
        elif isinstance(n,ast.Compare) and len(n.ops)==1 and isinstance(n.ops[0],(ast.In,ast.NotIn)) and table(n.comparators[0]):
            n.left=wrap(n.left,'_br5_token_key');seen.add(id(n.comparators[0]))
        elif isinstance(n,ast.Call) and isinstance(n.func,ast.Attribute) and table(n.func.value) and n.func.attr in ('get','pop','setdefault') and n.args:
            n.args[0]=wrap(n.args[0],'_br5_token_key');seen.add(id(n.func.value))
        elif isinstance(n,ast.Dict):
            out=parents.get(n)
            targets=out.targets if isinstance(out,ast.Assign) else [out.target] if isinstance(out,ast.AnnAssign) else []
            if any(isinstance(t,ast.Name) and t.id=='KEYWORDS' for t in targets):
                seen.update(id(v) for k,v in zip(n.keys,n.values) if k is None and tracked(v))
        elif isinstance(n,ast.Call) and isinstance(n.func,ast.Attribute) and n.func.attr=='copy' and tracked(n.func.value) and not n.args and not n.keywords:
            out=parents.get(n)
            if isinstance(out,ast.Assign) and len(out.targets)==1 and isinstance(out.targets[0],ast.Name) and out.targets[0].id=='KEYWORDS':
                seen.add(id(n.func.value))
        elif wrapper and isinstance(n,ast.Call) and isinstance(n.func,ast.Name) and n.func.id=='TokenizerCore':
            for kw in n.keywords:
                if kw.arg=='keywords' and tracked(kw.value):seen.add(id(kw.value))
        elif wrapper and isinstance(n,ast.GeneratorExp) and ast.unparse(n.elt)=='key.upper()' and len(n.generators)==1:
            g=n.generators[0]
            if isinstance(g.iter,ast.Tuple) and ast.unparse(g.target)=='key':
                forwarded=[v.value for v in g.iter.elts if isinstance(v,ast.Starred) and tracked(v.value)]
                if forwarded:
                    seen.update(id(v) for v in forwarded);n.elt=wrap(n.elt,'_br5_token_key')
    # Forwarding a constructor parameter into the known core storage keeps its keys intact.
    for n in ast.walk(tree):
        if core and isinstance(n,ast.Assign) and len(n.targets)==1 and ast.unparse(n.targets[0])=='self.keywords' and isinstance(n.value,ast.Name) and n.value.id=='keywords':
            seen.add(id(n.value))
    for fn in (n for n in ast.walk(tree) if isinstance(n,ast.FunctionDef)):
        if not any(isinstance(n,ast.Call) and isinstance(n.func,ast.Name) and n.func.id=='deepcopy' for n in ast.walk(fn)):continue
        for n in ast.walk(fn):
            if isinstance(n,ast.Call) and isinstance(n.func,ast.Name) and n.func.id=='dict' and len(n.args)==1 and not n.keywords:
                arg=n.args[0]
                if isinstance(arg,(ast.Name,ast.Attribute)):
                    site=f'{path}:{n.lineno}:{n.col_offset}'
                    n.args[0]=ast.copy_location(ast.Call(ast.Name('_br5_copy_dict',ast.Load()),[ast.Constant(site),arg],[]),arg)
    class Unknown(ast.NodeTransformer):
        def visit_Attribute(self,n):
            self.generic_visit(n)
            return wrap(n,'_br5_token_bulk') if tracked(n) and isinstance(n.ctx,ast.Load) and id(n) not in seen else n
        def visit_Name(self,n):
            return wrap(n,'_br5_token_bulk') if (n.id=='KEYWORDS' or core and n.id in aliases) and isinstance(n.ctx,ast.Load) and id(n) not in seen else n
    Unknown().visit(tree)
    return tree
