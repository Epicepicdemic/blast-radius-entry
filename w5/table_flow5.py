"""Verify that lookups of the parser table stay within their receiver's class hierarchy."""
import ast
import sys
from types import ModuleType


def local_lookup(name, fn, parents):
    for node in ast.walk(fn):
        if not isinstance(node, ast.Name) or node.id != name or not isinstance(node.ctx, ast.Load):
            continue
        parent = parents[node]
        if isinstance(parent, ast.Compare) and parent.left is node and len(parent.ops) == 1 and isinstance(parent.ops[0], (ast.Is, ast.IsNot)):
            continue
        if isinstance(parent, ast.Attribute) and parent.value is node and parent.attr == 'get':
            call = parents.get(parent)
            if isinstance(call, ast.Call) and call.func is parent:
                continue
        return False
    return True


def closed(root, field):
    for directory in ('sqlglot', 'tests'):
        for path in sorted((root / directory).rglob('*.py')):
            src = path.read_bytes()
            if field.encode() not in src:
                continue
            tree = ast.parse(src)
            parents = {c: n for n in ast.walk(tree) for c in ast.iter_child_nodes(n)}
            mod = '.'.join(path.relative_to(root).with_suffix('').parts).removesuffix('.__init__')
            namespace = vars(sys.modules[mod]) if mod in sys.modules else {}
            for n in ast.walk(tree):
                if not isinstance(n, ast.Attribute) or n.attr != field:
                    continue
                parent = parents[n]
                if not isinstance(n.ctx, ast.Load):
                    return False
                if isinstance(parent,ast.Subscript) and parent.value is n:
                    continue
                if isinstance(parent,ast.Compare) and len(parent.ops)==1 and isinstance(parent.ops[0],(ast.In,ast.NotIn)) and parent.comparators[0] is n:
                    continue
                if isinstance(parent, ast.Attribute) and parent.value is n and parent.attr == 'get' and isinstance(parents.get(parent), ast.Call) and parents[parent].func is parent:
                    continue
                if isinstance(parent, ast.Assign) and parent.value is n and len(parent.targets)==1 and isinstance(parent.targets[0],ast.Name):
                    fn=parent
                    while fn in parents and not isinstance(fn,(ast.FunctionDef,ast.AsyncFunctionDef)):
                        fn=parents[fn]
                    if isinstance(fn,ast.FunctionDef) and local_lookup(parent.targets[0].id,fn,parents):
                        continue
                # A display or comprehension can copy a binding into an inheriting
                # class. Receiver observations already include all its ancestors.
                node = n
                while node in parents and not isinstance(node, ast.stmt):
                    node=parents[node]
                owner=parents.get(node)
                targets=node.targets if isinstance(node,ast.Assign) else [node.target] if isinstance(node,ast.AnnAssign) else []
                if (not isinstance(owner,ast.ClassDef) or owner not in tree.body or len(targets)!=1 or
                        not isinstance(targets[0],ast.Name) or targets[0].id!=field or not isinstance(node.value,(ast.Dict,ast.DictComp))):
                    return False
                if isinstance(n.value,ast.Name):
                    base=namespace.get(n.value.id)
                elif isinstance(n.value,ast.Attribute) and isinstance(n.value.value,ast.Name):
                    provider=namespace.get(n.value.value.id)
                    base=vars(provider).get(n.value.attr) if isinstance(provider,ModuleType) else None
                else:
                    return False
                child=namespace.get(owner.name)
                if not isinstance(base,type) or not isinstance(child,type) or not issubclass(child,base):
                    return False
    return True


def receiver_mask(ix, owner, field):
    from rules5 import facts
    data=facts()
    if field not in data['closed_dispatch_fields']:
        return ix.all
    df=data['field_data']
    keep=df['opaque'] | data['dispatch_dynamic'].get(field,0)
    for (mode, key), hits in df['reads'].get((owner,field),{}).items():
        keep |= hits
    for (mode,key),hits in df['reads'].get((owner,'__namespace__'),{}).items():
        if mode in ('unknown','namespace') or key==field:
            keep|=hits
    return keep
