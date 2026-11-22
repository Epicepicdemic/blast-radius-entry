"""Identify cold class-body reads that exclusively forward a native map into a subclass."""
import ast
from functools import lru_cache
from pathlib import Path
import sys


@lru_cache(32)
def syntax(file):
    tree=ast.parse(file.read_bytes())
    nodes=list(ast.walk(tree))
    parents={c:n for n in nodes for c in ast.iter_child_nodes(n)}
    return tree,nodes,parents


@lru_cache(1024)
def forward(root, path, provider, field):
    file=Path(root)/path
    module=path[:-3].replace('/','.').removesuffix('.__init__')
    if module not in sys.modules or not file.is_file():
        return False
    namespace=vars(sys.modules[module])
    tree,nodes,parents=syntax(file)
    seen=False
    for n in nodes:
        if isinstance(n,ast.Constant) and n.value==field:return False
        if not isinstance(n,ast.Attribute) or n.attr!=field:continue
        mapping=parents[n];assignment=parents.get(mapping);owner=parents.get(assignment)
        if not (isinstance(n.value,ast.Name) and isinstance(mapping,ast.Dict) and
                any(k is None and value is n for k,value in zip(mapping.keys,mapping.values)) and
                isinstance(assignment,(ast.Assign,ast.AnnAssign)) and isinstance(owner,ast.ClassDef) and owner in tree.body):
            return False
        targets=assignment.targets if isinstance(assignment,ast.Assign) else [assignment.target]
        if len(targets)!=1 or not isinstance(targets[0],ast.Name) or targets[0].id!=field:return False
        child=namespace.get(owner.name);parent=namespace.get(n.value.id)
        if not isinstance(parent,type) or not isinstance(child,type) or not issubclass(child,parent):return False
        lineage={c.__module__+'.'+c.__qualname__ for c in parent.__mro__}
        if provider not in lineage or type(getattr(parent,field,None)) is not dict:return False
        seen=True
    return seen
