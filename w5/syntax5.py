"""Traverse the same children as Python's ast module with one field loop per node."""
import ast as _ast
from ast import *
from collections import deque


def __getattr__(name):
    return getattr(_ast, name)


def iter_child_nodes(node):
    children = []
    for field in node._fields:
        value = getattr(node, field, None)
        if isinstance(value, _ast.AST):
            children.append(value)
        elif isinstance(value, list):
            children.extend(item for item in value if isinstance(item, _ast.AST))
    return children


def walk(node):
    pending = deque([node])
    while pending:
        node = pending.popleft()
        pending.extend(iter_child_nodes(node))
        yield node
