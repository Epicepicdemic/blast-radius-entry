"""Attribute provenance for ordinary SQLGlot class dictionaries at the pinned revision."""
import ast
import builtins
from functools import cache
from pathlib import Path
import sys

import probe


@cache
def membership_sites():
    # The only value ignored by the reader trace is a dictionary reference
    # bound to a local whose every load is a constant-string membership test.
    # Restrict the proof to the audited metaclass, which doesn't leak its frame.
    path = "/sqlglot/sqlglot/dialects/dialect.py"
    tree = ast.parse(Path(path).read_bytes())
    meta = next(n for n in tree.body if isinstance(n, ast.ClassDef) and n.name == "_Dialect")
    new = next(n for n in meta.body if isinstance(n, ast.FunctionDef) and n.name == "__new__")
    parents = {c: p for p in ast.walk(new) for c in ast.iter_child_nodes(p)}
    result = set()
    for node in new.body:
        if not (isinstance(node, ast.Assign) and len(node.targets) == 1 and isinstance(node.targets[0], ast.Name)
                and isinstance(node.value, ast.Attribute) and node.lineno == node.end_lineno):
            continue
        name = node.targets[0].id
        refs = [n for n in ast.walk(new) if isinstance(n, ast.Name) and n.id == name and n is not node.targets[0]]
        if refs and all(isinstance(n.ctx, ast.Load) and isinstance(p := parents[n], ast.Compare)
                        and len(p.ops) == 1 and isinstance(p.ops[0], (ast.In, ast.NotIn))
                        and p.comparators == [n] and isinstance(p.left, ast.Constant)
                        and type(p.left.value) is str for n in refs):
            result.add((path, node.lineno, node.value.attr))
    return result


class Read:
    def __init__(self, key, name, value, membership):
        self.key = key
        self.name = name
        self.value = value
        self.membership = membership

    def __get__(self, obj, owner):
        if self.membership:
            frame = sys._getframe(1)
            if (frame.f_code.co_filename, frame.f_lineno, self.name) in self.membership:
                return self.value
        probe.class_reads[probe.context].add(self.key)
        return self.value


def start():
    create = builtins.__build_class__
    # Read the pinned AST before the audit hook is active.
    membership = membership_sites()

    def observed(body, name, *bases, **kwargs):
        cls = create(body, name, *bases, **kwargs)
        if len(bases) != 1 or type(cls) is not type or not cls.__module__.startswith("sqlglot."):
            return cls
        parent = bases[0]
        family = parent.__module__, parent.__qualname__
        if family not in (("sqlglot.expressions.core", "Expression"), ("sqlglot.tokens", "Tokenizer")):
            return cls
        ns = vars(cls)
        fields = []
        owner = cls.__module__ + "." + cls.__qualname__
        if family[1] == "Expression" and type(ns.get("arg_types")) is dict and "required_args" in ns:
            fields = ["arg_types", "required_args"]
        elif family[1] == "Tokenizer":
            fields = [k for k,v in ns.items() if k.isupper() and type(v) is dict]
        if not fields:
            return cls
        for field in fields:
            key = owner + "." + ("arg_types" if family[1] == "Expression" else field)
            probe.class_reads[probe.context].add("decl:" + key)
            setattr(cls, field, Read(key, field, ns[field], membership))
        # Track instance consumers as well. Tokenizers copy settings into their
        # cores; a cached instance may be used by a different test than its creator.
        original = cls.__getattribute__
        def read_instance(obj, attr):
            probe.class_reads[probe.context].add(owner)
            return original(obj, attr)
        cls.__getattribute__ = read_instance
        return cls

    builtins.__build_class__ = observed
