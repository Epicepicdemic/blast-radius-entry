"""Index value readers through pinned class table copies and inherited tables."""
import ast
from collections import defaultdict
import json
from pathlib import Path
import sys


def name_of(node):
    if isinstance(node, ast.Attribute):
        return node.attr
    if isinstance(node, ast.Name):
        return node.id
    return None


def target_of(stmt):
    if isinstance(stmt, ast.AnnAssign):
        return stmt.target
    if isinstance(stmt, ast.Assign) and len(stmt.targets) == 1:
        return stmt.targets[0]
    return None


def forwards_value(node, parents):
    """Return the destination of a shallow copy, or None for a consuming read."""
    null_filter = False
    while True:
        parent = parents.get(node)
        if isinstance(parent, ast.Dict) and any(
                k is None and v is node for k, v in zip(parent.keys, parent.values)):
            node = parent
            continue
        if isinstance(parent, ast.Starred) and isinstance(parents.get(parent), (ast.List, ast.Tuple)):
            node = parents[parent]
            continue
        if isinstance(parent, ast.Attribute) and parent.attr == "items":
            call = parents.get(parent)
            gen = parents.get(call)
            comp = parents.get(gen)
            if (isinstance(call, ast.Call) and not call.args and not call.keywords
                    and isinstance(gen, ast.comprehension) and gen.iter is call
                    and isinstance(comp, ast.DictComp) and comp.generators == [gen]
                    and isinstance(gen.target, ast.Tuple) and len(gen.target.elts) == 2
                    and all(isinstance(x, ast.Name) for x in gen.target.elts)
                    and isinstance(comp.key, ast.Name) and isinstance(comp.value, ast.Name)):
                key, value = (x.id for x in gen.target.elts)
                if comp.key.id == key and comp.value.id == value:
                    sensitive = [cond for cond in gen.ifs if any(isinstance(x, ast.Name) and x.id == value
                                                                for x in ast.walk(cond))]
                    if all(isinstance(c, ast.Compare) and isinstance(c.left, ast.Name)
                           and c.left.id == value and len(c.ops) == 1 and isinstance(c.ops[0], (ast.Is, ast.IsNot))
                           and isinstance(c.comparators[0], ast.Constant) and c.comparators[0].value is None
                           for c in sensitive):
                        null_filter |= bool(sensitive)
                        node = comp
                        continue
        break
    if getattr(parent, "value", None) is node:
        target = target_of(parent)
        if isinstance(target, ast.Name):
            return target.id, null_filter
    return None, False


def build(root, maps):
    masks = [int(x, 16) for x in maps["masks"]]
    full = (1 << len(maps["ids"])) - 1
    sites, copies, declarations = defaultdict(int), defaultdict(set), set()
    nullable = defaultdict(int)
    for path in maps["layout"]:
        tree = ast.parse((root / path).read_bytes())
        parents = {child: n for n in ast.walk(tree) for child in ast.iter_child_nodes(n)}
        lines = maps["lines"].get(path, {})
        unknown = set(maps.get("warm_unknown", {}).get("lines", {}).get(path, ()))
        for node in ast.walk(tree):
            if (isinstance(parents.get(node), ast.ClassDef)
                    and isinstance(getattr(node, "value", None), (ast.Dict, ast.List, ast.Tuple))
                    and isinstance(target_of(node), ast.Name)):
                declarations.add(target_of(node).id)
            if isinstance(node, ast.ImportFrom):
                for alias in node.names:
                    if alias.asname:
                        copies[alias.name].add(alias.asname)
            name = name_of(node)
            if not name or not isinstance(node.ctx, ast.Load):
                if (isinstance(node, ast.Call) and name_of(node.func) in ("getattr", "hasattr")
                        and len(node.args) >= 2 and isinstance(node.args[1], ast.Constant)
                        and isinstance(node.args[1].value, str)):
                    name = node.args[1].value
                else:
                    continue
            ptr = lines.get(str(node.lineno))
            hits = full if node.lineno in unknown else masks[ptr] if ptr is not None else 0
            dest, null_filter = forwards_value(node, parents)
            if dest:
                copies[name].add(dest)
                if null_filter:
                    nullable[name] |= hits
                continue
            parent = parents.get(node)
            # Removing an existing dict key without using the popped value
            # cannot distinguish two replacements at the same key.
            if isinstance(parent, ast.Attribute) and parent.attr == "pop":
                call = parents.get(parent)
                if isinstance(call, ast.Call) and len(call.args) == 2 and isinstance(parents.get(call), ast.Expr):
                    continue
            sites[name] |= hits
    result = {}
    for name in sorted(declarations):
        pending, seen, bits = [name], set(), 0
        while pending:
            current = pending.pop()
            if current in seen:
                continue
            seen.add(current)
            bits |= sites[current]
            for table in ("dialect_reads", "raw_class_reads"):
                for key in (current, "*"):
                    ptr = maps[table].get(key)
                    if ptr is not None:
                        bits |= masks[ptr]
            pending.extend(copies[current] - seen)
        import_sensitive = 0
        for current in seen:
            import_sensitive |= nullable[current]
        result[name] = [hex(bits), hex(import_sensitive)]
    return result


if __name__ == "__main__":
    root, maps, dest = map(Path, sys.argv[1:])
    dest.write_text(json.dumps(build(root, json.loads(maps.read_bytes()))))
