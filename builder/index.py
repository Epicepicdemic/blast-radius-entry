"""Resolve trace contexts, import closure and data readers once, before shipping."""
import ast
import importlib.util
import json
import sqlite3
import sys
from collections import defaultdict
from pathlib import Path

from statements import class_metadata, closure_factories, spans


def module_name(path):
    return path.removesuffix(".py").replace("/", ".").removesuffix(".__init__")


def dependencies(modules, trees):
    graph = defaultdict(set)
    for path, tree in trees.items():
        name = module_name(path)
        package = name if path.endswith("/__init__.py") else name.rpartition(".")[0]
        names = []
        for node in ast.walk(tree):
            if isinstance(node, ast.Import):
                names.extend(a.name for a in node.names)
            elif isinstance(node, ast.ImportFrom):
                try:
                    base = importlib.util.resolve_name("." * node.level + (node.module or ""), package)
                except ImportError:
                    continue
                names.append(base)
                names.extend(base + "." + a.name for a in node.names)
        names.append(name)
        for target in names:
            while target:
                if target in modules and modules[target] != path:
                    graph[path].add(modules[target])
                target = target.rpartition(".")[0]
    return graph


def data_key(node):
    if isinstance(node, ast.Constant) and isinstance(node.value, (str, int)):
        return repr(node.value)
    if isinstance(node, ast.Attribute):
        return "." + node.attr
    return None


def read_sites(node):
    if isinstance(node, ast.Attribute) and isinstance(node.ctx, ast.Load):
        yield "attributes", node.attr
    elif isinstance(node, ast.Name) and isinstance(node.ctx, ast.Load):
        yield "attributes", node.id
    elif isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id in ("getattr", "hasattr"):
        if len(node.args) >= 2 and isinstance(node.args[1], ast.Constant) and isinstance(node.args[1].value, str):
            yield "attributes", node.args[1].value
    key = None
    if isinstance(node, ast.Subscript) and isinstance(node.ctx, ast.Load):
        key = data_key(node.slice)
    elif isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute) and node.func.attr in ("get", "pop", "setdefault") and node.args:
        key = data_key(node.args[0])
    if key is not None:
        yield "keys", key


def build(directory, destination):
    trace = Path(directory)
    inventory = json.loads((trace / "items.json").read_text())
    status = json.loads((trace / "status.json").read_text())
    ids = sorted(status["passed"])
    assert set(ids).isdisjoint(status["skipped"])
    assert set(ids) | set(status["skipped"]) == set(inventory)
    scopes = defaultdict(int)
    scopes["collect:"] = (1 << len(ids)) - 1
    users = defaultdict(int)
    bits = {}
    for i, name in enumerate(ids):
        bit = bits[name] = 1 << i
        path = name.split("::")[0]
        users[path] |= bit
        scopes["test:" + name] = bit
        scopes["collect:" + path] |= bit
        for ancestor in inventory[name]:
            scopes["scope:" + ancestor] |= bit

    trees = {str(p): ast.parse(p.read_bytes()) for root in ("sqlglot", "tests", "sqlglotc")
             for p in Path(root).rglob("*.py")}
    modules = {module_name(p): p for p in trees}
    graph = dependencies(modules, trees)
    traces = [json.loads(f.read_text()) for f in sorted(trace.glob("[0-9]*.json"))]
    for blob in traces:
        for ctx in blob["submitters"]:
            scopes["pool"] |= scopes[ctx]
    # Every function a test executes is evidence it uses the containing module,
    # including dynamic dispatch and imports static resolution can't discover.
    for blob in traces:
        for ctx in set(blob["lines"]) | set(blob["loads"]):
            paths = set(blob["lines"].get(ctx, {})) | set(blob["loads"].get(ctx, []))
            if ctx.startswith("module:"):
                graph[ctx[7:]].update(paths - {ctx[7:]})
            else:
                for p in paths:
                    users[p] |= scopes[ctx]
    changed = True
    while changed:
        changed = False
        for parent, imports in graph.items():
            for child in imports:
                more = users[parent] & ~users[child]
                if more:
                    users[child] |= more
                    changed = True

    # An import can publish values through registries with no Python import
    # edge back to their eventual consumers. Any dependency actually observed
    # during initialization or collection is shared across the whole suite.
    all_tests = (1 << len(ids)) - 1
    for p in trees:
        scopes["module:" + p] = all_tests
    for ctx in list(scopes):
        if ctx.startswith("collect:"):
            scopes[ctx] = all_tests
    lines = defaultdict(lambda: defaultdict(int))
    class_reads = defaultdict(int)
    dialect_reads = defaultdict(int)
    entries = defaultdict(lambda: defaultdict(int))
    opens = defaultdict(int)
    for blob in traces:
        for ctx, paths in blob["lines"].items():
            for p, hits in paths.items():
                for n in hits:
                    lines[p][n] |= scopes[ctx]
        for ctx, names in blob["class_reads"].items():
            for name in names:
                class_reads[name] |= scopes[ctx]
        for ctx, names in blob["read_names"].items():
            for name in names:
                dialect_reads[name] |= scopes[ctx]
        for ctx, paths in blob["entries"].items():
            for p, hits in paths.items():
                for n in hits:
                    entries[p][n] |= scopes[ctx]
        for ctx, paths in blob["opens"].items():
            for p in paths:
                opens[p] |= scopes[ctx]

    masks = {}
    def intern(bits):
        return masks.setdefault(bits, len(masks))

    def encode(table):
        return {k: intern(v) for k, v in sorted(table.items()) if v}

    # Connect covered attribute, name and literal-key reads to definitions.
    attributes = defaultdict(int)
    keys = defaultdict(int)
    read_tables = {"attributes": attributes, "keys": keys}
    layouts = {}
    for p, tree in trees.items():
        bindings = []
        functions = []
        for node in ast.walk(tree):
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                functions.append([node.lineno, node.end_lineno])
            hits = lines[p].get(getattr(node, "lineno", 0), 0)
            if not hits:
                continue
            for table, key in read_sites(node):
                read_tables[table][key] |= hits

        def declarations(node):
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda)):
                return
            if isinstance(node, (ast.Assign, ast.AnnAssign)):
                targets = node.targets if isinstance(node, ast.Assign) else [node.target]
                names = sorted({x.id for t in targets for x in ast.walk(t) if isinstance(x, ast.Name) and isinstance(x.ctx, ast.Store)})
                entries = []
                if isinstance(node.value, ast.Dict):
                    entries = [[k.lineno, k.end_lineno, data_key(k)] for k in node.value.keys if k and data_key(k) is not None]
                bindings.append([node.lineno, node.end_lineno, names, entries])
            for child in ast.iter_child_nodes(node):
                declarations(child)
        declarations(tree)
        layouts[p] = [sorted(functions), bindings]

    raw, initialization = class_metadata(trees, lines)
    result = {"raw_class_reads": encode(raw), "tokenizer_init_names": initialization, "ids": ids, "skipped": sorted(status["skipped"]), "imports": {p: sorted(v) for p,v in sorted(graph.items())},
              "users": encode(users), "opens": encode(opens), "attributes": encode(attributes),
              "keys": encode(keys), "layout": layouts,
              "statements": {p: spans(tree) for p, tree in trees.items()},
              "class_reads": encode(class_reads),
              "factories": closure_factories(trees),
              "dialect_reads": encode(dialect_reads),
              "entries": {p: encode(v) for p,v in sorted(entries.items()) if v},
              "lines": {p: encode(v) for p,v in sorted(lines.items()) if v},
              "masks": [hex(k) for k in masks],
              "environment": [sys.version, sqlite3.sqlite_version]}
    Path(destination).write_text(json.dumps(result, separators=(",", ":")) + "\n")
    print(f"{len(ids)} passing, {len(status['skipped'])} skipped; {len(masks)} distinct sets; {Path(destination).stat().st_size} bytes.")
