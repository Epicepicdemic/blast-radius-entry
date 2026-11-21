"""Pinned import dependencies and readers that can observe a re-exported binding."""
import ast
from collections import defaultdict
from importlib.util import resolve_name
import json
from pathlib import Path
import sys

from mutation_summaries import module_name


def target(node, package):
    if isinstance(node, ast.ImportFrom):
        return resolve_name("." * node.level + (node.module or ""), package)
    return None


def build(root, maps):
    readers, eager, exports = defaultdict(int), {}, {}
    masks = [int(m, 16) for m in maps["masks"]]
    full = (1 << len(maps["ids"])) - 1
    for path in maps["layout"]:
        module = module_name(path)
        package = module if path.endswith("/__init__.py") else module.rpartition(".")[0]
        tree = ast.parse((root/path).read_bytes())
        imports = set()
        available = set()
        for node in tree.body:
            if isinstance(node, ast.Import):
                imports.update(a.name for a in node.names)
            elif isinstance(node, ast.ImportFrom):
                try:
                    imports.add(target(node, package))
                except (ImportError, ValueError):
                    pass
            elif isinstance(node, (ast.ClassDef, ast.FunctionDef, ast.AsyncFunctionDef)):
                available.add(node.name)
        eager[module] = sorted(imports)
        exports[module] = sorted(available)
        ptr = maps["users"].get(path)
        bits = full if ptr is None else masks[ptr]
        for node in ast.walk(tree):
            if isinstance(node, ast.ImportFrom):
                try:
                    source = target(node, package)
                except (ImportError, ValueError):
                    continue
                for alias in node.names:
                    readers[source + ":" + alias.name] |= bits
    return {"eager": eager, "exports": exports, "from": {k: hex(v) for k, v in readers.items()}}


if __name__ == "__main__":
    root, maps, dest = map(Path, sys.argv[1:])
    dest.write_text(json.dumps(build(root, json.loads(maps.read_bytes()))))
