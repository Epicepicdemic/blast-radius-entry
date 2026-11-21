"""Identify pinned test methods that share subprocess or serialization behavior."""
import ast
import json
from pathlib import Path
import sys


def pool_readers(root, ids):
    by_file = {}
    for test_id in ids:
        path, *node = test_id.split("::")
        by_file.setdefault(path, []).append((test_id, node))
    protected = set()
    for path, tests in by_file.items():
        source = (root / path).read_bytes()
        if not any(token in source for token in (b"multiprocessing", b"ProcessPool", b"pickle")):
            continue
        tree = ast.parse(source)
        # Follow calls to file-level helpers, self methods and callbacks passed
        # by name. Repeated names across classes join rather than losing an edge.
        references = {}
        operations = set()
        for fn in ast.walk(tree):
            if not isinstance(fn, (ast.FunctionDef, ast.AsyncFunctionDef)):
                continue
            refs = references.setdefault(fn.name, set())
            for node in ast.walk(fn):
                if isinstance(node, ast.Name):
                    refs.add(node.id)
                elif isinstance(node, ast.Attribute):
                    refs.add(node.attr)
                    if node.attr in ("submit", "starmap", "map_async", "apply_async"):
                        operations.add(fn.name)
                    if node.attr == "map" and isinstance(node.value, ast.Attribute) and node.value.attr == "pool":
                        operations.add(fn.name)
            if refs.intersection({"pickle", "dumps", "loads", "ProcessPoolExecutor", "Pool"}):
                # Constructing an idle class pool does not submit a job. Its
                # constructor only receives a multiprocessing context at the pin.
                creates_idle_pool = (fn.name == "setUpClass" and refs.isdisjoint({"submit", "map", "pickle", "dumps", "loads"})
                                     and "ProcessPoolExecutor" in refs)
                if not creates_idle_pool:
                    operations.add(fn.name)
        while True:
            callers = {name for name, refs in references.items() if refs & operations}
            if callers <= operations:
                break
            operations.update(callers)
        fixture = operations.intersection({"setUp", "setUpClass", "setUpModule", "tearDown", "tearDownClass", "tearDownModule"})
        for test_id, node in tests:
            if fixture or len(node) != 2 or node[-1] not in references or node[-1] in operations:
                protected.add(test_id)
    return sorted(protected)


if __name__ == "__main__":
    root, maps, dest = map(Path, sys.argv[1:])
    dest.write_text(json.dumps(pool_readers(root, json.loads(maps.read_bytes())["ids"])))
