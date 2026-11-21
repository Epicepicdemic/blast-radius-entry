"""Independent cold traces with one shared context and one bit per real query/call."""
import ast
from collections import defaultdict
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile

from index import read_sites
from statements import raw_namespace_lines

TARGETS = (
    "tests/test_executor.py::TestExecutor::test_execute_tpcds",
    "tests/test_parser.py::TestParser::test_max_nodes",
)


def reduce_cases(directory, target):
    status = json.loads((directory / "status.json").read_bytes())
    if status != {"passed": [target], "skipped": []}:
        raise ValueError(f"Incomplete cold test: {status}")
    blobs = [json.loads(p.read_bytes()) for p in sorted(directory.glob("[0-9]*.json"))]
    labels = {ctx for b in blobs for ctx in b["lines"] if ctx.startswith("case:")}
    contexts = ["shared"] + sorted(labels, key=lambda k: int(k.split("/")[-1]))
    if len(contexts) < 2:
        raise ValueError("No cases observed")
    bits = {ctx: 1 << i for i, ctx in enumerate(contexts)}
    output = {}
    for table in ("entries", "lines"):
        values = defaultdict(lambda: defaultdict(int))
        for b in blobs:
            for ctx, paths in b[table].items():
                for p, lines in paths.items():
                    for n in lines:
                        values[p][n] |= bits.get(ctx, 1)
        output[table] = values
    for table in ("opens", "class_reads", "dialect_reads"):
        key = "read_names" if table == "dialect_reads" else table
        output[table] = values = defaultdict(int)
        for b in blobs:
            for ctx, names in b[key].items():
                for name in names:
                    values[name] |= bits.get(ctx, 1)
    for table in ("attributes", "keys", "raw_class_reads"):
        output[table] = defaultdict(int)
    for p, lines in output["lines"].items():
        if not p.endswith(".py"):
            continue
        tree = ast.parse(Path(p).read_bytes())
        for n, name in raw_namespace_lines(tree):
            output["raw_class_reads"][str(name)] |= lines.get(n, 0)
        for node in ast.walk(tree):
            hit = lines.get(getattr(node, "lineno", 0), 0)
            if not hit:
                continue
            for table, key in read_sites(node):
                output[table][key] |= hit
    intern = {}
    def encode(values):
        return {str(k): encode(v) if isinstance(v, dict) else intern.setdefault(v,len(intern))
                for k,v in sorted(values.items()) if v}
    encoded = encode(output)
    encoded.update(contexts=contexts, masks=[hex(x) for x in intern])
    return encoded


def merge_cases(maps, reports):
    masks = {int(x,16):i for i,x in enumerate(maps["masks"])}
    def merge(old, evidence, bit):
        for k, val in evidence.items():
            if isinstance(val, dict):
                merge(old.setdefault(k, {}), val, bit)
            else:
                previous = int(maps["masks"][old[k]],16) if k in old else 0
                new = previous | bit
                if new not in masks:
                    masks[new] = len(maps["masks"])
                    maps["masks"].append(hex(new))
                old[k] = masks[new]
    for target, report in reports.items():
        bit = 1 << maps["ids"].index(target)
        for table in ("lines","entries","opens","class_reads","dialect_reads","attributes","keys","raw_class_reads"):
            merge(maps[table], report[table], bit)
        merge(maps["users"], {p:1 for p in report["lines"]}, bit)


def collect_cases(out):
    reports = {}
    for target in TARGETS:
        with tempfile.TemporaryDirectory() as tmp:
            subprocess.run([sys.executable,"-m","pytest","-p","trace_plugin","-p","case_plugin","-q",target],
                           env={**os.environ,"BR_TRACES":tmp}, check=True)
            reports[target] = reduce_cases(Path(tmp), target)
    (out / "case-coverage.json").write_text(json.dumps(reports,separators=(",",":"))+"\n")
    path = out / "maps.json"
    maps = json.loads(path.read_bytes())
    merge_cases(maps, reports)
    path.write_text(json.dumps(maps,separators=(",",":"))+"\n")


if __name__ == "__main__":
    collect_cases(Path("/out"))
