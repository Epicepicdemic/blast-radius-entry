"""Independent cold traces with one shared context and one bit per real query/call/row."""
import ast
from collections import defaultdict
from concurrent.futures import ThreadPoolExecutor
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

EXTRA_TARGETS = (
    "tests/test_executor.py::TestExecutor::test_execute_tpch",
    "tests/test_executor.py::TestExecutor::test_optimized_tpch",
    "tests/test_generator.py::TestGenerator::test_generator_memory",
    "tests/test_schema.py::TestSchema::test_cache_does_not_retain_queries",
    "tests/test_serde.py::TestSerde::test_serde",
    "tests/test_transpile.py::TestTranspile::test_identity",
    "tests/test_transpile.py::TestTranspile::test_partial",
    "tests/test_transpile.py::TestTranspile::test_pretty",
    "tests/test_optimizer.py::TestOptimizer::test_optimize",
    "tests/test_optimizer.py::TestOptimizer::test_isolate_table_selects",
    "tests/test_optimizer.py::TestOptimizer::test_qualify_tables",
    "tests/test_optimizer.py::TestOptimizer::test_normalize",
    "tests/test_optimizer.py::TestOptimizer::test_qualify_columns",
    "tests/test_optimizer.py::TestOptimizer::test_qualify_columns__with_invisible",
    "tests/test_optimizer.py::TestOptimizer::test_pushdown_cte_alias_columns",
    "tests/test_optimizer.py::TestOptimizer::test_qualify_columns__invalid",
    "tests/test_optimizer.py::TestOptimizer::test_normalize_identifiers",
    "tests/test_optimizer.py::TestOptimizer::test_quote_identifiers",
    "tests/test_optimizer.py::TestOptimizer::test_pushdown_projection",
    "tests/test_optimizer.py::TestOptimizer::test_simplify",
    "tests/test_optimizer.py::TestOptimizer::test_unnest_subqueries",
    "tests/test_optimizer.py::TestOptimizer::test_pushdown_predicates",
    "tests/test_optimizer.py::TestOptimizer::test_optimize_joins",
    "tests/test_optimizer.py::TestOptimizer::test_eliminate_joins",
    "tests/test_optimizer.py::TestOptimizer::test_eliminate_ctes",
    "tests/test_optimizer.py::TestOptimizer::test_merge_subqueries",
    "tests/test_optimizer.py::TestOptimizer::test_eliminate_subqueries",
    "tests/test_optimizer.py::TestOptimizer::test_canonicalize_internal_names",
    "tests/test_optimizer.py::TestOptimizer::test_canonicalize",
    "tests/test_optimizer.py::TestOptimizer::test_tpch",
    "tests/test_optimizer.py::TestOptimizer::test_tpcds",
    "tests/test_optimizer.py::TestOptimizer::test_annotate_types",
    "tests/test_optimizer.py::TestOptimizer::test_annotate_funcs",
    "tests/test_optimizer.py::TestOptimizer::test_optimize_in_nulls",
)

ALL_TARGETS = TARGETS + EXTRA_TARGETS


def _context_sort_key(ctx):
    body = ctx[5:] if ctx.startswith("case:") else ctx
    if "#" in body:
        prefix, idx = body.rsplit("#", 1)
        return (2, prefix, int(idx), "")
    parts = body.split("/")
    kind = parts[0]
    if kind == "executor":
        return (0, "", int(parts[1]), "")
    if kind == "phase2":
        return (1, "", int(parts[1]), "")
    if kind == "dialect":
        return (3, kind, int(parts[1]), parts[2] if len(parts) > 2 else "")
    return (4, kind, int(parts[-1]), body)


def reduce_cases(directory, target):
    status = json.loads((directory / "status.json").read_bytes())
    if status != {"passed": [target], "skipped": []}:
        raise ValueError(f"Incomplete cold test: {status}")
    blobs = [json.loads(p.read_bytes()) for p in sorted(directory.glob("[0-9]*.json"))]
    labels = {ctx for b in blobs for ctx in b["lines"] if ctx.startswith("case:")}
    contexts = ["shared"] + sorted(labels, key=_context_sort_key)
    if len(contexts) < 2:
        raise ValueError(f"No cases observed for {target}")
    bits = {ctx: 1 << i for i, ctx in enumerate(contexts)}
    ns_by_ctx = defaultdict(int)
    for b in blobs:
        for ctx, ns_val in b.get("case_ns", {}).items():
            ns_by_ctx[ctx] += ns_val
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
        return {
            str(k): encode(v) if isinstance(v, dict) else intern.setdefault(v, len(intern))
            for k, v in sorted(values.items())
            if v
        }

    encoded = encode(output)
    encoded.update(
        contexts=contexts,
        masks=[hex(x) for x in intern],
        times_us=[round(ns_by_ctx.get(ctx, 0) / 1000) for ctx in contexts],
    )
    return encoded


def merge_cases(maps, reports):
    masks = {int(x, 16): i for i, x in enumerate(maps["masks"])}

    def merge(old, evidence, bit):
        for k, val in evidence.items():
            if isinstance(val, dict):
                merge(old.setdefault(k, {}), val, bit)
            else:
                previous = int(maps["masks"][old[k]], 16) if k in old else 0
                new = previous | bit
                if new not in masks:
                    masks[new] = len(maps["masks"])
                    maps["masks"].append(hex(new))
                old[k] = masks[new]

    for target, report in reports.items():
        if target not in TARGETS:
            continue
        bit = 1 << maps["ids"].index(target)
        for table in ("lines", "entries", "opens", "class_reads", "dialect_reads", "attributes", "keys", "raw_class_reads"):
            merge(maps[table], report[table], bit)
        merge(maps["users"], {p: 1 for p in report["lines"]}, bit)


def _trace_one(target):
    with tempfile.TemporaryDirectory() as tmp:
        env = {**os.environ, "BR_TRACES": tmp, "BR_PHASE2_SPLIT": "1"}
        subprocess.run(
            [sys.executable, "-m", "pytest", "-p", "trace_plugin", "-p", "case_plugin", "-q", target],
            env=env,
            check=True,
        )
        return target, reduce_cases(Path(tmp), target)


def collect_cases(out, targets=ALL_TARGETS, merge=True):
    reports = {}
    workers = int(os.environ.get("BR_CASE_JOBS", "4"))
    with ThreadPoolExecutor(max_workers=workers) as ex:
        for target, rep in ex.map(_trace_one, targets):
            reports[target] = rep
            print(f"Case traced: {target} ({len(rep['contexts'])} contexts, {len(rep['masks'])} masks)", flush=True)
    ordered = {t: reports[t] for t in targets}
    (out / "case-coverage.json").write_text(json.dumps(ordered, separators=(",", ":")) + "\n")
    if merge:
        path = out / "maps.json"
        if path.exists():
            maps = json.loads(path.read_bytes())
            merge_cases(maps, ordered)
            path.write_text(json.dumps(maps, separators=(",", ":")) + "\n")


if __name__ == "__main__":
    only_extra = os.environ.get("BR_ONLY_CASES") == "1"
    collect_cases(Path("/out"), ALL_TARGETS, merge=not only_extra)
