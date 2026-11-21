"""Trace each numbered node, including imports and subprocesses, in a new interpreter."""
from collections import defaultdict
from concurrent.futures import ThreadPoolExecutor
import gzip
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import time


def trace_one(job):
    index, node, destination = job
    output = destination / f"{index}.json.gz"
    if output.exists():
        with gzip.open(output) as file:
            if json.load(file)["id"] != node:
                raise ValueError(f"Wrong checkpoint for {node}")
        return
    with tempfile.TemporaryDirectory() as tmp:
        env = {**os.environ, "BR_TRACES": tmp, "BR_COLD_TEST": node}
        run = subprocess.run([sys.executable, "-m", "pytest", "-q", "-p", "no:cacheprovider",
                              "-p", "trace_plugin", node], env=env,
                             stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        if run.returncode:
            raise RuntimeError(f"{node}: {run.stdout.decode(errors='replace')[-4000:]}")
        status = json.loads(Path(tmp, "status.json").read_bytes())
        if status != {"passed": [node], "skipped": []}:
            raise ValueError(f"{node}: {status}")
        key = "test:" + node
        files = {table: defaultdict(set) for table in ("lines", "entries")}
        names = {table: set() for table in ("loads", "opens", "class_reads", "read_names")}
        traces = list(Path(tmp).glob("[0-9]*.json"))
        if not traces:
            raise ValueError(f"No traces for {node}")
        for path in traces:
            blob = json.loads(path.read_bytes())
            for table, by_path in files.items():
                for name, lines in blob[table].get(key, {}).items():
                    by_path[name].update(lines)
            for table, seen in names.items():
                seen.update(blob[table].get(key, []))
        if not any(p.startswith("tests/") for p in files["lines"]):
            raise ValueError(f"No test source traced for {node}")
        result = {"id": node, **{k: sorted(v) for k, v in names.items()},
                  **{k: {p: sorted(v) for p, v in paths.items()} for k, paths in files.items()}}
        pending = output.with_suffix(".tmp")
        with gzip.open(pending, "wt", compresslevel=1) as file:
            json.dump(result, file, separators=(",", ":"))
        pending.replace(output)


def collect(out):
    maps = json.loads((out / "maps.json").read_bytes())
    destination = out / "cold"
    destination.mkdir(exist_ok=True)
    start = time.monotonic()
    jobs = [(i, node, destination) for i, node in enumerate(maps["ids"])]
    with ThreadPoolExecutor(max_workers=int(os.environ.get("BR_COLD_JOBS", "2"))) as pool:
        for count, _ in enumerate(pool.map(trace_one, jobs), 1):
            if count % 50 == 0 or count == len(jobs):
                print(f"Cold nodes {count}/{len(jobs)}, {time.monotonic()-start:.0f}s", flush=True)


if __name__ == "__main__":
    collect(Path("/out"))
