"""Run the pinned suite under the census plugin in fixed shards (image build time).

usage: python census_run.py ROOT OUT_DIR SHARDS
Test files are assigned to shards by a fixed rule (sorted, round-robin by size),
each shard runs in its own process in file order, and every shard must pass.
"""
import os
import subprocess
import sys
from pathlib import Path

root, out, shards = Path(sys.argv[1]), Path(sys.argv[2]), int(sys.argv[3])
files = sorted(str(p.relative_to(root)) for p in (root / "tests").rglob("test_*.py"))
files.sort(key=lambda f: -(root / f).stat().st_size)
groups = [sorted(files[i::shards]) for i in range(shards)]
out.mkdir(parents=True, exist_ok=True)
env = dict(os.environ, PYTHONHASHSEED="0", PYTHONPATH=f"{Path(__file__).parent}:{root}",
           SKIP_INTEGRATION=os.environ.get("SKIP_INTEGRATION", "0"))
procs = []
for i, group in enumerate(groups):
    e = dict(env, CENSUS_OUT=str(out / f"census{i}.json"))
    log = open(out / f"shard{i}.log", "w")
    procs.append((subprocess.Popen([sys.executable, "-m", "pytest", "-q", "-p", "no:cacheprovider",
                                    "-p", "census_plugin", "--timeout=600", *group],
                                   cwd=root, env=e, stdout=log, stderr=subprocess.STDOUT), log))
failed = 0
for i, (p, log) in enumerate(procs):
    rc = p.wait()
    log.close()
    tail = (out / f"shard{i}.log").read_text().strip().splitlines()[-1:]
    print(f"census shard {i}: rc={rc} {tail}", flush=True)
    failed |= rc != 0
if failed:
    sys.exit("census: a shard failed")
