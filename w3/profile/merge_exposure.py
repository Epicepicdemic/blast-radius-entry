"""Merge pinned-suite parent and spawned-pool observations, then gzip reproducibly."""

import argparse
import gzip
import json
from pathlib import Path

p = argparse.ArgumentParser()
p.add_argument("traces", type=Path)
p.add_argument("dest", type=Path)
args = p.parse_args()
exp = json.loads((args.traces / "exposure.json").read_bytes())
keys = json.loads((args.traces / "keys.json").read_bytes())
assert exp["ids"] == keys["ids"] and not exp["exitstatus"] and not keys["exitstatus"]
ids = {tid: i for i, tid in enumerate(exp["ids"])}
done = set()


def put(table, group, key, bits):
    target = table.setdefault(group, {})
    target[key] = hex(int(target.get(key, "0"), 16) | bits)


for f in sorted((args.traces / "workers").glob("*.json")):
    d = json.loads(f.read_bytes())
    if not d["clients"]:
        continue
    client_bits = sum(1 << ids[t] for t in set(d["clients"]))
    done.update(d["clients"])
    # Gaps around dispatch include initializer and unpickling in a fresh process.
    # Attribute worker-global activity to every client of this process.
    for ctx, items in d["functions"].items():
        for path, fn, line in items:
            put(
                exp["rows"],
                path,
                f"{fn}:{line}",
                (1 << ids[ctx]) if ctx in ids else client_bits,
            )
    for ctx, items in d["keys"].items():
        for site, key in items:
            put(
                keys["rows"],
                site,
                "*" if key is None else "k" + key,
                (1 << ids[ctx]) if ctx in ids else client_bits,
            )
covered = sum(1 << ids[t] for t in done)
for name, tab in [("exposure", exp), ("keys", keys)]:
    tab["unknown"] = hex(int(tab["unknown"], 16) & ~covered)
    raw = json.dumps(tab, sort_keys=True, separators=(",", ":")).encode()
    (args.dest / (name + ".json.gz")).write_bytes(gzip.compress(raw, mtime=0))
print(
    "traced pool clients",
    len(done),
    "remaining unknown",
    int(exp["unknown"], 16).bit_count(),
)
