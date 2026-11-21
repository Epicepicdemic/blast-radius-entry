"""Union isolated observations with the warm and per-case maps, then intern once."""
import ast
from collections import defaultdict
import gzip
import json
from pathlib import Path

from index import read_sites
from statements import raw_namespace_lines


def merge(out):
    path = out / "maps.json"
    maps = json.loads(path.read_bytes())
    masks = [int(bits, 16) for bits in maps["masks"]]
    flat = ("users", "opens", "class_reads", "dialect_reads", "attributes", "keys", "raw_class_reads")
    counts = {key: defaultdict(int, {name: masks[i] for name, i in maps[key].items()})
              for key in flat}
    nested = {key: defaultdict(dict, {p: {int(n): masks[i] for n, i in rows.items()}
                                           for p, rows in maps[key].items()})
              for key in ("lines", "entries")}
    warm_lines = nested["lines"]
    nested["lines"] = defaultdict(dict)
    for i, node in enumerate(maps["ids"]):
        with gzip.open(out / "cold" / f"{i}.json.gz") as file:
            blob = json.load(file)
        if blob["id"] != node:
            raise ValueError(f"Cold trace {i} does not match {node}")
        bit = 1 << i
        for key in ("lines", "entries"):
            for p, points in blob[key].items():
                rows = nested[key][p]
                for n in points:
                    rows[n] = rows.get(n, 0) | bit
        for key, names in (("users", set(blob["loads"]) | blob["lines"].keys()),
                           ("opens", blob["opens"]), ("class_reads", blob["class_reads"]),
                           ("dialect_reads", blob["read_names"])):
            for name in names:
                counts[key][name] |= bit
    all_bits = (1 << len(maps["ids"])) - 1
    order_dependent = {}
    for p, warm in warm_lines.items():
        rows = nested["lines"][p]
        guarded = []
        for n, warm_bits in warm.items():
            cold_bits = rows.get(n, 0)
            if p.startswith("sqlglot/") and warm_bits != all_bits and warm_bits & ~cold_bits:
                guarded.append(n)
            rows[n] = warm_bits | cold_bits
        if guarded:
            order_dependent[p] = sorted(guarded)
    # Import closure and indirect attribute/key reads use the enlarged line masks.
    changed = True
    while changed:
        changed = False
        for parent, imports in maps["imports"].items():
            for child in imports:
                added = counts["users"][parent] & ~counts["users"][child]
                if added:
                    counts["users"][child] |= added
                    changed = True
    for p in maps["layout"]:
        lines = nested["lines"].get(p, {})
        tree = ast.parse(Path(p).read_bytes())
        for n, name in raw_namespace_lines(tree):
            counts["raw_class_reads"][str(name)] |= lines.get(n, 0)
        for node in ast.walk(tree):
            bits = lines.get(getattr(node, "lineno", 0), 0)
            if bits:
                for table, name in read_sites(node):
                    counts[table][name] |= bits

    # Widen line selection and line-based proofs only. Derived readers above
    # use the observed union, as they did before the order-dependence guard.
    maps["order_dependent_lines"] = order_dependent
    for p, points in order_dependent.items():
        for n in points:
            nested["lines"][p][n] = all_bits

    # The line and data-file rules interpret absent warm evidence as "run all".
    # Keep that fallback while exposing the measured union to every other reader.
    prior = maps.get("warm_unknown", {})
    new_lines = {}
    for p, rows in nested["lines"].items():
        known = maps["lines"].get(p, {})
        unseen = sorted(set(prior.get("lines", {}).get(p, ())) | {n for n in rows if str(n) not in known})
        if unseen:
            new_lines[p] = unseen
    maps["warm_unknown"] = {
        "lines": new_lines,
        "opens": sorted(set(prior.get("opens", ())) | (counts["opens"].keys() - maps["opens"].keys())),
        "users": sorted(set(prior.get("users", ())) |
                        {p for p, bits in counts["users"].items() if bits and p not in maps["users"]}),
    }
    interned = {}
    def encode(rows):
        return {str(key): interned.setdefault(bits, len(interned))
                for key, bits in sorted(rows.items()) if bits}

    for key, rows in counts.items():
        maps[key] = encode(rows)
    for key, files in nested.items():
        maps[key] = {p: encode(rows) for p, rows in sorted(files.items()) if rows}
    maps["masks"] = [hex(bits) for bits in interned]
    pending = path.with_suffix(".tmp")
    pending.write_text(json.dumps(maps, separators=(",", ":")) + "\n")
    pending.replace(path)


if __name__ == "__main__":
    merge(Path("/out"))
