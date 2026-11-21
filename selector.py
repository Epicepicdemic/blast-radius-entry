"""Choose tests using only dependencies measured on the unmodified checkout."""
import os
import sys


def main():
    # Keep a private result stream even if an import writes to fd 1.
    output = os.fdopen(os.dup(1), "w", encoding="utf-8")
    os.dup2(2, 1)
    import json
    from pathlib import Path
    from packing import pack
    from patching import apply_patch

    root = Path("/sqlglot")
    data = Path("/data")
    index = Index(json.loads(Path(__file__).with_name("maps.json").read_bytes()))
    tests = json.loads((data / "tests.json").read_bytes())["tests"]
    numbers = {t["id"]: t["number"] for t in tests}
    # Both fail when the unmodified pinned suite runs in reverse order.
    reverse_failures = {numbers[name] for name in (
        "tests/dialects/test_dialect.py::TestDialect::test_enum",
        "tests/dialects/test_starrocks.py::TestStarrocks::test_time_slice_origin_roundtrip",
    ) if name in numbers}
    durations = {t["number"]: round(t["seconds"] * 1000) for t in tests}
    ranked = sorted(durations, key=lambda t: (-durations[t], t))
    positions = [numbers.get(name) for name in index.ids]
    unknown = set(ranked) - set(positions)

    def translate(mask):
        return {t for i, t in enumerate(positions) if t is not None and mask & (1 << i)}

    for patch in sorted((data / "commits").glob("*.patch")):
        try:
            selected = related = 0
            changes = apply_patch(patch.read_bytes(), root)
            for change in changes:
                required, nearby = index.select(change, certificates=len(changes) == 1)
                selected |= required
                related |= nearby
            required = translate(selected) | unknown
            if required:
                required.update(reverse_failures)
            preferred = translate(related) if selected else set()
        except (OSError, ValueError, SyntaxError, RecursionError, OverflowError):
            required, preferred = set(ranked), set()
        workers = pack(required, ranked, durations, preferred)
        print(json.dumps({"commit": patch.stem, "workers": workers}, separators=(",", ":")), file=output)
    output.close()


import ast
import marshal
from shared_writes import has_shared_write
from proofs import baseline_code, comparison_candidate, delayed_literal, opcode_lines, scope_changed
from functools import lru_cache


@lru_cache(maxsize=32)
def original_tree(source):
    return ast.parse(source, type_comments=True)


def equal_trees(a, b, *, headers_only=False):
    if type(a) is not type(b):
        return False
    if isinstance(a, ast.AST):
        # TypeIgnore.lineno is a semantic field pointing to a directive's
        # target. Keeping it makes the proof conservative when directives move.
        return all(equal_trees(getattr(a, k, None), getattr(b, k, None), headers_only=headers_only)
                   for k in a._fields
                   if not (headers_only and k == "body" and isinstance(a, (ast.FunctionDef, ast.AsyncFunctionDef))))
    if isinstance(a, list):
        return len(a) == len(b) and all(equal_trees(x, y, headers_only=headers_only) for x, y in zip(a, b))
    if isinstance(a, (float, complex)):
        return marshal.dumps(a, 2) == marshal.dumps(b, 2)
    return a == b


class Index:
    def __init__(self, data):
        self.data = data
        self.warm_unknown = data.get("warm_unknown", {})
        self.ids = data["ids"]
        self.all = (1 << len(self.ids)) - 1
        self.masks = [int(x, 16) for x in data["masks"]]

    def bits(self, table, key):
        pointer = self.data[table].get(key)
        return 0 if pointer is None else self.masks[pointer]

    def point(self, table, path, lineno):
        pointer = self.data[table].get(path, {}).get(str(lineno))
        return 0 if pointer is None else self.masks[pointer]

    def select(self, change, certificates=True):
        path = change.path
        opened = self.bits("opens", path)
        if not path.endswith(".py"):
            if path in self.warm_unknown.get("opens", ()):
                return self.all, 0
            return opened or self.all, 0
        users = self.bits("users", path)
        if not users or path not in self.data["layout"] or path in self.warm_unknown.get("users", ()):
            return self.all, 0
        # Replacements touch old lines. Insertions sit between two old lines.
        # Guard these coordinates before AST equality or a certificate can return.
        points = change.removed | change.insertions | {i + 1 for i in change.insertions}
        if not points.isdisjoint(self.data.get("order_dependent_lines", {}).get(path, ())):
            return self.all, users
        # compile() catches errors which ast.parse() alone would allow,
        # including misplaced break/nonlocal/return declarations.
        try:
            compiled = compile(change.after, path, "exec", dont_inherit=True)
        except (ValueError, SyntaxError):
            return self.all, 0
        before = after = None
        try:
            before = original_tree(change.before)
            after = ast.parse(change.after, type_comments=True)
            if path.startswith("sqlglot/") and (
                has_shared_write(before, change.removed) or has_shared_write(after, change.added)
            ):
                return self.all, users
            same = equal_trees(before, after)
            import_effect = not same and not equal_trees(before, after, headers_only=True)
        except (ValueError, SyntaxError):
            return self.all, users
        if same:
            return opened, users

        # The pinned suite also compares code objects without calling them.
        opened |= self.bits("attributes", "__code__") | self.bits("attributes", "__closure__")
        lines = self.data["lines"].get(path, {})
        if path.startswith("tests/"):
            return self.all, users
        if not import_effect and scope_changed(baseline_code(change.before, path), compiled):
            return self.all, users
        if certificates:
            proof = self.certificate(change, before, after, compiled, import_effect)
            if proof is not None:
                return opened | proof[1], users

        if (import_effect or change.insertions
                or not change.removed.isdisjoint(self.warm_unknown.get("lines", {}).get(path, ()))):
            return self.all, users
        functions, bindings = self.data["layout"][path]
        required = opened
        # A physical line inside a statement can be skipped on the baseline
        # (short-circuiting, comprehensions, conditional expressions). Its
        # siblings and entry lines still establish dependence on that statement.
        for first, last in self.data["statements"][path]:
            if any(first <= point <= last for point in change.removed):
                required |= self.range_users(lines, first, last)
        for point in sorted(change.removed):
            ptr = lines.get(str(point))
            # Outside a function body this could change a decorator, default,
            # class registry or module import. Include transitive importers.
            owners = [(a,b) for a,b in functions if a < point <= b]
            if not owners:
                required |= self.all
            if ptr is not None:
                required |= self.masks[ptr]
            else:
                return self.all, users
        for first, last, names, entries in bindings:
            if any(first <= n <= last for n in points):
                for name in names:
                    required |= self.bits("attributes", name)
                for i, (begin, end, key) in enumerate(entries):
                    # Changing a value also affects readers of its key. At
                    # boundaries include both adjacent entries conservatively.
                    boundary = entries[i + 1][0] if i + 1 < len(entries) else last
                    if any(begin <= n <= max(end, boundary) for n in points):
                        required |= self.bits("keys", key)
        return required or self.all, users

    def certificate(self, change, before, after, compiled, import_effect):
        path = change.path
        if (not path.startswith("sqlglot/") or change.insertions or len(change.removed) != 1
                or before is None or after is None):
            return None
        if import_effect:
            return delayed_literal(self, before, after, change)
        if not comparison_candidate(change):
            return None
        points = set()
        if not opcode_lines(baseline_code(change.before, path), compiled, points) or not points:
            return None
        mask = 0
        lines = self.data["lines"].get(path, {})
        for n in points:
            mask |= self.point("lines", path, n)
            for first, last in self.data["statements"][path]:
                if first <= n <= last:
                    mask |= self.range_users(lines, first, last)
        return "compiled comparison", mask

    def range_users(self, lines, first, last):
        result = 0
        for n in range(first, last + 1):
            ptr = lines.get(str(n))
            if ptr is not None:
                result |= self.masks[ptr]
        return result


if __name__ == "__main__":
    main()
