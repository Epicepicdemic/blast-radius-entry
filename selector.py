"""Choose tests using only dependencies measured on the unmodified checkout."""
import os
import sys
from time import monotonic


def _env_flag(name, default=True):
    val = os.environ.get(name)
    if val is None or not val.strip():
        return default
    return val.strip().lower() not in ("0", "false", "no", "off")


def main():
    started = monotonic()
    from bounded_batch import BATCH_SECONDS, bounded_results

    # Keep a private result stream even if an import writes to fd 1.
    output = os.fdopen(os.dup(1), "w", encoding="utf-8")
    os.dup2(2, 1)
    import json
    from pathlib import Path
    from packing import pack
    from patching import read_patch

    use_isolation_drop = _env_flag("ISOLATION_DROP", True)
    use_engine_skip = _env_flag("ENGINE_SKIP", True)

    root = Path("/sqlglot")
    data = Path("/data")
    fast = _env_flag("FAST_ANALYSIS")
    from pinned_data import load
    index = Index(load(Path(__file__).with_name("maps.json"), fast),
                  Project(load(Path(__file__).with_name("mutations.json"), fast)),
                  root=root)
    tests = json.loads((data / "tests.json").read_bytes())["tests"]
    numbers = {t["id"]: t["number"] for t in tests}
    names = {t["number"]: t["id"] for t in tests}
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

    full_plan = pack(set(ranked), ranked, durations)

    runner = None
    tpcds_num = None
    if use_isolation_drop or use_engine_skip:
        from runner import (
            LiveRunner,
            SLOW_UNITTEST_FILES,
            TPCDS_BACKEND_FILES,
            TPCDS_BACKEND_PREFIXES,
            TPCDS_TEST_ID,
        )
        runner = LiveRunner(root)
        tpcds_num = numbers.get(TPCDS_TEST_ID)

    def analyze(path):
        return index.select_changes(read_patch(path, root))

    deadline = started + BATCH_SECONDS
    patches = sorted((data / "commits").glob("*.patch"))
    try:
        for patch, result in bounded_results(patches, analyze, deadline):
            if result is None or result[0] == index.all:
                workers = full_plan
            else:
                selected, related = result
                raw_required = translate(selected) | unknown
                fallback = bool(unknown)
                required = set(raw_required)
                if required:
                    required.update(reverse_failures)
                preferred = translate(related) if selected else set()

                changes = None
                if (not fallback and raw_required
                        and (use_engine_skip or use_isolation_drop)
                        and monotonic() < deadline - 1.0):
                    if use_engine_skip and tpcds_num is not None and tpcds_num in raw_required:
                        without_tpcds = set(required) - {tpcds_num}
                        w_with = pack(required, ranked, durations, preferred)
                        w_without = pack(without_tpcds, ranked, durations, preferred)
                        cost_with = max((sum(durations[t] for t in w) for w in w_with), default=0) + 2000 * len(w_with)
                        cost_without = max((sum(durations[t] for t in w) for w in w_without), default=0) + 2000 * len(w_without)
                        if cost_with - cost_without > 12000:
                            try:
                                changes = read_patch(patch, root)
                            except (OSError, ValueError, SyntaxError, RecursionError, OverflowError):
                                changes = []
                                fallback = True
                            if not fallback and changes and not any(
                                c.path in TPCDS_BACKEND_FILES or c.path.startswith(TPCDS_BACKEND_PREFIXES)
                                for c in changes
                            ):
                                rem = deadline - monotonic()
                                if rem > 1.0 and runner.verify_tpcds_frontend(changes, timeout_s=min(20, max(1, int(rem)))):
                                    raw_required.discard(tpcds_num)
                                    required = set(raw_required)
                                    if required:
                                        required.update(reverse_failures)

                    if use_isolation_drop and not fallback and raw_required and len(raw_required) <= 40:
                        req_ids = [names[t] for t in sorted(raw_required, key=lambda t: (durations[t], t))]
                        req_files = {rid.split("::")[0] for rid in req_ids}
                        if not any(f in SLOW_UNITTEST_FILES for f in req_files):
                            sum_ms = sum(durations[t] for t in raw_required)
                            w_cur = pack(required, ranked, durations, preferred)
                            cur_cost = max((sum(durations[t] for t in w) for w in w_cur), default=0) + 2000 * len(w_cur)
                            est_cpu = 850 + sum_ms + 60 * len(req_files)
                            if sum_ms <= 900 and est_cpu <= cur_cost - 300:
                                if changes is None:
                                    try:
                                        changes = read_patch(patch, root)
                                    except (OSError, ValueError, SyntaxError, RecursionError, OverflowError):
                                        changes = []
                                        fallback = True
                                if not fallback and changes and all(c.path.endswith(".py") for c in changes):
                                    rem = deadline - monotonic()
                                    timeout_s = min(10, max(3, int(cur_cost / 1000) + 2), max(1, int(rem)))
                                    if rem > 1.0 and runner.verify_unittest(changes, req_ids, timeout_s=timeout_s):
                                        required = set()
                                        preferred = set()

                workers = pack(required, ranked, durations, preferred)
            print(json.dumps({"commit": patch.stem, "workers": workers}, separators=(",", ":")), file=output)
    finally:
        if runner is not None:
            runner.close()
        output.close()


import ast
import marshal
from pathlib import Path
from change_shapes import (align_directives, function_body_mask, import_mask, table_entry_mask,
                           unchanged_call_arguments)
from shared_writes import shared_write_effect
from mutation_summaries import Project, module_name
from patching import MAX_CHANGED_LINES, overlaps
from proofs import (
    baseline_code,
    comparison_candidate,
    delayed_literal,
    identity_equivalence,
    opcode_lines,
    scope_changed,
)
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


def possible_identity_change(change):
    # One side must physically contain == or != for this token rewrite.
    # Run the existing complete proof for every admitted candidate.
    for source, lines in ((change.before, change.removed), (change.after, change.added)):
        physical = source.split(b"\n")
        if any(b"==" in physical[n-1] or b"!=" in physical[n-1] for n in lines):
            return True
    return False


class Index:
    def __init__(self, data, project=None, *, narrow_shared_args=None, identity_equivalence=None, root="/sqlglot"):
        self.data = data
        self.project = project
        self.narrow_shared_args = (
            _env_flag("NARROW_SHARED_ARGS", True) if narrow_shared_args is None else bool(narrow_shared_args)
        )
        self.identity_equivalence = (
            _env_flag("IDENTITY_EQUIVALENCE", True) if identity_equivalence is None else bool(identity_equivalence)
        )
        self.fast = _env_flag("FAST_ANALYSIS")
        self.unused_imports = _env_flag("UNUSED_IMPORTS")
        self.local_scope_changes = _env_flag("LOCAL_SCOPE_CHANGES")
        self.touched_arguments = _env_flag("TOUCHED_ARGUMENTS")
        self.function_insertions = _env_flag("FUNCTION_INSERTIONS")
        self.class_table_entries = _env_flag("CLASS_TABLE_ENTRIES")
        self.root = Path(root) if root is not None else None
        self.warm_unknown = data.get("warm_unknown", {})
        self.ids = data["ids"]
        self.all = (1 << len(self.ids)) - 1
        self.masks = [int(x, 16) for x in data["masks"]]

    def bits(self, table, key):
        pointer = self.data.get(table, {}).get(key)
        return 0 if pointer is None else self.masks[pointer]

    def point(self, table, path, lineno):
        pointer = self.data.get(table, {}).get(path, {}).get(str(lineno))
        return 0 if pointer is None else self.masks[pointer]

    def binding_readers(self, bindings):
        mask = 0
        for binding in bindings:
            tag = binding[0]
            b_mask = 0
            if tag == "mod_val":
                mod, name = binding[1], binding[2]
                b_mask |= self.bits("attributes", name)
                b_mask |= self.bits("dialect_reads", name)
                b_mask |= self.bits("raw_class_reads", name)
                if mod:
                    b_mask |= self.bits("class_reads", f"{mod}.{name}")
            elif tag == "class":
                qualname, name = binding[1], binding[2]
                b_mask |= self.bits("attributes", name)
                b_mask |= self.bits("dialect_reads", name) | self.bits("dialect_reads", "*")
                b_mask |= self.bits("raw_class_reads", name) | self.bits("raw_class_reads", "*")
                if qualname:
                    b_mask |= self.bits("class_reads", qualname)
            elif tag == "cls_val":
                qualname, attr = binding[1], binding[2]
                b_mask |= self.bits("attributes", attr)
                b_mask |= self.bits("dialect_reads", attr) | self.bits("dialect_reads", "*")
                b_mask |= self.bits("raw_class_reads", attr) | self.bits("raw_class_reads", "*")
                if qualname:
                    b_mask |= self.bits("class_reads", qualname) | self.bits("class_reads", f"{qualname}.{attr}")
            if not b_mask:
                return None
            mask |= b_mask
        return mask

    def select_changes(self, changes):
        if sum(len(c.added) + len(c.removed) for c in changes) > MAX_CHANGED_LINES:
            return self.all, 0
        selected = related = 0
        if self.fast:
            # A semantic edit to a Python test already selects the suite. Do
            # this before indexing a potentially expensive multi-file patch.
            remaining = []
            for change in changes:
                if change.path.startswith("tests/") and change.path.endswith(".py"):
                    required, nearby = self.select(change, certificates=False)
                    selected |= required
                    related |= nearby
                else:
                    remaining.append(change)
            if selected == self.all or not remaining:
                return selected, related
        else:
            remaining = changes
        patch = None
        if self.project is not None and (not self.fast or len(remaining) > 1):
            patch = self.project.patched(remaining, on_demand=self.fast)
        for change in remaining:
            required, nearby = self.select(change, certificates=len(changes) == 1, patch=patch)
            selected |= required
            related |= nearby
            if self.fast and selected == self.all:
                break
        return selected, related

    def select(self, change, certificates=True, patch=None):
        if len(change.added) + len(change.removed) > MAX_CHANGED_LINES:
            return self.all, 0
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
        extra_mask = 0
        try:
            before = original_tree(change.before)
            module = module_name(path)
            if self.project is not None and path.startswith("sqlglot/"):
                if patch is None:
                    patch = self.project.patched([change], on_demand=self.fast)
                after = patch.source(module).tree
            else:
                after = ast.parse(change.after, type_comments=True)
            if path.startswith("sqlglot/"):
                untouched_old, untouched_new = (unchanged_call_arguments(before, after, change, equal_trees)
                                                if self.touched_arguments and certificates else ((), ()))
                full_before, b_before = shared_write_effect(
                    before,
                    change.removed,
                    self.project,
                    module,
                    narrow_shared_args=self.narrow_shared_args,
                    root=self.root,
                    fresh_literals=self.touched_arguments,
                    unchanged=untouched_old,
                    pinned=self.fast,
                )
                if full_before:
                    return self.all, users
                full_after, b_after = shared_write_effect(
                    after,
                    change.added,
                    patch,
                    module,
                    narrow_shared_args=self.narrow_shared_args,
                    root=self.root,
                    fresh_literals=self.touched_arguments,
                    unchanged=untouched_new,
                )
                if full_after:
                    return self.all, users
                found_bindings = b_before | b_after
                if found_bindings:
                    extra_mask = self.binding_readers(found_bindings)
                    if extra_mask is None:
                        return self.all, users
            same = equal_trees(before, after)
            import_effect = not same and not equal_trees(before, after, headers_only=True)
        except (ValueError, SyntaxError):
            return self.all, users
        if same and not extra_mask:
            return opened, users

        # The pinned suite also compares code objects without calling them.
        opened |= self.bits("attributes", "__code__") | self.bits("attributes", "__closure__")
        lines = self.data["lines"].get(path, {})
        if path.startswith("tests/"):
            return self.all, users
        shape_after = after
        body_edit = not import_effect
        if import_effect and certificates:
            shape_after = align_directives(before, after, change)
            if shape_after is not after and (self.function_insertions or self.local_scope_changes):
                body_edit = equal_trees(before, shape_after, headers_only=True)
        if body_edit:
            original = baseline_code(change.before, path)
            if scope_changed(original, compiled):
                if (self.local_scope_changes and certificates
                        and (self.function_insertions or not change.insertions)
                        and not scope_changed(original, compiled, ignore_locals=True)):
                    readers = function_body_mask(self, change, before, shape_after, equal_trees, local_scope=True)
                    if readers is not None:
                        return opened | extra_mask | readers, users
                return self.all, users
        if certificates and not extra_mask:
            proof = self.certificate(change, before, after, compiled, import_effect)
            if proof is not None:
                return opened | proof[1], users

        if import_effect and certificates and self.class_table_entries:
            readers = table_entry_mask(self, change, before, shape_after, equal_trees)
            if readers is not None:
                return opened | extra_mask | readers, users

        if import_effect and certificates and self.unused_imports:
            readers = import_mask(self, change, before, shape_after, equal_trees)
            if readers is not None:
                return opened | extra_mask | readers, users

        if (body_edit and change.insertions and self.function_insertions
                and certificates):
            readers = function_body_mask(self, change, before, shape_after, equal_trees)
            if readers is not None:
                return opened | extra_mask | readers, users

        if (import_effect or change.insertions
                or not change.removed.isdisjoint(self.warm_unknown.get("lines", {}).get(path, ()))):
            return self.all, users
        functions, bindings = self.data["layout"][path]
        required = opened | extra_mask
        # A physical line inside a statement can be skipped on the baseline
        # (short-circuiting, comprehensions, conditional expressions). Its
        # siblings and entry lines still establish dependence on that statement.
        removed = sorted(change.removed)
        for first, last in self.data["statements"][path]:
            if overlaps(removed, first, last):
                required |= self.range_users(lines, first, last)
        for point in removed:
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
        points = sorted(points)
        for first, last, names, entries in bindings:
            if overlaps(points, first, last):
                for name in names:
                    required |= self.bits("attributes", name)
                for i, (begin, end, key) in enumerate(entries):
                    # Changing a value also affects readers of its key. At
                    # boundaries include both adjacent entries conservatively.
                    boundary = entries[i + 1][0] if i + 1 < len(entries) else last
                    if overlaps(points, begin, max(end, boundary)):
                        required |= self.bits("keys", key)
        return required or self.all, users

    def certificate(self, change, before, after, compiled, import_effect):
        path = change.path
        if (not path.startswith("sqlglot/") or change.insertions or len(change.removed) != 1
                or before is None or after is None):
            return None
        if import_effect:
            return delayed_literal(self, before, after, change)
        if self.identity_equivalence and (not self.fast or possible_identity_change(change)):
            equiv = identity_equivalence(change, before, after, root_dir=self.root or "/sqlglot")
            if equiv is not None:
                return equiv
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
