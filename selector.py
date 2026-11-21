"""Choose tests using only dependencies measured on the unmodified checkout."""
from contextlib import suppress
import json
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
    # The scorer enforces its two CPUs with a quota. Bound native thread pools
    # that otherwise size themselves from the host's larger affinity mask.
    if hasattr(os, "sched_getaffinity"):
        allowed = sorted(os.sched_getaffinity(0))
        if len(allowed) > 2:
            os.sched_setaffinity(0, allowed[:2])

    # Keep a private result stream even if an import writes to fd 1.
    output = os.fdopen(os.dup(1), "w", encoding="utf-8")
    os.dup2(2, 1)

    root = Path("/sqlglot")
    data = Path("/data")
    fast = _env_flag("FAST_ANALYSIS")
    from pinned_data import load
    index = Index(load(Path(__file__).with_name("maps.json"), fast),
                  Project(load(Path(__file__).with_name("mutations.json"), fast)),
                  root=root, census_path=Path(__file__).with_name("census.json"))
    with output:
        select_batch(output, root, data, index, started)


def select_batch(output, root, data, index, started):
    from bounded_batch import BATCH_SECONDS, bounded_results
    from packing import pack
    from patching import read_patch

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

    full_plan = pack(set(ranked), ranked, durations)

    from time import process_time
    from cone import analyze as candidates, serialization_edit
    from state_watch import persistent_readers
    from verify import WarmSuite, runnable, schedule

    patches = sorted((data / "commits").glob("*.patch"))
    deadline = started + BATCH_SECONDS
    suite = WarmSuite(root, index.ids)
    shared = None
    try:
        suite.warm()
        shared = persistent_readers(index)
    except Exception:
        suite.ready = False
    ordered = sorted((i for i, n in enumerate(positions) if n is not None),
                     key=lambda i: index.ids[i])
    duration = {i: durations[positions[i]] for i in ordered}
    eligible = [i for i in ordered if runnable(index.ids[i])]
    pool_ids = set(json.loads(Path(__file__).with_name("pool_readers.json").read_bytes()))
    serde_sensitive = sum(1 << i for i in ordered if index.ids[i] in pool_ids)
    # The same work list is used on fast and slow hosts. Deadlines only widen.
    cap = min(5.0, 115 / max(1, len(patches)))

    from snapshot_cone import ImportSnapshot, runtime_readers
    snapshot = ImportSnapshot(index, root)

    def analyze(path):
        start = process_time()
        changes = read_patch(path, root)
        selected, protected, watches, hot, writers = candidates(index, changes, equal_trees, shared)
        if selected and any(serialization_edit(c) for c in changes):
            selected |= serde_sensitive
            protected |= serde_sensitive
        use_snapshot = runtime_readers(index, changes, equal_trees) if selected == protected == index.all else None
        return selected, protected, watches, hot, writers, use_snapshot, process_time() - start

    def cost(tests):
        workers = pack(tests, ranked, durations, fill=False)
        return 2000 * len(workers) + max(
            (sum(durations[t] for t in w) for w in workers), default=0)

    def plan_for(path, result):
        if result is not None and result[5] is not None and suite.ready and monotonic() < deadline:
            selected, protected, watch, hot, writers, (eager_importers, runtime_required), static_cpu = result
            from verify import cgroup_cpu
            if not snapshot.ready:
                snapshot.prepare()
            # Batch startup is charged by the scorer and bounded by the batch deadline.
            start_cpu = cgroup_cpu()
            changes = read_patch(path, root)
            cap_left = cap - static_cpu - ((cgroup_cpu() or 0) - (start_cpu or 0))
            selected, protected = snapshot.select(changes, deadline, cap_left)
            selected |= eager_importers | runtime_required
            protected |= runtime_required
            if any(serialization_edit(c) for c in changes):
                selected |= serde_sensitive
                protected |= serde_sensitive
            static_cpu += (cgroup_cpu() or 0) - (start_cpu or 0)
            result = selected, protected, (), None, 0, False, static_cpu
        if result is None or result[1] == index.all:
            workers = full_plan
        else:
            selected, protected, watch, hot, writers, _, static_cpu = result
            remaining_cpu = cap - static_cpu
            # An unresolved shared write needs evidence for every possible
            # writer. If the budget excludes one, keep the static outer bound.
            extra = index.all if writers else 0
            passed = 0
            if selected != protected and suite.ready and remaining_cpu > 0.1 and monotonic() < deadline:
                available = (selected & ~protected) | writers
                order = [i for i in eligible if available & (1 << i)]
                if writers:
                    order.sort(key=lambda i: not writers & (1 << i))
                subset = sorted(schedule(order, duration, min(1500, int(cap * 300))))
                chosen_mask = sum(1 << i for i in subset)
                current = translate(selected) | unknown
                estimated = (75 if hot is not None else 280) + sum(duration[i] + 2 for i in subset)
                saving = cost(current) - cost(current - translate(chosen_mask & ~protected))
                # Broad state checkpoints bracket each possible writer in the
                # pristine and patched runs. Reserve time for both passes.
                fits = not writers or 2 * (estimated + 100 * writers.bit_count()) < 1000 * cap
                if subset and fits and not writers & ~chosen_mask and (writers or saving > estimated):
                    changes = read_patch(path, root)
                    passed, extra = suite.check(index, changes, subset, watch, hot, writers,
                                                deadline, remaining_cpu)
            required = translate((selected & ~passed) | protected | extra) | unknown
            if required:
                required.update(reverse_failures)
            workers = pack(required, ranked, durations, fill=False)
        return workers

    # Drive output from the input inventory, even if the analysis worker stops.
    full_json = json.dumps(full_plan, separators=(",", ":"))
    results = None
    for offset, path in enumerate(patches):
        try:
            if results is None:
                results = bounded_results(patches[offset:], analyze, deadline)
            analyzed, result = next(results)
            if analyzed != path:
                raise ValueError("analysis result is out of order")
            workers = plan_for(path, result)
            encoded = full_json if workers is full_plan else json.dumps(workers, separators=(",", ":"))
        except Exception:
            encoded = full_json
            if results is not None:
                with suppress(Exception):
                    results.close()
                results = None
        output.write('{"commit":' + json.dumps(path.stem) + ',"workers":' + encoded + '}\n')
    if results is not None:
        with suppress(Exception):
            results.close()


import ast
import marshal
from pathlib import Path
from change_shapes import (align_directives, census_block_mask, function_body_mask, import_mask, table_entry_mask,
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
    if a is b:
        return True
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
    def __init__(self, data, project=None, *, narrow_shared_args=None, identity_equivalence=None, root="/sqlglot",
                 census_path=None):
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
        self.census_args = _env_flag("CENSUS_ARGS")
        self.census_blocks = _env_flag("CENSUS_BLOCKS")
        self.census = None
        if (self.census_args or self.census_blocks) and census_path is not None and Path(census_path).exists():
            from census import Census
            self.census = Census.load(census_path)
        self.root = Path(root) if root is not None else None
        self.warm_unknown = data.get("warm_unknown", {})
        self.ids = data["ids"]
        self.all = (1 << len(self.ids)) - 1
        self.masks = [int(x, 16) for x in data["masks"]]

    def bits(self, table, key):
        pointer = self.data.get(table, {}).get(key)
        return 0 if pointer is None else self.masks[pointer]

    @lru_cache(maxsize=None)
    def import_users(self, path):
        """Recover the test import closure when no traced reader owns the module."""
        known = self.bits("users", path)
        if known:
            return known
        importing = {path}
        graph = self.data.get("imports", {})
        while True:
            more = {source for source, deps in graph.items()
                    if source not in importing and not importing.isdisjoint(deps)}
            if not more:
                break
            importing.update(more)
        mask = 0
        for source in importing:
            mask |= self.bits("users", source)
        return mask | sum(1 << i for i, name in enumerate(self.ids)
                          if name.split("::", 1)[0] in importing)

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

    def select_changes(self, changes, *, effects=None):
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
            required, nearby = self.select(change, certificates=len(changes) == 1, patch=patch, effects=effects)
            selected |= required
            related |= nearby
            if self.fast and selected == self.all and effects is None:
                break
        return selected, related

    def select(self, change, certificates=True, patch=None, *, effects=None):
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
            census_old = census_new = None
            if self.census is not None and self.census_args and path.startswith("sqlglot/") and certificates:
                census_old = self.census.resolver(module, path, before)
                census_new = self.census.resolver(module, path, after)
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
                    census=census_old,
                )
                if full_before:
                    if effects is not None:
                        effects[path] = None
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
                    census=census_new,
                )
                if full_after:
                    if effects is not None:
                        effects[path] = None
                    return self.all, users
                found_bindings = b_before | b_after
                if found_bindings:
                    extra_mask = self.binding_readers(found_bindings)
                    if effects is not None:
                        effects[path] = extra_mask
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
                # Nested code objects and captured cells only change behaviour
                # where the edited block runs; census_block_mask rejects scope
                # declarations, generator changes and shadowed names.
                readers = self.census_block(change, before, shape_after, certificates)
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

        if body_edit and change.insertions:
            readers = self.census_block(change, before, shape_after, certificates)
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

    def census_block(self, change, before, after, certificates):
        if (self.census is None or not self.census_blocks or not certificates
                or not change.path.startswith("sqlglot/") or before is None or after is None):
            return None
        resolver = self.census.resolver(module_name(change.path), change.path, after)
        self.census_why = []
        return census_block_mask(self, change, before, after, equal_trees, resolver, self.census_why)

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
