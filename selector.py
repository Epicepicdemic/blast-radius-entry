"""Choose tests using only dependencies measured on the unmodified checkout."""
import ast
import json
import marshal
import os
import sys
from functools import lru_cache
from pathlib import Path
from time import monotonic, process_time

from batch_entry import main

if __name__ == "__main__":
    # Enter the guarded startup before importing the analysis modules below.
    main()
    sys.exit(0)

from change_shapes import (
    align_directives,
    census_block_mask,
    function_body_mask,
    import_mask,
    table_entry_mask,
    unchanged_call_arguments,
)
from mutation_summaries import Project, module_name
from patching import MAX_CHANGED_LINES, compiled_source, overlaps, parsed_source
from proofs import (
    baseline_code,
    comparison_candidate,
    delayed_literal,
    identity_equivalence,
    opcode_lines,
    scope_changed,
)
from shared_writes import shared_write_effect


def _env_flag(name, default=True):
    val = os.environ.get(name)
    if val is None or not val.strip():
        return default
    return val.strip().lower() not in ("0", "false", "no", "off")


def _has_env_dep(changes):
    for ch in changes:
        if not ch.path.endswith(".py"):
            continue
        for raw, pts in ((ch.before, ch.removed), (ch.after, ch.added)):
            if not pts:
                continue
            lines = raw.splitlines()
            for ln in pts:
                if 1 <= ln <= len(lines):
                    line = lines[ln - 1]
                    if (
                        b"environ" in line
                        or b"getenv" in line
                        or b"PYTEST_" in line
                        or b"__import__" in line
                    ):
                        return True
    return False


def load_index(root):
    from pinned_data import load
    fast = _env_flag("FAST_ANALYSIS")
    return Index(load(Path(__file__).with_name("maps.json"), fast),
                 Project(load(Path(__file__).with_name("mutations.json"), fast)),
                 root=root, census_path=Path(__file__).with_name("census.json"))


def prepare_batch(root, patches, tests, ranked, durations, full_plan, started):
    from bounded_batch import BATCH_SECONDS
    from cone import analyze as candidates, serialization_edit
    from packing import pack, packed_cost
    from patching import read_patch
    from snapshot_cone import ImportSnapshot, runtime_readers
    from state_watch import persistent_readers
    from verify import WarmSuite, runnable, schedule, cgroup_cpu

    use_inline_pool = _env_flag("INLINE_POOL", True)
    use_micro_oracles = _env_flag("MICRO_ORACLES", True)
    use_setupclass_deamort = _env_flag("SETUPCLASS_DEAMORT", True)
    use_row_slice = _env_flag("ROW_SLICE", True)
    use_twophase_tpc = _env_flag("TWOPHASE_TPC", True)
    use_stress_probes = _env_flag("STRESS_PROBES", True)
    use_gen_mem_escalate = _env_flag("GEN_MEM_ESCALATE", True)
    use_isolated_schedule = _env_flag("ISOLATED_SCHEDULE", True)
    use_reach_gate = _env_flag("REACH_GATE", True)
    big_only = _env_flag("HEAVY_BIG_ONLY", False)
    heavy_enabled = any((
        use_inline_pool,
        use_micro_oracles,
        use_setupclass_deamort,
        use_row_slice,
        use_twophase_tpc,
        use_stress_probes,
    ))

    fast = _env_flag("FAST_ANALYSIS")
    index = load_index(root)
    numbers = {t["id"]: t["number"] for t in tests}
    # Both fail when the unmodified pinned suite runs in reverse order.
    reverse_failures = {numbers[name] for name in (
        "tests/dialects/test_dialect.py::TestDialect::test_enum",
        "tests/dialects/test_starrocks.py::TestStarrocks::test_time_slice_origin_roundtrip",
    ) if name in numbers}
    positions = [numbers.get(name) for name in index.ids]
    unknown = set(ranked) - set(positions)
    num_to_idx = {n: i for i, n in enumerate(positions) if n is not None}

    def translate(mask):
        return {t for i, t in enumerate(positions) if t is not None and mask & (1 << i)}

    deadline = started + BATCH_SECONDS
    suite = WarmSuite(root, index.ids)
    suite.warm()
    shared = persistent_readers(index)
    ordered = sorted((i for i, n in enumerate(positions) if n is not None),
                     key=lambda i: index.ids[i])
    duration = {i: durations[positions[i]] for i in ordered}
    eligible = [i for i in ordered if runnable(index.ids[i])]
    pool_ids = set(json.loads(Path(__file__).with_name("pool_readers.json").read_bytes()))
    serde_sensitive = sum(1 << i for i in ordered if index.ids[i] in pool_ids)
    # The same work list is used on fast and slow hosts. Deadlines only widen.
    cap = min(5.0, 115 / max(1, len(patches)))

    snapshot = ImportSnapshot(index, root)

    # Lazy-loaded heavy data structures so trivial/non-heavy batches pay zero overhead.
    case_cov_holder = [False, None]
    tpcds_base_holder = [False, None]

    def get_case_cov():
        if not case_cov_holder[0]:
            case_cov_holder[0] = True
            # Child forks share the decoded, read-only observations for the batch.
            import heavy_reach
            heavy_reach.footprints()
            from pinned_data import load
            from slicer import CaseCoverage
            cc_path = Path(__file__).with_name("case-coverage.json")
            if cc_path.exists() or cc_path.with_suffix(".bin").exists():
                case_cov_holder[1] = CaseCoverage(load(cc_path, fast))
        return case_cov_holder[1]

    def get_tpcds_baseline():
        if not tpcds_base_holder[0]:
            tpcds_base_holder[0] = True
            from slicer import load_tpcds_baseline
            tpcds_base_holder[1] = load_tpcds_baseline()
        return tpcds_base_holder[1]

    tpcds_idx = None
    tpch_idx = None
    opt_tpch_idx = None
    if heavy_enabled:
        import micro_oracles
        import slicer
        tpcds_idx = num_to_idx.get(numbers.get(slicer.TEST_EXECUTE_TPCDS))
        tpch_idx = num_to_idx.get(numbers.get(slicer.TEST_EXECUTE_TPCH))
        opt_tpch_idx = num_to_idx.get(numbers.get(slicer.TEST_OPTIMIZED_TPCH))

    def analyze(path):
        start = process_time()
        changes = read_patch(path, root)
        selected, protected, watches, hot, writers = candidates(index, changes, equal_trees, shared)
        if selected and any(serialization_edit(c) for c in changes):
            selected |= serde_sensitive
            protected |= serde_sensitive
        use_snapshot = runtime_readers(index, changes, equal_trees) if selected == protected == index.all else None
        return selected, protected, watches, hot, writers, use_snapshot, process_time() - start

    positive_rank = [t for t in ranked if durations[t] > 0]

    def cost(tests_set):
        return packed_cost(tests_set, positive_rank, durations)

    def _vanilla_verify(selected, protected, watch, hot, writers, path, static_cpu):
        remaining_cpu = cap - static_cpu
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
            fits = not writers or 2 * (estimated + 100 * writers.bit_count()) < 1000 * cap
            if subset and fits and not writers & ~chosen_mask and (writers or saving > estimated):
                changes = read_patch(path, root)
                import state_watch
                state_watch.deep = state_watch.DEEP_STATE and state_watch.DEEP_WATCH in watch
                try:
                    passed, extra = suite.check(index, changes, subset, watch, hot, writers,
                                                deadline, remaining_cpu)
                finally:
                    state_watch.deep = False
        return passed, extra

    def plan_for(path, result):
        screened_import = False
        if result is not None and result[5] is not None and suite.ready and monotonic() < deadline:
            selected, protected, watch, hot, writers, (eager_importers, runtime_required), static_cpu = result
            if not snapshot.ready:
                snapshot.prepare()
            start_cpu = cgroup_cpu()
            changes = read_patch(path, root)
            cap_left = cap - static_cpu - ((cgroup_cpu() or 0) - (start_cpu or 0))
            selected, protected = snapshot.select(changes, deadline, cap_left)
            screened_import = protected != index.all
            selected |= eager_importers | runtime_required
            protected |= runtime_required
            if any(serialization_edit(c) for c in changes):
                selected |= serde_sensitive
                protected |= serde_sensitive
            static_cpu += (cgroup_cpu() or 0) - (start_cpu or 0)
            result = selected, protected, (), None, 0, False, static_cpu

        if result is None or result[1] == index.all:
            return full_plan

        selected, protected, watch, hot, writers, _, static_cpu = result
        remaining_cpu = cap - static_cpu

        if not heavy_enabled or writers:
            passed, extra = _vanilla_verify(selected, protected, watch, hot, writers, path, static_cpu)
            required = translate((selected & ~passed) | protected | extra) | unknown
            if required:
                required.update(reverse_failures)
            return pack(required, ranked, durations, fill=False)

        passed = 0
        extra = 0
        available = selected & ~protected
        if available and suite.ready and monotonic() < deadline - 0.15:
            # Check if we even have heavy/oracle/optimizer/executor candidates vs vanilla fast unit tests.
            avail_indices = [i for i in ordered if available & (1 << i)]
            has_heavy_cand = any(
                (not runnable(index.ids[i]))
                or index.ids[i].startswith("tests/test_optimizer.py::")
                or index.ids[i] in slicer.EXECUTOR_TPC_IDS
                or index.ids[i] in micro_oracles.MICRO_ORACLE_IDS
                for i in avail_indices
            )
            if not has_heavy_cand:
                passed, extra = _vanilla_verify(selected, protected, watch, hot, 0, path, static_cpu)
            else:
                changes = read_patch(path, root)
                if _has_env_dep(changes):
                    passed, extra = _vanilla_verify(selected, protected, watch, hot, 0, path, static_cpu)
                else:
                    can_slice_py = (hot is not None)
                    excluded = set()
                    runnable_items = []
                    slice_map = {}
                    dialect_map = {}
                    cached_p1 = None
                    case_cov = get_case_cov() if (use_row_slice or use_twophase_tpc or use_isolated_schedule) else None

                    current_req = translate(selected) | unknown
                    if current_req:
                        current_req.update(reverse_failures)
                    cur_cost = cost(current_req)

                    # Phase 1: TPC-DS structural verification if TPC-DS is an unprotected candidate.
                    if tpcds_idx is not None and (available & (1 << tpcds_idx)):
                        tpcds_num = positions[tpcds_idx]
                        tpcds_tid = slicer.TEST_EXECUTE_TPCDS
                        tpcds_marginal = cur_cost - cost(current_req - {tpcds_num})
                        if not (use_inline_pool and (use_twophase_tpc or use_row_slice)):
                            excluded.add(tpcds_idx)
                        elif use_reach_gate and tpcds_marginal < 1500:
                            excluded.add(tpcds_idx)
                        else:
                            sp_tpc = (
                                case_cov.plan_slice(tpcds_tid, changes, index, can_slice_py=can_slice_py)
                                if (use_row_slice and case_cov is not None)
                                else None
                            )
                            baseline_sigs = get_tpcds_baseline() if use_twophase_tpc else None
                            if use_twophase_tpc and baseline_sigs is not None:
                                p2 = set(sp_tpc["phase2_indices"] or ()) if (sp_tpc is not None and not sp_tpc["full"]) else set()
                                if len(p2) > 10:
                                    excluded.add(tpcds_idx)
                                else:
                                    if sp_tpc is not None and not sp_tpc["full"]:
                                        p1_cands = [idx for idx in (sp_tpc["exec_indices"] or ()) if idx not in p2]
                                    else:
                                        p1_cands = None
                                    ok_p1 = True
                                    mismatched = []
                                    if p1_cands is None or p1_cands:
                                        rem_p1 = deadline - monotonic()
                                        p1_cap = min(12.0, max(1.0, (rem_p1 - 1.5) * 0.4))
                                        if rem_p1 > 1.5:
                                            # Other expensive candidates can also clear in this commit.
                                            # Price TPC-DS with them present and with only protected tests left.
                                            blocked = translate(selected & protected) | unknown
                                            if blocked:
                                                blocked.update(reverse_failures)
                                            tpc_floor = blocked | reverse_failures | {tpcds_num}
                                            attainable_saving = max(tpcds_marginal, cost(tpc_floor) - cost(blocked))
                                            ok_p1, mismatched = suite.verify_tpcds_phase1(
                                                changes,
                                                hot,
                                                baseline_sigs,
                                                deadline,
                                                p1_cap,
                                                indices=p1_cands,
                                                screened_import=screened_import,
                                                saving_ms=attainable_saving,
                                                max_mismatches=max(0, 10 - len(p2)),
                                            )
                                        else:
                                            ok_p1 = False
                                    if not ok_p1:
                                        excluded.add(tpcds_idx)
                                    else:
                                        p2.update(mismatched)
                                        no_exec_touch = not any(
                                            c.path in slicer.TPCDS_BACKEND_FILES
                                            or c.path.startswith(slicer.TPCDS_BACKEND_PREFIXES)
                                            for c in changes
                                        )
                                        if len(p2) > 10:
                                            excluded.add(tpcds_idx)
                                        elif not p2:
                                            if (sp_tpc is not None and not sp_tpc["full"]) or no_exec_touch:
                                                passed |= 1 << tpcds_idx
                                            else:
                                                excluded.add(tpcds_idx)
                                        else:
                                            sp_p2 = dict(sp_tpc) if sp_tpc is not None else {"full": False}
                                            sp_p2["phase2_indices"] = sorted(p2)
                                            sp_p2["est_us"] = len(p2) * 350000
                                            slice_map[tpcds_tid] = sp_p2
                                            runnable_items.append(tpcds_idx)
                            elif sp_tpc is not None and not sp_tpc["full"] and use_setupclass_deamort:
                                sp_exec = dict(sp_tpc)
                                sp_exec["phase2_indices"] = None
                                if len(sp_exec.get("exec_indices") or ()) <= 12:
                                    slice_map[tpcds_tid] = sp_exec
                                    runnable_items.append(tpcds_idx)
                                else:
                                    excluded.add(tpcds_idx)
                            else:
                                excluded.add(tpcds_idx)

                    # Recompute current cost after any TPC-DS Phase 1 clear.
                    if passed:
                        current_req = translate(selected & ~passed) | unknown
                        if current_req:
                            current_req.update(reverse_failures)
                        cur_cost = cost(current_req)

                    for i in avail_indices:
                        if i == tpcds_idx:
                            continue
                        tid = index.ids[i]
                        if big_only and (tid in micro_oracles.MICRO_ORACLE_IDS or not runnable(tid)
                                         or tid.startswith("tests/test_optimizer.py::")) and tid != micro_oracles.TEST_MAX_NODES:
                            excluded.add(i)
                            continue
                        if tid in micro_oracles.MICRO_ORACLE_IDS:
                            if micro_oracles.micro_oracle_guard(
                                tid,
                                changes,
                                use_micro_oracles=use_micro_oracles,
                                use_stress_probes=use_stress_probes,
                            ):
                                if tid == micro_oracles.TEST_GENERATOR_MEMORY:
                                    d_names = micro_oracles.target_dialects_for_changes(changes)
                                    if d_names is None and use_row_slice and case_cov is not None:
                                        sp = case_cov.plan_slice(tid, changes, index, can_slice_py=can_slice_py)
                                        if sp is not None and not sp["full"] and sp["dialect_names"]:
                                            d_names = sp["dialect_names"]
                                    if d_names is not None:
                                        dialect_map[tid] = d_names
                                if use_reach_gate:
                                    o_est = 35
                                    if tid == micro_oracles.TEST_MAX_NODES:
                                        o_est = 140
                                    elif tid == micro_oracles.TEST_SCOPE:
                                        o_est = 450
                                    elif tid == micro_oracles.TEST_QUALIFY_CTE_CHAIN:
                                        o_est = 550
                                    elif tid == micro_oracles.TEST_DEEP_AST_ANNOTATION:
                                        o_est = 450
                                    elif tid == micro_oracles.TEST_SERDE_RECURSION:
                                        o_est = 300
                                    elif tid == micro_oracles.TEST_NAMED_SELECTS_CHAIN:
                                        o_est = 80
                                    elif tid == micro_oracles.TEST_GENERATOR_MEMORY:
                                        n_d = len(dialect_map[tid]) if tid in dialect_map else 33
                                        o_est = 60 + n_d * (5 if use_gen_mem_escalate else 12)
                                    if cur_cost - cost(current_req - {positions[i]}) <= o_est + 50:
                                        dialect_map.pop(tid, None)
                                        excluded.add(i)
                                        continue
                                runnable_items.append(i)
                            elif tid in micro_oracles.STRESS_ORACLE_IDS and not use_stress_probes:
                                if use_inline_pool and (use_row_slice or duration[i] < 1500):
                                    if use_row_slice and case_cov is not None and case_cov.has(tid):
                                        sp = case_cov.plan_slice(tid, changes, index, can_slice_py=can_slice_py)
                                        if sp is not None:
                                            slice_map[tid] = sp
                                    runnable_items.append(i)
                                else:
                                    excluded.add(i)
                            else:
                                excluded.add(i)
                        elif tid == slicer.TEST_EXECUTE_TPCH:
                            if use_inline_pool and use_setupclass_deamort:
                                if use_row_slice and case_cov is not None:
                                    sp = case_cov.plan_slice(tid, changes, index, can_slice_py=can_slice_py)
                                    if sp is not None:
                                        slice_map[tid] = sp
                                runnable_items.append(i)
                            else:
                                excluded.add(i)
                        elif tid == slicer.TEST_OPTIMIZED_TPCH:
                            if use_setupclass_deamort or use_row_slice:
                                if use_row_slice and case_cov is not None:
                                    sp = case_cov.plan_slice(tid, changes, index, can_slice_py=can_slice_py)
                                    if sp is not None:
                                        slice_map[tid] = sp
                                runnable_items.append(i)
                            else:
                                excluded.add(i)
                        elif runnable(tid, inline_pool=use_inline_pool, setupclass_deamort=use_setupclass_deamort):
                            if use_row_slice and case_cov is not None and case_cov.has(tid):
                                sp = case_cov.plan_slice(tid, changes, index, can_slice_py=can_slice_py)
                                if sp is not None:
                                    slice_map[tid] = sp
                            runnable_items.append(i)
                        else:
                            excluded.add(i)

                    def _is_active_oracle(tid):
                        return tid in micro_oracles.MICRO_ORACLE_IDS and micro_oracles.micro_oracle_guard(
                            tid,
                            changes,
                            use_micro_oracles=use_micro_oracles,
                            use_stress_probes=use_stress_probes,
                        )

                    def _est_ms(i):
                        tid = index.ids[i]
                        if _is_active_oracle(tid):
                            if tid == micro_oracles.TEST_MAX_NODES:
                                return 140
                            if tid == micro_oracles.TEST_SCOPE:
                                return 450
                            if tid == micro_oracles.TEST_QUALIFY_CTE_CHAIN:
                                return 550
                            if tid == micro_oracles.TEST_DEEP_AST_ANNOTATION:
                                return 450
                            if tid == micro_oracles.TEST_SERDE_RECURSION:
                                return 300
                            if tid == micro_oracles.TEST_NAMED_SELECTS_CHAIN:
                                return 80
                            if tid == micro_oracles.TEST_GENERATOR_MEMORY:
                                n_d = len(dialect_map[tid]) if tid in dialect_map else 33
                                return 60 + n_d * (5 if use_gen_mem_escalate else 12)
                        sp = slice_map.get(tid)
                        if sp is not None:
                            if tid == slicer.TEST_EXECUTE_TPCH:
                                return 15
                            if tid == slicer.TEST_EXECUTE_TPCDS:
                                p2_idx = sp.get("phase2_indices")
                                if p2_idx is not None:
                                    return 200 + len(p2_idx) * 350
                                return 200 + len(sp.get("exec_indices") or ()) * 250
                            if tid == slicer.TEST_OPTIMIZED_TPCH:
                                return max(80, (sp["est_us"] // 1000) // 3)
                            if sp.get("full", True):
                                return max(duration[i], (sp["est_us"] // 1000) // 3)
                            return max(3, (sp["est_us"] // 1000) // 3)
                        if tid.startswith("tests/test_executor.py::") and tid not in slicer.EXECUTOR_TPC_IDS and use_setupclass_deamort:
                            return max(5, duration[i])
                        return max(2, duration[i])

                    if runnable_items:
                        est_cache = {i: _est_ms(i) for i in runnable_items}
                        ovh_ms = 120 if hot is not None else 280
                        if use_isolated_schedule:
                            changed = True
                            while changed and runnable_items:
                                changed = False
                                has_floor = bool(excluded or (selected & protected) or unknown)
                                if has_floor:
                                    kept = []
                                    for i in runnable_items:
                                        if duration[i] == 0 or est_cache[i] >= duration[i]:
                                            excluded.add(i)
                                            changed = True
                                        else:
                                            kept.append(i)
                                    runnable_items = kept
                            if runnable_items and not (excluded or (selected & protected) or unknown):
                                neg = [i for i in runnable_items if duration[i] == 0 or est_cache[i] >= duration[i]]
                                if neg and len(neg) < len(runnable_items):
                                    pos = [i for i in runnable_items if duration[i] > 0 and est_cache[i] < duration[i]]
                                    net_all = cur_cost - (ovh_ms + sum(est_cache[i] for i in runnable_items))
                                    pos_floor = translate(sum(1 << i for i in neg))
                                    if pos_floor:
                                        pos_floor.update(reverse_failures)
                                    net_pos = (cur_cost - cost(pos_floor)) - (ovh_ms + sum(est_cache[i] for i in pos))
                                    if net_pos >= net_all:
                                        excluded.update(neg)
                                        runnable_items = pos

                        if runnable_items:
                            floor_set = translate(
                                (selected & protected) | sum(1 << i for i in excluded)
                            ) | unknown
                            if floor_set:
                                floor_set.update(reverse_failures)
                            floor_cost = cost(floor_set)
                            potential_savings = cur_cost - floor_cost
                            sum_est = sum(est_cache[i] for i in runnable_items)
                            if potential_savings >= 250:
                                if use_isolated_schedule:
                                    def _item_sort_key(i):
                                        tid = index.ids[i]
                                        is_orac = _is_active_oracle(tid)
                                        is_tpc_duck = tid in (
                                            slicer.TEST_EXECUTE_TPCDS,
                                            slicer.TEST_OPTIMIZED_TPCH,
                                        )
                                        est = est_cache[i]
                                        tier = 0 if is_orac else (3 if duration[i] == 0 else (2 if is_tpc_duck else 1))
                                        return (tier, -(duration[i] / max(1, est)), est, i)
                                else:
                                    def _item_sort_key(i):
                                        tid = index.ids[i]
                                        is_orac = _is_active_oracle(tid)
                                        is_exec = tid.startswith("tests/test_executor.py::")
                                        est = est_cache[i]
                                        tier = 0 if is_orac else (2 if is_exec else 1)
                                        return (tier, est, i)

                                ordered_items = sorted(runnable_items, key=_item_sort_key)
                                rem = deadline - monotonic()
                                if use_isolated_schedule:
                                    # Select the highest-net-gain prefix of ordered_items within cap.
                                    max_budget_ms = min(20000.0, max(0.0, (rem - 1.5) * 1000.0))
                                    cand_prefix = []
                                    acc_est = 0
                                    for i in ordered_items:
                                        if cand_prefix and acc_est + est_cache[i] > max_budget_ms:
                                            break
                                        cand_prefix.append(i)
                                        acc_est += est_cache[i]

                                    n_cand = len(cand_prefix)
                                    # Sample checkpoints: end of high-speedup prefix (orac/ratio>=2), chunk sizes, and full cand_prefix.
                                    ckpts = set()
                                    hi_end = 0
                                    for k_idx, i in enumerate(cand_prefix, 1):
                                        if _is_active_oracle(index.ids[i]) or duration[i] >= 2 * est_cache[i]:
                                            hi_end = k_idx
                                    if hi_end:
                                        ckpts.add(hi_end)
                                    step = max(1, n_cand // 8)
                                    for k_idx in range(step, n_cand + 1, step):
                                        ckpts.add(k_idx)
                                    if n_cand:
                                        ckpts.add(n_cand)

                                    best_k = 0
                                    best_net = 0
                                    best_est_sum = 0
                                    pref_masks = [0]
                                    pref_ests = [0]
                                    for i in cand_prefix:
                                        pref_masks.append(pref_masks[-1] | (1 << i))
                                        pref_ests.append(pref_ests[-1] + est_cache[i])

                                    for k_idx in sorted(ckpts):
                                        rem_req = current_req - translate(pref_masks[k_idx])
                                        if rem_req:
                                            rem_req.update(reverse_failures)
                                        saving_k = cur_cost - cost(rem_req)
                                        net_k = saving_k - (ovh_ms + pref_ests[k_idx])
                                        if net_k > best_net:
                                            best_net = net_k
                                            best_k = k_idx
                                            best_est_sum = pref_ests[k_idx]

                                    if best_k == 0 or best_net <= 100:
                                        ordered_items = []
                                        heavy_cap = 0.0
                                    else:
                                        ordered_items = cand_prefix[:best_k]
                                        budget_ms = min(
                                            max(2500.0, best_est_sum * 2.0 + 1000.0),
                                            max_budget_ms,
                                        )
                                        heavy_cap = min(20.0, budget_ms / 1000.0, max(0.5, rem - 1.5))
                                else:
                                    heavy_cap = min(13.0, max(2.0, potential_savings / 1000.0 * 1.25), max(0.5, rem - 1.5))

                                if ordered_items and rem > 1.5 and heavy_cap > 0.1:
                                    items_spec = [
                                        (i, _is_active_oracle(index.ids[i]), duration[i] == 0)
                                        for i in ordered_items
                                    ]
                                    h_passed, h_readers = suite.verify_heavy(
                                        index,
                                        changes,
                                        items_spec,
                                        watch,
                                        hot,
                                        deadline,
                                        heavy_cap,
                                        {
                                            "inline_pool": use_inline_pool,
                                            "micro_oracles": use_micro_oracles,
                                            "setupclass_deamort": use_setupclass_deamort,
                                            "row_slice": use_row_slice,
                                            "gen_mem_escalate": use_gen_mem_escalate,
                                        },
                                        slice_map=slice_map if use_row_slice else None,
                                        dialect_map=dialect_map,
                                    )
                                    passed |= h_passed
                                    extra |= h_readers

        required = translate((selected & ~passed) | protected | extra) | unknown
        if required:
            required.update(reverse_failures)
        return pack(required, ranked, durations, fill=False)

    return analyze, plan_for, deadline


@lru_cache(maxsize=32)
def original_tree(source):
    return parsed_source(source)


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
            compiled = compiled_source(change.after, path)
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
                after = parsed_source(change.after)
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
