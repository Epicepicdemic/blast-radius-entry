import difflib
import os
from pathlib import Path
import select
import signal
import sys
from tempfile import TemporaryDirectory
from time import monotonic
import types
import unittest
import unittest.mock

from fixture_overlay import Fixtures
from micro_oracles import (
    TEST_DEEP_AST_ANNOTATION,
    TEST_NAMED_SELECTS_CHAIN,
    TEST_QUALIFY_CTE_CHAIN,
    TEST_SERDE_RECURSION,
    _check_linear_scaling,
    check_generator_memory,
    micro_oracle_guard,
    stress_guard,
)
from patching import apply_patch
from slicer import (
    TEST_EXECUTE_TPCDS,
    CaseCoverage,
    _rewrite_subtest_method,
    compute_tpcds_mismatches,
    parse_fixture_pairs,
    parse_fixture_plain,
    parse_fixture_rows,
)
import slicer
from verify import (
    WarmSuite,
    _HeavyStreamResult,
    _has_trivial_teardown,
    _wrap_call_test_method,
    fork_masks_stream,
    runnable,
)


def _diff_change(root, path, old, new):
    target = root / path
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(old)
    diff = "".join(difflib.unified_diff(old.splitlines(True), new.splitlines(True), f"a/{path}", f"b/{path}", n=0))
    change, = apply_patch(diff.encode(), root)
    return change


class _DummyIndex:
    def __init__(self, layout, statements=None):
        self.data = {"layout": layout, "statements": statements or {}}


class HeavyStep2Tests(unittest.TestCase):
    def test_fixture_parsers_and_row_slicing(self):
        old_plain = b"SELECT 1\nSELECT 2\nSELECT 3\n"
        new_plain = b"SELECT 1\nSELECT 99\nSELECT 3\n"
        self.assertEqual(parse_fixture_plain(old_plain), ("SELECT 1", "SELECT 2", "SELECT 3"))
        self.assertEqual(parse_fixture_plain(new_plain), ("SELECT 1", "SELECT 99", "SELECT 3"))

        old_pairs = b"# title: a\nSELECT 1;\nSELECT 1;\n\n# title: b\nSELECT 2;\nSELECT 2;\n"
        new_pairs = b"# title: a\nSELECT 1;\nSELECT 1;\n\n# title: b\nSELECT 22;\nSELECT 22;\n"
        self.assertEqual(len(parse_fixture_pairs(old_pairs)), 2)

        tid = "tests/test_optimizer.py::TestOptimizer::test_optimize"
        cov = CaseCoverage({
            tid: {
                "contexts": ["shared", "case:optimizer/optimizer.sql#0", "case:optimizer/optimizer.sql#1"],
                "masks": ["0x1", "0x2", "0x4"],
                "times_us": [0, 5000, 1200],
                "lines": {},
                "opens": {"tests/fixtures/optimizer/optimizer.sql": 0},
                "class_reads": {},
                "dialect_reads": {},
                "attributes": {},
                "keys": {},
                "raw_class_reads": {},
            }
        })
        idx = _DummyIndex({})
        with TemporaryDirectory() as tmp:
            root = Path(tmp).resolve()
            ch_one = _diff_change(root, "tests/fixtures/optimizer/optimizer.sql", old_pairs.decode(), new_pairs.decode())
            plan = cov.plan_slice(tid, [ch_one], idx)
            self.assertFalse(plan["full"])
            self.assertEqual(plan["fixture_indices"], {"optimizer/optimizer.sql": [1]})
            self.assertEqual(plan["est_us"], 1200)

            added_pairs = old_pairs + b"\nSELECT 3;\nSELECT 3;\n"
            ch_shift = _diff_change(root, "tests/fixtures/optimizer/optimizer.sql", old_pairs.decode(), added_pairs.decode())
            plan_shift = cov.plan_slice(tid, [ch_shift], idx)
            self.assertTrue(plan_shift["full"])

    def test_case_coverage_soundness_guards_and_uncovered_branch(self):
        tid = "tests/test_optimizer.py::TestOptimizer::test_simplify"
        cov = CaseCoverage({
            tid: {
                "contexts": [
                    "shared",
                    "case:optimizer/simplify.sql#0",
                    "case:optimizer/simplify.sql#1",
                    "case:optimizer/simplify.sql#2",
                ],
                "masks": ["0x1", "0x2", "0x4", "0xa"],  # #0 & #2
                "times_us": [0, 8000, 1500, 900],
                "lines": {
                    "sqlglot/optimizer/simplify.py": {
                        "1": 0,  # shared
                        "3": 1,  # #0 only (if a:)
                        "7": 3,  # #0 and #2 (return b + 1)
                    }
                },
                "opens": {},
                "class_reads": {},
                "dialect_reads": {},
                "attributes": {},
                "keys": {},
                "raw_class_reads": {},
            }
        })
        idx = _DummyIndex(
            layout={"sqlglot/optimizer/simplify.py": ([[2, 5], [6, 8]], [])},
            statements={"sqlglot/optimizer/simplify.py": [[2, 5]]},
        )
        old_src = (
            "GLOBAL_X = 1\n"
            "def f1(a):\n"
            "    if a:\n"
            "        return 1\n"
            "    return 2\n"
            "def f2(b):\n"
            "    return b + 1\n"
        )
        with TemporaryDirectory() as tmp:
            root = Path(tmp).resolve()
            # Line 7 inside f2 hits #0 and #2 -> sorted cheapest-first
            ch_f2 = _diff_change(root, "sqlglot/optimizer/simplify.py", old_src, old_src.replace("return b + 1", "return b + 2"))
            sp = cov.plan_slice(tid, [ch_f2], idx)
            self.assertFalse(sp["full"])
            self.assertEqual(sp["fixture_indices"]["optimizer/simplify.sql"], [2, 0])

            # can_slice_py=False -> conservative full fallback
            sp_no_slice = cov.plan_slice(tid, [ch_f2], idx, can_slice_py=False)
            self.assertTrue(sp_no_slice["full"])

            # Uncovered line 4 inside f1 widens to cases that entered f1 (#0)
            ch_uncov = _diff_change(root, "sqlglot/optimizer/simplify.py", old_src, old_src.replace("return 1", "return 9"))
            sp_uncov = cov.plan_slice(tid, [ch_uncov], idx)
            self.assertFalse(sp_uncov["full"])
            self.assertEqual(sp_uncov["fixture_indices"]["optimizer/simplify.sql"], [0])

            # Top-level edit -> full fallback
            ch_top = _diff_change(root, "sqlglot/optimizer/simplify.py", old_src, old_src.replace("GLOBAL_X = 1", "GLOBAL_X = 2"))
            self.assertTrue(cov.plan_slice(tid, [ch_top], idx)["full"])

    def test_tpcds_two_phase_plan_split(self):
        cov = CaseCoverage({
            TEST_EXECUTE_TPCDS: {
                "contexts": ["shared", "case:executor/0", "case:executor/1", "case:phase2/1"],
                "masks": ["0x1", "0x2", "0x4", "0x8"],
                "times_us": [0, 5000, 6000, 40000],
                "lines": {
                    "sqlglot/planner.py": {"5": 1},
                    "sqlglot/executor/python.py": {"10": 3},
                },
                "opens": {},
                "class_reads": {},
                "dialect_reads": {},
                "attributes": {},
                "keys": {},
                "raw_class_reads": {},
            }
        })
        idx = _DummyIndex(
            layout={
                "sqlglot/planner.py": ([[3, 8]], []),
                "sqlglot/executor/python.py": ([[8, 12]], []),
            }
        )
        old_p = "x = 0\n\ndef plan_q():\n    a = 1\n    return a\n"
        old_e = "y = 0\n\n\n\n\n\n\ndef exec_q():\n    a = 1\n    return a\n"
        with TemporaryDirectory() as tmp:
            root = Path(tmp).resolve()
            ch_plan = _diff_change(root, "sqlglot/planner.py", old_p, old_p.replace("return a", "return a + 1"))
            sp_p = cov.plan_slice(TEST_EXECUTE_TPCDS, [ch_plan], idx)
            self.assertFalse(sp_p["full"])
            self.assertEqual(sp_p["exec_indices"], [0])
            self.assertEqual(sp_p["phase2_indices"], [])

            ch_exec = _diff_change(root, "sqlglot/executor/python.py", old_e, old_e.replace("return a", "return a + 1"))
            sp_e = cov.plan_slice(TEST_EXECUTE_TPCDS, [ch_exec], idx)
            self.assertFalse(sp_e["full"])
            self.assertEqual(sp_e["phase2_indices"], [1])

    def test_rewrite_subtest_method_gates_iterations(self):
        fake_mod = types.ModuleType("_dummy_subtest_mod")

        class DummyCase:
            def __init__(self):
                self.ran = []

            def subTest(self, **kwargs):
                class _Ctx:
                    def __enter__(self_c):
                        return None

                    def __exit__(self_c, *a):
                        return False

                return _Ctx()

            def target(self):
                for a in (10, 20):
                    for b in (1, 2, 3):
                        with self.subTest(a=a, b=b):
                            self.ran.append((a, b))

        fake_mod.DummyCase = DummyCase
        DummyCase.__module__ = fake_mod.__name__
        sys.modules[fake_mod.__name__] = fake_mod
        try:
            self.assertTrue(_rewrite_subtest_method(DummyCase, "target", [1, 4]))
            inst = DummyCase()
            inst.target()
            self.assertEqual(inst.ran, [(10, 2), (20, 2)])
        finally:
            sys.modules.pop(fake_mod.__name__, None)

    def test_heavy_stream_result_failfast_and_zero_shortcircuit(self):
        visited = []
        emitted = []
        aborted = []

        class SubTestCase(unittest.TestCase):
            def test_one(self):
                for i in range(100):
                    with self.subTest(i=i):
                        visited.append(("one", i))
                        if i == 0:
                            self.fail("boom")

            def test_two(self):
                visited.append(("two", 0))

            def test_zero(self):
                visited.append(("zero", 0))
                self.fail("zero fail")

        t1 = SubTestCase("test_one")
        t2 = SubTestCase("test_two")
        tz = SubTestCase("test_zero")
        for leaf in (t1, t2, tz):
            _wrap_call_test_method(leaf)

        fix = Fixtures(Path("."), [])
        res = _HeavyStreamResult(
            {t1: 0, t2: 1, tz: 2},
            fix,
            lambda: False,
            lambda: 0,
            lambda idx, r: emitted.append((idx, r)),
            lambda: aborted.append(True),
            {SubTestCase},
            zero_indices=frozenset({2}),
        )
        unittest.TestSuite([t1, t2, tz]).run(res)
        self.assertEqual(visited, [("one", 0), ("two", 0), ("zero", 0)])
        self.assertEqual(emitted, [(1, 0)])
        self.assertTrue(res.nonzero_failed)
        self.assertEqual(aborted, [])

    @unittest.skipUnless(hasattr(os, "pidfd_open") and hasattr(os, "memfd_create"), "Linux verifier")
    def test_warm_suite_verify_heavy_streaming_and_timeout(self):
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "sqlglot").mkdir()
            (root / "sqlglot/__init__.py").write_text("")
            (root / "tests").mkdir()
            (root / "tests/__init__.py").write_text("")
            (root / "tests/test_stream.py").write_text(
                "import time, unittest\n"
                "class StreamCase(unittest.TestCase):\n"
                "    def test_fast_pass(self): pass\n"
                "    def test_slow_hang(self): time.sleep(5)\n"
            )
            ids = [
                "tests/test_stream.py::StreamCase::test_fast_pass",
                "tests/test_stream.py::StreamCase::test_slow_hang",
            ]
            suite = WarmSuite(root, ids)
            suite.ready = True
            with sys.path_importer_cache and unittest.mock.patch.object(sys, "path", [str(root), *sys.path]):
                passed, readers = suite.verify_heavy(
                    types.SimpleNamespace(all=3),
                    [],
                    [(0, False, False), (1, False, False)],
                    (),
                    None,
                    monotonic() + 2,
                    0.35,
                    {},
                )
            self.assertEqual(passed, 1)
            self.assertEqual(readers, 0)

    def test_stress_guards_and_linear_scaling(self):
        with TemporaryDirectory() as tmp:
            root = Path(tmp).resolve()
            old = "def step(n):\n    return n + 1\n"
            c_ok = _diff_change(root, "sqlglot/optimizer/qualify.py", old, "def step(n):\n    return n + 2\n")
            self.assertTrue(stress_guard([c_ok], threshold=60))
            self.assertTrue(micro_oracle_guard(TEST_QUALIFY_CTE_CHAIN, [c_ok], use_micro_oracles=True, use_stress_probes=True))
            self.assertFalse(micro_oracle_guard(TEST_QUALIFY_CTE_CHAIN, [c_ok], use_micro_oracles=True, use_stress_probes=False))

            c_rec = _diff_change(root, "sqlglot/serde.py", old, "import sys\ndef step(n):\n    sys.setrecursionlimit(2000)\n    return n\n")
            self.assertFalse(micro_oracle_guard(TEST_SERDE_RECURSION, [c_rec]))
            self.assertFalse(micro_oracle_guard(TEST_DEEP_AST_ANNOTATION, [c_rec]))
            self.assertFalse(micro_oracle_guard(TEST_NAMED_SELECTS_CHAIN, [c_rec]))

        def quad_work(n):
            acc = 0
            for i in range(n * n * 4):
                acc += i
            return acc

        self.assertFalse(_check_linear_scaling(lambda n: n, quad_work, 100, 200, n_esc=400))

    def test_gen_mem_escalate_and_dockerfile_switches(self):
        from micro_oracles import target_dialects_for_paths

        class FakeDialect:
            __module__ = "sqlglot.dialects.mysql"

            class Generator:
                __module__ = "sqlglot.generators.mysql"

            @classmethod
            def get_or_raise(cls, name):
                return cls()

            @classmethod
            def generator(cls):
                return None

        fake_dialects = types.ModuleType("sqlglot.dialects")
        fake_dialects.Dialect = FakeDialect
        fake_dialects.Dialects = ["fake"]
        fake_dialect_sub = types.ModuleType("sqlglot.dialects.dialect")
        fake_dialect_sub.Dialect = FakeDialect
        fake_dialect_sub.Dialects = ["fake"]
        fake_sqlglot = types.ModuleType("sqlglot")
        fake_sqlglot.dialects = fake_dialects

        saved = {k: sys.modules.get(k) for k in ("sqlglot", "sqlglot.dialects", "sqlglot.dialects.dialect")}
        sys.modules["sqlglot"] = fake_sqlglot
        sys.modules["sqlglot.dialects"] = fake_dialects
        sys.modules["sqlglot.dialects.dialect"] = fake_dialect_sub
        try:
            self.assertEqual(target_dialects_for_paths(["sqlglot/dialects/mysql.py"]), ["fake"])
            self.assertEqual(target_dialects_for_paths(["sqlglot/generators/mysql.py"]), ["fake"])
            self.assertIsNone(target_dialects_for_paths(["sqlglot/parser.py"]))
            self.assertTrue(check_generator_memory(dialect_names=["fake"], escalate=True))
            self.assertTrue(check_generator_memory(dialect_names=["fake"], escalate=False))
        finally:
            for k, old in saved.items():
                if old is None:
                    sys.modules.pop(k, None)
                else:
                    sys.modules[k] = old

        dockerfile = (Path(__file__).resolve().parent.parent / "Dockerfile").read_text()
        for sw in (
            "INLINE_POOL",
            "MICRO_ORACLES",
            "SETUPCLASS_DEAMORT",
            "ROW_SLICE",
            "TWOPHASE_TPC",
            "STRESS_PROBES",
            "GEN_MEM_ESCALATE",
            "ISOLATED_SCHEDULE",
            "REACH_GATE",
        ):
            self.assertIn(f"ARG {sw}=1", dockerfile)
            self.assertIn(f"{sw}=${sw}", dockerfile)

    def test_runnable_switches_and_tpcds_max_mismatches(self):
        opt = "tests/test_optimizer.py::TestOptimizer::test_optimize"
        tpcds = "tests/test_executor.py::TestExecutor::test_execute_tpcds"
        self.assertFalse(runnable(opt, inline_pool=False))
        self.assertTrue(runnable(opt, inline_pool=True))
        self.assertFalse(runnable(tpcds, inline_pool=True, setupclass_deamort=False))
        self.assertTrue(runnable(tpcds, inline_pool=True, setupclass_deamort=True))

        plain_raw = b"# invalid\nSELECT a FROM x\n# invalid2\nSELECT b FROM y\n"
        self.assertEqual(
            parse_fixture_rows("optimizer/qualify_columns__invalid.sql", plain_raw),
            ("# invalid\nSELECT a FROM x", "# invalid2\nSELECT b FROM y"),
        )
        self.assertTrue(_has_trivial_teardown(HeavyStep2Tests))
        self.assertIn("len(mismatched) > max_mismatches", Path(slicer.__file__).read_text())
        self.assertEqual(compute_tpcds_mismatches.__defaults__, (None, None))

    @unittest.skipUnless(hasattr(os, "pidfd_open") and hasattr(os, "memfd_create"), "Linux verifier")
    def test_fork_masks_stream_sigprof_vs_crash(self):
        def run_prof(wfd):
            os.write(wfd, b"P 0 1\nP 1 2\n")
            os.kill(os.getpid(), signal.SIGPROF)

        def run_segv(wfd):
            os.write(wfd, b"P 0 1\n")
            os.kill(os.getpid(), signal.SIGSEGV)

        def run_abort(wfd):
            os.write(wfd, b"P 0 1\nABORT\n")

        self.assertEqual(fork_masks_stream(run_prof, monotonic() + 5, 2.0), (3, 3))
        self.assertEqual(fork_masks_stream(run_segv, monotonic() + 5, 2.0), (0, 0))
        self.assertEqual(fork_masks_stream(run_abort, monotonic() + 5, 2.0), (0, 0))

    @unittest.skipUnless(hasattr(os, "pidfd_open"), "Linux verifier")
    def test_stream_cpu_cutoff_discards_receipts_from_crashed_child(self):
        read_pid, write_pid = os.pipe()
        self.addCleanup(os.close, read_pid)
        self.addCleanup(os.close, write_pid)
        def child(fd):
            os.write(fd, b"P 1 4\n")
            os.write(write_pid, str(os.getpid()).encode())
            os.kill(os.getpid(), signal.SIGSEGV)

        def cpu_samples():
            yield 0.0
            # Deliver the exhausted budget immediately after the buffered
            # receipt and the crash are both observable to the parent.
            child_fd = os.pidfd_open(int(os.read(read_pid, 32)))
            try:
                self.assertTrue(select.select([child_fd], [], [], 2)[0])
            finally:
                os.close(child_fd)
            yield 2.5

        with unittest.mock.patch("verify.cgroup_cpu", side_effect=cpu_samples()):
            self.assertEqual(fork_masks_stream(child, monotonic() + 5, 2), (0, 0))

    def test_check_generator_memory_multidialect_batched(self):
        leaked = []
        leak_on = False

        class CleanDialect:
            @classmethod
            def generator(cls):
                return None

        class LeakDialect:
            @classmethod
            def generator(cls):
                if leak_on:
                    leaked.append("x" * 128)
                return None

        class FakeDialect:
            @classmethod
            def get_or_raise(cls, name):
                return LeakDialect if name == "leak" else CleanDialect

        fake_dialects = types.ModuleType("sqlglot.dialects")
        fake_dialects.Dialect = FakeDialect
        fake_dialects.Dialects = ["clean", "leak"]
        fake_dialect_sub = types.ModuleType("sqlglot.dialects.dialect")
        fake_dialect_sub.Dialect = FakeDialect
        fake_dialect_sub.Dialects = ["clean", "leak"]
        fake_sqlglot = types.ModuleType("sqlglot")
        fake_sqlglot.dialects = fake_dialects

        saved = {k: sys.modules.get(k) for k in ("sqlglot", "sqlglot.dialects", "sqlglot.dialects.dialect")}
        sys.modules["sqlglot"] = fake_sqlglot
        sys.modules["sqlglot.dialects"] = fake_dialects
        sys.modules["sqlglot.dialects.dialect"] = fake_dialect_sub
        try:
            self.assertTrue(check_generator_memory(dialect_names=["clean", "leak"], escalate=True))
            self.assertTrue(check_generator_memory(dialect_names=["clean", "leak"], escalate=False))
            leak_on = True
            self.assertFalse(check_generator_memory(dialect_names=["clean", "leak"], escalate=True))
            self.assertFalse(check_generator_memory(dialect_names=["clean", "leak"], escalate=False))
        finally:
            for k, old in saved.items():
                if old is None:
                    sys.modules.pop(k, None)
                else:
                    sys.modules[k] = old
