import mmap
import os
import resource
import sys
from pathlib import Path
import tempfile
import time
import unittest
from unittest.mock import patch

from bounded_batch import CHILD_ADDRESS_SPACE, bounded_results
from mutation_summaries import AnalysisLimit, Project, build
from patching import MAX_CHANGED_LINES, MAX_PATCH_BYTES, Change, UnknownPatch, apply_patch
from shared_writes import has_shared_write


def append_file(path, count, payload=b"    a = 1"):
    return (f"--- a/{path}\n+++ b/{path}\n@@ -1,0 +2,{count} @@\n".encode()
            + (b"+" + payload + b"\n") * count)


class LimitsTest(unittest.TestCase):
    def test_change_count_across_files_and_header_shaped_data(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp).resolve()
            for name in ("a.py", "b.py"):
                (root / name).write_text("def f():\n")
            exact = append_file("a.py", MAX_CHANGED_LINES)
            self.assertEqual(len(apply_patch(exact, root)[0].added), MAX_CHANGED_LINES)
            with self.assertRaisesRegex(UnknownPatch, "changed line limit"):
                apply_patch(exact + append_file("b.py", 1), root)
            # An added source line can look just like a second file header.
            with self.assertRaisesRegex(UnknownPatch, "changed line limit"):
                apply_patch(append_file("a.py", MAX_CHANGED_LINES + 1, b"++ b/fake"), root)

    def test_size_fallback_precedes_source_and_ast_access(self):
        with patch("patching.base", side_effect=AssertionError("opened pinned file")):
            with self.assertRaisesRegex(UnknownPatch, "changed line limit"):
                apply_patch(append_file("absent.py", MAX_CHANGED_LINES + 1), Path("/absent"))
            with self.assertRaisesRegex(UnknownPatch, "byte limit"):
                apply_patch(b"x" * (MAX_PATCH_BYTES + 1), Path("/absent"))
        self.assertTrue(has_shared_write(None, range(MAX_CHANGED_LINES + 1)))

    def test_heavy_summary_becomes_opaque(self):
        source = "def helper(x, y):\n    return x[0]\n"
        with patch("mutation_summaries.FUNCTION_WORK", 1):
            project = Project(build([("sqlglot/example.py", source)]))
        key = project.resolve("m/sqlglot.example:helper")
        self.assertEqual(project.data["masks"][key], 3)

    def test_patch_work_limit_precedes_selection(self):
        src = b"def helper(x): return x[0]\n"
        path = "sqlglot/example.py"
        project = Project(build([(path, src)]))
        with patch("mutation_summaries.PATCH_WORK", 1):
            with self.assertRaises(AnalysisLimit):
                project.patched([Change(path, src, src, added={1})])

    def test_large_file_skipped_and_dead_worker_replaced(self):
        if sys.platform != "linux":
            # Exercise IPC and deadlines on hosts without the Linux memory guard.
            self.enterContext(patch("bounded_batch.limit_child_resources"))
        def analyze(path):
            if path.name == "slow":
                time.sleep(10)
            if path.name == "crash":
                os._exit(1)
            if path.name == "huge":
                path.with_suffix(".opened").touch()
            return 1, 2

        with tempfile.TemporaryDirectory() as tmp:
            paths = [Path(tmp)/n for n in ("huge", "slow", "fast", "crash", "last")]
            for p in paths:
                p.touch()
            with paths[0].open("wb") as f:
                f.truncate(MAX_PATCH_BYTES + 1)
            rows = list(bounded_results(paths, analyze, time.monotonic() + 10, per_commit=0.35))
            self.assertEqual([r for _, r in rows], [None, None, (1, 2), None, (1, 2)])
            self.assertFalse(paths[0].with_suffix(".opened").exists())

    def test_worker_without_a_limit_never_analyzes(self):
        def analyze(path):
            path.with_suffix(".opened").touch()
            return 1, 2

        with tempfile.TemporaryDirectory() as tmp, patch("bounded_batch.limit_child_resources", side_effect=ValueError):
            paths = [Path(tmp)/n for n in ("first", "second")]
            for path in paths:
                path.touch()
            self.assertEqual(list(bounded_results(paths, analyze, time.monotonic() + 5)),
                             [(path, None) for path in paths])
            self.assertFalse(list(Path(tmp).glob("*.opened")))

    @unittest.skipUnless(sys.platform == "linux", "Linux address-space limit")
    def test_out_of_memory_worker_widens_and_restarts_for_next_commit(self):
        parent_limits = resource.getrlimit(resource.RLIMIT_AS)

        def analyze(path):
            soft, hard = resource.getrlimit(resource.RLIMIT_AS)
            if path.name == "exhaust":
                # An anonymous mapping requests virtual space without touching pages.
                with mmap.mmap(-1, CHILD_ADDRESS_SPACE):
                    return "allocation unexpectedly succeeded"
            return os.getpid(), soft, hard

        with tempfile.TemporaryDirectory() as tmp:
            paths = [Path(tmp) / name for name in ("first", "exhaust", "last")]
            for path in paths:
                path.touch()
            rows = list(bounded_results(paths, analyze, time.monotonic() + 8))
        self.assertEqual([path for path, _ in rows], paths)
        limit = min([CHILD_ADDRESS_SPACE] + [v for v in parent_limits if v != resource.RLIM_INFINITY])
        first, failure, last = [result for _, result in rows]
        self.assertEqual(first[1:], (limit, limit))
        self.assertIsNone(failure)
        self.assertEqual(last[1:], (limit, limit))
        self.assertNotEqual(first[0], last[0])
        self.assertEqual(resource.getrlimit(resource.RLIMIT_AS), parent_limits)

    def test_total_deadline_interrupts_current_and_skips_remaining(self):
        if sys.platform != "linux":
            # Exercise IPC and deadlines on hosts without the Linux memory guard.
            self.enterContext(patch("bounded_batch.limit_child_resources"))
        def analyze(path):
            path.with_suffix(".opened").touch()
            if path.name == "blocked":
                time.sleep(10)
            return 4, 5

        with tempfile.TemporaryDirectory() as tmp:
            paths = [Path(tmp)/n for n in ("ready", "blocked", "unread")]
            for p in paths:
                p.touch()
            rows = list(bounded_results(paths, analyze, time.monotonic() + 0.5, per_commit=5))
            self.assertEqual([r for _, r in rows], [(4, 5), None, None])
            self.assertTrue(paths[1].with_suffix(".opened").exists())
            self.assertFalse(paths[2].with_suffix(".opened").exists())
