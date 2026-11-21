import difflib
import os
import resource
from pathlib import Path
import sys
import tempfile
import unittest
from time import monotonic
from unittest.mock import patch

from cone import body_changes, serialization_edit
from patching import Change, apply_patch
from selector import equal_trees
from verify import CHILD_ADDRESS_SPACE, WarmSuite, fork_masks


class ShapeTest(unittest.TestCase):
    def changed(self, old, new):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            (root / "example.py").write_text(old)
            diff = "".join(difflib.unified_diff(old.splitlines(True), new.splitlines(True),
                                               "a/example.py", "b/example.py"))
            return apply_patch(diff.encode(), root)[0]

    def test_conditional_definition_needs_reimport(self):
        old = "if enabled:\n    def compute():\n        return 7\n"
        self.assertIsNone(body_changes(self.changed(old, old.replace("7", "8")), equal_trees))

    def test_pickle_method_body_without_protocol_name_on_changed_line(self):
        old = "class Record:\n    def __reduce__(self):\n        return int, (42,)\n"
        self.assertTrue(serialization_edit(self.changed(old, old.replace("42", "43"))))

    def test_multiple_edited_functions_and_unchanged_headers(self):
        old = "def a():\n    return 1\n\nclass C:\n    def b(self):\n        return 2\n"
        changed = self.changed(old, old.replace("return 1", "x = 3\n    return x").replace("return 2", "return 4"))
        self.assertEqual([name for name, _, _ in body_changes(changed, equal_trees)], ["a", "C.b"])


class Readers:
    all = (1 << 12) - 1

    def binding_readers(self, bindings):
        return 1 << 11 if any(b[-1] == "history" for b in bindings) else None


@unittest.skipUnless(hasattr(os, "pidfd_open") and hasattr(os, "memfd_create"), "Linux process verifier")
class ForkTest(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        for pkg in ("tests", "sqlglot"):
            (self.root / pkg).mkdir()
            (self.root / pkg / "__init__.py").write_text("")
        (self.root / "sqlglot/model.py").write_text("value = 1\nhistory = {'nested': []}\n")
        self.change = Change("sqlglot/model.py", b"", b"value = 9\nhistory = {'nested': []}\n")

    def verify(self, body, names, *, watch=(), cap=2, changes=None, writers=0):
        testfile = "tests/test_example.py"
        (self.root / testfile).write_text(
            "import os, sys, unittest\nfrom pathlib import Path\nfrom sqlglot.model import value, history\n"
            "class Example(unittest.TestCase):\n" + body)
        ids = [testfile + "::Example::" + name for name in names]
        suite = WarmSuite(self.root, ids)
        suite.ready = True
        with patch.object(sys, "path", [str(self.root), *sys.path]):
            return suite.verify(Readers(), [self.change] if changes is None else changes,
                                list(range(len(names))), watch, None, monotonic() + 4, cap, writers)

    def test_overlay_file_order_shared_class_fixture_and_subtest(self):
        body = """
    @classmethod
    def setUpClass(cls):
        cls.calls = []
    def test_first(self):
        self.assertEqual(value, 9)
        self.calls.append(value)
        history['nested'].append(value)
    def test_second(self):
        self.assertEqual(self.calls, [9])
    def test_sub(self):
        with self.subTest(i=1):
            self.assertEqual(value, 1)
    def test_error(self):
        raise ValueError('ordinary test error')
    @unittest.skip('not runnable')
    def test_skip(self):
        pass
"""
        result = self.verify(body, ["test_first", "test_second", "test_sub", "test_error", "test_skip"],
                             watch=("history",))
        self.assertEqual(result, (0b11, 1 << 11))
        self.assertEqual((self.root / "sqlglot/model.py").read_text().splitlines()[0], "value = 1")

    def test_indirect_writer_widens_to_binding_absent_from_edited_function(self):
        body = """
    def test_writer(self):
        def publish(values):
            values.append(42)
        publish(next(iter(history.values())))
"""
        self.assertEqual(self.verify(body, ["test_writer"], writers=1), (1, 1 << 11))
        undo = "    def test_restore(self): history['nested'].clear()\n"
        self.assertEqual(self.verify(body + undo, ["test_writer", "test_restore"], writers=3),
                         (3, 1 << 11))
        missing = "    @unittest.skip('writer unavailable')\n    def test_writer(self): pass\n"
        self.assertEqual(self.verify(missing, ["test_writer"], writers=1), (0, Readers.all))

    def test_removed_write_adds_pristine_readers(self):
        old = "value = 1\nhistory = {'nested': []}\ndef record(): history['nested'].append(8)\n"
        (self.root / "sqlglot/model.py").write_text(old)
        (self.root / "tests/test_example.py").write_text(
            "import unittest\nfrom sqlglot.model import record\nclass Example(unittest.TestCase):\n"
            "    def test_writer(self): record()\n")
        change = Change("sqlglot/model.py", old.encode(), old.replace("history['nested'].append(8)", "pass").encode())
        suite = WarmSuite(self.root, ["tests/test_example.py::Example::test_writer"])
        with patch.dict(sys.modules), patch.object(sys, "path", [str(self.root), *sys.path]):
            for key in tuple(sys.modules):
                if key.split(".")[0] in ("tests", "sqlglot"):
                    del sys.modules[key]
            suite.import_suite()
            suite.ready = True
            self.assertEqual(suite.check(Readers(), [change], [0], (), None, 1, monotonic() + 4, 3),
                             (1, 1 << 11))

    def test_fixture_error_crash_timeout_and_import_error_discard_passes(self):
        first = "    def test_first(self): self.assertEqual(value, 9)\n"
        for action in ("os._exit(4)", "while True: pass", "import line_c_missing_example"):
            with self.subTest(action=action):
                body = first + "    def test_second(self):\n        " + action + "\n"
                self.assertEqual(self.verify(body, ["test_first", "test_second"], cap=0.3), (0, 0))
        body = first + "    @classmethod\n    def tearDownClass(cls): raise RuntimeError('teardown')\n"
        self.assertEqual(self.verify(body, ["test_first"]), (0, 0))

    def test_sigsegv_discards_earlier_passes_and_zeroes_the_core_limit(self):
        limits = fork_masks(lambda: resource.getrlimit(resource.RLIMIT_CORE), (1, 1), monotonic() + 4, 2)
        self.assertEqual(limits, (0, 0))
        first = "    def test_first(self): pass\n"
        crash = "    def test_second(self):\n        import signal\n        signal.raise_signal(signal.SIGSEGV)\n"
        for writers, expected in ((0, (0, 0)), (2, (0, Readers.all))):
            with self.subTest(writers=writers):
                self.assertEqual(self.verify(first + crash, ["test_first", "test_second"], writers=writers), expected)
        self.assertEqual(self.verify(first, ["test_first"]), (1, 0))

    def test_address_space_limit_discards_passes_and_spares_parent(self):
        parent_limits = resource.getrlimit(resource.RLIMIT_AS)
        limits = fork_masks(lambda: resource.getrlimit(resource.RLIMIT_AS), (0, 0), monotonic() + 4, 2)
        expected = min([CHILD_ADDRESS_SPACE] + [v for v in parent_limits if v != resource.RLIM_INFINITY])
        self.assertEqual(limits, (expected, expected))
        first = "    def test_first(self): pass\n"
        for action in ("bytearray", "mmap"):
            with self.subTest(action=action):
                # mmap reserves address space without touching pages. Only attempt the
                # large bytearray once the real kernel limit is known to be in force.
                allocate = f"bytearray({expected})" if action == "bytearray" else f"mmap.mmap(-1, {expected})"
                body = first + f"""
    def test_large(self):
        import mmap, resource
        assert resource.getrlimit(resource.RLIMIT_AS) == ({expected}, {expected})
        {allocate}
"""
                self.assertEqual(self.verify(body, ["test_first", "test_large"]), (0, 0))
        self.assertEqual(resource.getrlimit(resource.RLIMIT_AS), parent_limits)
        self.assertEqual(self.verify(first, ["test_first"]), (1, 0))

    def test_fixture_must_be_seen_by_each_passing_case(self):
        relative = "tests/fixtures/example.sql"
        fixture = self.root / relative
        fixture.parent.mkdir()
        fixture.write_text("pinned")
        body = (f"    def test_reads(self): self.assertEqual(Path({str(fixture)!r}).read_text(), 'patched')\n"
                "    def test_no_read(self): pass\n")
        result = self.verify(body, ["test_reads", "test_no_read"],
                             changes=[Change(relative, b"pinned", b"patched")])
        self.assertEqual(result, (1, 0))
        self.assertEqual(fixture.read_text(), "pinned")
