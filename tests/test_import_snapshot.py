import ast
import importlib
import io
import json
import marshal
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from types import SimpleNamespace
from time import monotonic
from unittest.mock import patch

from import_state import capture, import_graph, modules, observe_initializers
from patching import Change
from batch_entry import run_batch
from selector import Index
from snapshot_cone import ImportSnapshot, key_site, outer_functions
from verify import CHILD_ADDRESS_SPACE, is_project


class Readers:
    all = (1 << 12) - 1
    data = {'layout': {p: [] for p in ('sqlglot/__init__.py', 'sqlglot/source.py', 'sqlglot/copy.py')}}

    def import_users(self, path):
        return self.bits('users', path)

    def bits(self, table, key):
        return {('users', 'sqlglot/source.py'): 0b1111, ('users', 'sqlglot/copy.py'): 0b1011,
                ('class_reads', 'sqlglot.source.Settings.TABLE'): 1,
                ('class_reads', 'sqlglot.copy.Consumer.TABLE'): 2,
                ('keys', "'x'"): 8, ('opens', 'sqlglot/source.py'): 16}.get((table, key), 0)


@unittest.skipUnless(hasattr(os, 'pidfd_open'), 'Linux snapshot fork')
class SnapshotTest(unittest.TestCase):
    def setUp(self):
        temp = tempfile.TemporaryDirectory()
        self.addCleanup(temp.cleanup)
        self.root = Path(temp.name)
        pkg = self.root / 'sqlglot'
        pkg.mkdir()
        (pkg/'__init__.py').write_text('class Dialect: classes = {}\n')
        self.before = ("class Settings:\n    TABLE = {'outer': {'x': 1}}\n"
                       "class Box:\n    __slots__ = ('value',)\n"
                       "    def __init__(self): self.value = 12\n"
                       "TEMPLATE = Box()\nA = []\nB = A\n")
        (pkg/'source.py').write_text(self.before)
        (pkg/'copy.py').write_text("from .source import Settings\nclass Consumer:\n    TABLE = {**Settings.TABLE}\n")
        self.enterContext(patch.dict(sys.modules))
        self.enterContext(patch.object(sys, 'path', [str(self.root), *sys.path]))
        for key in list(sys.modules):
            if is_project(key) and key.split('.')[0] == 'sqlglot':
                del sys.modules[key]
        importlib.import_module('sqlglot.copy')
        index = Readers()
        state, tables = capture(modules())
        data = self.root/'base.bin'
        data.write_bytes(marshal.dumps((state, tables, import_graph(self.root, index.data['layout']))))
        self.snapshot = ImportSnapshot(index, self.root)
        self.snapshot.prepare(data)

    def select(self, after):
        c = Change('sqlglot/source.py', self.before.encode(), after.encode())
        return self.snapshot.select([c], monotonic()+5, 3)

    def test_eager_helper_import_of_resident_module(self):
        (self.root/'sqlglot'/'dynamic.py').write_text(
            "from importlib import import_module\ndef get(): return import_module('sqlglot.source')\nVALUE = get().A\n")
        graph = {'sqlglot.dynamic': set(), 'sqlglot.source': set()}
        with observe_initializers(graph):
            importlib.import_module('sqlglot.dynamic')
        self.assertEqual(graph['sqlglot.dynamic'], {'sqlglot.source'})

    def test_census_includes_recorded_subclass_readers(self):
        index = self.snapshot.index
        child = 'sqlglot.copy:Derived'
        parent = 'sqlglot.source:Settings'
        key = 'sqlglot.copy.Derived.TABLE'
        index.census = SimpleNamespace(classes={child: {'mro': [child, parent]}})
        index.data = dict(index.data, class_reads={key: 0})
        old_bits = index.bits
        index.bits = lambda table, name: 32 if (table, name) == ('class_reads', key) else old_bits(table, name)
        self.snapshot.inherited = self.snapshot.inherited_readers()
        self.assertEqual(self.select(self.before.replace("'x': 1", "'x': 2"))[0], 1 | 2 | 8 | 16 | 32)

    def test_nested_key_and_copied_table(self):
        chosen, protected = self.select(self.before.replace("'x': 1", "'x': 2"))
        self.assertEqual(chosen, 1 | 2 | 8 | 16)
        self.assertEqual(protected, 16)
        self.assertEqual(sys.modules['sqlglot.source'].Settings.TABLE['outer']['x'], 1)

    def test_unattributed_slot_and_split_alias_use_importers(self):
        for after in (self.before.replace('= 12', '= 13'), self.before.replace('B = A', 'B = list(A)')):
            with self.subTest(after=after):
                chosen, _ = self.select(after)
                self.assertEqual(chosen, 15 | 16)

    def test_snapshot_sigsegv_selects_full_suite_and_next_snapshot_runs(self):
        after = self.before + "import signal\nsignal.raise_signal(signal.SIGSEGV)\n"
        self.assertEqual(self.select(after), (Readers.all, Readers.all))
        self.assertEqual(self.select(self.before.replace("'x': 1", "'x': 2")), (1 | 2 | 8 | 16, 16))

    def test_snapshot_allocation_failure_selects_full_suite(self):
        after = self.before + f"import mmap\nregion = mmap.mmap(-1, {CHILD_ADDRESS_SPACE})\n"
        self.assertEqual(self.select(after), (Readers.all, Readers.all))
        self.assertEqual(self.select(self.before.replace("'x': 1", "'x': 2")), (1 | 2 | 8 | 16, 16))

    def test_process_changes_and_import_errors_require_every_test(self):
        for tail in ("import sys\nsys.argv.append('extra')", "import os\nos.environ['SNAP_TEST'] = '1'",
                     "import sys\nsys.setrecursionlimit(4512)", "import os\nos.path.join = None",
                     "import missing_snapshot_module"):
            with self.subTest(tail=tail):
                self.assertEqual(self.select(self.before+tail+'\n'), (Readers.all, Readers.all))
        self.assertNotIn('SNAP_TEST', os.environ)


class BatchRecoveryTest(unittest.TestCase):
    def test_batch_setup_errors_emit_every_full_plan(self):
        temp = tempfile.TemporaryDirectory()
        self.addCleanup(temp.cleanup)
        root = Path(temp.name)
        (root / "commits").mkdir()
        names = ['a"quote', "middle", "third"]
        for name in reversed(names):
            (root / "commits" / (name + ".patch")).touch()
        tests = [{"id": str(i), "number": i, "seconds": 0.2} for i in range(7)]
        manifest = root / "tests.json"
        maps = root / "maps.json"
        maps.write_text(json.dumps({"ids": list(range(11))}))
        import pinned_data
        subprocess.run([sys.executable, pinned_data.__file__, str(maps)], check=True)
        maps.write_text("damaged")
        self.enterContext(patch("batch_entry.__file__", str(root / "batch_entry.py")))
        self.enterContext(patch("selector.__file__", str(root / "selector.py")))

        def check_full(numbers):
            output = io.StringIO()
            run_batch(output, root, root, monotonic())
            rows = [json.loads(line) for line in output.getvalue().splitlines()]
            self.assertEqual([r["commit"] for r in rows], names)
            for row in rows:
                self.assertLessEqual(len(row["workers"]), 8)
                self.assertEqual(sorted(n for w in row["workers"] for n in w), list(numbers))

        for bad in (None, "{", '{"tests": null}'):
            with self.subTest(unreadable_manifest=bad):
                if bad is not None:
                    manifest.write_text(bad)
                check_full(range(11))
        manifest.write_text(json.dumps({"tests": [{"number": 31}, {"number": 45}]}))
        check_full([31, 45])  # Runtime numbers survive malformed timing data.
        manifest.write_text(json.dumps({"tests": tests}))
        with patch("pinned_data.load", side_effect=OSError("unreadable index")) as load:
            check_full(range(7))
            load.assert_called_once()
        with patch("selector.load_index", return_value=Index({"ids": [], "masks": []})), \
                patch("verify.WarmSuite.warm", side_effect=RuntimeError("warmup failed")) as warm, \
                patch("bounded_batch.bounded_results") as analyze:
            check_full(range(7))
            warm.assert_called_once()
            analyze.assert_not_called()

    def test_parent_snapshot_key_error_only_widens_affected_commit(self):
        temp = tempfile.TemporaryDirectory()
        self.addCleanup(temp.cleanup)
        root = Path(temp.name)
        (root / "commits").mkdir()
        for name in ("first", "middle", "third"):
            (root / "commits" / (name + ".patch")).touch()
        ids = ["tests/example.py::Example::test_one", "tests/example.py::Example::test_two"]
        tests = [{"id": name, "number": i, "seconds": 0.1} for i, name in enumerate(ids, 1)]
        (root / "tests.json").write_text(json.dumps({"tests": tests}))
        (root / "pool_readers.json").write_text("[]")
        index = Index({"ids": ids, "masks": [], "layout": {}})

        def candidates(paths, analyze, deadline):
            for path in paths:
                yield path, (index.all, index.all, (), None, 0, (0, 0), 0.0)

        self.enterContext(patch("selector.__file__", str(root / "selector.py")))
        self.enterContext(patch("bounded_batch.bounded_results", candidates))
        self.enterContext(patch("verify.WarmSuite.warm", lambda suite: setattr(suite, "ready", True)))
        self.enterContext(patch("state_watch.persistent_readers", return_value={}))
        self.enterContext(patch("patching.read_patch", return_value=[]))
        self.enterContext(patch.object(ImportSnapshot, "prepare", lambda snap: setattr(snap, "ready", True)))
        select = self.enterContext(patch.object(ImportSnapshot, "select",
                                   side_effect=[(1, 1), KeyError("snapshot reader"), (2, 2)]))
        output = io.StringIO()
        with patch("selector.load_index", return_value=index):
            run_batch(output, root, root, monotonic())
        self.assertEqual(select.call_count, 3)
        self.assertEqual([json.loads(line) for line in output.getvalue().splitlines()], [
            {"commit": "first", "workers": [[1]]},
            {"commit": "middle", "workers": [[1, 2]]},
            {"commit": "third", "workers": [[2]]},
        ])


class KeysTest(unittest.TestCase):
    def test_absent_reader_uses_transitive_test_importers(self):
        idx = Index({'ids':['tests/a.py::A::t', 'tests/b.py::B::t'], 'masks':[],
                     'imports':{'tests/a.py':['sqlglot/copy.py'], 'sqlglot/copy.py':['sqlglot/input.py']}})
        self.assertEqual(idx.import_users('sqlglot/input.py'), 1)
        self.assertEqual(idx.import_users('sqlglot/unused.py'), 0)

    def test_conditional_and_repeated_definitions(self):
        tree = ast.parse("class C:\n if flag:\n  def f(self): return 1\n else:\n  def f(self): return 2")
        self.assertEqual(list(outer_functions(tree)), [(('C', 'f'), 1), (('C', 'f'), 2)])

    def test_class_enum_and_literal_lookup_forms(self):
        self.assertEqual(key_site(('class', ('a', 'Base.Sub'))), '.Sub')
        self.assertEqual(key_site(('enum', ('a','Color','BLUE'))), '.BLUE')
        self.assertEqual(key_site(('str', 'parse')), "'parse'")
        self.assertIsNone(key_site(('opaque', b'x')))
