import ast
import difflib
from pathlib import Path
from tempfile import TemporaryDirectory
from textwrap import dedent
import unittest

from patching import apply_patch
from selector import Index
from shared_writes import has_shared_write


def guarded(source):
    source = dedent(source)
    lines = {n for n, line in enumerate(source.splitlines(), 1) if "# edit" in line}
    return has_shared_write(ast.parse(source, type_comments=True), lines)


class SharedWritesTest(unittest.TestCase):
    def test_receiver_ownership(self):
        for head, guarded_receiver in [
            ("class C:\n def f(this):", False),
            ("class C:\n @classmethod\n def f(this):", True),
            ("class C:\n @staticmethod\n def f(this):", True),
            ("class C:\n def __new__(this):", True),
            ("class Meta(type):\n def f(this):", True),
            ("class Meta(type): pass\nclass Child(Meta):\n def f(this):", True),
        ]:
            for write in ['this.field = 1', 'setattr(this, "field", 1)']:
                with self.subTest(head=head, write=write):
                    self.assertEqual(guarded(head + "\n  " + write + "  # edit"), guarded_receiver)
        for write in ['this.field.add(k)', 'this.field[k] = v', 'this.field += v',
                      'type(this).x = v', 'this.__class__.x = v']:
            with self.subTest(write=write):
                self.assertTrue(guarded('class C:\n def f(this):\n  ' + write + '  # edit'))

    def test_shared_and_local_bindings(self):
        for source in [
            'registry = {}  # edit',
            'def f():\n global registry\n registry = {}  # edit',
            'def f():\n registry[k] = v  # edit',
            'def f():\n from mod import SomeClass as c\n c.x = v  # edit',
            'def f():\n local = Registry.items\n local[k] = v  # edit',
            'def f():\n def nested():\n  registry = {}\n registry.clear()  # edit',
            'class C:\n value = Registry.items.pop()  # edit',
            'def f():\n (local, Registry.items[k]) = values  # edit',
            'def f():\n Registry.items[k] = (\n  v  # edit\n )',
        ]:
            with self.subTest(source=source):
                self.assertTrue(guarded(source))
        for source in [
            'class C:\n X = {"k": 1}  # edit',
            'def f():\n buf = {}\n buf[k] = v  # edit',
            'def f():\n buf = set()\n buf.add(1)  # edit',
            'def f():\n buf = [x for x in xs]\n buf.reverse()  # edit',
            'def f():\n Registry.items.pop()\n return 1  # edit',
        ]:
            with self.subTest(source=source):
                self.assertFalse(guarded(source))

    def test_nested_calls_and_mutators(self):
        methods = ("update add append extend insert pop popitem setdefault clear remove "
                   "discard sort reverse __setitem__ __delitem__").split()
        for method in methods:
            with self.subTest(method=method):
                self.assertTrue(guarded(f'def f():\n return g(Registry.items.{method}(\n  k  # edit\n ))'))

    def test_container_protocols(self):
        for method in ("__ior__", "__iadd__", "__init__", "__setitem__", "__delattr__",
                       "difference_update", "symmetric_difference_update", "intersection_update",
                       "move_to_end", "appendleft", "extendleft", "popleft", "rotate",
                       "subtract", "__missing__", "_keep_positive"):
            with self.subTest(method=method):
                self.assertTrue(guarded(f"def f():\n Registry.data.{method}()  # edit"))
                self.assertFalse(guarded(f"def f():\n buf = []\n buf.{method}()  # edit"))
        self.assertFalse(guarded("def f():\n Registry.data.get(1)  # edit"))

    def test_operator_uses_first_argument(self):
        for name in ("setitem", "delitem", "iadd", "__iadd__", "imatmul", "iconcat"):
            for head, func in (("import operator as op", f"op.{name}"),
                               (f"from operator import {name} as change", "change")):
                with self.subTest(name=name, head=head):
                    # An inline literal is exempt from escape analysis but is
                    # not a private local receiver for an explicit operator.
                    self.assertTrue(guarded(f"{head}\ndef f():\n {func}([], 1)  # edit"))
                    self.assertTrue(guarded(f"{head}\ndef f():\n {func}(C.data, 1)  # edit"))
                    self.assertFalse(guarded(f"{head}\ndef f():\n buf = []\n {func}(buf, 1)  # edit"))

    def test_unknown_callees_and_arguments(self):
        for arg in ("MODULE_DATA", "self.field", "alias", "other", "value=C.data",
                    "*[C.data]", "**{'value': C.data}", "getattr(C, 'data')"):
            with self.subTest(arg=arg):
                self.assertTrue(guarded("MODULE_DATA = {}\nclass C:\n def f(self, other):\n"
                                        f"  alias = C.data\n  helper({arg})  # edit"))
        for arg in ("self", "buf", "dict()", "[]", "(1, 'value')"):
            with self.subTest(arg=arg):
                self.assertFalse(guarded(f"class C:\n def f(self):\n  buf = {{}}\n  helper({arg})  # edit"))
        self.assertTrue(guarded("def f():\n buf = [C.data]\n helper(*buf)  # edit"))
        self.assertTrue(guarded("def f():\n buf = {'x': C.data}\n helper(**buf)  # edit"))
        self.assertTrue(guarded("def f():\n len(h(C.data))  # edit"))
        self.assertTrue(guarded("def f(len):\n len(C.data)  # edit"))
        self.assertTrue(guarded("def f(obj):\n obj.len(C.data)  # edit"))
        self.assertFalse(guarded("def f():\n len(C.data)  # edit"))
        self.assertFalse(guarded("import builtins as b\ndef f():\n b.list(C.data)  # edit"))
        self.assertFalse(guarded("from builtins import iter as it\ndef f():\n it(C.data)  # edit"))

    def test_both_diff_coordinates_before_other_selection(self):
        path = "sqlglot/example.py"
        prefix = "def f():\n" + "    pass\n" * 8
        before = prefix + "    return Registry.items.get(k)\n"
        after = "# header\n\n" + before.replace(".get(", ".pop(")
        index = Index({"ids": ["a", "b"], "masks": ["1"], "opens": {}, "layout": {path: []},
                       "users": {path: 0}})
        # No line maps or certificates exist in this index. Reaching either fails.
        for old, new in [(before, after), (after, before), (after, after.replace("(k)", "(k) "))]:
            with TemporaryDirectory() as work:
                root = Path(work).resolve()
                (root / path).parent.mkdir()
                (root / path).write_text(old)
                diff = difflib.unified_diff(old.splitlines(True), new.splitlines(True),
                                            "a/" + path, "b/" + path, n=0)
                change, = apply_patch("".join(diff).encode(), root)
                self.assertEqual(index.select(change)[0], index.all)
