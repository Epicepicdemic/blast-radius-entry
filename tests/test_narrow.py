import ast
import unittest
from textwrap import dedent

import cone
import state_watch


def pair(old, new):
    a = ast.parse(dedent(old)).body[-1]
    b = ast.parse(dedent(new)).body[-1]
    return a, b


class HeaderEditTest(unittest.TestCase):
    def allowed(self, old, new, deferred=True):
        a, b = pair(old, new)
        return cone.header_change_allowed(a, b, deferred)

    def test_header_mask_restores_the_shared_parse_on_error(self):
        from patching import Change, parsed_source
        change = Change("sqlglot/demo.py", b"def f(a): return a\n", b"def f(a=1): return 2\n",
                        removed={1}, added={1})
        tree = parsed_source(change.after)
        expected = ast.dump(tree, include_attributes=True)
        def interrupt(left, right):
            self.assertIs(right, tree)
            raise RuntimeError("interrupted comparison")
        with self.assertRaisesRegex(RuntimeError, "interrupted comparison"):
            cone.body_changes(change, interrupt)
        self.assertEqual(ast.dump(tree, include_attributes=True), expected)

    def test_compiled_source_distinguishes_text_and_filename(self):
        from patching import compiled_source
        raw = b"x = 1"
        self.assertEqual(compiled_source(raw, "a.py").co_filename, "a.py")
        self.assertEqual(compiled_source(raw, "b.py").co_filename, "b.py")
        with self.assertRaises(SyntaxError):
            compiled_source(b"break", "b.py")

    def test_signature_changes(self):
        self.assertTrue(self.allowed("def f(a): pass", "def f(a, b=None): pass"))
        self.assertTrue(self.allowed("def f(a, b=1): pass", "def f(a, *, b=1): pass"))
        self.assertTrue(self.allowed("def f(a): pass", "def f(a, b=(1, 'x'), c=-1): pass"))
        # A default runs at definition time and may call or share anything.
        self.assertFalse(self.allowed("def f(a): pass", "def f(a, b=make()): pass"))
        self.assertFalse(self.allowed("def f(a): pass", "def f(a, b=CONSTANT): pass"))
        # An unchanged non-literal default is still evaluated the same way.
        self.assertTrue(self.allowed("def f(a, b=CONSTANT): pass", "def f(b=CONSTANT, *a): pass"))

    def test_decorators(self):
        self.assertTrue(self.allowed("@classmethod\ndef f(cls): pass", "@staticmethod\ndef f(): pass"))
        self.assertTrue(self.allowed("def f(a): pass", "@lru_cache(maxsize=None)\ndef f(a): pass"))
        # A property turns attribute reads into calls.
        self.assertFalse(self.allowed("def f(self): pass", "@property\ndef f(self): pass"))
        self.assertFalse(self.allowed("def f(a): pass", "@register\ndef f(a): pass"))
        self.assertFalse(self.allowed("def f(a): pass", "@lru_cache(maxsize=size())\ndef f(a): pass"))

    def test_annotations_without_future_import(self):
        self.assertTrue(self.allowed("def f(a: int): pass", "def f(a: str) -> Missing: pass"))
        self.assertFalse(self.allowed("def f(a): pass", "def f(a) -> Missing: pass", deferred=False))
        self.assertFalse(self.allowed("def f(a: int): pass", "def f(a: Missing): pass", deferred=False))
        # Unchanged annotations plus an unannotated new parameter evaluate nothing new.
        self.assertTrue(self.allowed("def f(a: int): pass", "def f(a: int, b=1): pass", deferred=False))

    def test_renames_and_kinds(self):
        self.assertFalse(self.allowed("def f(a): pass", "def g(a): pass"))
        self.assertFalse(self.allowed("def f(a): pass", "async def f(a): pass"))

    def test_deferred_annotations(self):
        self.assertTrue(cone.deferred_annotations(ast.parse("from __future__ import annotations\nx = 1")))
        self.assertFalse(cone.deferred_annotations(ast.parse("import annotations")))

    def test_body_changes_admits_headers_only_when_enabled(self):
        class Change:
            path = "sqlglot/m.py"
            before = b"from __future__ import annotations\ndef f(a):\n    return a\n"
            after = b"from __future__ import annotations\ndef f(a, b=None):\n    return a\n"
            removed = {2}
            added = {2}
            insertions = set()
            deletions = set()
        equal = lambda a, b: ast.dump(a) == ast.dump(b) if not isinstance(a, list) else \
            [ast.dump(x) for x in a] == [ast.dump(x) for x in b]
        saved = cone.HEADER_EDITS
        try:
            cone.HEADER_EDITS = True
            edits = cone.body_changes(Change, equal)
            self.assertEqual([e[0] for e in edits], ["f"])
            cone.HEADER_EDITS = False
            self.assertIsNone(cone.body_changes(Change, equal))
        finally:
            cone.HEADER_EDITS = saved

    def test_excluded_paths(self):
        self.assertIn("sqlglot/executor/env.py", cone.HEADER_EXCLUDED_PATHS)


class Node:
    __module__ = "sqlglot.expressions.core"
    __slots__ = ("args", "parent", "_type")

    def __init__(self, **args):
        self.args = args
        self.parent = None
        self._type = None


Node.__module__ = "sqlglot.expressions.core"


class DeepStateTest(unittest.TestCase):
    def test_in_place_changes_only_visible_when_deep(self):
        node = Node(this="a")
        cache = {"k": node}
        try:
            state_watch.deep = False
            before = state_watch.fingerprint(cache, set())
            node.args["this"] = "b"
            self.assertEqual(before, state_watch.fingerprint(cache, set()))
            state_watch.deep = True
            before = state_watch.fingerprint(cache, set())
            node.args["this"] = "c"
            self.assertNotEqual(before, state_watch.fingerprint(cache, set()))
            before = state_watch.fingerprint(cache, set())
            node._type = object()
            self.assertNotEqual(before, state_watch.fingerprint(cache, set()))
        finally:
            state_watch.deep = False

    def test_cycles_terminate(self):
        a, b = Node(), Node()
        a.args["x"] = b
        b.args["y"] = a
        b.parent = a
        try:
            state_watch.deep = True
            state_watch.fingerprint([a], set())
        finally:
            state_watch.deep = False

    def test_call_writes_need_deep_state(self):
        if not state_watch.DEEP_STATE:
            self.assertFalse(cone.CALL_WRITES)


if __name__ == "__main__":
    unittest.main()
