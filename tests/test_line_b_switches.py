import ast
import difflib
import json
import os
from pathlib import Path
from tempfile import TemporaryDirectory
from textwrap import dedent
import unittest
from unittest.mock import patch

from mutation_summaries import Project, build
from patching import Change, apply_patch
from runner import LiveRunner
from selector import Index, _env_flag
from shared_writes import shared_write_effect


def _diff_change(root, path, old, new):
    target = root / path
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(old)
    diff = "".join(difflib.unified_diff(old.splitlines(True), new.splitlines(True), f"a/{path}", f"b/{path}", n=0))
    change, = apply_patch(diff.encode(), root)
    return change


def _mini_index(
    path,
    ids,
    *,
    line_masks,
    attr_masks=None,
    dialect_masks=None,
    class_masks=None,
    raw_class_masks=None,
    entry_masks=None,
):
    masks = []

    def intern(bits):
        if bits not in masks:
            masks.append(bits)
        return masks.index(bits)

    full = (1 << len(ids)) - 1
    data = {
        "ids": ids,
        "masks": [],
        "opens": {},
        "users": {path: intern(full)},
        "layout": {path: [[], []]},
        "statements": {path: []},
        "lines": {path: {str(k): intern(v) for k, v in line_masks.items()}},
        "entries": {path: {str(k): intern(v) for k, v in entry_masks.items()}} if entry_masks else {},
        "attributes": {k: intern(v) for k, v in (attr_masks or {}).items()},
        "dialect_reads": {k: intern(v) for k, v in (dialect_masks or {}).items()},
        "class_reads": {k: intern(v) for k, v in (class_masks or {}).items()},
        "raw_class_reads": {k: intern(v) for k, v in (raw_class_masks or {}).items()},
        "keys": {},
    }
    data["masks"] = [hex(m) for m in masks]
    return data


class LineBSwitchesTest(unittest.TestCase):
    def test_env_flag_parsing(self):
        with patch.dict(os.environ, {}, clear=True):
            self.assertTrue(_env_flag("ISOLATION_DROP", True))
            self.assertFalse(_env_flag("NARROW_SHARED_ARGS", False))
        for val, expected in [("1", True), ("true", True), ("YES", True), ("0", False), ("false", False), ("off", False), ("", True)]:
            with patch.dict(os.environ, {"TEST_SWITCH": val}):
                self.assertEqual(_env_flag("TEST_SWITCH", True), expected)

    def test_narrow_shared_args_locals_params_and_calls_stay_narrow(self):
        src = dedent("""\
            class Node:
                def __init__(self, x=None):
                    self.x = x

            def helper(val, alias=None, copy=False):
                val.mutated = copy
                return val

            def make_node(n):
                return n

            def caller(scope, items):
                name, _ = make_node((items, scope))
                for child in scope.traverse():
                    for table, _ in child.selected.values():
                        out = helper(make_node(name), alias=table.alias_or_name, copy=False)  # edit
                return out
        """)
        new_src = src.replace("copy=False)  # edit", "copy=True)  # edit")
        path = "sqlglot/example.py"
        with TemporaryDirectory() as tmp:
            root = Path(tmp).resolve()
            (root / "sqlglot").mkdir()
            (root / "sqlglot/__init__.py").write_text("")
            change = _diff_change(root, path, src, new_src)
            proj = Project(build([("sqlglot/__init__.py", ""), (path, src)]))
            data = _mini_index(
                path,
                ["t0", "t1", "t2", "t3"],
                line_masks={16: 0b0010},
                attr_masks={"__code__": 0, "__closure__": 0},
            )
            data["layout"][path] = [[[12, 17]], []]
            idx_off = Index(data, proj, narrow_shared_args=False, identity_equivalence=False, root=root)
            idx_on = Index(data, proj, narrow_shared_args=True, identity_equivalence=False, root=root)
            self.assertEqual(idx_off.select(change)[0], idx_off.all)
            self.assertEqual(idx_on.select(change)[0], 0b0010)

    def test_narrow_shared_args_class_constructor_with_call_results(self):
        src = dedent("""\
            def seq_get(args, i):
                return args[i] if i < len(args) else None

            class Base:
                pass

            class Split(Base):
                def __init__(self, this=None, expr=None):
                    self.this = this

            class Parser:
                FUNCTIONS = {
                    "SPLIT": lambda args: Split(
                        this=seq_get(args, 0),
                        expr=seq_get(args, 1),
                    )
                }
        """)
        new_src = src.replace("seq_get(args, 0)", "seq_get(args, 1)", 1)
        path = "sqlglot/example.py"
        with TemporaryDirectory() as tmp:
            root = Path(tmp).resolve()
            change = _diff_change(root, path, src, new_src)
            proj = Project(build([(path, src)]))
            data = _mini_index(
                path,
                ["t0", "t1", "t2"],
                line_masks={14: 0b001},
                entry_masks={13: 0b001},
            )
            data["layout"][path] = [[[13, 16]], []]
            idx_off = Index(data, proj, narrow_shared_args=False, identity_equivalence=False, root=root)
            idx_on = Index(data, proj, narrow_shared_args=True, identity_equivalence=False, root=root)
            self.assertEqual(idx_off.select(change)[0], idx_off.all)
            self.assertEqual(idx_on.select(change)[0], 0b001)

    def test_narrow_shared_args_module_and_class_bindings_widen_to_readers(self):
        dep_src = dedent("""\
            class Base:
                pass

            class TSQL(Base):
                TIME_TRIE = {"a": 1}
        """)
        src = dedent("""\
            MODULE_DATA = {"x": 1}

            class C:
                data = {"y": 2}
                def m(self):
                    pass

            def helper(obj):
                return obj

            def run():
                from sqlglot.dep import TSQL
                a = helper(MODULE_DATA)
                b = helper(TSQL.TIME_TRIE)
                alias = C.data
                c = helper(alias)
                d = helper(getattr(C, "data"))
                e = helper(*[C.data])
                return a, b, c, d, e
        """)
        path = "sqlglot/example.py"
        dep_path = "sqlglot/dep.py"
        with TemporaryDirectory() as tmp:
            root = Path(tmp).resolve()
            (root / "sqlglot").mkdir()
            (root / "sqlglot/__init__.py").write_text("")
            (root / dep_path).write_text(dep_src)
            (root / path).write_text(src)
            proj = Project(build([("sqlglot/__init__.py", ""), (dep_path, dep_src), (path, src)]))
            data = _mini_index(
                path,
                ["t0", "t1", "t2", "t3", "t4"],
                line_masks={13: 0b00001, 14: 0b00001, 16: 0b00001, 17: 0b00001, 18: 0b00001},
                attr_masks={"MODULE_DATA": 0b00010, "data": 0b00100},
                dialect_masks={"TIME_TRIE": 0b01000},
            )
            data["layout"][path] = [[[11, 19]], []]
            idx = Index(data, proj, narrow_shared_args=True, identity_equivalence=False, root=root)

            # Module-level binding adds MODULE_DATA readers + changed line readers
            ch_mod = _diff_change(root, path, src, src.replace("helper(MODULE_DATA)", "helper(MODULE_DATA) "))
            self.assertEqual(idx.select(ch_mod)[0], 0b00011)

            # Local import class attribute binding adds TIME_TRIE dialect_reads + changed line readers
            ch_tsql = _diff_change(root, path, src, src.replace("helper(TSQL.TIME_TRIE)", "helper(TSQL.TIME_TRIE) "))
            self.assertEqual(idx.select(ch_tsql)[0], 0b01001)

            # Alias / getattr / unpacked C.data add data readers + changed line readers
            for snippet in ("helper(alias)", 'helper(getattr(C, "data"))', "helper(*[C.data])"):
                with self.subTest(snippet=snippet):
                    ch = _diff_change(root, path, src, src.replace(snippet, snippet + " "))
                    self.assertEqual(idx.select(ch)[0], 0b00101)

            # A resolved binding with zero recorded readers falls back to full suite
            ch_zero = _diff_change(root, path, src, src.replace("helper(MODULE_DATA)", "helper(C.m)"))
            self.assertEqual(idx.select(ch_zero)[0], idx.all)

    def test_narrow_shared_args_unresolved_and_direct_writes_remain_full_suite(self):
        cases = [
            "def f():\n    helper(UNKNOWN_GLOBAL)  # edit",
            "from mod import *\ndef f():\n    helper(x)  # edit",
            "class C:\n    data = {}\n    def f(self, k):\n        helper(getattr(C, k))  # edit",
            "def f():\n    eval('1')\n    x = fn()\n    helper(x)  # edit",
            "class C:\n    data = {}\ndef f():\n    C.data.update({})  # edit",
            "REGISTRY = {}\ndef f():\n    REGISTRY['k'] = 1  # edit",
        ]
        for body in cases:
            with self.subTest(body=body):
                lines = {n for n, l in enumerate(body.splitlines(), 1) if "# edit" in l}
                full, _ = shared_write_effect(ast.parse(body), lines, narrow_shared_args=True)
                self.assertTrue(full)

    def test_identity_equivalence_switch_and_live_runner_quit(self):
        enum_src = dedent("""\
            from enum import Enum, auto
            class Kind(Enum):
                A = auto()
                B = auto()
        """)
        mod_src = dedent("""\
            from sqlglot.kinds import Kind
            class Box:
                def __init__(self, k):
                    self.k = Kind(k)
                def is_a(self):
                    return self.k == Kind.A
        """)
        new_mod_src = mod_src.replace("self.k == Kind.A", "self.k is Kind.A")
        with TemporaryDirectory() as tmp:
            root = Path(tmp).resolve()
            (root / "sqlglot").mkdir()
            (root / "sqlglot/__init__.py").write_text("")
            (root / "sqlglot/kinds.py").write_text(enum_src)
            change = _diff_change(root, "sqlglot/box.py", mod_src, new_mod_src)
            data = _mini_index("sqlglot/box.py", ["t0", "t1", "t2"], line_masks={6: 0b010})
            data["layout"]["sqlglot/box.py"] = [[[5, 6]], []]
            idx_equiv_on = Index(data, narrow_shared_args=False, identity_equivalence=True, root=root)
            idx_equiv_off = Index(data, narrow_shared_args=False, identity_equivalence=False, root=root)
            self.assertEqual(idx_equiv_on.select(change)[0], 0)
            self.assertEqual(idx_equiv_off.select(change)[0], 0b010)

            runner = LiveRunner(root)
            self.assertTrue(runner.verify_unittest([], []))
            runner._ensure_proc()
            self.assertIsNotNone(runner._proc)
            runner.close()
            self.assertIsNone(runner._proc)
