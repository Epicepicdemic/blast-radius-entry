import ast
import unittest
from types import SimpleNamespace
from unittest.mock import patch

import heavy_reach as reach


def module(code):
    return ast.parse(code)


class TestReach(unittest.TestCase):
    def test_price_matches_the_emitted_plan(self):
        from itertools import combinations
        from packing import pack, packed_cost

        durations = dict(enumerate((30000, 12000, 8000, 8000, 12, 1, 0, 0, 0)))
        ranked = list(durations)
        positive = [n for n in ranked if durations[n]]
        for length in range(len(ranked) + 1):
            for items in combinations(ranked, length):
                workers = pack(set(items), ranked, durations, fill=False)
                bill = 2000 * len(workers) + max((sum(durations[t] for t in w) for w in workers), default=0)
                self.assertEqual(packed_cost(set(items), positive, durations), bill)

    def test_pop_ignores_value_but_observes_keys(self):
        change = SimpleNamespace(path="sqlglot/generators/d.py")
        rules = {"tables": [], "value_only": [["sqlglot.generators.d", "G", "TRANSFORMS"]]}

        def tree(k, v):
            return module(f"class G:\n    TRANSFORMS = {{exp.{k}: {v}}}\n")

        self.assertTrue(reach.table_change(change, tree("X", "f"), tree("X", "lambda a,b: a"), rules))
        self.assertFalse(reach.table_change(change, tree("X", "f"), tree("Y", "f"), rules))
        self.assertFalse(reach.table_change(change, tree("X", "f"), tree("X", "factory()"), rules))
        self.assertFalse(
            reach.table_change(change, tree("X", "f"), tree("X", "lambda x=touch(): x"), rules)
        )

    def test_unread_table_requires_standalone_edit(self):
        change = SimpleNamespace(path="sqlglot/parsers/d.py")
        rules = {"tables": [["sqlglot.parsers.d", "D", "FUNCTIONS"]], "value_only": []}
        a = "class D:\n    FUNCTIONS = {'X': f}\n"
        b = "class D:\n    FUNCTIONS = {**dict.fromkeys(('X','Y'), lambda x: x)}\n"
        self.assertTrue(reach.table_change(change, module(a), module(b), rules))
        for tail in ("    alias = FUNCTIONS\n", "    alias = FUNCTIONS.copy()\n"):
            self.assertFalse(reach.table_change(change, module(a + tail), module(b + tail), rules))
        self.assertFalse(reach.table_change(change, module(a), module(b + "effect()\n"), rules))

    def test_parser_method_requires_a_recorded_unread_declaration(self):
        path = "sqlglot/parsers/d.py"
        change = SimpleNamespace(path=path)
        future = "from __future__ import annotations\n"
        prefix = "class D:\n    sentinel = 1\n"
        key = ["sqlglot.parsers.d", "D", "parse_x"]

        def matched(method, reads, *, header=future, suffix=""):
            a = module(header + prefix + method + suffix)
            b = module(header + prefix + suffix)
            return reach.unused_parser_method(change, a, b, {"tables": reads})

        plain = "    def parse_x(self): return 1\n"
        self.assertTrue(matched(plain, [key]))
        self.assertFalse(matched(plain, []))
        self.assertFalse(matched(plain, [key], header=""))
        self.assertFalse(matched(plain, [key], suffix="    alias=parse_x\n"))
        self.assertFalse(matched("    @register\n" + plain, [key]))
        self.assertFalse(matched("    def parse_x(self, x=effect()): pass\n", [key]))

    def test_import_snapshot_required_for_unobserved_module_initializer(self):
        c = SimpleNamespace(path="sqlglot/isolated.py", before=b"x=1", after=b"x=2")
        with patch.object(reach, "footprints", return_value={"tpc": {"paths": []}}):
            self.assertFalse(reach.unchanged("tpc", [c], None))
            self.assertTrue(reach.unchanged("tpc", [c], None, screened_import=True))
            with patch.dict("sys.modules", {"sqlglot.isolated": object()}):
                self.assertFalse(reach.unchanged("tpc", [c], None, screened_import=True))

    def test_module_deletion_checks_internal_and_external_reads(self):
        change = SimpleNamespace(path="sqlglot/optimizer/test.py")
        before = module("CONSTANT = (exp.A,exp.B)\nX = 1")
        for reads, ok in [([], True), (["CONSTANT"], False), (["*"], False)]:
            rules = {"globals": {change.path: reads}}
            self.assertEqual(reach.unread_constant(change, before, module("X=1"), rules), ok)
        self.assertFalse(
            reach.unread_constant(change, module("CONSTANT=(side_effect(),)"), module(""), rules)
        )

    def test_predicate_only_removes_proven_absent_arguments(self):
        path = "sqlglot/optimizer/test.py"
        change = SimpleNamespace(path=path)
        a = module(
            "def probe(q) -> bool:\n if q.args.get('skip'): return True\n x=q.args.get('x')\n return any(q.cols) or (x is not None and touch(x))"
        )
        b = module("def probe(q) -> bool:\n return any(q.cols)")
        for keys, ok in [([], True), (["skip"], False), (["x"], False)]:
            self.assertEqual(
                reach.unchanged_predicate(change, a, b, {"entry_keys": {path + ":probe": keys}}), ok
            )
        self.assertFalse(
            reach.unchanged_predicate(
                change,
                a,
                module("def probe(q) -> bool:\n return all(q.cols)"),
                {"entry_keys": {path + ":probe": []}},
            )
        )

    def test_missing_assignment_in_a_closure(self):
        a = module("def f(q) -> bool:\n x=q.args.get('x')\n return any(x for a in q.cols)").body[0]
        b = module("def f(q) -> bool:\n return any(x for a in q.cols)").body[0]
        from selector import equal_trees

        self.assertFalse(equal_trees(reach.predicate_body(a, []), reach.predicate_body(b, [])))

    def test_cold_arm_keeps_the_original_test_and_observed_lines(self):
        before = module("def f(x):\n if x:\n  return read()\n return 0")
        after = module("def f(x):\n if x:\n  return write()\n return 0")
        self.assertTrue(reach.edits_in_cold_arms(before, after, [2, 4]))
        self.assertFalse(reach.edits_in_cold_arms(before, after, [2, 3, 4]))
        different_test = module("def f(x):\n if not x:\n  return write()\n return 0")
        self.assertFalse(reach.edits_in_cold_arms(before, different_test, [2, 4]))
        self.assertFalse(reach.edits_in_cold_arms(module("if x: pass"), module("if x: effect()"), []))

    def test_absent_file_rejects_process_effect_and_import_failures(self):
        c = SimpleNamespace(
            path="sqlglot/dialects/isolated.py", before=b"x=1", after=b"import os\nos.environ['X']='1'"
        )
        with patch.object(reach, "footprints", return_value={"tpc": {"paths": []}}):
            self.assertFalse(reach.unchanged("tpc", [c], None))
            with patch("importlib.import_module", side_effect=ImportError):
                with self.assertRaises(ImportError):
                    reach.unchanged("tpc", [c], [(c.path, "f", 1, 1)])


if __name__ == "__main__":
    unittest.main()
