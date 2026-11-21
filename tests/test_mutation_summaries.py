import ast
import difflib
import tempfile
import unittest
from pathlib import Path
from textwrap import dedent

from mutation_summaries import Project, build, module_name, parameters
from patching import apply_patch
from shared_writes import has_shared_write

PATH = "sqlglot/example.py"


def code(text):
    return dedent(text).strip() + "\n"


class Fixture:
    def __init__(self, source, **modules):
        self.files = {PATH: code(source), **{p: code(s) for p, s in modules.items()}}
        self.project = Project(build(self.files.items()))

    def mutated(self, name):
        key = self.project.resolve("m/sqlglot.example:" + name.replace(".", ":"))
        sig, _, _ = self.project.record(key)
        return {n for i, n in enumerate(parameters(sig)) if self.project.data["masks"][key] & 1 << i}

    def guard(self, expression):
        text = self.files[PATH]
        line, = [i for i, row in enumerate(text.splitlines(), 1) if expression in row]
        return has_shared_write(ast.parse(text), {line}, self.project, module_name(PATH))

    def patch(self, replacements):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp).resolve()
            diffs = []
            for path, new in replacements.items():
                old = self.files[path]
                (root / path).parent.mkdir(parents=True, exist_ok=True)
                (root / path).write_text(old)
                diffs.extend(difflib.unified_diff(old.splitlines(True), code(new).splitlines(True),
                                                  "a/" + path, "b/" + path))
            changes = apply_patch("".join(diffs).encode(), root)
        return self.project.patched(changes), changes


class SummaryTest(unittest.TestCase):
    def test_getter_direct_and_transitive_writes(self):
        f = Fixture("""
            def read(xs, i):
                return xs[i]
            def leaf(other, xs):
                alias = xs
                alias[0].clear()
            def middle(a, b):
                leaf(xs=b, other=a)
            def root(p, q):
                middle(q, p)
            def use():
                read(REGISTRY, 0)
                root([], REGISTRY)
                root(REGISTRY, [])
        """)
        self.assertEqual(f.mutated("read"), set())
        self.assertEqual(f.mutated("leaf"), {"xs"})
        self.assertEqual(f.mutated("middle"), {"b"})
        self.assertEqual(f.mutated("root"), {"p"})
        self.assertFalse(f.guard("read(REGISTRY"))
        self.assertFalse(f.guard("root([], REGISTRY"))
        self.assertTrue(f.guard("root(REGISTRY"))

    def test_recursive_pair_propagates_unknown(self):
        f = Fixture("""
            def first(a, b):
                second(b, a)
            def second(x, y):
                first(y, x)
                external(y)
            def pure(x):
                again(x)
            def again(x):
                pure(x)
        """)
        self.assertEqual(f.mutated("first"), {"a"})
        self.assertEqual(f.mutated("second"), {"y"})
        self.assertEqual(f.mutated("pure"), set())
        self.assertEqual(f.mutated("again"), set())

    def test_method_and_inplace_writes(self):
        f = Fixture("""
            class Bucket:
                def update_value(self, index):
                    self[index] = 0
                def touch(self):
                    self.size = 1
                def remove(self):
                    del self.items[:]
            def change(xs):
                alias = xs
                alias += [1]
            def use():
                Bucket.touch(REGISTRY)
        """)
        for name in ("Bucket.update_value", "Bucket.touch", "Bucket.remove"):
            self.assertEqual(f.mutated(name), {"self"})
        self.assertEqual(f.mutated("change"), {"xs"})
        self.assertTrue(f.guard("Bucket.touch(REGISTRY)"))

    def test_escape_channels_and_callbacks(self):
        for stmt in ("saved = x; return saved", "return {'key': x}", "cache = [x]",
                     "owner.field = x", "global saved; saved = x", "owner[0] = x",
                     "def use_later(): return x", "yield x", "third_party(x)",
                     "raise x", "return x.__dict__"):
            with self.subTest(stmt=stmt):
                f = Fixture("def helper(x):\n    " + stmt)
                self.assertEqual(f.mutated("helper"), {"x"})
        f = Fixture("""
            def helper(x, callback):
                alias = callback
                alias(x)
            def forward(cb, value):
                helper(callback=cb, x=value)
        """)
        self.assertEqual(f.mutated("helper"), {"callback", "x"})
        self.assertEqual(f.mutated("forward"), {"cb", "value"})

    def test_import_reexport_and_assignment_alias(self):
        f = Fixture("""
            from .api import read as fetch
            import sqlglot.impl as implementation
            def use():
                local = fetch
                local(STATE)
                implementation.write(STATE)
        """, **{"sqlglot/api.py": "from .impl import *", "sqlglot/impl.py": """
            def read(xs):
                return xs[0]
            def write(xs):
                xs.clear()
        """})
        self.assertFalse(f.guard("local(STATE)"))
        self.assertTrue(f.guard("implementation.write(STATE)"))

    def test_uncertain_binding_keeps_unknown_answer(self):
        for definitions, expr in [
            ("def read(x): pass\nread = provider()", "read(STATE)"),
            ("@decorate\ndef read(x): pass", "read(STATE)"),
            ("from third_party import read", "read(STATE)"),
            ("if enabled:\n    from sqlglot.impl import read", "read(STATE)"),
            ("class Child(External):\n    def read(x): pass", "Child.read(STATE)"),
            ("def read(x): pass", "read(unknown=STATE)"),
        ]:
            with self.subTest(definitions=definitions):
                f = Fixture(definitions + "\ndef use():\n    " + expr,
                            **{"sqlglot/impl.py": "def read(x): pass"})
                self.assertTrue(f.guard(expr))
        f = Fixture("""
            def read(x): pass
            def run(read, receiver):
                read(STATE)
                receiver.read(OTHER)
        """)
        self.assertTrue(f.guard("read(STATE)"))
        self.assertTrue(f.guard("receiver.read(OTHER)"))

    def test_positional_keyword_only_and_variadics(self):
        f = Fixture("""
            def helper(plain, /, middle, *tail, option=1, **extra):
                middle.clear()
                tail[0].clear()
                option.clear()
                extra["key"].clear()
            def use():
                helper(STATE, [], option=[])
                helper(0, STATE)
                helper(0, [], STATE)
                helper(0, [], option=STATE)
                helper(0, [], plain=STATE)
                helper(0, *STATE)
                helper(0, [], **STATE)
        """)
        self.assertEqual(f.mutated("helper"), {"middle", "tail", "option", "extra"})
        self.assertFalse(f.guard("helper(STATE, []"))
        for row in ("helper(0, STATE)", "helper(0, [], STATE)", "option=STATE",
                    "plain=STATE", "helper(0, *STATE)", "[], **STATE"):
            with self.subTest(row=row):
                self.assertTrue(f.guard(row))

    def test_patch_rebinds_transitive_callee_across_files(self):
        f = Fixture("""
            from .wrapper import wrapper
            def run():
                wrapper(OLD)
        """, **{"sqlglot/wrapper.py": """
            from .leaf import leaf as target
            def wrapper(x):
                target(x)
        """, "sqlglot/leaf.py": "def leaf(x): pass"})
        self.assertFalse(f.guard("wrapper(OLD)"))
        patched, changes = f.patch({
            PATH: f.files[PATH].replace("OLD", "NEW"),
            "sqlglot/leaf.py": "def leaf(x): x.clear()",
        })
        caller, leaf = changes
        after = patched.source(module_name(PATH)).tree
        self.assertTrue(has_shared_write(after, caller.added, patched, module_name(PATH)))
        leaf_key = patched.resolve("m/sqlglot.leaf:leaf")
        self.assertEqual(patched.solved[leaf_key], 1)
        self.assertEqual(f.project.data["masks"][f.project.resolve("m/sqlglot.leaf:leaf")], 0)
        self.assertFalse(f.guard("wrapper(OLD)"))

    def test_deleted_write_and_new_definition_have_distinct_summaries(self):
        f = Fixture("""
            def helper(x):
                x.clear()
                return 0
            def run():
                helper(OLD)
        """)
        patched, changes = f.patch({PATH: """
            def helper(x):
                return 0
            def new(x):
                return x
            def run():
                helper(NEW)
                new(STATE)
        """})
        self.assertTrue(f.guard("helper(OLD)"))
        self.assertEqual(patched.solved[patched.resolve("m/sqlglot.example:helper")], 0)
        self.assertEqual(patched.solved[patched.resolve("m/sqlglot.example:new")], 1)
        after = patched.source(module_name(PATH)).tree
        self.assertFalse(has_shared_write(after, {6}, patched, module_name(PATH)))
        self.assertTrue(has_shared_write(after, {7}, patched, module_name(PATH)))

    def test_module_attribute_rebinding_withdraws_alias_proof(self):
        f = Fixture("""
            from .impl import read as get
            def use():
                get(STATE)
        """, **{"sqlglot/impl.py": "def read(xs): return xs[0]",
                 "sqlglot/patcher.py": "from . import impl\nimpl.read = provider"})
        self.assertTrue(f.guard("get(STATE)"))

    def test_lambda_and_return_alias(self):
        f = Fixture("""
            identity = lambda x: x
            def outer(data):
                copy = data
                identity(copy)
        """)
        self.assertEqual(f.mutated("identity"), {"x"})
        self.assertEqual(f.mutated("outer"), {"data"})

    def test_getter_result_in_opaque_outer_call_still_triggers(self):
        f = Fixture("""
            def get(xs):
                return xs[0]
            def run():
                external(get(STATE))
        """)
        self.assertTrue(f.guard("external(get(STATE))"))
