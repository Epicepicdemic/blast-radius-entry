import ast
import fnmatch
import unittest
from pathlib import Path
from textwrap import dedent

from census import Census, _qualnames
from change_shapes import _innermost_block
from mutation_summaries import Source
from shared_writes import _class_qualnames, _hierarchy, shared_write_effect

REPO = Path(__file__).resolve().parent.parent

DOC = {
    "modules": {
        "m": {
            "exp": ["module", "sqlglot.expressions"],
            "re": ["module", "re"],
            "REGISTRY": ["mut"],
            "NAMES": ["elems"],
            "LIMIT": ["imm"],
            "helper": ["func"],
        },
        "sqlglot.expressions": {
            "DType": ["type", "sqlglot.expressions:DType", False],
            "DataType": ["type", "sqlglot.expressions:DataType", True],
            "Column": ["type", "sqlglot.expressions:Column", True],
            "Written": ["type", "sqlglot.expressions:Written", True],
        },
    },
    "classes": {
        "sqlglot.expressions:DType": {"mro": ["sqlglot.expressions:DType"], "attrs": {"INT": ["imm"]}},
        "sqlglot.expressions:DataType": {
            "mro": ["sqlglot.expressions:DataType"],
            "attrs": {"NUMERIC": ["elems"], "CACHE": ["mut"], "build": ["func"]},
        },
        "sqlglot.expressions:Column": {"mro": ["sqlglot.expressions:Column"], "attrs": {}},
        "sqlglot.expressions:Written": {"mro": ["sqlglot.expressions:Written"], "attrs": {}},
    },
    "attr_kinds": {"NUMERIC": ["elems"], "CACHE": ["mut"], "build": ["func"], "INT": ["imm"],
                   "is_type": ["func"], "TABLE": ["mut"]},
    "instance_attrs": ["parent"],
    "params": {
        "sqlglot/m.py:f": {"calls": 3, "shared": ["shared_p"], "opaque": ["obj"]},
        "sqlglot/m.py:C.g": {"calls": 2, "shared": [], "opaque": ["self"]},
        "sqlglot/m.py:never": {"calls": 0, "shared": [], "opaque": []},
    },
    "written": ["sqlglot.expressions:Written"],
}

HEAD = "def f(node, shared_p, obj, items, *rest):\n"


def resolve(body, head=HEAD):
    """Census answer for the single argument of the call marked '# here'."""
    source = dedent(head) + "".join("    " + line + "\n" for line in dedent(body).strip().splitlines())
    tree = ast.parse(source)
    fn = next(n for n in ast.walk(tree) if isinstance(n, ast.FunctionDef))
    line = next(i for i, text in enumerate(source.splitlines(), 1) if "# here" in text)
    call = next(n for n in ast.walk(tree) if isinstance(n, ast.Call) and n.lineno == line)
    r = Census(DOC).resolver("m", "sqlglot/m.py", tree)
    arg = call.args[0] if call.args else call.keywords[0].value
    return r(arg, fn, None, call, tree)


class CensusResolverTest(unittest.TestCase):
    def test_static_values(self):
        cases = {
            "node.is_type(exp.DType.INT)  # here": True,
            "node.is_type(*exp.DataType.NUMERIC)  # here": True,
            "node.is_type(exp.DataType.NUMERIC)  # here": False,   # the container itself is shared
            "node.is_type(exp.DataType.CACHE)  # here": False,
            "node.find(exp.Column)  # here": True,
            "node.find(exp.Written)  # here": False,               # a class written during the suite
            "node.find(REGISTRY)  # here": False,
            "node.find(LIMIT)  # here": True,
            "node.find(*NAMES)  # here": True,
            "node.find(lambda n: n)  # here": True,
            "node.find(f'x{LIMIT}')  # here": True,
        }
        for body, expected in cases.items():
            with self.subTest(body=body):
                self.assertIs(resolve(body), expected)

    def test_parameters_follow_the_census(self):
        self.assertTrue(resolve("helper(node)  # here"))
        self.assertFalse(resolve("helper(shared_p)  # here"))
        self.assertFalse(resolve("helper(obj)  # here"))      # opaque object
        self.assertTrue(resolve("helper(node.this)  # here"))
        self.assertFalse(resolve("helper(node.parent)  # here"))
        self.assertFalse(resolve("helper(shared_p.this)  # here"))
        self.assertFalse(resolve("helper(node.this.this)  # here"))
        # A function the pinned suite never called has no evidence.
        self.assertFalse(resolve("helper(node)  # here", "def never(node):\n"))

    def test_rebinding_a_parameter_needs_every_binding(self):
        self.assertFalse(resolve("node = REGISTRY\nhelper(node)  # here"))
        # The census saw the entry value only; a rebinding can walk deeper.
        self.assertFalse(resolve("node = node.this\nhelper(node)  # here"))

    def test_locals(self):
        self.assertTrue(resolve("for k in ('a', 'b'):\n    helper(k)  # here"))
        self.assertTrue(resolve("for k in exp.DataType.NUMERIC:\n    helper(k)  # here"))
        self.assertFalse(resolve("for k in REGISTRY:\n    helper(k)  # here"))
        self.assertTrue(resolve("x = 'a' if LIMIT else 'b'\nhelper(x)  # here"))
        self.assertFalse(resolve("x = node.find()\nhelper(x)  # here"))
        self.assertFalse(resolve("with open('f') as x:\n    helper(x)  # here"))
        self.assertTrue(resolve("x = node.copy()\nhelper(x)  # here"))
        self.assertTrue(resolve("x = exp.Column(this=node.this)\nhelper(x)  # here"))
        self.assertFalse(resolve("x = exp.Column(this=shared_p)\nhelper(x)  # here"))

    def test_comprehensions(self):
        self.assertTrue(resolve("any(node.args.get(k) for k in REGISTRY)  # here"))  # any() is a sink
        self.assertTrue(resolve("[helper(k) for k in exp.DataType.NUMERIC]  # here"))
        self.assertTrue(resolve("[helper(k) for k in ('a', 'b')]  # here"))
        self.assertFalse(resolve("[helper(k) for k in REGISTRY]  # here"))
        self.assertFalse(resolve("[helper(k) for k, v in items]  # here"))
        self.assertTrue(resolve("helper([k for k in NAMES])  # here"))
        self.assertFalse(resolve("helper([k for k in REGISTRY])  # here"))
        self.assertTrue(resolve("m = {k: 1 for k in NAMES}\nfor key in m:\n    helper(key)  # here"))
        self.assertFalse(resolve("m = {k: 1 for k in REGISTRY}\nfor key in m:\n    helper(key)  # here"))

    def test_shadowing_disables_module_resolution(self):
        self.assertFalse(resolve("exp = node\nnode.is_type(exp.DType.INT)  # here"))
        self.assertFalse(resolve("node.is_type(exp.DType.INT)  # here", "def f(node, exp):\n"))

    def test_sink_methods_never_mutate_arguments(self):
        self.assertTrue(resolve("items.intersection(shared_p)  # here"))
        self.assertTrue(resolve("sorted(shared_p)  # here"))
        # A method name SQLGlot defines is not a sink.
        self.assertFalse(resolve("items.is_type(shared_p)  # here"))

    def test_shared_write_guard_uses_census(self):
        source = "def f(node, shared_p, obj, items, *rest):\n    node.is_type(exp.DType.INT, mystery())\n"
        tree = ast.parse(source)
        resolver = Census(DOC).resolver("m", "sqlglot/m.py", tree)
        full, _ = shared_write_effect(tree, {2}, None, "m", narrow_shared_args=True, census=resolver)
        self.assertTrue(full)   # mystery() is unproven
        for binding in ("import mystery", "from external import mystery", "from external import *",
                        "def mystery(): pass", "async def mystery(): pass", "class mystery: pass"):
            with self.subTest(binding=binding):
                doc = ast.parse(binding + "\n" + source)
                postimage = Census(DOC).resolver("m", "sqlglot/m.py", doc)
                full, _ = shared_write_effect(doc, {doc.body[-1].body[0].lineno}, None, "m",
                                              narrow_shared_args=True, census=postimage)
                self.assertTrue(full)
        chained = ast.parse("def f(self, expression):\n    expression.is_type("
                            "type(self.dialect).__class__.__new__(type(type(self.dialect)), "
                            "'Alias', (type(self.dialect),), {}))")
        resolver = Census(DOC).resolver("m", "sqlglot/m.py", chained)
        self.assertTrue(shared_write_effect(chained, {2}, None, "m", narrow_shared_args=True,
                                            census=resolver)[0])
        source = "def f(node, shared_p, obj, items, *rest):\n    node.is_type(exp.DType.INT)\n"
        tree = ast.parse(source)
        resolver = Census(DOC).resolver("m", "sqlglot/m.py", tree)
        self.assertFalse(shared_write_effect(tree, {2}, None, "m", narrow_shared_args=True, census=resolver)[0])
        self.assertTrue(shared_write_effect(tree, {2}, None, "m", narrow_shared_args=True)[0])

    def test_loads_shared(self):
        tree = ast.parse("def f(self, node):\n    x = self.TABLE\n    y = exp.DType.INT\n    z = REGISTRY\n")
        fn = tree.body[0]
        r = Census(DOC).resolver("m", "sqlglot/m.py", tree)
        nodes = lambda line: [n for n in ast.walk(fn) if getattr(n, "lineno", 0) == line]
        self.assertTrue(r.loads_shared(nodes(2), fn))
        self.assertFalse(r.loads_shared(nodes(3), fn))
        self.assertTrue(r.loads_shared(nodes(4), fn))

    def test_innermost_block(self):
        tree = ast.parse(dedent("""\
            def f(x):
                a = 1
                if x:
                    b = 2
                    c = 3
                return a
            """))
        fn = tree.body[0]
        self.assertIs(_innermost_block(fn, 4, 5), fn.body[1])
        self.assertIs(_innermost_block(fn, 3, 3), fn.body[1])   # a changed header
        self.assertIs(_innermost_block(fn, 2, 4), fn)


@unittest.skipUnless((REPO / ".dockerignore").exists(), "needs the repository checkout")
class ScopeIndexTest(unittest.TestCase):
    def test_nested_headers_and_conditional_declarations_share_scope_index(self):
        tree = ast.parse(dedent("""\
            class Outer:
                class Inner:
                    def run(self, default=lambda: 1):
                        try:
                            pass
                        except ValueError:
                            def recover(): return 1
                        match default:
                            case None:
                                class Local: pass
            """))
        parent, names = _hierarchy(tree, "sqlglot.example")
        source = Source("sqlglot.example", tree)
        self.assertEqual(parent, source.parents)
        self.assertEqual(names, _class_qualnames(source.parents, "sqlglot.example"))
        self.assertEqual(set(_qualnames(tree).values()),
                         {"Outer.Inner.run", "Outer.Inner.run.<locals>.recover"})


class DockerContextTest(unittest.TestCase):
    def test_every_copied_file_is_in_the_allow_list(self):
        allow = [line[1:].strip().lstrip("/") for line in (REPO / ".dockerignore").read_text().splitlines()
                 if line.startswith("!")]
        for line in (REPO / "Dockerfile").read_text().splitlines():
            if not line.startswith("COPY") or "--from" in line:
                continue
            for name in line.split()[1:-1]:
                name = name.rstrip("/")
                ok = any(name == a.rstrip("/") or fnmatch.fnmatch(name, a.replace("/**", "/*"))
                         or fnmatch.fnmatch(name + "/x", a) for a in allow)
                with self.subTest(name=name):
                    self.assertTrue(ok, f"{name} is copied but not allowed by .dockerignore")
                    self.assertTrue((REPO / name).exists(), name)


if __name__ == "__main__":
    unittest.main()
