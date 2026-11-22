import concurrent.futures
import difflib
from pathlib import Path
import pickle
from tempfile import TemporaryDirectory
import unittest

from inline_pool import (
    InlinePool,
    LazyDuckDB,
    install_inline_pool,
    install_lazy_duckdb,
    make_pool_factory,
)
from micro_oracles import (
    MICRO_ORACLE_IDS,
    TEST_GENERATOR_MEMORY,
    TEST_MAX_NODES,
    TEST_SCOPE,
    max_nodes_guard,
    scope_guard,
)
from patching import apply_patch


def _diff_change(root, path, old, new):
    target = root / path
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(old)
    diff = "".join(difflib.unified_diff(old.splitlines(True), new.splitlines(True), f"a/{path}", f"b/{path}", n=0))
    change, = apply_patch(diff.encode(), root)
    return change


def _add(x, y):
    return x + y


class _Unpicklable:
    def __reduce__(self):
        raise pickle.PicklingError("broken pickle")


def _echo(x):
    return x


class HeavyStep1Tests(unittest.TestCase):
    def test_inline_pool_runs_and_roundtrips_pickle(self):
        called = []

        def init(v):
            called.append(v)

        with InlinePool(initializer=init, initargs=("ok",), pickle_roundtrip=True) as pool:
            self.assertEqual(called, ["ok"])
            fut = pool.submit(_add, 2, 3)
            self.assertIsInstance(fut, concurrent.futures.Future)
            self.assertEqual(fut.result(), 5)
            bad = pool.submit(_echo, _Unpicklable())
            with self.assertRaises(pickle.PicklingError):
                bad.result()
            mapped = list(pool.map(_add, [1, 2], [3, 4]))
            self.assertEqual(mapped, [4, 6])

    def test_inline_pool_can_disable_pickle_roundtrip(self):
        with InlinePool(pickle_roundtrip=False) as pool:
            obj = _Unpicklable()
            self.assertIs(pool.submit(_echo, obj).result(), obj)

    def test_make_pool_factory_and_install(self):
        import types
        import sys

        fake_mod = types.ModuleType("tests.test_optimizer")
        fake_mod.ProcessPoolExecutor = object()
        sys.modules["tests.test_optimizer"] = fake_mod
        try:
            factory = install_inline_pool(pickle_roundtrip=True)
            self.assertIs(fake_mod.ProcessPoolExecutor, factory)
            with fake_mod.ProcessPoolExecutor() as pool:
                self.assertIsInstance(pool, InlinePool)
        finally:
            sys.modules.pop("tests.test_optimizer", None)

        f = make_pool_factory(pickle_roundtrip=True)
        with f() as pool:
            self.assertEqual(pool.submit(_add, 1, 2).result(), 3)

    def test_lazy_duckdb_delays_connect_until_attribute_access(self):
        import types
        import sys

        events = []

        class FakeConn:
            def execute(self, sql):
                events.append(("execute", sql))
                return "res"

            def sql(self, query):
                events.append(("sql", query))
                return query

            def close(self):
                events.append(("close",))

        fake_duckdb = types.ModuleType("duckdb")

        def connect(config=None):
            events.append(("connect", config))
            return FakeConn()

        fake_duckdb.connect = connect
        old_duckdb = sys.modules.get("duckdb")
        sys.modules["duckdb"] = fake_duckdb
        try:
            proxy = LazyDuckDB(ddl="CREATE TABLE t (a INT);")
            self.assertEqual(events, [])
            proxy.close()
            self.assertEqual(events, [])
            self.assertEqual(proxy.sql("SELECT 1"), "SELECT 1")
            self.assertEqual(
                events,
                [
                    ("connect", {"threads": 1}),
                    ("execute", "CREATE TABLE t (a INT);"),
                    ("sql", "SELECT 1"),
                ],
            )
            proxy.close()
            self.assertEqual(events[-1], ("close",))
        finally:
            if old_duckdb is None:
                sys.modules.pop("duckdb", None)
            else:
                sys.modules["duckdb"] = old_duckdb

    def test_install_lazy_duckdb_patches_setup_class(self):
        import types
        import sys

        fake_opt = types.ModuleType("tests.test_optimizer")

        class FakeTestOptimizer:
            cleanups = []

            @classmethod
            def setUpClass(cls):
                raise AssertionError("original setUpClass must be replaced")

            @classmethod
            def addClassCleanup(cls, fn):
                cls.cleanups.append(fn)

        fake_opt.TestOptimizer = FakeTestOptimizer
        old_mod = sys.modules.get("tests.test_optimizer")
        sys.modules["tests.test_optimizer"] = fake_opt
        try:
            self.assertTrue(install_lazy_duckdb())
            self.assertTrue(getattr(FakeTestOptimizer, "_br_lazy_duckdb", False))
        finally:
            if old_mod is None:
                sys.modules.pop("tests.test_optimizer", None)
            else:
                sys.modules["tests.test_optimizer"] = old_mod

    def test_max_nodes_guard(self):
        self.assertIn(TEST_MAX_NODES, MICRO_ORACLE_IDS)
        self.assertIn(TEST_GENERATOR_MEMORY, MICRO_ORACLE_IDS)
        self.assertIn(TEST_SCOPE, MICRO_ORACLE_IDS)
        with TemporaryDirectory() as tmp:
            root = Path(tmp).resolve()
            old = "def check(n, limit):\n    return n > limit\n"
            c_small = _diff_change(root, "sqlglot/parser.py", old, "def check(n, limit):\n    return n > limit + 1\n")
            self.assertTrue(max_nodes_guard([c_small]))

            c_big = _diff_change(root, "sqlglot/parser.py", old, "def check(n, limit):\n    return n > 50_000\n")
            self.assertFalse(max_nodes_guard([c_big]))

            c_pow = _diff_change(root, "sqlglot/parser.py", old, "def check(n, limit):\n    return n > 10 ** 5\n")
            self.assertFalse(max_nodes_guard([c_pow]))

    def test_scope_guard(self):
        with TemporaryDirectory() as tmp:
            root = Path(tmp).resolve()
            old = "def build(x):\n    return x\n"
            c_small = _diff_change(root, "sqlglot/optimizer/scope.py", old, "def build(x):\n    return x + 1\n")
            self.assertTrue(scope_guard([c_small]))

            c_limit = _diff_change(root, "sqlglot/optimizer/scope.py", old, "def build(x):\n    return x > 250\n")
            self.assertFalse(scope_guard([c_limit]))

            c_rec = _diff_change(root, "sqlglot/optimizer/scope.py", old, "import sys\ndef build(x):\n    sys.setrecursionlimit(5000)\n    return x\n")
            self.assertFalse(scope_guard([c_rec]))

    def test_check_test_scope_rejects_quadratic_regression(self):
        import types
        import sys
        import micro_oracles

        class FakeExpr:
            def __init__(self, n, sql_text=""):
                self.expression = sql_text
                self.n = n

            def traverse(self):
                return [self] * self.n

        fake_sqlglot = types.ModuleType("sqlglot")
        fake_opt = types.ModuleType("sqlglot.optimizer")
        fake_scope = types.ModuleType("sqlglot.optimizer.scope")

        def fake_parse_one(sql, **kwargs):
            n = sql.count("UNION ALL") + 1
            if "INTERSECT" in sql:
                return 801 if sql.count("INTERSECT") == 200 else 1601
            return 399 if n == 200 else (799 if n == 400 else 1599)

        def fake_build_scope(expr):
            loops = (expr // 10) ** 2 * 400
            acc = 0
            for i in range(loops):
                acc += i
            return FakeExpr(expr)

        def fake_traverse_scope(expr):
            return [FakeExpr(expr)] * expr

        fake_sqlglot.parse_one = fake_parse_one
        fake_scope.build_scope = fake_build_scope
        fake_scope.traverse_scope = fake_traverse_scope
        fake_opt.scope = fake_scope

        fake_to = types.ModuleType("tests.test_optimizer")

        class FakeTestOptimizer:
            def __init__(self, name):
                pass

            def test_scope(self):
                pass

        fake_to.TestOptimizer = FakeTestOptimizer
        saved = {k: sys.modules.get(k) for k in ("sqlglot", "sqlglot.optimizer", "sqlglot.optimizer.scope", "tests.test_optimizer")}
        sys.modules["sqlglot"] = fake_sqlglot
        sys.modules["sqlglot.optimizer"] = fake_opt
        sys.modules["sqlglot.optimizer.scope"] = fake_scope
        sys.modules["tests.test_optimizer"] = fake_to
        try:
            self.assertFalse(micro_oracles.check_test_scope())
        finally:
            for k, old in saved.items():
                if old is None:
                    sys.modules.pop(k, None)
                else:
                    sys.modules[k] = old

    def test_dockerignore_covers_dockerfile_copies(self):
        repo = Path(__file__).resolve().parent.parent
        ignore_lines = [
            ln.strip()
            for ln in (repo / ".dockerignore").read_text().splitlines()
            if ln.strip() and not ln.strip().startswith("#")
        ]
        allowed = {ln[1:].rstrip("/") for ln in ignore_lines if ln.startswith("!")}
        dockerfile = (repo / "Dockerfile").read_text()
        for ln in dockerfile.splitlines():
            s = ln.strip()
            if not s.startswith("COPY "):
                continue
            raw_tokens = s.split()[1:]
            if any(tok.startswith("--from=") for tok in raw_tokens):
                continue
            tokens = [tok for tok in raw_tokens if not tok.startswith("--")]
            for src in tokens[:-1]:
                src_clean = src.rstrip("/")
                if "/" in src_clean:
                    top = src_clean.split("/", 1)[0]
                    self.assertTrue(
                        src_clean in allowed or top in allowed or f"{top}/**" in allowed,
                        f"{src} missing from .dockerignore allow-list",
                    )
                elif src_clean.endswith(".py") and "/*.py" in allowed:
                    continue
                else:
                    self.assertIn(src_clean, allowed, f"{src} missing from .dockerignore allow-list")
