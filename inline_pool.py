"""In-process ProcessPoolExecutor replacement with optional pickle round-tripping."""
import concurrent.futures
import pickle


class InlinePool:
    """Drop-in replacement for ProcessPoolExecutor that runs tasks in-process.

    Returns real ``concurrent.futures.Future`` objects so ``wait()`` and
    ``as_completed()`` work without monkeypatching ``concurrent.futures``.
    """

    def __init__(
        self,
        max_workers=None,
        mp_context=None,
        initializer=None,
        initargs=(),
        *,
        pickle_roundtrip=True,
        **kwargs,
    ):
        self.pickle_roundtrip = pickle_roundtrip
        if initializer is not None:
            initializer(*initargs)

    def submit(self, fn, *args, **kwargs):
        fut = concurrent.futures.Future()
        try:
            if self.pickle_roundtrip:
                fn, args, kwargs = pickle.loads(pickle.dumps((fn, args, kwargs)))
            res = fn(*args, **kwargs)
            if self.pickle_roundtrip:
                res = pickle.loads(pickle.dumps(res))
            fut.set_result(res)
        except BaseException as exc:
            fut.set_exception(exc)
        return fut

    def map(self, fn, *iterables, timeout=None, chunksize=1):
        for args in zip(*iterables):
            yield self.submit(fn, *args).result(timeout=timeout)

    def shutdown(self, wait=True, *, cancel_futures=False):
        pass

    def __enter__(self):
        return self

    def __exit__(self, exc_type, exc, tb):
        self.shutdown()


def make_pool_factory(*, pickle_roundtrip=True):
    def _factory(*args, **kwargs):
        kwargs.setdefault("pickle_roundtrip", pickle_roundtrip)
        return InlinePool(*args, **kwargs)

    return _factory


def install_inline_pool(*, pickle_roundtrip=True):
    """Patch loaded SQLGlot test modules to use InlinePool instead of spawn pools."""
    import sys

    factory = make_pool_factory(pickle_roundtrip=pickle_roundtrip)
    for mod_name in ("tests.test_optimizer", "tests.test_executor"):
        mod = sys.modules.get(mod_name)
        if mod is not None and hasattr(mod, "ProcessPoolExecutor"):
            mod.ProcessPoolExecutor = factory
    return factory


_OPT_DDL = """
CREATE TABLE x (a INT, b INT);
CREATE TABLE y (b INT, c INT);
CREATE TABLE z (b INT, c INT);
CREATE TABLE w (d TEXT, e TEXT);

INSERT INTO x VALUES (1, 1);
INSERT INTO x VALUES (2, 2);
INSERT INTO x VALUES (2, 2);
INSERT INTO x VALUES (3, 3);
INSERT INTO x VALUES (null, null);

INSERT INTO y VALUES (2, 2);
INSERT INTO y VALUES (2, 2);
INSERT INTO y VALUES (3, 3);
INSERT INTO y VALUES (4, 4);
INSERT INTO y VALUES (null, null);

INSERT INTO y VALUES (3, 3);
INSERT INTO y VALUES (3, 3);
INSERT INTO y VALUES (4, 4);
INSERT INTO y VALUES (5, 5);
INSERT INTO y VALUES (null, null);

INSERT INTO w VALUES ('a', 'b');

CREATE TABLE unpivotable (id INT, jan INT, feb INT, north INT, south INT);
INSERT INTO unpivotable VALUES (1, 100, 200, 7, 8);
INSERT INTO unpivotable VALUES (2, 300, 400, 9, 10);

CREATE TABLE pivotable (id INT, cat TEXT, val INT, kind TEXT, amt INT);
INSERT INTO pivotable VALUES (1, 'a', 10, 'x', 5);
INSERT INTO pivotable VALUES (1, 'b', 20, 'x', 5);

CREATE TABLE comparisons AS
SELECT * FROM (VALUES (1), (2), (NULL)) AS x(a)
CROSS JOIN (VALUES (1), (2), (NULL)) AS y(b)
CROSS JOIN (VALUES (TRUE), (FALSE), (NULL)) AS z(c);
"""


class LazyDuckDB:
    """Lazy DuckDB connection proxy that initializes optimizer fixture tables on first use."""

    def __init__(self, ddl=_OPT_DDL):
        self._ddl = ddl
        self._conn = None

    def _ensure(self):
        if self._conn is None:
            import duckdb

            conn = duckdb.connect(config={"threads": 1})
            conn.execute(self._ddl)
            self._conn = conn
        return self._conn

    def __getattr__(self, name):
        return getattr(self._ensure(), name)

    def close(self):
        if self._conn is not None:
            self._conn.close()
            self._conn = None


def install_lazy_duckdb():
    """Replace TestOptimizer.setUpClass so cls.conn initializes lazily on first execute."""
    import sys

    mod = sys.modules.get("tests.test_optimizer")
    if mod is None or not hasattr(mod, "TestOptimizer"):
        return False
    cls_type = mod.TestOptimizer
    if getattr(cls_type, "_br_lazy_duckdb", False):
        return True

    @classmethod
    def _lazy_setup_class(cls):
        import sqlglot
        from sqlglot.schema import MappingSchema

        cls.pool = mod.ProcessPoolExecutor(mp_context=mod.get_context("spawn"))
        cls.addClassCleanup(cls.pool.shutdown)
        sqlglot.schema = MappingSchema()
        cls.conn = LazyDuckDB()
        cls.addClassCleanup(cls.conn.close)

    cls_type.setUpClass = _lazy_setup_class
    cls_type._br_lazy_duckdb = True
    return True
