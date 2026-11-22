"""Sub-test slicing, fixture diffing, lazy TestExecutor setup, child hooks, and TPC-DS Phase 1."""
import ast
import hashlib
import marshal
import os
from pathlib import Path
import pickle
import sys
import textwrap

from patching import overlaps


TEST_EXECUTE_TPCDS = "tests/test_executor.py::TestExecutor::test_execute_tpcds"
TEST_EXECUTE_TPCH = "tests/test_executor.py::TestExecutor::test_execute_tpch"
TEST_OPTIMIZED_TPCH = "tests/test_executor.py::TestExecutor::test_optimized_tpch"
TEST_GENERATOR_MEMORY = "tests/test_generator.py::TestGenerator::test_generator_memory"
TEST_MAX_NODES = "tests/test_parser.py::TestParser::test_max_nodes"
TEST_OPTIMIZE_IN_NULLS = "tests/test_optimizer.py::TestOptimizer::test_optimize_in_nulls"
TEST_CACHE_SCHEMA = "tests/test_schema.py::TestSchema::test_cache_does_not_retain_queries"

EXECUTOR_TPC_IDS = frozenset({
    TEST_OPTIMIZED_TPCH,
    TEST_EXECUTE_TPCH,
    TEST_EXECUTE_TPCDS,
})
SLOW_UNITTEST_FILES = (
    "tests/test_executor.py",
    "tests/test_optimizer.py",
    "tests/test_sqlglotc.py",
)
TPCDS_BACKEND_PREFIXES = (
    "sqlglot/executor/",
    "sqlglot/expressions/",
    "tests/",
)
TPCDS_BACKEND_FILES = frozenset({
    "sqlglot/planner.py",
    "sqlglot/schema.py",
    "sqlglot/helper.py",
    "sqlglot/generator.py",
    "sqlglot/errors.py",
    "sqlglot/serde.py",
})

PLAIN_FIXTURES = frozenset({
    "identity.sql",
    "partial.sql",
    "optimizer/qualify_columns__invalid.sql",
})
TPCDS_FIXTURE = "optimizer/tpc-ds/tpc-ds.sql"
TPCH_FIXTURE = "optimizer/tpc-h/tpc-h.sql"

_TPCDS_BASELINE_BIN = Path(__file__).with_name("tpcds_baseline.bin")
_TPCDS_BASELINE_CACHE = None


def _filter_comments(text):
    return "\n".join(line for line in text.splitlines() if line and not line.startswith("--"))


def parse_fixture_plain(raw_bytes):
    text = raw_bytes.decode("utf-8", errors="surrogateescape")
    rows = []
    lines = []
    for line in _filter_comments(text).splitlines():
        lines.append(line)
        if not line.startswith("#"):
            rows.append("\n".join(lines))
            lines.clear()
    return tuple(rows)


def parse_fixture_pairs(raw_bytes):
    text = raw_bytes.decode("utf-8", errors="surrogateescape")
    stmts = _filter_comments(text).split(";")
    size = len(stmts)
    return tuple((stmts[i].strip(), stmts[i + 1].strip()) for i in range(0, size, 2) if i + 1 < size)


def parse_fixture_rows(rel_path, raw_bytes):
    if rel_path in PLAIN_FIXTURES:
        return parse_fixture_plain(raw_bytes)
    return parse_fixture_pairs(raw_bytes)


def _decode_test_entry(raw):
    masks = [int(x, 16) for x in raw["masks"]]
    contexts = raw["contexts"]
    ctx_bit = {c: (1 << i) for i, c in enumerate(contexts)}
    prefixes = set()
    for c in contexts[1:]:
        body = c[5:] if c.startswith("case:") else c
        if "#" in body:
            prefixes.add(body.split("#", 1)[0])
    return {
        "contexts": contexts,
        "ctx_bit": ctx_bit,
        "all_cases": ((1 << len(contexts)) - 1) & ~1,
        "masks": masks,
        "times_us": raw.get("times_us") or [0] * len(contexts),
        "total_us": sum(raw.get("times_us") or ()),
        "lines": raw.get("lines", {}),
        "opens": raw.get("opens", {}),
        "class_reads": raw.get("class_reads", {}),
        "dialect_reads": raw.get("dialect_reads", {}),
        "attributes": raw.get("attributes", {}),
        "keys": raw.get("keys", {}),
        "raw_class_reads": raw.get("raw_class_reads", {}),
        "fixture_prefixes": frozenset(prefixes),
    }


def _td_bit(td, table, key):
    ptr = td[table].get(key)
    return 0 if ptr is None else td["masks"][ptr]


def _td_range_mask(lines_map, masks, first, last):
    out = 0
    for n in range(first, last + 1):
        ptr = lines_map.get(str(n))
        if ptr is not None:
            out |= masks[ptr]
    return out


class CaseCoverage:
    """Lazy wrapper around ``case-coverage.json`` supporting per-row/case slicing."""

    def __init__(self, data):
        self.raw = data or {}
        self._cache = {}

    def has(self, tid):
        return tid in self.raw

    def _get(self, tid):
        dec = self._cache.get(tid)
        if dec is None and tid in self.raw:
            dec = _decode_test_entry(self.raw[tid])
            self._cache[tid] = dec
        return dec

    def total_us(self, tid):
        td = self._get(tid)
        return 0 if td is None else td["total_us"]

    def _full_plan(self, tid, td):
        contexts = td["contexts"][1:]
        exec_indices = None
        phase2_indices = None
        row_indices = None
        dialect_names = None
        sub_indices = None
        parser_calls = None
        fixture_indices = None

        if tid == TEST_EXECUTE_TPCDS:
            exec_indices = sorted(int(c.split("/", 1)[1]) for c in contexts if c.startswith("case:executor/"))
            phase2_indices = sorted(int(c.split("/", 1)[1]) for c in contexts if c.startswith("case:phase2/"))
        elif tid == TEST_EXECUTE_TPCH:
            exec_indices = sorted(int(c.split("/", 1)[1]) for c in contexts if c.startswith("case:executor/"))
        elif tid == TEST_OPTIMIZED_TPCH:
            row_indices = sorted(int(c.split("/", 1)[1]) for c in contexts if c.startswith("case:row/"))
        elif tid == TEST_GENERATOR_MEMORY:
            dialect_names = [c.split("/", 2)[2] for c in contexts if c.startswith("case:dialect/")]
        elif tid in (TEST_OPTIMIZE_IN_NULLS, TEST_CACHE_SCHEMA):
            sub_indices = sorted(int(c.split("/", 1)[1]) for c in contexts if c.startswith("case:sub/"))
        elif tid == TEST_MAX_NODES:
            parser_calls = sorted(int(c.split("/", 1)[1]) for c in contexts if c.startswith("case:parser/"))
        elif td["fixture_prefixes"]:
            fixture_indices = {p: None for p in td["fixture_prefixes"]}

        return {
            "full": True,
            "contexts": contexts,
            "est_us": td["total_us"],
            "exec_indices": exec_indices,
            "phase2_indices": phase2_indices,
            "row_indices": row_indices,
            "dialect_names": dialect_names,
            "sub_indices": sub_indices,
            "parser_calls": parser_calls,
            "fixture_indices": fixture_indices,
        }

    def _hit_mask(self, tid, td, changes, index, extra_bindings=None, can_slice_py=True):
        masks = td["masks"]
        ctx_bit = td["ctx_bit"]
        layout = index.data.get("layout", {})
        stmts_map = index.data.get("statements", {})
        hit = 0

        for change in changes:
            path = change.path
            if not path.endswith(".py"):
                if path.startswith("tests/fixtures/"):
                    rel = path[len("tests/fixtures/"):]
                    before_rows = parse_fixture_rows(rel, change.before)
                    after_rows = parse_fixture_rows(rel, change.after)
                    if len(before_rows) != len(after_rows):
                        return 1  # Index shift -> conservative full fallback.
                    changed = [i for i, (b, a) in enumerate(zip(before_rows, after_rows)) if b != a]
                    if rel in td["fixture_prefixes"]:
                        for i in changed:
                            bit = ctx_bit.get(f"case:{rel}#{i}")
                            if bit is None:
                                return 1
                            hit |= bit
                        continue
                    if tid == TEST_EXECUTE_TPCDS and rel == TPCDS_FIXTURE:
                        for i in changed:
                            eb = ctx_bit.get(f"case:executor/{i}")
                            pb = ctx_bit.get(f"case:phase2/{i}")
                            if eb is None:
                                return 1
                            hit |= eb | (pb or 0)
                            # Turning execute on for a previously non-execute query needs phase2.
                            if pb is None:
                                return 1
                        continue
                    if tid == TEST_EXECUTE_TPCH and rel == TPCH_FIXTURE:
                        for i in changed:
                            eb = ctx_bit.get(f"case:executor/{i}")
                            if eb is None:
                                return 1
                            hit |= eb
                            if "execute" in after_rows[i][0].lower() and "execute" not in before_rows[i][0].lower():
                                return 1
                        continue
                    if tid == TEST_OPTIMIZED_TPCH and rel == TPCH_FIXTURE:
                        for i in changed:
                            rb = ctx_bit.get(f"case:row/{i}")
                            if rb is None:
                                return 1
                            hit |= rb
                        continue
                open_mask = _td_bit(td, "opens", path)
                if open_mask:
                    hit |= open_mask
                elif not path.startswith("tests/fixtures/"):
                    return 1
                continue

            if not can_slice_py:
                return 1

            # Python file edits
            test_file = tid.split("::", 1)[0]
            if path == test_file or path == "tests/helpers.py":
                return 1
            if path.startswith("tests/"):
                if path in td["lines"] or path in td["opens"]:
                    return 1
                continue

            if path not in layout:
                return 1

            # Lazy class-level caches execute only on first construction in a run,
            # so subsequent cached rows cannot be safely excluded by line slicing.
            if path == "sqlglot/generator.py" and any(ln <= 105 for ln in (change.removed | change.insertions)):
                return 1
            if path == "sqlglot/dialects/dialect.py" and any(ln <= 290 for ln in (change.removed | change.insertions)):
                return 1

            hit |= _td_bit(td, "opens", path)

            functions, bindings = layout[path]
            lines_map = td["lines"].get(path, {})
            stmts = stmts_map.get(path, ())

            removed = sorted(change.removed)
            if removed and stmts:
                for first, last in stmts:
                    if overlaps(removed, first, last):
                        hit |= _td_range_mask(lines_map, masks, first, last)

            for pt in removed:
                owners = [(a, b) for a, b in functions if a < pt <= b]
                if not owners:
                    return 1
                ptr = lines_map.get(str(pt))
                if ptr is not None:
                    hit |= masks[ptr]
                else:
                    # Uncovered line inside an enclosing function: widen to cases that entered it.
                    owners.sort(key=lambda ab: ab[1] - ab[0])
                    for fa, fb in owners:
                        fn_hit = _td_range_mask(lines_map, masks, fa, fb)
                        if fn_hit:
                            hit |= fn_hit
                            break

            for ins in change.insertions:
                owners = [(a, b) for a, b in functions if a < ins <= b]
                if not owners:
                    return 1
                # Innermost enclosing function body; fall back outward if empty.
                owners.sort(key=lambda ab: ab[1] - ab[0])
                fn_hit = 0
                for fa, fb in owners:
                    fn_hit = _td_range_mask(lines_map, masks, fa, fb)
                    if fn_hit:
                        break
                if fn_hit:
                    hit |= fn_hit

            points = sorted(change.removed | change.insertions | {i + 1 for i in change.insertions})
            for first, last, bnames, entries in bindings:
                if overlaps(points, first, last):
                    for name in bnames:
                        hit |= _td_bit(td, "attributes", name)
                        hit |= _td_bit(td, "raw_class_reads", name)
                        hit |= _td_bit(td, "dialect_reads", name)
                    for i, (begin, end, key) in enumerate(entries):
                        boundary = entries[i + 1][0] if i + 1 < len(entries) else last
                        if overlaps(points, begin, max(end, boundary)):
                            hit |= _td_bit(td, "keys", key)

            try:
                ast.parse(change.before, type_comments=True)
                ast.parse(change.after, type_comments=True)
            except SyntaxError:
                return 1

            hit |= _td_bit(td, "attributes", "__code__") | _td_bit(td, "attributes", "__closure__")

            if extra_bindings and path in extra_bindings:
                for binding in extra_bindings[path]:
                    tag = binding[0]
                    if tag == "mod_val":
                        mod, name = binding[1], binding[2]
                        hit |= _td_bit(td, "attributes", name)
                        hit |= _td_bit(td, "dialect_reads", name)
                        hit |= _td_bit(td, "raw_class_reads", name)
                        if mod:
                            hit |= _td_bit(td, "class_reads", f"{mod}.{name}")
                    elif tag == "class":
                        qualname, name = binding[1], binding[2]
                        hit |= _td_bit(td, "attributes", name)
                        hit |= _td_bit(td, "dialect_reads", name) | _td_bit(td, "dialect_reads", "*")
                        hit |= _td_bit(td, "raw_class_reads", name) | _td_bit(td, "raw_class_reads", "*")
                        if qualname:
                            hit |= _td_bit(td, "class_reads", qualname)
                    elif tag == "cls_val":
                        qualname, attr = binding[1], binding[2]
                        hit |= _td_bit(td, "attributes", attr)
                        hit |= _td_bit(td, "dialect_reads", attr) | _td_bit(td, "dialect_reads", "*")
                        hit |= _td_bit(td, "raw_class_reads", attr) | _td_bit(td, "raw_class_reads", "*")
                        if qualname:
                            hit |= _td_bit(td, "class_reads", qualname) | _td_bit(td, "class_reads", f"{qualname}.{attr}")

        return hit

    def plan_slice(self, tid, changes, index, extra_bindings=None, can_slice_py=True):
        """Plan the subset of sub-tests / fixture rows to execute for ``tid``."""
        td = self._get(tid)
        if td is None:
            return None
        if not changes:
            return self._full_plan(tid, td)

        hit = self._hit_mask(tid, td, changes, index, extra_bindings=extra_bindings, can_slice_py=can_slice_py)
        if hit == 0 or (hit & 1):
            return self._full_plan(tid, td)

        contexts = td["contexts"]
        times_us = td["times_us"]
        selected_indices = [i for i in range(1, len(contexts)) if hit & (1 << i)]
        if not selected_indices:
            return self._full_plan(tid, td)

        # Sort selected contexts cheapest-first for faster fail-fast behavior.
        selected_indices.sort(key=lambda i: (times_us[i], i))
        sel_ctxs = [contexts[i] for i in selected_indices]
        est_us = sum(times_us[i] for i in selected_indices)

        exec_indices = None
        phase2_indices = None
        row_indices = None
        dialect_names = None
        sub_indices = None
        parser_calls = None
        fixture_indices = None

        if tid == TEST_EXECUTE_TPCDS:
            exec_set = set()
            p2_set = set()
            for c in sel_ctxs:
                if c.startswith("case:executor/"):
                    exec_set.add(int(c.split("/", 1)[1]))
                elif c.startswith("case:phase2/"):
                    p2_set.add(int(c.split("/", 1)[1]))
            exec_indices = sorted(exec_set | p2_set)
            phase2_indices = sorted(p2_set)
        elif tid == TEST_EXECUTE_TPCH:
            exec_indices = sorted(int(c.split("/", 1)[1]) for c in sel_ctxs if c.startswith("case:executor/"))
        elif tid == TEST_OPTIMIZED_TPCH:
            row_indices = sorted(int(c.split("/", 1)[1]) for c in sel_ctxs if c.startswith("case:row/"))
        elif tid == TEST_GENERATOR_MEMORY:
            dialect_names = [c.split("/", 2)[2] for c in sel_ctxs if c.startswith("case:dialect/")]
        elif tid in (TEST_OPTIMIZE_IN_NULLS, TEST_CACHE_SCHEMA):
            sub_indices = sorted(int(c.split("/", 1)[1]) for c in sel_ctxs if c.startswith("case:sub/"))
        elif tid == TEST_MAX_NODES:
            parser_calls = sorted(int(c.split("/", 1)[1]) for c in sel_ctxs if c.startswith("case:parser/"))
        elif td["fixture_prefixes"]:
            fixture_indices = {p: [] for p in td["fixture_prefixes"]}
            for c in sel_ctxs:
                body = c[5:] if c.startswith("case:") else c
                if "#" in body:
                    pref, sidx = body.rsplit("#", 1)
                    if pref in fixture_indices:
                        fixture_indices[pref].append(int(sidx))

        return {
            "full": False,
            "contexts": sel_ctxs,
            "est_us": est_us,
            "exec_indices": exec_indices,
            "phase2_indices": phase2_indices,
            "row_indices": row_indices,
            "dialect_names": dialect_names,
            "sub_indices": sub_indices,
            "parser_calls": parser_calls,
            "fixture_indices": fixture_indices,
        }


# ---------------------------------------------------------------------------
# TPC-DS Phase 1 structural query signatures and build-time baseline cache
# ---------------------------------------------------------------------------


def _hash_step_tree(root, pe, out_h):
    memo = {}

    def expr_repr(e):
        if e is None:
            return b"None"
        return repr(e).encode()

    def step_bytes(s):
        sid = id(s)
        if sid in memo:
            return memo[sid]
        sh = hashlib.blake2b(digest_size=16)
        sh.update(repr((s.type_name, s.name, s.limit, s.offset)).encode())
        sh.update(repr((
            getattr(s, "source_name", None),
            getattr(s, "left", None),
            getattr(s, "right", None),
            getattr(s, "distinct", None),
        )).encode())
        src = getattr(s, "source", None)
        if isinstance(src, str) or src is None:
            sh.update(repr(src).encode())
        else:
            sh.update(expr_repr(src))
        sh.update(expr_repr(getattr(s, "condition", None)))
        for seq_attr in ("projections", "aggregations", "operands", "key"):
            seq = getattr(s, seq_attr, None)
            sh.update(seq_attr.encode())
            if seq:
                for item in seq:
                    sh.update(expr_repr(item))
        grp = getattr(s, "group", None)
        if grp:
            for gk in sorted(grp):
                sh.update(gk.encode() + b"=" + expr_repr(grp[gk]))
        jns = getattr(s, "joins", None)
        if jns:
            for jname in sorted(jns):
                j = jns[jname]
                sh.update(jname.encode() + repr(j.get("side")).encode())
                sh.update(expr_repr(j.get("condition")))
                for jk in j.get("source_key", ()):
                    sh.update(b"sk:" + expr_repr(jk))
                for jk in j.get("join_key", ()):
                    sh.update(b"jk:" + expr_repr(jk))
        dep_pairs = sorted((step_bytes(d), d) for d in s.dependencies)
        for db, _ in dep_pairs:
            sh.update(b"dep:" + db)
        res = sh.digest()
        memo[sid] = res
        return res

    out_h.update(step_bytes(root))

    def walk_exec(s):
        cond = getattr(s, "condition", None)
        if cond is not None:
            out_h.update(pe.generator.generate(pe._replace_subqueries(cond)).encode())
        for lst_attr in ("projections", "aggregations", "operands", "key"):
            items = getattr(s, lst_attr, None)
            if items:
                for item in items:
                    out_h.update(pe.generator.generate(pe._replace_subqueries(item)).encode())
        grp = getattr(s, "group", None)
        if grp:
            for gk in sorted(grp):
                out_h.update(pe.generator.generate(pe._replace_subqueries(grp[gk])).encode())
        jns = getattr(s, "joins", None)
        if jns:
            for jname in sorted(jns):
                j = jns[jname]
                if j.get("condition") is not None:
                    out_h.update(pe.generator.generate(pe._replace_subqueries(j["condition"])).encode())
                for jk in j.get("source_key", ()):
                    out_h.update(pe.generator.generate(pe._replace_subqueries(jk)).encode())
                for jk in j.get("join_key", ()):
                    out_h.update(pe.generator.generate(pe._replace_subqueries(jk)).encode())
        for _, d in sorted(((memo[id(dep)], dep) for dep in s.dependencies), key=lambda x: x[0]):
            walk_exec(d)

    walk_exec(root)


def tpcds_query_sig(sql, meta, schema=None, dummy_base=None):
    from sqlglot import find_tables, parse_one, transpile
    from sqlglot.executor.python import PythonExecutor
    from sqlglot.executor.table import Table, ensure_tables
    from sqlglot.optimizer import optimize
    from sqlglot.planner import Plan
    from sqlglot.schema import ensure_schema
    from tests.helpers import TPCDS_SCHEMA

    h = hashlib.blake2b(digest_size=16)
    h.update(transpile(sql, write="duckdb")[0].encode())
    expr = parse_one(sql)
    expr2 = pickle.loads(pickle.dumps(expr))
    h.update(repr(expr2).encode())
    tlist = [t.name for t in find_tables(expr)]
    h.update(repr(tlist).encode())
    if meta.get("execute"):
        if dummy_base is None:
            dummy = {t: Table(columns=tuple(TPCDS_SCHEMA[t].keys()), rows=[]) for t in tlist if t in TPCDS_SCHEMA}
        else:
            dummy = {t: dummy_base[t] for t in tlist if t in dummy_base}
        tables_ = ensure_tables(dummy)
        sch = ensure_schema(TPCDS_SCHEMA) if schema is None else schema
        h.update(repr(tables_.supported_table_args).encode())
        h.update(repr(sch.supported_table_args).encode())
        opt = optimize(expr2, sch, leave_tables_isolated=True)
        h.update(opt.sql().encode())
        h.update(repr(opt).encode())
        plan = Plan(opt)
        pe = PythonExecutor(tables=tables_)
        _hash_step_tree(plan.root, pe, h)
        seen_subs = set()
        while True:
            pending = sorted(k for k in pe._subquery_plans if k not in seen_subs)
            if not pending:
                break
            for k in pending:
                seen_subs.add(k)
                h.update(k.encode())
                _hash_step_tree(pe._subquery_plans[k].root, pe, h)
    return h.digest()


def build_tpcds_baseline(root, out_path):
    root_str = str(root)
    old_cwd = os.getcwd()
    inserted = False
    if root_str not in sys.path:
        sys.path.insert(0, root_str)
        inserted = True
    try:
        os.chdir(root_str)
        from sqlglot.executor.table import Table
        from sqlglot.schema import ensure_schema
        from tests.helpers import TPCDS_SCHEMA, load_sql_fixture_pairs

        sqls = list(load_sql_fixture_pairs(TPCDS_FIXTURE))
        schema = ensure_schema(TPCDS_SCHEMA)
        dummy_base = {t: Table(columns=tuple(cols.keys()), rows=[]) for t, cols in TPCDS_SCHEMA.items()}
        sigs = [tpcds_query_sig(sql, meta, schema=schema, dummy_base=dummy_base) for meta, sql, _ in sqls]
        Path(out_path).write_bytes(marshal.dumps(sigs))
        return sigs
    finally:
        os.chdir(old_cwd)
        if inserted and sys.path and sys.path[0] == root_str:
            sys.path.pop(0)


def load_tpcds_baseline(path=None):
    global _TPCDS_BASELINE_CACHE
    target = _TPCDS_BASELINE_BIN if path is None else Path(path)
    if path is None and _TPCDS_BASELINE_CACHE is not None:
        return _TPCDS_BASELINE_CACHE
    if target.is_file():
        data = marshal.loads(target.read_bytes())
        if path is None:
            _TPCDS_BASELINE_CACHE = data
        return data
    return None


def compute_tpcds_mismatches(baseline_sigs, indices=None, max_mismatches=None):
    from sqlglot.executor.table import Table
    from sqlglot.schema import ensure_schema
    from tests.helpers import TPCDS_SCHEMA, load_sql_fixture_pairs

    sqls = list(load_sql_fixture_pairs(TPCDS_FIXTURE))
    n_total = len(baseline_sigs)
    if len(sqls) != n_total:
        return False, []
    target_indices = range(n_total) if indices is None else [int(i) for i in indices if 0 <= int(i) < n_total]
    schema = ensure_schema(TPCDS_SCHEMA)
    dummy_base = {t: Table(columns=tuple(cols.keys()), rows=[]) for t, cols in TPCDS_SCHEMA.items()}
    mismatched = []
    for idx in target_indices:
        meta, sql, _ = sqls[idx]
        try:
            sig = tpcds_query_sig(sql, meta, schema=schema, dummy_base=dummy_base)
        except BaseException:
            mismatched.append(idx)
            if max_mismatches is not None and len(mismatched) > max_mismatches:
                return True, mismatched
            continue
        if sig != baseline_sigs[idx]:
            mismatched.append(idx)
            if max_mismatches is not None and len(mismatched) > max_mismatches:
                return True, mismatched
    return True, mismatched


# ---------------------------------------------------------------------------
# Child-side runtime hooks (installed inside the forked test execution child)
# ---------------------------------------------------------------------------


class _LazyConn:
    """Lazy DuckDB connection wrapper for TestExecutor TPC-H / TPC-DS."""

    def __init__(self, directory, schema):
        self._dir = directory
        self._schema = schema
        self._conn = None

    def _ensure(self):
        if self._conn is None:
            import duckdb

            conn = duckdb.connect(config={"threads": 1})
            for table, columns in self._schema.items():
                file_name = f"{self._dir}{table}.csv.gz"
                conn.execute(
                    f"CREATE VIEW {table} AS "
                    f"SELECT * FROM READ_CSV('{file_name}', delim='|', header=True, columns={columns})"
                )
            self._conn = conn
        return self._conn

    def __getattr__(self, name):
        return getattr(self._ensure(), name)

    def close(self):
        if self._conn is not None:
            self._conn.close()
            self._conn = None


class _LazyTPCTables(dict):
    """Lazy dict mapping TPC table name -> Table, loading each CSV on first lookup."""

    def __init__(self, directory, schema):
        super().__init__()
        self._dir = directory
        self._schema = schema

    def _load_one(self, table):
        import ast as _ast
        import csv
        from sqlglot.executor.table import Table
        from tests.test_executor import open_file

        columns = self._schema[table]
        file_name = f"{self._dir}{table}.csv.gz"
        rows = []
        ctypes = []
        with open_file(file_name) as f:
            reader = csv.reader(f, delimiter="|")
            next(reader)
            for row in reader:
                if not ctypes:
                    for v in row:
                        try:
                            ctypes.append(type(_ast.literal_eval(v)))
                        except (ValueError, SyntaxError):
                            ctypes.append(str)
                rows.append(
                    tuple(None if (t is not str and v == "") else t(v) for t, v in zip(ctypes, row))
                )
        tbl = Table(columns=columns, rows=rows)
        super().__setitem__(table, tbl)
        return tbl

    def __contains__(self, key):
        return key in self._schema

    def __getitem__(self, key):
        if super().__contains__(key):
            return super().__getitem__(key)
        if key in self._schema:
            return self._load_one(key)
        raise KeyError(key)

    def get(self, key, default=None):
        if key in self._schema:
            return self[key]
        return default

    def keys(self):
        return self._schema.keys()

    def __iter__(self):
        return iter(self._schema)

    def __len__(self):
        return len(self._schema)

    def items(self):
        return [(k, self[k]) for k in self._schema]


def install_lazy_executor_setup(disable_sql_cache=False):
    """Replace TestExecutor.setUpClass with lazy DuckDB / CSV / fixture loaders."""
    te_mod = sys.modules.get("tests.test_executor")
    if te_mod is None or not hasattr(te_mod, "TestExecutor"):
        return False
    cls = te_mod.TestExecutor
    if getattr(cls, "_br_lazy_setup", False):
        return True

    @classmethod
    def _lazy_setup_class(c):
        from tests.helpers import TPCDS_SCHEMA, TPCH_SCHEMA, load_sql_fixture_pairs

        c.cache = {}
        c.tpch_conn = _LazyConn(te_mod.DIR_TPCH, TPCH_SCHEMA)
        c.tpcds_conn = _LazyConn(te_mod.DIR_TPCDS, TPCDS_SCHEMA)
        c.tpch_tables = _LazyTPCTables(te_mod.DIR_TPCH, TPCH_SCHEMA)
        c.tpcds_tables = _LazyTPCTables(te_mod.DIR_TPCDS, TPCDS_SCHEMA)
        c._br_tpch_sqls = None
        c._br_tpcds_sqls = None

        class _LazySQLs:
            def __init__(self, attr_name, fixture_name):
                self.attr_name = attr_name
                self.fixture_name = fixture_name

            def _ensure(self, owner):
                if disable_sql_cache:
                    return list(load_sql_fixture_pairs(self.fixture_name))
                val = getattr(owner, self.attr_name, None)
                if val is None:
                    val = list(load_sql_fixture_pairs(self.fixture_name))
                    setattr(owner, self.attr_name, val)
                return val

            def __iter__(self):
                return iter(self._ensure(c))

            def __len__(self):
                return len(self._ensure(c))

            def __getitem__(self, idx):
                return self._ensure(c)[idx]

        c.tpch_sqls = _LazySQLs("_br_tpch_sqls", TPCH_FIXTURE)
        c.tpcds_sqls = _LazySQLs("_br_tpcds_sqls", TPCDS_FIXTURE)

    @classmethod
    def _lazy_teardown_class(c):
        for attr in ("tpch_conn", "tpcds_conn"):
            conn = getattr(c, attr, None)
            if conn is not None and hasattr(conn, "close"):
                conn.close()

    cls.setUpClass = _lazy_setup_class
    cls.tearDownClass = _lazy_teardown_class
    cls._br_lazy_setup = True
    return True


def _rewrite_subtest_method(cls, method_name, keep_indices):
    """Rewrite a method's AST so only ``with self.subTest(...):`` at ``keep_indices`` run."""
    import inspect

    fn = getattr(cls, method_name, None)
    if fn is None:
        return False
    src = textwrap.dedent(inspect.getsource(fn))
    tree = ast.parse(src)
    fn_def = tree.body[0]

    class _SubTestGate(ast.NodeTransformer):
        def visit_With(self, node):
            self.generic_visit(node)
            is_sub = False
            for item in node.items:
                ctx = item.context_expr
                if (
                    isinstance(ctx, ast.Call)
                    and isinstance(ctx.func, ast.Attribute)
                    and ctx.func.attr == "subTest"
                ):
                    is_sub = True
                    break
            if not is_sub:
                return node
            gate = ast.parse(
                "_br_i = _br_ctr[0]\n"
                "_br_ctr[0] += 1\n"
                "if _br_i in _br_keep:\n"
                "    pass\n"
            ).body
            gate[2].body = [node]
            return gate

    fn_def = _SubTestGate().visit(fn_def)
    init = ast.parse("_br_ctr = [0]").body
    fn_def.body = init + fn_def.body
    tree.body[0] = fn_def
    ast.fix_missing_locations(tree)

    mod = sys.modules[cls.__module__]
    ns = dict(vars(mod))
    ns["_br_keep"] = frozenset(keep_indices)
    code = compile(tree, f"<sliced_{method_name}>", "exec")
    exec(code, ns)
    setattr(cls, method_name, ns[method_name])
    return True


def install_child_slices(slice_specs):
    """Configure per-test fixture, executor, and subTest slicing in the child process."""
    if not slice_specs:
        return

    import functools
    import tests.helpers as helpers_mod

    orig_helpers_plain = helpers_mod.load_sql_fixtures
    orig_helpers_pairs = helpers_mod.load_sql_fixture_pairs

    active_fixture_filter = [None]

    def _filtered_iter(raw_iter, rel_path, order):
        if order is None:
            for row in raw_iter:
                yield row
            return
        rows = list(raw_iter)
        if not order:
            return
        n = len(rows)
        seen = set()
        for idx in order:
            if 0 <= idx < n and idx not in seen:
                seen.add(idx)
                yield rows[idx]

    def sliced_plain(path, *args, **kwargs):
        filt = active_fixture_filter[0]
        if filt is not None and path in filt:
            return _filtered_iter(orig_helpers_plain(path, *args, **kwargs), path, filt[path])
        return orig_helpers_plain(path, *args, **kwargs)

    def sliced_pairs(path, *args, **kwargs):
        filt = active_fixture_filter[0]
        if filt is not None and path in filt:
            return _filtered_iter(orig_helpers_pairs(path, *args, **kwargs), path, filt[path])
        return orig_helpers_pairs(path, *args, **kwargs)

    has_fixture_slices = any(
        (not sp.get("full", True)) and sp.get("fixture_indices")
        for sp in slice_specs.values()
    )
    if has_fixture_slices:
        helpers_mod.load_sql_fixtures = sliced_plain
        helpers_mod.load_sql_fixture_pairs = sliced_pairs
        for mod_name in ("tests.test_optimizer", "tests.test_serde", "tests.test_transpile"):
            mod = sys.modules.get(mod_name)
            if mod is not None:
                if hasattr(mod, "load_sql_fixtures"):
                    mod.load_sql_fixtures = sliced_plain
                if hasattr(mod, "load_sql_fixture_pairs"):
                    mod.load_sql_fixture_pairs = sliced_pairs

    for tid, sp in slice_specs.items():
        if sp.get("full", True):
            continue
        mod_path, cls_name, meth_name = tid.split("::")
        mod_name = mod_path[:-3].replace("/", ".")
        mod = sys.modules.get(mod_name)
        if mod is None:
            continue
        cls = getattr(mod, cls_name, None)
        if cls is None:
            continue

        if tid == TEST_EXECUTE_TPCDS:
            keep = sp.get("phase2_indices") if sp.get("phase2_indices") is not None else sp.get("exec_indices")
            if keep is not None:
                keep_set = frozenset(keep)
                orig_fn = getattr(cls, meth_name)

                @functools.wraps(orig_fn)
                def _wrapped_tpcds(self, _orig=orig_fn, _keep=keep_set):
                    prev_sqls = self.__class__.tpcds_sqls
                    all_sqls = list(prev_sqls)
                    self.__class__.tpcds_sqls = [
                        row if idx in _keep else ({}, "SELECT 1", "")
                        for idx, row in enumerate(all_sqls)
                    ]
                    try:
                        return _orig(self)
                    finally:
                        self.__class__.tpcds_sqls = prev_sqls

                setattr(cls, meth_name, _wrapped_tpcds)

        elif tid == TEST_EXECUTE_TPCH:
            keep = sp.get("exec_indices")
            if keep is not None:
                keep_set = frozenset(keep)
                orig_fn = getattr(cls, meth_name)

                @functools.wraps(orig_fn)
                def _wrapped_tpch(self, _orig=orig_fn, _keep=keep_set):
                    prev_sqls = self.__class__.tpch_sqls
                    all_sqls = list(prev_sqls)
                    self.__class__.tpch_sqls = [
                        row if idx in _keep else ({}, "SELECT 1", "")
                        for idx, row in enumerate(all_sqls)
                    ]
                    try:
                        return _orig(self)
                    finally:
                        self.__class__.tpch_sqls = prev_sqls

                setattr(cls, meth_name, _wrapped_tpch)

        elif tid == TEST_OPTIMIZED_TPCH:
            keep = sp.get("row_indices")
            if keep is not None:
                keep_set = frozenset(keep)
                orig_fn = getattr(cls, meth_name)

                @functools.wraps(orig_fn)
                def _wrapped_opt_tpch(self, _orig=orig_fn, _keep=keep_set):
                    prev_sqls = self.__class__.tpch_sqls
                    all_sqls = list(prev_sqls)
                    self.__class__.tpch_sqls = [
                        row for idx, row in enumerate(all_sqls) if idx in _keep
                    ]
                    try:
                        return _orig(self)
                    finally:
                        self.__class__.tpch_sqls = prev_sqls

                setattr(cls, meth_name, _wrapped_opt_tpch)

        elif tid in (TEST_OPTIMIZE_IN_NULLS, TEST_CACHE_SCHEMA):
            sub_idx = sp.get("sub_indices")
            if sub_idx is not None:
                _rewrite_subtest_method(cls, meth_name, sub_idx)

        elif sp.get("fixture_indices"):
            fmap = sp["fixture_indices"]
            orig_fn = getattr(cls, meth_name)

            @functools.wraps(orig_fn)
            def _wrapped_fix(self, _orig=orig_fn, _fmap=fmap):
                prev = active_fixture_filter[0]
                active_fixture_filter[0] = _fmap
                try:
                    return _orig(self)
                finally:
                    active_fixture_filter[0] = prev

            setattr(cls, meth_name, _wrapped_fix)


if __name__ == "__main__":
    if len(sys.argv) >= 4 and sys.argv[1] == "--build-tpcds":
        build_tpcds_baseline(sys.argv[2], sys.argv[3])
