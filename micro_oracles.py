"""Parametric micro-oracles and counter guards for heavy SQLGlot tests."""
import ast
import gc
import marshal
import math
from pathlib import Path
import sys
import textwrap
import time
import tracemalloc

TEST_MAX_NODES = "tests/test_parser.py::TestParser::test_max_nodes"
TEST_GENERATOR_MEMORY = "tests/test_generator.py::TestGenerator::test_generator_memory"
TEST_SCOPE = "tests/test_optimizer.py::TestOptimizer::test_scope"
TEST_QUALIFY_CTE_CHAIN = "tests/test_optimizer.py::TestOptimizer::test_qualify_struct_star_long_cte_chain"
TEST_SERDE_RECURSION = "tests/test_serde.py::TestSerde::test_recursion"
TEST_DEEP_AST_ANNOTATION = "tests/test_optimizer.py::TestOptimizer::test_deep_ast_type_annotation"
TEST_NAMED_SELECTS_CHAIN = "tests/test_expressions.py::TestExprs::test_named_selects_long_by_name_chain"

STRESS_ORACLE_IDS = frozenset({
    TEST_QUALIFY_CTE_CHAIN,
    TEST_SERDE_RECURSION,
    TEST_DEEP_AST_ANNOTATION,
    TEST_NAMED_SELECTS_CHAIN,
})

MICRO_ORACLE_IDS = frozenset({
    TEST_MAX_NODES,
    TEST_GENERATOR_MEMORY,
    TEST_SCOPE,
}) | STRESS_ORACLE_IDS

_DIALECT_MODULES_BIN = Path(__file__).with_name("dialect_modules.bin")
_TEST_SCOPE_CODE_BIN = Path(__file__).with_name("test_scope_code.bin")
_DIALECT_MODULES_CACHE = None
_TEST_SCOPE_CODE_CACHE = None


def _eval_const_num(node):
    if isinstance(node, ast.Constant) and isinstance(node.value, (int, float)) and not isinstance(node.value, bool):
        return node.value
    if isinstance(node, ast.UnaryOp) and isinstance(node.op, (ast.UAdd, ast.USub)):
        val = _eval_const_num(node.operand)
        if val is not None:
            return val if isinstance(node.op, ast.UAdd) else -val
    if isinstance(node, ast.BinOp):
        left = _eval_const_num(node.left)
        right = _eval_const_num(node.right)
        if left is not None and right is not None:
            if isinstance(node.op, ast.Add):
                return left + right
            if isinstance(node.op, ast.Sub):
                return left - right
            if isinstance(node.op, ast.Mult):
                return left * right
            if isinstance(node.op, ast.FloorDiv) and right != 0:
                return left // right
            if isinstance(node.op, ast.LShift) and isinstance(left, int) and isinstance(right, int) and 0 <= right <= 30:
                return left << right
            if isinstance(node.op, ast.Pow) and isinstance(right, int) and 0 <= right <= 12:
                return left ** right
    return None


def _changed_ast_constants(changes, path_suffix=None):
    """Return numeric constants and identifiers added/removed on changed lines."""
    if not changes:
        return set(), set()
    if len(changes) == 1 and path_suffix is None:
        cached = getattr(changes[0], "_oracle_constants", None)
        if cached is not None:
            return cached
    from patching import parsed_source

    added_nums = set()
    removed_nums = set()
    changed_names = set()
    for c in changes:
        if not c.path.endswith(".py"):
            continue
        if path_suffix and not c.path.endswith(path_suffix):
            continue
        try:
            b_tree = parsed_source(c.before)
            a_tree = parsed_source(c.after)
        except SyntaxError:
            return None, None
        rem = c.removed
        add = c.added
        for tree, lines, out in ((b_tree, rem, removed_nums), (a_tree, add, added_nums)):
            for node in ast.walk(tree):
                ln = getattr(node, "lineno", None)
                if ln is not None and ln in lines:
                    num = _eval_const_num(node)
                    if num is not None:
                        out.add(num)
                    elif isinstance(node, ast.Name):
                        changed_names.add(node.id)
                    elif isinstance(node, ast.Attribute):
                        changed_names.add(node.attr)
    result = added_nums | removed_nums, changed_names
    if len(changes) == 1 and path_suffix is None:
        changes[0]._oracle_constants = result
    return result


def max_nodes_guard(changes):
    """Emit full test_max_nodes if diff introduces threshold literals >= 10_000."""
    if not changes:
        return True
    nums, _names = _changed_ast_constants(changes)
    if nums is None:
        return False
    return not any(n >= 10_000 for n in nums)


def scope_guard(changes):
    """Emit full test_scope if diff touches setrecursionlimit or constants >= 200."""
    if not changes:
        return True
    nums, names = _changed_ast_constants(changes)
    if nums is None:
        return False
    if "setrecursionlimit" in names:
        return False
    return not any(n >= 200 for n in nums)


def stress_guard(changes, threshold=200):
    """Emit full stress test if diff touches setrecursionlimit or constants >= threshold."""
    if not changes:
        return True
    nums, names = _changed_ast_constants(changes)
    if nums is None:
        return False
    if "setrecursionlimit" in names:
        return False
    return not any(n >= threshold for n in nums)


def check_max_nodes(changes=None):
    """Micro-oracle for TestParser.test_max_nodes.

    Runs Calls 1, 2, 5, 6 verbatim; measures c(8), c(9), c(10) at exact depth=100;
    verifies linearity, intercept + 10_000 * slope > 1_000_000, and exact > vs >=
    boundary at c(10). Diff literals >= 10_000 are rejected by max_nodes_guard.
    """
    if not max_nodes_guard(changes):
        return False

    import sqlglot
    from sqlglot import exp, parse_one
    from sqlglot.errors import ParseError
    from sqlglot.parser import Parser

    # Call 1
    if not isinstance(parse_one("SELECT 1", max_nodes=1_000_000), exp.Select):
        return False

    # Call 2
    cols = [f"col{i}" for i in range(500)]
    sql2 = f"SELECT {','.join(cols)} FROM t"
    if not isinstance(parse_one(sql2, max_nodes=1_000_000), exp.Select):
        return False

    # Exact depth=100 linear extrapolation for Calls 3 & 4
    depth = 100
    expr = "x" + "=x" * depth
    counts = []
    sql10 = ""
    for w in (8, 9, 10):
        sql = f"SELECT {','.join([expr] * w)}"
        if w == 10:
            sql10 = sql
        parser = Parser(max_nodes=1_000_000)
        parser.parse(sqlglot.tokenize(sql), sql)
        counts.append(parser._node_count)

    slope = counts[2] - counts[1]
    if slope <= 0 or slope != (counts[1] - counts[0]):
        return False
    intercept = counts[0] - 8 * slope
    if intercept + 10_000 * slope <= 1_000_000:
        return False

    # Exact boundary test at w=10: catches '>' -> '>=' mutations on _node_count > max_nodes
    c10 = counts[2]
    if not isinstance(parse_one(sql10, max_nodes=c10), exp.Select):
        return False
    try:
        parse_one(sql10, max_nodes=c10 - 1)
        return False
    except ParseError as exc:
        if "Maximum number of AST nodes" not in str(exc) or f"({c10 - 1})" not in str(exc):
            return False

    # Calls 5 & 6
    try:
        parse_one("SELECT " + ",".join(f"x={i}" for i in range(100)), max_nodes=5)
        return False
    except ParseError:
        pass
    if not isinstance(parse_one("SELECT 1, 2, 3"), exp.Select):
        return False

    return True


def _pause_hooks():
    saved_trace = sys.gettrace()
    saved_profile = sys.getprofile()
    sys.settrace(None)
    sys.setprofile(None)
    return saved_trace, saved_profile


def _restore_hooks(saved):
    saved_trace, saved_profile = saved
    if saved_profile is not None:
        sys.setprofile(saved_profile)
    if saved_trace is not None:
        sys.settrace(saved_trace)


def _compute_dialect_modules():
    from sqlglot.dialects.dialect import Dialect, Dialects

    by_dialect = {}
    for d in Dialects:
        obj = Dialect.get_or_raise(d)
        cls = obj if isinstance(obj, type) else type(obj)
        mods = {cls.__module__}
        for owner in (cls, getattr(cls, "Generator", None), getattr(cls, "Parser", None), getattr(cls, "Tokenizer", None)):
            if owner is not None:
                owner_cls = owner if isinstance(owner, type) else type(owner)
                for base in owner_cls.__mro__:
                    m = getattr(base, "__module__", "")
                    if (m.startswith("sqlglot.dialects.") or m.startswith("sqlglot.generators.")) and m not in (
                        "sqlglot.generator",
                        "sqlglot.dialects.dialect",
                    ):
                        mods.add(m)
        by_dialect[str(getattr(d, "value", d))] = sorted(mods)
    return by_dialect


def _load_dialect_modules():
    global _DIALECT_MODULES_CACHE
    if _DIALECT_MODULES_CACHE is not None:
        return _DIALECT_MODULES_CACHE
    if _DIALECT_MODULES_BIN.is_file():
        _DIALECT_MODULES_CACHE = marshal.loads(_DIALECT_MODULES_BIN.read_bytes())
        return _DIALECT_MODULES_CACHE
    return None


def target_dialects_for_paths(paths):
    """Return subset of Dialects names if paths only touch leaf dialect/generator files.

    Returns None to check all dialects whenever shared/base files or dialect
    inheritance might be affected.
    """
    if not paths:
        return None

    changed_mods = set()
    for p in paths:
        if not p.startswith("sqlglot/") or not p.endswith(".py"):
            return None
        mod = p[:-3].replace("/", ".").removesuffix(".__init__")
        if mod.startswith("sqlglot.dialects.") or mod.startswith("sqlglot.generators."):
            if mod in ("sqlglot.dialects.dialect", "sqlglot.dialects", "sqlglot.generators"):
                return None
            changed_mods.add(mod)
        else:
            return None

    # Use build-time MRO cache when running against real sqlglot (not mocked in unit tests).
    dialects_mod = sys.modules.get("sqlglot.dialects")
    use_cached = (
        dialects_mod is None
        or getattr(getattr(dialects_mod, "Dialect", None), "__module__", "") == "sqlglot.dialects.dialect"
    )
    if use_cached:
        cached = _load_dialect_modules()
        if cached is not None:
            hits = [d for d, mods in cached.items() if changed_mods.intersection(mods)]
            return hits or None

    try:
        from sqlglot.dialects.dialect import Dialect, Dialects
    except ImportError:
        sqlglot_dir = "/sqlglot"
        if sqlglot_dir not in sys.path and Path(sqlglot_dir).is_dir():
            sys.path.append(sqlglot_dir)
            from sqlglot.dialects.dialect import Dialect, Dialects
        else:
            return None

    by_module = {}
    for d in Dialects:
        obj = Dialect.get_or_raise(d)
        cls = obj if isinstance(obj, type) else type(obj)
        mods = {cls.__module__}
        for owner in (cls, getattr(cls, "Generator", None), getattr(cls, "Parser", None), getattr(cls, "Tokenizer", None)):
            if owner is not None:
                owner_cls = owner if isinstance(owner, type) else type(owner)
                for base in owner_cls.__mro__:
                    m = getattr(base, "__module__", "")
                    if (m.startswith("sqlglot.dialects.") or m.startswith("sqlglot.generators.")) and m not in (
                        "sqlglot.generator",
                        "sqlglot.dialects.dialect",
                    ):
                        mods.add(m)
        by_module[d] = mods

    hits = [d for d, mods in by_module.items() if mods & changed_mods]
    return hits or None


def target_dialects_for_changes(changes):
    if not changes:
        return None
    return target_dialects_for_paths([c.path for c in changes])


def check_generator_memory(changes=None, dialect_names=None, changed_paths=None, escalate=True):
    """Micro-oracle for TestGenerator.test_generator_memory.

    Pauses tracing hooks around tracemalloc, runs 100 iterations per dialect, and
    escalates any dialect with delta >= 32 B to 1,000 iterations (or always runs
    1,000 iterations when escalate=False).
    """
    from sqlglot.dialects import Dialect, Dialects

    if dialect_names is None:
        if changed_paths is not None:
            dialect_names = target_dialects_for_paths(changed_paths)
        else:
            dialect_names = target_dialects_for_changes(changes)
    targets = list(Dialects) if dialect_names is None else list(dialect_names)
    if not targets:
        return False

    saved = _pause_hooks()
    try:
        dialects = [Dialect.get_or_raise(name) for name in targets]
        if len(dialects) == 1:
            dialect = dialects[0]
            for _ in range(100):
                dialect.generator()
            gc.collect()

            need_full = not escalate
            if escalate:
                tracemalloc.start()
                try:
                    before = tracemalloc.get_traced_memory()[0]
                    for _ in range(100):
                        dialect.generator()
                    gc.collect()
                    after = tracemalloc.get_traced_memory()[0]
                finally:
                    tracemalloc.stop()
                need_full = (after - before >= 32)

            if need_full:
                tracemalloc.start()
                try:
                    b2 = tracemalloc.get_traced_memory()[0]
                    for _ in range(1000):
                        dialect.generator()
                    gc.collect()
                    a2 = tracemalloc.get_traced_memory()[0]
                finally:
                    tracemalloc.stop()
                if a2 - b2 >= 1024:
                    return False
        else:
            for dialect in dialects:
                for _ in range(100):
                    dialect.generator()
            gc.collect()

            probe_iters = 100 if escalate else 1000
            probe_limit = 64 if escalate else 1024
            tracemalloc.start()
            try:
                before = tracemalloc.get_traced_memory()[0]
                for dialect in dialects:
                    for _ in range(probe_iters):
                        dialect.generator()
                gc.collect()
                after = tracemalloc.get_traced_memory()[0]
            finally:
                tracemalloc.stop()

            if after - before >= probe_limit:
                for dialect in dialects:
                    tracemalloc.start()
                    try:
                        b2 = tracemalloc.get_traced_memory()[0]
                        for _ in range(1000):
                            dialect.generator()
                        gc.collect()
                        a2 = tracemalloc.get_traced_memory()[0]
                    finally:
                        tracemalloc.stop()
                    if a2 - b2 >= 1024:
                        return False
    finally:
        _restore_hooks(saved)
    return True


def _measure_depth_and_time(fn, repeats=1, measure_depth=True):
    times = []
    res = None
    for _ in range(repeats):
        t0 = time.perf_counter()
        res = fn()
        times.append(time.perf_counter() - t0)
    times.sort()
    median_t = times[len(times) // 2]

    if not measure_depth:
        return res, median_t, 0

    cur = 0
    peak = 0

    def _prof(frame, event, arg):
        nonlocal cur, peak
        if event == "call":
            cur += 1
            if cur > peak:
                peak = cur
        elif event == "return":
            cur -= 1

    saved = sys.getprofile()
    sys.setprofile(_prof)
    try:
        fn()
    finally:
        sys.setprofile(saved)
    return res, median_t, peak


def _current_stack_depth():
    depth = 0
    f = sys._getframe()
    while f is not None:
        depth += 1
        f = f.f_back
    return depth


def _compile_test_scope_unit_code(fn):
    import inspect

    src = textwrap.dedent(inspect.getsource(fn))
    tree = ast.parse(src)
    fn_def = tree.body[0]
    filtered = []
    skip_vars = {"many_unions", "scopes_using_traverse", "scopes_using_traverse_scope", "chain"}
    for stmt in fn_def.body:
        names = {n.id for n in ast.walk(stmt) if isinstance(n, ast.Name)}
        if names & skip_vars:
            continue
        filtered.append(stmt)
    fn_def.body = filtered
    ast.fix_missing_locations(tree)
    return compile(tree, "<micro_test_scope>", "exec")


def _load_test_scope_code(to_mod):
    global _TEST_SCOPE_CODE_CACHE
    if _TEST_SCOPE_CODE_CACHE is not None:
        return _TEST_SCOPE_CODE_CACHE
    if (
        _TEST_SCOPE_CODE_BIN.is_file()
        and getattr(to_mod, "__file__", "") == "/sqlglot/tests/test_optimizer.py"
    ):
        _TEST_SCOPE_CODE_CACHE = marshal.loads(_TEST_SCOPE_CODE_BIN.read_bytes())
        return _TEST_SCOPE_CODE_CACHE
    return _compile_test_scope_unit_code(to_mod.TestOptimizer.test_scope)


def _run_test_scope_unit_assertions(changed_paths=None):
    """Run all non-large-N assertions from TestOptimizer.test_scope verbatim."""
    global _TEST_SCOPE_CODE_CACHE
    use_fast = (
        (not changed_paths or "tests/test_optimizer.py" not in changed_paths)
        and "tests.test_optimizer" not in sys.modules
        and _TEST_SCOPE_CODE_BIN.is_file()
    )
    if use_fast:
        import unittest
        from sqlglot import exp, optimizer, parse_one
        from sqlglot.optimizer.scope import build_scope, traverse_scope, walk_in_scope

        if _TEST_SCOPE_CODE_CACHE is None:
            _TEST_SCOPE_CODE_CACHE = marshal.loads(_TEST_SCOPE_CODE_BIN.read_bytes())
        ns = {
            "__builtins__": __builtins__,
            "exp": exp,
            "optimizer": optimizer,
            "parse_one": parse_one,
            "build_scope": build_scope,
            "traverse_scope": traverse_scope,
            "walk_in_scope": walk_in_scope,
        }
        exec(_TEST_SCOPE_CODE_CACHE, ns)
        case = unittest.TestCase("assertTrue")
        ns["test_scope"](case)
        return

    import tests.test_optimizer as to

    use_cache = not changed_paths or "tests/test_optimizer.py" not in changed_paths
    code = _load_test_scope_code(to) if use_cache else _compile_test_scope_unit_code(to.TestOptimizer.test_scope)
    ns = dict(vars(to))
    exec(code, ns)
    case = to.TestOptimizer("test_scope")
    ns["test_scope"](case)


def _median_time(fn, repeats=3):
    times = []
    for _ in range(repeats):
        t0 = time.perf_counter()
        fn()
        times.append(time.perf_counter() - t0)
    times.sort()
    return times[len(times) // 2]


def _check_linear_scaling(make_input, run_fn, n_low, n_high, n_esc=None, check_res=None, check_depth=True):
    """Run fn at n_low and n_high (re-timing & escalating to n_esc on spike) for O(N) depth & time."""
    inp_low = make_input(n_low)
    inp_high = make_input(n_high)
    res_low, t_low, d_low = _measure_depth_and_time(lambda: run_fn(inp_low), repeats=1, measure_depth=check_depth)
    res_high, t_high, d_high = _measure_depth_and_time(lambda: run_fn(inp_high), repeats=1, measure_depth=check_depth)
    if check_res is not None:
        if not check_res(n_low, res_low) or not check_res(n_high, res_high):
            return False
    if check_depth and d_high - d_low > 2:
        return False
    ratio = t_high / max(t_low, 1e-4)
    if ratio >= 2.55 or t_low < 0.003:
        t_low = _median_time(lambda: run_fn(inp_low), repeats=3)
        t_high = _median_time(lambda: run_fn(inp_high), repeats=3)
        ratio = t_high / max(t_low, 1e-4)
    if ratio >= 3.0:
        return False
    if n_esc is not None and ratio >= 2.60:
        inp_esc = make_input(n_esc)
        res_esc, t_esc, d_esc = _measure_depth_and_time(lambda: run_fn(inp_esc), repeats=2, measure_depth=check_depth)
        if check_res is not None and not check_res(n_esc, res_esc):
            return False
        if check_depth and d_esc - d_high > 2:
            return False
        if t_esc / max(t_high, 1e-4) >= 2.8 or t_esc / max(t_low, 1e-4) >= 6.0:
            return False
    return True


def check_test_scope(changes=None, changed_paths=None):
    """Micro-oracle for TestOptimizer.test_scope.

    Runs all unit assertions verbatim, and checks N=240 vs N=480 (escalating to 960) union and hive chains
    under sys.setrecursionlimit(current + 150) for stack growth <= 2 and time ratio < 3.0.
    """
    if not scope_guard(changes):
        return False

    from sqlglot import parse_one
    from sqlglot.optimizer.scope import build_scope, traverse_scope

    try:
        _run_test_scope_unit_assertions(changed_paths=changed_paths)
    except BaseException:
        return False

    old_limit = sys.getrecursionlimit()
    cur_depth = _current_stack_depth()
    try:
        sys.setrecursionlimit(cur_depth + 150)

        u120 = parse_one(" UNION ALL ".join(["SELECT x FROM t"] * 120))
        a120 = list(build_scope(u120).traverse())
        b120 = traverse_scope(u120)
        if len(a120) != 239 or len(b120) != 239 or not all(x.expression is y.expression for x, y in zip(a120, b120)):
            return False

        if not _check_linear_scaling(
            lambda n: parse_one(" UNION ALL ".join(["SELECT x FROM t"] * n)),
            lambda expr: len(list(build_scope(expr).traverse())),
            240,
            480,
            n_esc=960,
            check_res=lambda n, r: r == 2 * n - 1,
            check_depth=True,
        ):
            return False

        if not _check_linear_scaling(
            lambda n: parse_one("SELECT 1" + " UNION SELECT 1 INTERSECT SELECT 1" * n, read="hive"),
            lambda expr: len(list(build_scope(expr).traverse())),
            240,
            480,
            n_esc=960,
            check_res=lambda n, r: r == 4 * n + 1,
            check_depth=False,
        ):
            return False
    except BaseException:
        return False
    finally:
        sys.setrecursionlimit(old_limit)

    return True


def check_qualify_cte_chain(changes=None):
    """Linear scaling micro-oracle for TestOptimizer.test_qualify_struct_star_long_cte_chain."""
    if not stress_guard(changes, threshold=25):
        return False

    from sqlglot import exp, parse_one
    from sqlglot.optimizer.annotate_types import annotate_types
    from sqlglot.optimizer.qualify import qualify

    schema = {"t": {"s": "STRUCT<x INT>"}}

    def make_query(join, n):
        ctes = ["c0 AS (SELECT s FROM t)"]
        for i in range(1, n):
            source = "t AS l" if join == "SEMI JOIN" else f"c{i - 1} AS l"
            if join == "CORRELATED":
                projection = "(SELECT l.s) AS s"
            else:
                projection = "l.s"
                if join:
                    source += f" {join} c{i - 1} AS r ON l.s = r.s"
            ctes.append(f"c{i} AS (SELECT {projection} FROM {source})")
        return parse_one(f"WITH {', '.join(ctes)} SELECT (s).* FROM c{n - 1}", dialect="risingwave")

    def run_chain(expr):
        q = qualify(expr.copy(), schema=schema, dialect="risingwave")
        annotate_types(q, schema=schema, dialect="risingwave")
        return q.named_selects, q.selects[0].is_type(exp.DType.INT)

    old_limit = sys.getrecursionlimit()
    cur_depth = _current_stack_depth()
    try:
        sys.setrecursionlimit(cur_depth + 150)
        for join in ("", "JOIN", "SEMI JOIN", "CORRELATED"):
            if not _check_linear_scaling(
                lambda n, j=join: make_query(j, n),
                run_chain,
                25,
                50,
                n_esc=100,
                check_res=lambda n, r: r == (["x"], True),
                check_depth=(join == "JOIN"),
            ):
                return False
    except BaseException:
        return False
    finally:
        sys.setrecursionlimit(old_limit)

    return True


def check_serde_recursion(changes=None):
    """Linear scaling micro-oracle for TestSerde.test_recursion."""
    if not stress_guard(changes, threshold=150):
        return False

    import pickle
    from sqlglot import parse_one
    from tests.test_serde import TestSerde

    tc = TestSerde("test_recursion")

    def make_expr(n):
        sql = "SELECT 1" + " UNION ALL SELECT 1" * n
        expr = parse_one(sql)
        return expr, expr.sql()

    def run_serde(pair):
        expr, before = pair
        dumped_ok = tc.dump_load(expr).sql() == before
        pickled_ok = pickle.loads(pickle.dumps(expr)).sql() == before
        return dumped_ok and pickled_ok

    old_limit = sys.getrecursionlimit()
    cur_depth = _current_stack_depth()
    try:
        sys.setrecursionlimit(cur_depth + 150)
        if not _check_linear_scaling(
            make_expr,
            run_serde,
            150,
            300,
            n_esc=600,
            check_res=lambda n, r: bool(r),
        ):
            return False
    except BaseException:
        return False
    finally:
        sys.setrecursionlimit(old_limit)

    return True


def check_deep_ast_annotation(changes=None):
    """Linear scaling micro-oracle for TestOptimizer.test_deep_ast_type_annotation."""
    if not stress_guard(changes, threshold=100):
        return False

    from sqlglot import exp, parse_one
    from sqlglot.optimizer.annotate_types import annotate_types

    old_limit = sys.getrecursionlimit()
    cur_depth = _current_stack_depth()
    try:
        sys.setrecursionlimit(cur_depth + 150)

        def make_union(n):
            sql = "SELECT 1 UNION ALL " * n + "SELECT 1"
            return sql, parse_one(sql)

        def run_union(pair):
            sql, expr = pair
            ann = annotate_types(expr.copy())
            return ann.sql() == sql and ann.selects[0].type.this == exp.DataType.Type.INT

        if not _check_linear_scaling(
            make_union,
            run_union,
            100,
            200,
            n_esc=400,
            check_res=lambda n, r: bool(r),
        ):
            return False

        def make_binary(n):
            sql = "SELECT " + "t.a + " * n + "t.a FROM t"
            return sql, parse_one(sql)

        def run_binary(pair):
            sql, expr = pair
            ann = annotate_types(expr.copy(), schema={"t": {"a": "INT"}})
            return ann.sql() == sql and ann.selects[0].type.this == exp.DataType.Type.INT

        if not _check_linear_scaling(
            make_binary,
            run_binary,
            100,
            200,
            n_esc=400,
            check_res=lambda n, r: bool(r),
        ):
            return False
    except BaseException:
        return False
    finally:
        sys.setrecursionlimit(old_limit)

    return True


def check_named_selects_chain(changes=None):
    """Linear scaling micro-oracle for TestExprs.test_named_selects_long_by_name_chain."""
    if not stress_guard(changes, threshold=100):
        return False

    from sqlglot import parse_one

    old_limit = sys.getrecursionlimit()
    cur_depth = _current_stack_depth()
    try:
        for unique in (False, True):
            def make_expr(n, u=unique):
                names = [f"a{i}" if u else "a" for i in range(n)]
                sql = " UNION ALL BY NAME ".join(f"SELECT 1 AS {name}" for name in names)
                prev = sys.getrecursionlimit()
                sys.setrecursionlimit(old_limit)
                try:
                    expr = parse_one(sql, dialect="duckdb")
                finally:
                    sys.setrecursionlimit(prev)
                expected = names if u else ["a"]
                return expr, expected

            def run_expr(pair):
                expr, expected = pair
                return expr.named_selects == expected

            sys.setrecursionlimit(cur_depth + 150)
            try:
                if not _check_linear_scaling(
                    make_expr,
                    run_expr,
                    100,
                    200,
                    n_esc=400,
                    check_res=lambda n, r: bool(r),
                ):
                    return False
            finally:
                sys.setrecursionlimit(old_limit)
    except BaseException:
        return False
    finally:
        sys.setrecursionlimit(old_limit)

    return True


def micro_oracle_guard(test_id, changes, use_micro_oracles=True, use_stress_probes=True):
    """Return True if the micro-oracle for ``test_id`` is admissible for ``changes``."""
    if test_id == TEST_MAX_NODES:
        return use_micro_oracles and max_nodes_guard(changes)
    if test_id == TEST_GENERATOR_MEMORY:
        return use_micro_oracles
    if test_id == TEST_SCOPE:
        return use_micro_oracles and scope_guard(changes)
    if test_id == TEST_QUALIFY_CTE_CHAIN:
        return use_stress_probes and stress_guard(changes, threshold=25)
    if test_id == TEST_SERDE_RECURSION:
        return use_stress_probes and stress_guard(changes, threshold=150)
    if test_id in (TEST_DEEP_AST_ANNOTATION, TEST_NAMED_SELECTS_CHAIN):
        return use_stress_probes and stress_guard(changes, threshold=100)
    return False


def run_micro_oracle(test_id, changes=None, changed_paths=None, dialect_names=None, escalate=True):
    """Run the micro-oracle for ``test_id``. Returns True iff the test passes."""
    if test_id == TEST_MAX_NODES:
        return check_max_nodes(changes=changes)
    if test_id == TEST_GENERATOR_MEMORY:
        return check_generator_memory(
            changes=changes,
            dialect_names=dialect_names,
            changed_paths=changed_paths,
            escalate=escalate,
        )
    if test_id == TEST_SCOPE:
        return check_test_scope(changes=changes, changed_paths=changed_paths)
    if test_id == TEST_QUALIFY_CTE_CHAIN:
        return check_qualify_cte_chain(changes=changes)
    if test_id == TEST_SERDE_RECURSION:
        return check_serde_recursion(changes=changes)
    if test_id == TEST_DEEP_AST_ANNOTATION:
        return check_deep_ast_annotation(changes=changes)
    if test_id == TEST_NAMED_SELECTS_CHAIN:
        return check_named_selects_chain(changes=changes)
    return False


def build_caches(root, dialect_out, scope_out):
    """Precompute dialect MRO map and filtered test_scope code object at image build time."""
    root = str(root)
    if root not in sys.path:
        sys.path.insert(0, root)
    by_dialect = _compute_dialect_modules()
    Path(dialect_out).write_bytes(marshal.dumps(by_dialect))
    import tests.test_optimizer as to
    code = _compile_test_scope_unit_code(to.TestOptimizer.test_scope)
    Path(scope_out).write_bytes(marshal.dumps(code))


if __name__ == "__main__":
    if len(sys.argv) == 5 and sys.argv[1] == "--build":
        build_caches(sys.argv[2], sys.argv[3], sys.argv[4])
