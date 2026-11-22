"""Offline only. Keep the real loop, inputs, spawn pool, setup and assertions."""
from contextlib import contextmanager
import pytest
import probe


@contextmanager
def case(name):
    previous = probe.context
    probe.switch("case:" + name)
    try:
        yield
    finally:
        probe.switch(previous)


@pytest.fixture(autouse=True)
def label_queries(request, monkeypatch):
    name = request.node.name
    if name in ("test_execute_tpcds", "test_execute_tpch"):
        suite = request.cls
        attr = "tpcds_sqls" if name == "test_execute_tpcds" else "tpch_sqls"

        class Queries(list):
            def __iter__(self):
                for i, row in enumerate(super().__iter__()):
                    with case(f"executor/{i}"):
                        yield row

        monkeypatch.setattr(suite, attr, Queries(getattr(suite, attr)))
        compare = suite.subtestHelper

        def compare_query(self, i, *args, **kwargs):
            with case(f"executor/{i}"):
                return compare(self, i, *args, **kwargs)

        monkeypatch.setattr(suite, "subtestHelper", compare_query)
    elif name == "test_optimized_tpch":
        suite = request.cls

        class RowQueries(list):
            def __iter__(self):
                for i, row in enumerate(super().__iter__()):
                    with case(f"row/{i}"):
                        yield row

        monkeypatch.setattr(suite, "tpch_sqls", RowQueries(suite.tpch_sqls))
    elif name == "test_max_nodes":
        parse_one = request.module.parse_one
        number = 0

        def parse_case(*args, **kwargs):
            nonlocal number
            number += 1
            with case(f"parser/{number}"):
                return parse_one(*args, **kwargs)

        monkeypatch.setattr(request.module, "parse_one", parse_case)
    elif name == "test_generator_memory":
        inst = request.instance
        orig_sub = inst.subTest
        idx = 0

        @contextmanager
        def wrap_sub(*args, **kwargs):
            nonlocal idx
            cur = idx
            idx += 1
            d = kwargs.get("dialect")
            dname = getattr(d, "value", str(d)) if d is not None else ""
            with orig_sub(*args, **kwargs):
                with case(f"dialect/{cur}/{dname}"):
                    yield

        monkeypatch.setattr(inst, "subTest", wrap_sub)
    elif name in ("test_optimize_in_nulls", "test_cache_does_not_retain_queries"):
        inst = request.instance
        orig_sub = inst.subTest
        idx = 0

        @contextmanager
        def wrap_sub(*args, **kwargs):
            nonlocal idx
            cur = idx
            idx += 1
            with orig_sub(*args, **kwargs):
                with case(f"sub/{cur}"):
                    yield

        monkeypatch.setattr(inst, "subTest", wrap_sub)
    else:
        import tests.helpers as helpers_mod

        in_check_file = 0
        orig_pairs = getattr(request.module, "load_sql_fixture_pairs", helpers_mod.load_sql_fixture_pairs)
        orig_plain = getattr(request.module, "load_sql_fixtures", helpers_mod.load_sql_fixtures)
        orig_helpers_pairs = helpers_mod.load_sql_fixture_pairs
        orig_helpers_plain = helpers_mod.load_sql_fixtures

        def wrap_pairs(path, *args, **kwargs):
            if in_check_file:
                return orig_helpers_pairs(path, *args, **kwargs)
            def gen():
                for i, row in enumerate(orig_helpers_pairs(path, *args, **kwargs)):
                    with case(f"{path}#{i}"):
                        yield row
            return gen()

        def wrap_plain(path, *args, **kwargs):
            if in_check_file:
                return orig_helpers_plain(path, *args, **kwargs)
            def gen():
                for i, row in enumerate(orig_helpers_plain(path, *args, **kwargs)):
                    with case(f"{path}#{i}"):
                        yield row
            return gen()

        if hasattr(request.module, "load_sql_fixture_pairs"):
            monkeypatch.setattr(request.module, "load_sql_fixture_pairs", wrap_pairs)
        if hasattr(request.module, "load_sql_fixtures"):
            monkeypatch.setattr(request.module, "load_sql_fixtures", wrap_plain)
        monkeypatch.setattr(helpers_mod, "load_sql_fixture_pairs", wrap_pairs)
        monkeypatch.setattr(helpers_mod, "load_sql_fixtures", wrap_plain)

        if request.cls is not None and hasattr(request.cls, "check_file"):
            orig_check_file = request.cls.check_file
            orig_as_completed = getattr(request.module, "as_completed", None)

            def wrapped_check_file(self, file, func, *args, **kwargs):
                nonlocal in_check_file
                in_check_file += 1
                fixture_rel = f"optimizer/{file}.sql"
                fut_cases = {}
                cur_row = [0]
                orig_submit = self.pool.submit

                def pairs_spy(path, *pa, **pkw):
                    for i, row in enumerate(orig_helpers_pairs(path, *pa, **pkw)):
                        cur_row[0] = i
                        yield row

                def submit_spy(*s_args, **s_kwargs):
                    lbl = f"{fixture_rel}#{cur_row[0]}"
                    with case(lbl):
                        fut = orig_submit(*s_args, **s_kwargs)
                    fut_cases[fut] = lbl
                    return fut

                def as_completed_spy(futs, *ac_args, **ac_kwargs):
                    it = orig_as_completed(futs, *ac_args, **ac_kwargs) if orig_as_completed else iter(futs)
                    for fut in it:
                        lbl = fut_cases.get(fut)
                        if lbl is not None:
                            with case(lbl):
                                yield fut
                        else:
                            yield fut

                saved_pairs = request.module.load_sql_fixture_pairs
                saved_ac = getattr(request.module, "as_completed", None)
                request.module.load_sql_fixture_pairs = pairs_spy
                self.pool.submit = submit_spy
                if orig_as_completed is not None:
                    request.module.as_completed = as_completed_spy
                try:
                    return orig_check_file(self, file, func, *args, **kwargs)
                finally:
                    self.pool.submit = orig_submit
                    request.module.load_sql_fixture_pairs = saved_pairs
                    if orig_as_completed is not None:
                        request.module.as_completed = saved_ac
                    in_check_file -= 1

            monkeypatch.setattr(request.cls, "check_file", wrapped_check_file)
