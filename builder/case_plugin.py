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
    if request.node.name == "test_execute_tpcds":
        suite = request.cls
        class Queries(list):
            def __iter__(self):
                for i, row in enumerate(super().__iter__()):
                    with case(f"executor/{i}"):
                        yield row
        monkeypatch.setattr(suite, "tpcds_sqls", Queries(suite.tpcds_sqls))
        compare = suite.subtestHelper
        def compare_query(self, i, *args, **kwargs):
            with case(f"executor/{i}"):
                return compare(self, i, *args, **kwargs)
        monkeypatch.setattr(suite, "subtestHelper", compare_query)
    elif request.node.name == "test_max_nodes":
        parse_one = request.module.parse_one
        number = 0
        def parse_case(*args, **kwargs):
            nonlocal number
            number += 1
            with case(f"parser/{number}"):
                return parse_one(*args, **kwargs)
        monkeypatch.setattr(request.module, "parse_one", parse_case)
