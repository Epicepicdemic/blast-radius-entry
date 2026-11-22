"""Build a test-to-executed-function and concrete-receiver index on the pin."""

import collections
import functools
import json
import os
import sys
from pathlib import Path

import pytest

ROOT = "/sqlglot/"
context = "@collection"
hits = collections.defaultdict(set)
inventory = {}
completed = set()
pool = set()
tool = sys.monitoring.PROFILER_ID
mon = sys.monitoring


def switch(key):
    global context
    context = key
    mon.restart_events()


def entry(code, offset):
    name = code.co_filename
    if name.startswith(ROOT + "sqlglot/"):
        hits[context].add((name[len(ROOT) :], code.co_qualname, code.co_firstlineno))
    return mon.DISABLE


@functools.cache
def origins(cls):
    return tuple(
        ("@" + base.__module__.replace(".", "/") + ".py", base.__qualname__, 0)
        for base in cls.__mro__
        if base.__module__.startswith("sqlglot.")
    )


def install_receivers():
    from sqlglot import Dialect, Generator, Parser, Tokenizer

    for cls in [Dialect, Parser, Generator, Tokenizer]:
        previous = cls.__init__

        @functools.wraps(previous)
        def record(self, *args, _init=previous, **kwargs):
            hits[context].update(origins(type(self)))
            return _init(self, *args, **kwargs)

        cls.__init__ = record


def pytest_configure(config):
    from concurrent.futures import ProcessPoolExecutor
    from _pytest.fixtures import FixtureDef

    install_receivers()
    prev_submit = ProcessPoolExecutor.submit

    def submit(self, *args, **kwargs):
        pool.add(context)
        return prev_submit(self, *args, **kwargs)

    ProcessPoolExecutor.submit = submit
    finish = FixtureDef.finish

    def scoped_finish(self, request):
        prev = context
        switch("scope:" + request.node.nodeid)
        try:
            return finish(self, request)
        finally:
            switch(prev)

    FixtureDef.finish = scoped_finish
    mon.use_tool_id(tool, "pinned exposure")
    mon.register_callback(tool, mon.events.PY_START, entry)
    mon.set_events(tool, mon.events.PY_START)


def pytest_collection_finish(session):
    for item in session.items:
        inventory[item.nodeid] = [ancestor.nodeid for ancestor in item.listchain()]


@pytest.hookimpl(wrapper=True, tryfirst=True)
def pytest_runtest_protocol(item):
    switch(item.nodeid)
    try:
        return (yield)
    finally:
        switch("@collection")


@pytest.hookimpl(wrapper=True, tryfirst=True)
def pytest_fixture_setup(fixturedef, request):
    prev = context
    switch("scope:" + request.node.nodeid)
    try:
        return (yield)
    finally:
        switch(prev)


def pytest_runtest_logreport(report):
    if report.when == "call" and report.passed:
        completed.add(report.nodeid)


def pytest_sessionfinish(session, exitstatus):
    mon.set_events(tool, 0)
    ids = json.loads(Path("/app/maps.json").read_bytes())["ids"]
    rows = collections.defaultdict(dict)
    unknown = 0
    for i, tid in enumerate(ids):
        bit = 1 << i
        if tid not in completed:
            unknown |= bit
            continue
        contexts = [tid, *("scope:" + s for s in inventory[tid])]
        if any(c in pool for c in contexts):
            unknown |= bit
        for c in contexts:
            for path, fn, line in hits[c]:
                key = f"{fn}:{line}"
                rows[path][key] = rows[path].get(key, 0) | bit
    out = dict(
        ids=ids,
        unknown=hex(unknown),
        collected=len(completed),
        exitstatus=exitstatus,
        rows={p: {k: hex(v) for k, v in names.items()} for p, names in rows.items()},
        startup=[list(item) for item in sorted(hits["@collection"])],
    )
    Path(os.environ["EXPOSURE_OUT"]).write_text(json.dumps(out, separators=(",", ":")))
