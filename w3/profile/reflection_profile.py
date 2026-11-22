"""Track audit-visible function code readers on the unmodified, uninstrumented project."""
import json
import os
import sys
from collections import defaultdict
from pathlib import Path
from types import FunctionType

import pytest

reads = defaultdict(set)
passed = set()
incomplete = set()
current = "@shared"
busy = False

def observe(event, args):
    global busy
    if busy or event != "object.__getattr__" or args[1] != "__code__" or type(args[0]) is not FunctionType:
        return
    busy = True
    try:
        code = args[0].__code__
        path = code.co_filename
        if path.startswith("/sqlglot/"):
            source = path[len("/sqlglot/"):]
            reads[source].add(current)
            reads[source + ":" + code.co_qualname].add(current)
    finally:
        busy = False

def pytest_configure(config):
    sys.addaudithook(observe)

@pytest.hookimpl(wrapper=True, tryfirst=True)
def pytest_runtest_call(item):
    global current
    current = item.nodeid
    try:
        return (yield)
    finally:
        current = "@shared"

def pytest_runtest_logreport(report):
    if report.failed or report.skipped:
        incomplete.add(report.nodeid)
    if report.when == "call" and report.passed and getattr(report, "context", None) is None:
        passed.add(report.nodeid)

def pytest_sessionfinish(session,exitstatus):
    Path(os.environ["REFLECTION_OUT"]).write_text(json.dumps(
        dict(passed=sorted(passed-incomplete), paths={p:sorted(ids) for p,ids in reads.items()})))
