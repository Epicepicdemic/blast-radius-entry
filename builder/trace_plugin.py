import json
import os
from pathlib import Path

import pytest
import probe


def pytest_configure(config):
    from _pytest.fixtures import FixtureDef
    finish = FixtureDef.finish

    def scoped_finish(fixture, request):
        previous = probe.context
        probe.switch("scope:" + request.node.nodeid)
        try:
            return finish(fixture, request)
        finally:
            probe.switch(previous)

    FixtureDef.finish = scoped_finish


@pytest.hookimpl(wrapper=True, tryfirst=True)
def pytest_make_collect_report(collector):
    previous = probe.context
    path = Path(collector.path)
    if path.suffix == ".py":
        probe.switch("collect:" + str(path.relative_to("/sqlglot")))
    try:
        return (yield)
    finally:
        probe.switch(previous)


def pytest_collection_finish(session):
    inventory = {item.nodeid: [node.nodeid for node in item.listchain()] for item in session.items}
    Path(os.environ["BR_TRACES"], "items.json").write_text(json.dumps(inventory))


@pytest.hookimpl(wrapper=True, tryfirst=True)
def pytest_runtest_protocol(item):
    probe.switch("test:" + item.nodeid)
    try:
        return (yield)
    finally:
        probe.switch("collect:")


@pytest.hookimpl(wrapper=True, tryfirst=True)
def pytest_fixture_setup(fixturedef, request):
    # unittest setUpClass is invoked inside pytest's class-scoped fixture.
    previous = probe.context
    probe.switch("scope:" + request.node.nodeid)
    try:
        return (yield)
    finally:
        probe.switch(previous)


passed = set()
skipped = set()


def pytest_runtest_logreport(report):
    if report.passed and report.when == "call":
        passed.add(report.nodeid)
    if report.skipped:
        skipped.add(report.nodeid)


def pytest_sessionfinish(session, exitstatus):
    Path(os.environ["BR_TRACES"], "status.json").write_text(json.dumps({
        "passed": sorted(passed), "skipped": sorted(skipped),
    }))
