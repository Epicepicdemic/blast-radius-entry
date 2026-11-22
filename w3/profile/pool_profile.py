"""Pinned supplementary pass: attribute actual spawned-worker reads to submitters."""

import collections
import json
import os
from pathlib import Path
import pytest

clients = collections.defaultdict(set)
active = None


def setup_child():
    # Run in the new interpreter before it unpickles a task or initializer.
    import key_profile as kp

    kp.install_loader()
    from multiprocessing.util import Finalize

    Finalize(None, dump_child, exitpriority=0)


installed = False


def ensure_exposure():
    global installed
    if installed:
        return
    import exposure as xp

    xp.install_receivers()
    xp.mon.use_tool_id(xp.tool, "pinned worker execution")
    xp.mon.register_callback(xp.tool, xp.mon.events.PY_START, xp.entry)
    xp.mon.set_events(xp.tool, xp.mon.events.PY_START)
    installed = True


def tagged(tid, fn, args, kwargs):
    import exposure as xp
    import key_profile as kp

    ensure_exposure()
    kp.context = tid
    xp.switch(tid)
    clients[os.getpid()].add(tid)
    return fn(*args, **kwargs)


def dump_child():
    import exposure as xp
    import key_profile as kp

    payload = dict(
        clients=list(clients[os.getpid()]),
        functions={k: list(v) for k, v in xp.hits.items()},
        keys={k: list(v) for k, v in kp.hits.items()},
    )
    Path(os.environ["POOL_OUT"], f"{os.getpid()}.json").write_text(json.dumps(payload))


@pytest.hookimpl(wrapper=True, tryfirst=True)
def pytest_runtest_protocol(item):
    global active
    active = item.nodeid
    try:
        return (yield)
    finally:
        active = None


def pytest_configure(config):
    from concurrent.futures import ProcessPoolExecutor

    submit = ProcessPoolExecutor.submit

    def apply(pool, fn, /, *args, **kwargs):
        if active is None:
            raise RuntimeError("pool submission outside a test")
        return submit(pool, tagged, active, fn, args, kwargs)

    ProcessPoolExecutor.submit = apply
