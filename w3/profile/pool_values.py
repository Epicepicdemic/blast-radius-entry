"""Account for each submitted pin task and the concrete process which received it."""
from collections import defaultdict
from concurrent.futures import ProcessPoolExecutor
import json
from multiprocessing.util import Finalize
import os
from pathlib import Path

import value_profile as obs

submitted = {}
finished = {}
ready = False

def begin_worker():
    global ready
    obs.install()
    ready=True
    Finalize(None, finish_worker, exitpriority=0)

def tagged(seq, owner, func, args, kwargs):
    obs.current=owner
    try:
        result=func(*args, **kwargs)
        finished[seq]=owner
        return result
    finally:
        obs.current="@shared"

def finish_worker():
    path=Path(os.environ["W2_VALUE_WORKERS"])/f"{os.getpid()}.json"
    path.write_text(json.dumps(dict(ready=ready, finished=finished, observations=obs.snapshot()),separators=(",",":")))

def pytest_configure(config):
    obs.install()
    original=ProcessPoolExecutor.submit
    def submit(pool, func, /, *args, **kwargs):
        seq=len(submitted)
        submitted[seq]=obs.current
        return original(pool,tagged,seq,obs.current,func,args,kwargs)
    ProcessPoolExecutor.submit=submit

pytest_runtest_call=obs.pytest_runtest_call
pytest_runtest_logreport=obs.pytest_runtest_logreport

def pytest_sessionfinish(session,exitstatus):
    raw=dict(submitted=submitted, observations=obs.snapshot())
    Path(os.environ["W2_VALUE_WORKERS"],"parent.json").write_text(json.dumps(raw,separators=(",",":")))
