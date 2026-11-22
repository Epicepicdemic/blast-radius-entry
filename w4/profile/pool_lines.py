"""Measure pin worker execution per submitted future; unacknowledged tasks stay opaque."""
import collections
import gzip
import json
import os
from pathlib import Path
import sys
import pytest
from concurrent.futures import ProcessPoolExecutor

current=None
submitted=collections.Counter()
all_ids=json.load(open("/app/maps.json"))["ids"]
pool=set(json.load(open("/app/pool_readers.json")))
out=Path("/tmp/pool-lines")
monitor=sys.monitoring
pending_lines=None
def traced_line(code,line):
    path=code.co_filename
    if path.startswith("/sqlglot/sqlglot/"):
        pending_lines[path[9:]].add(line)
    return monitor.DISABLE

def recorded_task(key,fn,args,kwargs):
    global pending_lines
    pending_lines=collections.defaultdict(set)
    tool=monitor.OPTIMIZER_ID
    if monitor.get_tool(tool) is None:monitor.use_tool_id(tool,"worker lines")
    monitor.register_callback(tool,monitor.events.LINE,traced_line)
    monitor.restart_events()
    monitor.set_events(tool,monitor.events.LINE)
    try:
        return fn(*args,**kwargs)
    finally:
        monitor.set_events(tool,0)
        doc={p:sorted(v) for p,v in pending_lines.items()}
        with gzip.open(out/key,"wt") as f:json.dump(doc,f,separators=(",",":"))

def pytest_configure(config):
    out.mkdir(exist_ok=True)
    orig=ProcessPoolExecutor.submit
    def submit(self,fn,*args,**kw):
        if current is None:raise RuntimeError("worker outside an attributed test")
        i=all_ids.index(current)
        submitted[i]+=1
        return orig(self,recorded_task,f"{i}.{submitted[i]}.gz",fn,args,kw)
    ProcessPoolExecutor.submit=submit

@pytest.hookimpl(wrapper=True,tryfirst=True)
def pytest_runtest_protocol(item):
    global current
    current=item.nodeid
    try:
        return (yield)
    finally:
        current=None

def pytest_collection_modifyitems(config,items):
    selected=[x for x in items if x.nodeid in pool]
    config.hook.pytest_deselected(items=[x for x in items if x.nodeid not in pool])
    items[:]=selected
    assert {x.nodeid for x in selected}==pool

def pytest_sessionfinish(session,exitstatus):
    assert not exitstatus
    rows=collections.defaultdict(dict)
    proved=0
    for tid in pool:
        i=all_ids.index(tid)
        for k in range(1,submitted[i]+1):
            f=out/f"{i}.{k}.gz"
            if not f.is_file():break
            for path,lines in json.load(gzip.open(f)).items():
                for line in lines:rows[path][line]=rows[path].get(line,0)|1<<i
        else:
            if submitted[i]:proved|=1<<i
    with gzip.open("/tmp/pool-lines.gz","wt") as f:
        json.dump(dict(ids=all_ids,proved=hex(proved),submissions=sum(submitted.values()),
                       rows={p:{k:hex(v) for k,v in m.items()} for p,m in rows.items()}),f,separators=(",",":"))
