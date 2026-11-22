"""Add pin operand evidence from every acknowledged instrumented process-pool task."""
import collections
import gzip
import json
import os
from pathlib import Path
import sys
from concurrent.futures import ProcessPoolExecutor
import operands

ids=json.load(open("/app/maps.json"))["ids"]
target=set(json.load(open("/app/pool_readers.json")))
folder=Path("/tmp/worker-operands")
submitted=collections.Counter()
spawned=set()
def observe(event, args):
    if event in ('subprocess.Popen','os.fork','os.forkpty','os.posix_spawn','os.system','os.exec','_posixsubprocess.fork_exec'):
        spawned.add(scope.where())
scope=operands.scopes
entries=set()

def task(key,fn,args,kwargs):
    operands.comparisons.clear()
    operands.callbacks.clear()
    # Spawn can bypass the installed source loader. Such a task is opaque.
    ready=hasattr(__import__("builtins"),"_br5_compare") and any(type(f) is operands.Finder for f in sys.meta_path)
    try:return fn(*args,**kwargs)
    finally:
        with gzip.open(folder/key,"wt") as fh:
            json.dump(dict(ready=ready and operands.monitor.get_tool(operands.tool)=='pinned test code',test_entries=sorted(operands.started),comparisons={k:sorted(v) for k,v in operands.comparisons.items()},
                           callbacks={k:sorted(v) for k,v in operands.callbacks.items()}),fh,separators=(",",":"))

def pytest_collection_modifyitems(config,items):
    keep=[i for i in items if i.nodeid in target]
    config.hook.pytest_deselected(items=[i for i in items if i.nodeid not in target])
    items[:]=keep
    assert {i.nodeid for i in keep}==target

def pytest_configure(config):
    operands.pytest_configure(config)
    sys.addaudithook(observe)
    folder.mkdir(exist_ok=True)
    orig=ProcessPoolExecutor.submit
    def submit(pool,fn,*args,**kw):
        name=scope.where()
        n=ids.index(name)
        submitted[name]+=1
        return orig(pool,task,f"{n}.{submitted[name]}.gz",fn,args,kw)
    ProcessPoolExecutor.submit=submit

pytest_runtest_protocol=scope.pytest_runtest_protocol
pytest_fixture_setup=scope.pytest_fixture_setup
pytest_collection_finish=scope.pytest_collection_finish
pytest_runtest_logreport=scope.pytest_runtest_logreport

def pytest_sessionfinish(session,exitstatus):
    assert not exitstatus and set(scope.passed)>=target
    proved=0
    out={s:collections.defaultdict(dict) for s in ("comparisons","callbacks")}
    for name,count in submitted.items():
        n=ids.index(name)
        for i in range(1,count+1):
            p=folder/f"{n}.{i}.gz"
            if not p.exists():break
            r=json.load(gzip.open(p))
            if not r["ready"]:break
            entries.update(map(tuple,r["test_entries"]))
            for s in out:
                for site,vals in r[s].items():
                    for v in vals:out[s][site][v]=out[s][site].get(v,0)|1<<n
        else:
            if count:proved|=1<<n
    # Include the clean parent in this independent pool-only schedule as well.
    for s in out:
        for site,vals in getattr(operands,s).items():
            for v,tags in vals.items():
                m=0
                for t in tags:
                    if t in ids:m|=1<<ids.index(t)
                    elif t.startswith("@scope/"):
                        m|=sum(1<<ids.index(name) for name,parents in scope.contexts.items() if name in ids and t[7:] in parents)
                    else:m=(1<<len(ids))-1
                out[s][site][v]=out[s][site].get(v,0)|m
    unresolved=set()
    for t in spawned:
        if t in target:unresolved.add(t)
        elif t.startswith('@scope/'):
            unresolved.update(n for n,ps in scope.contexts.items() if t[7:] in ps)
        else:unresolved.update(target)
    no_process=sum(1<<ids.index(n) for n in target-set(submitted)-unresolved)
    data=dict(ids=ids,proved=hex(proved),no_process=hex(no_process),test_entries=sorted(entries|operands.started),tasks=sum(submitted.values()),
              **{s:{k:{v:hex(m) for v,m in vals.items()} for k,vals in sorted(out[s].items())} for s in out})
    Path("/tmp/operand_workers.gz").write_bytes(gzip.compress(json.dumps(data,separators=(",",":")).encode(),mtime=0))
