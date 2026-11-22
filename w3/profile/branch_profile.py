"""Record original branch destinations during the complete checked TPC-DS signature."""
from collections import defaultdict
import hashlib
import json
import os
import sys
import types

PIN = "/sqlglot/"
os.chdir(PIN)
sys.path[:0] = ["/app", PIN]
mon = sys.monitoring
tool = mon.PROFILER_ID
branches = {}
inspected = set()
auditing = False


def audit(event, args):
    global auditing
    if not auditing and event == "object.__getattr__" and args[1] == "__code__" and isinstance(args[0], types.FunctionType):
        auditing = True
        try:
            inspected.add(args[0].__code__)
        finally:
            auditing = False


def enter(code, offset):
    if code.co_filename.startswith(PIN + "sqlglot/"):
        branches.setdefault(code, defaultdict(set))
        mon.set_local_events(tool, code, mon.events.BRANCH)
    return mon.DISABLE


def branch(code, source, target):
    dest = branches[code][source]
    dest.add(target)
    # A conditional with two observed successors cannot certify an untaken arm.
    if len(dest) == 2:
        return mon.DISABLE


sys.addaudithook(audit)
mon.use_tool_id(tool, "pinned TPC-DS branches")
mon.register_callback(tool, mon.events.PY_START, enter)
mon.register_callback(tool, mon.events.BRANCH, branch)
mon.set_events(tool, mon.events.PY_START)
import slicer
baseline = slicer.load_tpcds_baseline()
assert baseline and slicer.compute_tpcds_mismatches(baseline) == (True, [])
mon.set_events(tool, 0)
result = {}
for code, edges in branches.items():
    path = code.co_filename[len(PIN):]
    key = f"{code.co_qualname}:{code.co_firstlineno}"
    by_name = result.setdefault(path, {})
    # A reflected, duplicated, or branch-free callable supplies no shortcut.
    if key in by_name or code in inspected:
        by_name[key] = None
    else:
        single = {i:next(iter(dest)) for i,dest in edges.items() if len(dest)==1}
        by_name[key] = [hashlib.sha256(code.co_code).hexdigest(), single] if single else None
print(json.dumps(dict(python=list(sys.version_info[:3]), rows=len(baseline), paths=result),
                 sort_keys=True,separators=(",",":")))
