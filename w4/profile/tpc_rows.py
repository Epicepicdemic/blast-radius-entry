"""Trace the exact pinned structural signature calculation, including setup outside rows."""
import collections
import gzip
import json
import os
import sys

sys.path[:0] = ["/app", "/sqlglot"]
os.chdir("/sqlglot")
import slicer

baseline = slicer.load_tpcds_baseline()
assert baseline
monitor = sys.monitoring
tool = monitor.PROFILER_ID
current = len(baseline)
lines = collections.defaultdict(dict)
def line(code, lineno):
    path = code.co_filename
    if path.startswith("/sqlglot/sqlglot/"):
        by_line = lines[path[9:]]
        by_line[lineno] = by_line.get(lineno, 0) | 1 << current
    return monitor.DISABLE

original = slicer.tpcds_query_sig
count = 0
def query(*a, **kw):
    global count, current
    current = count
    count += 1
    monitor.restart_events()
    try:
        return original(*a, **kw)
    finally:
        current = len(baseline)
        monitor.restart_events()

slicer.tpcds_query_sig = query
monitor.use_tool_id(tool, "wave4")
monitor.register_callback(tool, monitor.events.LINE, line)
monitor.set_events(tool, monitor.events.LINE)
ok, different = slicer.compute_tpcds_mismatches(baseline)
monitor.set_events(tool, 0)
assert count == len(baseline) and ok and not different
assert "sqlglot/parser.py" in lines
with gzip.GzipFile(fileobj=sys.stdout.buffer,mode="wb",mtime=0) as out:
    out.write(json.dumps({"rows":count,"lines":lines},separators=(",",":")).encode())
