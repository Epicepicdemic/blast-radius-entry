"""One-shot CPython line events, attributed to a test, fixture scope or importer."""
import atexit
import functools
import json
import os
import sys
import time
from collections import defaultdict

ROOT = "/sqlglot/"
monitor = sys.monitoring
tool = monitor.COVERAGE_ID
cold_test = os.environ.get("BR_COLD_TEST")
context = ""
ctx_t0 = time.perf_counter_ns()
case_ns = defaultdict(int)
hits = defaultdict(lambda: defaultdict(set))
opens = defaultdict(set)
loads = defaultdict(set)
submitters = set()
class_reads = defaultdict(set)
read_names = defaultdict(set)
entries = defaultdict(lambda: defaultdict(set))



@functools.cache
def source(filename):
    return filename[len(ROOT):] if filename.startswith(ROOT) else None


def module_context():
    if cold_test:
        return context
    frame = sys._getframe(1)
    while frame:
        filename = source(frame.f_code.co_filename)
        if filename and frame.f_code.co_name == "<module>":
            return "module:" + filename
        frame = frame.f_back
    return context


def line(code, lineno):
    path = source(code.co_filename)
    if path:
        hits[context][path].add(lineno)
        # Import-time work can be cached across tests, including calls into helpers.
        if context.startswith(("module:", "collect:")):
            origin = module_context()
            hits[origin][path].add(lineno)
    return monitor.DISABLE


def entered(code, offset):
    path = source(code.co_filename)
    if path and code.co_name == "<lambda>":
        entries[context][path].add(code.co_firstlineno)
        if context.startswith(("module:", "collect:")):
            entries[module_context()][path].add(code.co_firstlineno)
    return monitor.DISABLE


def audit(event, args):
    if event not in ("open", "os.listdir", "os.scandir", "exec"):
        return
    if event == "exec":
        code = args[0]
        path = source(code.co_filename)
        if path and code.co_name == "<module>":
            loads[context].add(path)
        return
    raw = args[0]
    if not isinstance(raw, (str, bytes)):
        return
    path = source(os.path.abspath(os.fsdecode(raw)))
    if path and "__pycache__/" not in path:
        # Import machinery opens bytecode/source for imports. Explicit source
        # readers (including inspect/linecache) must survive a formatting proof.
        frame = sys._getframe(1)
        if (frame.f_code.co_filename == "/builder/dialect_reads.py" and frame.f_code.co_name == "raw_sites"):
            return
        if path.endswith(".py") and frame.f_code.co_filename.startswith("<frozen importlib"):
            return
        opens[context].add(path)
        origin = module_context()
        if origin != context:
            opens[origin].add(path)


def switch(key):
    global context, ctx_t0
    if cold_test:
        key = "test:" + cold_test
    if key != context:
        now = time.perf_counter_ns()
        if context.startswith("case:"):
            case_ns[context] += now - ctx_t0
        ctx_t0 = now
        context = key
        os.environ["BR_CONTEXT"] = key
        monitor.restart_events()


def dump():
    global ctx_t0
    now = time.perf_counter_ns()
    if context.startswith("case:"):
        case_ns[context] += now - ctx_t0
        ctx_t0 = now
    out = os.environ["BR_TRACES"]
    with open(f"{out}/{os.getpid()}.json", "w") as file:
        json.dump({
            "lines": {k: {p: sorted(v) for p, v in files.items()} for k, files in hits.items()},
            "class_reads": {k: sorted(v) for k, v in class_reads.items()},
            "read_names": {k: sorted(v) for k, v in read_names.items()},
            "entries": {k: {p: sorted(v) for p, v in files.items()} for k, files in entries.items()},
            "opens": {k: sorted(v) for k, v in opens.items()},
            "loads": {k: sorted(v) for k, v in loads.items()},
            "submitters": sorted(submitters),
            "case_ns": dict(case_ns),
        }, file, separators=(",", ":"))


def task(key, fn, args, kwargs):
    switch(key)
    try:
        return fn(*args, **kwargs)
    finally:
        switch("pool")


def start():
    from importlib.machinery import SourceFileLoader
    from concurrent.futures import ProcessPoolExecutor
    execute = SourceFileLoader.exec_module

    def traced_module(loader, module):
        path = source(loader.path)
        if not path:
            return execute(loader, module)
        previous = context
        loads[previous].add(path)
        switch("module:" + path)
        try:
            result = execute(loader, module)
            if path == "sqlglot/dialects/dialect.py":
                from dialect_reads import install
                install(module)
            if path == "sqlglot/executor/python.py" and os.environ.get("BR_PHASE2_SPLIT") == "1":
                orig_execute = module.PythonExecutor.execute

                def traced_execute(self, plan):
                    prev = context
                    if prev.startswith("case:executor/"):
                        idx = prev.split("/", 1)[1]
                        switch("case:phase2/" + idx)
                        try:
                            return orig_execute(self, plan)
                        finally:
                            switch(prev)
                    return orig_execute(self, plan)

                module.PythonExecutor.execute = traced_execute
            return result
        finally:
            switch(previous)

    SourceFileLoader.exec_module = traced_module
    submit = ProcessPoolExecutor.submit

    def traced_submit(pool, fn, /, *args, **kwargs):
        submitters.add(context)
        return submit(pool, task, context, fn, args, kwargs)

    ProcessPoolExecutor.submit = traced_submit
    # Spawned pool workers deserialize arguments and serialize results outside
    # task(). Share that activity, including imports, among actual pool users.
    initial = os.environ.get("BR_CONTEXT", "collect:")
    if "multiprocessing.spawn" in " ".join(sys.orig_argv):
        initial = "pool"
    switch(initial)
    import class_reads as class_instrumentation
    class_instrumentation.start()
    sys.addaudithook(audit)
    monitor.use_tool_id(tool, "blast-radius")
    monitor.register_callback(tool, monitor.events.LINE, line)
    monitor.register_callback(tool, monitor.events.PY_START, entered)
    monitor.set_events(tool, monitor.events.LINE | monitor.events.PY_START)
    atexit.register(dump)
