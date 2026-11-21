"""Run candidate unittest cases under a copy-on-write, in-memory source overlay."""
from collections import defaultdict
import errno
import gc
import importlib
import importlib.abc
import importlib.util
import os
import resource
import select
import signal
import sys
import unittest
from types import CodeType, FunctionType
from time import monotonic

from fixture_overlay import Fixtures
from mutation_summaries import module_name
from state_watch import changed_readers, snapshot


# Includes the warm interpreter's inherited mappings (about 395 MiB on amd64).
CHILD_ADDRESS_SPACE = 896 * 1024 * 1024


class Overlay(importlib.abc.MetaPathFinder, importlib.abc.InspectLoader):
    def __init__(self, root, changes):
        self.files = {module_name(c.path): (str(root / c.path), c.after) for c in changes if c.path.endswith(".py")}

    def find_spec(self, fullname, path=None, target=None):
        if fullname not in self.files:
            return None
        return importlib.util.spec_from_file_location(fullname, self.files[fullname][0], loader=self)

    def get_filename(self, fullname):
        return self.files[fullname][0]

    def is_package(self, fullname):
        return self.get_filename(fullname).endswith("/__init__.py")

    def get_source(self, fullname):
        return importlib.util.decode_source(self.files[fullname][1])

    def get_code(self, fullname):
        filename, source = self.files[fullname]
        return compile(source, filename, "exec", dont_inherit=True)


class Result(unittest.TestResult):
    def __init__(self, indices, fixtures, checkpoint=None):
        super().__init__()
        self.fixtures = fixtures
        self.invalid = False
        self.incomplete = 0
        self.checkpoint = checkpoint
        self.indices = indices
        self.passed = 0
        self.observed = 0

    def startTest(self, test):
        super().startTest(test)
        self.fixtures.seen.clear()

    def stopTest(self, test):
        if self.checkpoint is not None:
            self.checkpoint(self.indices[test])
        super().stopTest(test)

    def addSkip(self, test, reason):
        parent = getattr(test, "test_case", test)
        if parent in self.indices:
            self.incomplete |= 1 << self.indices[parent]
        super().addSkip(test, reason)

    def addSuccess(self, test):
        if self.fixtures.files.keys() <= self.fixtures.seen:
            self.passed |= 1 << self.indices[test]
            self.observed |= 1 << self.indices[test]

    def addFailure(self, test, err):
        if self.fixtures.files.keys() <= self.fixtures.seen:
            self.observed |= 1 << self.indices[test]
        super().addFailure(test, err)

    def handle_error(self, err):
        error = err[1]
        if isinstance(error, MemoryError) or (isinstance(error, OSError) and error.errno == errno.ENOMEM):
            # unittest caught an allocation failure. Abort before accepting any passes.
            raise error
        if issubclass(err[0], (ImportError, TimeoutError)):
            self.invalid = True

    def addSubTest(self, test, subtest, err):
        if err and issubclass(err[0], AssertionError) and self.fixtures.files.keys() <= self.fixtures.seen:
            self.observed |= 1 << self.indices[test]
        if err:
            self.handle_error(err)
        super().addSubTest(test, subtest, err)

    def addError(self, test, err):
        # setUpClass, tearDownClass and module fixture errors are reported on
        # synthetic objects. They invalidate evidence for the entire run.
        self.handle_error(err)
        if test not in self.indices:
            raise RuntimeError("suite fixture failed")
        self.incomplete |= 1 << self.indices[test]
        super().addError(test, err)


def is_project(name):
    return name.split(".", 1)[0] in ("sqlglot", "tests")


def quiet():
    fd = os.open(os.devnull, os.O_WRONLY)
    for target in (1, 2):
        os.dup2(fd, target)
    os.close(fd)


def reap_group(pid):
    try:
        os.killpg(pid, signal.SIGKILL)
    except ProcessLookupError:
        pass
    try:
        os.kill(pid, signal.SIGKILL)
    except ProcessLookupError:
        pass
    for target in (pid, -pid):
        while True:
            try:
                os.waitpid(target, 0)
            except ChildProcessError:
                break


def cgroup_cpu():
    try:
        with open("/sys/fs/cgroup/cpu.stat", "rb") as f:
            for line in f:
                if line.startswith(b"usage_usec "):
                    return int(line.split()[1]) / 1_000_000
    except OSError:
        pass
    return None


class WarmSuite:
    def __init__(self, root, ids):
        self.root = root
        self.modules = tuple(dict.fromkeys(module_name(i.split("::")[0]) for i in ids))
        self.nodes = [i.split("::") for i in ids]
        self.ready = False

    def warm(self):
        import ctypes
        # Reap group members orphaned by a timed-out test. prctl is Linux-only.
        pr_set_child_subreaper = 36
        if ctypes.CDLL(None).prctl(pr_set_child_subreaper, 1, 0, 0, 0) != 0:
            raise RuntimeError("could not become a child subreaper")
        os.chdir(self.root)
        sys.path.insert(0, str(self.root))
        sys.dont_write_bytecode = True
        self.started = set()

        def record(code, offset):
            if code.co_filename.startswith(str(self.root) + "/"):
                self.started.add((code.co_filename, code.co_qualname, code.co_firstlineno))
            return sys.monitoring.DISABLE

        monitor = sys.monitoring
        tool = monitor.PROFILER_ID
        monitor.use_tool_id(tool, "pinned imports")
        try:
            monitor.register_callback(tool, monitor.events.PY_START, record)
            monitor.set_events(tool, monitor.events.PY_START)
            self.import_suite()
        finally:
            monitor.set_events(tool, 0)
            monitor.register_callback(tool, monitor.events.PY_START, None)
            monitor.free_tool_id(tool)
        self.functions = defaultdict(list)
        for obj in gc.get_objects():
            if type(obj) is FunctionType and obj.__code__.co_filename.startswith(str(self.root) + "/"):
                code = obj.__code__
                self.functions[code.co_filename, code.co_qualname, code.co_firstlineno].append(obj)
        self.ready = True

    def import_suite(self):
        importlib.import_module("sqlglot")
        for module in self.modules:
            importlib.import_module(module)

    def replace_bodies(self, overlay, hot):
        """Rebind every alias of a resident, uncalled function in the fork only."""
        if hot is None:
            return False
        compiled = {}
        updates = []
        for path, name, old_line, new_line in hot:
            module = module_name(path)
            if module not in sys.modules:
                continue  # Its first import will go through the overlay.
            filename = overlay.get_filename(module)
            key = filename, name, old_line
            if key in self.started or key not in self.functions:
                return False
            if module not in compiled:
                codes = {}
                pending = [overlay.get_code(module)]
                while pending:
                    code = pending.pop()
                    codes[code.co_qualname, code.co_firstlineno] = code
                    pending.extend(c for c in code.co_consts if isinstance(c, CodeType))
                compiled[module] = codes
            replacement = compiled[module].get((name, new_line))
            if replacement is None:
                return False
            for fn in self.functions[key]:
                if fn.__code__.co_freevars != replacement.co_freevars:
                    return False
                updates.append((fn, replacement))
        for fn, code in updates:
            fn.__code__ = code
        return True

    def execute(self, index, changes, indices, watch, hot, writers=0):
        overlay = Overlay(self.root, changes)
        sys.meta_path.insert(0, overlay)
        fixtures = Fixtures(self.root, changes)
        fixtures.install()
        filenames = {p for p, _ in overlay.files.values()}
        bypassed = False

        def audit(event, args):
            nonlocal bypassed
            if event in ("subprocess.Popen", "os.fork", "os.forkpty", "os.posix_spawn",
                         "os.system", "os.exec", "_posixsubprocess.fork_exec"):
                bypassed = True
                raise RuntimeError("external interpreter cannot inherit the overlay")
            if event == "open" and isinstance(args[0], (str, bytes)):
                path = os.path.abspath(os.fsdecode(args[0]))
                if path in filenames or (path in fixtures.files and fixtures.opening != path):
                    bypassed = True  # Direct reads see the read-only disk.
        sys.addaudithook(audit)
        if not self.replace_bodies(overlay, hot):
            for key in tuple(sys.modules):
                if is_project(key):
                    del sys.modules[key]
            self.import_suite()
        cases = {}
        for i in indices:
            path, cls, name = self.nodes[i]
            case_type = getattr(sys.modules[module_name(path)], cls)
            if issubclass(case_type, unittest.TestCase) and callable(getattr(case_type, name, None)):
                cases[case_type(name)] = i

        previous = snapshot(watch)
        readers = 0

        def checkpoint(i=None):
            nonlocal previous, readers
            if i is None or writers & (1 << i):
                state = snapshot(watch)
                readers |= changed_readers(index, previous, state)
                previous = state

        result = Result(cases, fixtures, checkpoint if writers else None)
        unittest.TestSuite(cases).run(result)
        checkpoint()  # Includes class and module teardown.
        invalid = bypassed or result.invalid or fixtures.unfaithful
        if writers & ~(result.observed & ~result.incomplete) or (writers and invalid):
            return 0, index.all
        return (0 if invalid else result.passed & ~result.incomplete), readers

    def check(self, index, changes, indices, watch, hot, writers, deadline, cap):
        if not writers:
            return self.verify(index, changes, indices, watch, hot, deadline, cap)
        # A removed mutation is invisible in the patched child's final state.
        # Inspect the same writers on both sides, tracking project-owned state
        # independently of the local name through which a helper received it.
        start = monotonic()
        cpu_start = cgroup_cpu()
        baseline, old_readers = self.verify(index, [], indices, (), (), deadline, cap, writers)
        if writers & ~baseline or old_readers == index.all:
            return 0, index.all
        cpu_now = cgroup_cpu()
        elapsed = monotonic() - start
        if cpu_start is not None and cpu_now is not None:
            elapsed = max(elapsed, cpu_now - cpu_start)
        remaining = cap - elapsed
        if remaining <= 0:
            return 0, index.all
        passed, new_readers = self.verify(index, changes, indices, (), hot, deadline, remaining, writers)
        return passed, old_readers | new_readers

    def verify(self, index, changes, indices, watch, hot, deadline, cap, writers=0):
        fallback = (0, index.all if writers else 0)
        if not self.ready or not indices:
            return fallback
        return fork_masks(lambda: self.execute(index, changes, indices, None if writers else set(watch),
                                               hot, writers), fallback, deadline, cap)


def fork_masks(run, fallback, deadline, cap):
    """Bound a fork and accept only two integer masks from a successful exit."""
    if cap <= 0 or monotonic() >= deadline:
        return fallback
    read_fd, write_fd = os.pipe()
    try:
        cpu_start = cgroup_cpu()
        pid = os.fork()
    except OSError:
        os.close(read_fd)
        os.close(write_fd)
        return fallback
    if pid == 0:
        try:
            os.close(read_fd)
            os.setpgid(0, 0)
            quiet()
            signal.signal(signal.SIGPROF, signal.SIG_DFL)
            signal.setitimer(signal.ITIMER_PROF, cap)
            resource.setrlimit(resource.RLIMIT_CPU, (5, 5))
            limit = CHILD_ADDRESS_SPACE
            for inherited in resource.getrlimit(resource.RLIMIT_AS):
                if inherited != resource.RLIM_INFINITY:
                    limit = min(limit, inherited)
            resource.setrlimit(resource.RLIMIT_AS, (limit, limit))
            passed, extra = run()
            os.write(write_fd, f"{passed:x} {extra:x}".encode())
        except BaseException:
            os._exit(1)
        os._exit(0)
    os.close(write_fd)
    try:
        try:
            os.setpgid(pid, pid)
        except ProcessLookupError:
            return fallback
        # Wait for exit, not for EOF on a descriptor a descendant could
        # inherit. Keep the leader unreaped until its group has been killed.
        pid_fd = os.pidfd_open(pid)
        try:
            end = min(deadline, monotonic() + cap + 1)
            while True:
                left = end - monotonic()
                if left <= 0:
                    return fallback
                done = select.select([pid_fd], [], [], min(left, 0.05))[0]
                if cpu_start is not None:
                    cpu_now = cgroup_cpu()
                    if cpu_now is None or cpu_now - cpu_start >= cap:
                        return fallback
                if done:
                    break
        finally:
            os.close(pid_fd)
        status = os.waitid(os.P_PID, pid, os.WEXITED | os.WNOWAIT)
        if status.si_code != os.CLD_EXITED or status.si_status != 0:
            return fallback
        os.set_blocking(read_fd, False)
        reply = os.read(read_fd, 4096)
        passed, extra = (int(x, 16) for x in reply.split())
        return passed, extra
    except (OSError, ValueError):
        return fallback
    finally:
        os.close(read_fd)
        reap_group(pid)


def runnable(test_id):
    parts = test_id.split("::")
    if len(parts) != 3:
        return False
    path, _, method = parts
    # ProcessPoolExecutor(spawn) and the external integration environment
    # cannot consume this process's in-memory source. Allocation tests measure
    # the interpreter's pre-existing allocation state.
    return (path not in ("tests/test_optimizer.py", "tests/test_sqlglotc.py")
            and not (path == "tests/test_executor.py" and method in ("test_execute_tpch", "test_execute_tpcds"))
            and method != "test_generator_memory")


def schedule(indices, durations, limit):
    """A deterministic work list. A hard CPU or wall limit rolls back all drops."""
    chosen = []
    remaining = limit
    for i in indices:
        # Include dispatch overhead even on zero-duration cases.
        estimate = durations[i] + 2
        if estimate <= remaining:
            remaining -= estimate
            chosen.append(i)
    return chosen
