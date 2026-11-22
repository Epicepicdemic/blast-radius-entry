"""Run candidate unittest cases under a copy-on-write, in-memory source overlay."""
from collections import defaultdict
import errno
import functools
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

from bounded_batch import CHILD_ADDRESS_SPACE, limit_child_resources
from fixture_overlay import Fixtures
from mutation_summaries import module_name
from state_watch import changed_readers, snapshot


class _FailFastStop(BaseException):
    """Stops the current leaf unittest immediately on its first subTest failure."""


def _wrap_call_test_method(leaf):
    orig = leaf._callTestMethod

    def _wrapped(method):
        try:
            return orig(method)
        except _FailFastStop:
            return None

    leaf._callTestMethod = _wrapped


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

    def _exc_info_to_string(self, err, test):
        # Avoid linecache opening changed files on disk (which trips audit bypassed=True).
        return ""

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


class _HeavyStreamResult(unittest.TestResult):
    def __init__(self, indices, fixtures, bypassed_fn, checkpoint_readers, emit_pass,
                 emit_abort, safe_teardown_types, zero_indices=frozenset(), all_mask=0):
        super().__init__()
        self.indices = indices
        self.fixtures = fixtures
        self.bypassed_fn = bypassed_fn
        self.checkpoint_readers = checkpoint_readers
        self.emit_pass = emit_pass
        self.emit_abort = emit_abort
        self.safe_teardown_types = safe_teardown_types
        self.zero_indices = zero_indices
        self.all_mask = all_mask
        self.bad = False
        self.aborted = False
        self.readers_overflow = False
        self.nonzero_failed = False
        self.buffered_passes = []

    def _exc_info_to_string(self, err, test):
        return ""

    def _mark_bad(self, test):
        self.bad = True
        idx = self.indices.get(test)
        if idx is not None and idx not in self.zero_indices:
            self.nonzero_failed = True

    def _handle_error(self, err):
        error = err[1]
        if isinstance(error, MemoryError) or (isinstance(error, OSError) and error.errno == errno.ENOMEM):
            self.aborted = True
            self.emit_abort()
            raise error
        if issubclass(err[0], (ImportError, TimeoutError)):
            self.bad = True

    def startTest(self, test):
        super().startTest(test)
        self.bad = False
        self.fixtures.seen.clear()

    def addError(self, test, err):
        self._handle_error(err)
        if test not in self.indices:
            self.aborted = True
            self.emit_abort()
            self.stop()
            return
        self._mark_bad(test)
        super().addError(test, err)

    def addFailure(self, test, err):
        self._mark_bad(test)
        super().addFailure(test, err)

    def addSkip(self, test, reason):
        parent = getattr(test, "test_case", test)
        self._mark_bad(parent)
        super().addSkip(test, reason)

    def addExpectedFailure(self, test, err):
        self._mark_bad(test)
        super().addExpectedFailure(test, err)

    def addUnexpectedSuccess(self, test):
        self._mark_bad(test)
        super().addUnexpectedSuccess(test)

    def addSubTest(self, test, subtest, err):
        if err is not None:
            self._handle_error(err)
            self._mark_bad(test)
            raise _FailFastStop()

    def stopTest(self, test):
        delta_readers = self.checkpoint_readers()
        idx = self.indices.get(test)
        if self.all_mask and delta_readers == self.all_mask:
            self._mark_bad(test)
            self.readers_overflow = True
            self.stop()
            super().stopTest(test)
            return
        if (
            idx is not None
            and not self.bad
            and not self.aborted
            and not self.bypassed_fn()
            and not self.fixtures.unfaithful
            and (self.fixtures.files.keys() <= self.fixtures.seen)
        ):
            if type(test) in self.safe_teardown_types:
                self.emit_pass(idx, delta_readers)
            else:
                self.buffered_passes.append((idx, delta_readers))
        elif idx is not None and idx not in self.zero_indices:
            self.nonzero_failed = True
        super().stopTest(test)


def _has_trivial_teardown(case_type):
    if case_type.__name__ in ("TestOptimizer", "TestExecutor"):
        return True
    td = getattr(case_type, "tearDownClass", None)
    base_td = unittest.TestCase.tearDownClass
    if getattr(td, "__func__", td) is not getattr(base_td, "__func__", base_td):
        return False
    cleanups = getattr(case_type, "_class_cleanups", ())
    return not cleanups


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
        if (self.root / "sqlglot/serde.py").is_file():
            importlib.import_module("sqlglot.serde")
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

    def _prepare_child(self, changes, hot, needed_modules=None):
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
            has_py = any(c.path.endswith(".py") for c in changes)
            if has_py or not hasattr(self, "started"):
                for key in tuple(sys.modules):
                    if is_project(key):
                        del sys.modules[key]
            if needed_modules is not None:
                if "sqlglot" not in sys.modules:
                    importlib.import_module("sqlglot")
                for mod in needed_modules:
                    if mod not in sys.modules:
                        importlib.import_module(mod)
            elif has_py or not all(module_name(p) in sys.modules for p, _, _ in self.nodes):
                self.import_suite()
        return fixtures, lambda: bypassed

    def execute(self, index, changes, indices, watch, hot, writers=0):
        needed = tuple(dict.fromkeys(module_name(self.nodes[i][0]) for i in indices))
        fixtures, is_bypassed = self._prepare_child(changes, hot, needed_modules=needed)
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
        invalid = is_bypassed() or result.invalid or fixtures.unfaithful
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

    def _install_heavy_hooks(self, slice_map, flags, has_fixture_overlay):
        if flags.get("setupclass_deamort", True):
            import slicer
            slicer.install_lazy_executor_setup(disable_sql_cache=has_fixture_overlay)

        if flags.get("inline_pool", True):
            import inline_pool
            inline_pool.install_inline_pool(pickle_roundtrip=True)
            inline_pool.install_lazy_duckdb()

        if flags.get("row_slice", True) and slice_map:
            import slicer
            slicer.install_child_slices(slice_map)

    def _execute_heavy(self, index, changes, items, watch_set, hot, flags,
                       slice_map, dialect_map, write_fd):
        import micro_oracles
        needed = tuple(dict.fromkeys(module_name(self.nodes[idx][0]) for idx, is_orac, _ in items if not is_orac))
        fixtures, is_bypassed = self._prepare_child(changes, hot, needed_modules=needed)
        changed_paths = [c.path for c in changes]
        previous = snapshot(watch_set)

        def checkpoint_readers():
            nonlocal previous
            if not watch_set:
                return 0
            state = snapshot(watch_set)
            delta = changed_readers(index, previous, state)
            previous = state
            return delta

        def emit_line(line):
            os.write(write_fd, line.encode())

        def emit_pass(idx, readers):
            emit_line(f"P {idx} {readers:x}\n")

        def emit_abort():
            emit_line("ABORT\n")

        nonzero_failed = False
        oracle_items = [(idx, zero_ms) for idx, is_orac, zero_ms in items if is_orac]
        if oracle_items:
            if flags.get("micro_oracles", True):
                escalate = flags.get("gen_mem_escalate", True)
                for idx, zero_ms in oracle_items:
                    tid = "::".join(self.nodes[idx])
                    fixtures.seen.clear()
                    passed_orac = False
                    try:
                        passed_orac = bool(
                            micro_oracles.run_micro_oracle(
                                tid,
                                changes=changes,
                                changed_paths=changed_paths,
                                dialect_names=dialect_map.get(tid) if dialect_map else None,
                                escalate=escalate,
                            )
                        )
                    except BaseException:
                        passed_orac = False
                    delta_r = checkpoint_readers()
                    if index.all and delta_r == index.all:
                        nonzero_failed = True
                        break
                    if (
                        passed_orac
                        and not is_bypassed()
                        and not fixtures.unfaithful
                        and (fixtures.files.keys() <= fixtures.seen)
                    ):
                        emit_pass(idx, delta_r)
                    elif not zero_ms:
                        nonzero_failed = True
            else:
                if any(not zero_ms for _, zero_ms in oracle_items):
                    nonzero_failed = True

        unit_items = [(idx, zero_ms) for idx, is_orac, zero_ms in items if not is_orac]
        if unit_items:
            self._install_heavy_hooks(slice_map, flags, bool(fixtures.files))
            nonzero_units = [idx for idx, zero_ms in unit_items if not zero_ms]
            zero_units = [idx for idx, zero_ms in unit_items if zero_ms]
            zero_set = frozenset(zero_units)

            def _run_batch(batch_indices):
                cases = {}
                safe_types = set()
                for idx in batch_indices:
                    path, cls_name, name = self.nodes[idx]
                    case_type = getattr(sys.modules[module_name(path)], cls_name)
                    if issubclass(case_type, unittest.TestCase) and callable(getattr(case_type, name, None)):
                        leaf = case_type(name)
                        _wrap_call_test_method(leaf)
                        cases[leaf] = idx
                        if _has_trivial_teardown(case_type):
                            safe_types.add(case_type)
                if not cases:
                    return None
                res = _HeavyStreamResult(
                    cases, fixtures, is_bypassed, checkpoint_readers,
                    emit_pass, emit_abort, safe_types, zero_indices=zero_set, all_mask=index.all,
                )
                unittest.TestSuite(cases).run(res)
                teardown_readers = checkpoint_readers()
                if res.aborted or is_bypassed() or fixtures.unfaithful:
                    emit_abort()
                    res.aborted = True
                    return res
                if res.readers_overflow or (index.all and teardown_readers == index.all):
                    res.readers_overflow = True
                    return res
                for b_idx, b_readers in res.buffered_passes:
                    emit_pass(b_idx, b_readers | teardown_readers)
                if teardown_readers:
                    emit_line(f"R {teardown_readers:x}\n")
                return res

            aborted = False
            if nonzero_units:
                res = _run_batch(nonzero_units)
                if res is None:
                    nonzero_failed = True
                else:
                    aborted = res.aborted
                    if res.nonzero_failed or res.readers_overflow or len(res.indices) < len(nonzero_units):
                        nonzero_failed = True
            if zero_units and not nonzero_failed and not aborted:
                _run_batch(zero_units)

    def verify_heavy(self, index, changes, items, watch, hot, deadline, cap, flags,
                     slice_map=None, dialect_map=None):
        """Stream passed test indices and watched reader masks from one warm fork."""
        if not self.ready or not items:
            return 0, 0
        return fork_masks_stream(
            lambda write_fd: self._execute_heavy(
                index, changes, items, set(watch), hot, flags,
                slice_map or {}, dialect_map or {}, write_fd,
            ),
            deadline,
            cap,
        )

    def verify_tpcds_phase1(self, changes, hot, baseline_sigs, deadline, cap,
                            indices=None, max_mismatches=10):
        """Run structural TPC-DS Phase 1 inside a warm fork against cached baseline digests."""
        if not self.ready or not baseline_sigs or cap <= 0 or monotonic() >= deadline:
            return False, []

        def _run_p1(write_fd):
            import slicer
            fixtures, is_bypassed = self._prepare_child(changes, hot, needed_modules=("tests.helpers",))
            ok, mismatched = slicer.compute_tpcds_mismatches(
                baseline_sigs, indices=indices, max_mismatches=max_mismatches,
            )
            if (
                not ok
                or is_bypassed()
                or fixtures.unfaithful
                or (fixtures.files and not (fixtures.files.keys() <= fixtures.seen))
            ):
                os.write(write_fd, b"ERR\n")
                return
            payload = ",".join(str(i) for i in mismatched)
            os.write(write_fd, f"OK {payload}\n".encode())

        line = fork_reply_line(_run_p1, deadline, cap)
        if line is None or not line.startswith("OK"):
            return False, []
        rest = line[2:].strip()
        if not rest:
            return True, []
        try:
            return True, [int(x) for x in rest.split(",") if x]
        except ValueError:
            return False, []


def fork_reply_line(run_write, deadline, cap):
    """Run ``run_write(write_fd)`` in a bounded fork and return its single reply line or None."""
    if cap <= 0 or monotonic() >= deadline:
        return None
    read_fd, write_fd = os.pipe()
    try:
        cpu_start = cgroup_cpu()
        pid = os.fork()
    except OSError:
        os.close(read_fd)
        os.close(write_fd)
        return None
    if pid == 0:
        try:
            os.close(read_fd)
            os.setpgid(0, 0)
            quiet()
            signal.signal(signal.SIGPROF, signal.SIG_DFL)
            signal.setitimer(signal.ITIMER_PROF, cap)
            cpu_lim = max(5, int(cap) + 2)
            resource.setrlimit(resource.RLIMIT_CPU, (cpu_lim, cpu_lim))
            limit_child_resources(CHILD_ADDRESS_SPACE)
            run_write(write_fd)
        except BaseException:
            os._exit(1)
        os._exit(0)
    os.close(write_fd)
    try:
        try:
            os.setpgid(pid, pid)
        except ProcessLookupError:
            return None
        pid_fd = os.pidfd_open(pid)
        try:
            end = min(deadline, monotonic() + cap + 1)
            while True:
                left = end - monotonic()
                if left <= 0:
                    return None
                done = select.select([pid_fd], [], [], min(left, 0.05))[0]
                if cpu_start is not None:
                    cpu_now = cgroup_cpu()
                    if cpu_now is None or cpu_now - cpu_start >= cap:
                        return None
                if done:
                    break
        finally:
            os.close(pid_fd)
        status = os.waitid(os.P_PID, pid, os.WEXITED | os.WNOWAIT)
        if status.si_code != os.CLD_EXITED or status.si_status != 0:
            return None
        os.set_blocking(read_fd, False)
        reply = os.read(read_fd, 65536).decode("utf-8", errors="replace").strip()
        return reply
    except (OSError, ValueError):
        return None
    finally:
        os.close(read_fd)
        reap_group(pid)


def fork_masks_stream(run_write, deadline, cap):
    """Run ``run_write(write_fd)`` in a bounded fork, streaming ``P <idx> <readers:x>``."""
    if cap <= 0 or monotonic() >= deadline:
        return 0, 0
    read_fd, write_fd = os.pipe()
    try:
        cpu_start = cgroup_cpu()
        pid = os.fork()
    except OSError:
        os.close(read_fd)
        os.close(write_fd)
        return 0, 0
    if pid == 0:
        try:
            os.close(read_fd)
            os.setpgid(0, 0)
            quiet()
            signal.signal(signal.SIGPROF, signal.SIG_DFL)
            signal.setitimer(signal.ITIMER_PROF, cap + 0.5)
            cpu_lim = max(5, int(cap) + 3)
            resource.setrlimit(resource.RLIMIT_CPU, (cpu_lim, cpu_lim))
            limit_child_resources(CHILD_ADDRESS_SPACE)
            run_write(write_fd)
        except BaseException:
            try:
                os.write(write_fd, b"ABORT\n")
            except OSError:
                pass
            os._exit(1)
        os._exit(0)
    os.close(write_fd)
    try:
        try:
            os.setpgid(pid, pid)
        except ProcessLookupError:
            return 0, 0
        os.set_blocking(read_fd, False)
        pid_fd = os.pidfd_open(pid)
        passed = 0
        readers = 0
        aborted = False
        buf = bytearray()

        def _drain_lines():
            nonlocal passed, readers, aborted
            while b"\n" in buf:
                pos = buf.index(b"\n")
                raw_line = bytes(buf[:pos]).decode("utf-8", errors="replace").strip()
                del buf[:pos + 1]
                if not raw_line:
                    continue
                if raw_line == "ABORT":
                    aborted = True
                    passed = 0
                    return False
                parts = raw_line.split()
                if parts[0] == "P" and len(parts) == 3:
                    try:
                        idx = int(parts[1])
                        r_mask = int(parts[2], 16)
                        passed |= 1 << idx
                        readers |= r_mask
                    except ValueError:
                        pass
                elif parts[0] == "R" and len(parts) == 2:
                    try:
                        readers |= int(parts[1], 16)
                    except ValueError:
                        pass
            return True

        def _drain_pipe():
            while True:
                try:
                    chunk = os.read(read_fd, 4096)
                except BlockingIOError:
                    break
                except OSError:
                    break
                if not chunk:
                    break
                buf.extend(chunk)
            return _drain_lines()

        try:
            end = min(deadline, monotonic() + cap + 1)
            earned_at_cutoff = None
            while True:
                if not _drain_pipe():
                    return 0, 0
                left = end - monotonic()
                if cpu_start is not None:
                    cpu_now = cgroup_cpu()
                    if cpu_now is None:
                        return 0, 0
                    if cpu_now - cpu_start >= cap:
                        left = 0
                if left <= 0:
                    # A child can have faulted after its last receipt while the
                    # parent was sampling CPU. Always classify the actual exit.
                    if not _drain_pipe():
                        return 0, 0
                    earned_at_cutoff = passed
                    try:
                        os.kill(pid, signal.SIGPROF)
                    except ProcessLookupError:
                        pass
                    if not select.select([pid_fd], [], [], 0.05)[0]:
                        return 0, 0
                    break
                ready = select.select([read_fd, pid_fd], [], [], min(left, 0.05))[0]
                if pid_fd in ready:
                    break
            status = os.waitid(os.P_PID, pid, os.WEXITED | os.WNOWAIT)
            if not _drain_pipe():
                return 0, 0
            clean_exit = (status.si_code == os.CLD_EXITED and status.si_status == 0)
            prof_timeout = (status.si_code == os.CLD_KILLED and status.si_status == signal.SIGPROF)
            if not (clean_exit or prof_timeout) or aborted:
                return 0, 0
            if earned_at_cutoff is not None:
                passed &= earned_at_cutoff
            return passed, readers
        finally:
            os.close(pid_fd)
    except (OSError, ValueError):
        return 0, 0
    finally:
        os.close(read_fd)
        reap_group(pid)


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
            cpu_lim = max(5, int(cap) + 2)
            resource.setrlimit(resource.RLIMIT_CPU, (cpu_lim, cpu_lim))
            limit_child_resources(CHILD_ADDRESS_SPACE)
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


def runnable(test_id, *, inline_pool=False, setupclass_deamort=False):
    parts = test_id.split("::")
    if len(parts) != 3:
        return False
    path, _, method = parts
    if path == "tests/test_sqlglotc.py":
        return False
    if path == "tests/test_optimizer.py" and not inline_pool:
        return False
    if path == "tests/test_executor.py" and method in ("test_execute_tpch", "test_execute_tpcds"):
        return bool(inline_pool and setupclass_deamort)
    if method == "test_generator_memory":
        return False
    return True


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
