"""Warm-forked subprocess verifier and symlink-overlay helper for Line B."""
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile


TPCDS_TEST_ID = "tests/test_executor.py::TestExecutor::test_execute_tpcds"
SLOW_UNITTEST_FILES = (
    "tests/test_executor.py",
    "tests/test_optimizer.py",
    "tests/test_sqlglotc.py",
)
TPCDS_BACKEND_PREFIXES = (
    "sqlglot/executor/",
    "sqlglot/expressions/",
    "tests/",
)
TPCDS_BACKEND_FILES = frozenset({
    "sqlglot/planner.py",
    "sqlglot/schema.py",
    "sqlglot/helper.py",
    "sqlglot/generator.py",
    "sqlglot/errors.py",
    "sqlglot/serde.py",
})


_WORKER_CODE = r'''
import hashlib
import io
import json
import os
import pickle
import signal
import sys
import unittest

import dateutil
import mypy_extensions
import pytz
import typing_extensions


def _run_unittest(ov, nodes, timeout_s):
    r_fd, w_fd = os.pipe()
    pid = os.fork()
    if pid == 0:
        os.close(r_fd)
        devnull = os.open(os.devnull, os.O_WRONLY)
        os.dup2(devnull, 1)
        os.dup2(devnull, 2)
        os.close(devnull)
        os.environ["SKIP_INTEGRATION"] = "0"
        sys.dont_write_bytecode = True
        os.chdir(ov)
        sys.path[:] = [ov] + [p for p in sys.path if p != "/sqlglot"]
        ok = False
        try:
            loader = unittest.TestLoader()
            suite = unittest.TestSuite([loader.loadTestsFromName(n) for n in nodes])
            if suite.countTestCases() == len(nodes):
                res = unittest.TextTestRunner(stream=io.StringIO(), failfast=True).run(suite)
                ok = (
                    res.wasSuccessful()
                    and res.testsRun == len(nodes)
                    and not res.skipped
                    and not res.expectedFailures
                    and not res.unexpectedSuccesses
                )
        except BaseException:
            ok = False
        os.write(w_fd, b"1" if ok else b"0")
        os.close(w_fd)
        os._exit(0 if ok else 1)

    os.close(w_fd)
    timed_out = False

    def _on_alarm(signum, frame):
        nonlocal timed_out
        timed_out = True
        try:
            os.kill(pid, signal.SIGKILL)
        except OSError:
            pass

    old_handler = signal.signal(signal.SIGALRM, _on_alarm)
    signal.alarm(max(1, int(timeout_s)))
    data = b""
    try:
        while True:
            try:
                chunk = os.read(r_fd, 16)
            except InterruptedError:
                if timed_out:
                    break
                continue
            if not chunk:
                break
            data += chunk
    finally:
        signal.alarm(0)
        signal.signal(signal.SIGALRM, old_handler)
        os.close(r_fd)
        try:
            _, status = os.waitpid(pid, 0)
        except OSError:
            status = 1
    return (not timed_out) and data == b"1" and os.WIFEXITED(status) and os.WEXITSTATUS(status) == 0


_TPCDS_HARNESS = r"""
import hashlib, pickle
from sqlglot import find_tables, parse_one, transpile
from sqlglot.executor.python import PythonExecutor
from sqlglot.executor.table import ensure_tables, Table
from sqlglot.optimizer import optimize
from sqlglot.planner import Plan
from sqlglot.schema import ensure_schema
from tests.helpers import TPCDS_SCHEMA, load_sql_fixture_pairs

_SQLS = list(load_sql_fixture_pairs("optimizer/tpc-ds/tpc-ds.sql"))
_SCHEMA_CACHE = ensure_schema(TPCDS_SCHEMA)

def _hash_step_tree(root, pe, out_h):
    memo = {}

    def expr_repr(e):
        if e is None:
            return b"None"
        return repr(e).encode()

    def step_bytes(s):
        sid = id(s)
        if sid in memo:
            return memo[sid]
        sh = hashlib.blake2b(digest_size=16)
        sh.update(repr((s.type_name, s.name, s.limit, s.offset)).encode())
        sh.update(repr((getattr(s, "source_name", None), getattr(s, "left", None), getattr(s, "right", None), getattr(s, "distinct", None))).encode())
        src = getattr(s, "source", None)
        if isinstance(src, str) or src is None:
            sh.update(repr(src).encode())
        else:
            sh.update(expr_repr(src))
        sh.update(expr_repr(getattr(s, "condition", None)))
        for seq_attr in ("projections", "aggregations", "operands", "key"):
            seq = getattr(s, seq_attr, None)
            sh.update(seq_attr.encode())
            if seq:
                for item in seq:
                    sh.update(expr_repr(item))
        grp = getattr(s, "group", None)
        if grp:
            for gk in sorted(grp):
                sh.update(gk.encode() + b"=" + expr_repr(grp[gk]))
        jns = getattr(s, "joins", None)
        if jns:
            for jname in sorted(jns):
                j = jns[jname]
                sh.update(jname.encode() + repr(j.get("side")).encode())
                sh.update(expr_repr(j.get("condition")))
                for jk in j.get("source_key", ()):
                    sh.update(b"sk:" + expr_repr(jk))
                for jk in j.get("join_key", ()):
                    sh.update(b"jk:" + expr_repr(jk))
        dep_pairs = sorted((step_bytes(d), d) for d in s.dependencies)
        for db, _ in dep_pairs:
            sh.update(b"dep:" + db)
        res = sh.digest()
        memo[sid] = res
        return res

    out_h.update(step_bytes(root))

    def walk_exec(s):
        cond = getattr(s, "condition", None)
        if cond is not None:
            out_h.update(pe.generator.generate(pe._replace_subqueries(cond)).encode())
        for lst_attr in ("projections", "aggregations", "operands", "key"):
            items = getattr(s, lst_attr, None)
            if items:
                for item in items:
                    out_h.update(pe.generator.generate(pe._replace_subqueries(item)).encode())
        grp = getattr(s, "group", None)
        if grp:
            for gk in sorted(grp):
                out_h.update(pe.generator.generate(pe._replace_subqueries(grp[gk])).encode())
        jns = getattr(s, "joins", None)
        if jns:
            for jname in sorted(jns):
                j = jns[jname]
                if j.get("condition") is not None:
                    out_h.update(pe.generator.generate(pe._replace_subqueries(j["condition"])).encode())
                for jk in j.get("source_key", ()):
                    out_h.update(pe.generator.generate(pe._replace_subqueries(jk)).encode())
                for jk in j.get("join_key", ()):
                    out_h.update(pe.generator.generate(pe._replace_subqueries(jk)).encode())
        for _, d in sorted(((memo[id(dep)], dep) for dep in s.dependencies), key=lambda x: x[0]):
            walk_exec(d)

    walk_exec(root)

def query_sig(idx):
    meta, sql, _ = _SQLS[idx]
    h = hashlib.blake2b(digest_size=16)
    h.update(transpile(sql, write="duckdb")[0].encode())
    expr = parse_one(sql)
    expr2 = pickle.loads(pickle.dumps(expr))
    h.update(repr(expr2).encode())
    tlist = [t.name for t in find_tables(expr)]
    h.update(repr(tlist).encode())
    if meta.get("execute"):
        dummy = {t: Table(columns=tuple(TPCDS_SCHEMA[t].keys()), rows=[]) for t in tlist if t in TPCDS_SCHEMA}
        tables_ = ensure_tables(dummy)
        schema = ensure_schema(TPCDS_SCHEMA)
        h.update(repr(tables_.supported_table_args).encode())
        h.update(repr(schema.supported_table_args).encode())
        opt = optimize(expr2, schema, leave_tables_isolated=True)
        h.update(opt.sql().encode())
        h.update(repr(opt).encode())
        plan = Plan(opt)
        pe = PythonExecutor(tables=tables_)
        _hash_step_tree(plan.root, pe, h)
        seen_subs = set()
        while True:
            pending = sorted(k for k in pe._subquery_plans if k not in seen_subs)
            if not pending:
                break
            for k in pending:
                seen_subs.add(k)
                h.update(k.encode())
                _hash_step_tree(pe._subquery_plans[k].root, pe, h)
    return h.digest()
"""


class _BaselineServer:
    def __init__(self):
        self.cache = {}
        self.proc = None
        self.to_child = None
        self.from_child = None

    def _ensure(self):
        if self.proc is not None:
            return
        in_r, in_w = os.pipe()
        out_r, out_w = os.pipe()
        pid = os.fork()
        if pid == 0:
            os.close(in_w)
            os.close(out_r)
            devnull = os.open(os.devnull, os.O_WRONLY)
            os.dup2(devnull, 1)
            os.dup2(devnull, 2)
            os.close(devnull)
            sys.dont_write_bytecode = True
            os.chdir("/sqlglot")
            sys.path.insert(0, "/sqlglot")
            ns = {}
            try:
                exec(_TPCDS_HARNESS, ns)
                fn = ns["query_sig"]
                n_total = len(ns["_SQLS"])
                os.write(out_w, f"{n_total}\n".encode())
                fin = os.fdopen(in_r, "r")
                fout = os.fdopen(out_w, "wb")
                for line in fin:
                    idx = int(line.strip())
                    try:
                        sig = fn(idx).hex().encode() + b"\n"
                    except BaseException:
                        sig = b"ERR\n"
                    fout.write(sig)
                    fout.flush()
            except BaseException:
                pass
            os._exit(0)
        os.close(in_r)
        os.close(out_w)
        self.proc = pid
        self.to_child = os.fdopen(in_w, "w")
        self.from_child = os.fdopen(out_r, "r")
        self.n_queries = int(self.from_child.readline().strip())

    def get(self, idx):
        if idx in self.cache:
            return self.cache[idx]
        self._ensure()
        self.to_child.write(f"{idx}\n")
        self.to_child.flush()
        val = self.from_child.readline().strip()
        self.cache[idx] = val
        return val

    def close(self):
        if self.proc is not None:
            try:
                self.to_child.close()
                self.from_child.close()
                os.waitpid(self.proc, 0)
            except OSError:
                pass
            self.proc = None


_BASELINE = _BaselineServer()


def _run_tpcds_frontend(ov, timeout_s):
    try:
        _BASELINE._ensure()
    except BaseException:
        return False
    n_total = _BASELINE.n_queries
    r_fd, w_fd = os.pipe()
    pid = os.fork()
    if pid == 0:
        os.close(r_fd)
        devnull = os.open(os.devnull, os.O_WRONLY)
        os.dup2(devnull, 1)
        os.dup2(devnull, 2)
        os.close(devnull)
        sys.dont_write_bytecode = True
        os.chdir(ov)
        sys.path[:] = [ov] + [p for p in sys.path if p != "/sqlglot"]
        fout = os.fdopen(w_fd, "w")
        try:
            ns = {}
            exec(_TPCDS_HARNESS, ns)
            fn = ns["query_sig"]
            if len(ns["_SQLS"]) != n_total:
                fout.write("ERR\n")
                fout.flush()
                os._exit(1)
            for idx in range(n_total):
                sig = fn(idx).hex()
                fout.write(sig + "\n")
                fout.flush()
        except BaseException:
            try:
                fout.write("ERR\n")
                fout.flush()
            except BaseException:
                pass
            os._exit(1)
        os._exit(0)

    os.close(w_fd)
    timed_out = False

    def _on_alarm(signum, frame):
        nonlocal timed_out
        timed_out = True
        try:
            os.kill(pid, signal.SIGKILL)
        except OSError:
            pass

    old_handler = signal.signal(signal.SIGALRM, _on_alarm)
    signal.alarm(max(1, int(timeout_s)))
    matched = 0
    fin = os.fdopen(r_fd, "r")
    try:
        for idx in range(n_total):
            line = fin.readline()
            if not line:
                break
            psig = line.strip()
            bsig = _BASELINE.get(idx)
            if psig == "ERR" or bsig == "ERR" or psig != bsig:
                try:
                    os.kill(pid, signal.SIGKILL)
                except OSError:
                    pass
                break
            matched += 1
    except BaseException:
        try:
            os.kill(pid, signal.SIGKILL)
        except OSError:
            pass
    finally:
        signal.alarm(0)
        signal.signal(signal.SIGALRM, old_handler)
        fin.close()
        try:
            _, status = os.waitpid(pid, 0)
        except OSError:
            status = 1
    return (not timed_out) and matched == n_total and os.WIFEXITED(status) and os.WEXITSTATUS(status) == 0


for raw_line in sys.stdin:
    req = json.loads(raw_line)
    mode = req["mode"]
    if mode == "quit":
        break
    if mode == "unittest":
        ok = _run_unittest(req["ov"], req["nodes"], req["timeout"])
    elif mode == "tpcds":
        ok = _run_tpcds_frontend(req["ov"], req["timeout"])
    else:
        ok = False
    sys.stdout.write("1\n" if ok else "0\n")
    sys.stdout.flush()

_BASELINE.close()
'''


def _to_dotted_node(test_id):
    if "::" not in test_id:
        return test_id[:-3].replace("/", ".")
    path_part, *rest = test_id.split("::")
    return path_part[:-3].replace("/", ".") + "." + ".".join(rest)


class LiveRunner:
    def __init__(self, root=Path("/sqlglot")):
        self.root = Path(root)
        self._proc = None

    def _ensure_proc(self):
        if self._proc is None:
            env = {
                "PATH": os.environ.get("PATH", "/usr/local/bin:/usr/bin:/bin"),
                "HOME": "/tmp",
                "SKIP_INTEGRATION": "0",
                "OPENBLAS_NUM_THREADS": "1",
                "OMP_NUM_THREADS": "1",
                "PYTHONDONTWRITEBYTECODE": "1",
            }
            self._proc = subprocess.Popen(
                [sys.executable, "-B", "-c", _WORKER_CODE],
                stdin=subprocess.PIPE,
                stdout=subprocess.PIPE,
                stderr=subprocess.DEVNULL,
                text=True,
                env=env,
            )

    def _make_overlay(self, changes):
        ov = Path(tempfile.mkdtemp(prefix="br_ov_", dir="/tmp"))
        for entry in self.root.iterdir():
            os.symlink(entry, ov / entry.name)
        for change in changes:
            parts = Path(change.path).parts
            cur = ov
            for part in parts[:-1]:
                nxt = cur / part
                if nxt.is_symlink():
                    orig = nxt.resolve()
                    nxt.unlink()
                    nxt.mkdir()
                    for child in orig.iterdir():
                        os.symlink(child, nxt / child.name)
                cur = nxt
            tgt = cur / parts[-1]
            if tgt.is_symlink() or tgt.exists():
                tgt.unlink()
            tgt.write_bytes(change.after)
        return ov

    def verify_unittest(self, changes, test_ids, timeout_s=8):
        if not test_ids:
            return True
        self._ensure_proc()
        ov = self._make_overlay(changes)
        try:
            req = {
                "mode": "unittest",
                "ov": str(ov),
                "nodes": [_to_dotted_node(tid) for tid in test_ids],
                "timeout": timeout_s,
            }
            self._proc.stdin.write(json.dumps(req) + "\n")
            self._proc.stdin.flush()
            resp = self._proc.stdout.readline().strip()
            return resp == "1"
        except Exception:
            self.close()
            return False
        finally:
            shutil.rmtree(ov, ignore_errors=True)

    def verify_tpcds_frontend(self, changes, timeout_s=20):
        self._ensure_proc()
        ov = self._make_overlay(changes)
        try:
            req = {"mode": "tpcds", "ov": str(ov), "timeout": timeout_s}
            self._proc.stdin.write(json.dumps(req) + "\n")
            self._proc.stdin.flush()
            resp = self._proc.stdout.readline().strip()
            return resp == "1"
        except Exception:
            self.close()
            return False
        finally:
            shutil.rmtree(ov, ignore_errors=True)

    def close(self):
        if self._proc is not None:
            try:
                if self._proc.poll() is None and self._proc.stdin is not None:
                    self._proc.stdin.write('{"mode":"quit"}\n')
                    self._proc.stdin.flush()
                    self._proc.stdin.close()
                self._proc.wait(timeout=2)
            except Exception:
                try:
                    self._proc.kill()
                except Exception:
                    pass
            finally:
                for pipe in (self._proc.stdin, self._proc.stdout):
                    if pipe is not None:
                        try:
                            pipe.close()
                        except Exception:
                            pass
            self._proc = None
