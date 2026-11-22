"""Supervise the released verifier lazily and charge its entire process tree to the request."""
import ctypes
import os
import signal
from contextlib import suppress
from multiprocessing import get_context
from pathlib import Path
from time import monotonic

# At most one live request is outstanding. Reserve two CPUs' possible usage between polls.
POLL_SECONDS = 0.025
GUARD_SECONDS = 0.18
MAX_CPU_SECONDS = 16.0
MAX_REPLY = 65536


def run_service(pipe, parent_end, root, paths, tests, ranked, durations, full, started, raw, bounds):
    parent_end.close()
    # Patch execution happens in a further fork. Only this trusted process owns the reply channel.
    os.register_at_fork(after_in_child=pipe.close)
    from bounded_batch import bounded_results
    from selector import prepare_batch

    analyze, resolve, deadline = prepare_batch(root, paths, tests, ranked, durations, full, started, precomputed=raw)

    def requests():
        nonlocal soft_end
        while True:
            try:
                raw = pipe.recv_bytes(128)
            except EOFError:
                return
            offset, soft_end, cutoff = raw.split()
            soft_end = float(soft_end)
            import live
            live.cpu_cutoff = float(cutoff)
            yield paths[int(offset)]

    def checkpoint(mask):
        # This is the release's complete static or post-import bound, before further verification.
        pipe.send_bytes(b"B" + format(mask, "x").encode("ascii"))

    soft_end = 0
    try:
        for path, result in bounded_results(requests(), analyze, deadline):
            try:
                upper, owed = bounds[path]
                workers = resolve(path, result, until=soft_end, checkpoint=checkpoint, upper=upper, owed=owed)
                numbers = [str(n) for group in workers for n in group]
                pipe.send_bytes(b"F" + " ".join(numbers).encode("ascii"))
            except (ValueError, OSError, RuntimeError, RecursionError, OverflowError, MemoryError):
                pipe.send_bytes(b"E")
    finally:
        pipe.close()


class LiveVerifier:
    def __init__(self, root, paths, tests, ranked, durations, full, started, mask_width, raw, bounds):
        self.mask_width = mask_width
        self.args = root, paths, tests, ranked, durations, full, started, raw, bounds
        self.process = self.pipe = None
        self.all_numbers = set(ranked)
        self.subreaper = False

    def start(self):
        if not self.subreaper:
            # A verifier grandchild may lead its own process group. Adopt it even if its parent dies.
            if ctypes.CDLL(None).prctl(36, 1, 0, 0, 0) != 0:
                raise OSError("cannot supervise verifier descendants")
            self.subreaper = True
        ctx = get_context("fork")
        self.pipe, child = ctx.Pipe()
        self.process = ctx.Process(target=run_service, args=(child, self.pipe, *self.args))
        try:
            self.process.start()
        finally:
            child.close()

    def close(self):
        if self.pipe is not None:
            self.pipe.close()
        if self.process is not None:
            if self.process.pid is not None:
                self.process.join(0.015)
                if self.process.is_alive():
                    self.process.kill()
                self.process.join()
            self.process.close()
        self.pipe = self.process = None
        # All static workers have joined before this service is opened. Only orphaned verifier
        # descendants can remain. Kill each generation and wait for its children to be adopted.
        if self.subreaper:
            children = Path("/proc/thread-self/children")
            while (pids := children.read_text().split()):
                for pid in map(int, pids):
                    with suppress(ProcessLookupError):
                        os.kill(pid, signal.SIGKILL)
                    with suppress(ChildProcessError):
                        os.waitpid(pid, 0)

    def request(self, offset, seconds, deadline, from_mask, keep):
        from verify import cgroup_cpu
        start = cgroup_cpu()
        if start is None:
            return keep, 0, "unmetered"
        stop = start + seconds - GUARD_SECONDS
        # Release sub-stages stop before the supervisor. A checkpoint survives a later timeout.
        wall = monotonic()
        soft_end = min(deadline - 0.15, wall + max(32.0, 2 * seconds))
        reason = "budget"
        try:
            if self.process is None:
                self.start()
            self.pipe.send_bytes(f"{offset} {soft_end} {stop - 0.20}".encode("ascii"))
            while monotonic() < deadline and (now := cgroup_cpu()) is not None and now < stop:
                if not self.pipe.poll(min(POLL_SECONDS, max(0, deadline - monotonic()))):
                    continue
                reply = self.pipe.recv_bytes(MAX_REPLY)
                if reply[:1] == b"B":
                    cap = int(reply[1:], 16)
                    if cap < 0 or cap.bit_length() > self.mask_width:
                        raise ValueError("invalid checkpoint")
                    keep = keep & from_mask(cap, True)
                elif reply[:1] == b"F":
                    final = {int(n) for n in reply[1:].split()}
                    if not final <= self.all_numbers:
                        raise ValueError("invalid verifier inventory")
                    keep = keep & final
                    reason = "verified"
                    break
                elif reply == b"E":
                    reason = "declined"
                    break
                else:
                    raise ValueError("unknown verifier reply")
        except (EOFError, ValueError, RuntimeError, OSError):
            reason = "service exit"
        if reason not in ("verified", "declined"):
            self.close()
        end = cgroup_cpu()
        return keep, (end-start if end is not None else seconds), reason


cpu_cutoff = None

def fork_allowance(cap):
    """Cooperatively stop the release's nested forks before the hard parent watchdog."""
    if cpu_cutoff is None:
        return cap
    from verify import cgroup_cpu
    now = cgroup_cpu()
    return 0 if now is None else min(cap, cpu_cutoff - now)
