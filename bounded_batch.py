"""Run patch analysis in a killable worker under one wall-clock deadline."""
import errno
import gc
import multiprocessing
import resource
from stat import S_ISREG
from time import monotonic

from patching import MAX_PATCH_BYTES

# Leave 30 seconds of the shorter kit limit for startup, output and shutdown.
BATCH_SECONDS = 150
COMMIT_SECONDS = 3


# Includes the warm interpreter's inherited mappings (about 395 MiB on amd64).
CHILD_ADDRESS_SPACE = 896 * 1024 * 1024


def limit_child_resources(limit):
    resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
    for inherited in resource.getrlimit(resource.RLIMIT_AS):
        if inherited != resource.RLIM_INFINITY:
            limit = min(limit, inherited)
    resource.setrlimit(resource.RLIMIT_AS, (limit, limit))


def _serve(channel, parent_channel, analyze):
    parent_channel.close()
    try:
        limit_child_resources(CHILD_ADDRESS_SPACE)
    except (ValueError, OSError):
        return  # A worker without an enforceable ceiling cannot supply evidence.
    # This child only analyzes syntax. Exclude the inherited suite from cyclic
    # collections while continuing to collect trees allocated by the worker.
    gc.freeze()
    while True:
        try:
            path = channel.recv()
        except EOFError:
            return
        try:
            result = analyze(path)
        except MemoryError:
            # Discard the worker and its partially populated caches. EOF widens
            # this patch, and bounded_results forks a fresh worker for the next.
            return
        except OSError as error:
            if error.errno == errno.ENOMEM:
                return
            result = None
        except (ValueError, SyntaxError, RecursionError, OverflowError):
            result = None
        channel.send(result)


def bounded_results(paths, analyze, deadline, per_commit=COMMIT_SECONDS):
    """Yield a bitset pair, or None for the precomputed full plan, for each input.

    The Linux entry forks only after loading trusted maps. The parent never
    parses a patch and can interrupt a native parser or a stuck Python loop.
    Each response is two small integers derived from the fixed test inventory.
    """
    context = multiprocessing.get_context("fork")
    process = channel = None

    def stop():
        nonlocal process, channel
        if process is not None:
            channel.close()
            if process.pid is not None:
                if process.is_alive():
                    process.kill()
                process.join()
            process.close()
            process = channel = None

    try:
        for path in paths:
            result = None
            until = min(monotonic() + per_commit, deadline)
            if monotonic() < until:
                try:
                    info = path.stat()
                    if S_ISREG(info.st_mode) and info.st_size <= MAX_PATCH_BYTES:
                        if process is None:
                            channel, child = context.Pipe()
                            process = context.Process(target=_serve, args=(child, channel, analyze),
                                                      daemon=True)
                            try:
                                process.start()
                            finally:
                                child.close()
                        channel.send(path)
                        if channel.poll(max(0, until - monotonic())):
                            result = channel.recv()
                        else:
                            stop()
                except (OSError, EOFError):
                    stop()
            yield path, result
    finally:
        stop()
