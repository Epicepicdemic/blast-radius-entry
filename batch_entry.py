"""Read the batch inventory and keep the output usable if selector startup fails."""
from contextlib import suppress
import json
import os
from pathlib import Path
from time import monotonic


def main():
    started = monotonic()
    with os.fdopen(os.dup(1), "w", encoding="utf-8") as output:
        os.dup2(2, 1)  # Imports may write to stdout.
        run_batch(output, Path("/sqlglot"), Path("/data"), started)


def run_batch(output, root, data, started):
    patches = sorted((data / "commits").glob("*.patch"))
    if not patches:
        return
    tests = numbers = full_plan = None
    try:
        tests = json.loads((data / "tests.json").read_bytes())["tests"]
        if not isinstance(tests, list):
            raise ValueError("invalid test inventory")
        numbered = [test["number"] for test in tests]
        if any(type(n) is not int or n < 0 for n in numbered) or len(set(numbered)) != len(tests):
            raise ValueError("invalid test numbers")
        numbers = numbered
        from packing import pack
        durations = {t["number"]: round(t["seconds"] * 1000) for t in tests}
        ranked = sorted(durations, key=lambda t: (-durations[t], t))
        full_plan = pack(set(ranked), ranked, durations)
        # Native libraries can size thread pools from host affinity despite the quota.
        if hasattr(os, "sched_getaffinity"):
            allowed = sorted(os.sched_getaffinity(0))
            if len(allowed) > 2:
                os.sched_setaffinity(0, allowed[:2])
        from bounded_batch import bounded_results
        from selector import prepare_batch
        analyze, plan_for, deadline = prepare_batch(root, patches, tests, ranked, durations, full_plan, started)
    except Exception:
        if full_plan is None:
            # The kit numbers tests from zero without gaps. Keep a separate build-time
            # count from the pinned suite for an unreadable runtime manifest.
            if numbers is None:
                count = len(tests) if isinstance(tests, list) else int(Path(__file__).with_name("test-count").read_text())
                numbers = range(count)
            full_plan = [list(numbers[i::8]) for i in range(min(len(numbers), 8))]
        encoded = json.dumps(full_plan, separators=(",", ":"))
        for path in patches:
            write_plan(output, path, encoded)
        return

    # Drive output from the input inventory, even if the analysis worker stops.
    full_json = json.dumps(full_plan, separators=(",", ":"))
    results = None
    for offset, path in enumerate(patches):
        try:
            if results is None:
                results = bounded_results(patches[offset:], analyze, deadline)
            analyzed, result = next(results)
            if analyzed != path:
                raise ValueError("analysis result is out of order")
            workers = plan_for(path, result)
            encoded = full_json if workers is full_plan else json.dumps(workers, separators=(",", ":"))
        except Exception:
            encoded = full_json
            if results is not None:
                with suppress(Exception):
                    results.close()
                results = None
        write_plan(output, path, encoded)
    if results is not None:
        with suppress(Exception):
            results.close()


def write_plan(output, path, encoded):
    output.write('{"commit":' + json.dumps(path.stem) + ',"workers":' + encoded + '}\n')
