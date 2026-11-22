"""Write one result per input even if loading the bundle or the runtime inventory fails."""
import io
import json
import os
from pathlib import Path


def fallback(data, app, stream):
    from packing import pack
    try:
        tests = json.loads((data / "tests.json").read_bytes())["tests"]
        durations = {t["number"]: int(t["seconds"] * 1000 + 0.5) for t in tests}
        ranked = sorted(durations, key=lambda n: (-durations[n], n))
        workers = pack(set(ranked), ranked, durations)
    except (OSError, ValueError, TypeError, KeyError):
        numbers = range(int((app / "test-count").read_text()))
        workers = [list(numbers[i::8]) for i in range(min(len(numbers), 8))]
    encoded = json.dumps(workers, separators=(",", ":"))
    for path in sorted((data / "commits").glob("*.patch")):
        stream.write('{"commit":' + json.dumps(path.stem) + ',"workers":' + encoded + '}\n')


def main():
    if hasattr(os, "sched_getaffinity"):
        os.sched_setaffinity(0, sorted(os.sched_getaffinity(0))[:2])
    app = Path(__file__).resolve().parent
    data = Path("/data")
    with os.fdopen(os.dup(1), "w") as out:
        os.dup2(2, 1)
        try:
            from fast_select import run
            buffer = io.StringIO()
            run(buffer, Path("/sqlglot"), data, app)
        except Exception:
            fallback(data, app, out)
        else:
            out.write(buffer.getvalue())


if __name__ == "__main__":
    main()
