"""Run outside the entry image. KIT is the unpacked official sample download."""
import argparse
from collections import defaultdict
from functools import lru_cache
import importlib.util
import json
from pathlib import Path
import shutil


def oracle(times):
    """Exact minimum cost, using an LPT upper bound and a feasibility search."""
    if not times:
        return 0
    jobs = sorted((t for t in times if t), reverse=True)
    if not jobs:
        return 2000
    total = sum(jobs)
    best = total + 2000
    for count in range(2, min(8, len(jobs)) + 1):
        fee = 2000 * count
        low = max(jobs[0], (total + count - 1) // count)
        if low + fee >= best:
            continue
        loads = [0] * count
        for t in jobs:
            loads[loads.index(min(loads))] += t
        high = min(max(loads), best - fee)
        while low < high:
            middle = (low + high) // 2

            @lru_cache(None)
            def fits(i, free):
                if i == len(jobs):
                    return True
                for j, room in enumerate(free):
                    if room < jobs[i] or (j and free[j - 1] == room):
                        continue
                    new = list(free)
                    new[j] -= jobs[i]
                    if fits(i+1, tuple(sorted(new))):
                        return True
                return False

            if fits(0, (middle,) * count):
                high = middle
            else:
                low = middle + 1
            fits.cache_clear()
        best = min(best, high + fee)
    return best


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("kit", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--folds", type=Path, help="prepare per-kind input directories for isolated reruns")
    parser.add_argument("--held-out", help="score only this kind, from its separate run")
    args = parser.parse_args()
    data = args.kit / "sample"
    tests = json.loads((data / "tests.json").read_bytes())["tests"]
    answers = json.loads((data / "answers.json").read_bytes())["commits"]
    assert set(answers) == {p.stem for p in (data / "commits").glob("*.patch")}
    if args.held_out:
        answers = {k: v for k, v in answers.items() if v["kind"] == args.held_out}
        assert answers
    stdout = args.output.read_bytes()
    assert len(stdout) <= 2_000_000
    spec = importlib.util.spec_from_file_location("official", args.kit / "score.py")
    kit = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(kit)
    result = kit.evaluate_run(stdout, tests, answers)
    if not result["ok"]:
        raise SystemExit(result)
    rows = {v["commit"]: v["workers"] for v in map(json.loads, stdout.splitlines())}
    ms = {t["number"]: round(t["seconds"] * 1000) for t in tests}
    zero = {n for n, t in ms.items() if t == 0}
    costs = defaultdict(int)
    optimal = defaultdict(int)
    for name, answer in sorted(answers.items()):
        workers = [w for w in rows[name] if w]
        selected = {n for w in workers for n in w}
        assert not workers or zero <= selected
        failed = set(answer["failing"]) - selected
        cost = (max((sum(ms[n] for n in w) for w in workers), default=0)
                + 2000 * len(workers) + 300000 * bool(failed))
        minimum = oracle([ms[n] for n in answer["failing"]])
        kind = answer["kind"]
        costs[kind] += cost
        optimal[kind] += minimum
        if not args.held_out:
            print(f"{name} {kind:8} {len(selected):4} tests  {cost/1000:7.3f} s  "
                  f"oracle {minimum/1000:6.3f} s  gap {(cost-minimum)/1000:6.3f} s  "
                  f"missed {sorted(failed)}")
        if args.folds:
            directory = args.folds / kind
            directory.mkdir(exist_ok=True, parents=True)
            shutil.copyfile(data / "commits" / (name + ".patch"), directory / (name + ".patch"))
    total = sum(costs.values())
    assert total == result["simulated_milliseconds"]
    print(f"{args.held_out or 'all'}: {len(rows)} commits, {len(result['missed_commits'])} misses, "
          f"{total/1000:.3f} s simulated, {sum(optimal.values())/1000:.3f} s oracle.")
    if result["missed_commits"]:
        raise SystemExit(f"Missed commits: {result['missed_commits']}")


if __name__ == "__main__":
    main()
