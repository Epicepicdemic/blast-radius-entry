#!/usr/bin/env bash
set -euo pipefail
# The sample kit is fetched by the host evaluator, outside the Docker build.
mkdir -p scratch
work=$(mktemp -d "$PWD/scratch/verify.XXXXXX")
if [ -n "${KIT:-}" ]; then
    kit=$(cd "$KIT" && pwd)
else
    kit=$work/kit
    mkdir "$kit"
    curl -fsSL https://www.joinbuilders.org/buildathon/tracks/blast-radius/files/blast-radius-sample.tar.gz -o "$work/kit.tgz"
    python3 - "$work/kit.tgz" <<'PY'
import hashlib, pathlib, sys
assert hashlib.sha256(pathlib.Path(sys.argv[1]).read_bytes()).hexdigest() == "81efabbc69c3c4367d928f2dba0f33ce9dccccbd080b54721b2636e5d8afab9d"
PY
    tar xzf "$work/kit.tgz" -C "$kit"
fi
python3 - "$kit/sample/tests.json" <<'PY'
import json, sys
maps = json.load(open("maps.json"))
manifest = json.load(open(sys.argv[1]))
assert set(maps["ids"]) == {t["id"] for t in manifest["tests"]}
assert set(maps["skipped"]) == set(manifest["skipped"])
print("Baseline matched test inventory:", len(maps["ids"]), "passing,", len(maps["skipped"]), "skipped")
PY
start=$SECONDS
timeout 600 docker build --no-cache --platform linux/amd64 -t br-entry .
echo "Clean entry build took $((SECONDS-start)) s"
flags=(--rm --platform linux/amd64 --network none --cpus 2 --memory 4096m --memory-swap 4096m
       --pids-limit 256 --read-only --tmpfs /tmp:rw,size=64m,mode=1777 --cap-drop ALL
       --security-opt no-new-privileges --user 65534:65534 --env HOME=/tmp
       --volume "$kit/sample/tests.json:/data/tests.json:ro")
run() {
    local patches=$1
    shift
    timeout 180 docker run "${flags[@]}" --volume "$patches:/data/commits:ro" br-entry "$@"
}
run "$kit/sample/commits" > "$work/output.jsonl"
python3 "$kit/score.py" "$kit/sample" "$kit/sample/answers.json" "$work/output.jsonl"
python3 tools/report.py "$kit" "$work/output.jsonl" --folds "$work/folds"
for fold in "$work"/folds/*; do
    run "$fold" > "$fold.jsonl"
    python3 tools/report.py "$kit" "$fold.jsonl" --held-out "$(basename "$fold")"
done
# Fresh cgroups; the shell's read of cpu.stat after the selector exits includes
# interpreter startup, shutdown and all descendants. It also includes the shell.
for i in 1 2 3; do
    run "$kit/sample/commits" sh -ec 'python /app/selector.py; cat /sys/fs/cgroup/cpu.stat >&2' \
        > "$work/timed-$i.jsonl" 2> "$work/cpu-$i.txt"
    cmp "$work/output.jsonl" "$work/timed-$i.jsonl"
    awk '$1 == "usage_usec" {seen=1; printf "Container CPU: %.6f s\n", $2/1000000; if ($2 <= 0) exit 1}
         END {if (!seen) exit 1}' "$work/cpu-$i.txt"
done
