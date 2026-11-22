# Wave-5 SQLGlot test selector

Extract the overlay onto a clean archive of the team entry at `5d6d8aa`. The Docker build checks and links profiles from the original SQLGlot source at `eb11aec4be8cb2122afe713a4816662c3f0fb2fa`. The default command reads `tests.json` and `commits/*.patch` from the mounted data directory and emits one JSON worker plan per patch on stdout.

```sh
mkdir -p "$ENTRY"
git archive 5d6d8aa | tar -xf - -C "$ENTRY"
tar -xzf blast-entry-wave5.tar.gz -C "$ENTRY"
docker build --platform linux/amd64 -t blast-entry-wave5 "$ENTRY"
docker run --rm --platform linux/amd64 --read-only --network none \
  --user 65534:65534 --cpus 2 --memory 4g --pids-limit 256 --cap-drop ALL \
  --tmpfs /tmp:rw,size=64m,mode=1777 -v "$DATA:/data:ro" blast-entry-wave5
```

Use an empty directory for `ENTRY` and an absolute path for `DATA`. Test identities determine the mapping to the submitted inventory numbers. `W3_TRACE=1` writes diagnostic information to stderr.

## Selecting tests

The selector checks the old and new code, tracks the first execution that can diverge, and retains source readers, shared-state readers, and opaque worker contexts. A binding census covers imported names, wildcard imports, functions, async functions, classes and pattern bindings. Class creation can publish state through an inherited hook or a computed metaclass. The registration guard examines nested calls and both sides of an edit before applying cheaper selection rules. An isolated removal of an import can use the existing cold dialect and registry-reader bound.

Class field reads are attributed through the method resolution order. The selector distinguishes direct key and arity checks from reads of a whole table and follows inherited copies. Lexical ownership checks cover destructuring, loop targets, comprehensions, and aliases through object fields. A paired check can compare state after the same candidate writers execute on the original and patched code. Incomplete runs retain the original obligation. Worker packing uses measured test durations and the contest worker-start charge.

## Rebuilding the clean profiles

The collector runs inside the built image against its unmodified checkout. Its only host mount contains collector code. Collecting all profiles takes longer than building the image. From the extracted entry, run

```sh
python3 w5/profile/reproduce.py ./recollected --image blast-entry-wave5
```

Pass profile names after the output directory to collect a subset. Each compressed JSON file stores the pin's test identity order. The collector records successful full-suite or targeted pool coverage before emitting its output. The linker checks those identities before converting observations to masks. The earlier release notes describe the inherited pin profiles.

| Profile | Observation |
| --- | --- |
| `operands` | Runtime types in enum comparisons, scalar callback arguments, and entered test helpers |
| `operand_workers` | Operand and entry observations from acknowledged process-pool tasks, plus process starts |
| `observers` | Reads of function code, documentation, defaults, and other callable metadata |
| `write_shells` | Concrete receiver types and whether an object is reachable from project state across test boundaries |
| `field_uses` | Class field and namespace reads, optional expression arguments, exact membership checks, and arity |
| `dispatch_uses` | Dispatch keys consumed through concrete and inherited tables, including whole-table readers |
| `prefixes` | Reached operands in short-circuit and conditional expressions |
| `passive_ops` | User-defined operations, raised exceptions, constructor argument-binding errors, native copying behavior and lookup of existing tokenizer keywords |

Process-pool work can initialize dialect classes on different tasks across otherwise identical runs. The field profile records the task that observed each read. Unacknowledged tasks remain opaque. A wildcard receiver type means the collector exceeded its concrete-type cap. Concrete types listed alongside the wildcard carry no ownership certificate. Timing and allocation tests run with native object lifetimes and contribute opaque contexts.

The build-time linker also reads the pin's syntax trees and Python method resolution order. The submission image contains the original pin, its selectors, collectors and linked data. The separate evaluation report records the limits of the measured cohorts.
