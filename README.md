# Blast Radius

A static test selector for SQLGlot at `eb11aec4be8cb2122afe713a4816662c3f0fb2fa`. It reads independent unified diffs and the numbered test manifest in `/data`, then prints one JSON object per commit.

## How selection works

The image contains a static selector and a dependency index measured on the unmodified commit. The runtime manifest supplies test numbers and prices. The selector validates hunk coordinates and old bytes, applies each patch independently in memory, and compiles Python with the pinned interpreter.

The offline collector uses the kit’s Python image, exact package lock and `SKIP_INTEGRATION=0`. It records CPython line and lambda-entry events, source and fixture opens, pytest fixture scopes, imports, and work in spawned Python processes and pool tasks. Module initialization and collection can publish objects through global registries. An observed dependency during either phase is charged to the whole suite. Pool serialization outside the task belongs to the pool’s submitters. Unrecognized runtime test IDs are mandatory.

Two additional cold pytest runs trace the complete TPC-DS executor and parser node-limit tests. The executor trace follows parent parsing, each submitted task, and comparison with DuckDB. The parser trace follows six real calls, including both large parses. Each test has a shared bucket for setup, imports, pool machinery and work between cases. The per-case index in `case-coverage.json` records physical lines, potential name and literal-key reads at those lines, observed class reads, lambda entries and file opens. The collector merges positive dependencies from every bucket into the runtime index. Selector execution uses the resulting unions.

The collector also starts a fresh Python interpreter for every passing node in the manifest. One node owns all events from startup through teardown and worker shutdown, including source executed by imports and shared fixtures. A later consumer of a process-wide cache therefore records its own first read and initialization. The reducer unions these observations with the suite and case traces and recomputes derived source readers from the combined line masks. The general line and data-file rules retain the full-suite fallback for sites absent from the original suite and case traces. Every isolated run must pass before the collector writes the combined index.

For each Python change under `sqlglot/`, the selector inspects removed lines in the original syntax tree and added lines in the reconstructed tree. A changed line in an assignment or mutating call on potentially shared state selects the full suite before syntax equality, certificates or line coverage. A later test can read the modified object without ever executing the write. This check includes module bindings, explicit global and nonlocal writes, class receivers, subscript writes, `setattr`, and in-place collection operations. A multiline operation includes its arguments or assigned value. Plain class-body declarations continue through the existing reader maps. Mutating calls within their values still count.

Direct assignment to an ordinary instance receiver, such as `self.field = value`, writes the instance. The expression `self.field.update(...)` or `self.field[key] = value` can change a container inherited from the class, and `self.field += value` can invoke an in-place operator on it. All three select the suite. The receiver exemption uses the first positional parameter of a plain instance method, regardless of its name. Class methods, implicit class receivers such as `__new__`, metaclass methods, and unresolved decorators or base classes receive conservative treatment. The selector also recognizes function-local containers created by literals, comprehensions, or unshadowed built-in constructors. An unresolved alias or parameter used as a mutation receiver selects the suite.

The selector derives mutating methods from Python’s mutable container types, including the collections types, and checks the first argument of in-place operator calls. Passing a potentially shared object to a helper can also let it change that object. The same guard checks positional, keyword and unpacked arguments, including class attributes, module names and unresolved aliases. Recognized pure builtins such as `len` and `sorted` are exempt for that call. Their argument expressions are still checked for nested writes.

At image build time, `mutation_summaries.py` parses every Python module in the pinned SQLGlot package. Each function, method and lambda gets a parameter signature and a mask of possible writes or escapes. The analysis follows local aliases, assignments through objects, in-place operators, container and closure captures, returned arguments and calls through callbacks. A direct getter can return an element. Its caller can still receive a shared object. An unresolved call marks its arguments and receiver inside the calling function. A worklist propagates these effects back to callers until recursive groups reach a fixed point.

At selection time, a unique project binding can exempt individual arguments whose receiving parameters have no recorded effect. The resolver follows direct imports, re-exports and unambiguous aliases. It binds positional-only and keyword-only parameters and includes every parameter an unpack can reach. Rebindings, opaque decorators, unresolved instance or constructor dispatch and ambiguous targets preserve the previous shared-argument check. Enclosing calls and nested calls are each checked. A full-suite decision on either side of the patch takes precedence.

The pinned image contains the original summaries and their call constraints. Each diff gets its own view of the changed modules. The selector recomputes summaries for touched definitions and resolves transitive calls against every file in that diff. Static analysis reads the reconstructed source. Live verification can later run selected tests against it in a child process.

The selector sends the full suite for a patch over 1 MiB or over 2,000 added and removed lines combined across files. It checks byte size before opening the patch and counts edits before parsing Python. The shared-write check uses binary search on changed line numbers. Each function summary has a bounded work allowance for syntax visits and alias propagation. Exceeding it marks every parameter as possibly mutated. Patched modules and their call graph also share an aggregate work allowance.

A separate worker analyzes one commit at a time. The parent gives it up to three wall-clock seconds per commit and up to 150 seconds across the batch, including map loading. A timed-out commit gets the precomputed full-suite plan. The parent can restart the worker for the next commit. When the batch deadline expires, it emits full plans for the unresolved remainder.

### Rules that can omit a test

| Evidence | Required tests and rationale |
| --- | --- |
| Equal Python syntax trees | Keep explicit source readers. CPython compiles the same syntax, including type comments. A reader can still observe different bytes or encoding. |
| Existing data file | Keep every observed reader of that path, including consumers of shared fixtures. Every byte of an SQL fixture counts. An unobserved path selects the suite. |
| Covered function-body replacement | Keep tests reaching any changed line, its enclosing multiline statement or guard, source readers and code-object inspectors. All touched files contribute. A changed test module or an edit without sufficient coverage or a structural certificate selects the suite. |
| Aligned comparison instructions | Recursively compare the old and new code objects. Require identical scope, flags, constants, exception ranges, instruction boundaries and opcodes. Only an operand of an existing comparison may differ. Keep readers of every differing instruction’s source line and enclosing statement. This recovers an unexecuted branch without assuming a comparison result. |
| Literal in a lambda body | Changing one bounded literal leaves lambda construction and defaults intact. Keep every test that entered a lambda on that definition line. Lambdas sharing the line share their readers. |
| Literal argument captured by a closure | Resolve an unshadowed direct import. The pinned factory must only define an undecorated inner function and return it, with deferred annotations and no evaluated defaults. Both calls bind identical argument positions. Keep every test reaching the returned function body across all registrations. |
| Scalar on a concrete dialect | For a same-type integer or Boolean change in an ordinary direct subclass, keep covered name reads, observed class and instance lookups, and possible raw namespace readers. Reads in the dialect metaclass participate. |
| Tokenizer dictionary value | Require an unchanged, unique literal string key set and tuples of integers. Exclude fields consumed by tokenizer subclass initialization. Keep observed reads of the original binding, every observed consumer of a tokenizer instance of that family, and possible raw namespace readers. A class-creation read can be ignored only where a pinned local is used exclusively in constant-string membership tests. Those tests see the same keys. |
| Expression class schema | Require a direct expression subclass whose only statement declares the string-to-Boolean `arg_types` dictionary. The pinned initializer computes `required_args` from its truth values. Keep readers of either binding, instance consumers and possible raw namespace readers. |

The six specialized rules starting with aligned comparisons require a single changed production file and one replaced physical line with preserved indentation. Each literal rule checks the complete syntax trees for exactly one eligible value difference. Source readers and known function-code inspectors stay selected. A failed proof uses the broader selection. Any unresolved initialization change, compile failure, unsupported diff, new or deleted file, context mismatch, or absent coverage selects the suite. In particular, a syntax error can reach a test through a registry whose Python imports are invisible in that test.

The initialization proofs use the pinned source. Coverage is empirical. Test order, cross-test state, native readers and timing can expose dependencies absent from a baseline run.

### Selection switches

Each switch defaults to 1 and accepts a Docker build argument or a runtime environment override such as `-e FUNCTION_INSERTIONS=0`.

| Switch | Effect |
| --- | --- |
| `CLASS_TABLE_ENTRIES` | Checks replacements inside one class dict, list or tuple display. The build follows shallow copies and inherited table names to covered reads. It includes literal-key and reflective readers. Changes confined to a lambda body can use the original lambda’s entry coverage through all copies. |
| `FUNCTION_INSERTIONS` | For a certified read-only edit inside one existing function, includes the entire original function’s body coverage and its source and code readers. New declarations, unresolved calls and shared writes select the suite. |
| `TOUCHED_ARGUMENTS` | Matches unchanged argument slots at the same callee and recognizes fresh formatted strings. Explicit shared receivers, known at-risk parameters and unresolved bindings keep their existing guards. |
| `LOCAL_SCOPE_CHANGES` | Extends the function rule to changes in local variables. It checks flags, closure bindings, nested code objects and references that could be shadowed. |
| `UNUSED_IMPORTS` | Checks a single added or removed module-level alias for unused or re-exported names. Includes binding readers and importers that request the name or use a star import. |
| `FAST_ANALYSIS` | Loads image-built binary indexes, reuses pinned binding facts, and stops analysis once a full-suite decision is known. |
| `NARROW_SHARED_ARGS` | Resolves possibly shared arguments and includes known binding readers. A shared binding without reader evidence selects the suite. |
| `ISOLATION_DROP` | Runs eligible small unittest selections in an isolated child. Passing selections can be dropped. |
| `ENGINE_SKIP` | Replays the TPC-DS frontend on eligible changes before dropping the executor test. |
| `IDENTITY_EQUIVALENCE` | Checks whether a single identity/equality comparison has the same result for the pinned class or enum. |

### Worker placement

Longest-processing-time-first packing prices one through eight workers in integer milliseconds. The least expensive plan keeps every required test. All zero-duration tests join a nonempty plan. Related tests have priority when filling space below the busiest worker’s load.

## Reproduce

Build the entry with `docker build --platform linux/amd64 -t br-entry .`. Its default target uses the committed maps. A separate Git stage fetches only the pinned SQLGlot commit, checks the detached HEAD against its full hash, and copies the checkout into the Python image. The entry and tracer install the same locked Python packages, including DuckDB, NumPy and pandas.

```sh
docker build --platform linux/amd64 --target tracer -t br-tracer .
mkdir -p scratch/generated
docker run --rm --platform linux/amd64 --cpus 2 --memory 7g -e PYTHON_CPU_COUNT=2 \
    -v "$PWD/scratch/generated:/out" br-tracer
```

The offline collector can take over an hour on a small machine. BR_COLD_JOBS sets the number of isolated pytest processes to run concurrently. Its per-node checkpoints are in the output directory. Use a fresh output directory when changing the source, environment or instrumentation. The collector emits `maps.json` and `case-coverage.json`. With a local starter kit, run `KIT=/absolute/path/to/kit bash tools/verify.sh`. The verifier rebuilds the entry, checks the manifest, runs the official scorer and computes the exact oracle cost for each sample. It runs each labeled kind in isolation and measures fresh-cgroup CPU on three matching batches under the kit flags. The **Measure** workflow applies the build resource limits on a native amd64 runner.

## How the selector was tested

Independent edits were applied to clean copies of the pinned checkout. Pytest ran the modified sources in fresh processes, including subtests, fixture setup, teardown and collection. The evaluator compared observed failures with the required tests before worker placement and with the image output. The sample scorer separately checked the numbered worker plans under the official run flags. The map collector reads only the unmodified sources and their execution traces.

## Third-party code and libraries

The source-fetch stage uses the digest-pinned Alpine Git image from Docker Hub. The entry uses CPython and its standard library from the official Python slim image, and the pinned SQLGlot source (MIT). SQLite is provided by the base image. The evaluation script calls the Builders starter kit’s official scorer. GitHub Actions uses actions/checkout and actions/upload-artifact, and Docker Buildx uses BuildKit. All selector, packing and tracing code in this repository was written for this entry.

The image installs the following distributions at the versions in [the official package lock](builder/requirements.lock).

`ast_serialize`, `cfgv`, `distlib`, `duckdb`, `execnet`, `filelock`, `identify`, `iniconfig`, `Jinja2`, `librt`, `markdown2`, `MarkupSafe`, `mypy`, `mypy_extensions`, `nodeenv`, `numpy`, `packaging`, `pandas`, `pandas-stubs`, `pathspec`, `pdoc`, `platformdirs`, `pluggy`, `pre_commit`, `psutil`, `Pygments`, `pyperf`, `pytest`, `pytest-timeout`, `pytest-xdist`, `python-dateutil`, `python-discovery`, `pytz`, `PyYAML`, `ruff`, `setuptools`, `setuptools-scm`, `types-python-dateutil`, `types-pytz`, `typing_extensions`, `tzdata`, `vcs-versioning`, `virtualenv`.

## License

[MIT](LICENSE).
