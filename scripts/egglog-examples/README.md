# Finite egglog example ports

This corpus contains **33 additional egglog source examples** that run on
semi-persistent through direct ports or explicit encodings. It includes
the source inputs, selected validation cases and deliberate failure
controls, with a runner for both naive and semi-naive evaluation.

It is separate from the
[17-family benchmark registry](../../egraph/benches/corpus.toml). These
33 source files are not 33 new performance families. No engine changes,
benchmark registrations or performance claims accompany this corpus.

“Finite example” means preserving the supplied example's computation and
documented observations, with the adaptations recorded in its manifest.
It does not establish the entire native egglog API or equivalence on
arbitrary inputs. Four constructor/query fixtures are small regression
tests with weak or absent source assertions.

## Contents

| Manifest / fixture group | Sources | Examples |
| --- | ---: | --- |
| [primitives](manifests/primitives.json) | 10 | bitwise, bool, i64, pair, string, primitives, looking_up_global, name-resolution, use-at-in-string, datatypes |
| [relations](manifests/relations.json) | 6 | points-to, schedule-demo, relation-query-allowed, test-combined, test-combined-steps, stratified |
| [collections](manifests/collections.json) | 4 | map, set, unstable-fn, eqsat-basic-multiset |
| [constructors](manifests/constructors.json) | 4 | proof-extract-cost, repro-querybug2, repro-querybug4, repro-silly-panic |
| [core](manifests/core.json) | 8 | array, list, antiunify, fibonacci, fibonacci-demand, path-union, naturals, birewrite |
| [cyk-endpoints](manifests/cyk-endpoints.json) | 1 | cykjson, including its original 801-token input |
| **Total** | **33** | **93 source, validation and control cases** |

Each example has one source case and three comparison arms:

1. The original computation on egglog, with any input/observation harness
   changes recorded explicitly.
2. The supported encoding on egglog.
3. The encoding on semi-persistent.

Selected controls sometimes apply only to the affected encoding. Both
execution modes are used for every program entry: **277 entries, 554
processes** in a complete run. Those are execution counts, not additional
examples.

`fixtures/<group>/<example>/upstream.egg` preserves the exact source bytes
at egglog commit `593df10e1465904e8b7a3dc85d8ef3976842b509`. Manifests
record its path, SHA-256 and pinned source URL, and the path/hash and
expected outcome of every runnable program. Some direct arms reuse the
same physical file. Other programs add dialect changes, assertions or
supporting definitions; consult `adaptations` and `limitations` before
interpreting a result. Git attributes preserve inherited trailing
whitespace in these hashed fixtures.

The semi-persistent programs use `check-eq` and `check-neq` (formerly
`prove`) for their build-and-compare assertions. This preserves the observations encoded before `check`
became a query that only matches existing terms. In particular, some
absence checks rely on building a witness term before comparing its
class. Egglog programs retain their original `check` syntax; programs
that previously shared a file have separate copies where this spelling
differs. This corpus exercises build-and-compare assertions. Query
printing, match counts and lazy query completion need separate tests.

The upstream files and derived fixtures retain egglog's
[MIT license](LICENSE.egglog). The Python tooling uses the repository's
Apache-2.0 license. Attribution comments on derived programs and a narrow
scaffold exception for exact `upstream.egg` files avoid changing source
bytes merely to satisfy the project's owned-source header check.

## Run

Use Python 3.10 or newer. No Python packages are required. From the
repository root:

```sh
# Validate all provenance/program hashes and runner regressions.
python3 -B scripts/egglog-examples/test_runner.py
python3 -B scripts/egglog-examples/run.py --check

cargo build --locked --release -p semi-persistent-egraph --bin semi-persistent

# Run only semi-persistent, in both modes.
python3 -B scripts/egglog-examples/run.py \
  --output scripts/egglog-examples/runs/ours-1
```

To compare all three arms, build egglog at the pinned commit in a separate
checkout:

```sh
git clone https://github.com/egraphs-good/egglog.git /tmp/egglog-example-reference
git -C /tmp/egglog-example-reference checkout 593df10e1465904e8b7a3dc85d8ef3976842b509
cargo build --locked --release \
  --manifest-path /tmp/egglog-example-reference/Cargo.toml --bin egglog

python3 -B scripts/egglog-examples/run.py \
  --egglog /tmp/egglog-example-reference/target/release/egglog \
  --output scripts/egglog-examples/runs/paired-1
```

Use a new output directory for each run. The runner refuses to overwrite
existing results. `--ours` accepts an alternate semi-persistent binary.
It records binary hashes; it does not infer which source revision an
arbitrary supplied binary was built from. The caller must build the
reference from the pinned source.

To narrow a run:

```sh
python3 -B scripts/egglog-examples/run.py \
  --example core/array --source-only \
  --output scripts/egglog-examples/runs/array-1
```

`--group` and `--example` can be repeated. Unknown names fail rather than
silently running nothing.

## What the runner checks

The runner verifies source and program hashes before execution and runs
one process at a time. Successful cases must exit successfully and satisfy
their supplied assertions and any recorded extraction-output checks.
Negative controls must fail with their specified diagnostic. A parser
error, signal or timeout cannot stand in for the expected rejection.
Expected success exits with code 0; both expected rejection categories
exit with code 1. A crash with another exit code fails the run.

Each process has a 30-second wall watchdog and an 8-MiB combined output
guard by default. `--timeout` and `--output-limit-mib` change those limits.
The output guard is sampled, so a process may briefly exceed it. These
limits are not memory limits or benchmark acceptance criteria.
Interruption and SIGTERM kill and reap the child process group and preserve
completed results. Binary and program hashes are rechecked before each
invocation; keep the supplied binaries and fixtures unchanged during a run.

`results.json` records configuration coverage, expected and actual
outcomes, program and binary hashes, and paths to stdout/stderr logs.
Its `complete` flag and planned process count distinguish an interrupted
run from full configuration coverage.
Elapsed times are watchdog diagnostics. This is a correctness corpus,
not the project's Criterion performance harness.

The [recorded validation](validation.json) identifies a fresh release
build of semi-persistent at `9b51c72742fc459dbeed5ababc197e8a56130266`
and the pinned egglog binary. All 554 processes matched their expected
outcomes: 378 successful executions, 164 intended check failures and
12 intended runtime failures, with no timeouts. The record includes the
runner, manifest and binary hashes so later reruns can be distinguished.

## Adaptations that affect interpretation

- **Relations and schedules.** Most relation encodings separate row
  identity from membership using `Holds(Row(...)) = Present`. Simplified
  presence encodings are used only where row identity is unobserved.
  Combined rulesets share one iteration snapshot; bounded schedule
  translations preserve the named example, not arbitrary nested schedules.
- **Tables and errors.** Array/list/Fibonacci encodings preserve demand,
  definedness and uniqueness observations through witnesses or boxed
  results. Some native runtime errors become explicit checks after
  computation, changing error timing.
- **Primitives and collections.** Bitwise operations, string operations,
  sets and maps become computations using supported constructors and
  rules. Concrete callbacks are defunctionalized. Helper schedules and
  finite domains are documented; this is not a general callback or
  mutable-container API.
- **Extraction.** Some encoded outputs have different representations or
  costs. Their value observations are checked separately where needed.
  `proof-extract-cost` exercises normal weighted extraction, not proof mode.
- **CYK.** The endpoint encoding changes chart coordinates from
  `(span, start)` to `(start, start + span)`, retaining all three parsing
  rules and conflict checks. The original CSV input is inlined. The
  801-token source case checks root chart membership and the definedness
  of an otherwise unused root-tree lookup; it has no independent full-chart
  oracle. The smaller validation case and ambiguity control add evidence,
  not a proof of general parsing or immediate native error semantics.

## Relation to the broader audit

The local investigation attempted 48 distinct source files: these 33
finite-example ports, three specialized fixed-trace encodings, and 12
partial/reduced/alternative implementations. The latter 15 are excluded
from this portable corpus. The full upstream inventory contained 187
`.egg` files, including 141 main programs/demos and separate rejection,
proof and support fixtures.

These counts identify source coverage. Growing a useful performance suite
still requires selecting independent workload families, varying their
inputs, maintaining independent correctness checks, and using the
repository's benchmark methodology.
