# egglog comparison: E3 translation pilot and E4 harness

This directory holds the pilot for work items E3 (translator) and E4 (harness) of
`doc/egglog-comparison-plan.md`: three benchmarks from the intersection set, translated
into our surface language in two encodings each, timed against egglog at its own commit.

It is not a status page. The numbers in `pilot-results.csv` are one machine, one day; the
protocol below regenerates them, and the per-benchmark ledgers record every semantic
difference that stands between the three programs being compared.

## What is here

Ten benchmarks, the whole ranked intersection set. The first three are the pilot;
the next four landed 2026-08-16, and the last three on 2026-08-17, once the two
pattern-language features they needed existed.

| benchmark | source | configurations |
|---|---|---|
| `eqsat-basic` | `egglog/tests/web-demo/eqsat-basic.egg`, ranked 8, the calibration smoke test | 3 |
| `math-add-ac` | the `add-ac` ruleset block of `egglog/tests/web-demo/math.egg` lines 138-160, ranked 2 | 3 |
| `math-microbenchmark` | `egglog/tests/math-microbenchmark.egg`, ranked 1 | 3 |
| `calc` | `egglog/tests/calc.egg`, ranked 6, `:until` goals over four push/pop blocks | 3 |
| `until` | `egglog/tests/until.egg`, ranked 6, `:until` against a non-terminating generator | 3 |
| `integer_math` | `egglog/tests/integer_math.egg`, ranked 5, **scoped** | 3 |
| `matrix` | `egglog/tests/web-demo/matrix.egg`, ranked 7, mixed AC and A-only | 3 |
| `bdd` | `egglog/tests/web-demo/bdd.egg`, ranked 9, commutative without associative | 3 |
| `herbie` | `egglog/tests/web-demo/herbie.egg`, ranked 3, **scoped**, no native dual | 2 |
| `eqsolve` | `egglog/tests/web-demo/eqsolve.egg`, ranked 10, the extraction path, no native dual | 2 |

`matrix`, `bdd` and `eqsolve` were dropped on 2026-08-16 for want of two
pattern-language features, a root-binding form `(= v pat)` and primitive predicates
in `:when`. Both landed, and all three now ship with their load-bearing rule intact.
Their ledgers open with that history; the drop-era ledgers are in the history of
commit c2558c7 and are not current. Two configurations remain unwritten:
`eqsolve`'s native-AC dual, postponed on AC congruence completion, and herbie's,
plus `repro-herbie-vanilla` (ranked 4). Reasons in `eqsolve.deviations.md` and
`herbie.deviations.md`.

`matrix`'s native column carries native AC on `Times` only; its A-only operators
keep their associativity rewrites, because a one-element application of an
`:assoc` operator is not identified with its argument, so an n-ary restatement is
not writable. That is the benchmark's own selection property, so read
`matrix.deviations.md` before drawing an A-only conclusion from this set.

`integer_math` and `herbie` are scoped columns: a reduced program, identical in
every configuration, standing in for the upstream benchmark. Their timings are not
comparable to anything upstream calls by those names. Both ledgers open with that
warning and state what the scoping cost — for `integer_math`, 537 term nodes down
to 100.

| file | engine | encoding |
|---|---|---|
| `<name>.egglog.egg` | egglog | theirs, unchanged except as its ledger records |
| `<name>.rules.egg` | ours | A/C supplied as explicit rewrite rules, their encoding |
| `<name>.native.egg` | ours | A/C carried by the operator declaration, the A/C rules deleted |
| `<name>.deviations.md` | | every semantic difference between the three |

`run-pilot.py` is the pilot harness and `pilot-results.csv` its output, one line per
timed run. `run-full.py` covers the whole set with the same protocol; it names its
output after `--label`, so `smoke-results.csv` is a 1-run-0-warmup pass proving the
harness runs end to end and `final-results.csv` is reserved for the campaign at one
pinned commit. Do not read `smoke-results.csv` as a timing result, for two reasons.
With no warmups its first cell per process pays cold-start cost, visible as
eqsat-basic's 376 ms against a warm 3.3 ms. And its `ours` binary was built from a
working tree carrying another agent's uncommitted `egraph/src` changes, so it names
no commit, which `methodology.md` section 1 requires of any table. What the pass
does establish is validation, not timing: both engines exit non-zero on a failed
check, so a clean sweep means every check of every program holds in every
configuration. That pass covered the seven benchmarks that existed on 2026-08-16;
`matrix`, `bdd` and `eqsolve` were swept the same way when they landed and their
counts are in their ledgers.

`gen-herbie.py` regenerates herbie's two programs and `herbie-dropped.txt`, the
verbatim listing of every form the scoping removes.

Beside the pilot, `addac-sweep.md` reports the add-ac width-scaling sweep that answers
part (b) of the convergence target in
`egraph/doc/design/20-index-selectivity-and-delta-suffixes.md`: the `math-add-ac` block
generalized to sum width n = 7..20, three configurations per width, in
`addac-n<k>.{egglog,rules,native}.egg`. `gen-addac-sweep.py` writes those programs,
`run-addac-sweep.py` times them, and `addac-sweep.csv` holds the per-run values. Native
AC holds at 4n - 3 nodes and one iteration across the whole range while the rules
encoding reaches 37 902 nodes at n = 20; read `addac-sweep.md` for the shape of that
growth, for the goal-binding deviation that makes the three programs the same problem,
and for the timing trap that erases the result.

`semi-persistence/` holds work item E6, which quantifies what push/pop is worth:
the survey of how each engine implements it, a micro-benchmark of push/assert/
run/check/pop cycles over bases of 1e4 to 1e6 nodes on both engines, the
internal restore-versus-re-run baseline that needs no cross-engine caveat, and
`calc.egg` as the multi-block macro exhibit. Read
`semi-persistence/semi-persistence.md`; its section 8 states what the numbers do
not establish, which includes the asymptotic separation the experiment was
designed to find.

`span-table-sparsity.md` prices the `O(num_keys)` term in the per-round index
build and states the design that removes it: at S = 1e6 the span tables are
40.6 ms of a 65.4 ms index build because they are dense over a key space 2.44x
the values it holds, and installing a semi-naive delta costs 19.6 ms to make 23
values addressable. `run-span-table.py` regenerates every number in it and
checks corpus identity across binaries. That document also retracts the cost
claim in `containers-verus/doc/design/16-layered-span-map.md` section 4 and the
semi-naive column of `semi-persistence/semi-persistence.md` section 5; read it
before citing either. Its section 11 records the verified landing: the index
build goes 57.61 ms to 32.64 per round at S = 1e6, the delta build 12.75 to
1.38, and peak resident set size 1 047.3 MiB to 608.2. Sections 1 through 10 are
the diagnosis and their prototype numbers are superseded by section 11.

Read the ledgers before the numbers. `math-microbenchmark.deviations.md` in particular
records a deviation large enough to change how its native column may be read: eleven of
its rules are restated in n-ary form, because a binary pattern against a variadic AC
operator is an exact pattern and would silently stop firing on flat nodes of arity three
or more.

## What the pilot measured

Median wall time over 10 runs after 2 warmups, and the node count each engine reports.
Regenerate with `run-pilot.py`; the per-run values are in `pilot-results.csv`.

This run followed `registry: memoize completion_column`, so it measures that change and
chapter 20's S1 together, and egglog's own median calibrates the machine at 523.9 ms
against the previous run's 508.3 ms on an unchanged binary.

| benchmark | config | median wall | nodes | classes | iterations |
|---|---|---|---|---|---|
| eqsat-basic | egglog | 6.6 ms | 11 | not reported | 3 |
| eqsat-basic | ours, rules, naive | 3.3 ms | 17 | 11 | 3 |
| eqsat-basic | ours, rules, semi-naive | 3.4 ms | 17 | 11 | 3 |
| eqsat-basic | ours, native, naive | 3.2 ms | 14 | 11 | 3 |
| eqsat-basic | ours, native, semi-naive | 3.3 ms | 14 | 11 | 3 |
| math-add-ac | egglog | 10.7 ms | 1 939 | not reported | 7 |
| math-add-ac | ours, rules, naive | 10.8 ms | 3 317 | 159 | 7 |
| math-add-ac | ours, rules, semi-naive | 10.0 ms | 3 359 | 136 | 7 |
| math-add-ac | ours, native, naive | 3.0 ms | 25 | 25 | 1 |
| math-add-ac | ours, native, semi-naive | 3.0 ms | 25 | 25 | 1 |
| math-microbenchmark | egglog | 523.9 ms | 1 047 896 | not reported | 11 |
| math-microbenchmark | ours, rules, naive | 747.8 ms | 1 233 013 | 507 992 | 11 |
| math-microbenchmark | ours, rules, semi-naive | 945.3 ms | 1 254 916 | 518 063 | 11 |
| math-microbenchmark | ours, native, naive | 644.9 ms | 755 926 | 446 915 | 11 |
| math-microbenchmark | ours, native, semi-naive | 761.7 ms | 755 917 | 446 915 | 11 |

Three results carry the pilot, and chapter 20's S1 has moved two of them since the first
run. egglog runs `math-microbenchmark` 1.4x faster than our rules encoding runs the same
program with the same rules to the same 11 iterations, against 22.7x before: the gap was
one join order on one rule and not per-match throughput, which `throughput-gap-ours.md`
establishes and this table now confirms end to end. The load-independent control is the
e-matching step count, which the same change takes from 218,567,542 to 7,284,276 on that
benchmark. Native AC still beats our rules encoding on `math-add-ac`, by 3.6x at 99%
fewer nodes, and on `math-microbenchmark` it keeps the node-count result (39% fewer) but
holds only 1.16x of the wall time against 10.3x, because the rules encoding is the
configuration S1 sped up. Our semi-naive strategy on `math-microbenchmark` under native AC
was 13.9x slower than naive and is now 1.18x, from the same fix: its variant plans
mispriced `by_contains` and drove a Mul-Mul self-join on a shared factor, which cost
198,571,597 match steps against naive's 3,074,117 and now costs 3,167,101.

Node counts moved slightly against the first run, in the second decimal place, because
matching now reads the round's index snapshot rather than the live union-find
(chapter 09, "Which Snapshot"): a match an earlier rule of a round creates is found in the
next round instead of that one, so a run stopped at a fixed iteration budget ends a little
differently. `math-add-ac` under the rules encoding ends at 3 317 nodes against 3 256, and
`math-microbenchmark` under the rules encoding at 1 233 013 against 1 234 680.

Translating `math-microbenchmark` also exposed a matcher defect: a concrete literal inside
a rule's left-hand side never matches, so `(rewrite (Add a (Const 0)) a)` is dead while
egglog's identical rule fires. Six of that benchmark's 24 rules are written that way. The
translations work around it with let-bound globals; the reproduction and the three probes
that bound the defect are in `math-microbenchmark.deviations.md`.

## Protocol

Both engines are built in release mode and driven as separate processes, so the wall time
includes process start, parse, sortcheck, saturation, and the statistics commands. Each
(benchmark, configuration) pair runs 2 warmups then 10 timed runs; the summary reports the
median.

egglog runs `-j 1 --mode no-messages`, which is the plan's protocol: threading is their
only nondeterminism source, and `no-messages` suppresses the output of `print-size` and
`print-stats`. Ours runs with default flags plus `--types machine`, which is what puts
`i64`, `f64` and `String` in scope; the `bignum` group has no `String` sort and would not
type `math-microbenchmark`.

Our engine is timed under **both** saturation strategies, because the choice is not
settled by a default: `src/main.rs` makes naive the default and `--use-semi-naive` the
opt-in, so `ours-*-naive` is the shipped configuration and `ours-*-semi` is reported
beside it. On `math-microbenchmark` under native AC the two differ by more than an order
of magnitude, in naive's favour, which is the reason to keep reporting both.

Two asymmetries in the timing, both stated rather than corrected. First, our timed runs
compute and print `print-size` while egglog's `no-messages` mode skips that work; at
1.2 M nodes the listing is a linear pass and 14 lines of output, which is small against an
11-second run but not zero. Second, both engines write their statistics JSON during the
timed run, so that cost is symmetric.

Node counts are not measured the same way by the two engines, and the difference runs in
egglog's favour: their `print-size` reports table cardinality after rebuild, ours reports
stored nodes, so a node that congruence turned into a duplicate is still counted by us and
not by them. `eqsat-basic.deviations.md` demonstrates this on a two-line probe. Our totals
also include one node per distinct interned literal, which theirs never count.

## Re-running

Build both engines:

```
cd <this repo>          && cargo build --release -p semi-persistent-egraph
cd <egglog checkout>    && cargo build --release
```

Then, from this directory:

```
python3 run-pilot.py                       # 2 warmups + 10 runs, writes pilot-results.csv
python3 run-pilot.py --runs 3 --warmups 1  # quicker pass
python3 run-pilot.py --ours <path> --egglog <path>
```

The harness defaults to `../target/release/semi-persistent` and
`/tmp/egglog/target/release/egglog`.

To run one program by hand:

```
../target/release/semi-persistent math-microbenchmark.native.egg --types machine
<egglog>/target/release/egglog -j 1 math-microbenchmark.egglog.egg
```

Each program writes `<name>.<config>.stats.json` next to itself. Those files are
regenerated by every run and are not committed.

## Building egglog when cargo cannot reach crates.io

On the machine that produced these numbers, `cargo` could not open a connection to
`index.crates.io` while `curl` to the same host succeeded, so egglog's dependencies were
vendored by hand: read `name`, `version` and `checksum` for every registry package in
egglog's `Cargo.lock`, fetch `https://static.crates.io/crates/<name>/<name>-<version>.crate`,
extract each into `vendor/<name>-<version>/` with a `.cargo-checksum.json` holding that
checksum, and point `.cargo/config.toml` at the directory:

```toml
[source.crates-io]
replace-with = "vendored-sources"
[source.vendored-sources]
directory = "vendor"
```

`cargo build --release --offline -p egglog` then succeeds. Record this only because the
egglog side of the comparison cannot be reproduced without it on a similarly restricted
machine. The `.crate` files stay useful: keeping the download cache means a later
re-vendor needs no network at all, which is how the 2026-08-16 rebuild ran.

egglog pins toolchain 1.91.0. It was not installable when the pilot ran, so that build
used 1.93.0 and produced an 8.98 MB binary. 1.91.0 is installed now and the current
binary is built at the pinned toolchain: 8.82 MB, and byte-for-byte agreement with the
committed ledgers on the three benchmarks checked (eqsat-basic 11 nodes / 3 iterations,
math-add-ac 1 939 / 7, addac-n7 451). The toolchain deviation is withdrawn.

## What the pilot does not cover

One machine, no CPU pinning, no isolation from other load; treat differences under about
10% as noise. Three of the ten intersection benchmarks, chosen by the plan as the pilot
set. No proof or term-encoding mode on either side. Iterations to fixpoint are not
reported separately from iterations at the budget, because none of the three benchmarks
saturates before its budget except `math-add-ac` under native AC, which saturates
immediately.
