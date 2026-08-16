# egglog comparison: E3 translation pilot and E4 harness

This directory holds the pilot for work items E3 (translator) and E4 (harness) of
`doc/egglog-comparison-plan.md`: three benchmarks from the intersection set, translated
into our surface language in two encodings each, timed against egglog at its own commit.

It is not a status page. The numbers in `pilot-results.csv` are one machine, one day; the
protocol below regenerates them, and the per-benchmark ledgers record every semantic
difference that stands between the three programs being compared.

## What is here

Three benchmarks, each in three configurations:

| benchmark | source |
|---|---|
| `eqsat-basic` | `egglog/tests/web-demo/eqsat-basic.egg`, benchmark 8, the calibration smoke test |
| `math-add-ac` | the `add-ac` ruleset block of `egglog/tests/web-demo/math.egg` lines 138-160, benchmark 2 |
| `math-microbenchmark` | `egglog/tests/math-microbenchmark.egg`, benchmark 1 |

| file | engine | encoding |
|---|---|---|
| `<name>.egglog.egg` | egglog | theirs, unchanged except as its ledger records |
| `<name>.rules.egg` | ours | A/C supplied as explicit rewrite rules, their encoding |
| `<name>.native.egg` | ours | A/C carried by the operator declaration, the A/C rules deleted |
| `<name>.deviations.md` | | every semantic difference between the three |

`run-pilot.py` is the harness and `pilot-results.csv` its output, one line per timed run.

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

Read the ledgers before the numbers. `math-microbenchmark.deviations.md` in particular
records a deviation large enough to change how its native column may be read: eleven of
its rules are restated in n-ary form, because a binary pattern against a variadic AC
operator is an exact pattern and would silently stop firing on flat nodes of arity three
or more.

## What the pilot measured

Median wall time over 10 runs after 2 warmups, and the node count each engine reports.
Regenerate with `run-pilot.py`; the per-run values are in `pilot-results.csv`.

| benchmark | config | median wall | nodes | classes | iterations |
|---|---|---|---|---|---|
| eqsat-basic | egglog | 5.8 ms | 11 | not reported | 3 |
| eqsat-basic | ours, rules, naive | 3.3 ms | 17 | 11 | 3 |
| eqsat-basic | ours, rules, semi-naive | 3.3 ms | 17 | 11 | 3 |
| eqsat-basic | ours, native, naive | 3.1 ms | 14 | 11 | 3 |
| eqsat-basic | ours, native, semi-naive | 3.2 ms | 14 | 11 | 3 |
| math-add-ac | egglog | 9.6 ms | 1 939 | not reported | 7 |
| math-add-ac | ours, rules, naive | 10.7 ms | 3 256 | 148 | 7 |
| math-add-ac | ours, rules, semi-naive | 10.0 ms | 3 304 | 134 | 7 |
| math-add-ac | ours, native, naive | 3.0 ms | 25 | 25 | 1 |
| math-add-ac | ours, native, semi-naive | 3.0 ms | 25 | 25 | 1 |
| math-microbenchmark | egglog | 508.3 ms | 1 047 896 | not reported | 11 |
| math-microbenchmark | ours, rules, naive | 11 561.8 ms | 1 234 680 | 506 565 | 11 |
| math-microbenchmark | ours, rules, semi-naive | 11 299.2 ms | 1 251 193 | 515 357 | 11 |
| math-microbenchmark | ours, native, naive | 1 118.4 ms | 755 928 | 446 917 | 11 |
| math-microbenchmark | ours, native, semi-naive | 15 539.4 ms | 755 919 | 446 917 | 11 |

Three results carry the pilot. Native AC beats our own rules encoding by 10.3x on
`math-microbenchmark` and by 3.6x on `math-add-ac`, at 39% and 99% fewer nodes, which is
the property the comparison exists to measure. egglog runs `math-microbenchmark` 22.7x
faster than our rules encoding runs the same program with the same rules to the same
11 iterations, a gap 18% more nodes does not explain, so it is a matching-throughput
result and the pilot's main negative finding. Our semi-naive strategy is 13.9x slower than
naive on `math-microbenchmark` under native AC for the same final e-graph, which is why
both strategies are reported rather than one.

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
machine. egglog also pins toolchain 1.91.0, which was not installable here; the build used
1.93.0 through `RUSTUP_TOOLCHAIN` and produced an 8.98 MB binary.

## What the pilot does not cover

One machine, no CPU pinning, no isolation from other load; treat differences under about
10% as noise. Three of the ten intersection benchmarks, chosen by the plan as the pilot
set. No proof or term-encoding mode on either side. Iterations to fixpoint are not
reported separately from iterations at the budget, because none of the three benchmarks
saturates before its budget except `math-add-ac` under native AC, which saturates
immediately.
