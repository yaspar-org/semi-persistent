<!--
Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
SPDX-License-Identifier: Apache-2.0
-->
# Campaign final-r5

Archived campaign at engine commit a4ab9b7 against egglog 7b1adf2, over the same
seventeen-benchmark set as final-r4. It is the first campaign produced by
`scripts/egglog-compare/compare.py`, and the first that records its own
provenance: `final-r5-provenance.json` names both engine revisions, the
protocol, and the benchmarks that ran and were skipped. Raw runs:
`final-r5-results.csv` actually contains aggregate medians rather than every
timed sample. This record is superseded by `final-r6`, whose runner retains
every sample and complete binary/machine/source provenance.

Protocol: process wall clock, 2 warmups then 10 timed runs, medians; egglog
release CLI with `-j 1 --mode no-messages`; ours with default flags plus each
program's `--types` groups. One machine, no CPU pinning, no isolation from
other load.

## Headline: wall-time ratios egglog / ours (geometric means)

| configuration | all (n) | solver-dominated (n) |
|---|---|---|
| egglog / ours, rules, naive | 1.58 (17) | 1.26 (9) |
| egglog / ours, rules, semi-naive | 1.47 (17) | 1.11 (9) |
| egglog / ours, native, naive | 3.94 (11) | 6.46 (5) |
| egglog / ours, native, semi-naive | 4.23 (11) | 7.56 (5) |
| egglog / ours, native-A, naive | 4.55 (1) | 4.55 (1) |
| egglog / ours, native-A, semi-naive | 6.43 (1) | 6.43 (1) |

Above 1 means we are faster. Startup-dominated, meaning every configuration is
under 13 ms on both engines and excluded from the second column: `eqsat-basic`,
`calc`, `until`, `integer_math`, `intersection`, `typecheck`, `resolution`,
`math-add-ac`. That is one more than r4 excluded, because `math-add-ac` fell
under the threshold in every configuration this time.

## Per-benchmark medians (ms)

| benchmark | egglog | rules, naive | rules, semi | native, naive | native, semi |
|---|---|---|---|---|---|
| `acgen` | 1132.7 | 10175.9 | 24409.9 | 3.6 | 3.3 |
| `bdd` | 24.4 | 33.7 | 19.5 | 13.8 | 8.6 |
| `calc` | 8.9 | 3.5 | 3.5 | 3.3 | 3.3 |
| `combinators` | 27.3 | 4.7 | 5.0 | - | - |
| `eqsat-basic` | 6.0 | 3.2 | 3.2 | 3.2 | 3.2 |
| `eqsolve` | 25.2 | 123.1 | 120.9 | - | - |
| `herbie` | 128.1 | 28.9 | 35.8 | 14.3 | 20.9 |
| `integer_math` | 11.9 | 3.6 | 3.9 | 3.5 | 3.9 |
| `intersection` | 5.3 | 3.2 | 3.1 | - | - |
| `knapsack` | 15.4 | 4.8 | 4.9 | - | - |
| `levenshtein-distance` | 24.9 | 8.5 | 8.3 | - | - |
| `math-add-ac` | 10.0 | 10.6 | 11.2 | 3.1 | 3.0 |
| `math-microbenchmark` | 509.0 | 533.2 | 1632.5 | 482.1 | 488.8 |
| `matrix` | 27.4 | 12.9 | 7.4 | 12.9 | 7.0 |
| `resolution` | 10.2 | 4.9 | 5.0 | 3.6 | 3.6 |
| `typecheck` | 10.8 | 3.9 | 4.2 | - | - |
| `until` | 6.9 | 3.2 | 3.2 | 3.5 | 3.2 |

`matrix` also ships a native-A column, 6.0 ms naive and 4.3 ms semi-naive,
which isolates the A-only half of the signature. Read `matrix.deviations.md`
before drawing an A-only conclusion from it.

## Where we lose, which is the part worth reading

**`acgen`, rules encoding: 0.11x naive and 0.05x semi-naive.** Pure AC
saturation supplied as explicit rewrite rules is the worst case for the rules
encoding, and semi-naive makes it twice as bad again. The same benchmark under
the native encoding is 317x and 347x the other way, at 3.6 and 3.3 ms against
egglog's 1132.7 ms. Both numbers are the same claim from two sides: carrying
AC in the operator declaration is what makes this workload cheap, and
expressing it as rules is what makes it hopeless.

**`eqsolve`, rules encoding: 0.20x.** Known and recorded in
`eqsolve.deviations.md`; its native encoding is validated but excluded from
timed tables.

**`math-microbenchmark`, semi-naive rules: 0.31x against 0.95x naive.**
Semi-naive is 3.1x slower than naive on this program, which is the largest
naive-versus-semi gap in the set and the one number here that has no recorded
explanation. The native columns show no such split (482.1 against 488.8 ms), so
it is specific to the rules encoding. Not investigated.

**`bdd` and `math-add-ac`, rules encoding: 0.72x and 0.94x naive.** Both under
the noise threshold this comparison claims (about 10%) for `math-add-ac`; `bdd`
is a real loss that the semi-naive column reverses (1.25x).

## What this campaign does and does not establish

It establishes that the pinned egglog revision builds and runs and that both
engines complete every comparable program with its checks passing. The original
runner silently left every structural-statistics cell blank, so this campaign
does **not** establish successful stats parsing.
That gate and its parser regression tests first appear in `final-r6`.

It does not reproduce r4's numbers line for line and is not meant to. The
engine has moved since r4 and the runner is new. Where r4 and r5 disagree, r5
is the current measurement and r4 is a record.
