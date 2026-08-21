<!--
Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
SPDX-License-Identifier: Apache-2.0
-->
# Campaign final-r6

This is the newest retained historical cross-engine campaign. It measures a
source snapshot based on revision
`8f0414832894533e6e9205cd24831418f8d64455` against egglog
`7b1adf249c918226871b9b3d5e8f089585e46e99`.
The measured snapshot predates the current implementation. These process
medians were not estimated by Criterion and have no bootstrap confidence
intervals, so they describe only the named binaries and do not establish a
current performance ratio.

The source snapshot is identified by its base revision and tracked-patch
SHA-256 (`71c2749a4650f9a5b57b576274d50eb132203a9d08f61037cdc71374586ffee1`).
The exact binaries are bound by SHA-256:

- ours: `75797470fb3bec38b3ea0180608fe77617c40e4a42545c8d3e6079aa1dec9729`;
- egglog: `414d0e095eb5d255becef3fc6e3999e93f66ef233fa3d80c7f594a028c07002c`.

Protocol: process wall clock, two warmups followed by ten retained timed
samples per configuration, medians reported, egglog release CLI with
`-j 1 --mode no-messages`, and ours with default flags plus each program's
declared type groups. The campaign contains 750 timed samples and 75 aggregate
rows:

- `final-r6-samples.csv`: every timed invocation;
- `final-r6-results.csv`: medians, ranges, means, standard deviations, and
  stable node/class/iteration counts;
- `final-r6-provenance.json`: normalized commands, timestamps, source snapshot,
  binary hashes, non-identifying machine/tool metadata, protocol, and skipped
  programs.

## Environment qualification

This was not an isolated-host run. The 14-core machine started at load averages
6.78, 6.78, and 6.81. Absolute startup-dominated times are consequently higher
than r5. Both engines were measured under the same sequential campaign, but
these wall times
must not be presented as quiet-machine results or used to infer small-runtime
speedups. The raw samples and standard deviations are retained so that a future
quiet-host replication can replace, rather than obscure, this record.

## Headline ratios

Geometric means of per-benchmark `egglog / ours`; values above one mean ours
was faster in these retained process samples. They are descriptive statistics,
not confidence-interval-supported comparisons.

| configuration | all benchmarks (n) | fixed throughput subset (n) |
|---|---:|---:|
| rules, naive | 1.19 (17) | 1.00 (9) |
| rules, semi-naive | 1.11 (17) | 0.88 (9) |
| native, naive | 2.56 (11) | 4.37 (5) |
| native, semi-naive | 2.69 (11) | 4.96 (5) |
| native-A, naive | 2.98 (1) | 2.98 (1) |
| native-A, semi-naive | 3.27 (1) | 3.27 (1) |

The fixed subset preserves r5's nine solver-dominated program names rather
than reclassifying benchmarks from this campaign's inflated startup floor:
`acgen`, `bdd`, `combinators`, `eqsolve`, `herbie`, `knapsack`,
`levenshtein-distance`, `math-microbenchmark`, and `matrix`. It is a
sensitivity view, not a claim that this loaded campaign cleanly separates
startup from solver work.

## Per-benchmark medians

Milliseconds:

| benchmark | egglog | rules-naive | rules-semi | native-naive | native-semi | native-A-naive | native-A-semi |
|---|---:|---:|---:|---:|---:|---:|---:|
| `acgen` | 812.1 | 6793.3 | 16439.1 | 8.1 | 7.3 | - | - |
| `bdd` | 23.5 | 28.8 | 24.3 | 18.0 | 11.7 | - | - |
| `calc` | 11.8 | 7.5 | 7.6 | 7.6 | 7.7 | - | - |
| `combinators` | 25.3 | 8.6 | 8.7 | - | - | - | - |
| `eqsat-basic` | 9.8 | 7.6 | 7.5 | 7.6 | 7.7 | - | - |
| `eqsolve` | 23.2 | 99.1 | 92.9 | - | - | - | - |
| `herbie` | 96.9 | 32.3 | 31.4 | 15.8 | 20.1 | - | - |
| `integer_math` | 15.5 | 8.3 | 7.9 | 7.6 | 7.9 | - | - |
| `intersection` | 10.8 | 7.8 | 8.2 | - | - | - | - |
| `knapsack` | 16.4 | 8.5 | 8.7 | - | - | - | - |
| `levenshtein-distance` | 21.5 | 11.9 | 11.6 | - | - | - | - |
| `math-add-ac` | 13.3 | 12.3 | 13.2 | 7.4 | 7.6 | - | - |
| `math-microbenchmark` | 371.8 | 396.3 | 1165.3 | 372.3 | 367.3 | - | - |
| `matrix` | 28.5 | 19.4 | 10.8 | 14.2 | 10.3 | 9.5 | 8.7 |
| `resolution` | 13.0 | 8.7 | 8.8 | 7.7 | 7.5 | - | - |
| `typecheck` | 15.0 | 8.6 | 9.1 | - | - | - | - |
| `until` | 11.9 | 8.4 | 8.0 | 7.7 | 7.7 | - | - |

## Where the engine loses

- In this snapshot, `acgen` with explicit AC rules was 0.12x naive and 0.05x
  semi-naive; native AC measured 100x and 111x on the same workload. This is
  the intended functional contrast between rule enumeration and operator
  canonization, but the ratios require a Criterion rerun before reuse.
- In this snapshot, `eqsolve` rules measured 0.23x/0.25x. Its native
  translation was validation-only because that run's lazy completion took
  hundreds of seconds.
- In this snapshot, `math-microbenchmark` rules measured 0.94x naive and 0.32x
  semi-naive. That source state had an unexplained semi-naive regression;
  native measured approximately parity.
- In this snapshot, `bdd` measured 0.82x rules-naive and 0.97x rules-semi. At
  these absolute times, the loaded-host startup qualification dominates any
  small ratio near one.

## Statistics and runner evidence

The strict campaign required nodes and iterations from egglog, and nodes,
classes, and iterations from ours, on every timed sample. Egglog 7b1adf2 does
not report e-class counts. Its JSON stores iteration records as an array and
omits table cardinalities, so the runner counts the array and performs one
untimed normal-mode cardinality probe per benchmark. The probe is outside all
timings. The parser handles both egglog output shapes: cardinality tables with
and without a following `Overall statistics:` section.

All required metrics parsed and were stable. The aggregate CSV labels egglog
rows `varies-or-missing:classes` solely because that unsupported column is
blank; its required node and iteration fields are present. For example,
`acgen` records 173,063 egglog table rows and 10 iterations, versus 561,336
stored nodes, 2,058 classes, and 10 iterations for each of our rules
strategies.

This campaign is a historical record for its pinned source state. A current
cross-engine performance statement requires a same-revision Criterion rerun
with bootstrap confidence intervals.
