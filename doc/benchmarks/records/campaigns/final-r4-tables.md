# Campaign final-r4

One campaign at engine commit 9b8f90f: the first over the seventeen-benchmark
set, adding combinators, resolution, typecheck, knapsack,
levenshtein-distance, intersection and acgen (the generated AC stress test
from egglog-bridge, N=11) to the ten of final-r3. Protocol as in
final-tables.md: process wall clock, 2 warmups + 10 runs, medians, egglog
release CLI with -j 1 --mode no-messages, same machine as the r1 record,
binary md5s not recorded. Raw runs: final-r4-results.csv. Superseded by
final-r6, which is the newest retained historical campaign; r1, r2, r3, and r5
are other historical records in this directory. None measures the current
implementation.

## Headline: wall-time ratios egglog / ours (geometric means)

| configuration | all (n) | solver-dominated (n) |
|---|---|---|
| egglog / ours, rules, naive | 1.52 (17) | 1.16 (10) |
| egglog / ours, rules, semi-naive | 1.41 (17) | 1.03 (10) |
| egglog / ours, native, naive | 3.87 (11) | 5.59 (6) |
| egglog / ours, native, semi-naive | 4.10 (11) | 6.25 (6) |

Above 1 means we are faster. Startup-dominated (every configuration under
13 ms on both engines, excluded from the second column): eqsat-basic, calc,
until, integer_math, intersection, typecheck, resolution. The headline is
not comparable to r3's: the benchmark set grew, and acgen raises the native
column by design (below).

## Per-benchmark medians (ms)

| benchmark | egglog | rules, naive | rules, semi | native, naive | native, semi |
|---|---|---|---|---|---|
| eqsat-basic | 6.7 | 3.5 | 3.3 | 3.3 | 3.2 |
| math-add-ac | 9.9 | 10.6 | 11.4 | 3.2 | 3.1 |
| math-microbenchmark | 511.4 | 521.0 | 1611.4 | 472.8 | 477.4 |
| calc | 8.2 | 3.6 | 3.7 | 3.3 | 3.3 |
| until | 6.6 | 3.3 | 3.2 | 3.1 | 3.1 |
| integer_math | 11.5 | 3.5 | 3.8 | 3.5 | 3.9 |
| matrix | 23.9 | 12.2 | 6.9 | 12.3 | 6.9 |
| bdd | 21.8 | 33.4 | 19.2 | 13.0 | 8.4 |
| herbie | 119.2 | 28.7 | 36.2 | 14.4 | 20.4 |
| eqsolve | 24.6 | 124.5 | 115.8 |  |  |
| combinators | 24.7 | 4.6 | 5.1 |  |  |
| resolution | 9.7 | 4.6 | 4.8 | 3.5 | 3.4 |
| typecheck | 10.5 | 3.9 | 4.1 |  |  |
| knapsack | 13.9 | 4.8 | 4.9 |  |  |
| levenshtein-distance | 22.2 | 8.4 | 8.1 |  |  |
| intersection | 5.3 | 3.2 | 3.2 |  |  |
| acgen | 1108.9 | 9463.5 | 23309.0 | 3.2 | 3.3 |

matrix native-A: 6.0 / 4.3 ms. eqsolve's native configuration is validated
under --lazy-ac-eqs and excluded from timed tables (its ledger).

## Reading acgen

acgen is egglog's own generated AC stress test: two rewrite rules
(commutativity and associativity) on an 11-literal sum, run 10 000. The
native column saturates at 41 nodes in one iteration because AC canonization
holds the one flat multiset the rewrites otherwise enumerate: that collapse
is the property the benchmark isolates, not a truncated run, and it is why
this row raises the native headline. On the rules encoding we lose to egglog
(9.5 s naive, 23.3 s semi against their 1.1 s at 561 336 nodes): the same
e-matching-volume signature as bdd and eqsolve. The acgen ledger records the
N=13 point (egglog 34.8 s, ours 253 s) and why N=11 ships.

## Survivor policy on the merge-heavy rows

Two rows change under --union-by size (3 runs each at this commit, not part
of the default-flag campaign, which measures the shipped default rank):
math-microbenchmark rules-semi 1611 ms (rank) against roughly 600 ms (size),
and acgen rules-semi 23 309 ms (rank) against 9 100 ms (size), which is
parity with its naive column. Both are the class-growth-delta cost that the
directed policies bound; the policy is opt-in.
