<!--
Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
SPDX-License-Identifier: Apache-2.0
-->
# E8 — union-find path compression (S1) — **closed on its own gate**

S1 was framed as a study, not a recommendation: compare on-the-fly compression
(status quo) against a systematic sweep after each `rebuild` and against a
threshold sweep. Its gate was instrumentation first — hops per `find_const` plus a
chain-length histogram — and **prototype the sweeps only if mean hops ≫ 1**.

**Mean hops is 0.000 to 0.433, and the deepest chain observed anywhere is 2.**
There is nothing for a sweep to compress. Closed without prototyping.

## Measured

A temporary counter in `find_const` and `find` (the latter measuring the chain
*before* it compresses, so the numbers are comparable), over every benchmark
workload:

| workload | fn | calls | mean hops | h = 0 | h = 1 | max |
|---|---|---|---|---|---|---|
| `plain7/naive` | `find_const` |   160 238 | 0.433 | 56.7% | 43.2% | **2** |
| `plain7/naive` | `find`       |   635 510 | 0.276 | 72.4% | 27.6% | **2** |
| `plain7/semi`  | `find_const` |   103 875 | 0.388 | 61.6% | 38.0% | **2** |
| `plain7/semi`  | `find`       |   306 467 | 0.276 | 72.5% | 27.3% | **2** |
| `ac6/naive`    | `find_const` |    77 152 | 0.002 | 99.8% |  0.2% | 1 |
| `ac6/naive`    | `find`       |    84 798 | 0.119 | 88.1% | 11.9% | 1 |
| `ac10/naive`   | `find_const` | 3 033 034 | 0.000 | 100.0% | 0.0% | 1 |
| `ac10/naive`   | `find`       | 2 661 484 | 0.096 | 90.4% |  9.6% | 1 |
| `ac10/semi`    | `find_const` | 2 027 521 | 0.001 | 99.9% |  0.1% | 1 |
| `ac10/semi`    | `find`       | 1 748 904 | 0.096 | 90.4% |  9.6% | 1 |
| `accompl32`    | `find_const` |     3 607 | 0.112 | 88.8% | 11.2% | 1 |
| `accompl64`    | `find_const` |     7 287 | 0.113 | 88.7% | 11.3% | 1 |

`find` is never called on the completion workloads (they run with no rules), which
is why those rows are `find_const` only.

## Why the trees are this flat

Three things compound, and each is already in the code:

1. **Union by rank** keeps height logarithmic in class size — and the classes here
   are small, so log of them is 1 or 2.
2. **On-the-fly compression in `find`** flattens every chain it walks, and `find`
   is called 2.7M times on `ac10/naive` against 3.0M `find_const` calls. The
   mutating path runs at comparable volume to the read-only one, so it is
   continuously doing the work a sweep would do in bulk.
3. **`rebuild` recanonicalizes eagerly.** Node children are rewritten to
   representatives every round, so the ids that later get looked up are mostly
   already roots — which is exactly what the h = 0 column shows: 100% on
   `ac10/naive`.

The three candidate policies differ only in *when* chains get flattened. When the
chains are at most 2 links and 88-100% of lookups start at a root, all three
policies do nearly the same amount of work, and the two sweep variants add an
O(n) pass per round to save at most one pointer hop on a tenth of the lookups.

## What this says about the concurrency constraint

The plan noted that `find_const` deliberately does not mutate so it can run
concurrently, and that this constraint stands. It does — and this measurement makes
the constraint free rather than a tradeoff. The reason a non-mutating `find_const`
is normally a cost is that it forgoes compression; here there is essentially
nothing to forgo, since its mean is 0.000-0.433 hops without compressing anything.

A systematic sweep placed before `mark()` (the plan's suggestion for avoiding the
diff-log cost) would still be the right shape *if* the numbers had justified one.
Recorded here so that the design note survives the close.

## If this comes back

The measurement is workload-dependent, and these workloads have small classes.
A workload that merges large classes in a pattern union-by-rank handles poorly —
in particular one that leans on `union_directed`, which explicitly overrides
union-by-rank and whose doc comment already warns that ranks can climb faster and
`find` may be slower — could produce deeper trees. The probe is ~20 lines
(a hop counter in `find_const`/`find` plus a histogram dump); re-add it against
the workload in question rather than assuming these numbers transfer.

## Reproduce

The instrumentation was temporary and is not retained. To recreate: count loop
iterations in `union_find.rs`'s `find_const`, count the pre-compression chain
length in `find`, accumulate into a thread-local histogram, and dump per workload
from a driver shaped like `examples/acsite.rs`.
