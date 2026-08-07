<!--
Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
SPDX-License-Identifier: Apache-2.0
-->
# E10 — branchless duplicate merge in `update_multiset` (B3) — **closed on its own gate**

B3 proposed rewriting `canon.rs`'s compaction loop — the one branching on
`buf[r].a == buf[w].a` to decide whether to merge a duplicate or advance the
write cursor — into a branchless form. Its gate, and the plan's own lowest
priority item: **only if a profile attributes measurable time to
`update_multiset`; else close.**

**`update_multiset` is called 0 times on every benchmark workload, and 118 times
across all 90 `.egg` fixtures, of which the duplicate branch is taken 8 times in
total.** There is no time to attribute. Closed without prototyping.

## Measured

A call counter in `update_multiset`, driven by an `acsite`/`complsite`-shaped
harness over the benchmark workloads:

| workload | `update_multiset` calls |
|---|---|
| `ac6/naive` | 0 |
| `ac6/semi` | 0 |
| `ac10/naive` | 0 |
| `ac10/semi` | 0 |
| `accompl32` | 0 |
| `accompl64` | 0 |

Then over the whole fixture corpus, which is the broadest AC workload in the
repo:

| corpus | calls | mean input | duplicate pairs merged |
|---|---|---|---|
| 90 `.egg` fixtures | 118 | small | **8** |

Per protocol item 10, the zero was checked against a counter proven capable of
firing before being believed: temporarily dumping from inside
`canon::tests`'s own `MSetCanon::canonize` call printed `1 calls, mean_in 3.00,
mean_out 2.00, dups 33.3%`. The instrumentation works; the benchmarks genuinely
do not reach it.

## Why the benchmarks never reach it

`update_multiset` runs only from `MSetCanon::canonize`, which is reached only
from `NodeStore::recanonize_node::<MSetCanon>` — the *rebuild* path for a dirty
MSet node. A second, independent probe (an `eprintln!` at that dispatch arm in
`node_store.rs:372`) also fired 0 times on all six workloads, confirming the
attribution rather than just the count.

The reason is structural. The AC benchmarks build one wide `add` node and then
rewrite *around* it; the completion benchmarks run with no rules at all, so
nothing merges classes underneath an existing MSet node. Recanonizing an MSet
node requires a union that changes one of its children's representatives, and
these workloads do not produce one.

So the situation resembles E9's — an optimization aimed at code no benchmark
executes — but the diagnosis is different and worth distinguishing. E9's target
was in a matcher engine with *no consumers at all*; this one is on a live,
correct, reachable path that simply is not exercised by the shapes in
`saturate_bench`. That is a gap in the bench suite as much as a property of the
code.

## What would have to be true for this to come back

Two things, together:

1. **A workload that repeatedly dirties MSet nodes** — one where unions merge
   classes that appear as children of AC nodes, round after round. The corpus
   reaches 118 calls; a workload would need orders of magnitude more before the
   loop is worth counting instructions in.
2. **Wide multisets with many duplicates.** The branch B3 targets is the
   *duplicate* arm, taken 8 times in 118 calls here. A branchless rewrite pays
   for itself when the branch is unpredictable, which needs a duplicate rate near
   50%, not near 7%.

If a caller ever shows up with both, the measurement is cheap: a call counter and
an in/out size ratio in `update_multiset`, which is what produced the table
above. Note also that the loop is already close to minimal — one compare, one
add, one conditional store — so the ceiling on a branchless rewrite is small even
where it applies. B3 was ranked last in the plan for that reason and the
measurement agrees.

## Reproduce

The instrumentation was temporary and is not retained. To recreate: process-global
atomics in `canon.rs`'s `update_multiset` counting calls plus input and output
lengths, dumped per workload from an `acsite`-shaped driver, and a fixture-sweep
test that runs every `tests/egg/*.egg` under `catch_unwind` and reports the
totals. Prove the counter can fire (dump it from `canon::tests`) before trusting
a zero.
