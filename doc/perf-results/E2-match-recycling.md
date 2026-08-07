<!--
Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
SPDX-License-Identifier: Apache-2.0
-->
# E2 — match buffer recycling (A2)

**Change.** `run_step` emitted one `env.clone()` per solution, and `Match`'s
`Clone` allocates nine `Vec`s. The `Vec<Match>` was then dropped at the end of
every (rule, variant), freeing all nine per match. So each emitted match cost up
to nine allocations and nine frees, per query, per round.

Added `ematch::MatchPool`: a `Vec<Match>` plus a live length. `clear()` drops the
previous query's results by setting `len = 0` without releasing storage, and
`push` overwrites an existing slot via `Match::clone_from` (newly implemented —
nine `Vec::clone_from`s, which reuse capacity) instead of allocating a new
`Match`. Only the first query pays; after that the pool sits at its high-water
mark.

`run_query_into(plan, .., &mut pool)` is the new entry point. `run_query` stays,
wrapping it for tests, the REPL and `EGraph::run_query`. Both drivers hoist one
pool outside the round loop:

- `saturate` → `apply::apply_rule_pooled` (with `apply_rule` kept as the
  pool-allocating wrapper its ten test call sites use);
- `saturate_semi` → `run_rule_variant`, which takes the pool as a parameter. This
  is where reuse compounds: a semi-naive round runs one query per
  (rule, join atom), all with similar match counts.

`saturate_trace` still uses `run_query` — it prints every binding, so allocation
is not its cost.

**Verdict: accepted, and it is the largest win in the series so far.** 22-33% on
the rewrite-driven rows.

## Numbers

Baseline `E1-before` = commit `0a9b7cb`, i.e. **before E1**, so these are
cumulative over E1 + E2. E1's own contribution was 2-6%; the remainder is E2.
Three full-suite runs, `MALLOC_MMAP_THRESHOLD_=65536`.

| bench | run 1 | run 2 | run 3 | E1 alone | E2's share |
|---|---|---|---|---|---|
| `plain7/naive`  | −31.7% | −33.1% | −32.1% | −4.8% | ≈ −28% |
| `plain7/semi`   | −29.7% | −29.9% | −30.4% | −5.2% | ≈ −26% |
| `ac6/naive`     | −22.1% | −22.2% | −22.9% | −3.9% | ≈ −19% |
| `ac6/semi`      | −12.0% | −12.0% | −11.0% | −1.9% | ≈ −10% |
| `ac10/naive`    |  −9.7% |  −9.4% |  −9.4% | −0.6% | ≈  −9% |
| `ac10/semi`     | −11.8% | −11.2% | −11.4% | −1.3% | ≈ −10% |
| `accompl32`     |  −2.6% |  −3.5% |  −2.5% | +4.5% | n/a |
| `accompl64`     |  −1.2% |  −2.3% |  −1.5% | +4.2% | n/a |

Every row is `p = 0.00` on all three runs, and the spread between runs is under
1.5 points everywhere — no ambiguity to resolve here.

The completion rows are again the interesting case, and again not evidence about
this change: they do zero e-matching and their allocation counts are unchanged
(3931 / 7972, identical to E0). They read +4% under E1 and −2% under E2. Both
numbers are layout; E1's file explains the three checks that established that.

## Mechanism (allocation counts)

`examples/allocprobe.rs`, saturation region only.

| workload | E0 | after E1 | after E2 | E2 vs E1 |
|---|---|---|---|---|
| `plain7/naive` | 229 587 | 193 003 | **148 110** | −23.3% |
| `plain7/semi`  | 121 341 |  98 357 |  **75 159** | −23.6% |
| `ac6/naive`    |  62 768 |  58 680 |  **49 224** | −16.1% |
| `ac6/semi`     |       — |  27 174 |  **23 564** | −13.3% |
| `ac10/naive`   | 1 857 690 | 1 852 818 | **1 702 889** | −8.1% |
| `ac10/semi`    | 1 228 320 | 1 223 390 | **1 098 261** | −10.2% |
| `accompl32`    | 3 931 | 3 931 | 3 931 | 0 |
| `accompl64`    | 7 972 | 7 972 | 7 972 | 0 |

Bytes allocated tell the story more sharply than counts, because recycling
removes the *large* allocations (the rest-slice pools) rather than the small
ones: `plain7/naive` 27.5 MB → **11.1 MB** (−60%), `plain7/semi` 12.7 MB →
**4.6 MB** (−63%), `ac10/naive` 107.6 MB → **81.0 MB** (−25%). Peak live bytes
are unchanged, as expected — the pool holds the same data, it just stops
returning it to the allocator between queries.

Allocations per match step on `plain7/naive`: 1.01 (E0) → 0.85 (E1) → **0.65**.

## Why the win is bigger than the allocation count suggests

Counts fall 23% but time falls 32%. Three effects beyond the allocator call
itself:

- **Freeing is not free.** Each dropped `Match` was nine `dealloc`s that the
  count column above does not show (it counts allocations only). Recycling
  removes both sides.
- **The recycled buffers stay hot.** A pool slot reused across thousands of
  matches is in L1/L2; a fresh `Vec` is cold and, at these sizes, may come from
  a different arena each time.
- **`clone_from` on an adequately-sized destination is a `memcpy`** with no
  capacity check failure path, where `clone` is an allocate-then-copy.

## Correctness

`cargo test --workspace --release`: 80 test binaries, 0 failures.

The specific hazard this change introduces is stale slot contents: a slot beyond
`len` holds the previous query's match. `matches_mut`/`matches` return only
`&[..len]`, so a stale slot is unreachable and is fully overwritten by
`clone_from` before it can be observed. What would catch a mistake here is the
naive-vs-semi-naive equivalence tests in `saturate.rs` (they compare match sets
between the two drivers, both of which now use pools) and the `MatchSet`
cross-check tests in `ematch.rs`, which compare pooled output against the
independent SoA path.

## Reproduce

```bash
export MALLOC_MMAP_THRESHOLD_=65536
cd egraph
cargo bench --bench saturate_bench -- --baseline E1-before
cargo run --release --example allocprobe
```
