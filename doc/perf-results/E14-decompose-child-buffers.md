<!--
Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
SPDX-License-Identifier: Apache-2.0
-->
# E14: recycle decompose child buffers (A7): **accepted**

**Verdict: accepted. −13.5% on both `ac10` rows and −6 to −7.4% on both `ac6`
rows, reproducing within 0.5 points across three runs, confirmed standalone at
−12.7% with identical checksums. 30-41% fewer allocations.**

The three variadic decompose steps in the recursive matcher (`ExpandA`,
`DecomposeAC`, `DecomposeACI`) each allocated a fresh `Vec` per match step to
hold the node's children. They now borrow it from `MatchPool`.

## The plan pointed at dead code

A7 was written up against `ematch.rs`'s `ACDecompose`/`ACIDecompose` **frames**,
each of which stores `elems.to_vec()`, with the proposed fix being a shared
offset pool in the style of `Match`'s `seq_pool`/`set_pool`.

Instrumenting those three `to_vec()` sites recorded **zero clones** on every
workload tried: `ac6` and `ac10` under both drivers, the whole lib test suite,
and all 90 `.egg` fixtures. That is because `ematch.rs` contains **two** matcher
engines:

| engine | entry point | AC dispatch | used by |
|---|---|---|---|
| recursive DFS | `run_query_into` → `run_step` | `ematch.rs:578` | `saturate`, `apply`, `EGraph::run_query`: *everything* |
| frame machine | `MatchIterator::next_match` | `ematch.rs:1439` | `run_query_iter`, `collect_set`: lib tests only |

`MatchIterator` has no consumers outside `ematch.rs`'s own tests. The frames A7
names are only reachable through it, so the sites are real code that no
production path and no benchmark executes.

Verifying that before drawing the conclusion mattered, and the first attempt at
it was wrong twice: the counters were read from the `egg_tests` binary while the
frame machine is exercised only by *lib* tests (a different process: global
atomics do not cross binaries), and the reporting test was placed in a module
that sorts before `tests`, so it ran first. Driving `(add x:1 ..rest)` through
`collect_set` from inside `mod tests` made the counter read 2, which is what
established the instrumentation was sound and the zeros meant absence of
workload.

## Where the allocations actually were

The live recursive engine has the same shape of cost one level away, a fresh
`Vec` per *step* rather than per *frame*:

| workload | decompose steps | mean children | buffers | total allocs | share |
|---|---|---|---|---|---|
| `ac6/naive`  |   5 348 |  6.00 |  5 348 |    29 352 | 18.2% |
| `ac6/semi`   |   2 188 |  6.00 |  2 188 |    14 732 | 14.9% |
| `ac10/naive` | 141 902 | 10.00 | 141 902 | 1 070 299 | 39.8% |
| `ac10/semi`  |  93 172 | 10.00 |  93 172 |   682 741 | 40.9% |

The share column is allocations *removed*, not buffers created, because a `Vec`
grown from empty to 10 elements reallocates three times (4, 8, 16). 141 902 × 3 =
425 706 against the 425 702 the allocation counter actually shows: the
mechanism accounts for the measured drop to within 4 allocations out of a
million, which is the protocol item 5 check passing about as cleanly as it can.

## Design

`MatchPool` already exists to recycle per-match storage and is already threaded
to all three sites, so the buffers go there: two free-lists, one of `Vec<Cfg::G>`
for child ids (`ExpandA`, `DecomposeACI`) and one of `Vec<(Cfg::G, Cfg::M)>` for
`(id, multiplicity)` pairs (`DecomposeAC`).

Three choices worth recording:

**Lent by move, not by reference.** Each borrower passes `&mut pool` *down the
same call* that uses the buffer, so a `&mut` into the pool cannot coexist with
it. `take_id_buf` moves a buffer out and `give_id_buf` returns it. The upside is
that double-lending becomes unrepresentable rather than merely tested against;
the downside is that forgetting to return one leaks a single allocation, which is
a perf bug and not a correctness one.

**A free-list, not one slot per `step_idx`.** Nested decompose steps are live
simultaneously (a plan can decompose an AC node inside another one), so a single
slot per step index would need the plan's depth. `pop`/`push` gives correct
nesting for free and needs no bookkeeping.

**The free-lists deliberately survive `clear()`.** They hold no query state:
`seq_children`/`set_children`/`mset_children` all begin with `buf.clear()`, so
every borrower overwrites before reading. Surviving `clear` is the entire point.
That invariant is now load-bearing where it was previously incidental, so it is
stated at both the pool and the accessors, and the mutation table below covers
it.

## Numbers

`saturate_bench` against `E14-before` (= `7fa1467`), three runs:

| bench | run 1 | run 2 | run 3 | absolute after |
|---|---|---|---|---|
| `saturate/ac10/naive` | **−13.5%** | **−13.7%** | **−13.6%** | 67.9 ms (was 78.8) |
| `saturate/ac10/semi`  | **−13.3%** | **−13.5%** | **−13.3%** | 42.6 ms (was 49.2) |
| `saturate/ac6/naive`  | **−6.9%** | **−7.4%** | **−7.3%** | 2.20 ms (was 2.38) |
| `saturate/ac6/semi`   | **−5.7%** | **−6.0%** | **−5.4%** | 1.17 ms (was 1.24) |
| `saturate/plain7/semi`  | −1.4% | −2.3% | −2.1% | 7.32 ms |
| `saturate/plain7/naive` | −0.1% | +0.1% | +0.6% | 13.2 ms |
| `saturate/accompl32`  | −2.0% | −2.3% | −1.8% | 1.026 ms |
| `saturate/accompl64`  | −2.6% | −3.0% | −2.4% | 2.520 ms |

The four AC rows reproduce within 0.5 points and the row ordering tracks the
allocation table: `ac10` removes 40% of its allocations and gains 13.5%, `ac6`
removes 15-18% and gains 6-7%.

`plain7/naive` is the one row with no variadic steps at all (its patterns are
fixed-arity) and it is flat, as it must be. `plain7/semi` at −1.4 to −2.3% and
the two completion rows at −1.8 to −3.0% are small consistent gains from a
second-order effect rather than the mechanism: removing 40% of the allocator
traffic in one workload leaves the allocator's free lists in a less fragmented
state for every subsequent bench in the process. They are recorded as measured
but the change is not claimed to speed up completion, which does no matching at
all (it runs with no rules).

Standalone confirmation per protocol item 7, min of 40/200 reps:

| | baseline | pooled | |
|---|---|---|---|
| `ac10/naive` | 74.4503 ms | 65.0035 ms | **−12.7%** |
| `ac6/semi`   |  1.1906 ms |  1.1249 ms |  **−5.5%** |

−12.7% standalone against −13.5% in criterion, checksums identical (`ac10`
41920, `ac6` 17400). Criterion, the standalone site and the allocation counter
all agree, which is the bar protocol item 7 sets.

## Correctness

`cargo test --workspace --release`: 81 test binaries, 0 failures. `cargo fmt
--all --check` and `cargo clippy --release --all-targets` clean.

One test added, because the existing suite could not have caught a regression
here: every test went through `run_query`, which builds a *fresh* pool per call,
so no test ever ran a query against a pool that already held data.
`reused_pool_matches_a_fresh_pool` drives all four recycled-storage shapes
(plain join, `ExpandA`, `DecomposeAC`, `DecomposeACI`) twice, comparing a shared
pool against a fresh one.

Mutation-checked:

| mutation | result |
|---|---|
| drop `buf.clear()` from `mset_children` | **fails** the new test |
| drop `buf.clear()` from `set_children` | **fails** the new test |
| drop `buf.clear()` from `seq_children` | passes: see below |
| clear the free-lists inside `MatchPool::clear` | passes, correctly |
| never return a borrowed buffer | passes, correctly |
| return the buffer before filling it | passes, correctly |

The last three are correct survivals rather than coverage gaps. Clearing the
free-lists and leaking buffers both only give up recycling, which is a
performance change with no observable behavior; and lending by move makes
"return before use" fail to compile as an aliasing bug: the mutation had to be
written as returning a *different* empty `Vec`, which is merely wasteful.

`seq_children` needs its own note. The step *is* reached with a dirty buffer
(instrumenting it printed `len_before=3` on half the calls), so this is not the
frame-machine situation over again. `run_expand_a` reads a bounded prefix
(`pre`/`suf` window) and never the buffer's length, so trailing junk past the
node's real children is invisible to it. A test asserting otherwise would be
asserting something untrue. The `clear` stays because relying on that is fragile
for no gain.

## Reproduce

```bash
export MALLOC_MMAP_THRESHOLD_=65536
cd egraph
cargo bench --bench saturate_bench -- --save-baseline E14-before   # at 7fa1467
# apply the change, then
cargo bench --bench saturate_bench -- --baseline E14-before
cargo run --release --example acsite -- 10 40 naive
cargo run --release --example acsite -- 6 200 semi
cargo run --release --example allocprobe
```

The reachability instrumentation was temporary and is not retained. To recreate:
a `to_vec_probed(tag)` shim over `[T]::to_vec` plus process-global atomics, wired
into the three frame sites *and* the three live-engine sites, reported from a
test inside `mod tests` that drives a rest-variable pattern itself rather than
depending on test order: both mistakes made the first time are easy to repeat.
