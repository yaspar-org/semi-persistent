<!--
Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
SPDX-License-Identifier: Apache-2.0
-->
# E4a: dense-id tables in `extract_best` (A4)

**Change.** `extract_best`'s `best_cost` and `best_node` were `FastMap`s keyed by
class id. The ids are dense by construction (the fixpoint scan is over
`from_usize(0..n)` and every representative is one of those ids), so both are now
`Vec`s indexed directly, sized `n` up front.

`usize::MAX` is the "unset" marker for both tables. They are only ever written
together, and a cost of `usize::MAX` is never recorded (a saturating total cannot
be `<` the incumbent when the incumbent is already `usize::MAX`), so
`best_cost[i] != UNSET` holds exactly when class `i` has a best node. That is the
same predicate the map version spelled `get(..).unwrap_or(usize::MAX)`, and it is
what replaces the old `best_node.get(&root_repr)` reachability test.

`reconstruct` now takes `&[Cfg::G]` instead of `&FastMap`.

**Verdict: accepted.** 22-29% on the fixpoint-dominated rows, and the two rows
that do not improve are rows where the fixpoint is not the cost, established
below with counts rather than inferred.

## Bench

This experiment needed a benchmark that did not exist: `extract_best`'s only
non-test caller is `interpret.rs:226`, and `saturate_bench` never extracts. See
`egraph/benches/extract_bench.rs` (committed separately) for the three workload
shapes and why each is there.

## Numbers

Baseline `E4-before` = commit `6305cb9` (the bench commit).
Three runs, `MALLOC_MMAP_THRESHOLD_=65536`.

| bench | run 1 | run 2 | run 3 |
|---|---|---|---|
| `extract/tree20`   | −28.7% | −29.3% | −26.6% |
| `extract/tree200`  |  −0.4% |  −0.4% |  −0.8% |
| `extract/dag12`    |  +0.9% |  −0.9% |  +3.4% |
| `extract/dag16`    | +34.6% (p=0.00) | +10.2% (p=0.14) | +2.2% (p=0.73) |
| `extract/wide32`   | −22.1% | −22.5% | −21.7% |
| `extract/wide128`  |  −3.4% |  −2.8% |  −2.5% |

`tree20` and `wide32` are the rows where the fixpoint dominates, and they carry
the whole win. `dag16`'s readings are noise: its three intervals span −9% to
+48% and two of the three fail significance; a row whose per-iteration work is
building and dropping a 131 071-node term is not a measurement of a table
lookup. `dag12` straddles zero across runs for the same reason at smaller scale.

## Mechanism

`examples/extractprobe.rs` (added with this experiment) reports the structure
behind each row:

| workload | classes | fixpoint passes | scan visits | reconstructed term nodes |
|---|---|---|---|---|
| `tree20`   |  41 | 2 |  82 |      41 |
| `tree200`  | 401 | 2 | 802 |     401 |
| `dag12`    |  13 | 2 |  26 |   8 191 |
| `dag16`    |  17 | 2 |  34 | 131 071 |
| `wide32`   |  95 | 2 | 190 |      65 |
| `wide128`  | 383 | 2 | 766 |     257 |

This explains the split exactly. `tree20` does 82 scan visits against a 41-node
term: table lookups are most of its work, so removing the hashing shows up in
full. `dag16` does 34 scan visits against a 131 071-node term: the tables are
touched 34 times and the row is 99.97% `reconstruct`, so no table change could
move it. `wide32` sits with `tree20`; `wide128` and `tree200` sit in between for
the reason in the next section.

Allocation counts are not the mechanism here and are not improved: two `Vec`s of
length `n` replace two maps that grew to `n` entries, which is the same order of
allocation. The win is per-lookup instructions.

## Two findings for later experiments

Both came out of `extractprobe` and neither is acted on here.

**The fixpoint always converges in 2 passes on all six workloads**: one pass to
propagate costs and one to observe no change. **This closes E12 (C3).** Its
gating precondition was "measure pass counts first; if typical ≤ 3 close", and
the count is 2, including on `tree400`. The worklist rewrite would replace
`2 x n` scan visits with an edge traversal plus queue maintenance and could not
repay it. Recorded in `E12-worklist-fixpoint.md`.

**Extraction on a left-deep chain is quadratic in depth**, which nothing about
the shape justifies. Both the class count and the term size are O(depth):

```
tree depth scaling (min of 5 runs)
  depth  25:     19.7 us
  depth  50:     76.0 us   x3.86
  depth 100:    326.3 us   x4.30
  depth 200:  1 310.6 us   x4.02
  depth 400:  5 308.8 us   x4.05
```

Doubling depth quadruples time. The cause is in `reconstruct`, not in the
fixpoint: `for _ in 0..mult { children.push(t.clone()) }` deep-clones the whole
subterm and then drops the original, so a chain of depth *d* copies subterms of
size *d*, *d−1*, …: O(d²) node copies even though every `mult` is 1. This is
independent of memoization but lives in the same three lines E11 (C2) rewrites,
so it is folded into that experiment. It is also why `tree200` gains only 0.4%:
at depth 200 the row is dominated by this copying, not by the 802 table lookups.

## Correctness

`cargo test --workspace --release`: 81 test binaries, 0 failures.

**`extract_best` had no direct test.** The `.egg` fixtures reach it through the
interpreter, which prints the result without asserting it, so they covered "does
not crash" and nothing more. Given the change replaces two map absence-tests with
one sentinel comparison, that was not enough to gate on, so
`tests/extract_best.rs` was added with this experiment: cheapest-of-several in
one class, cost propagation from an improved child to its parent, shared-subterm
reproduction, and a cyclic class extracting through its grounded member. All four
assert the extracted term, not just that extraction succeeded.

One gap is deliberate and documented in that file: nothing tests `extract_best`
returning `None`, because `add` cannot build a class that fails to ground: a
node's children are ids that already exist, so every class is grounded through
the leaves it was built from. The `None` arm is defensive.

## Reproduce

```bash
export MALLOC_MMAP_THRESHOLD_=65536
cd egraph
cargo bench --bench extract_bench -- --baseline E4-before
cargo run --release --example extractprobe
```
