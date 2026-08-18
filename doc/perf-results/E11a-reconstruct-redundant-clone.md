<!--
Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
SPDX-License-Identifier: Apache-2.0
-->
# E11a: the redundant clone in `reconstruct`

**Change.** `reconstruct` emitted a child term `mult` times as:

```rust
let t = reconstruct(eg, best_node, eg.find_const(child));
for _ in 0..mult {
    children.push(t.clone());
}
```

`t` is a freshly built `Term` that nothing else owns, and it is dropped at the end
of the closure. So the loop deep-copied it `mult` times and threw the original
away. Now it clones `mult - 1` times and moves the original in:

```rust
for _ in 1..mult { children.push(t.clone()); }
children.push(t);
```

**Verdict: accepted. 91-98% on every extraction row.** This is by far the largest
win in the series, and it is not a constant factor: it removes an asymptotic
term.

## Why it is asymptotic

`Term` is a recursive `enum` with `Vec<Term>` children, so `clone` is a deep copy
of the whole subtree. Every `mult` in a fixed-arity graph is 1, so the old loop
ran exactly once, and that one iteration copied everything the recursive call had
just built.

That makes the copying recursive too. Extracting a left-deep chain of depth *d*
copied a subterm of size *d−1* at the top level, *d−2* below it, and so on:
**O(d²) node copies to produce a *d*-node result.** The fix makes it O(d).

`examples/extractprobe.rs` measures the chain directly (min of 5, µs):

| depth | before | after | before ratio | after ratio |
|---|---|---|---|---|
|  25 |    19.7 |  1.5 | — | — |
|  50 |    76.0 |  2.9 | x3.86 | x1.97 |
| 100 |   326.3 |  8.2 | x4.30 | x2.79 |
| 200 | 1 310.6 | 16.0 | x4.02 | x1.95 |
| 400 | 5 308.8 | 31.6 | x4.05 | x1.98 |

Doubling the depth quadrupled the time before and doubles it now. At depth 400
that is **168x**. Checksums are identical at every depth, which is what says the
two versions build the same term.

## Numbers

`extract_bench`, against `E4-before` (= `6305cb9`), so cumulative with E4a, but
E4a's contribution was 0.4-29% and this is 91-98%, so the attribution is not in
doubt.

| bench | change | absolute after |
|---|---|---|
| `extract/tree20`  | **−91.9%** |   1.41 µs |
| `extract/tree200` | **−98.5%** |  22.4 µs |
| `extract/dag12`   | **−91.0%** | 335.3 µs |
| `extract/dag16`   | **−93.8%** |   7.95 ms |
| `extract/wide32`  | **−93.6%** |   2.87 µs |
| `extract/wide128` | **−97.6%** |  15.5 µs |

All `p = 0.00`. The larger workloads gain more, as an asymptotic fix should:
`tree200` (−98.5%) beats `tree20` (−91.9%), `wide128` (−97.6%) beats `wide32`
(−93.6%).

`dag16` drops from 127 ms to 7.95 ms. Its per-iteration work is building a
131 071-node term, and it was doing that ~16x over.

## Note on the DAG rows and C2

C2 proposed memoizing `reconstruct` per class, because a class reachable through
*k* paths is rebuilt *k* times. That is still true after this change (the DAG
rows still build every path) and it is a separate experiment (E11b). This change
is not memoization: it removes copies that were redundant on *one* path, which is
why it helps the tree rows (where there is no sharing at all) as much as the DAG
rows.

The two compose rather than overlap: this one makes each path cheap, memoization
would remove paths. C2's premise was always about the DAG case; what this shows is
that most of the DAG case's cost was not sharing but the copy, since `dag16`
improved 93.8% before any memo existed.

## Correctness

`cargo test --workspace --release`: 81 test binaries, 0 failures.

The specific hazard is the loop bound: `1..mult` where the old code had `0..mult`.
If `mult` were ever 0 the old code emitted nothing and `1..0` also emits nothing,
but the unconditional `children.push(t)` after it would emit one, so an explicit
`if mult == 0 { return; }` guard precedes it.

No existing test exercised `mult > 1`, because only multiset ops report it, so
`multiset_multiplicity_is_reproduced_exactly` was added to
`tests/extract_best.rs`: `add(a, a, a, b)` must extract with exactly three `(a)`
and one `(b)`. It was mutation-checked: changing the bound to `2..mult` fails
that test and no other.

## Reproduce

```bash
export MALLOC_MMAP_THRESHOLD_=65536
cd egraph
cargo bench --bench extract_bench -- --baseline E4-before
cargo run --release --example extractprobe
```
