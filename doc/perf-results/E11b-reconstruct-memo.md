<!--
Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
SPDX-License-Identifier: Apache-2.0
-->
# E11b: memoizing `reconstruct` (C2): **rejected**

C2's second half: memoize `reconstruct` per class, so a class reachable through
*k* paths is built once instead of *k* times. Four variants were implemented and
measured. **All four regress the shared-subterm workload they were meant to fix,
except one row, and every variant regresses the tree and wide rows by 6-84%.**

The reason is not bookkeeping overhead. It is that **memoization cannot be
asymptotic while `reconstruct` returns an owned `Term`**. See "Why the premise
does not hold". That makes this a closed question rather than one to retry with a
better data structure.

## Why the premise does not hold

C2 reasoned that a class reached *k* times is "rebuilt *k* times", and a memo
removes *k−1* of those rebuilds. What the memo actually removes is *k−1*
*traversals*. It does not remove the *k−1* copies, because `Term` is a recursive
`enum` owning `Vec<Term>` children: a memo hit still has to `clone()` the stored
subterm to hand the caller something it can own.

So per occurrence of a shared class, the choice is:

| | cost |
|---|---|
| rebuild | walk the graph + allocate the subtree |
| memo hit | hash lookup + deep-copy the subtree |

Both are Θ(subterm size). The memo trades a graph walk for a hash probe and keeps
the allocation and copying, which is where the time actually goes: E11a already
established that in this function, copies dominate traversal: that is why
removing one redundant copy per child was worth 91-98%.

An asymptotic win here needs the *output* to be a DAG (`Rc<Term>`, or a term bank
with ids), so occurrences share storage instead of copying it. That is a change to
`extract_best`'s public return type and to every consumer of `Term`, not a change
to `reconstruct`. It is out of E11's scope and out of the plan's.

## The four variants

| | memo storage | when an entry is written |
|---|---|---|
| **A** | `Vec<Option<Term>>`, `vec![None; n]` | if a pre-pass counted > 1 reference |
| **B** | same | always |
| **C** | same | on the second visit to a class (`seen` flags) |
| **D** | `FastMap<usize, Term>`, empty | on the second visit (`seen` flags) |

**Variant B is the one to not write, and its failure is instructive.** Memoizing
unconditionally reintroduces the exact O(depth²) term E11a removed: storing an
entry costs `term.clone()`, so every level of the recursion deep-copies the
subtree it just built, which is what the old `for _ in 0..mult` loop did.
`extractprobe`'s chain scaling, min of 5:

| depth | E11a (shipped) | variant B |
|---|---|---|
|  25 |  1.5 µs |    28.6 µs |
|  50 |  2.9 µs |   100.0 µs |
| 100 |  8.2 µs |   379.7 µs |
| 200 | 16.0 µs | 1 528.3 µs |
| 400 | 31.6 µs | 6 262.3 µs |
| per-doubling ratio | **x1.98** | **x4.10** |

Variants A, C and D all gate the write so a singly-reached class stores nothing,
and all three keep the x1.9-2.0 ratio. A used a counting pre-pass; C and D detect
the second visit lazily, which is strictly better: the pre-pass is itself
O(graph), the same order as reconstructing a tree.

## Numbers

`extract_bench` against `E11b-before` (= `d3b5c20`, a fresh full-suite baseline:
E11a's absolute figures came from a filtered run and are not comparable).

| bench | variant A | variant C | **variant D** |
|---|---|---|---|
| `extract/tree20`  | +84.0% | +74.7% | **+9.6%** |
| `extract/tree200` | +31.4% | +31.2% | **+7.3%** |
| `extract/dag12`   | +30.5% | +41.2% | **+18.3%** |
| `extract/dag16`   | −17.8% | −18.5% | **−9.4%** |
| `extract/wide32`  | +59.8% | +56.1% | **+9.9%** |
| `extract/wide128` | +21.5% | +18.1% | **+6.2%** |

All `p = 0.00`. Variant A was run twice (+84.0/+84.1, −17.8/−18.2) and D three
times (`dag12` +18.3/+16.5, `dag16` −9.4/−10.1); the signs and magnitudes hold, so
none of this is protocol-item-6 layout noise.

**A → C → D isolates the cost to the dense memo table, not the memo logic.** A's
tree regression looked like the counting pre-pass, but C removes that pre-pass and
still reads +74.7%. What A and C share is `vec![None; n]`: `Term` is a large
non-`Copy` type, so a dense table allocates, zeroes and then drop-scans one slot
per class on *every* extraction, including the tree rows that have no sharing at
all. Replacing it with an initially-empty map (D) cuts the tree regression from
+75% to +9.6%.

This is worth recording as a limit on E4a's reasoning rather than a contradiction
of it. A dense `Vec` beat a map for the *cost* tables because `usize` and a class
id are word-sized and every slot is written. The same argument fails for a table
of `Term`, where the slots are large, most are never written, and construction and
teardown alone outweigh the hashing a map would charge.

## The one row that improves, and why it is not enough

`dag16` gains 9-10% under D. It is the workload with the most sharing (17 classes
producing a 131 071-node term), so it is where a memo hit's deep copy finally
beats a rebuild's graph walk plus allocation. `dag12`, the *same shape* four
levels shallower, regresses 16-18%: its subterms are small enough that the hash
probe and the `seen` write cost more than the walk they replace.

A change that helps one workload by 10%, hurts its smaller sibling by 17%, and
hurts every non-sharing workload by 6-10% is not a change to retain. The plan's
acceptance condition for E11 was "accept unless tree-shaped extraction regresses";
tree-shaped extraction regresses in all four variants.

## Correctness

Every variant passed `cargo test --release --test extract_best` (6 tests) before
being timed, and `extractprobe`'s checksums were identical to the shipped code's
at all five depths: the variants build the same terms, they just take longer to
do it. Nothing is retained, so nothing ships; `egraph/src/extract.rs` is unchanged
at `d3b5c20`.

## If this comes back

Not as memoization. The question C2 was reaching for is whether extraction should
return a shared DAG instead of an owned tree, and that is an API question with a
much larger payoff than 10% on one row: `dag16`'s output is 131 071 nodes
representing 17 distinct classes. Nothing in this experiment argues against that;
what it shows is that you cannot get any of its benefit while the return type is
`Term`.

## Reproduce

```bash
export MALLOC_MMAP_THRESHOLD_=65536
cd egraph
cargo bench --bench extract_bench -- --save-baseline E11b-before   # at d3b5c20
# apply a variant, then
cargo bench --bench extract_bench -- --baseline E11b-before
cargo run --release --example extractprobe
```
