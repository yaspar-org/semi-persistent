<!--
Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
SPDX-License-Identifier: Apache-2.0
-->
# The Layered Span Map: Incremental Maintenance over a Build-Once Index

This chapter describes `containers-verus/src/layered_span_map.rs`, which extends
[chapter 15](15-dense-span-map.md) with a second generation. It states the
representation chosen, the two alternatives rejected and why, what the proofs
establish about the combined view, and one obligation the container places on
its caller that the container cannot check.

Deployment status: `LayeredSpanMap` is implemented and verified, and the
engine does not enable it. The engine's per-round index builds run on the
`DenseSpanMap` stamped-reuse path (chapter 15), whose measured build cost
leaves the layered scheme nothing to recover on the engine's workloads.
This chapter records the design and its proofs; revisit the wiring only if
an index-build share is measured that the stamped-reuse path does not
already cover.

## 1. The number this exists to fix

`comparison/semi-persistence/semi-persistence.md` section 5 measures incremental
saturation on a base of one million nodes. One round of matching after an
assertion batch costs us **353 ms**; egglog pays **1.8 ms** for the same cycle in
scope. The gap is not push or pop, which our semi-persistence already wins: it is
that after a small assertion batch we re-match the whole base and they match the
delta.

Index rebuilding is part of that cost. Chapter 6 rebuilds all four index families
from scratch every round, which is O(base) per round no matter how few keys the
round touched. A round that adds a hundred nodes to a million-node base pays for
a million.

## 2. The representation

```rust
LayeredSpanMap<V> {
    base:    DenseSpanMap<V>,   // the previous generation
    delta:   DenseSpanMap<V>,   // this generation's additions, same key space
    invalid: Vec<usize>,        // strictly ascending keys whose base bucket is dropped
}
```

The logical contents of key `k` are

```text
view(k) == (if invalidated(k) { empty } else { base.view(k) }) ++ delta.view(k)
```

and `refines()` states the same thing as a single stream, so a caller reasons
about one sequence per key rather than about two generations:

```text
view(k) == key_slice(base_stream.filter(key not invalidated) ++ delta_stream, k)
```

The two statements are the same because `key_slice` distributes over
concatenation (`lemma_key_slice_add`) and dropping the invalidated keys empties
exactly those keys (`lemma_key_slice_filter_invalid`).

**Invalidation is per key, not per (key, value) pair.** This is the decision the
module turns on. A per-pair tombstone set makes the surviving base bucket a
subsequence of a contiguous run rather than a contiguous run, and a
non-contiguous segment cannot be handed to the galloping seek that chapter 12
verifies and chapter 6 uses. Serving a per-pair tombstone set on the read path
costs either a membership test per element, which turns an O(log n) seek into an
O(n) filtered scan, or a materialization of the filtered bucket, which is the
O(base) rebuild the layering exists to remove. Per-key invalidation keeps both
segments contiguous, so `get` returns two slices and the seek is unchanged.

Per-key granularity is also what the consumer produces. A merge changes canonical
representatives, and the index families are keyed by canonical representative, so
a merge invalidates the merged classes' buckets in their entirety. The consumer
does not have a set of scattered dead pairs; it has a set of dead keys.

## 3. Read-path cost of invalidation

`get(k)` performs one binary search over `invalid` (O(log t) in the number of
invalidated keys, `t`), then two array indexes into the two span tables, and
returns two slices. It touches no value and copies nothing. `is_invalidated` is
the only part of the read path invalidation adds.

**A bitset over the key space was rejected.** It answers in one test instead of
O(log t), but it costs O(num_keys) to allocate and clear every round, and
num_keys is the span-table length, which chapter 6 records at roughly 2.4 M keys
per round on the rules encoding. Reintroducing an O(num_keys) per-round cost is
the thing the layering removes, so the O(touched) representation wins on the
metric that motivated the work. Which one is faster in wall-clock terms is a
measurement nobody has taken; if a workload is measured with large `t` and a
small key space, the bitset is the fix.

## 4. Layer count and the flatten threshold

**Exactly one delta layer.** Stacking N generations would make `get` return N
slices and turn the consumer's seek into an N-way merge, which moves cost onto
the read path. The read path is the hot path: leapfrog join probes far more often
than the index is built. So the layer count is pinned at two and the cost is
moved into a rebuild.

`flatten` collapses both generations into a single `DenseSpanMap` with the same
per-key contents, and `needs_flatten` is the threshold predicate:
`delta + invalid > base / 4`. The constant `c = 1/4` mirrors the rebuild fallback
the e-graph's cache layer already uses (commit a8a4187), so the two amortization
policies in the system agree rather than each picking their own.

`flatten`'s rebuilt stream is grouped by key rather than in original stream
order. That is sound because a key's slice is the stream's filter down to that
key, and filtering ignores the positions of other keys' entries. The proof that
`flatten` preserves every key's contents is what makes the compaction policy
sound: without it, a flatten is a silent opportunity to reorder or drop.

**The operation that implements the policy is `replace_delta`.** Round N+1 hands
in the accumulated delta stream and the accumulated invalidations; the base
carries over untouched and is never read. Its contract is `try_with_delta`'s with
`base_stream()` and `base_view()` carried through from the receiver, so a caller
can chain rounds without re-establishing anything about the base. The previous
delta generation is discarded, which is why the caller accumulates the stream
rather than handing in only the newest round's entries.

`into_base` is the O(1) way back to a `DenseSpanMap`. It returns the base
generation and **discards the delta and the invalidations**: it is not the
logical view. A caller that wants the logical contents as one map wants
`flatten`. Both are stated in the ensures so the two are not confusable:
`into_base` gives `r.view() == self.base_view()`, `flatten` gives
`r.view()[k] == self.view()[k]`.

**What this costs per round, stated honestly.** Installing a generation is
O(delta + invalid): the base is not read. It is not O(touched) in the strict
sense across a period, because `replace_delta` rebuilds the delta map from the
accumulated stream, which is O(accumulated delta) and bounded by `c * base`.
Against the current O(base) every round that is bounded by a factor of four in
the worst case and much better immediately after a flatten. True O(touched) per
round requires N layers, which is the read amplification this design refuses.
Revisit only if the index build is measured to dominate after this change lands.

> **Correction, 2026-08-16: the cost above omits the span-table term. Do not
> cite the paragraph above.** Installing a generation is O(delta + invalid +
> num_keys), not O(delta + invalid). `replace_delta` builds the delta generation
> with `DenseSpanMap::build`, whose span table is dense over the whole key space:
> a build writes `num_keys` counts, `num_keys` offsets, `num_keys` cursors and
> `num_keys` spans however few values the stream carries. On the E6 two-round
> cycle at S = 1e6 the delta carries 46 touched nodes and 23 `by_child_pos`
> entries against a key bound of 1,002,009, and the install costs 19.6 ms against
> 0.07 ms of matching in the round it feeds
> (`comparison/span-table-sparsity.md` section 3). The omitted term is three
> orders of magnitude larger than the one that was stated. The remedy is a build
> path proportional to the occupied keys, measured at 0.010 ms for the same
> install; section 7 of that document states the container change it needs. That
> container change has since landed as `DenseSpanMap::build_in`
> (`15-dense-span-map.md` section 7), but `replace_delta` still builds its delta
> generation with the dense path, so the 19.6 ms stands until it is switched.

## 5. In-place refresh of one `DenseSpanMap`, rejected

Appending to an interior bucket of a single `DenseSpanMap` is not possible
without moving data. The spans tile the pool exactly, so bucket `k` is
immediately followed by bucket `k+1`, and inserting one value into bucket `k`
shifts every value after it and rewrites every span from `k+1` onward. That is
O(pool) per insertion and O(pool) per round even for a single touched key, which
is the cost being removed. Reserving slack per bucket would break the tiling
invariant, and the tiling is what `lemma_spans_disjoint` derives disjointness
from, so the container's central safety property would have to be reproved
against a weaker invariant for no gain on the read path. Layering leaves
`DenseSpanMap` and its proofs untouched.

## 6. Cross-generation sortedness, and the obligation it rests on

`lemma_concat_sorted` proves that concatenating two sorted sequences is sorted
**when every element of the first precedes every element of the second**.
`lemma_view_sorted` applies it: given both generations' streams sorted by a
relation and that separation hypothesis at key `k`, key `k`'s logical slice is
sorted, so the consumer may treat the two segments as one sorted run.

**The separation hypothesis is the caller's obligation and the container cannot
check it.** It is stated as a hypothesis, not asserted, because it is a property
of how the caller assigns values across generations.

For the e-graph the hypothesis holds for keys that receive only new nodes: node
ids are append-only and the build visits them in ascending order, so every delta
id exceeds every base id. **It does not hold for a key that receives re-filed
nodes.** When classes `r1` and `r2` merge into `r1`, the nodes that were filed
under `r2` are re-filed under `r1` carrying their original ids, which interleave
with `r1`'s existing base ids. The concatenation for key `r1` is then two sorted
runs that overlap, and treating it as one sorted run would make the galloping
seek skip matches. That is a latent trap with a specific trigger: it fires the
first time a merge target's bucket is left live while receiving re-filed nodes.

The fix is a condition on the invalidation set, and it is cheap: **invalidate
every key whose bucket receives re-filed entries, not only the keys that lose
them.** Invalidating `r1` as well as `r2` empties `r1`'s base segment, so
separation holds trivially, and the surviving entries are re-filed into the delta
in ascending id order. Stage 4 must establish this when it builds the
invalidation set; the container proves the consequence, not the premise.

## 7. Trust classification and status

The module adds **no `external_body` markers**: the default-build count is
unchanged at 27 and the `literal-types` count at 5. There are no `admit`s or
`assume`s. The public surface is total, so the partial-API allowlist does not
grow: `get`, `key_len`, `is_invalidated`, `needs_flatten` and `flatten` carry no
`requires`, and their postconditions are conditioned on `wf()` instead.
`try_with_delta` conditions its `wf()` conclusion on the base's, which is how the
caller chains generations: `try_build_base` and `flatten` are the two sources of
a well-formed base.

Whole-crate verification goes 1669 to 1696 conditions, 0 errors, with and without
`literal-types`. The module verifies in 10.0 s with no `#[verifier::rlimit]` and
no `spinoff_prover`.

`containers-conformance/tests/layered_span_map_differential.rs` runs 14 tests
against a `HashMap<usize, Vec<V>>` oracle written from the definition of the
logical view: randomized base, delta and invalidated-key inputs; the
ascending-id shape the consumer produces, which checks separation and the sorted
concatenation; `flatten` equivalence and round trip; the threshold predicate; and
rejection of an unsorted, repeated or out-of-range invalidated-key list.

---
[← Table of Contents](00-table-of-contents.md)
