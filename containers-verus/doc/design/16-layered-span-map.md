<!--
Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
SPDX-License-Identifier: Apache-2.0
-->
# Layered Span Map

`LayeredSpanMap` extends [the dense span map](15-dense-span-map.md) with one
incremental generation. It is implemented and verified, but the e-graph does
not currently enable it.

The design preserves the base value pool across updates. It does not yet make
generation installation proportional only to touched keys, because the delta
still uses a dense span table.

## 1. Representation

```rust
LayeredSpanMap<V> {
    base: DenseSpanMap<V>,
    delta: DenseSpanMap<V>,
    invalid: Vec<usize>,
}
```

`invalid` is strictly ascending and contains keys whose base bucket must not be
read. The logical value at key `k` is:

```text
view(k) ==
    (if invalidated(k) { empty } else { base.view(k) })
    ++ delta.view(k)
```

The corresponding logical stream is the base stream with invalidated keys
removed, followed by the delta stream. `refines()` proves that filtering this
stream by key yields `view(k)`.

## 2. Per-Key Invalidation

Invalidation is per key, not per `(key, value)` pair. Per-pair tombstones would
make a base bucket non-contiguous. A non-contiguous bucket cannot be passed
directly to the verified galloping cursor without either:

- testing tombstone membership while scanning; or
- materializing a filtered bucket.

Per-key invalidation keeps the base and delta portions contiguous, so `get(k)`
returns two slices. It adds one binary search over `invalid`.

This granularity also matches representative changes in the e-graph: when a
class merge re-files entries, the affected index buckets are replaced as
whole buckets.

## 3. One Delta Layer

The map has exactly one delta generation. Additional generations would make a
lookup return an unbounded number of slices and require an N-way merge on the
read path.

`replace_delta` discards the old delta and installs a complete accumulated
delta over the same base. The caller must therefore pass all additions since
the base generation, not only the newest round.

`into_base` is an O(1) move that discards the delta and invalidations. It does
not return the logical view. `flatten` is the operation that materializes the
logical view as one `DenseSpanMap`.

## 4. Actual Costs

Let:

- `b` be the base value count;
- `d` be the supplied delta value count;
- `i` be the invalidated-key count; and
- `k` be the dense key-space size.

The current implementation has these costs:

| Operation | Time |
|---|---:|
| `get(key)` | O(log i) plus two span lookups |
| `try_with_delta` / `replace_delta` | O(d + i + k) |
| `into_base` | O(1) |
| `flatten` | O(b + d + k) |

The `+ k` term in delta installation is essential:
`DenseSpanMap::build` starts with an empty `SpanArena` and grows its span table
to the complete key space. Its counting, extent, and placement passes are
sparse, but this fresh-table growth remains O(k). The operation avoids
rebuilding or scanning the base value pool, but it is not strictly O(touched).

`needs_flatten` returns true when `d + i > b / 4`. This bounds accumulated
delta size relative to the base, but it does not amortize away the dense
span-table term.

To obtain ordinary O(d + i) installation, the layered map could retain and
recycle the previous delta's sufficiently large `SpanArena` through
`DenseSpanMap::build_in`. Table growth would still cost the number of missing
slots, and generation-stamp exhaustion would still require an exceptional
O(table length) clear. That change must preserve the same per-key slice
contract before the e-graph enables this structure.

## 5. Sortedness Across Generations

`lemma_concat_sorted` proves that two sorted slices concatenate to a sorted
slice only when every base element precedes every delta element. This separation
hypothesis belongs to the caller; the container cannot infer it from the two
maps.

Append-only node ids satisfy separation for buckets that receive only new
nodes. Re-filed old nodes can violate it. If classes `r1` and `r2` merge into
`r1`, entries formerly filed under `r2` may interleave with `r1`'s base ids.

The caller must therefore invalidate every destination bucket that receives
re-filed entries, as well as every bucket that loses them. The replacement
delta then contains the complete surviving bucket in sorted order, while the
base segment is empty.

## 6. Rejected Alternatives

### Per-Pair Tombstones

Rejected because they destroy contiguous slices or add per-element filtering
to the read path.

### Unbounded Layer Stacking

Rejected because lookup and seek costs grow with the number of generations.

### In-Place Interior Insertion

A `DenseSpanMap` pool is tiled by adjacent spans. Inserting into an interior
bucket shifts later values and rewrites later spans, which is O(pool) and
invalidates the simple disjoint-span proof.

### Dense Invalidation Bitset

A bitset gives O(1) membership but costs O(k) to initialize or clear. It may be
appropriate when invalidations are dense; the current sorted list favors small
`i`.

## 7. Verification

The module proves:

- equivalence of the two-segment view and logical-stream refinement;
- exact invalidation behavior;
- validation of sorted, unique, in-range invalidation keys;
- preservation of the base across delta replacement;
- `flatten` equivalence for every key;
- the flatten-threshold predicate; and
- sorted concatenation under the explicit separation hypothesis.

The public operations are total and add no trusted `external_body`.
Differential tests compare the view with a `HashMap<usize, Vec<V>>` oracle,
including randomized invalidations, flattening, threshold behavior, sortedness,
and invalid input.

---
[Table of Contents](00-table-of-contents.md)
