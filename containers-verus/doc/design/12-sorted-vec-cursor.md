<!--
Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
SPDX-License-Identifier: Apache-2.0
-->
# Verified Sorted-Vector Cursor

This chapter describes `containers-verus/src/sorted_vec_cursor.rs`, the cursor
used by the e-graph's leapfrog join.

The subject is an algorithm over an existing sorted slice rather than a
container representation. Its central property is that `seek` cannot skip a key
that could participate in a join.

## 1. Algorithm

The cursor stores a slice and a forward-only position. `seek(target)`:

1. returns immediately if exhausted or already at a key at least `target`;
2. doubles a step from the current position while the probed key is below the
   target;
3. clamps the resulting window to the slice; and
4. uses a lower-bound bisection inside that window.

The gallop costs O(log d) comparisons in the distance advanced, followed by
the bounded bisection. The implementation uses `step < n - lo` rather than
`lo + step < n`, making overflow freedom follow directly from the loop
invariant.

Performance is target and workload dependent. Compare cursor strategies with
the Criterion benches under `containers-verus/benches/` and
`containers-conformance/benches/`; no fixed speedup is part of this design.

## 2. Model

`nat_model(slice)` projects each dense id to a natural number in slice order.
`cursor_wf` requires:

- strict ordering of the model; and
- `pos <= len`.

The target index is the shared B+ tree specification:

```text
seek_target_idx(model, target)
    = number of model keys strictly below target
```

The cursor postcondition is:

```text
pos_after = max(pos_before, seek_target_idx(model, target))
```

The `max` captures forward-only semantics: seeking behind the current cursor
does not move it backward.

## 3. Soundness Theorems

The verified surface establishes:

- a positioned cursor holds a key at least the target;
- every skipped key is strictly below the target;
- if the target is present at or after the old position, seek lands on it;
- seek never decreases the position;
- exhaustion means no remaining key reaches the target; and
- repeated `step` enumerates the strictly increasing suffix.

Every slice access and arithmetic operation is also proved in bounds.

`BPlusCursor` and `SortedVecCursor` reuse the same target-index specification:

| Cursor | Seek result |
|---|---|
| B+ tree | absolute lower bound |
| sorted vector | maximum of current position and lower bound |

Leapfrog only performs monotone seeks, so both refine its cursor requirement.

## 4. Gallop Invariant

The load-bearing loop facts are:

```text
old_pos <= lo < n
model[lo] < target
1 <= step <= lo + 1
```

`model[lo] < target` justifies searching `lo + 1 .. hi`: excluding `lo`
cannot skip the answer. The ladder bound proves progress and prevents doubling
from overflowing.

The lower-bound bisection maintains that every element before its split is
below the target and every element after it is at least the target. Shared
uniqueness lemmas identify the resulting split with `seek_target_idx`.

## 5. Runtime Evidence

Property tests run the executable cursor with Verus contracts erased and
compare it with a linear lower-bound oracle across both supported id widths.
They cover:

- empty and singleton slices;
- repeated forward seeks;
- already-satisfied and exhausted states;
- large jumps and near-end windows; and
- step/seek composition.

These tests guard the executable build and supplement the universal Verus
proof; they are not the source of the soundness claim.

## 6. Consumer Boundary

`src/sorted_cursor.rs` defines the plain-Rust `SortedCursor` trait used by
leapfrog and its `Difference` combinator. The trait implementation delegates to
the verified inherent methods.

The trait returns `Option` from `key` and `step`, so it checks cursor validity
before calling the verified operation whose core contract assumes a valid
position.

The e-graph re-exports this cursor rather than maintaining a second
implementation. Compilation therefore ties the verified body to the join's
cursor type.

## 7. Scope

Verified:

- construction and position validity;
- `key`, `step`, and forward `seek`;
- lower-bound soundness and no-skip theorems; and
- bounds/overflow safety.

Not proved:

- a machine-level O(log d) cost theorem; or
- a universal performance advantage over another search strategy.

Run `cargo verus verify` for the current verification result.

---
[Table of Contents](00-table-of-contents.md)
