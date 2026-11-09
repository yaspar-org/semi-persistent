<!--
Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
SPDX-License-Identifier: Apache-2.0
-->
# 21. The Abstract-Value Pool

[← 20 Hot-Path Discipline](20-hot-path-discipline.md) · [Table of contents](00-table-of-contents.md)

Status: task specification for the branch `abs-class-storage`, PR 2 of 4.
Nothing in this chapter is implemented yet. Signatures marked "proposed" are
starting points, and the student may change them under the constraints stated
here.

## 1. What the PR delivers

The PR gives every e-class an optional abstract value stored in the class
layer. The class layer is `containers-verus/src/eclasses.rs`, and
`egraph::EClasses` and `egraph::UnionFind` are type aliases of it. The
design follows the storage proposal in
[eclass-analysis.md §4](../../../egraph/doc/future/eclass-analysis.md#4-storage):
a handle in `ClassData`, values in a pool under the same mark.

The PR delivers five things:

1. a field `abs` in `ClassData`, a handle into a new abstract-value pool;
2. the pool itself, a semi-persistent vector of opaque fixed-width `Copy`
   entries, marked and restored with the other components;
3. `MergeInfo::absorbed_abs`, so the caller reads the absorbed class's value
   after a merge and writes the combined value;
4. invariant W8 in `eg_model_wf`, preserved by every operation;
5. the archive extension, so `restore` returns every handle and every pool
   entry to its state at the matching mark.

The PR does not compute abstract values, meets or reductions. The sibling
branch `abs-saturation-engine` (PR 3) computes the meet on a merge and calls
this API. The sibling branch `abs-domain-registry` (PR 4) defines the
fixed-width entry format. The sibling branch `abs-surface-syntax` (PR 1)
defines the input syntax. This crate must not depend on `abstract-domains`.

## 2. Proposed API

All signatures in this section are proposals.

### 2.1 Entry type

The pool stores entries of a type parameter `A: Copy + Default`. The class
layer never inspects an entry; it stores, copies and restores it. The width of
`A` is fixed by `abs-domain-registry`. A default `A = NoAbs`, a zero-sized
unit type, keeps existing instantiations source-compatible.

```rust
// proposed: EClasses gains the entry type after the store policy.
pub struct EClasses<T, K, L, N, J, const TRACK: bool, const PROOFS: bool,
                    P = HotFirst, A = NoAbs>
where
    // existing bounds, plus:
    P: PlainFamily<A, usize, TRACK>,
    A: Copy + Default;
```

### 2.2 Class payload and merge result

```rust
// proposed
pub struct ClassData<L: DenseId, T: DenseId> {
    // existing fields: use_list, min_row, atomic, matchable, size
    pub abs: Option<<T as DenseId>::Index>,
}

pub struct MergeInfo<T: DenseId, L: DenseId> {
    // existing fields: survivor, absorbed, absorbed_uses, absorbed_min_row,
    // absorbed_atomic
    pub absorbed_abs: Option<<T as DenseId>::Index>,
}
```

`add_singleton` sets `abs: None`. `merge` copies the absorbed class's handle
into `absorbed_abs` and leaves the survivor's handle and the pool unchanged.
The absorbed entry stays allocated until a restore truncates the pool, so the
caller reads it through `abs_value_at`.

### 2.3 Field and spec views

```rust
// proposed field, next to min_pool
pub(crate) abs_pool: SpVec<A, usize, <P as PlainFamily<A, usize, TRACK>>::Store, TRACK>,

// proposed spec views, next to pool_view / pool_archive
pub open(crate) spec fn abs_pool_view(&self) -> Seq<A>;
pub open(crate) spec fn abs_pool_archive(&self) -> Seq<Seq<A>>;
/// The value of live class `id`: None without a handle, else the pool entry.
pub open(crate) spec fn abs_value_spec(&self, id: nat) -> Option<A>;
```

### 2.4 Operations

```rust
// proposed
pub fn abs_handle(&self, key: K) -> (h: Option<<T as DenseId>::Index>)
    requires self.wf(),
    ensures h == self.class_data_spec(key.as_nat()).abs;

pub fn abs_value(&self, key: K) -> (r: Option<A>)
    requires self.wf(),
    ensures r == self.abs_value_spec(key.as_nat());

/// Reads the entry a MergeInfo handle names (the min_monomial_at_row shape).
/// Refuses an unallocated handle.
pub fn abs_value_at(&self, h: Option<<T as DenseId>::Index>) -> (r: Option<A>)
    requires self.wf(),
    ensures h matches Some(i) ==> r == Some(self.abs_pool_view()[i.as_nat() as int]),
            h is None ==> r is None;

/// Allocates the class's entry on first use, else overwrites it.
/// Both paths are tracked writes. Refuses a dead key or pool exhaustion.
pub fn set_abs_value(&mut self, key: K, v: A)
    requires old(self).wf(),
    ensures
        final(self).wf(),
        final(self).n_spec() == old(self).n_spec(),
        final(self).roots_view() == old(self).roots_view(),
        final(self).num_classes_spec() == old(self).num_classes_spec(),
        final(self).min_width_spec() == old(self).min_width_spec(),
        final(self).abs_value_spec(key.as_nat()) == Some(v),
        forall|id: nat| id != key.as_nat() && old(self).reprs.contains_spec(id)
            ==> final(self).abs_value_spec(id) == old(self).abs_value_spec(id);
```

`merge_with` gains two ensures, carried to `merge`, `merge_directed`,
`merge_directed_with` and the `merge_justified*` forms:

```rust
// proposed, inside the `r matches Some(mi)` block of merge_with
&&& mi.absorbed_abs == old(self).class_data_spec(
        old(self).key_of(mi.absorbed.id_nat() as int)).abs
&&& final(self).abs_pool_view() == old(self).abs_pool_view()
```

The second clause gives the caller `abs_value_at(mi.absorbed_abs)` with the
pre-merge entry. The caller then calls `set_abs_value(survivor_key, meet)`.

## 3. Invariant W8

W8 joins the W-invariant table in the `eclasses.rs` module header, in the
style of W6:

> W8: the abstract-value pool is whole entries; live handles are allocated and
> pairwise distinct.

Stated over the views of `eg_model_wf`, with `abs_pool: Seq<A>` a new
parameter:

```rust
// W8a: whole entries. One cell holds one entry of type A, so the pool
// length counts entries and no write splits an entry.
// W8b: live handles are allocated
&&& (forall|id: nat| #[trigger] ss_contains(reprs_sparse, reprs_indices, live, id)
        && ss_value(reprs_dense, reprs_sparse, id).abs is Some
        ==> ss_value(reprs_dense, reprs_sparse, id).abs->Some_0.as_nat()
            < abs_pool.len())
// W8c: live handles are pairwise distinct
&&& (forall|id1: nat, id2: nat|
        ss_contains(reprs_sparse, reprs_indices, live, id1)
            && ss_contains(reprs_sparse, reprs_indices, live, id2) && id1 != id2
            && #[trigger] ss_value(reprs_dense, reprs_sparse, id1).abs is Some
            && #[trigger] ss_value(reprs_dense, reprs_sparse, id2).abs is Some
            ==> ss_value(reprs_dense, reprs_sparse, id1).abs->Some_0.as_nat()
                != ss_value(reprs_dense, reprs_sparse, id2).abs->Some_0.as_nat())
```

If the student stores an entry across `abs_width > 1` cells, W8a becomes
`abs_width > 0 ==> abs_pool.len() % abs_width == 0`. W8b then becomes
`(h + 1) * abs_width <= abs_pool.len()`, the exact shape of W6. If `A` carries
a decode predicate, W8a also states it per cell, as the pool-cells-decode
clause does for `Opt<T>`.

W8c is the frame condition of `set_abs_value`: writing one class's entry
leaves every other live class's value unchanged.

Per operation, the proof obligation is:

| Operation | Handles | Pool | W8 argument |
|---|---|---|---|
| `new` | none live | empty | vacuous |
| `add_singleton` | new key gets `None` | unchanged | old handles keep W8 |
| `merge_with` | absorbed key removed, survivor unchanged | unchanged | a subset of the old live handles |
| `set_abs_value`, first write | key gets `len` | grows by 1 | `len` exceeds every old handle, so it is fresh |
| `set_abs_value`, overwrite | unchanged | 1 cell written | handles and length unchanged |
| `set_min_monomial`, `set_atomic`, `set_class_matchable`, `add_use`, `splice_uses` | `abs` carried | unchanged | old W8 |
| `restore_frames`, `reset_frames` | archived | archived | per-frame W8 from the archive |

`merge_with` discharges W8 in `lemma_merge_wf`. The survivor's payload write
there must carry `abs` unchanged, as it carries `min_row`.

## 4. Archive and restore obligation

The handle lives in `ClassData`, so the repr set's dense column already
restores it. The pool is a new component with its own frame stack. The
obligation is that both restore together.

1. `eg_archive_agrees` gains a parameter `abs_snaps: Seq<Seq<A>>` with three
   clauses: `abs_snaps.len() == f`; `eg_model_wf` holds per frame `k` with
   `abs_snaps[k]`, so W8 holds in every archived mark; and archived lengths
   are monotone, `abs_snaps[k1].len() <= abs_snaps[k2].len()` for
   `k1 <= k2`.
2. `EClasses::wf` gains `abs_pool.wf()` and the bound
   `abs_pool.snapshots_view()[k].len() <= abs_pool.view().len()` for every
   frame, outside the opaque predicate, as for `min_pool`.
3. `push_frames` pushes the pool in lockstep and ensures
   `abs_pool_archive() == old.abs_pool_archive().push(old.abs_pool_view())`.
4. `restore_frames` and `reset_frames` restore the pool in lockstep and ensure
   `abs_pool_view() == old.abs_pool_archive()[target]`, with the archive
   truncated as for `pool_archive`.
5. The component depth checks in the three frame functions include
   `abs_pool.depth_exec()`.
6. The `Member` impl in `group.rs` adds the pool view to `Model` and `archive`.

Together with the existing `reprs_dense_view() == old.reprs_dense_archive()[f]`,
items 3 and 4 give the semi-persistence theorem for abstract values. For every
class key live at mark `f`, after a restore to `f`, the class's handle and its
pool entry equal their values at mark `f`. The student states this theorem as
an ensures of `restore_frames` in terms of `abs_value_spec`.

## 5. Payload size (decision 1)

`egraph/src/classes.rs` pins the `ClassData` repr at 16 bytes for 31-bit ids
and at most 32 bytes for 63-bit ids. The current repr holds three index words
(use list, `min_row`, `size`) and three flags (`present`, `atomic`,
`matchable`): 15 bytes, padded to 16 at 31-bit ids, and 27 bytes, padded to
32 at 63-bit ids. A separate `(handle, present)` pair adds one word and one
byte, so the assert fails at both widths. This is the first design decision.

| Option | 31-bit repr | 63-bit repr | Cost | Proof work |
|---|---|---|---|---|
| A. Widen the budget: store `abs` as `(handle, present)`, as `min_row` is stored | 20 bytes (+25%) | 40 bytes (+25%) | 4 bytes per class at 31-bit ids, in the live column and in every captured old value | the `min_row` pattern; no new technique |
| B1. Share a word: one side-row number indexes both the `min_pool` row and the pool entry | 16 bytes | 32 bytes | a class with only one of the two allocates both; the two pools grow in lockstep | W6 and W8 share one allocation clause; `set_min_monomial` and `set_abs_value` share allocation |
| B2. Share bits: encode `None` as a sentinel index and move the flags into spare high bits of the index words | 16 bytes | 32 bytes | decode costs a mask per read | new `repr_wf` and extensionality proofs for packed words; the use-list word's high bit already carries the capture tag |

Option A requires a measurement. The student reports peak resident memory and
wall time on the benchmark set, before and after, and updates both asserts and
their comments with the measured result. Option B1 or B2 keeps both asserts
unchanged; the student states which pool allocations become shared or which
bits are reused.

A further option drops the handle and indexes the pool by class key. The key
is unique per live class and survives a merge as the survivor's key. This
option keeps 16 bytes and makes W8c hold by construction. It departs from the
handle design of eclass-analysis.md §4 and sizes the pool by the key range,
so the student argues it against the table above before choosing it.

## 6. Change sites

Each site carries a comment `TODO(abs-class-storage)` that names the change
and the section of this chapter. Line numbers refer to the hand-off commit
of this branch.

| File:line | Site | Change | § |
|---|---|---|---|
| `containers-verus/src/eclasses.rs:42` | module header | add W8 to the W-invariant table | 3 |
| `containers-verus/src/eclasses.rs:62` | `ClassData` | add `abs` | 2 |
| `containers-verus/src/eclasses.rs:96` | `EqSpec::eq_exec` | compare `abs` as `min_row` | 7 |
| `containers-verus/src/eclasses.rs:142` | `Default for ClassData` | `abs: None` | 2 |
| `containers-verus/src/eclasses.rs:156` | `ClassDataRepr` | store `abs`; the 16-byte decision | 5 |
| `containers-verus/src/eclasses.rs:184` | `Tagged for ClassData` | extend `value_of`, `repr_wf`, extensionality, `into_repr`, `from_repr` | 7 |
| `containers-verus/src/eclasses.rs:291` | `eg_model_wf` parameters | add the pool view | 3 |
| `containers-verus/src/eclasses.rs:363` | `eg_model_wf` W6 clauses | state W8 after W6 | 3 |
| `containers-verus/src/eclasses.rs:411` | `eg_archive_agrees` | archived pool snapshots, per-frame W8, monotone lengths | 4 |
| `containers-verus/src/eclasses.rs:477` | `min_pool` field | add `abs_pool` and its `PlainFamily` bound | 2 |
| `containers-verus/src/eclasses.rs:693` | `EClasses::wf` | `abs_pool.wf()`, predicate arguments, archived-length bound | 4 |
| `containers-verus/src/eclasses.rs:718` | `new` | allocate the empty pool | 2 |
| `containers-verus/src/eclasses.rs:879` | `add_singleton` | `abs: None`, also in the spec literal | 2 |
| `containers-verus/src/eclasses.rs:1216` | `MergeInfo` | add `absorbed_abs` | 2 |
| `containers-verus/src/eclasses.rs:1244` | `lemma_merge_wf` | carry `abs`; discharge W8 | 3 |
| `containers-verus/src/eclasses.rs:1730` | `merge_with` ensures | `absorbed_abs`; pool view unchanged | 2 |
| `containers-verus/src/eclasses.rs:1906` | `merge_with` result | `absorbed_abs: data.abs` | 2 |
| `containers-verus/src/eclasses.rs:2250` | `set_min_monomial` | model for `set_abs_value` | 7 |
| `containers-verus/src/eclasses.rs:2754` | `min_monomial_at_row` | model for `abs_value_at` | 2 |
| `containers-verus/src/eclasses.rs:2799` | `merge` | carry the `absorbed_abs` ensures to every public merge form | 2 |
| `containers-verus/src/eclasses.rs:2959` | `push_frames` | push the pool in lockstep | 4 |
| `containers-verus/src/eclasses.rs:3135` | `reset_frames` | reset the pool in lockstep | 4 |
| `containers-verus/src/eclasses.rs:3295` | `restore_frames` | restore the pool; view equals archive | 4 |
| `containers-verus/src/group.rs:1607` | `Member for EClasses` | pool in `Model`, `archive` and depth checks | 4 |
| `egraph/src/classes.rs:50` | 31-bit size assert | 16-byte decision | 5 |
| `egraph/src/classes.rs:62` | 63-bit size assert | 32-byte bound | 5 |
| `containers-verus/doc/design/egraph-class-layer.md:30` | Surface | list the handle and pool | 2 |
| `containers-verus/doc/design/egraph-class-layer.md:37` | Invariants | W1 through W8 | 3 |

The type aliases in `egraph/src/classes.rs` and the `fold_min_monomial` call
sites in `egraph/src/egraph.rs` change only if the entry parameter `A` has no
default. The meet on merge belongs to `abs-saturation-engine`. The unverified
reference `containers/src/eclasses.rs` is a differential oracle and needs no
change; `containers-conformance` may compare `absorbed_abs` once the
reference has it.

## 7. Patterns to follow

Every step of this PR has a precedent in the `min_row` / `min_pool` code.
Line numbers refer to the hand-off commit, which includes the TODO comments.

- `ClassData::min_row` (`eclasses.rs:68`) and its `(row, present)` repr
  (`ClassDataRepr`, line 163): the absent value is pinned to
  `(min, false)` by `repr_wf`, which the extensionality lemma needs.
- `EqSpec::eq_exec` (line 97): the `min_row` match and its injectivity proof.
- W6 in `eg_model_wf` (line 364): allocation and distinctness of live rows.
- `eg_archive_agrees` (line 397): `pool_snaps` and its monotone-length clause.
- The `min_pool` field (line 482) and its `PlainFamily` bound.
- `MergeInfo::absorbed_min_row` (line 1221), set at line 1907 and ensured in
  `merge_with` (line 1687).
- `set_min_monomial` (line 2257): first-use allocation by
  `min_pool.try_push_repeat` (line 2314), the payload write `reprs.set_live`
  (line 2333), the tracked cell write `min_pool.set_index` (line 2411), and
  the mid-state lemma `lemma_mid_pool_wf` (line 2436).
- `min_monomial_at_row` (line 2759): a read through a handle carried in
  `MergeInfo`, with a runtime allocation check.
- `push_frames` (line 2963), `reset_frames` (line 3139), `restore_frames`
  (line 3299): the `pool_view` / `pool_archive` ensures.
- `set_min_width` (line 2080): the one place outside mark and restore that
  reveals `eg_archive_agrees`; it must pass the new pool arguments through.

## 8. Decisions left to the student

1. Payload size (§5): option A with a measurement, or option B1 or B2.
2. Entry representation: a type parameter `A`, a const-generic word array,
   or entries spanning `abs_width` cells.
3. One pool or one pool per sort. Per-sort pools widen the handle to a
   `(sort tag, offset)` pair, as eclass-analysis.md §4 sketches.
4. Handle adoption on merge: when the survivor has no handle and the absorbed
   class has one, `merge` may move the handle to the survivor. Adoption saves
   one pool entry and adds one payload write to `merge_with`.
5. Whether `set_abs_value` returns the previous value, so the caller detects
   a change without a second read.

Each decision is recorded in this chapter, with its reason, before the PR
leaves draft.

## 9. Acceptance criteria

1. Verification reports 0 errors for the modules `eclasses` and `group`:
   `cargo verus focus -p semi-persistent-containers-verus -- --verify-only-module eclasses`,
   and the same with `group`.
2. The PR adds no `admit`, no `assume` and no `external_body`. The trust
   ledger in [Chapter 2](02-trust-boundary.md) is unchanged.
3. The tests in `containers-verus/tests/abs_class_storage.rs` are
   implemented, their `#[ignore]` attributes removed, and they pass:
   `cargo test -p semi-persistent-containers-verus --test abs_class_storage`.
4. The existing suites pass, among them `eclasses_behavior` and the
   `containers-conformance` test `egraph_reference_differential`.
5. `egraph` builds with the size asserts updated to the chosen option of §5.
   Option A reports the measurement in the assert comment.
6. W8 appears in the `eclasses.rs` module header and in
   [egraph-class-layer.md](egraph-class-layer.md), and every
   `TODO(abs-class-storage)` comment is resolved and removed.
7. `cargo fmt --all --check`, `cargo clippy` and
   `bash scripts/check-oss-scaffold.sh` pass.

## 10. Links

- [eclass-analysis.md §4 Storage](../../../egraph/doc/future/eclass-analysis.md#4-storage):
  the storage design this PR implements.
- [E-Graph Class-Layer Integration](egraph-class-layer.md): the class layer's
  surface and invariants.
- [Chapter 2, The Trust Boundary](02-trust-boundary.md): the
  `external_body` ledger.
- [Chapter 18, Store Policy](18-store-policy.md): the `PlainFamily` column
  family the pool uses.
- Sibling branches: `abs-surface-syntax` (PR 1), `abs-saturation-engine`
  (PR 3), `abs-domain-registry` (PR 4).
