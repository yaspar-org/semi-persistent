<!--
Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
SPDX-License-Identifier: Apache-2.0
-->
# The class layer: kernel and engine parity

The engine's class layer is this crate's verified kernel:
`egraph::EClasses`, `egraph::UnionFind`, and `egraph::ProofBuf` are type
aliases of `EClasses<T, L, N, J, TRACK, PROOFS>`,
`UnionFind<T, J, TRACK, PROOFS>`, and `ProofBuf<T, J>` with the engine's
`Justification<T>` as `J` (`egraph/src/classes.rs`,
`egraph/src/union_find.rs`). There is no adapter layer. This chapter states
what the kernel provides and where its behavior deliberately differs from
the pre-swap production code; the method-by-method audit evidence is
[`13-parity-matrix.md`](13-parity-matrix.md) and
[`14-parity-audit-2.md`](14-parity-audit-2.md).

## Surface

- **Union-find**: `make_set(id)` (sequential-id refuse) and `try_make_set`;
  `find` (two-pass full compression) and `find_const`; `union` and
  `union_directed` (refused under `PROOFS`); `union_justified` and
  `union_justified_directed`; `reroot_proof`; `explain` into
  `ProofBuf<T, J>`; `mark`/`restore` archiving fast and proof columns in
  lockstep.
- **EClasses**: `add_singleton(id)`; `add_use` (refuses an out-of-range
  parent, W5); `use_list_id`, `use_list_len` (the header's cached count,
  verified by the list's `cache_len` clause), `class_size` (the W7-verified
  member count), `atomic`, `set_atomic`, `min_monomial`,
  `min_monomial_at_row`, `set_min_monomial`, `set_min_width`; `find`,
  `find_const`, `repr_id`; `merge`, `merge_directed` (by-uses survivor),
  `merge_directed_with` and `merge_justified_directed_with` (the caller
  supplies the survivor: the engine's `--union-by` policies compute it from
  `class_size`/`use_list_len`), `merge_justified`,
  `merge_justified_directed`; `splice_uses`, `uses()`, `iter_uses`,
  `iter_class`; `mark`/`restore`.
- **Invariants**: W1..W7 as `wf()`, the table in the `eclasses.rs` module
  header. `merge` folds the survivor's size before the ring splice and the
  merge lemma re-establishes W7 from the two operand classes' instances.
  The archive clauses extend every invariant to every outstanding mark, and
  `restore` refuses mixed-mark and cross-container token components.

## Verified core, trusted glue

The partition work (rings, keys, use-lists, pool, sizes, archives) is
verified. The proof-forest logic (re-rooting, LCA walk in `explain`) is
in-struct trusted glue over verified columns: no W-invariant reads the
proof columns, their storage and mark/restore lockstep are `wf` clauses,
and their algorithms are the engine's, hosted in a non-verus impl block.
Verifying path-reversal termination would need proof-forest acyclicity as
a ghost invariant maintained through reversal; that is real proof work
with no invariant payoff, and it is not scheduled.

## Deliberate divergences from the pre-swap production code

- **Saturating rank bump.** Production's `u8` rank bump wraps after 255
  forced-survivor bumps on one root; the kernel saturates at 255. Identical
  below 255, strictly safer at it; no invariant reads rank.
- **Canonical absent cells.** A merged-away ring cell stores canonical
  `none`; production kept the key bits with the presence bit cleared. Every
  public read returns `None` either way; raw cell bytes differ.
- **Refuse messages at the total-shell boundary.** Preconditions that
  production enforced with `assert!`/`debug_assert!` refuse at the kernel's
  public surface with named messages; the panic conditions are the same.

Everything else is algorithmically equal, including the two-pass `find`
(chosen over path halving after a 3-5% measurement on merge-heavy
saturation) and the row-number min-monomial pool scheme. Layout is pinned
by the consumer's compile-time asserts: 12-byte ring cell and 16-byte class
payload at 31-bit ids, with the 63-bit instantiation carrying its own
assert (`egraph/src/classes.rs`).
