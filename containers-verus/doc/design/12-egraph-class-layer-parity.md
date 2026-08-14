<!--
Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
SPDX-License-Identifier: Apache-2.0
-->
# Class-layer parity assessment: verified kernel against production

A side-by-side reading of the verified class layer against production's, at
method granularity: interface equivalence, algorithmic equivalence, state
layout, and every divergence found, each classified MUST-FIX,
STRICTER-SAFE, UNOBSERVABLE, or ACCEPTED with its argument. Sources read:
`egraph/src/union_find.rs` (production union-find, still in-tree),
`egraph/src/classes.rs` at `d14fd17^` (production `EClasses`, pre-swap),
against `containers-verus/src/{union_find,eclasses}.rs` and the post-swap
adapter. This document drives the PROOFS-parity refactor; its MUST-FIX
list is that work's specification.

## Union-find

### State

| | production | kernel today | verdict |
|---|---|---|---|
| type parameters | `UnionFind<T, TRACK, PROOFS>` | `UnionFind<T, TRACK>` | **MUST-FIX**: kernel gains `J` (justification payload; production hard-codes `Justification<T>`, an egraph type the kernel cannot name) and `PROOFS`; egraph aliases `UnionFind<T, TRACK, PROOFS> = kernel::UnionFind<T, Justification<T>, TRACK, PROOFS>` |
| fast forest | `parent_fast: VecI<T>`, `rank: VecI<u8>` | same columns, same stores | equal |
| proof forest | `parent_proof: Option<VecI<T>>`, `justification: Option<VecI<Justification<T>>>`, `Some` iff `PROOFS` | ABSENT from the struct; the same two columns live in the post-swap `EClasses` adapter | **MUST-FIX**: the dual structure moves into the kernel struct, `Some` iff `PROOFS`, uncompressed (no operation ever path-compresses the proof side — its value IS the original edges) |
| token | `{parent_fast, rank, parent_proof: Option, justification: Option}` | `{parent, rank}` (+ the pair in the adapter's token) | **MUST-FIX**: token carries the option pair |

### Methods

| method | production algorithm | kernel | verdict |
|---|---|---|---|
| `new` | proof columns `Some(empty)` iff `PROOFS` | no proof columns | MUST-FIX |
| `make_set(id)` | `assert!` id sequential; push `id` to parent, `0` to rank, `id`/`Filler` to proof columns | kernel mints instead (`try_make_set`); adapter asserts and delegates; filler pushes live in the adapter | **MUST-FIX**: kernel exposes `make_set(id)` with the sequential check (refuse) and the in-struct filler pushes; `try_make_set` stays as the total mint |
| `find` | two-pass: walk to root, then point every path node at the root | identical two passes, verified (measured against halving first: full compression won 3-5%) | equal; out-of-range refuses with a named message where production's would refuse inside the store read — same divergence class as every total-shell conversion |
| `find_const` | read-only walk | identical, verified | equal |
| `union` | `assert!(!PROOFS)`; by-rank, tie keeps `find(a)`'s root | same selection verified; the `!PROOFS` assert lives nowhere (kernel had no PROOFS) | **MUST-FIX**: kernel `union` refuses under `PROOFS` with production's exact message |
| `union_directed` | forced survivor; same rank maintenance | same, verified | MUST-FIX only for the `!PROOFS` assert |
| rank maintenance | `if rank_surv <= rank_abs { set(surv, rank_abs + 1) }` — unsaturated `u8` arithmetic | same condition, bump saturates at 255 | **ACCEPTED DIVERGENCE**: production's `+ 1` panics in debug and wraps in release after 255 forced-survivor bumps on one root; a wrapped rank corrupts the by-rank heuristic (soundness unaffected — no invariant reads rank). The saturating form is identical below 255 and strictly safer at it. Recorded here; revisit only if bit-exact rank state is ever compared |
| `union_justified`, `union_justified_directed` | `union_inner` with the edge record: on success, `reroot_proof(b)`, `pp[b] = a`, `j[b] = just` — original NODES, not roots | absent from kernel; adapter replicates verbatim after the kernel merge, same success gating, same order | **MUST-FIX**: moves into the kernel struct (glue over the verified columns; see trust note) |
| `reroot_proof` | reverse the proof path from `x`, shifting justifications child-ward, then `pp[x] = x` | adapter hosts it verbatim | MUST-FIX: in-struct |
| `explain` | equivalence check via `find_const`; walk both nodes to proof roots; LCA via a seen-set; emit a-to-LCA then reversed LCA-to-b into `ProofBuf.steps` | adapter hosts it verbatim (including `ProofBuf`'s scratch reuse) | MUST-FIX: in-struct, with `ProofBuf<T, J>` in the kernel and egraph aliasing `ProofBuf<T> = kernel::ProofBuf<T, Justification<T>>`; the scratch fields egraph's `explain_deep` borrows become `pub` |
| `mark`/`restore` | `try_mark`/`try_restore` per column with `expect`, proof columns via `Option::map` | fast columns verified with archives; proof columns in the adapter | MUST-FIX: in-struct, wf carrying the `PROOFS ==> lengths track n` clause and the archive extension so restore re-establishes it |

### Trust classification for the proof forest, stated before the work

No W-invariant reads the proof columns; they are metadata. Their STORAGE
becomes verified in-struct state (lengths track `n`, wf-composed
mark/restore). Their LOGIC — re-rooting, LCA — stays production's code
verbatim, hosted as in-struct trusted glue over the verified columns (the
same non-verus impl-block pattern as the `Iterator` delegations), because
verifying path-reversal termination means modeling proof-forest acyclicity
as a ghost invariant maintained through reversal: real proof work with zero
W-invariant payoff, postponed with that named condition. This is the same
trust class the algorithms have in production today, at the same structural
address. Consequence to check at implementation time: `J`'s `Tagged` impl
comes from the consumer (erased laws) — the same consumer-side-Tagged trust
item the migration doc already carries for every payload type.

## EClasses

### State and parameters

Production `EClasses<T, L, N, TRACK, PROOFS>` holds
`{entries, reprs, uf(dual), uses, min_pool, min_width}`. The kernel holds
the same five components with the fast-only union-find; the adapter holds
the proof pair beside it. **MUST-FIX**: the kernel becomes
`EClasses<T, L, N, J, TRACK, PROOFS>` embedding the dual union-find, and
egraph's `classes.rs` collapses to type aliases plus re-exports — the
adapter disappears as a layer.

### Methods

| method | assessment |
|---|---|
| `new`, `set_min_width`, `min_width`, `len`, `is_empty`, `num_classes` | equal (delegation; width freeze refuses where production asserts, same condition) |
| `add_singleton(id)` | production asserts sequential inside `make_set` plus a ring `debug_assert`; adapter asserts at its own boundary then mints. Same panic condition, DIFFERENT message ("node ids must be dense..." vs "id must be sequential"). MUST-FIX resolves this by routing through kernel `make_set(id)`, restoring the message |
| `add_use` | same append + atomic-flag algorithm. STRICTER-SAFE divergence: kernel refuses an out-of-range parent id (W5); production stored any value silently. Every caller in the workspace passes real node ids (full suites green) |
| `use_list_id/len`, `min_monomial(_at_row)`, `atomic`, `set_atomic`, `set_min_monomial` | algorithmically equal, incl. the row-number pool scheme; column bound refuses where production `debug_assert`s then refuses in the store |
| `find`, `find_const`, `repr_id` | equal |
| `merge` | same sequence: union, read absorbed key and data, ring splice with payload clear, repr removal. UNOBSERVABLE divergence: production's absorbed cell keeps the key bits with the presence bit cleared (`set_none` preserves the value, feeding its internal `repr_id_unchecked` mid-merge); the kernel writes canonical `none` — every public read (`repr_id` via `to_option`) returns `None` either way, and the kernel PROVES the key it reads mid-merge is live instead of using an unchecked read. Raw cell bytes differ post-merge |
| `merge_directed` | equal: same `prefer_a_by_uses` policy (larger use-list survives, ties to `a`), computed from the same reads |
| `merge_justified`, `merge_justified_directed` | adapter-level today (MUST-FIX: kernel-level with the in-struct edge record); success gating and ordering already verbatim |
| `explain` | verbatim algorithm; moves in-struct with the union-find |
| `splice_uses`, `uses()`, `iter_uses`, `iter_class` | equal (verified iterators are the same ones production adopted pre-swap) |
| `mark`/`restore` | same component order both directions. STRICTER-SAFE: kernel restore refuses mixed-mark and cross-container token components (nine-way frame agreement) and DISCHARGES SparseSet restore's snapshot-wf precondition from its archive, where production trusted the pairing |
| stage-0 debug monitor | retired: its three assertions are wf clauses now |

## Match store (adjacent, for completeness)

E17's `MatchRow::clear` leaves a stale value where the owned `Match`
re-arms a panic-on-read guard; equivalent for compiled action sequences
(set-before-read), recorded in E17's file. Not part of the class layer.

## Status

The MUST-FIX list below is DONE: the kernel is
`UnionFind<T, J, TRACK, PROOFS>` / `EClasses<T, L, N, J, TRACK, PROOFS>`
with the dual uncompressed forest in-struct, `make_set(id)` and
`add_singleton(id)` with production's messages, `union`/`merge` refusing
under `PROOFS` with production's messages, the justified family and
`explain` at their production addresses (partition work verified, proof
logic in-struct glue), and the token carrying the option pair whose
mark/restore lockstep is a wf clause re-established from the archive.
`egraph::UnionFind`, `egraph::EClasses`, and `egraph::ProofBuf` are type
aliases of the kernel; the adapter layer is gone. Coverage: the full proof
suite (justified merges, deep congruence explains, proof restores) runs
through the kernel forest; kernel-level PROOFS tests, a 63-bit behavior
round trip, and a 63-bit conformance relation check exist beside the 31-bit
differential. Verify 1632/0 both feature configurations; saturate_bench
reads identical to the pre-refactor state.

## Bottom line

Algorithms: equivalent everywhere, two deliberate exceptions (saturating
rank — accepted, argued above; full-compression `find` was aligned TO
production after measurement). Interfaces: equivalent at the egraph-facing
`EClasses` surface, NOT yet at the kernel level — the `PROOFS`/`J`
parameters, the dual in-struct forest, `make_set(id)`, the justified
family, `explain`, and the token shape are adapter-hosted, which is a
structural deviation from the replicate-the-design instruction. The
MUST-FIX list above is the specification for moving them into the kernel;
production behavior used in anger (PROOFS mode powers `explain` for every
proof-emitting workload) gets the same structural home it has in
production, with storage verified and logic in the same trust class as
today, honestly labeled.
