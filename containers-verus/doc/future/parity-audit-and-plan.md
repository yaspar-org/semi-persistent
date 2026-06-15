# Feature-Parity Audit and Verification Plan

*A rigorous, skeptical accounting of what the verified `containers-verus` crate
covers versus the production [`semi-persistent-containers`](../../../containers)
crate — written to make the PR's claims precise. Every gap and every place the
verus spec is weaker than (or deliberately diverges from) production is flagged.
The companion [B+tree design doc](bplus-tree-design.md) scopes the one container
still in progress.*

[Design Table of Contents](../design/00-table-of-contents.md)

## 0. One-paragraph verdict

The verus crate **verifies the full semi-persistent core and the flat-arena
container family at production parity for their essential operations, with
specs that are generally *stronger* than production** (production's invariants
are implicit; ours are declarative and machine-checked). What is **not** at
parity: the **B+tree** (scaffold only — milestone 1 of 7), three **production
modules with no verus counterpart** (`bitset`, the `define_id!` id-macro family,
`sorted_cursor`), the `IdFactory` allocator, and a handful of **convenience
methods** (`iter`/`get_mut`/`len`-aliases) omitted from otherwise-verified
containers. Several **deliberate divergences** (`T: Copy + Default` vs
`T: Clone`; `ParallelStore`/`NodeRef` modeling choices; `usize` vs the full
`DenseId` family) are documented, not accidental. The PR should be framed as
*"the verified semi-persistent vector and flat container family,"* explicitly
excluding the B+tree and the id-macro/bitset/cursor utilities.

## 1. Module-level coverage

| Production module | Verus counterpart | Status |
|---|---|---|
| `vec.rs` + `diff_store.rs` + `token.rs` | `vec`, `diff_store`, `parallel_store`, `inline_store`, `capture_bits`, `frame`, `container_id`, `fork_history` | **Verified** (core theorem + both backends + branch-cut) |
| `append_only_vec.rs` | `append_only_vec` | **Verified** (core API) |
| `map.rs` | `map` (`SpMap`) | **Verified** (core API) |
| `sparse_set.rs` | `sparse_set` | **Verified** (real spec: bijection + id pool) |
| `list.rs` | `list` (+ `opt`) | **Verified** (prepend/append/splice) |
| *(e-graph `classes.rs` ring)* | `circular_list` | **Verified** (not a production `containers` module; the class-membership ring, ported here) |
| `tagged.rs` | `tagged` (+ `dense_id`, `opt`) | **Verified** (trait + `BoolPair` + a real bit-stealer) |
| `dense_id.rs` | `dense_id`, `index_like` | **Partial** — `DenseId31` + `IndexLike` trait verified; **`IdFactory` absent** |
| `id.rs` (`define_id7/15/31/63!`) | — | **ABSENT** — no macro; `DenseId31` is one hand-written instance |
| `bplus.rs` | `bplus` | **Scaffold only** — milestone 1 of 7 (see §4) |
| `bitset.rs` | *(internal use covered by `capture_bits`)* | **ABSENT as a public type** (see §3) |
| `sorted_cursor.rs` | — | **ABSENT** — no `SortedCursor` trait / cursor iteration |

## 2. Method-level parity (the verified containers)

Status legend: **✓** verified (proved `ensures` capturing production behavior, no
`admit`/`external_body`); **◐** present but unproved (`external_body`
diagnostic); **✗** absent.

### Vec (the foundation)
| Production item | Verus | Notes |
|---|---|---|
| `with_store` / `new` | ✓ | both `ParallelStore` and `InlineStore` backends verified against `DiffStore` |
| `push` / `pop` / `set` / `get` | ✓ | incl. **pop into a marked region** (the hard case) — first-write-wins, proved |
| `len` / `is_empty` / `depth` | ✓ | |
| `mark` / `restore` | ✓ | **headline theorem**: after `restore(token)`, `view() == snapshots[token.frame_idx]`, at arbitrary nesting depth |
| `is_valid_token` + ForkHistory | ✓ | branch-cut safety: `is_valid` exec-walk proved == `fork_valid` spec; stale/cross-branch tokens rejected |
| `View` / `ViewIter` iteration | ✓ | read-only handle + iterator, contracted |
| `TRACK = false` | ✓ | proved observationally a plain `std::Vec`, zero diff-log overhead while unmarked |
| `as_slice` | ◐ | `external_body`, no spec (a backend-specific fast path outside the persistence contract) |
| `total_bytes` / `tracking_bytes` / `heap_bytes` | ◐ | `external_body` capacity diagnostics; no spec content (production identical) |

The Vec spec is, if anything, **stronger** than production: production never
states the reconstruction theorem; we prove it. The capture flags additionally
use a **packed `Vec<u64>` (`CaptureBits`)** proved to refine a ghost `Seq<bool>`
— 8× denser than a `Vec<bool>`, matching production's bitset density.

### AppendOnlyVec
`new` / `push` / `get` / `len` / `is_empty` / `mark` / `restore` /
`depth` / `is_valid_token`: **✓**. Snapshot invariant `snapshots[k] ==
data[0..frames[k]]` proved. **Absent (✗)**: `get_mut`, `iter`.

### Map (`SpMap`)
`new` / `insert` / `id_of` / `contains_key` / `get` / `log_len` / `mark` /
`restore` / `is_valid_token`: **✓**. The index-agrees-with-log invariant
(`is_last_occurrence`, last-write-wins) is **proved**, and `rebuild_index` is
proved correct by loop induction. **Standing assumption**: `obeys_key_model::<K>()`
(vstd proves it for primitive keys; a custom key supplies it). **Absent (✗)**:
`get_by_key`, `len`, `is_empty`, `iter` (the verus `log_len` is the analogous
size accessor; a key-count `len` is not exposed).

### SparseSet
`new` / `new_inline` / `add` / `remove` / `contains` / `get` / `set` / `len` /
`is_empty` / `mark` / `restore`: **✓**, against the **real spec** — not just
persistence. `wf` is the permutation invariant (dense/sparse mutually inverse on
the live prefix), refined to a ghost `Set<nat>` + an index pool; `add` recycles
the freed-id pool LIFO, `remove`'s swap is a transposition proved to preserve
the permutation; the set and pool provably partition `[0, cap)`. **Absent (✗)**:
`remove_value` (the linear-scan-by-value variant), `data` (the raw dense-slice
accessor), and production's generic `with_store` constructor (verus exposes the
two concrete `new`/`new_inline` instead).

### ListArena
`new` / `new_list` / `prepend` / `append` / `splice` / `is_empty` / `mark` /
`restore`: **✓**, on the **ghost-model-list** invariant (per-list `Seq<usize>`
of node ids; in-range-only + disjoint + cache-consistency). `splice` matches
production semantics (`dst := dst ++ src`, `src` cleared) and is proved to
preserve disjointness. **Divergence**: `restore` takes the ghost model live at
mark as an extra `Ghost` parameter (VecTokens are opaque and can't carry it).
**Absent (✗)**: `iter` (verus exposes the spec-level `list_seq`, not an exec
iterator).

### CircularList
`new` / `add_singleton` / `next_of` / `len` / `splice` / `mark` / `restore`:
**✓**. The O(1) ring-merge (`splice` by `next`-swap) is proved to merge two
rings into one **unconditionally** (no cycle-return side assumption), on an
explicit ghost ring-partition model. (This ports the e-graph's
`classes.rs` ring, not a `containers/` module.)

## 3. Production features with NO verus counterpart

These are **honest gaps** the PR must not imply are covered:

1. **`id.rs` — the `define_id7/15/31/63!` macros + their generated id types.**
   Verus has exactly one hand-written `DenseId31`; it does not generate the id
   family, the 7/15/63-bit widths, or the `NodeId`/`StoredNodeId` clean-vs-repr
   split the macro produces. `DenseId31` *demonstrates* that the niche encoding
   verifies; it is not a drop-in for the macro.
2. **`IdFactory`** (sequential id allocation) — absent.
3. **`bitset.rs`** as a public `BitSet` type — absent. The *internal* packed-bit
   need is met by the verified `CaptureBits` (used inside `ParallelStore`), but
   there is no standalone public bitset.
4. **`sorted_cursor.rs`** — the `SortedCursor` trait and ordered cursor
   iteration (`seek`/`step`/`key`) are absent. (`Vec`/`AppendOnlyVec` have
   verified read iterators; the *sorted-cursor* abstraction the B+tree exposes
   is not ported.)
5. **`Default`/`Clone`/`Debug`/`Hash` derives and the broader trait surface** of
   the production id types — out of scope.

## 4. The B+tree: precise status and plan

**Status: scaffold only — milestone 1 of 7.** What is verified today (`bplus.rs`,
~190 lines vs production's ~1040): the module, a node struct over the verified
arena, a *milestone-1* `wf` (root is an in-range leaf; per-node count ≤ cap and
keys sorted), an abstract `model()`, and `new`/`is_empty`/`len` — i.e. the
**empty / single-leaf tree** is proved well-formed with `model == []`. There are
**no internal nodes, no `insert`, no splitting** yet. This is ~5% of the
container and the *flat* 5%; the B+tree's defining theorem (insert-with-split
preserving sortedness + balance) is entirely unproved.

The full plan is in [bplus-tree-design.md](bplus-tree-design.md); the milestone
ladder (each leaves the module green):

| M | Deliverable | Difficulty |
|---|---|---|
| 1 ✓ | model + `wf` + `new`/`is_empty`/`len` (empty tree) | done |
| 2 | `contains` — descend-and-search reaches the unique leaf; `contains ⟺ ∈ model` | moderate |
| 3 | `insert`, **no-split** case (leaf has room) — one-node footprint, rest framed | SparseSet-scale |
| 4 | **leaf split**, parent has room — two-leaf split + leaf-link splice + separator insert | hard |
| 5 | **full split propagation + new root** — induction up the path stack | hardest |
| 6 | `mark`/`restore` — compose from the inner `Vec` | mechanical |
| 7 | `from_sorted` bulk-build + ordered-cursor iteration theorem | moderate |

Reality check: M1 (done) validated the invariant *shape*, but **M2–M3 will force
`wf` to be reshaped, not just extended** — the milestone-1 `wf` cannot express
cross-node ordering without the recursive ghost tree, so the "monotone
additions" hope from the M1 commit message is optimistic for clause 5. Deletion
stays out of scope (production is insert-only). Expect M4–M5 to dominate the
effort; this is a multi-session undertaking comparable to the original `Vec`
proof.

## 5. Deliberate divergences (documented, not gaps)

- **`T: Copy + Default`** throughout, vs production's `T: Clone`. `Copy ⊂ Clone`
  suffices for the e-graph's id-typed payloads; `Default` enables the DoS-free
  bounded-capture pop (see [05-restore-regrow-alternatives](../design/05-restore-regrow-alternatives.md)).
- **`ListArena` uses `ParallelStore` + `NodeRef{some,idx}`**, not production's
  `InlineStore` + `Opt`'s stolen bit — same logical content, avoids porting the
  composite-`Tagged` niche for the node/head structs.
- **`usize` ids in several containers** vs production's `DenseId` newtypes —
  `DenseId31` shows the niche encoding verifies; the containers themselves index
  by plain `usize` for proof simplicity.
- **`restore` ghost-model parameters** (ListArena, CircularList) — a proof
  artifact (opaque tokens can't carry the ghost model), not a runtime API change.
- **Single fixed node geometry** in the B+tree scaffold vs production's generic
  `NodeLayout` (6 size variants) — the proof is about tree structure, not packing.

## 6. What the PR should claim

Recommended scope statement for the PR description:

> Verifies the semi-persistent **vector** (exact diff-log reconstruction at
> arbitrary mark nesting, incl. pop into a marked region; fork-history
> branch-cut safety; `TRACK=false` zero-overhead) and the flat-arena container
> family built on it — **AppendOnlyVec, Map, SparseSet, ListArena** — plus the
> e-graph **circular class-list**, all with machine-checked specifications and
> **no `admit`s or `assume`s**. Storage is verified for both the inline
> (niche-bit) and parallel (packed `Vec<u64>` bitset) backends, and a real
> MSB-stealing `DenseId31` exercises the niche obligations non-vacuously.
>
> **Out of scope (documented future work):** the **B+tree** (scaffolding +
> design doc only); the `define_id!` id-macro family and `IdFactory`; a
> standalone public `BitSet`; the `SortedCursor` trait. A small set of
> convenience methods (`iter`/`get_mut`/key-count `len`) are omitted from
> otherwise-verified containers.

Per-module verified counts are in `verify-all.sh` output; the tally at the time
of writing is 326 verified, 0 errors, 0 admits across 18 modules (the B+tree
contributing only its 8 scaffold facts).

---
[Design Table of Contents](../design/00-table-of-contents.md)
