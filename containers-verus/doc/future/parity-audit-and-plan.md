# Feature-Parity Audit

Method-by-method coverage of the verified `containers-verus` crate versus the
production [`semi-persistent-containers`](../../../containers) crate.

[Design Table of Contents](../design/00-table-of-contents.md)

## 1. Module-level coverage

| Production module | Verus counterpart | Status |
|---|---|---|
| `vec.rs` + `diff_store.rs` + `token.rs` | `vec`, `diff_store`, `parallel_store`, `inline_store`, `capture_bits`, `frame`, `container_id`, `fork_history` | **Verified** (core theorem + both backends + branch-cut) |
| `append_only_vec.rs` | `append_only_vec` | **Verified** (core API) |
| `map.rs` | `map` (`SpMap`) | **Verified** (core API) |
| `sparse_set.rs` | `sparse_set` | **Verified** (real spec: bijection + id pool) |
| `list.rs` | `list` (+ `opt`) | **Verified** (prepend/append/splice) |
| *(e-graph `classes.rs` ring)* | `circular_list` | **Verified** (not a production `containers` module; the class-membership ring, ported here) |
| `tagged.rs` | `tagged` (+ `dense_id`, `opt`) | **Verified** (trait + `BoolTagged` + a real bit-stealer) |
| `dense_id.rs` | `dense_id`, `index_like`, `id_factory` | **Verified**: `DenseId31` + `IndexLike` trait, plus `IdFactory` sequential allocation |
| `id.rs` (`define_id7/15/31/63!`) | `id_macros` | **Verified**: the `define_id7/15/31/63!` family with full proofs |
| `bplus.rs` | `bplus`, `bplus_tree`, `bplus_layout`, `bplus_search` | **Verified**: insert (split + new root + O(1) append fast path, total), batched `from_sorted` (one arena write per leaf), in-order traversal + `seek`, arena-never-overflows, `mark`/`restore`; insert-only (see §4) |
| `bitset.rs` | `bitset` (`BitSet`) | **Present** as a public type; kept outside the container proofs (see §3) |
| `sorted_cursor.rs` | `sorted_cursor`, `sorted_vec_cursor` | **Verified**: the `SortedCursor` trait and the galloping `SortedVecCursor` |

### 1.1 Public type-name mapping

Public type names match production **except** for the four below. The first two
are *forced* by name collisions with `vstd` and cannot be the production name;
the rest are deliberate. Everything else (`Vec`, `AppendOnlyVec`, `SparseSet`,
`ListArena`, `BPlusTreeSet`, `Opt`, `InlineStore`, `ParallelStore`, `ContainerId`,
`ForkHistory`, `ShrinkPolicy`, the `*Token` types, and the `DiffStore` / `Tagged`
/ `IndexLike` / `DenseId` traits) is name-identical.

| Production | Verus | Reason |
|---|---|---|
| `Map` / `MapToken` | **`SpMap`** / `MapToken` | *forced*: `Map` collides with `vstd::map::Map` (a spec type). Token name matches. |
| `View` / `ViewIter` | **`VecView`** / **`VecViewIter`** | *forced*: `View` collides with vstd's `View` trait (the `@` operator). |
| `BoolTagged` | **`BoolTagged`** | aligned (was briefly `BoolPair`; renamed to match, incl. field `tag` → `tagged`). |
| *(e-graph `EClassEntry`)* | **`CircularList`** / `CircularListNode` | the class-membership ring lives in `egraph/src/classes.rs`, not `containers/`; given a descriptive container name here. |

Verus-internal types with no production public equivalent (proof scaffolding or
modeling choices, intentionally `pub` for the proofs): `CaptureBits`, `Frame`,
`ForkOrigin`, `NodeRef`, `ListHead`, `ListNode`, `DenseId31`, `DenseUsize`,
`OptElem`, `BNode`.

## 2. Method-level parity (the verified containers)

Status legend: **✓** verified (proved `ensures` capturing production behavior, no
`admit`/`external_body`); **◐** present but unproved (`external_body`
diagnostic); **✗** absent.

### Vec (the foundation)
| Production item | Verus | Notes |
|---|---|---|
| `with_store` / `new` | ✓ | both `ParallelStore` and `InlineStore` backends verified against `DiffStore` |
| `push` / `pop` / `set` / `get` | ✓ | incl. **pop into a marked region** (the hard case), first-write-wins, proved |
| `len` / `is_empty` / `depth` | ✓ | |
| `mark` / `restore` | ✓ | **headline theorem**: after `restore(token)`, `view() == snapshots[token.frame_idx]`, at arbitrary nesting depth |
| `is_valid_token` + ForkHistory | ✓ | branch-cut safety: `is_valid` exec-walk proved == `fork_valid` spec; stale/cross-branch tokens rejected |
| `View` / `ViewIter` iteration | ✓ | read-only handle + iterator, contracted |
| `TRACK = false` | ✓ | proved observationally a plain `std::Vec`, zero diff-log overhead while unmarked |
| `as_slice` | ◐ | `external_body`, no spec (a backend-specific fast path outside the persistence contract) |
| `total_bytes` / `tracking_bytes` / `heap_bytes` | ◐ | `external_body` capacity diagnostics; no spec content (production identical) |

The Vec spec is, if anything, **stronger** than production: production never
states the reconstruction theorem; we prove it. The capture flags additionally
use a **packed `Vec<u64>` (`CaptureBits`)** proved to refine a ghost `Seq<bool>`,
8× denser than a `Vec<bool>`, matching production's bitset density.

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
`is_empty` / `mark` / `restore`: **✓**, against the **real spec**, not just
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

Four items listed here as gaps in earlier revisions of this audit have since
been closed; they are recorded below with their current home, because in-code
comments and the design chapters still cite this section:

1. **`id.rs`: the `define_id7/15/31/63!` macros + their generated id types** —
   **closed**. `src/id_macros.rs` provides the family with full proofs, and
   `src/lib.rs` re-exports the generated `SparseSetId`/`UseListId`/`UseNodeId`.
   `DenseId31` remains the hand-written instance the niche proofs build on.
2. **`IdFactory`** (sequential id allocation) — **closed**. `src/id_factory.rs`
   provides `IdFactory` plus `IdRangeError` (`alloc`/`try_alloc`/`count`).
3. **`bitset.rs`** as a public `BitSet` type — **closed**. `src/bitset.rs`
   provides it, deliberately kept outside the container proofs; the *internal*
   packed-bit need is still met by the verified `CaptureBits` inside
   `ParallelStore`.
4. **`sorted_cursor.rs`**: the `SortedCursor` trait and ordered cursor
   iteration — **closed**. `src/sorted_cursor.rs` defines the trait and
   `src/sorted_vec_cursor.rs` verifies the galloping `SortedVecCursor` the
   e-graph's `seek` runs on.

The one remaining gap:

5. **`Default`/`Clone`/`Debug`/`Hash` derives and the broader trait surface** of
   the production id types, out of scope.

## 4. The B+tree

**Fully verified**: generic `BPlusTreeSet<K: DenseId, L: NodeLayout, S:
SearchKind, const TRACK>` over the real bit-stealing ids (`DenseId31`/`DenseId63`)
and all six packed node layouts; `bplus` 139, `bplus_tree` 124, `bplus_layout`
311, `bplus_search` 9 facts, 0 `external_body`, 0 `admit`/`assume`. Insert (with
split propagation, new-root growth, and the O(1) append fast path) is total and
carries its full model transition; in-order traversal and `seek` are proven sound;
the arena provably never overflows; `mark`/`restore` work. Insert-only, matching
production (no `remove`).

**Performance gaps, no soundness gap.** All latent — `egraph` never calls
`from_sorted` and never instantiates `BPlusTreeSet` outside benches — but each is a
place where a *verified* method is materially worse than its production
counterpart. A 1:1 body diff against `containers/src/bplus.rs` found three
([Design Ch. 10 §5](../design/10-bplus-tree.md), harness at
`containers-conformance/examples/onesite_bplus.rs` — *not* `bulkload.rs`, which
understates gaps; see Ch. 11); all three are fixed, and a fourth, invisible to any
body diff because it lives below the source, was found later and fixed too:

- **The `S: SearchKind` parameter was never called — FIXED.** `grep -c 'S::'` over
  the verified tree returned 0, against six production call sites. Five
  hand-written linear scans stood in for it, while two verified binary searches
  (`leaf_find_ge`, `find_child`) sat in the same file used only by `seek`. All five
  now dispatch to them. Random-order insertion went from 1.4-1.5x to **0.9-1.0x**
  on `bulkload.rs`, and the proofs got smaller. (That 0.9-1.0x reading was the
  harness flattering us — on `onesite_bplus.rs` the same build was still ~1.3x,
  which is what the fourth item below fixes.)
- **`insert` had no append fast path — FIXED** (was 1.4-2.3x and growing with `n`,
  now **1.0-1.1x**). Production caches `last_leaf` and appends in O(1) when the key
  extends the rightmost leaf, skipping the descent entirely. Not specific to bulk
  building — it cost on *any* ascending insertion, the common case for id-keyed
  indexes. Verified via `last_leaf_ok` as a `wf` clause plus `lemma_append_last_wf`
  / `lemma_binds_append_last`; sound because the rightmost child has no separator
  above it, so growing it upward cannot break cross-node ordering.
- **`from_sorted` looped `insert` instead of bulk loading — FIXED** (was 30-72x, now
  **3.7-6.6x**). It now calls `fast_append_run`, which fills the *entire* rightmost
  leaf with one arena read and one arena write, falling through to `insert` only at
  the leaf-full boundary (once per `leaf_cap` keys). Verified by generalizing the
  single-key fast path from a key to a run: `lemma_append_run_wf` +
  `lemma_binds_append_run`, which inherit the same soundness argument (the rightmost
  child has no separator above it). The residual is entirely the boundary split; see
  [Design Ch. 10 §5.2.3](../design/10-bplus-tree.md) for the measurement that
  isolates it and for what a fully verified level-builder would still need.
- **The bisections had production's *shape* but not its *lowering* — FIXED** (pure
  descent was +15…+21%, now **~20% faster** than production). Production calls
  `slice::partition_point`, which uses `core::hint::select_unpredictable` internally
  and therefore compiles its base update to `cmovbe`. Our hand-written loop had the
  same unconditional-`size -= half` shape and *read* branchless as
  `base = if lt { mid } else { base }` — but LLVM's if-conversion heuristic judged
  the compare predictable and emitted `ja`/`jmp`; an arithmetic mask folds back to
  the same branch. On shuffled keys that compare is a coin flip, mispredicting at
  ~half the levels of every descent. All four bisections now route the base update
  through `bplus_layout::sel_usize` (an `external_body`, `unsafe`-free wrapper over
  the intrinsic); the tail step keeps a plain `if`, which lowers to `adc`. See
  [Design Ch. 10 §5.1.1](../design/10-bplus-tree.md).

**How the root cause was pinned down — and first got wrong.** Not by comparing verus
to production, which only yields ratios. By pricing each production feature against
**production's own** baseline: production is the only implementation with *both*
features, so measuring bulk-load vs ascending-insert vs shuffled-insert *within one
binary* isolates each with zero cross-crate confound. Two shapes did the work —
production's ascending-insert cost is **flat** in `n` (34.70 → 36.89 ns/key from 10k
to 1M, which is only possible if no descent is happening), and its bulk-load cost
*falls* with `n`. The three independently-measured factors multiply back to the
observed total to three significant figures at two different `n`.

The shuffled column was then over-read. At 0.80-1.03x on `bulkload.rs` it was taken
to prove "the descent itself was never the problem, so recursion, bounds checks, and
proof machinery cost nothing measurable" — a conclusion about *three* mechanisms
drawn from *one* aggregate number, on the harness that understates gaps. On
`onesite_bplus.rs` the descent was +15…+21%, and it was a real mechanism (the
bisection's lowering, fourth item above). **A ratio near 1.0 bounds a sum, not each
addend** — and only if you trust the harness that produced it.

**But the *explanation* attached to that decomposition was wrong**, and it stayed
wrong in these docs for a while: the bulk-vs-append column was called a
complexity-class difference. Once the append fast path landed, both sides do O(n)
node visits, and production's own append loop is *still* 20-48x slower than
production's own bulk load — two O(n) loops cannot differ by 40x for a complexity
reason. The actual mechanism is the **per-key whole-node copy** (`get_index`/
`set_index` move 64-512 bytes in and out per key; priced in isolation, 20-25x an
in-place slot write). **A correct factorization tells you which column the cost is
in, not what that column is buying** — that distinction is the transferable lesson,
and it is what turned a "needs a whole new proof" item into a 100-line one, since
amortizing a copy needs far less than building a tree bottom-up.

**The audit's question was too narrow.** This table asks "is this method
verified?" — `from_sorted` answered yes while touching one node per key where
production touched one per leaf, and the missing fast path was invisible to both the
proof and the property tests, since neither observes how many nodes were touched.
The `SearchKind` case is sharper still: the *signature* matched production exactly,
generic parameter and all, and the trait behind it was fully verified. Only the call
graph was wrong.

Four habits follow, and the other containers deserve all four:

1. **Diff the production body**, for fast paths and cached state, not just the
   signature and the contract.
2. **Check that generic strategy parameters are actually dispatched to** — `grep -c
   'S::'`. A pluggable-strategy A/B that shows *no* difference between impls is
   evidence neither one is running, not evidence they are equivalent.
3. **To test a per-item cost, vary only that cost.** The first probe of the
   node-copy hypothesis swept node size across layouts, saw flat per-key cost, and
   called the hypothesis falsified. Invalid: bigger nodes copy more bytes per key
   but split proportionally *less* often, so the effects cancel and manufacture
   flatness. Never vary a geometry parameter that other costs also depend on — the
   same failure mode as Ch. 11's positional confound, in a different disguise.
4. **When a source-level optimization measures as no-change, check that it was
   compiled.** A null result has two readings — the mechanism is innocent, or the
   change never reached the machine code — and only disassembly separates them. A
   branchless rewrite of the bisection was written, verified, benchmarked, measured
   at ±1%, and used to acquit branch prediction; the source was branchless and the
   object code never was. Diffing the two arms' asm for the *same* function
   (`cmovbe` in production, `ja` in ours) found it.

The complete design and proof-status accounting is its own chapter:
[Design Ch. 10: The B+Tree Set](../design/10-bplus-tree.md). It is not repeated
here.

## 5. Deliberate divergences (documented, not gaps)

- **`T: Copy + Default`** throughout, vs production's `T: Clone`. `Copy ⊂ Clone`
  suffices for the e-graph's id-typed payloads; `Default` enables the DoS-free
  bounded-capture pop (see [06-restore-regrow-alternatives](../design/06-restore-regrow-alternatives.md)).
- **`ListArena` uses `ParallelStore` + `NodeRef{some,idx}`**, not production's
  `InlineStore` + `Opt`'s stolen bit, same logical content, avoids porting the
  composite-`Tagged` niche for the node/head structs.
- **`usize` ids in several containers** vs production's `DenseId` newtypes:
  `DenseId31` shows the niche encoding verifies; the containers themselves index
  by plain `usize` for proof simplicity.
- **`restore` ghost-model parameters** (ListArena, CircularList), a proof
  artifact (opaque tokens can't carry the ghost model), not a runtime API change.
- The B+tree verifies the generic `NodeLayout` (all six packed size variants
  via the `gen_layout_u32!`/`gen_layout_u64!` macros), matching production's
  geometry.

## 6. What the PR claims

> Verifies the semi-persistent **vector** (exact diff-log reconstruction at
> arbitrary mark nesting, incl. pop into a marked region; fork-history
> branch-cut safety; `TRACK=false` zero-overhead), the flat-arena container
> family built on it (**AppendOnlyVec, Map, SparseSet, ListArena**, plus the
> e-graph **circular class-list**), and the recursive **BPlusTreeSet** (insert
> with split propagation, total; sound in-order traversal and `seek`; arena
> never overflows; `mark`/`restore`), all with machine-checked specifications
> and **no `admit`s or `assume`s**. Storage is verified for both the inline
> (niche-bit) and parallel (packed `Vec<u64>` bitset) backends, and real
> MSB-stealing `DenseId31`/`DenseId63` ids exercise the niche obligations
> non-vacuously.
>
> Also verified: the `define_id7/15/31/63!` id-macro family and `IdFactory`,
> and the `SortedCursor` trait with the galloping `SortedVecCursor`. A public
> `BitSet` ships, deliberately outside the container proofs.
>
> **Out of scope (§3):** the `Default`/`Clone`/`Debug`/`Hash` derives and
> broader trait surface of the production id types. A small set of convenience
> methods (`iter`/`get_mut`/key-count `len`) are omitted from otherwise-verified
> containers.

Per-module verified counts are in `verify-all.sh` output; the tally is 1405
verified, 0 errors, 0 `admit`s/`assume`s across 31 module entries.

---
[Design Table of Contents](../design/00-table-of-contents.md)
