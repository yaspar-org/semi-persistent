# B+Tree Set — Design and a Bi-Abductive Proof Plan (future work)

*Scoping document for verifying `BPlusTreeSet`, the largest container in the
production crate ([`containers/src/bplus.rs`](../../../containers/src/bplus.rs),
~1040 lines). The proof is **not yet attempted**; this records the data
structure, the well-formedness invariant, and how an `insert` proof decomposes
under the [bi-abductive / dynamic-frames](../design/09-arena-aliasing-dynamic-frames.md)
discipline the other arena containers already use, so the eventual effort starts
from a settled spec rather than a blank page.*

[Design Table of Contents](../design/00-table-of-contents.md)

## 1. Why this is its own document

Every other container we verified is a *flat* arena structure: one level of
indices, and a well-formedness invariant that is a property of a partition or a
permutation. A B+tree is **recursive and balanced**. Its invariant has to pin
down, simultaneously, sortedness *across* a tree of nodes, that all leaves sit
at the same depth, that the leaf-level linked list agrees with the tree, and
fixed-capacity packing — and its one interesting mutation, `insert`, can **split
a node and propagate the split up the root-to-leaf path**, touching a whole
path's worth of nodes in one call. That is a categorically larger proof than
SparseSet or ListArena, comparable to the original `Vec` reconstruction effort,
and it deserves to be planned before it is built.

One scoping fact makes it tractable: **production's `BPlusTreeSet` is
insert-only**. There is no `remove`. The API is `new` / `insert` / `contains`
(via cursor) / `len` / `mark` / `restore` / `from_sorted`, plus an ordered
`cursor`. So the hard rebalancing direction — merge/borrow on deletion — is
simply out of scope; we owe only **insert-with-split** and the read/iteration
side. That roughly halves the classical B+tree verification burden.

## 2. The data structure

All nodes — leaf and internal — share one cache-aligned struct in a single
arena `VecI<L::Node>`, indexed by `L::ArenaIdx` (`u32` or `usize`); a separate
one-element `meta` vector holds the header (`root`, `last_leaf`, `nkeys`). The
node is fixed-size and packed:

```
#[repr(C, align(N))] struct Node {        // N ∈ {64,128,256,512}
    flags: u8,            // bit0 = is-leaf; bit1 = Tagged capture bit
    count: u8,            // # keys currently used
    _pad: u16,
    data: [Word; DATA_LEN],   // Word = u32 or u64; DATA_LEN = LEAF_CAP
    link: Link,           // leaf: next-leaf arena index; internal: last child
}
```

`NodeLayout` is a compile-time trait fixing the geometry (`LEAF_CAP`,
`INTERNAL_KEY_CAP`, `INTERNAL_CHILD_CAP`, `MAX_DEPTH`) for each `(size, word)`
pairing, with `INTERNAL_CHILD_CAP = INTERNAL_KEY_CAP + 1` and
`2 · INTERNAL_KEY_CAP ≤ DATA_LEN`. Two readings of `data`:

- **Leaf**: `data[0..count]` are the sorted keys; `link` is the arena index of
  the next leaf in key order (NIL `= ArenaIdx::MAX` at the last leaf). The
  header's `last_leaf` caches the rightmost leaf for the sorted-append fast path.
- **Internal**: `data[0..count]` are `count` separator keys; the `count+1`
  children are packed into the same node — the first `INTERNAL_KEY_CAP` in
  `data[INTERNAL_KEY_CAP .. 2·INTERNAL_KEY_CAP]` (so child `i` for
  `i < INTERNAL_KEY_CAP` lives at `data[INTERNAL_KEY_CAP + i]`), and the **last
  child** (index `INTERNAL_KEY_CAP`) reuses the `link` field. That overload is
  unambiguous because the node kind is known from `flags` bit 0: `link` is a
  leaf sibling pointer iff the node is a leaf, and the last-child slot iff it is
  internal; a leaf never indexes children and an internal node never walks the
  leaf chain. The `internal_child(i)` / `set_internal_child(i, _)` accessors
  encode this slot arithmetic. Child `i` holds keys `< data[i]`; child `count`
  holds keys `≥ data[count-1]`.

On u64 layouts the in-`data` child slots are `u64` while `link` is `usize`; both
are value-preserving views of an `ArenaIdx` on a 64-bit host (the crate
feature-gates 32-bit), and `ArenaIdx::MAX` is reserved as NIL so no real index
collides with the sentinel.

Each `Node` is `Tagged` (the capture bit is `flags` bit 1), so the whole tree is
a `Vec<Node>` over the verified semi-persistent backend — `mark`/`restore`
compose for free, exactly as for the other arena containers.

## 3. The abstract model and well-formedness

### 3.1 Abstract model

A `BPlusTreeSet` represents a **finite sorted set of keys**. The cleanest ghost
model is a `Seq<K::Index>` that is strictly increasing (equivalently a
`Set<nat>` plus the statement that an in-order traversal yields it sorted). The
two read operations anchor the spec:

- `contains(k)  ⟺  k ∈ model`
- the cursor's in-order walk yields exactly `model`, ascending.

`insert(k)` then refines `model := model ∪ {k}` and returns `k ∉ old model`.

### 3.2 The `wf` invariant (the heart of it)

Unlike the flat containers, `wf` is a predicate over a **ghost tree** that
mirrors the arena. The plan is to carry a ghost `tree: TreeShape` (an inductive
description: a leaf carries its key sequence; an internal node carries its
separator keys and child subtrees) and tie it to the arena. The clauses:

1. **arena in-range** — every `root` / child / `link` index is NIL or a real
   allocated node (the only per-index constraint, as in [§10](../design/01-verification-design.md);
   *no* "points at a smaller index" ordering — the tree shape comes from the
   ghost model, exactly the lesson from the ListArena rebuild).
2. **shape / acyclicity** — the ghost `tree` is a finite tree whose nodes are
   *distinct* arena indices (disjointness: no node appears twice — the
   dynamic-frames separation clause), and `root` is its root.
3. **balanced** — all leaves are at the same depth (carry a ghost `height`; every
   root-to-leaf path has length `height`).
4. **node-local sortedness** — within every node, `data[0..count]` is strictly
   increasing.
5. **cross-node ordering (the B+tree key invariant)** — for an internal node
   with separators `s[0..count]` and children `c[0..count]`, every key in the
   subtree under `c[i]` is `< s[i]`, and every key under `c[count]` is
   `≥ s[count-1]`; recursively. This is what makes the search-and-descend in
   `insert`/`contains` land in the right leaf.
6. **capacity** — `count ≤ LEAF_CAP` (leaf) / `≤ INTERNAL_KEY_CAP` (internal),
   and (the B+tree balance lower bound for non-root nodes) `count ≥ ⌈cap/2⌉`.
   *Note*: with insert-only, the lower bound is only ever *established* by
   splits, never threatened by deletes — a real simplification.
7. **leaf-link consistency** — following `link` from the leftmost leaf visits
   every leaf exactly once in ascending key order, ending at `last_leaf` with
   NIL; the concatenation of the leaves' key sequences is the abstract `model`.
   This is a second, independent "ghost sequence over arena ids" view (cf.
   ListArena), and clause 7 is the statement that it agrees with the tree view
   of clauses 4–5.

Clauses 4+5+7 together are the soundness of search: `contains` and `insert`
descend by `s::find_*` comparisons and must reach the unique leaf that would
hold `k`.

### 3.3 Arena-capacity sufficiency: why a `Word`-width index never overflows

The arena index type is paired with the key width on purpose: 31-bit keys use a
`u32` arena index, 63-bit keys a `usize` (= `u64` on 64-bit) index — the child
slots in `data` and the keys are the same `Word` width, so they overlay in one
`[Word; DATA_LEN]` array with no size mismatch, and the in-`data` child slots
need no cast (u32) or a value-preserving 64-bit cast (u64). The question this
raises: with only a `Word`-width index, can the arena run out of indices before
the key space is exhausted? The answer is no, by a counting argument that the
`wf` invariant already contains the ingredients for.

**The node-count bound.** Minimum occupancy (clause 6: every non-root node
`≥ ⌈cap/2⌉` full) forces the node count to be a fraction of the key count. Write
`m_L = ⌈LEAF_CAP/2⌉` (min keys per non-root leaf) and `d = ⌈CHILD_CAP/2⌉` (min
children per non-root internal node). For `N` keys:

```
#leaves   L ≤ N / m_L
#internal I ≤ L / (d − 1)          (geometric series up the levels)
#nodes    M = L + I ≤ L · d/(d−1) ≤ (N / m_L) · d/(d−1)
```

For `Layout64U32` (`LEAF_CAP = 14`, `CHILD_CAP = 8`, so `m_L = 7`, `d = 4`):
`M ≤ (N/7)·(4/3) = 4N/21 ≈ 0.19 · N`. So **`M < N`** — strictly fewer nodes than
keys — for every layout (`cap ≥ 14`).

**Sufficiency.** Chain that with the width pairing:

```
M  <  N  ≤  keyspace  =  ½ · max_nat(ArenaIdx)
└──┬──┘    └─────────────────┬─────────────────┘
 occupancy        31-bit keys ↔ u32 index : keyspace = 2³¹ = 2³²/2
                  63-bit keys ↔ usize     : keyspace = 2⁶³ = 2⁶⁴/2
```

The index type has exactly one bit more than the key space, so the live node
count occupies at most half of it and `ArenaIdx::MAX` (reserved as NIL) sits in
the unused half. For `Layout64U32` the worst case is `M ≈ 0.19 · 2³¹ ≈ 4.1×10⁸`
nodes against a usable `u32` capacity `≈ 4.29×10⁹` — roughly 10× headroom. So
31-bit keys use a *native* 32-bit arena index (never a truncated `usize`), and
it provably suffices.

**What is enforced vs. proved (today).** The verified code enforces overflow
safety locally and honestly: `Vec::push` carries `view().len() + 1 < max_nat()`
and `insert` requires arena headroom as a precondition, so reaching
`ArenaIdx::MAX` is a precondition failure, never a silent wraparound. The global
sufficiency theorem above is, for now, a meta-level argument (as in production).
It *is* formalizable from the existing invariant — `tree_wf` carries the
occupancy clause and `tree_disjoint` makes `|tree_ids(t)|` the true distinct node
count, so a structural induction

```
tree_wf(t,h,cap,key_cap,root) ∧ tree_disjoint(t)
    ⟹ |tree_ids(t)| ≤ ceil_div(|tree_keys(t)|, m_L) · d/(d−1) + 1
```

would let `insert`'s headroom precondition be *derived* from the key type's bound
(`K::id_bound() ≤ keyspace`) rather than assumed. Deferred to a milestone after
the split/propagation insert (it needs multi-level trees to be meaningful);
tracked separately.

## 4. Insert, and its bi-abductive decomposition

`insert(k)` has three layers, and each maps onto the
[frame / anti-frame](../design/09-arena-aliasing-dynamic-frames.md) split.

**(a) Descend.** Walk root→leaf, recording the path `[(node, child-pos); MAX_DEPTH]`
on a stack, using `find_gt` at internal nodes to pick the child. The **anti-frame**
the descent abduces is the cross-node-ordering invariant (clause 5): it is what
guarantees the walk reaches the *unique* leaf whose key range contains `k`, so
that inserting there preserves sortedness.

**(b) Leaf insert, no split (the common case + the sorted-append fast path).**
If the target leaf has `count < LEAF_CAP`, shift and insert. The **footprint** is
exactly one node (the leaf); the **frame** is the entire rest of the tree —
every other node's bytes are untouched, so its `wf` sub-facts carry verbatim, and
the only obligations are local: the leaf stays sorted (clause 4) and its key set
gained `k`. The fast path (`last_leaf`, append when `k >` the current max) is a
specialization with the same one-node footprint. The **anti-frame** for taking
this branch is precisely `count < LEAF_CAP` — Verus will force it, and it is the
production code's `if n < L::LEAF_CAP` guard.

**(c) Split and propagate (the hard case).** A full leaf splits into two
(`mid = ⌈cap/2⌉`), the new right leaf is spliced into the leaf-link, and a
**separator key + new child pointer are pushed to the parent**; if the parent is
also full it splits too, and so on up the recorded path, possibly creating a new
root. The proof obligation is an **induction up the path stack**: maintain the
loop invariant *"the tree below the current level is a valid B+tree forest whose
key multiset is `old ∪ {k}`, and `(pkey, pchild)` is the separator/child still
to be inserted one level up."* Each iteration is, again, a frame step (only the
current parent and the new sibling are in the footprint; their siblings and
unrelated subtrees are framed out) plus a local re-establishment of clauses
4–6 for the two split halves and clause 7 if a leaf was involved. The split's
key-redistribution is index arithmetic over fixed arrays — bounded, decidable,
and (as in `CaptureBits`/`SparseSet`) the place where `nat`/bounded-int reasoning
does the work; the *structural* facts come from the ghost tree, not from the
raw `copy_within` calls.

The termination/measure for the propagation loop is the recorded depth, bounded
by `MAX_DEPTH` (≤ 24); the ghost `height` increases by exactly one iff a new
root is created.

## 5. Suggested milestone breakdown

Ordered so each milestone leaves the module green, smallest provable unit first:

1. **Model + `wf` + `new`/`is_empty`/`len`.** Define `TreeShape`, the seven
   clauses, and prove the empty tree (single empty leaf) is `wf` with
   `model == []`. No mutation yet — this is where the invariant design is
   validated or revised.
2. **`contains` (cursor read).** Prove the descend-and-search reaches the leaf
   whose range holds `k`, and `contains(k) ⟺ k ∈ model`, using clauses 4–5.
   Establishes the search-soundness lemmas the inserts reuse.
3. **`insert`, no-split only.** Restrict (initially with a precondition, later
   discharged) to the `count < LEAF_CAP` case; prove the one-node-footprint frame
   argument and `model := model ∪ {k}`. This is the SparseSet-scale step.
4. **Leaf split, no propagation** (parent has room). Prove the two-leaf split +
   leaf-link splice + single separator insert into a non-full parent.
5. **Full split propagation + new root.** The induction up the path stack; the
   hardest milestone, and the one to budget the most for.
6. **`mark`/`restore`** — compose from the inner `Vec` (mechanical, mirrors the
   other containers), with a `bplus_snap_wf` restore precondition.
7. **`from_sorted`** bulk-build (optional; a bottom-up construction with its own
   invariant) and the ordered-cursor iteration theorem (cursor yields `model`
   ascending).

Milestones 1–3 alone deliver "a verified sorted-set `contains` + the easy
insert", a coherent partial result; 4–5 are where the genuine B+tree proof
lives; 6–7 round it out. Deletion remains out of scope unless production grows a
`remove`.

## 6. Reused machinery (nothing starts from zero)

- **Semi-persistence** (`mark`/`restore`) composes from the verified `Vec` over
  `ParallelStore`, exactly as for ListArena / SparseSet — milestone 6 is
  near-mechanical.
- **The arena/dynamic-frames discipline** ([Chapter 9](../design/09-arena-aliasing-dynamic-frames.md))
  applies directly: a ghost description (here a tree, plus the leaf-link
  sequence), in-range-only index constraints, disjointness as a `wf` clause,
  and frame/anti-frame operation proofs.
- **Bounded-int / array-index reasoning** as developed for `CaptureBits` and the
  `SparseSet` permutation lemmas carries to the split's key redistribution.
- **`Tagged` nodes** are already understood (the node's `flags` capture bit is a
  `Tagged` impl just like `DenseId31`'s stolen MSB).

The one genuinely new ingredient is the **recursive, height-balanced ghost tree
and its induction** — which is why this is a future, dedicated effort rather than
another increment on the flat-container family.

---
[Design Table of Contents](../design/00-table-of-contents.md)
