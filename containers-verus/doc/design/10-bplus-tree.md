# The B+Tree Set: Design and Proof

*`BPlusTreeSet` is the largest container in the crate and the only recursive,
height-balanced one. This chapter is the design record and the proof-status
reference: §1–4 describe the structure, invariant, and how the proofs are
organized; §5 is the current accounting of what is verified. Companion to the
arena/dynamic-frames method in [Chapter 9](09-arena-aliasing-dynamic-frames.md)
and the trust boundary in [Chapter 2](02-trust-boundary.md).*

[Design Table of Contents](00-table-of-contents.md)

Every other verified container is a *flat* arena structure: one level of indices,
and a well-formedness invariant that is a property of a partition or a
permutation. A B+tree is recursive and balanced. Its invariant pins down,
simultaneously, sortedness *across* a tree of nodes, that all leaves sit at the
same depth, that the leaf-level linked list agrees with the tree, and
fixed-capacity packing, and its one interesting mutation, `insert`, can split a
node and propagate the split up the root-to-leaf path, touching a whole path's
worth of nodes in one call. That makes it a larger proof than SparseSet or
ListArena, comparable to the original `Vec` reconstruction.

One fact makes it tractable: production's `BPlusTreeSet` is insert-only, there is
no `remove`. So the hard rebalancing direction (merge/borrow on deletion) is out
of scope; the obligation is insert-with-split plus the read/iteration side,
roughly half the classical B+tree verification burden.

## 1. The data structure

All nodes, leaf and internal, share one packed, cache-aligned struct in a
single arena `Vec<L::Node>` indexed by `L::ArenaIdx` (`u32` or `usize`); the
header (`root`, `nkeys`) lives in exec fields alongside it. `NodeLayout` is a
compile-time trait fixing the geometry (`LEAF_CAP`, `INTERNAL_KEY_CAP`,
`CHILD_CAP = KEY_CAP + 1`) for each `(size, word)` pairing; six layouts are
stamped out by the `gen_layout_u32!` / `gen_layout_u64!` macros (sizes 64–512
bytes, `Word ∈ {u32, u64}`). Two readings of the packed `data: [Word; DATA_LEN]`:

- **Leaf**: `data[0..count]` are the sorted keys; `link` is the arena index of
  the next leaf in key order (`NIL = ArenaIdx::MAX` at the last leaf).
- **Internal**: `data[0..count]` are `count` separator keys; the `count+1`
  children pack into the same node: the first `KEY_CAP` in the upper half of
  `data`, and the **last child reuses the `link` field**. The overload is
  unambiguous because the node kind is known from a `flags` bit: `link` is a leaf
  sibling pointer iff the node is a leaf, the last-child slot iff internal. Child
  `i` holds keys `< data[i]`; child `count` holds keys `≥ data[count-1]`.

Each `Node` is `Tagged` (the capture bit is a `flags` bit), so the whole tree is
a `Vec<Node>` over the verified semi-persistent backend; `mark`/`restore`
compose, exactly as for the other arena containers (§4).

A deliberate width pairing: 31-bit keys (`DenseId31`) use a `u32` arena index,
63-bit keys (`DenseId63`) a `usize` (= `u64` on 64-bit, feature-gated). The
in-`data` child slots and the keys are the same `Word` width, so they overlay in
one array with no size mismatch; the child slots need no cast (u32) or a
value-preserving 64-bit cast (u64). `ArenaIdx::MAX` is reserved as NIL, so no
real index collides with the sentinel. This pairing is also what makes the arena
provably never overflow (§2.3).

## 2. The abstract model and well-formedness

### 2.1 Abstract model

A `BPlusTreeSet` represents a **finite sorted set of keys**. The ghost model is a
`Seq<nat>` (`tree_keys`) that is strictly increasing. Two read operations anchor
the spec:

- `contains(k)  ⟺  k ∈ model`
- the cursor's in-order walk yields exactly `model`, ascending (§3c).

`insert(k)` refines `model.to_set() := model.to_set() ∪ {k}` and returns
`k ∉ old model`.

### 2.2 The `wf` invariant (the heart of it)

`wf` is a predicate over a **ghost tree** (`Tree`, in `bplus_tree.rs`: a leaf
carries its key sequence; an internal node carries separators and child subtrees)
tied to the arena by a flat `binds` bridge. Its clauses:

1. **arena in-range**: every `root` / child / `link` index is NIL or a real
   allocated node. This is the *only* per-index constraint: there is **no**
   "points at a smaller index" ordering; the tree shape comes from the ghost
   model. (The hard-won lesson from the ListArena rebuild, [Ch. 9 §4](09-arena-aliasing-dynamic-frames.md).)
2. **shape / disjointness**: the ghost `Tree`'s nodes are *distinct* arena
   indices (`tree_disjoint`: no node appears twice, the dynamic-frames
   separation clause), with `root` its root.
3. **balanced**: all leaves at the same depth (`tree_wf` carries a `height`;
   every root-to-leaf path has length `height`).
4. **node-local sortedness**: within every node, `data[0..count]` strictly
   increasing.
5. **cross-node ordering (the B+tree key invariant)**: for an internal node with
   separators `s` and children `c`, every key under `c[i]` is `< s[i]`, every key
   under `c[count]` is `≥ s[count-1]`, recursively. This is what makes
   search-and-descend land in the right leaf.
6. **capacity / occupancy**: `count ≤ LEAF_CAP` / `≤ KEY_CAP`, and (the balance
   lower bound for non-root nodes) `count ≥ ⌈cap/2⌉`. With insert-only this lower
   bound is only ever *established* by splits, never threatened by deletes.
7. **leaf-link consistency**: following `link` from the leftmost leaf visits
   every leaf once in ascending key order ending at NIL; the concatenation of the
   leaves' keys is the abstract `model`. A second, independent "ghost sequence
   over arena ids" view (cf. ListArena), and clause 7 states it agrees with the
   tree view of clauses 4–5.

Clauses 4+5+7 together are the **soundness of search**: `contains` and `insert`
descend by separator comparisons and reach the unique leaf that would hold `k`.

Two further standing facts, used pervasively:

- `model_bounded`: every model key is `< K::id_bound()`. The `K → K::Index`
  storage coercion widens to the word type, which is wider than the id's valid
  range; this clause re-asserts the range that production enforces with a runtime
  assert, and is what lets the cursor's `key()` rebuild the exact `K`.
- `arena.len() == node_count(tree@)`: no dead arena slots. Insert-only with
  in-place `set` + one `push` per split means every allocated slot is live, the
  link that turns the node-count bound (§2.3) into a bound on `arena.len()`.

### 2.3 Arena-capacity sufficiency: the arena provably never overflows

With only a `Word`-width arena index, can the arena run out of indices before the
key space is exhausted? **No**, and unlike production (which argues this at the
meta level) it is *proved*, so `insert` carries **no caller capacity
precondition**: it is total on any `wf` tree.

The argument flips the usual direction. Assume the arena were full (`M ≈ 2^N`
nodes) and ask the *minimum* number of distinct keys such a tree must hold. Keys
live only in leaves, so fewest-keys = fewest-leaves = most-internal-heavy =
minimum branching, i.e. the tree sitting at the occupancy floor (clause 6). With
`m_L = ⌈LEAF_CAP/2⌉ ≥ 7` keys per non-root leaf and every non-root internal node
having `≥ 2` children:

```
L_min · node_count(t)  ≤  2 · |tree_keys(t)| + L_min          (the structural bound)
```

Chain with two facts the invariant already gives: the model is a strictly-sorted
set bounded by `id_bound`, so `|tree_keys| ≤ id_bound`; and the width pairing
makes `id_bound = ½ · max_nat(ArenaIdx)` exactly (31-bit keys ↔ u32 index: 2³¹ =
2³²/2; 63-bit ↔ usize: 2⁶³ = 2⁶⁴/2). So

```
node_count ≤ max_nat / 7  ≪  max_nat,
```

with `arena.len() == node_count` (§2.2) and `height ≤ node_count`, giving
`arena.len() + height + 3 < max_nat`, exactly the headroom one more insert
needs. The proof is `lemma_arena_never_overflows`, composing a structural
node-count induction (`lemma_node_count_bound`) with the per-layout numeric facts
(`lemma_capacity_headroom`, `lemma_word_arena_same_width`) and the bit-stealing id
relation (`lemma_id_bound_word_relation`). The one-bit headroom, index space
exactly twice the key space, is the whole reason it closes with room to spare;
the occupancy floor (≥ 7 keys/leaf, not the trivial ≥ 1) supplies the slack to
also cover the `+ height + 3`.

### 2.4 Two design decisions, and why they hold up

**One arena-associated ghost `Tree`, not ghost subtree state on each node.** A
tempting alternative gives each node value a ghost field describing its own
subtree. We deliberately do not, for three reasons:

1. *It is the ListArena trap.* Node-local subtree state references children's
   ghost state in *other* arena slots, so reading one node's invariant
   transitively reads others, and a mutation's frame becomes "every node whose
   ghost field mentions a touched id", unbounded and pointer-chasing, exactly the
   shape that killed the first ListArena `wf` ([Ch. 9](09-arena-aliasing-dynamic-frames.md)).
2. *Semi-persistence makes it actively wrong.* The arena is semi-persistent;
   `restore` rewinds `view()`. The whole invariant is stated over `view()`, so a
   restore brings back a structurally valid prior tree for free (the `Vec` theorem
   does the work, because `wf` reads only `view()`). Node-local ghost state would
   have to be snapshotted and restored in lockstep and re-proven after every
   rewind. The single ghost `Tree` sidesteps this.
3. *The locality benefit is obtained without the coupling.* `subtree_wf(arena, t,
   …)` is a predicate about *one* ghost subtree, and `lemma_subtree_wf_frame` says
   a mutation outside `t`'s `tree_ids` preserves it, so the recursive insert
   reasons locally and frames the siblings, the upside of node-local state, while
   the ghost `Tree` stays one clean object off the arena.

The price is the framing machinery (`tree_disjoint`, `lemma_binds_frame`,
`lemma_subtree_wf_frame`, …): a *one-time fixed* cost (paid and verified) against
node-local state's *recurring* cost on every semi-persistence operation.

**The `link`-overloaded last child.** Overloading `link` as the last child of an
internal node forces a branch `if i < KEY_CAP { data[KEY_CAP+i] } else { link }`.
Storing all children in `data` instead would need `2·KEY_CAP + 1 ≤ DATA_LEN`,
forcing `KEY_CAP` down by one, a different branching factor and different split
points, i.e. observably a *different* data structure from production's, breaking
the parity this project requires. The overload's proof cost is fully contained: it
appears in exactly three layout-layer places (the `child_view` spec, the `child`
accessor, `set_internal_child`); everything above that line reasons through the
`child_view` abstraction and never sees the branch. Kept.

## 3. Insert, contains, and the cursor

### 3a. The bi-abductive insert

`insert` maps onto the [frame / anti-frame](09-arena-aliasing-dynamic-frames.md)
split in three layers:

- **Descend.** Walk root→leaf, picking the child with `find_gt` at each internal
  node. The anti-frame the descent relies on is cross-node ordering (clause 5):
  it guarantees the walk reaches the *unique* leaf whose key range contains `k`.
- **Leaf insert, no split** (the common case). If the target leaf has
  `count < LEAF_CAP`, shift and insert. The footprint is one node; the frame is
  the entire rest of the tree: every other node's bytes are untouched, so its
  `wf` sub-facts carry verbatim, and the only obligations are local (the leaf
  stays sorted, its key set gained `k`).
- **Split and propagate** (the hard case). A full leaf splits into two
  (`mid = ⌈cap/2⌉`), the right leaf is spliced into the leaf-link, and a
  separator + child pointer are pushed to the parent; if the parent is full it
  splits too, up to a possible new root. The crate verifies this as a
  **recursion** whose measure is the tree height (not production's explicit path
  stack): each level is a frame step (only the current parent and the new sibling
  are in the footprint) plus a local re-establishment of clauses 4–6 for the two
  halves, and clause 7 if a leaf was involved. The split's key redistribution is
  bounded array-index arithmetic; the *structural* facts come from the ghost tree.

`insert` carries its full model transition (`model'.to_set() == model.to_set() ∪
{k}`, `added == !contains`): for an insert-only set, full functional correctness.
A new-root split increases `height` by one. The recursion's split/absorb
reconstruction (`reconstruct_*`, the `forest_binds`/`forest_links` machinery) is
proven with **zero `external_body`**.

### 3b. contains

A root-to-leaf descent reusing the same search-soundness lemmas: `contains(k) ⟺ k
∈ model`, from clauses 4–5.

### 3c. The cursor: sound in-order traversal and seek

`BPlusCursor` walks the leaf-link chain with a ghost model index, tied together by
`cursor_wf`. Two named, verified soundness theorems:

- **`theorem_traversal_in_order`**: `seek_first` then `key(); step()`* enumerates
  the strictly-sorted model: every key, ascending, no gaps and no duplicates.
- **`theorem_seek_never_skips`**: if `k` is in the set, `seek(k)` lands exactly on
  it (never steps past a present key); otherwise on the least key `> k`.

The descent and binary searches (`find_child`, `leaf_find_ge`) use overflow-safe
midpoints (`lo + (hi - lo)/2`), Verus-checked; the only value cast on the seek
path is `key()`'s `K::from_usize`, which round-trips exactly via `model_bounded`.
Cost is not *proved* logarithmic, but is validated empirically (a per-seek
node-visit ≈ `log_B(n)` test).

## 4. Semi-persistence: mark / restore

`mark` snapshots the tree (delegating to the arena `Vec`'s `mark`, recording the
exec header fields); `restore(token, Ghost(snap_tree))` rolls the arena back to
its frame snapshot and **re-establishes the full tree `wf`**: the structural half
factored as `tree_state_wf(arena, root, tree, nkeys)` so `restore`'s precondition
can state "the snapshot arena + the ghost tree live at the mark form a valid
B+tree." `restore` ensures `model == tree_keys(snap_tree)`. Both are total on a
`wf` tree. This is the same compose-from-the-inner-`Vec` pattern as ListArena /
SparseSet, plus the tree-level rollback theorem.

## 5. Proof status

**Fully verified, zero `external_body` in the B+tree modules, zero `admit`/
`assume`.** Per-module verified-fact counts (run `./verify-all.sh`):

| Module | Facts | Content |
|---|---|---|
| `bplus` | 127 | the tree: `wf`, `new`/`contains`/`len`, insert (+ arena-overflow proof), cursor + seek + the two soundness theorems, mark/restore |
| `bplus_tree` | 109 | the ghost `Tree` model and its structural lemmas |
| `bplus_layout` | 311 | the `NodeLayout` trait + six packed layouts + verified mutators |
| `bplus_search` | 5 | the `SearchKind` (binary search) trait |

What is guaranteed:

- **Every operation is total and proven**: `new`, `contains`, `len`, `is_empty`,
  `insert`/`insert_general`, `mark`, and the cursor all carry their full contracts
  with no caller-side capacity obligation (§2.3). For an insert-only set, `insert`
  is full functional correctness.
- **Sound in-order traversal and seek** (§3c): the cursor enumerates the sorted
  set with no gaps/dups, and seek never skips a present key.
- **The arena never overflows** (§2.3), proved from `wf` plus the static
  bit-stealing fact, not assumed.
- **First-class semi-persistence** (§4): verified `mark`/`restore` with a tree-level
  rollback theorem.

Runtime property tests (`cargo test`; Verus contracts erased) back the executable
code against a plain-`std` sorted-set oracle: `bplus_proptest` (insert / contains /
seek / step / key / tree mark-restore, plus the empirical log-cost check) and
`bplus_contract_fuzz` (the `NodeLayout` primitive postconditions against a hand
oracle).

**Trust boundary:** none specific to the B+tree; its modules have zero
`external_body`. The crate-wide trusted items (`ContainerId`, byte-accounting
diagnostics) are enumerated in [Chapter 2](02-trust-boundary.md).

**Scope:** insert-only, matching production (no `remove`). A bulk `from_sorted`
constructor is not implemented.

## 6. Reused machinery

Nothing started from zero. Semi-persistence composes from the verified `Vec` over
`ParallelStore` (as for ListArena / SparseSet). The arena/dynamic-frames discipline
([Chapter 9](09-arena-aliasing-dynamic-frames.md)) applies directly: a ghost
description (here a tree plus the leaf-link sequence), in-range-only index
constraints, disjointness as a `wf` clause, and frame/anti-frame operation proofs.
Bounded-int / array-index reasoning (developed for `CaptureBits` and the
`SparseSet` permutation lemmas) carries to the split's key redistribution; `Tagged`
nodes work exactly as `DenseId31`'s stolen MSB. The one genuinely new ingredient
was the recursive, height-balanced ghost tree and its induction.

---
[← Table of Contents](00-table-of-contents.md)
