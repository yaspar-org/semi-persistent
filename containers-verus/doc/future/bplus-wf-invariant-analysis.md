# B+tree `wf`: invariant design via ghost model + dynamic frames

*Working analysis for the `BPlusTreeSet` well-formedness invariant, written
before the proof so the invariant is right the first time. Applies the
ghost-id-set / dynamic-frames method of
[Ch 9](../design/09-arena-aliasing-dynamic-frames.md) and the bi-abduction
discipline (forward/backward passes, abduce the missing side condition) to the
specific shape of a B+tree, with the standard textbook B+tree invariants as the
target.*

## 0. Why design the invariant first

`contains`/`insert`/split are only provable if `wf` is *exactly* strong enough:
too weak and the postconditions don't follow; too strong (or false) and no
operation can re-establish it. The ListArena history is the cautionary tale
([Ch 9 §4](../design/09-arena-aliasing-dynamic-frames.md)): an early `wf` made
node content a *pointer-chasing* predicate and needed "`next` points at a
smaller arena index" to make the recursion terminate. That invariant is **false**
for `append`/`splice` (which link an old node forward to a freshly-allocated
larger id), so it could not be re-established and the proofs died. The fix was to
state content over a **ghost sequence**, leaving the only per-index constraint as
in-range. The B+tree must learn this lesson up front: its shape lives in a ghost
*tree*, and the arena ids are a representation of it, never the other way round.

## 1. The textbook B+tree invariants (the target)

A B+tree (insert-only here; production has no `remove`) over a key order `<`:

1. **Balanced.** All leaves are at the same depth. Equivalently every node
   carries a height `h`, leaves have `h = 0`, an internal node of height `h` has
   children of height `h-1`.
2. **Node-local sortedness.** Within a node, the `count` keys (leaf keys or
   internal separators) are strictly increasing.
3. **Cross-node (search) ordering.** For an internal node with separators
   `s[0..count]` and children `c[0..count]` (so `count+1` children): every key in
   subtree `c[i]` is `< s[i]`, and every key in subtree `c[count]` is
   `>= s[count-1]`. Recursively, the separators partition the key space so a
   root-to-leaf descent by comparison lands in the unique leaf whose range holds
   the query key. *This is the soundness-of-search invariant.*
4. **Capacity / balance bounds.** `count <= cap`; non-root nodes additionally
   `count >= ceil(cap/2)`. Insert-only means the lower bound is only ever
   *established* by splits, never threatened — a real simplification.
5. **Leaf-link consistency.** Following `link` from the leftmost leaf visits every
   leaf once in ascending key order, NIL-terminated; the concatenation of leaf key
   sequences is the abstract sorted-set model.

Clauses 2+3+5 together are *the* property `contains`/`insert` lean on: the search
descends by `find_*` comparisons and must reach the one leaf that would hold `k`.

Clause 5 is not optional. The reason this B+tree exists (over a plain sorted set)
is the leaf-link chain: it backs an incremental sorted cursor (`seek`/`next`/
`key`) used for leapfrog join in e-graph pattern matching. A model that cannot
express the chain cannot verify that cursor, so the link is a first-class `wf`
clause and a ghost view, not a detail to defer.

The framing that keeps it tractable (and avoids the "two views might diverge"
trap below): the chain is *bound to the tree*, single source of truth, exactly as
`child_view` is bound to `kids[i].id`. Define `tree_leaf_ids(t): Seq<nat>` as the
in-order (left-to-right) leaf-id sequence (a node fn + forest companion + a
`_cons` unfold lemma, the same idiom as `keys`). The link clause is then: for each
position `p` in `tree_leaf_ids`, `link_view(arena[lids[p]]) == lids[p+1]`, and NIL
at the last (NIL `= max_nat() - 1`, the `u32::MAX`/`usize::MAX` that `new_leaf`
writes, provably distinct from every real id because `push` keeps `len <
max_nat - 1`). There is no second independent ghost sequence to keep in sync — the
executable links simply realize the tree's own in-order leaf order. The property
the cursor needs, "walking links enumerates keys in ascending order," is then a
*derived* lemma from clause 3 (cross-node ordering), not an axiom.

## 2. The ghost model: a recursive tree over arena ids

Following Ch 9, the executable structure (arena `Vec<L::Node>` + `root` id) is a
*representation* of a ghost mathematical object, and `wf` ties them together. For
a B+tree the natural ghost object is a **recursive tree**, not a flat id-set:

```
ghost enum Tree {
    Leaf  { id: nat, keys: Seq<nat> },                 // keys as as_nat values
    Inner { id: nat, seps: Seq<nat>, kids: Seq<Tree> },
}
```

Two ghost views are derived from it (mirroring the two ListArena/CircularList
views — a tree view and a linear view that must agree, clause 5):

- `ids(t) : Set<nat>` — every arena id appearing in `t` (its node footprint, the
  dynamic-frames *region*).
- `keys(t) : Seq<nat>` — the in-order key sequence (leaves left to right). This is
  `model()`.

The arena binding: a ghost map (or just the arena itself) sends each `id` in
`ids(tree)` to the `L::Node` value at that arena slot, and `wf` says that node's
*observable fields* (`is_leaf`, `count`, `keys_view`, `child_view`, `link`) match
the ghost node at that id. So the executable `child`/`link` indices are a
representation of the ghost `kids`/leaf-link, exactly as `next` represented the
ghost sequence in ListArena.

### Why a recursive tree and not a flat `Seq<Seq<id>>`

ListArena/CircularList used `Seq<Seq<id>>` because their structure is *flat* (a
set of independent lists/rings). A B+tree is genuinely *nested* — clause 3's
ordering is recursive (keys in a subtree bounded by an ancestor's separators) and
clause 1's balance is about path length. A recursive ghost `Tree` lets both be
structural: balance is "all `Leaf`s at the same depth," expressible by an
`Inner`-carries-height field; ordering is a recursive predicate over subtrees.
Recursion terminates on the ghost tree's structure (a `decreases t` measure), not
on chasing `child` pointers through the arena — which is the same move that saved
ListArena (content off the ghost object, not off the pointers).

## 3. `wf`, as the four dynamic-frames clauses (Ch 9 §4 row)

Instantiating the standard four sub-predicates to the ghost `Tree`:

| clause | dynamic-frames role | B+tree statement |
|---|---|---|
| **in-range** | ids name real arena slots | every `id ∈ ids(tree)` satisfies `id < arena.len()`, and `root == tree.id`. *No "child id < parent id" ordering* — the false-invariant trap; tree shape comes from the ghost `Tree`, not id order. |
| **disjoint** | regions don't overlap (separation) | the ids of distinct subtrees are pairwise disjoint, and no id repeats within the tree. This is what makes "this subtree" a well-defined footprint that split can carve and reattach. |
| **coverage** | region is bounded | every node *reachable as part of the tree* is in `ids(tree)`; the arena may hold dead nodes (insert-only never frees, so dead = never-reachable scratch), so coverage is one-directional (tree ⊆ arena live), unlike SparseSet's exact partition. |
| **shape** | pointers realize the region | for each ghost node at `id`: the arena node's `is_leaf`/`count`/`keys_view`/`child_view`/`link` equal the ghost node's fields; children ids are `kids[i].id`; leaf `link` is the next leaf's id (or NIL at the last). Plus the **B+tree-specific** clauses 1–5 of §1, stated over the ghost `Tree`. |

The B+tree adds, *inside* the shape clause, what flat arenas didn't need:
**balance** (clause 1), **cross-node ordering** (clause 3), and **leaf-link =
in-order** (clause 5). These are the genuinely new proof obligations; in-range +
disjoint + coverage are the same skeleton as the other arena containers.

## 4. Bi-abduction on the three operations

For each operation: a *forward* pass (what the code establishes), a *backward*
pass (WP of the postcondition through the body), and the *anti-frame* — the side
condition their intersection abduces. The **frame** is always the disjointness
clause doing its job: subtrees not on the touched path keep their `wf` for free
because their id-regions didn't move.

### 4a. `contains(k)` (read-only; M2)

- **Postcondition (backward):** `result == (k ∈ keys(tree))`.
- **Forward:** descend root→leaf; at an `Inner`, `i = find_gt(seps, k)` picks child
  `i`; at a `Leaf`, `find_ge(keys, k)` then equality test.
- **Anti-frame abduced:** at each step we need "`k`, if present, is in subtree
  `kids[i]`." That is exactly **clause 3** (cross-node ordering): `find_gt`'s
  postcondition gives `seps[i-1] <= k < seps[i]` (boundary), and clause 3 says the
  keys `< seps[i]` and `>= seps[i-1]` live under `kids[i]`. So `contains` is a
  structural induction on the ghost `Tree`, with clause 3 as the load-bearing
  hypothesis and `find_*`'s contracts (already verified, §`bplus_search`) as the
  per-node step. `keys(tree)` membership reduces to leaf membership because clause
  5 makes `keys` the in-order leaf concatenation. **No mutation, no frame needed
  beyond reading.** This is why M2 is the first real milestone: it exercises
  clause 3 without having to *re-establish* anything.

### 4b. `insert(k)`, no split (`count < cap`; M3)

- **Postcondition:** `keys(tree') == insert-sorted(keys(tree), k)`; `wf(tree')`.
- **Forward:** descend to the target leaf `ℓ` (same as `contains`); shift-insert
  `k` into `ℓ.keys`.
- **Footprint:** exactly `{ℓ.id}` — one node. The **frame** is the entire rest of
  the tree: every other ghost node's fields are unchanged and its id is `≠ ℓ.id`
  (disjointness), so its shape facts (clauses 1–5) carry verbatim. The only local
  obligations: `ℓ` stays sorted (clause 2), `ℓ`'s key set gained `k`, and `ℓ` is
  *still the right leaf* — i.e. inserting `k` into `ℓ` doesn't violate clause 3,
  which holds because the descent landed in the leaf whose separator range
  contains `k`. **Anti-frame for taking this branch:** `count < cap` (Verus forces
  it; it's the production `if n < LEAF_CAP` guard). This is the "SparseSet-scale"
  step: one-node footprint, everything else framed out.

### 4c. `insert(k)` with split + propagation (M4–M5; the hard one)

- A full leaf splits at `mid = ceil(cap/2)`; the new right leaf is spliced into
  the leaf-link; a `(separator, right-child-id)` pair is pushed to the parent; if
  the parent is full it splits too, up the recorded path, possibly a new root.
- **Loop invariant (the abduced WP up the path stack):** "the forest below the
  current level is a valid B+tree forest whose key multiset is
  `keys(old) ∪ {k}`, and `(pkey, pchild)` is the separator/child still to insert
  one level up." Each iteration's **footprint** is the current parent + the new
  sibling; their siblings and unrelated subtrees are **framed out** by
  disjointness; the local work re-establishes clauses 2–4 for the two split halves
  and clause 5 if a leaf was involved. The split's key redistribution is index
  arithmetic over the fixed `data` array — bounded, decidable, the place
  `nat`/bounded-int reasoning carries it (as in `CaptureBits`/`SparseSet`).
- **New ids:** a split *allocates* a node (arena push). Disjointness must be
  *extended* to the fresh id — provable because a freshly-pushed arena slot has an
  id `∉ ids(tree)` (it was beyond `arena.len()`). This is the dynamic-frames
  "region grows" step, and it's why coverage is one-directional: the new node
  joins the tree region; no node ever leaves it.

## 5. Is any of this *false*? (the skeptical pass)

Bi-abduction's value is catching a false invariant before sinking proof effort.
Checks against this design:

- **No id-ordering assumption.** We explicitly do *not* require child ids to be
  ordered vs parent ids (the ListArena trap). A split pushes the new sibling at
  the arena tail (largest id) and links a *smaller-id* parent to it; any
  "ids decrease down the tree" clause would be false here. Confirmed avoided: the
  only per-id clause is in-range.
- **Balance is establishable.** Insert-only + split-at-root keeps all leaves at
  one depth: a split raises height only by creating a new root above *both*
  halves, so every leaf's depth increases by exactly 1 simultaneously. Clause 1 is
  preserved, not violated, by split. (A `remove` would threaten it — out of scope.)
- **Leaf-link vs tree-order agreement (clause 5).** The naive framing — two
  *independent* ghost views (the tree's in-order `keys`, and a separate linear
  leaf-link chain) that must coincide — is the ListArena/CircularList "two views
  must agree" trap, where the risk is silent divergence after a split. We avoid it
  by *not* introducing a second independent view: the chain is derived from the
  tree (`tree_leaf_ids`) and the links are *bound* to it (`link_view(lids[p]) ==
  lids[p+1]`), the same single-source-of-truth move that `child_view ==
  kids[i].id` already makes for the downward pointers. There is then nothing to
  "agree" — there is one ghost object and the links realize its in-order leaf
  order. A split's remaining obligation is local: the splice inserts the new
  right leaf's id immediately after the split leaf's id in `tree_leaf_ids`, and
  the two touched `link`s (old leaf → new right, new right → old next) match.
  Still the most intricate splice, but the divergence risk is designed out, not
  defended against.
- **`as_nat` ordering is total and matches `find_*`.** Already discharged:
  `bplus_search` is proven over the `as_nat` order, and `lemma_order_is_as_nat`
  bridges exec compares to it. Clause 3 must be stated in `as_nat` too, so the
  descent's `find_gt` postcondition composes with it directly.

## 6. Consequence for the milestone ladder

- **M2a (reshape):** introduce the ghost `Tree`, `ids`/`keys` derivations, and the
  four `wf` clauses with the §1 B+tree clauses inside `shape`. Re-prove
  `new`/`is_empty`/`len` (single-leaf `Tree::Leaf` base case). No mutation.
- **M2b (`contains`):** §4a — structural induction on `Tree`, clause 3 + `find_*`.
- **M3 (`insert` no split):** §4b — one-node footprint, frame the rest.
- **M4–M5 (split/propagate):** §4c — the path-stack loop invariant, region growth,
  clause-5 re-agreement; budget the most here.

The recursive ghost `Tree` is the single decision that makes balance and ordering
structural and keeps the arena ids a pure representation — the same principle
(content off the ghost object, ids only in-range) that made the flat arena
containers go through, lifted to a nested structure.

---
[Arena / dynamic-frames method](../design/09-arena-aliasing-dynamic-frames.md) ·
[B+tree design](bplus-tree-design.md)
