# M4c: the fully general `insert`, recursively — decomposition + bi-abductive sketch

*Living reference for the descent + split-propagation insert (task #59). Written
before the proof; update as each unit lands. Reads alongside the
[`wf` invariant analysis](bplus-wf-invariant-analysis.md) (§4 has the original
iterative-loop framing; this doc supersedes it with the recursive plan) and the
[B+tree design](bplus-tree-design.md).*

## Why recursive, not iterative

Production's `insert` records a path stack and propagates splits bottom-up in a
loop. We verify a **recursive** insert instead:

- Recursion depth is the **tree height**, `O(log_fanout n)`, hard-bounded (~24,
  production caps `MAX_DEPTH`). It scales with `log n` over a high-fanout
  balanced tree, not with `n` — so no stack-overflow concern (that needs frames
  scaling with data size).
- `decreases tree_height(cur)` is the natural measure — the same one `contains`
  already uses, with the same proven lemmas (`lemma_tree_wf_height`,
  `lemma_forest_max_height_at`).
- The frame toolkit (`lemma_binds_frame` + the `tree_disjoint` `wf` clause)
  applies **per level**: recursing into child `cp` frames out every other child
  directly. The iterative version's loop invariant describes a *partially-
  rebuilt* tree — a harder object.

Faithfulness is preserved: production is iterative only for the hot-path perf of
a fixed stack array; the type, interface, and observable behaviour are identical
(we already accept internal-algorithm divergence, e.g. `subrange` splits vs
production's in-place `copy_within`).

## The recursive unit

```
insert_rec(idx: ArenaIdx, ghost cur: Tree, key: K) -> Option<(sep: Word, new_child: ArenaIdx)>
```

- `None` — "absorbed; my subtree's id is unchanged, my model gained `key`."
- `Some((sep, rid))` — "I split; I am now the *left* half, `rid` is a freshly
  allocated right half, and `sep` must be inserted into my parent just after my
  child slot."

Top-level `insert` calls `insert_rec(root, tree@, key)`; on `Some`, the root
split, so build a `new_internal2(sep, old_root, rid)` root (height grows by one —
the M4b new-root move, reused).

## The two split shapes (asymmetric, already modelled)

- **Leaf split (B+tree).** Separator is a *copy* of the right half's first key;
  the key stays in the right leaf. `keys_all_ge(right, sep)` with equality at
  index 0. Landed in M4b (`leaf_split_at`, `lemma_split_tree_wf`).
- **Internal split (B-tree-style promotion).** The median separator is *promoted
  out* — removed from both halves: `seps = lseps ++ [promoted] ++ rseps`, and
  `promoted` becomes the parent's separator, stored in neither child. Children
  split `cb[0..imid+1]` left, `cb[imid+1..]` right. Arithmetic de-risked in a
  probe; mutator `internal_split_at` + `lemma_internal_split_tree_wf` are the new
  pieces.

## Bi-abductive sketch of `insert_rec`

### Postcondition (backward / WP target)

Whatever the result, over the touched region only:
- **wf forest** — each returned node satisfies `tree_wf` at `cur`'s height
  (split: both halves; absorb: the one node);
- **model** — `tree_keys(new forest).to_set() == old tree_keys(cur).to_set() ∪
  {key.id_nat()}` (set suffices for the spec);
- **binds** — holds for the new subtree(s) against the grown arena;
- **leaf-link** — the chain is the old one with exactly the new right leaf
  spliced in after the split leaf;
- **disjoint** — `tree_disjoint` extends to the fresh id(s).

### Forward pass (what the body establishes), by case

- **Leaf, absorb** (`count < leaf_cap`): footprint `{idx}`; `leaf_insert_at`;
  return `None`. Frame: everything else untouched.
- **Leaf, split** (`count == leaf_cap`): footprint `{idx}` + one fresh `rid`;
  `leaf_split_at` + `set_link`; return `Some((right[0], rid))`. (M4b minus the
  new-root step.)
- **Internal**: `cp = find_gt(seps, key)`; recurse on child `cp`.
  - child returns `None` → return `None` (frame: I'm unchanged).
  - child returns `Some((sep, rid))`:
    - `count < key_cap` → `internal_insert_at(self, cp, sep, rid)`; return `None`.
    - `count == key_cap` → `internal_split_at`; return
      `Some((promoted, new_internal_id))`.

### Anti-frame each step abduces (pre-loaded as `requires` / invariants)

- **descent step**: cross-node ordering (`lemma_descent_step`, proven) — the key
  can only live under child `cp`, so recursing there is sound.
- **split branch**: `count == cap` (the full guard); **fresh-id disjointness** —
  the pushed `rid` / `new_internal_id` equal `arena.len()`, hence `∉
  tree_ids(cur)`, so `lemma_binds_frame` preserves every sibling's `binds`. This
  is the M4c-specific obligation the prerequisite commits (binds-frame +
  `tree_disjoint`) exist to discharge.
- **arena growth**: `arena.len() + (1 or 2) < max_nat` — the headroom
  precondition already on `insert`.

### The frame, stated once

At an internal node, only the descended child `cp` and the nodes a split
allocates are in the footprint. Every *other* child subtree `kids[j]` (`j ≠ cp`):
its ids are disjoint from the footprint (by `tree_disjoint`), and the arena only
*grew* (pushes never overwrite existing slots; the single `set` is on `idx`
itself), so `lemma_binds_frame` transports its `binds` verbatim. That is why
`insert_rec` never re-touches siblings.

### Termination

`decreases tree_height(cur)`; recursing into child `cp` strictly decreases it
(`lemma_tree_wf_height` + `lemma_forest_max_height_at`, proven for `contains`).
Bounded by `MAX_DEPTH` (~24).

## Build order (each unit committable green)

Layout layer (DONE — all 6 layouts green):
- `set_internal_child` (commit 9ad8168), `internal_key_insert` +
  `internal_insert_at` (8418e54), `internal_split_at` (c151abd).

Tree layer:
1. **`lemma_internal_split_tree_wf`** (ghost) — DONE (commit 74a29ec), on the
   forest subrange lemmas (d56ae12). Also fixed the internal-occupancy bound
   ceil→floor (652fc9f). The genuinely new structural proof is landed.
2. **`insert_rec` leaf base case** — leaf split/absorb, assembled from M3 + M4b
   pieces, returning `Option` instead of mutating the root directly.
3. **`insert_rec` internal recursive case** — descend, recurse, then absorb
   (`internal_insert_at`, landed) or split (`internal_split_at`, landed).
4. **Top-level `insert` rewrite** — call `insert_rec`, grow a new root on `Some`.

Steps 2–4 are the remaining work: the recursive exec method that ties the
landed layout mutators + ghost lemmas together with the arena framing
(`lemma_binds_frame` + `tree_disjoint`), returning the `Option<(sep, child)>`
split product and re-establishing `wf` over the new `kids` at each level.

## What is genuinely new vs. reused

Reused, already landed: descent (M4a), leaf split + new-root (M4b), frame
toolkit + `tree_disjoint` (M4c prereqs), `internal_insert_at` (M4c step 2),
`set_internal_child` (M4c step 1). The two new proof obligations:

1. **`lemma_internal_split_tree_wf`** — like `lemma_split_tree_wf` but for the
   B-tree-style promotion: prove the two halves `Inner{lseps, lkids}` /
   `Inner{rseps, rkids}` are wf, `promoted` separates them, and recombination
   preserves the model. Trickier than the leaf case because a *child subtree*
   moves from the old node into one half, so its `binds` / `tree_wf` /
   `tree_ids` must transfer — handled by the frame lemma plus a sub-forest split
   lemma.
2. **Recursive re-assembly** at the internal case: the child's returned
   subtree(s) slot back into the parent's `kids` sequence — `Seq` surgery
   (`kids` with one element replaced by one or two) that the absorb / split cases
   produce, with `binds` / leaf-link / disjointness re-established over the new
   `kids`.

## Engineering note (carried from the proof-attempts log)

Keep `NodeLayout` trait bodies small and per-layout; multi-step generic logic
goes in **free functions over `L`** (e.g. `internal_insert_at`). A heavy default
trait body destabilizes previously-green sibling methods via crate-wide spec
pruning — observed twice (the `IndexLike` order lemmas, then `internal_insert_at`
as a default body breaking the `child` accessor).

---
[wf invariant analysis](bplus-wf-invariant-analysis.md) ·
[B+tree design](bplus-tree-design.md)
