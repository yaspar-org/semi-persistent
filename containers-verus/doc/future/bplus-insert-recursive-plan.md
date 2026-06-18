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
2. **`insert_rec` leaf base case** — DONE (commit 938471d): `insert_rec_leaf`,
   absorb + split, returns the `Option<(sep, child)>` product, touches only the
   arena, no assumes. Supported by `subtree_wf` + the frame lemmas (b80843e) and
   the forest-update lemmas (4dc92b4).
3. **`insert_rec` internal recursive case** — descend, recurse into child `cp`,
   then absorb (`internal_insert_at`) or split (`internal_split_at`). The arena
   grew under the recursive call, so frame the parent's *other* children with
   `lemma_subtree_wf_frame`, reconstruct the parent over the updated `kids`
   (`lemma_forest_wf_update` for absorb; `lemma_internal_split_tree_wf` for
   split). Decreases `tree_height(cur)`. **All supporting lemmas are now landed**
   — this step is pure assembly of: `lemma_forest_binds_update` (binds),
   `lemma_forest_disjoint_update` (disjoint), `lemma_forest_keys_update` (keys),
   `lemma_forest_links_compose` (leaf-links), `lemma_subtree_wf_frame` (siblings),
   the forest subrange/height lemmas (`tree_wf`). No new theory remains.
4. **Top-level `insert` rewrite** — call `insert_rec`, grow a new root on `Some`
   (reuse the M4b new-root construction), update `self.tree`/`root`/`nkeys`.

Steps 2–4 are the remaining work: the recursive exec method that ties the
landed layout mutators + ghost lemmas together with the arena framing
(`lemma_binds_frame` + `tree_disjoint`), returning the `Option<(sep, child)>`
split product and re-establishing `wf` over the new `kids` at each level.

**M4c progress (step-3, `insert_rec` VERIFIED end-to-end; two reconstruction
lemmas remain `external_body`).** `insert_rec` structure:
- leaf delegation, internal `find_gt` descent, recursive call: VERIFIED.
- the child-returns-None **absorb branch**: FULLY VERIFIED, no assumes. Rebuilds
  the parent over `kids.update(cp, ncl)` via `reconstruct_absorb`, which composes
  `lemma_forest_binds_update` (binds), `lemma_forest_wf_update` + the
  `keys_all_lt/ge_set` bridges (tree_wf + cross-node ordering),
  `lemma_forest_links_update` (the leaf-link chain, itself built on
  decompose/compose + `lemma_forest_links_frame_ids`), `lemma_forest_disjoint_
  update` (disjoint), and `reconstruct_absorb_model` (model). The frame ensures
  (slots outside `tree_ids(cur)` unchanged) is threaded from the recursion.
- the child-returns-Some **split branch**: VERIFIED at the `insert_rec` level. The
  parent-absorb sub-case (`internal_insert_at` when room) and parent-split
  sub-case (`internal_split_at` otherwise) both discharge `insert_rec`'s
  postcondition.
  - `reconstruct_child_split_absorb` (parent had room): **FULLY PROVEN** — no
    `external_body`. `tree_wf`+model via `lemma_child_split_absorb_tree_wf` (on
    the shared `lemma_child_split_combined_wf`); `binds` via
    `lemma_forest_binds_concat`/`_pair`/`_subrange` + `lemma_child_split_binds_node`;
    `tree_disjoint`+footprint+first-leaf via `lemma_child_split_absorb_ids`;
    leaf-links via `lemma_forest_links_splice` (+ `lemma_forest_links_cons`).
  - `reconstruct_parent_split` (parent was full): structural `tree_wf`+model
    **done** (`lemma_parent_split_tree_wf` = `lemma_child_split_combined_wf` +
    `lemma_internal_split_tree_wf`). REMAINING `external_body`: the arena assembly
    (binds/links/disjoint/footprint for both halves) and `lemma_parent_split_
    promoted` (see below). Carries the correct ensures, validated by the property
    tests. No `assume(false)` anywhere.

### The separator-equals-right-min invariant (found proving the promoted key) — LANDED

`reconstruct_parent_split` must return `promoted == tree_keys(rt)[0]` (the
grandparent's `Some` arm needs `sep == tree_keys(nr)[0]`). That is a SHARPER
B+tree fact than `tree_wf` originally tracked: every separator EQUALS the minimum
key of the subtree immediately to its right (separators are routing copies of
leaf minima), not merely a bound. A runtime probe in `check_node` (`sep[i-1] ==
min(child i)`) confirmed it HOLDS across all property tests; a second trace probe
(`min_key_preservation_trace`) confirmed `new_min == min(old_min, key)` on every
insert (13,127 preserved / 65 lowered of 13,192).

`tree_wf`'s cross-node clause now carries `seps[i-1] == tree_keys(kids[i])[0]`
alongside the inequalities. Threading it through cost: the recursion carries
min-key preservation (`key >= cur_min ⟹ nl[0] == cur[0]`) on both arms, proven in
the leaf base case (insert at pos>0 keeps index 0) and propagated by
`lemma_child_split_combined_wf` → `lemma_internal_split_tree_wf` →
`reconstruct_absorb`/`reconstruct_child_split_absorb`. The min preconditions are
key-conditional, matching what descent + the recursion supply.
`lemma_parent_split_promoted` is now PROVEN from it (no longer external_body).

### Remaining: `reconstruct_parent_split` arena assembly

The structural core is proven (`lemma_parent_split_tree_wf` =
`lemma_child_split_combined_wf` + `lemma_internal_split_tree_wf` +
`lemma_parent_split_promoted`). The last `external_body` is the per-half ARENA
assembly: `binds` / `leaf_links` / `tree_disjoint` / footprint for the two output
nodes `pl` (at `gid`) and `pr` (fresh at `rid`), given `internal_split_at`'s
arena layout. It mirrors `reconstruct_child_split_absorb`'s assembly (now fully
proven) but produces two arena nodes instead of one. Its full ensures are
validated by the property tests.

### The footprint-contract spec bug (caught by runtime evaluation, fixed)

`insert_rec`'s `None` postcondition originally claimed *exact* footprint
equality: `tree_ids(nl) == tree_ids(cur)` and the same for `tree_leaf_ids`. That
is **false**: a `None` return means only "this node's root id is unchanged", not
"the footprint is unchanged" — a node deep under child `cp` can split and be
absorbed at every intervening level, allocating fresh leaf + internal slots, so
the subtree's id set GROWS even though the recursion returned `None`. A new
runtime evaluator (`footprint_contract_holds`, which reifies the ghost
`tree_ids`/`tree_leaf_ids` before and after each insert) measured this: **869 of
8800 inserts (~10%) grow the footprint on a `None` return.** A state-`wf` check
cannot see this (the tree stays well-formed); only evaluating the *transition
contract* exposes it.

The honest contract is the same subset+freshness the `Some` arm already used,
plus **first-leaf preservation** (a split only ever splices a fresh leaf to the
RIGHT, so a subtree's leftmost leaf never moves — and that, not full leaf-id
sequence equality, is all the leaf-link chain reads at child boundaries). The
fix cascaded through `reconstruct_absorb` and its forest lemmas
(`lemma_forest_disjoint_update` now takes a freshness `bound` and propagates
pairwise disjointness; `lemma_forest_leaf_ids_update_first` replaces the
exact-sequence `lemma_forest_leaf_ids_update`; `lemma_forest_binds_update` dropped
its unused footprint-equality requires; `lemma_forest_links_update` /
`lemma_build_forest_links` / `reconstruct_absorb_links` now require only
first-leaf preservation). All re-verified, no regressions (755 verified, 0
errors crate-wide).

So the internal case is real and verified end to end; the two split-side
reconstruction lemmas are the remaining `external_body` proofs, then the
top-level wrapper (step 4).

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
