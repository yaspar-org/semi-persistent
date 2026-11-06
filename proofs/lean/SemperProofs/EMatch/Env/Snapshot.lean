import SemperProofs.EMatch.Env.Model

/-!
# `canon` and the frozen graph (spec D)

The Lean `Graph` has a fixed `find`. The engine's `canon(index, eg, id)`
(`ematch.rs:1117-1136`) is `index.full.round_repr(id)`: the `repr` table
filled at index build (`index.rs:499-504`, `repr_tab.push(eg.class_repr(gid))`,
`class_repr = classes.find_const`), falling back to the live
`eg.find_const(id)` only for ids minted after the build (`id ≥ repr.len()`).
`RoundSnapshot` states the three hypotheses under which the refinement's
`G` is the engine's view for the whole round. No proof is claimed beyond
the trivial corollary `canon_eq_find`; the hypotheses are documented
assumptions about the driver (`saturate.rs:390-432`).
-/

namespace Semper.EMatch.Env

open Semper.EMatch

/-- The engine's `canon` during the round, parameterized by the position
`i` of the rule being matched (the live union-find drifts between rules;
`live i` is `find_const` after the actions of the rules before `i`). -/
def canon (buildSize : Nat) (roundRepr : NodeId → C) (live : Nat → NodeId → C)
    (i : Nat) (id : NodeId) : C :=
  if id < buildSize then roundRepr id else live i id

/-- Spec D, H1-H3, as assumptions relating `G` to the engine's round:

* `buildSize` is `repr.len()`, the number of ids at index build
  (`index.rs:499-504`); `roundRepr` is the `repr` table, i.e. `round_repr`
  (`index.rs:806-808`); `live i` is the live `find_const` while rule `i`
  runs.
* **H1 (snapshot)**: `G.nodes` are the nodes at build time, all with ids
  below `buildSize` (`nodes_lt`), their stored children too
  (`children_lt`: children are ids read from the frozen node store), and
  `G.find` is `round_repr` on them (`find_eq_repr`). `round_repr` returns
  representatives (`find_idem`). Globals are assumed bound to pre-build ids
  (spec D, H1 caveat); nothing is stated about `live` on ids `≥ buildSize`.
* **H2 (canonical contents)**: `rebuild` precedes `build` with no
  intervening mutation (`saturate.rs:392-400`), so stored children are
  `find` fixed points (`children_canon`); distinctness of multiset/set
  entries is structural in the Lean `Multiset`/`Finset` children, and the
  `spair` exemption (two entries of one class) is kept by `decomposeComm`.
* **H3 (per-rule freezing)**: a rule's matches are computed before its
  actions run (`apply.rs:1401-1411`); merges change only the live
  union-find and `add` mints ids `≥ buildSize`, so for every rule position
  `i` the engine's `canon i` agrees with `G.find` on every id a step reads
  (`canon_frozen`, a consequence of H1 by `canon_eq_find`: it is recorded
  as a field to make the per-round statement explicit).

Hence each rule of the round runs on the same `G`, and the hypotheses
`G.ChildrenCanon`, `G.FindIdem` of `refine`/`restore` hold. -/
structure RoundSnapshot (G : Graph) (buildSize : Nat) (roundRepr : NodeId → C)
    (live : Nat → NodeId → C) : Prop where
  nodes_lt : ∀ p ∈ G.nodes, p.1 < buildSize
  children_lt : ∀ p ∈ G.nodes, ∀ c, Children.containsClass p.2.children c = true → c < buildSize
  find_eq_repr : ∀ id, id < buildSize → G.find id = roundRepr id
  find_idem : G.FindIdem
  children_canon : G.ChildrenCanon
  canon_frozen : ∀ i id, id < buildSize → canon buildSize roundRepr live i id = G.find id

/-- H3 follows from H1: on build-time ids `canon` never consults `live`. -/
theorem canon_eq_find {G : Graph} {buildSize : Nat} {roundRepr : NodeId → C}
    {live : Nat → NodeId → C}
    (h : ∀ id, id < buildSize → G.find id = roundRepr id) (i : Nat) (id : NodeId)
    (hid : id < buildSize) : canon buildSize roundRepr live i id = G.find id := by
  simp [canon, hid, h id hid]

/-- The round's `canon` on a stored node id is `G.find`, for every rule of
the round. -/
theorem RoundSnapshot.canon_node {G : Graph} {buildSize : Nat} {roundRepr : NodeId → C}
    {live : Nat → NodeId → C} (hs : RoundSnapshot G buildSize roundRepr live) (i : Nat)
    {p : NodeId × Node} (hp : p ∈ G.nodes) :
    canon buildSize roundRepr live i p.1 = G.find p.1 :=
  hs.canon_frozen i p.1 (hs.nodes_lt p hp)

end Semper.EMatch.Env
