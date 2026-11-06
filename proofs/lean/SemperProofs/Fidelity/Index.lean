import SemperProofs.EMatch.Engine.Saturate.Invariant

/-!
# The index as a filter on the store (fidelity row: index skip predicates)

The engine keeps every node it ever built in its store; the matcher reads
the index, built by `IndexStore::build` (`index.rs:499-538`), which skips a
node when

* it is subsumed (`FLAG_SUBSUMED`, `index.rs:521-523`),
* the client's matching shield is on and the node is flagged unmatchable
  (`FLAG_UNMATCHABLE`, `index.rs:527-530`),
* its class is not matchable (`is_repr_matchable(repr)`, `index.rs:535-537`).

`FLAG_CONGRUENT_DUP` is deliberately not a skip (`index.rs:509-520`).
The skip reads the node's own flags and its class only.

The development so far read `Graph.nodes` as the index. `Store` makes the
distinction: `Store.graph` is every stored node, `Store.index` the nodes
the index keeps, with the same `find`. The join theorems are restated on
the store: a binding is emitted on the index exactly when it matches the
store at nodes none of which is skipped (`matches_index_iff`,
`mem_runNaive_index_iff`).
-/

namespace Semper.EMatch.Fidelity

open Semper.EMatch

/-- The three skip predicates of `index.rs:521-537`. -/
structure SkipFlags where
  subsumed : NodeId → Bool
  shield : Bool
  unmatchable : NodeId → Bool
  classMatchable : C → Bool

/-- A store: every built node (subsumed ones included), the union-find, the
node and class flags. -/
structure Store where
  nodes : List (NodeId × Node)
  find : NodeId → C
  flags : SkipFlags

/-- `index.rs:521-537`, in order: subsumed, shielded, unmatchable class. -/
def Store.skip (S : Store) (id : NodeId) : Bool :=
  S.flags.subsumed id || (S.flags.shield && S.flags.unmatchable id) ||
    !S.flags.classMatchable (S.find id)

/-- Every stored node. -/
def Store.graph (S : Store) : Graph := ⟨S.nodes, S.find⟩

/-- The nodes the index files (`index.rs:499-545`). -/
def Store.index (S : Store) : Graph := ⟨S.nodes.filter (fun p => !S.skip p.1), S.find⟩

@[simp] theorem Store.graph_nodes (S : Store) : S.graph.nodes = S.nodes := rfl
@[simp] theorem Store.graph_find (S : Store) : S.graph.find = S.find := rfl
@[simp] theorem Store.index_find (S : Store) : S.index.find = S.find := rfl

theorem Store.mem_index {S : Store} {p : NodeId × Node} :
    p ∈ S.index.nodes ↔ p ∈ S.nodes ∧ S.skip p.1 = false := by
  simp [Store.index]

theorem Store.index_sub {S : Store} {p : NodeId × Node} (h : p ∈ S.index.nodes) :
    p ∈ S.graph.nodes :=
  (Store.mem_index.1 h).1

/-- No node of the binding's scanning atoms is skipped. -/
def Unskipped (S : Store) (atoms : List QAtom) (σ : Binding) : Prop :=
  ∀ a, QAtom.scan a ∈ atoms → ∀ id, σ.node a.node = some id → S.skip id = false

theorem atomSat_index_iff {S : Store} {σ : Binding} {a : RAtom} :
    AtomSat S.index σ a ↔
      AtomSat S.graph σ a ∧ ∀ id, σ.node a.node = some id → S.skip id = false := by
  constructor
  · intro h
    refine ⟨atomSat_transfer h (fun id n _ hmem => ⟨Store.index_sub hmem, rfl⟩), ?_⟩
    obtain ⟨id, n, hid, hmem, -⟩ := h
    intro id' hid'
    rw [hid] at hid'
    cases hid'
    exact (Store.mem_index.1 hmem).2
  · rintro ⟨h, hns⟩
    refine atomSat_transfer h ?_
    intro id n hid hmem
    exact ⟨Store.mem_index.2 ⟨hmem, hns id hid⟩, rfl⟩

/-- The join theorems on the store: matching the index is matching the
store at unskipped nodes. -/
theorem matches_index_iff {S : Store} {atoms : List QAtom} {σ : Binding} :
    Matches S.index atoms σ ↔ Matches S.graph atoms σ ∧ Unskipped S atoms σ := by
  constructor
  · intro h
    refine ⟨{ h with sat := fun q hq => ?_ }, ?_⟩
    · cases q with
      | scan a => exact (atomSat_index_iff.1 (h.sat _ hq)).1
      | eq x y => exact h.sat _ hq
    · intro a ha
      exact (atomSat_index_iff.1 (h.sat _ ha)).2
  · rintro ⟨h, hns⟩
    exact { h with
      sat := fun q hq => by
        cases q with
        | scan a => exact atomSat_index_iff.2 ⟨h.sat _ hq, hns a hq⟩
        | eq x y => exact h.sat _ hq }

/-- `mem_runNaive_iff` on the engine's index, stated on the store. -/
theorem mem_runNaive_index_iff {S : Store} {sig : Sym → Kind} {atoms : List QAtom} {ap : APlan}
    (hwf : AtomsWF S.index sig atoms) (h : SchedA atoms ∅ ∅ ap) (σ : Binding) :
    σ ∈ runNaive S.index ap ↔ Matches S.graph atoms σ ∧ Unskipped S atoms σ := by
  rw [mem_runNaive_iff hwf h, matches_index_iff]

/-- The filter keeps the index's structural facts: `KeysNodup` and
conformance of the store pass to the index. -/
theorem Store.index_sublist (S : Store) : S.index.nodes.Sublist S.graph.nodes :=
  List.filter_sublist

end Semper.EMatch.Fidelity
