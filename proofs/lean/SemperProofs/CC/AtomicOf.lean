import SemperProofs.CC.Atoms

/-!
# The atomic set from the engine's `atomic` bit, and the collapse from `add`

`Atoms.lean` takes the atomic set `A` as a parameter and assumes the
one-element collapse `AtomCollapse`. This file derives both from models of
the engine's two mechanisms.

## The `atomic` bit (`atomicOf`)

The engine keeps one bit per class (`containers/src/eclasses.rs`, field
`atomic`), set and never cleared:

* `add_use` (`eclasses.rs:344`), called for every child of a fresh node
  (`egraph.rs`, `add`, `add_mset`, `add_with_creation_evidence`): the
  child's class is atomic. A node is never deleted and a retired node keeps
  its uses, so the clause reads "a child of a stored node", active or
  retired (`State.IsChild`).
* `register_if_fresh` (`egraph.rs`, `None => self.classes.set_atomic(repr)`):
  a fresh node of an operator without a completion column makes its class
  atomic. Every class holds a node, so a class that holds no `f`-node holds
  a node of another operator and is atomic (`¬ State.HoldsNode`).
* `fold_min_monomial` (`egraph.rs`, `if absorbed_atomic { set_atomic }`): a
  merge ORs the two bits. Both clauses are stated through `find`, so a
  class that absorbs an atomic class is atomic.

The model's state holds `f`-nodes only, so one case of the bit is outside
it: a class that holds an `f`-node and a node of another operator and is
no child is atomic in the engine and not in `atomicOf st`. The theorems of
`Atoms.lean` hold for every `A`, so a reader who knows such a class adds it
to the set; `atomicOf st ⊆ A` is the direction the engine guarantees.

## The collapse from `add` (`addNF`, `AddStep`)

`add` returns an existing class for a degenerate normal form without
building a node: `Normal::Single(g)` gives `find g` (`egraph.rs`, `add`
and `add_mset`, the `Normal::Single` case) and `Normal::Unit` gives the
unit's class. `addNF` is that function on monomials: `{x} ↦ find x`,
`∅ ↦ find u`, `none` otherwise. `AddStep` is the normalize step of
completion with `add` so modelled: an active node of the view whose normal
form `addNF` resolves is merged into the class `addNF` returns. At a
fixpoint of `AddStep` the collapse holds (`atomCollapse_of_addFixed`), so
`RoundFixedA` is `RoundFixed` of the view plus that fixpoint
(`roundFixedA_of_addFixed`).
-/

namespace SemperProofs.CC

open Relation

variable {n : ℕ}

namespace State

/-- The class `c` holds a stored `f`-node, active or retired. -/
def HoldsNode (st : State n) (c : Fin n) : Prop := ∃ p ∈ st.nodes, st.find p.2 = st.find c

/-- The class `c` is a child of a stored `f`-node, active or retired
(`add_use`, `eclasses.rs:344`, on every child of a fresh node). -/
def IsChild (st : State n) (c : Fin n) : Prop :=
  ∃ p ∈ st.nodes, ∃ x ∈ p.1, st.find x = st.find c

end State

/-- The atomic set the engine's `atomic` bit defines, as far as the store
of one operator shows it: a child of a stored node (`add_use`), or a class
with no `f`-node, which holds a node of another operator
(`register_if_fresh`). Merges OR the bit; both clauses read `find`. -/
def atomicOf (st : State n) : Set (Fin n) := {c | st.IsChild c ∨ ¬ st.HoldsNode c}

theorem mem_atomicOf {st : State n} {c : Fin n} :
    c ∈ atomicOf st ↔ st.IsChild c ∨ ¬ st.HoldsNode c := Iff.rfl

/-- A child of a stored node is atomic: the tier 1 check "no `f`-node has
a non-atomic `f`-child" holds by definition. -/
theorem child_mem_atomicOf {st : State n} {p : Monomial n × Fin n} (hp : p ∈ st.nodes) {x : Fin n}
    (hx : x ∈ p.1) : x ∈ atomicOf st :=
  Or.inl ⟨p, hp, x, hx, rfl⟩

/-- A class with no `f`-node is atomic. -/
theorem leaf_mem_atomicOf {st : State n} {c : Fin n} (h : ¬ st.HoldsNode c) : c ∈ atomicOf st :=
  Or.inr h

/-- The atomic set is read through `find`: two ids of one class are both
atomic or neither. -/
theorem mem_atomicOf_congr {st : State n} {c d : Fin n} (h : st.find c = st.find d) :
    c ∈ atomicOf st ↔ d ∈ atomicOf st := by
  simp only [mem_atomicOf, State.IsChild, State.HoldsNode, h]

/-! ## `add` on a degenerate normal form -/

/-- The class `add` returns for a normal form without building a node:
`x`'s class for the one-element monomial `{x}` (`Normal::Single`), the
unit's class for the empty monomial (`Normal::Unit`), none otherwise (a
node is built, `Normal::Node`). -/
noncomputable def addNF (st : State n) (u : Option (Fin n)) (N : Monomial n) : Option (Fin n) :=
  if h : ∃ x, N = {x} then some (st.find h.choose)
  else if N = 0 then u.map st.find else none

theorem addNF_single (st : State n) (u : Option (Fin n)) (x : Fin n) :
    addNF st u {x} = some (st.find x) := by
  have h : ∃ y, ({x} : Monomial n) = {y} := ⟨x, rfl⟩
  simp only [addNF, h, dite_true]
  rw [← Multiset.singleton_inj.1 h.choose_spec]

theorem addNF_zero (st : State n) (u : Option (Fin n)) : addNF st u 0 = u.map st.find := by
  have h : ¬ ∃ y, (0 : Monomial n) = {y} := fun ⟨y, hy⟩ => Multiset.singleton_ne_zero y hy.symm
  simp only [addNF, h, dite_false, ite_true]

theorem addNF_some {st : State n} {u : Option (Fin n)} {N : Monomial n} {x : Fin n}
    (h : addNF st u N = some x) :
    (∃ y, N = {y} ∧ x = st.find y) ∨ (N = 0 ∧ ∃ y, u = some y ∧ x = st.find y) := by
  unfold addNF at h
  split_ifs at h with h₁ h₂
  · exact Or.inl ⟨h₁.choose, h₁.choose_spec, (Option.some_injective _ h).symm⟩
  · refine Or.inr ⟨h₂, ?_⟩
    cases u with
    | none => exact absurd h (by simp)
    | some y => exact ⟨y, rfl, (Option.some_injective _ (by simpa using h)).symm⟩

/-- The normalize step of completion on the completion view, with `add`
modelled by `addNF`: an active node `(M, c)` whose normal form `N` is a
monomial `add` resolves to an existing class `x` is merged into `x`. The
case where `add` builds a node is `Infer.mint` followed by `joinMerge`
(`Defs.lean`); this step is the one `Infer` lacks. -/
inductive AddStep (L : Laws n) (A : Set (Fin n)) (u : Option (Fin n)) : State n → State n → Prop
  | collapse {st : State n} {M : Monomial n} {c : Fin n} {N : Monomial n} {x : Fin n} :
      (M, c) ∈ (st.withAtoms A u).active →
      ReflTransGen (Rw L (st.withAtoms A u).rules) M N →
      (∀ P, ¬ Rw L (st.withAtoms A u).rules N P) →
      addNF st u N = some x → st.find c ≠ x →
      AddStep L A u st (st.merge c x)

/-- A fixpoint of the normalize step: no `AddStep` applies. -/
def AddFixed (L : Laws n) (A : Set (Fin n)) (u : Option (Fin n)) (st : State n) : Prop :=
  ∀ st', ¬ AddStep L A u st st'

/-- **The one-element collapse at a fixpoint of `add`.** An active node of
the view whose normal form is an implicit node's monomial is in that
node's class: `addNF` returns the class, and if the node's class differed
a step would apply. -/
theorem atomCollapse_of_addFixed {L : Laws n} {st : State n} {A : Set (Fin n)}
    {u : Option (Fin n)} (h : AddFixed L A u st) : AtomCollapse L st A u := by
  intro M c N x hM hx hMN hN
  by_contra hne
  have hadd : addNF st u N = some (st.find x) := by
    rcases mem_atomNodes.1 hx with ⟨-, rfl⟩ | ⟨hu, rfl⟩
    · exact addNF_single st u x
    · rw [addNF_zero, hu]; rfl
  exact h _ (AddStep.collapse hM hMN hN hadd (fun e => hne e.symm))

/-- `RoundFixedA` from `RoundFixed` of the view and a fixpoint of `add`. -/
theorem roundFixedA_of_addFixed {L : Laws n} {st : State n} {A : Set (Fin n)}
    {u : Option (Fin n)} (hfix : RoundFixed L (st.withAtoms A u)) (hadd : AddFixed L A u st) :
    RoundFixedA L st A u :=
  roundFixedA_iff.2 ⟨hfix, atomCollapse_of_addFixed hadd⟩

/-- The step is not idle when `find` is idempotent: the merged class's
representative changes. -/
theorem AddStep.find_changed {L : Laws n} {A : Set (Fin n)} {u : Option (Fin n)}
    {st st' : State n} (hidem : ∀ y, st.find (st.find y) = st.find y)
    (h : AddStep L A u st st') : ∃ c, st'.find c ≠ st.find c := by
  cases h with
  | @collapse M c N x _ _ _ hadd hne =>
    refine ⟨c, ?_⟩
    have hx : st.find x = x := by
      rcases addNF_some hadd with ⟨y, -, rfl⟩ | ⟨-, y, -, rfl⟩ <;> exact hidem y
    simp only [State.merge, ite_true]
    rw [hx]
    exact fun e => hne e.symm

/-! ## Completeness with the derived atomic set -/

/-- `CompleteAtoms` with the atomic set the `atomic` bit defines. -/
abbrev CompleteAtomic (L : Laws n) (S : Set (Monomial n × Monomial n)) (st : State n)
    (u : Option (Fin n)) : Prop :=
  CompleteAtoms L S st (atomicOf st) u

namespace CompleteAtomic

variable {L : Laws n} {S : Set (Monomial n × Monomial n)} {st : State n} {u : Option (Fin n)}

/-- Two theory-equal monomials of the view are in one class. -/
theorem same_class (h : CompleteAtomic L S st u) {M N : Monomial n} {c d : Fin n}
    (hM : (M, c) ∈ (st.withAtoms (atomicOf st) u).active)
    (hN : (N, d) ∈ (st.withAtoms (atomicOf st) u).active) (hMN : E L S M N) :
    st.find c = st.find d :=
  CompleteAtoms.same_class h hM hN hMN

/-- A node theory-equal to a child of a stored node lands in its class. -/
theorem child_class (h : CompleteAtomic L S st u) {M : Monomial n} {c x : Fin n}
    (hM : (M, c) ∈ st.active) {p : Monomial n × Fin n} (hp : p ∈ st.nodes) (hx : x ∈ p.1)
    (hMx : E L S M {x}) : st.find c = st.find x :=
  CompleteAtoms.atom_class h hM (child_mem_atomicOf hp hx) hMx

/-- A node theory-equal to a leaf constant, a class with no `f`-node, lands
in its class. -/
theorem leaf_class (h : CompleteAtomic L S st u) {M : Monomial n} {c x : Fin n}
    (hM : (M, c) ∈ st.active) (hx : ¬ st.HoldsNode x) (hMx : E L S M {x}) :
    st.find c = st.find x :=
  CompleteAtoms.atom_class h hM (leaf_mem_atomicOf hx) hMx

/-- Two atomic classes equal in the theory are in one class. -/
theorem atoms (h : CompleteAtomic L S st u) {x y : Fin n} (hx : x ∈ atomicOf st)
    (hy : y ∈ atomicOf st) (hxy : E L S ({x} : Monomial n) {y}) : st.find x = st.find y :=
  CompleteAtoms.atoms h hx hy hxy

end CompleteAtomic

/-- `completion_complete_atoms` with `A := atomicOf st`: the hypotheses
of `CompleteAtoms` on the view of the derived atomic set, the fixed round
as `RoundFixed` of the view plus a fixpoint of `add`. -/
theorem completion_complete_atomic {L : Laws n} {S : Set (Monomial n × Monomial n)}
    {st : State n} {u : Option (Fin n)} {ss₀ ss : SlotState n}
    (h5₀ : SlotState.I5 ss₀) (hrun : SlotState.OpsStar ss₀ ss)
    (ha : SlotState.Agrees (st.withAtoms (atomicOf st) u) ss)
    (h0 : I0Active (st.withAtoms (atomicOf st) u)) (hcanon : ∀ c, L.clamp (st.rhs c) = st.rhs c)
    (hfix : RoundFixed L (st.withAtoms (atomicOf st) u)) (hadd : AddFixed L (atomicOf st) u st)
    (hlaw : ∀ P Q, L.lawRel P Q → degLex P Q)
    (hnf_ax : ∀ M N, ¬ Rw (plain n) L.axRules (L.clamp M) N)
    (hcp : ∀ r₁ r₂, r₁ ∈ (st.withAtoms (atomicOf st) u).rules ∪ L.axRules →
      r₂ ∈ (st.withAtoms (atomicOf st) u).rules ∪ L.axRules → r₁ ≠ r₂ → Overlap r₁.1 r₂.1 →
      Joinable (Rw (plain n) ((st.withAtoms (atomicOf st) u).rules ∪ L.axRules))
        (criticalPair (plain n) r₁ r₂).1 (criticalPair (plain n) r₁ r₂).2)
    (hcc : ∀ P c d, (P, c) ∈ st.active → (P, d) ∈ st.active → st.find c = st.find d)
    (hS : ∀ M N, (M, N) ∈ S → ∃ c d, (M, c) ∈ (st.withAtoms (atomicOf st) u).active ∧
      (N, d) ∈ (st.withAtoms (atomicOf st) u).active ∧ st.find c = st.find d)
    (hcancel : L.cancellative → ∀ M N X,
      Joinable (Rw (plain n) ((st.withAtoms (atomicOf st) u).rules ∪ L.axRules)) (M + X) (N + X) →
      Joinable (Rw (plain n) ((st.withAtoms (atomicOf st) u).rules ∪ L.axRules)) M N)
    {M N : Monomial n} {c d : Fin n} (hM : (M, c) ∈ (st.withAtoms (atomicOf st) u).active)
    (hN : (N, d) ∈ (st.withAtoms (atomicOf st) u).active) (hMN : E L S M N) :
    st.find c = st.find d :=
  completion_complete_atoms h5₀ hrun ha h0 hcanon (roundFixedA_of_addFixed hfix hadd) hlaw hnf_ax
    hcp hcc hS hcancel hM hN hMN

end SemperProofs.CC
