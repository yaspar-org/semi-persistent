import SemperProofs.CC.Main
import SemperProofs.CC.Lattice

/-!
# Leaf constants: a class read as its one-element monomial

A class with no node of the operator `f` (a leaf constant such as `a` and
`b` in `(union (+ a b) c)`, or `c` itself) still occurs in monomials: `a`
is a summand of `{a, b}`, and the equation `a + b = c` relates the
two-element monomial `{a, b}` to the one-element monomial `{c}`. The engine
identifies the one-element monomial `{x}` with the class `x` everywhere:

* `nary_canon::normalize` returns `Normal::Single(x)` for a single child of
  multiplicity 1, and `add` then returns `x`'s class instead of building a
  node (`add_mset_buffered`, `add`);
* recanonicalization that leaves a stored node with one child records the
  pair (node, child) as a merge (`degeneracy_pair`), so the stored
  one-element node joins its child's class at the next rebuild;
* `class_rhs_into` gives an `atomic` class (referenced as a child, or
  holding a non-AC node) the right-hand side `{find c}`, a monomial that is
  the class itself and that no stored node needs to spell.

The empty monomial is identified the same way with the class of the
operator's identity, when it has one: `Normal::Unit` makes `add` return the
unit's class, recanonicalization to the empty list records the pair (node,
unit), and `class_rhs_into` gives the unit's class the right-hand side `∅`.

The model reads this as follows. `A` is a set of atomic classes (in the
engine, every class referenced as a child: a stored child is atomic, Chapter
6 §6c) and `u` the unit class, if any. `st.withAtoms A u` adds, for each
`x ∈ A`, the one-element monomial `{x}` as an active node of the class `x`,
and the empty monomial as an active node of `u`; these nodes are implicit
(the engine stores none of them) and are never retired. The completeness
theorems of `Main.lean` apply to `st.withAtoms A`; the hypotheses that are
not already statements about the stored nodes are:

* `RoundFixedA` (equivalently `RoundFixed` of `st.withAtoms A u` together
  with `AtomCollapse`, `roundFixedA_iff`): a normal form that is the
  monomial of an implicit node, `{x}` of an atom or `∅` of the unit, is
  present in a class exactly when that class is `x`'s (the unit's). This
  is the one-element collapse: completion merges the node into `x`'s class,
  which is what `add` returning `x`'s class does. Any other normal form is
  a stored active node of the class.
* `hcc` over the stored active nodes only. Congruence over the implicit
  nodes is derived (`RoundFixedA.congr`): a stored node whose monomial is
  that of an implicit node, such as a one-element node `({x}, c)` (the
  materialized representation, kept by the engine until the degeneracy
  merge), is in the implicit node's class at a fixed round
  (`RoundFixedA.materialized`), and no two implicit nodes share a monomial.

`completion_complete_atoms` is the result: two `=_E`-equal monomials of
`st.withAtoms A u`, stored nodes, leaf constants or the unit, are in one
class.
`completion_complete_atom_class` is the case `M =_E {x}`: a node equal to a
constant in the theory lands in the constant's class.
-/

namespace SemperProofs.CC

open Relation

variable {n : ℕ}

/-- The implicit nodes: the one-element monomial `{x}` of each class
`x ∈ A`, as a node of the class `x`, and the empty monomial of the unit
class `u`, if any. -/
def atomNodes (A : Set (Fin n)) (u : Option (Fin n)) : Set (Monomial n × Fin n) :=
  {p | (p.2 ∈ A ∧ p.1 = {p.2}) ∨ (u = some p.2 ∧ p.1 = 0)}

theorem mem_atomNodes {A : Set (Fin n)} {u : Option (Fin n)} {M : Monomial n} {c : Fin n} :
    (M, c) ∈ atomNodes A u ↔ (c ∈ A ∧ M = {c}) ∨ (u = some c ∧ M = 0) := Iff.rfl

/-- No two implicit nodes share a monomial. -/
theorem atomNodes_func {A : Set (Fin n)} {u : Option (Fin n)} {P : Monomial n} {c d : Fin n}
    (hc : (P, c) ∈ atomNodes A u) (hd : (P, d) ∈ atomNodes A u) : c = d := by
  rw [mem_atomNodes] at hc hd
  rcases hc with ⟨-, hc⟩ | ⟨hc, hc'⟩ <;> rcases hd with ⟨-, hd⟩ | ⟨hd, hd'⟩
  · exact Multiset.singleton_inj.1 (hc.symm.trans hd)
  · exact absurd (hc.symm.trans hd') (Multiset.singleton_ne_zero c)
  · exact absurd (hc'.symm.trans hd) (Multiset.singleton_ne_zero d).symm
  · exact Option.some_injective _ (hc.symm.trans hd)

namespace State

/-- The completion view of a state whose classes in `A` are atomic and
whose operator has the unit class `u` (if any): the stored nodes and the
implicit nodes `({x}, x)` for `x ∈ A` and `(∅, u)`, never retired. `find`
and the right-hand sides are the stored ones; the rule set
`(st.withAtoms A u).rules` therefore has the rules `M → {x}` that the
engine reads for an atomic class whose right-hand side is `{x}`, and
`M → ∅` for the unit's class. -/
def withAtoms (st : State n) (A : Set (Fin n)) (u : Option (Fin n)) : State n where
  find := st.find
  nodes := st.nodes ∪ atomNodes A u
  retired := st.retired \ atomNodes A u
  rhs := st.rhs

variable {st : State n} {A : Set (Fin n)} {u : Option (Fin n)}

@[simp] theorem withAtoms_find : (st.withAtoms A u).find = st.find := rfl

@[simp] theorem withAtoms_rhs : (st.withAtoms A u).rhs = st.rhs := rfl

theorem mem_active_withAtoms {p : Monomial n × Fin n} :
    p ∈ (st.withAtoms A u).active ↔ p ∈ st.active ∨ p ∈ atomNodes A u := by
  simp only [active, withAtoms, Set.mem_sdiff, Set.mem_union]
  by_cases h : p ∈ atomNodes A u
  · simp only [h, or_true, not_true_eq_false, and_false, not_false_eq_true, and_self]
  · simp only [h, or_false, not_false_eq_true, and_true]

theorem active_withAtoms {p : Monomial n × Fin n} (h : p ∈ st.active) :
    p ∈ (st.withAtoms A u).active :=
  mem_active_withAtoms.2 (Or.inl h)

/-- An implicit node is active. -/
theorem implicit_active {p : Monomial n × Fin n} (h : p ∈ atomNodes A u) :
    p ∈ (st.withAtoms A u).active :=
  mem_active_withAtoms.2 (Or.inr h)

/-- The implicit node of an atom is active. -/
theorem atom_active {x : Fin n} (hx : x ∈ A) :
    (({x} : Monomial n), x) ∈ (st.withAtoms A u).active :=
  implicit_active (Or.inl ⟨hx, rfl⟩)

/-- The implicit node of the unit is active. -/
theorem unit_active {x : Fin n} (hx : u = some x) :
    ((0 : Monomial n), x) ∈ (st.withAtoms A u).active :=
  implicit_active (Or.inr ⟨hx, rfl⟩)

/-- The stored rules are rules of the completion view. -/
theorem rules_withAtoms : st.rules ⊆ (st.withAtoms A u).rules := by
  rintro p ⟨c, c', hp, h2, hlt, hc', hcc⟩
  exact ⟨c, c', active_withAtoms hp, h2, hlt, Or.inl hc', hcc⟩

end State

/-- `RetiredCovered` passes to the completion view: its retired nodes are
stored retired nodes, and its active nodes contain the stored ones. -/
theorem RetiredCovered.withAtoms {st : State n} (h : RetiredCovered st) (A : Set (Fin n))
    (u : Option (Fin n)) : RetiredCovered (st.withAtoms A u) := by
  intro M c hM
  obtain ⟨hn, K, c', hK, hc⟩ := h M c hM.1
  exact ⟨Or.inl hn, K, c', State.active_withAtoms hK, hc⟩


/-! ## The one-element collapse -/

/-- The one-element collapse at a fixed round: an active node whose normal
form is the monomial of an implicit node (`{x}` of an atom, `∅` of the
unit) is in that node's class. The engine materializes a normal form with
`add`, which returns `x`'s class for `{x}` (`Normal::Single`) and the
unit's for `∅` (`Normal::Unit`), and merges the node's class into it. -/
def AtomCollapse (L : Laws n) (st : State n) (A : Set (Fin n)) (u : Option (Fin n)) : Prop :=
  ∀ M c N x, (M, c) ∈ (st.withAtoms A u).active → (N, x) ∈ atomNodes A u →
    ReflTransGen (Rw L (st.withAtoms A u).rules) M N →
    (∀ P, ¬ Rw L (st.withAtoms A u).rules N P) → st.find x = st.find c

/-- A round that changes nothing, with leaf constants. `nf_present`: the
normal form of an active node (stored or implicit) is a stored active node
of its class unless it is the monomial of an implicit node; `collapse`:
in that case the node is in the implicit node's class. `lhs_reduced` and
`cp_joinable` are the reducibility and (B) conditions of `RoundFixed` over
the rules of the completion view. -/
structure RoundFixedA (L : Laws n) (st : State n) (A : Set (Fin n)) (u : Option (Fin n)) :
    Prop where
  nf_present : ∀ M c N, (M, c) ∈ (st.withAtoms A u).active →
    ReflTransGen (Rw L (st.withAtoms A u).rules) M N →
    (∀ P, ¬ Rw L (st.withAtoms A u).rules N P) → (∀ x, (N, x) ∉ atomNodes A u) →
    ∃ c', (N, c') ∈ st.active ∧ st.find c' = st.find c
  collapse : AtomCollapse L st A u
  lhs_reduced : ∀ r₁ r₂, r₁ ∈ (st.withAtoms A u).rules → r₂ ∈ (st.withAtoms A u).rules →
    r₁ ≠ r₂ → ¬ r₂.1 ≤ r₁.1
  cp_joinable : ∀ r₁ r₂, r₁ ∈ (st.withAtoms A u).rules → r₂ ∈ (st.withAtoms A u).rules →
    r₁ ≠ r₂ → Overlap r₁.1 r₂.1 → ¬ r₁.1 ≤ r₂.1 → ¬ r₂.1 ≤ r₁.1 →
    Joinable (Rw L (st.withAtoms A u).rules) (criticalPair L r₁ r₂).1 (criticalPair L r₁ r₂).2

/-- `RoundFixedA` is `RoundFixed` of the completion view plus the
one-element collapse. In the direction `→`, `nf_present` for a normal form
that is an implicit node's monomial (`{x}` with `x ∈ A`, or `∅`) holds by
definition: its witness is the implicit node, in the node's class by
`collapse`. -/
theorem roundFixedA_iff {L : Laws n} {st : State n} {A : Set (Fin n)} {u : Option (Fin n)} :
    RoundFixedA L st A u ↔ RoundFixed L (st.withAtoms A u) ∧ AtomCollapse L st A u := by
  constructor
  · intro h
    refine ⟨⟨fun M c N hM hMN hN => ?_, h.lhs_reduced, h.cp_joinable⟩, h.collapse⟩
    by_cases hx : ∃ x, (N, x) ∈ atomNodes A u
    · obtain ⟨x, hx⟩ := hx
      exact ⟨x, State.implicit_active hx, h.collapse M c N x hM hx hMN hN⟩
    · push Not at hx
      obtain ⟨c', h₁, h₂⟩ := h.nf_present M c N hM hMN hN hx
      exact ⟨c', State.active_withAtoms h₁, h₂⟩
  · rintro ⟨h, hcol⟩
    refine ⟨fun M c N hM hMN hN hx => ?_, hcol, h.lhs_reduced, h.cp_joinable⟩
    obtain ⟨c', h₁, h₂⟩ := h.nf_present M c N hM hMN hN
    rcases State.mem_active_withAtoms.1 h₁ with h₁ | h₁
    · exact ⟨c', h₁, h₂⟩
    · exact absurd h₁ (hx c')

namespace RoundFixedA

variable {L : Laws n} {st : State n} {A : Set (Fin n)} {u : Option (Fin n)}

theorem roundFixed (h : RoundFixedA L st A u) : RoundFixed L (st.withAtoms A u) :=
  (roundFixedA_iff.1 h).1

/-- **A materialized node is in its implicit node's class at a fixed
round.** A stored active node `(N, c)` whose monomial is that of the
implicit node `(N, x)`, such as a one-element node `({x}, c)` with `x`
atomic, has the same normal form `N'` as the implicit node. If `N'` is an
implicit node's monomial, both are in its class by the collapse; otherwise
both classes hold a stored active node `N'`, and congruence of the stored
nodes joins them. This is the engine's `degeneracy_pair` merge, derived. -/
theorem materialized (hfix : RoundFixedA L st A u)
    (hcc : ∀ P c d, (P, c) ∈ st.active → (P, d) ∈ st.active → st.find c = st.find d)
    {N : Monomial n} {x c : Fin n} (hx : (N, x) ∈ atomNodes A u) (h : (N, c) ∈ st.active) :
    st.find c = st.find x := by
  obtain ⟨N', hN, hN'⟩ := exists_nf (Rw_wf (L := L) (rules_oriented (st.withAtoms A u))) N
  by_cases hy : ∃ y, (N', y) ∈ atomNodes A u
  · obtain ⟨y, hy⟩ := hy
    have h₁ := hfix.collapse _ c _ y (State.active_withAtoms h) hy hN hN'
    have h₂ := hfix.collapse _ x _ y (State.implicit_active hx) hy hN hN'
    rw [← h₁, h₂]
  · push Not at hy
    obtain ⟨c₁, h₁, e₁⟩ := hfix.nf_present _ c N' (State.active_withAtoms h) hN hN' hy
    obtain ⟨c₂, h₂, e₂⟩ := hfix.nf_present _ x N' (State.implicit_active hx) hN hN' hy
    rw [← e₁, ← e₂]
    exact hcc N' c₁ c₂ h₁ h₂

/-- Congruence on the completion view, from congruence on the stored
active nodes: no two implicit nodes share a monomial, and a stored node
with an implicit node's monomial is in its class (`materialized`). -/
theorem congr (hfix : RoundFixedA L st A u)
    (hcc : ∀ P c d, (P, c) ∈ st.active → (P, d) ∈ st.active → st.find c = st.find d) :
    ∀ P c d, (P, c) ∈ (st.withAtoms A u).active → (P, d) ∈ (st.withAtoms A u).active →
      (st.withAtoms A u).find c = (st.withAtoms A u).find d := by
  intro P c d hc hd
  rcases State.mem_active_withAtoms.1 hc with hc | hc <;>
    rcases State.mem_active_withAtoms.1 hd with hd | hd
  · exact hcc P c d hc hd
  · exact hfix.materialized hcc hd hc
  · exact (hfix.materialized hcc hc hd).symm
  · rw [atomNodes_func hc hd]

end RoundFixedA

/-! ## Completeness with leaf constants -/

/-- **Completeness at convergence with leaf constants.** The hypotheses of
`completion_complete_at_convergence`, read on the completion view
`st.withAtoms A`, except two that are stated on the stored state: the
round is fixed in the sense of `RoundFixedA` (the one-element collapse
included), and congruence `hcc` ranges over the stored active nodes. Two
`=_E`-equal monomials of the view, each a stored active node or the
one-element monomial `{x}` of an atom `x ∈ A` or the empty monomial of the
unit, are in one class.

The minimal-monomial state the view agrees with (`ha`, a `SlotState`) holds
each atom `{x}` as an active monomial of `x`'s class, so the right-hand
side of a class with an atom is a one-element monomial (or `∅` for the
unit's class), as `class_rhs_into` returns for an atomic class.
`I0Active` constrains only the classes holding an active node of the view;
a class neither atomic nor holding a node (a class of another operator
that no node references) is unconstrained. -/
theorem completion_complete_atoms {L : Laws n} {S : Set (Monomial n × Monomial n)}
    {st : State n} {A : Set (Fin n)} {u : Option (Fin n)}
    {ss₀ ss : SlotState n}
    (h5₀ : SlotState.I5 ss₀) (hrun : SlotState.OpsStar ss₀ ss)
    (ha : SlotState.Agrees (st.withAtoms A u) ss)
    (h0 : I0Active (st.withAtoms A u)) (hcanon : ∀ c, L.clamp (st.rhs c) = st.rhs c)
    (hfix : RoundFixedA L st A u)
    (hlaw : ∀ P Q, L.lawRel P Q → degLex P Q)
    (hnf_ax : ∀ M N, ¬ Rw (plain n) L.axRules (L.clamp M) N)
    (hcp : ∀ r₁ r₂, r₁ ∈ (st.withAtoms A u).rules ∪ L.axRules →
      r₂ ∈ (st.withAtoms A u).rules ∪ L.axRules → r₁ ≠ r₂ → Overlap r₁.1 r₂.1 →
      Joinable (Rw (plain n) ((st.withAtoms A u).rules ∪ L.axRules))
        (criticalPair (plain n) r₁ r₂).1 (criticalPair (plain n) r₁ r₂).2)
    (hcc : ∀ P c d, (P, c) ∈ st.active → (P, d) ∈ st.active → st.find c = st.find d)
    (hS : ∀ M N, (M, N) ∈ S → ∃ c d, (M, c) ∈ (st.withAtoms A u).active ∧
      (N, d) ∈ (st.withAtoms A u).active ∧ st.find c = st.find d)
    (hcancel : L.cancellative → ∀ M N X,
      Joinable (Rw (plain n) ((st.withAtoms A u).rules ∪ L.axRules)) (M + X) (N + X) →
      Joinable (Rw (plain n) ((st.withAtoms A u).rules ∪ L.axRules)) M N)
    {M N : Monomial n} {c d : Fin n} (hM : (M, c) ∈ (st.withAtoms A u).active)
    (hN : (N, d) ∈ (st.withAtoms A u).active) (hMN : E L S M N) : st.find c = st.find d :=
  completion_complete_at_convergence h5₀ hrun ha h0 hcanon hfix.roundFixed hlaw hnf_ax hcp
    (hfix.congr hcc) hS hcancel hM hN hMN

/-- The hypotheses of `completion_complete_atoms`, packaged, with two
replacements. `hcancel` is replaced by lattice closure for a cancellative
operator: the engine's `lattice_round` establishes `LatticeClosed` at its
fixpoint (`Lattice.latticeClosed_of_engineFixed`) and does not establish
`hcancel` (`Lattice.hcancel_not_derivable`). `hcp` is replaced by its
part involving a law instance (`AxiomCP`): the rule-rule part follows from
the fixed round (`ruleRuleCP_of_fixed`, through `hcp_of_fixed`). -/
structure CompleteAtoms (L : Laws n) (S : Set (Monomial n × Monomial n)) (st : State n)
    (A : Set (Fin n)) (u : Option (Fin n)) : Prop where
  slots : ∃ ss₀ ss : SlotState n,
    SlotState.I5 ss₀ ∧ SlotState.OpsStar ss₀ ss ∧ SlotState.Agrees (st.withAtoms A u) ss
  h0 : I0Active (st.withAtoms A u)
  hcanon : ∀ c, L.clamp (st.rhs c) = st.rhs c
  hfix : RoundFixedA L st A u
  hlaw : ∀ P Q, L.lawRel P Q → degLex P Q
  hnf_ax : ∀ M N, ¬ Rw (plain n) L.axRules (L.clamp M) N
  hcp_ax : AxiomCP L (st.withAtoms A u).rules
  hcc : ∀ P c d, (P, c) ∈ st.active → (P, d) ∈ st.active → st.find c = st.find d
  hS : ∀ M N, (M, N) ∈ S → ∃ c d, (M, c) ∈ (st.withAtoms A u).active ∧
    (N, d) ∈ (st.withAtoms A u).active ∧ st.find c = st.find d
  hlat : L.cancellative → Lattice.LatticeClosed L (st.withAtoms A u)

namespace CompleteAtoms

variable {L : Laws n} {S : Set (Monomial n × Monomial n)} {st : State n} {A : Set (Fin n)}
  {u : Option (Fin n)}

/-- `completion_complete_atoms` on the packaged hypotheses. For a
cancellative operator the conclusion comes from lattice closure alone
(`Lattice.complete_of_latticeClosed`, what the engine's `lattice_round`
establishes at its fixpoint); otherwise `hcancel` is vacuous and the
rewriting argument applies. -/
theorem same_class (h : CompleteAtoms L S st A u) {M N : Monomial n} {c d : Fin n}
    (hM : (M, c) ∈ (st.withAtoms A u).active) (hN : (N, d) ∈ (st.withAtoms A u).active)
    (hMN : E L S M N) : st.find c = st.find d := by
  by_cases hc : L.cancellative
  · exact Lattice.complete_of_latticeClosed (h.hlat hc) h.hS hM hN (Lattice.E_union_left hMN)
  · obtain ⟨ss₀, ss, h5₀, hrun, ha⟩ := h.slots
    exact completion_complete_atoms h5₀ hrun ha h.h0 h.hcanon h.hfix h.hlaw h.hnf_ax
      (hcp_of_fixed h.hfix.roundFixed h.hcp_ax) h.hcc h.hS (fun h => absurd h hc) hM hN hMN

/-- Two stored active nodes. -/
theorem nodes (h : CompleteAtoms L S st A u) {M N : Monomial n} {c d : Fin n}
    (hM : (M, c) ∈ st.active) (hN : (N, d) ∈ st.active) (hMN : E L S M N) :
    st.find c = st.find d :=
  h.same_class (State.active_withAtoms hM) (State.active_withAtoms hN) hMN

/-- **A node equal to a leaf constant lands in the constant's class.** -/
theorem atom_class (h : CompleteAtoms L S st A u) {M : Monomial n} {c x : Fin n}
    (hM : (M, c) ∈ st.active) (hx : x ∈ A) (hMx : E L S M {x}) : st.find c = st.find x :=
  h.same_class (State.active_withAtoms hM) (State.atom_active hx) hMx

/-- Two leaf constants equal in the theory are in one class. -/
theorem atoms (h : CompleteAtoms L S st A u) {x y : Fin n} (hx : x ∈ A) (hy : y ∈ A)
    (hxy : E L S ({x} : Monomial n) {y}) : st.find x = st.find y :=
  h.same_class (State.atom_active hx) (State.atom_active hy) hxy

/-- A node equal to the empty monomial lands in the unit's class. -/
theorem unit_class (h : CompleteAtoms L S st A u) {M : Monomial n} {c x : Fin n}
    (hM : (M, c) ∈ st.active) (hx : u = some x) (hMx : E L S M 0) : st.find c = st.find x :=
  h.same_class (State.active_withAtoms hM) (State.unit_active hx) hMx

/-- A materialized one-element node is in its child's class. -/
theorem materialized (h : CompleteAtoms L S st A u) {x c : Fin n} (hx : x ∈ A)
    (hc : (({x} : Monomial n), c) ∈ st.active) : st.find c = st.find x :=
  h.hfix.materialized h.hcc (Or.inl ⟨hx, rfl⟩) hc

end CompleteAtoms

end SemperProofs.CC
