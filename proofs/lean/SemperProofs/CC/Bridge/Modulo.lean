import SemperProofs.CC.Bridge.Represents

/-!
# Bridge: matching modulo the AC theory

Composes completeness of AC-congruence closure
(`completion_complete_at_convergence`) with the plan theorems of the
e-matching engine (`engine_plan_sound` / `engine_plan_complete`) on the
graph `represents st f A`.

* `CompleteHyps L S st` packages the hypotheses of
  `completion_complete_at_convergence` verbatim.
* `ac_equal_same_class`: two `=_E`-equal active nodes are in one class;
  `ac_equal_same_class_graph` restates it on the graph.
* `Term` / `ETerm`: the binary ground terms of the operator over the class
  pool and the set of those `=_E`-equal to a node's monomial.
* `matches_closed_under_theory`: a match at any node whose monomial is
  `=_E`-equal to `n`'s is a match at `n`'s class. The per-node form (a
  match at `n` yields a match at `n'`) is false: `per_node_form_fails`.
* `engine_match_modulo_complete` / `engine_match_modulo_sound`: the
  composition with the plan theorems.
-/

namespace SemperProofs.CC.Bridge

open Semper.EMatch

variable {n : ℕ}

/-! ## The hypotheses of completeness at convergence -/

/-- The hypotheses of `completion_complete_at_convergence`, verbatim, on
the converged state `st` for the laws `L` and the asserted equations `S`.
See `CC/Main.lean` and `CC/Assemble.lean` for their reading. -/
structure CompleteHyps (L : Laws n) (S : Set (Monomial n × Monomial n)) (st : State n) :
    Prop where
  slots : ∃ ss₀ ss : SlotState n,
    SlotState.I5 ss₀ ∧ SlotState.OpsStar ss₀ ss ∧ SlotState.Agrees st ss
  h0 : I0Active st
  hcanon : ∀ c, L.clamp (st.rhs c) = st.rhs c
  hfix : RoundFixed L st
  hlaw : ∀ P Q, L.lawRel P Q → degLex P Q
  hnf_ax : ∀ M N, ¬ Rw (plain n) L.axRules (L.clamp M) N
  hcp : ∀ r₁ r₂, r₁ ∈ st.rules ∪ L.axRules → r₂ ∈ st.rules ∪ L.axRules → r₁ ≠ r₂ →
    Overlap r₁.1 r₂.1 →
    Joinable (Rw (plain n) (st.rules ∪ L.axRules))
      (criticalPair (plain n) r₁ r₂).1 (criticalPair (plain n) r₁ r₂).2
  hcc : ∀ P c d, (P, c) ∈ st.nodes → (P, d) ∈ st.nodes → st.find c = st.find d
  hS : ∀ M N, (M, N) ∈ S →
    ∃ c d, (M, c) ∈ st.active ∧ (N, d) ∈ st.active ∧ st.find c = st.find d
  hcancel : L.cancellative → ∀ M N X,
    Joinable (Rw (plain n) (st.rules ∪ L.axRules)) (M + X) (N + X) →
    Joinable (Rw (plain n) (st.rules ∪ L.axRules)) M N

/-- Two `=_E`-equal active nodes of a converged state are in one class. -/
theorem ac_equal_same_class {L : Laws n} {S : Set (Monomial n × Monomial n)} {st : State n}
    (h : CompleteHyps L S st) {M N : Monomial n} {c d : Fin n}
    (hM : (M, c) ∈ st.active) (hN : (N, d) ∈ st.active) (hMN : E L S M N) :
    st.find c = st.find d := by
  obtain ⟨ss₀, ss, h5₀, hrun, ha⟩ := h.slots
  exact completion_complete_at_convergence h5₀ hrun ha h.h0 h.hcanon h.hfix h.hlaw h.hnf_ax
    h.hcp h.hcc h.hS h.hcancel hM hN hMN

/-- On the graph: two `mset` nodes whose monomials are `=_E`-equal are in
one class. -/
theorem ac_equal_same_class_graph {L : Laws n} {S : Set (Monomial n × Monomial n)}
    {st : State n} {A : Finset (Monomial n × Fin n)} (h : CompleteHyps L S st)
    (hA : Enumerates st A) (f : Sym) {p q : Monomial n × Fin n} (hp : p ∈ A) (hq : q ∈ A)
    (hpq : E L S p.1 q.1) :
    (represents st f A).find (nodeId p) = (represents st f A).find (nodeId q) := by
  rw [represents_find, represents_find]
  exact congrArg clsId (ac_equal_same_class h ((hA p).1 hp) ((hA q).1 hq) hpq)

/-! ## Ground terms of the operator and the theory on patterns -/

/-- A binary ground term of the operator over the class pool: a leaf is a
class, `app s t` is `f(s, t)`. Associativity and commutativity are absorbed
by `flatten`. -/
inductive Term (n : ℕ) where
  | leaf (x : Fin n)
  | app (s t : Term n)

/-- The flat AC node of a term: its multiset of leaves. -/
def Term.flatten : Term n → Monomial n
  | .leaf x => {x}
  | .app s t => s.flatten + t.flatten

/-- The terms `=_E`-equal to a node's monomial. -/
def ETerm (L : Laws n) (S : Set (Monomial n × Monomial n)) (p : Monomial n × Fin n) :
    Set (Term n) :=
  { t | E L S t.flatten p.1 }

/-- The match set of a pattern at a class: the bindings matching `P` at
any node of the class. -/
def ClassMatches (G : Graph) (P : Pat) (c : C) : Set Binding :=
  { σ | MatchC G P c σ }

/-- A match at a node lifts to a match at its class. -/
theorem matchC_of_matchN {st : State n} {f : Sym} {A : Finset (Monomial n × Fin n)}
    {p : Monomial n × Fin n} (hp : p ∈ A) {P : Pat} (hhead : P.head = some f) {σ : Binding}
    (hm : MatchN (represents st f A) P (mkNode st f p) σ) :
    MatchC (represents st f A) P ((represents st f A).find (nodeId p)) σ :=
  MatchC.app (node_mem_represents hp) rfl hhead hm

/-- Matches are closed under the theory, at the class level: for every
active node `p'` whose monomial is `=_E`-equal to `p`'s, every binding
matching `P` at `p'`'s node matches `P` at `p`'s class. The root of the
pattern binds the class `find p`, not the node `p`. -/
theorem matches_closed_under_theory {L : Laws n} {S : Set (Monomial n × Monomial n)}
    {st : State n} {A : Finset (Monomial n × Fin n)} (h : CompleteHyps L S st)
    (hA : Enumerates st A) {f : Sym} {p p' : Monomial n × Fin n} (hp : p ∈ A) (hp' : p' ∈ A)
    (hE : E L S p.1 p'.1) {P : Pat} (hhead : P.head = some f) {σ : Binding}
    (hm : MatchN (represents st f A) P (mkNode st f p') σ) :
    MatchC (represents st f A) P ((represents st f A).find (nodeId p)) σ := by
  rw [ac_equal_same_class_graph h hA f hp hp' hE]
  exact matchC_of_matchN hp' hhead hm

/-- The class-level match set is determined by the theory-equivalence class
of the node's monomial. -/
theorem classMatches_congr {L : Laws n} {S : Set (Monomial n × Monomial n)}
    {st : State n} {A : Finset (Monomial n × Fin n)} (h : CompleteHyps L S st)
    (hA : Enumerates st A) (f : Sym) {p p' : Monomial n × Fin n} (hp : p ∈ A) (hp' : p' ∈ A)
    (hE : E L S p.1 p'.1) (P : Pat) :
    ClassMatches (represents st f A) P ((represents st f A).find (nodeId p)) =
      ClassMatches (represents st f A) P ((represents st f A).find (nodeId p')) := by
  rw [ac_equal_same_class_graph h hA f hp hp' hE]

/-- A term of `ETerm p` whose flat node is present is in `p`'s class, and
every match at its node is a match at `p`'s class. -/
theorem eterm_matches {L : Laws n} {S : Set (Monomial n × Monomial n)}
    {st : State n} {A : Finset (Monomial n × Fin n)} (h : CompleteHyps L S st)
    (hA : Enumerates st A) {f : Sym} {p : Monomial n × Fin n} (hp : p ∈ A) {t : Term n}
    (ht : t ∈ ETerm L S p) {c' : Fin n} (hc' : (t.flatten, c') ∈ A) {P : Pat}
    (hhead : P.head = some f) {σ : Binding}
    (hm : MatchN (represents st f A) P (mkNode st f (t.flatten, c')) σ) :
    (represents st f A).find (nodeId (t.flatten, c')) = (represents st f A).find (nodeId p) ∧
    MatchC (represents st f A) P ((represents st f A).find (nodeId p)) σ :=
  ⟨ac_equal_same_class_graph h hA f hc' hp ht,
    matches_closed_under_theory h hA hp hc' (E.symm ht) hhead hm⟩

/-! ## The per-node form is false -/

/-- The state of the counterexample: six classes, `find` the identity, the
two active nodes `f{0, 1, 2}` and `f{0, 3}` in class 4, and the nodes
`f{1, 2}` and `f{3}` in class 3 (so that `{1, 2} =_E {3}` is an asserted
equation between active nodes of one class). -/
def cexState : State 6 where
  find := id
  nodes := {({0, 1, 2}, 4), ({0, 3}, 4), ({1, 2}, 3), ({3}, 3)}
  retired := ∅
  rhs := fun _ => ∅

/-- The enumeration of the counterexample's active nodes. -/
def cexA : Finset (Monomial 6 × Fin 6) := {({0, 1, 2}, 4), ({0, 3}, 4), ({1, 2}, 3), ({3}, 3)}

/-- The asserted equation `{1, 2} = {3}`. -/
def cexS : Set (Monomial 6 × Monomial 6) := {({1, 2}, {3})}

/-- The pattern `f{x, y, z}`: three distinct elements, no rest. -/
def cexPat : Pat := .ac 0 [(.var 0, .exact 1), (.var 1, .exact 1), (.var 2, .exact 1)] none

theorem cexA_enumerates : Enumerates cexState cexA := by
  intro p
  simp [cexA, cexState, State.active]

theorem cex_E : E (Laws.plainAC 6) cexS ({0, 1, 2} : Monomial 6) {0, 3} := by
  have h : E (Laws.plainAC 6) cexS ({1, 2} + {0}) ({3} + {0}) :=
    E.congr {0} (E.ax (by simp [cexS]))
  have e₁ : ({1, 2} : Monomial 6) + {0} = {0, 1, 2} := by decide
  have e₂ : ({3} : Monomial 6) + {0} = {0, 3} := by decide
  rwa [e₁, e₂] at h

/-- The binding `x ↦ 0, y ↦ 1, z ↦ 2`. -/
def cexσ : Binding :=
  { Binding.empty with cls := fun x => if x < 3 then some x else none }

theorem cex_match :
    MatchN (represents cexState 0 cexA) cexPat (mkNode cexState 0 ({0, 1, 2}, 4)) cexσ := by
  have hm : mkNode cexState 0 ({0, 1, 2}, 4) = ⟨0, .mset {0, 1, 2}⟩ := by
    simp [mkNode, cexState, clsId]
  rw [hm]
  refine MatchN.ac (taken := [0, 1, 2]) (by decide) rfl (by decide) ?_ ?_ ?_
  · intro et het
    simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_cons,
      List.not_mem_nil, or_false] at het
    rcases het with rfl | rfl | rfl <;> exact MatchC.var (by simp [cexσ])
  · intro et het
    simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_cons,
      List.not_mem_nil, or_false] at het
    rcases het with rfl | rfl | rfl <;> simp only [MultOk] <;> decide
  · simp [MsetRestOk]

theorem cex_no_match (σ : Binding) :
    ¬ MatchN (represents cexState 0 cexA) cexPat (mkNode cexState 0 ({0, 3}, 4)) σ := by
  have hm : mkNode cexState 0 ({0, 3}, 4) = ⟨0, .mset {0, 3}⟩ := by
    simp [mkNode, cexState, clsId]
  rw [hm]
  intro h
  cases h with
  | @ac _ _ _ _ taken _ hnd hlen hmem _ _ _ =>
    have hsub : (taken : Multiset C) ⊆ ({0, 3} : Multiset C) := fun c hc => hmem c (by simpa using hc)
    have hle : (taken : Multiset C) ≤ ({0, 3} : Multiset C) :=
      (Multiset.le_iff_subset (by simpa using hnd)).2 hsub
    have := Multiset.card_le_card hle
    simp at hlen
    simp at this
    omega

/-- **The per-node form of closure under the theory is false.** There is a
converged-shaped state with two active nodes `p = f{0, 1, 2}` and
`p' = f{0, 3}` of one class, `=_E`-equal under the asserted equation
`{1, 2} = {3}`, a pattern `f{x, y, z}` and a binding matching it at `p`'s
node, while no binding matches it at `p'`'s node: the pattern needs three
distinct children, `p'` has two. The match at `p` is a match at the
class (`matches_closed_under_theory`), which is all that holds. -/
theorem per_node_form_fails :
    ∃ (st : State 6) (A : Finset (Monomial 6 × Fin 6)) (L : Laws 6)
      (S : Set (Monomial 6 × Monomial 6)) (p p' : Monomial 6 × Fin 6) (P : Pat) (σ : Binding),
      Enumerates st A ∧ p ∈ A ∧ p' ∈ A ∧ st.find p.2 = st.find p'.2 ∧ E L S p.1 p'.1 ∧
      P.head = some 0 ∧
      MatchN (represents st 0 A) P (mkNode st 0 p) σ ∧
      ∀ σ', ¬ MatchN (represents st 0 A) P (mkNode st 0 p') σ' :=
  ⟨cexState, cexA, Laws.plainAC 6, cexS, ({0, 1, 2}, 4), ({0, 3}, 4), cexPat, cexσ,
    cexA_enumerates, by simp [cexA], by simp [cexA], rfl, cex_E, rfl, cex_match, cex_no_match⟩

/-! ## Composition with the plan theorems -/

/-- **E-matching is complete modulo the AC theory, at the class level.**

Let `st` be a converged completion state satisfying the hypotheses of
`completion_complete_at_convergence` (`CompleteHyps`), `A` enumerate its
active nodes and `G = represents st f A` be the e-matching graph of the
operator `f`. Let `p` be an active node and `t` a ground term of the
operator `=_E`-equal to `p`'s monomial (`t ∈ ETerm L S p`) whose flat node
`(t.flatten, c')` is present. Then every binding `σ` matching the pattern
`P` at `t`'s node is emitted by every `PlanOK` plan for `P`, with the root
node variable `r` bound to a node of `p`'s class and the pattern variables
bound below `σ`.

The remaining gap: a term `t ∈ ETerm L S p` whose flat node is *not*
present (`t.flatten` is no active node) has no node in `G` and is not
matched node-wise; a pattern that would match `t`'s flat node but no
present node of the class (`per_node_form_fails` shows the shape) finds no
binding. Such a term is matched only through the class: the root of the
pattern binds the class `find p`, and that class is the class of every
present term `=_E`-equal to `p`. This is the semantics the paper states for
e-matching over e-classes: a pattern matches an e-class, and a class
represents a term when it holds one node spelling it. -/
theorem engine_match_modulo_complete {L : Laws n} {S : Set (Monomial n × Monomial n)}
    {st : State n} {A : Finset (Monomial n × Fin n)} (h : CompleteHyps L S st)
    (hA : Enumerates st A) {f : Sym} {sig : Sym → Kind} (hf : sig f = .ac) {P : Pat} {r : Var}
    {plan : Plan} (hwk : PatWK sig P) (hnd : P.restVars.Nodup) (hr : r ∉ P.vars)
    (hP : P.head.isSome = true) (hplan : PlanOK ((atoms P r).map QAtom.scan) plan)
    {p : Monomial n × Fin n} (hp : p ∈ A) {t : Term n} (ht : t ∈ ETerm L S p) {c' : Fin n}
    (hc' : (t.flatten, c') ∈ A) {σ : Binding}
    (hm : MatchN (represents st f A) P (mkNode st f (t.flatten, c')) σ) :
    ∃ σ' ∈ run (represents st f A) plan Binding.empty, ∃ id,
      σ'.node r = some id ∧
      (represents st f A).find id = (represents st f A).find (nodeId p) ∧
      BelowOn P.vars σ' σ := by
  obtain ⟨σ', hσ', hroot, hbelow⟩ :=
    engine_plan_complete (represents_keysNodup st f A) (represents_conforms st f A sig hf) hwk
      hnd hr hP hplan (node_mem_represents hc') hm
  exact ⟨σ', hσ', nodeId (t.flatten, c'), hroot,
    ac_equal_same_class_graph h hA f hc' hp ht, hbelow⟩

/-- **Soundness modulo the theory.** Every binding a `PlanOK` plan emits
matches `P` at the node of some active `p'`, binds the root class to
`find p'`, and is a class-level match for every active `p` whose monomial
is `=_E`-equal to `p'`'s. -/
theorem engine_match_modulo_sound {L : Laws n} {S : Set (Monomial n × Monomial n)}
    {st : State n} {A : Finset (Monomial n × Fin n)} (h : CompleteHyps L S st)
    (hA : Enumerates st A) {f : Sym} {sig : Sym → Kind} (hf : sig f = .ac) {P : Pat} {r : Var}
    {plan : Plan} (hwk : PatWK sig P) (hnd : P.restVars.Nodup) (hr : r ∉ P.vars)
    (hP : P.head.isSome = true) (hplan : PlanOK ((atoms P r).map QAtom.scan) plan)
    {σ : Binding} (hσ : σ ∈ run (represents st f A) plan Binding.empty) :
    ∃ p' ∈ A, σ.node r = some (nodeId p') ∧
      σ.cls r = some ((represents st f A).find (nodeId p')) ∧
      MatchN (represents st f A) P (mkNode st f p') σ ∧
      ∀ p ∈ A, E L S p.1 p'.1 →
        MatchC (represents st f A) P ((represents st f A).find (nodeId p)) σ := by
  obtain ⟨id, nd, hroot, hmem, hcls, hm⟩ :=
    engine_plan_sound (represents_keysNodup st f A) (represents_conforms st f A sig hf) hwk
      hnd hr hP hplan hσ
  obtain ⟨p', hp', rfl, rfl⟩ := mem_represents.1 hmem
  refine ⟨p', hp', hroot, hcls, hm, fun p hp hE => ?_⟩
  have hhead : P.head = some f := by cases hm; rfl
  exact matches_closed_under_theory h hA hp hp' hE hhead hm

end SemperProofs.CC.Bridge
