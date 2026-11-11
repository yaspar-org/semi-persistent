import SemperProofs.CC.Lemmas
import SemperProofs.CC.Proofs.CriticalPairModulo
import SemperProofs.CC.Slot

/-!
# Completeness at convergence from engine-level hypotheses

`same_class` and `fix_sufficient` take `hjoin : ∀ M N, E L S M N →
Joinable (Rw L st.rules) M N`, the conclusion of L13. That hypothesis is
not an engine fact, and it is not even satisfiable in general: a monomial
that is `R`-normal but not `clamp`-canonical (such as `{e, a}` with the
identity `e`) has no `Rw L R` step, so it is not `Rw L R`-joinable with
`{a}` although `=_E`-equal to it. The engine never holds such a monomial,
but the induction of L13 passes through them (the `congr` case builds
`M + X`).

The assembly here therefore runs the induction of L13 over plain rewriting
by the rules together with the law instances, `Rw (plain n) (R ∪ Ax)`,
which is confluent by the proof of `confluent_modulo'`, and reads the result
back on active nodes through their right-hand sides, which are normal forms
for that system. Every hypothesis of the final theorem is a property of the
laws, of the slot maintenance, or of the converged state.
-/

namespace SemperProofs.CC

open Relation

variable {n : ℕ}

/-- Plain rewriting by the rules and the law instances. -/
abbrev RwAx (L : Laws n) (R : Rules n) : Monomial n → Monomial n → Prop :=
  Rw (plain n) (R ∪ L.axRules)

/-- A law instance is one `RwAx` step. -/
theorem RwAx_of_law {L : Laws n} {R : Rules n} {P Q : Monomial n} (h : L.lawRel P Q) :
    RwAx L R P Q :=
  ⟨P, Q, Or.inr h, le_rfl, by rw [plain_clamp, tsub_self, zero_add]⟩

/-- `RwAx` is confluent under the hypotheses of `confluent_modulo'`. -/
theorem RwAx_confluent (L : Laws n) (R : Rules n)
    (hor : Oriented R)
    (hlaw : ∀ P Q, L.lawRel P Q → degLex P Q)
    (hcp : ∀ r₁ r₂, r₁ ∈ R ∪ L.axRules → r₂ ∈ R ∪ L.axRules → r₁ ≠ r₂ →
      Overlap r₁.1 r₂.1 →
      Joinable (RwAx L R) (criticalPair (plain n) r₁ r₂).1 (criticalPair (plain n) r₁ r₂).2) :
    Confluent (RwAx L R) :=
  newman (Rw_wf (oriented_union hor hlaw)) (critical_pair_lemma (plain n) (fun _ => rfl) _ hcp)

/-- The induction of L13 over `RwAx`: every `=_E`-equal pair is
`RwAx`-joinable, given that every asserted equation is a pair of active
nodes in one class of a converged state. -/
theorem E_joinable_RwAx {L : Laws n} {S : Set (Monomial n × Monomial n)} {st : State n}
    (hconv : Converged L st)
    (hconf : Confluent (RwAx L st.rules))
    (hS : ∀ M N, (M, N) ∈ S →
      ∃ c d, (M, c) ∈ st.active ∧ (N, d) ∈ st.active ∧ st.find c = st.find d)
    (hcancel : L.cancellative → ∀ M N X,
      Joinable (RwAx L st.rules) (M + X) (N + X) → Joinable (RwAx L st.rules) M N)
    {M N : Monomial n} (h : E L S M N) : Joinable (RwAx L st.rules) M N := by
  induction h with
  | ax h =>
    obtain ⟨c, d, hMc, hNd, hcd⟩ := hS _ _ h
    have h₁ := hconv.nodes_reduce _ c hMc
    have h₂ := hconv.nodes_reduce _ d hNd
    rw [hcd] at h₁
    exact ⟨_, Rw_rtg_embed h₁, Rw_rtg_embed h₂⟩
  | refl M => exact ⟨M, ReflTransGen.refl, ReflTransGen.refl⟩
  | symm _ ih => obtain ⟨P, h₁, h₂⟩ := ih; exact ⟨P, h₂, h₁⟩
  | trans _ _ ih₁ ih₂ =>
    obtain ⟨P, h₁, h₂⟩ := ih₁
    obtain ⟨Q, h₃, h₄⟩ := ih₂
    obtain ⟨T, h₅, h₆⟩ := hconf _ _ _ h₂ h₃
    exact ⟨T, h₁.trans h₅, h₄.trans h₆⟩
  | congr X _ ih => exact Joinable_add (fun _ => rfl) X ih
  | law h => exact ⟨_, ReflTransGen.single (RwAx_of_law h), ReflTransGen.refl⟩
  | cancel hc _ ih => exact hcancel hc _ _ _ ih

/-- Every monomial rewrites to its `clamp` in at most one law step. -/
theorem clamp_rtg_RwAx (L : Laws n) (R : Rules n) (M : Monomial n) :
    ReflTransGen (RwAx L R) M (L.clamp M) := by
  rcases L.clamp_law M with h | h
  · rw [h]
  · exact ReflTransGen.single (RwAx_of_law h)

/-- A step by a rule or a law (`State.RwL`) is a chain of plain steps by
the rules and the law instances: a clamped rule step is a plain rule step
followed by at most one law step (`Rw_embed`), and a law step alone is one
law instance (`clamp_rtg_RwAx`). -/
theorem RwL_embed {L : Laws n} {st : State n} {M N : Monomial n} (h : st.RwL L M N) :
    ReflTransGen (RwAx L st.rules) M N := by
  rcases h with h | ⟨rfl, -⟩
  · exact Rw_embed h
  · exact clamp_rtg_RwAx L _ M

theorem RwL_rtg_embed {L : Laws n} {st : State n} {M N : Monomial n}
    (h : ReflTransGen (st.RwL L) M N) : ReflTransGen (RwAx L st.rules) M N := by
  induction h with
  | refl => exact ReflTransGen.refl
  | tail _ hstep ih => exact ih.trans (RwL_embed hstep)

/-- **The rule-rule critical pairs of a fixed round are joinable under plain
rewriting by the rules and law instances.** `RoundFixed.cp_joinable_all`
joins the clamped reducts under clamped rewriting; each plain reduct
reaches its clamp in at most one law step (`clamp_rtg_RwAx`), and a clamped
step embeds into plain steps (`Rw_rtg_embed`). This is the rule-rule part
of `hcp`, derived from the fixpoint; the pairs that involve a law instance
are `AxiomCP`. -/
theorem ruleRuleCP_of_fixed {L : Laws n} {st : State n} (hfix : RoundFixed L st) :
    ∀ r₁ r₂, r₁ ∈ st.rules → r₂ ∈ st.rules → r₁ ≠ r₂ → Overlap r₁.1 r₂.1 →
      Joinable (RwAx L st.rules)
        (criticalPair (plain n) r₁ r₂).1 (criticalPair (plain n) r₁ r₂).2 := by
  intro r₁ r₂ h₁ h₂ hne hov
  obtain ⟨P, hP₁, hP₂⟩ := hfix.cp_joinable_all r₁ r₂ h₁ h₂ hne hov
  exact ⟨P, (clamp_rtg_RwAx L _ _).trans (Rw_rtg_embed hP₁),
    (clamp_rtg_RwAx L _ _).trans (Rw_rtg_embed hP₂)⟩

/-- The critical pairs of `R ∪ Ax` that involve a law instance: a rule
against a law instance, or two law instances. These are the pairs the
engine's per-rule axiom critical pairs and the inverse rules R1 to R5
address; `CC/Laws/` discharges them law by law from conditions on the
left-hand sides. For a law set with no law instance (plain AC) the
hypothesis is empty (`AxiomCP.of_no_ax`). -/
def AxiomCP (L : Laws n) (R : Rules n) : Prop :=
  ∀ r₁ r₂, r₁ ∈ R ∪ L.axRules → r₂ ∈ R ∪ L.axRules → (r₁ ∈ L.axRules ∨ r₂ ∈ L.axRules) →
    r₁ ≠ r₂ → Overlap r₁.1 r₂.1 →
    Joinable (Rw (plain n) (R ∪ L.axRules))
      (criticalPair (plain n) r₁ r₂).1 (criticalPair (plain n) r₁ r₂).2

theorem AxiomCP.of_no_ax {L : Laws n} {R : Rules n} (h : ∀ p, p ∉ L.axRules) : AxiomCP L R :=
  fun r₁ r₂ _ _ hax _ _ => (hax.elim (h r₁) (h r₂)).elim

/-- **`hcp` from the fixpoint.** The critical-pair hypothesis of
`completion_complete_at_convergence` over `R ∪ Ax` splits into the
rule-rule pairs, which `RoundFixed` gives (`ruleRuleCP_of_fixed`), and the
pairs involving a law instance (`AxiomCP`). -/
theorem hcp_of_fixed {L : Laws n} {st : State n} (hfix : RoundFixed L st)
    (hax : AxiomCP L st.rules) :
    ∀ r₁ r₂, r₁ ∈ st.rules ∪ L.axRules → r₂ ∈ st.rules ∪ L.axRules → r₁ ≠ r₂ →
      Overlap r₁.1 r₂.1 →
      Joinable (Rw (plain n) (st.rules ∪ L.axRules))
        (criticalPair (plain n) r₁ r₂).1 (criticalPair (plain n) r₁ r₂).2 := by
  intro r₁ r₂ h₁ h₂ hne hov
  rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
  · exact ruleRuleCP_of_fixed hfix r₁ r₂ h₁ h₂ hne hov
  · exact hax r₁ r₂ (Or.inl h₁) (Or.inr h₂) (Or.inr h₂) hne hov
  · exact hax r₁ r₂ (Or.inr h₁) (Or.inl h₂) (Or.inl h₁) hne hov
  · exact hax r₁ r₂ (Or.inr h₁) (Or.inr h₂) (Or.inl h₁) hne hov

/-- The rule set of a state is oriented by definition (`State.rules` folds
`degLex` in; the engine's read-time guard). -/
theorem rules_oriented (st : State n) : Oriented st.rules :=
  fun _ _ ⟨_, _, _, _, h, _, _⟩ => h

/-- I0 strengthened, on the classes that hold an active node: such a
class's right-hand side is an *active* node of that class. The engine's
slot names an active node: `refresh_min_monomial` considers active nodes
only and retirement requires a smaller active classmate. A class with no
active node of the operator (a leaf constant such as `a` in `a + b`, or a
class of another operator) is not constrained; `Atoms.lean` reads a leaf
constant `x` as its one-element monomial `{x}`.

Before 2026-11-06 the quantifier ranged over every class of `Fin n`
(`I0ActiveAll`), which no state with a leaf constant satisfies. -/
def I0Active (st : State n) : Prop :=
  ∀ M c, (M, c) ∈ st.active →
    ∃ c', (st.rhs (st.find c), c') ∈ st.active ∧ st.find c' = st.find c

/-- The former `I0Active`: every class of `Fin n`, with or without an
active node, has an active node as right-hand side. -/
def I0ActiveAll (st : State n) : Prop :=
  ∀ c, ∃ c', (st.rhs (st.find c), c') ∈ st.active ∧ st.find c' = st.find c

theorem I0Active_of_all {st : State n} (h : I0ActiveAll st) : I0Active st :=
  fun _ c _ => h c

theorem I0On_of_active {st : State n} (h : I0Active st) : I0On st :=
  fun M c hM => let ⟨c', h₁, h₂⟩ := h M c hM; ⟨c', h₁.1, h₂⟩

/-- Right-hand sides of classes holding an active node are normal forms of
the rules, derived: a step from `rhs c` lands strictly below it in
degree-lex, its normal form is an active classmate by `nf_present`, and I5
puts no active classmate strictly below `rhs c`. -/
theorem rhs_normal {L : Laws n} {st : State n} (h0 : I0Active st) (h5 : I5 st)
    (hfix : RoundFixed L st) {M : Monomial n} {c : Fin n} (hM : (M, c) ∈ st.active)
    (P : Monomial n) :
    ¬ Rw L st.rules (st.rhs (st.find c)) P := by
  intro hP
  obtain ⟨c', hc', hcc'⟩ := h0 M c hM
  obtain ⟨N, hPN, hN⟩ := exists_nf (Rw_wf (L := L) (rules_oriented st)) P
  have hrN : ReflTransGen (Rw L st.rules) (st.rhs (st.find c)) N := ReflTransGen.head hP hPN
  have hlt : degLex (st.rhs (st.find c)) N := by
    have h₁ := Rw_degLex (rules_oriented st) hP
    rcases hPN.cases_head with rfl | ⟨Q, hQ, hQN⟩
    · exact h₁
    · -- iterate `Rw_degLex` along `P →* N`
      have : ∀ {A B : Monomial n}, ReflTransGen (Rw L st.rules) A B → A = B ∨ degLex A B := by
        intro A B h
        induction h with
        | refl => exact Or.inl rfl
        | tail _ hs ih =>
          rcases ih with rfl | ih
          · exact Or.inr (Rw_degLex (rules_oriented st) hs)
          · exact Or.inr (degLex_trans ih (Rw_degLex (rules_oriented st) hs))
      rcases this hPN with rfl | h₂
      · exact h₁
      · exact degLex_trans h₁ h₂
  obtain ⟨c'', hN', hcc''⟩ := hfix.nf_present _ c' N hc' (hcc' ▸ hrN) hN
  rcases h5 N c'' hN' with h | h
  · rw [hcc'', hcc'] at h
    rw [h] at hlt
    exact degLex_irrefl _ hlt
  · rw [hcc'', hcc'] at h
    exact degLex_irrefl _ (degLex_trans hlt h)

/-- Completeness at convergence for the fixed engine, from engine-level
hypotheses only. Two `=_E`-equal active nodes are in one class, provided:

* `h5₀`, `hrun`, `ha`: the run maintained the min-monomial slots with the
  refresh, from a state whose slots were least, and the completion state
  agrees with the slot state (discharges I5 through `reachable_I5`);
* `h0`: every class holding an active node has one of its own active nodes
  as right-hand side;
* `hcanon`: right-hand sides are `clamp`-canonical (`nary_canon` output);
* `hfix`: the last round changed nothing;
* `hlaw`: every law instance removes children, so shrinks in degree-lex;
* `hnf_ax`: `clamp` outputs are normal for the law instances (`nary_canon`
  is a normal-form function);
* `hcp`: every critical pair of two distinct overlapping rules of
  `R ∪ Ax` is joinable (the (B) close plus the axiom pairs, Kapur
  Lemmas 5-9);
* `hcc`: congruent active nodes are in one class (plain congruence closure);
* `hS`: every asserted equation is a pair of active nodes in one class
  (what `merge` establishes);
* `hcancel`: for a cancellative operator, joinability cancels a common
  summand (outside the paper's theorem unless the operator is not
  cancellative, where it is vacuous). -/
theorem completion_complete_at_convergence' {L : Laws n}
    {S : Set (Monomial n × Monomial n)} {st : State n}
    {ss₀ ss : SlotState n}
    (h5₀ : SlotState.I5 ss₀) (hrun : SlotState.OpsStar ss₀ ss) (ha : SlotState.Agrees st ss)
    (h0 : I0Active st) (hcanon : ∀ c, L.clamp (st.rhs c) = st.rhs c) (hfix : RoundFixed L st)
    (hlaw : ∀ P Q, L.lawRel P Q → degLex P Q)
    (hnf_ax : ∀ M N, ¬ Rw (plain n) L.axRules (L.clamp M) N)
    (hcp : ∀ r₁ r₂, r₁ ∈ st.rules ∪ L.axRules → r₂ ∈ st.rules ∪ L.axRules → r₁ ≠ r₂ →
      Overlap r₁.1 r₂.1 →
      Joinable (Rw (plain n) (st.rules ∪ L.axRules))
        (criticalPair (plain n) r₁ r₂).1 (criticalPair (plain n) r₁ r₂).2)
    (hcc : ∀ P c d, (P, c) ∈ st.active → (P, d) ∈ st.active → st.find c = st.find d)
    (hS : ∀ M N, (M, N) ∈ S →
      ∃ c d, (M, c) ∈ st.active ∧ (N, d) ∈ st.active ∧ st.find c = st.find d)
    (hcancel : L.cancellative → ∀ M N X,
      Joinable (Rw (plain n) (st.rules ∪ L.axRules)) (M + X) (N + X) →
      Joinable (Rw (plain n) (st.rules ∪ L.axRules)) M N)
    {M N : Monomial n} {c d : Fin n} (hM : (M, c) ∈ st.active) (hN : (N, d) ∈ st.active)
    (hMN : E L S M N) : st.find c = st.find d := by
  have h5 : I5 st := SlotState.state_I5_of_slot (SlotState.reachable_I5 h5₀ hrun) ha
  have hor : Oriented st.rules := rules_oriented st
  have hconv : Converged L st := roundFixed_converged (I0On_of_active h0) h5 hcanon hfix
  have hconf : Confluent (RwAx L st.rules) := RwAx_confluent L st.rules hor hlaw hcp
  obtain ⟨P, hMP, hNP⟩ := E_joinable_RwAx hconv hconf hS hcancel hMN
  -- the right-hand sides of the two classes are normal for `RwAx`
  have pn : ∀ {K e}, (K, e) ∈ st.active → ∀ Q, ¬ RwAx L st.rules (st.rhs (st.find e)) Q :=
    fun {_ e} hK => plain_normal_of_normal hnf_ax ⟨st.rhs (st.find e), (hcanon (st.find e)).symm⟩
      (rhs_normal h0 h5 hfix hK)
  have hMr : ReflTransGen (RwAx L st.rules) M (st.rhs (st.find c)) :=
    Rw_rtg_embed (hconv.nodes_reduce M c hM)
  have hNr : ReflTransGen (RwAx L st.rules) N (st.rhs (st.find d)) :=
    Rw_rtg_embed (hconv.nodes_reduce N d hN)
  obtain ⟨Q, hrQ, hPQ⟩ := hconf _ _ _ hMr hMP
  have e₁ := rtg_of_normal (pn hM) hrQ
  obtain ⟨T, hrT, hPT⟩ := hconf _ _ _ hNr hNP
  have e₂ := rtg_of_normal (pn hN) hrT
  obtain ⟨U, hQU, hTU⟩ := hconf _ _ _ hPQ hPT
  rw [← e₁] at hQU
  rw [← e₂] at hTU
  have f₁ := rtg_of_normal (pn hM) hQU
  have f₂ := rtg_of_normal (pn hN) hTU
  obtain ⟨c', hc', hcc'⟩ := h0 M c hM
  obtain ⟨d', hd', hdd'⟩ := h0 N d hN
  have := hcc _ c' d' hc' (by rw [f₁, ← f₂]; exact hd')
  rw [hcc', hdd'] at this
  exact this

end SemperProofs.CC
