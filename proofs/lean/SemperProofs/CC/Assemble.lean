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

/-- The rule set of a state is oriented by definition (`State.rules` folds
`degLex` in; the engine's read-time guard). -/
theorem rules_oriented (st : State n) : Oriented st.rules :=
  fun _ _ ⟨_, _, _, _, h, _, _⟩ => h

/-- I0 strengthened: every class's right-hand side is an *active* node of
that class. The engine's slot names an active node: `refresh_min_monomial`
considers active nodes only and retirement requires a smaller active
classmate. -/
def I0Active (st : State n) : Prop :=
  ∀ c, ∃ c', (st.rhs (st.find c), c') ∈ st.active ∧ st.find c' = st.find c

theorem I0_of_active {st : State n} (h : I0Active st) : I0 st :=
  fun c => let ⟨c', h₁, h₂⟩ := h c; ⟨c', h₁.1, h₂⟩

/-- Right-hand sides are normal forms of the rules, derived: a step from
`rhs c` lands strictly below it in degree-lex, its normal form is an active
classmate by `nf_present`, and I5 puts no active classmate strictly below
`rhs c`. -/
theorem rhs_normal {L : Laws n} {st : State n} (h0 : I0Active st) (h5 : I5 st)
    (hfix : RoundFixed L st) (c : Fin n) (P : Monomial n) :
    ¬ Rw L st.rules (st.rhs (st.find c)) P := by
  intro hP
  obtain ⟨c', hc', hcc'⟩ := h0 c
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
* `h0`: every class's right-hand side is one of its own active nodes;
* `hcanon`: right-hand sides are `clamp`-canonical (`nary_canon` output);
* `hfix`: the last round changed nothing;
* `hlaw`: every law instance removes children, so shrinks in degree-lex;
* `hnf_ax`: `clamp` outputs are normal for the law instances (`nary_canon`
  is a normal-form function);
* `hcp`: every critical pair of two distinct overlapping rules of
  `R ∪ Ax` is joinable (the (B) close plus the axiom pairs, Kapur
  Lemmas 5-9);
* `hcc`: congruent nodes are in one class (plain congruence closure);
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
    (hcc : ∀ P c d, (P, c) ∈ st.nodes → (P, d) ∈ st.nodes → st.find c = st.find d)
    (hS : ∀ M N, (M, N) ∈ S →
      ∃ c d, (M, c) ∈ st.active ∧ (N, d) ∈ st.active ∧ st.find c = st.find d)
    (hcancel : L.cancellative → ∀ M N X,
      Joinable (Rw (plain n) (st.rules ∪ L.axRules)) (M + X) (N + X) →
      Joinable (Rw (plain n) (st.rules ∪ L.axRules)) M N)
    {M N : Monomial n} {c d : Fin n} (hM : (M, c) ∈ st.active) (hN : (N, d) ∈ st.active)
    (hMN : E L S M N) : st.find c = st.find d := by
  have h5 : I5 st := SlotState.state_I5_of_slot (SlotState.reachable_I5 h5₀ hrun) ha
  have hor : Oriented st.rules := rules_oriented st
  have hnf : ∀ c P, ¬ Rw L st.rules (st.rhs (st.find c)) P := rhs_normal h0 h5 hfix
  have hconv : Converged L st := roundFixed_converged (I0_of_active h0) h5 hcanon hfix
  have hconf : Confluent (RwAx L st.rules) := RwAx_confluent L st.rules hor hlaw hcp
  obtain ⟨P, hMP, hNP⟩ := E_joinable_RwAx hconv hconf hS hcancel hMN
  -- the right-hand sides are normal for `RwAx`
  have pn : ∀ e, ∀ Q, ¬ RwAx L st.rules (st.rhs (st.find e)) Q := fun e =>
    plain_normal_of_normal hnf_ax ⟨st.rhs (st.find e), (hcanon (st.find e)).symm⟩ (hnf e)
  have hMr : ReflTransGen (RwAx L st.rules) M (st.rhs (st.find c)) :=
    Rw_rtg_embed (hconv.nodes_reduce M c hM)
  have hNr : ReflTransGen (RwAx L st.rules) N (st.rhs (st.find d)) :=
    Rw_rtg_embed (hconv.nodes_reduce N d hN)
  obtain ⟨Q, hrQ, hPQ⟩ := hconf _ _ _ hMr hMP
  have e₁ := rtg_of_normal (pn c) hrQ
  obtain ⟨T, hrT, hPT⟩ := hconf _ _ _ hNr hNP
  have e₂ := rtg_of_normal (pn d) hrT
  obtain ⟨U, hQU, hTU⟩ := hconf _ _ _ hPQ hPT
  rw [← e₁] at hQU
  rw [← e₂] at hTU
  have f₁ := rtg_of_normal (pn c) hQU
  have f₂ := rtg_of_normal (pn d) hTU
  obtain ⟨c', hc', hcc'⟩ := I0_of_active h0 c
  obtain ⟨d', hd', hdd'⟩ := I0_of_active h0 d
  have := hcc _ c' d' hc' (by rw [f₁, ← f₂]; exact hd')
  rw [hcc', hdd'] at this
  exact this

end SemperProofs.CC
