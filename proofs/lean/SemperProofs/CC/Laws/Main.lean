import SemperProofs.CC.Laws.CriticalPairs

/-!
# Completeness at convergence for the concrete law sets

Instantiations of `completion_complete_at_convergence` with the laws the
engine implements. `hlaw` and `hnf_ax` are discharged by the law; `hcp`
is reduced to the rule-rule critical pairs plus the law-specific
rule-side hypothesis of `CriticalPairs.lean`.
-/

namespace SemperProofs.CC

open Relation

variable {n : ℕ}

/-- Completeness at convergence for an AC operator with an identity `u`.
Beyond the engine-level hypotheses of `completion_complete_at_convergence`
(slot maintenance, canonical and active right-hand sides, a round that
changed nothing, congruence closure, the asserted equations present), the
law contributes: rule-rule critical pairs joinable (`hRR`) and no rule
left side carries the unit (`hu`). -/
theorem completion_complete_identity (u : Fin n) (cancel : Prop)
    {S : Set (Monomial n × Monomial n)} {st : State n} {ss₀ ss : SlotState n}
    (h5₀ : SlotState.I5 ss₀) (hrun : SlotState.OpsStar ss₀ ss) (ha : SlotState.Agrees st ss)
    (h0 : I0Active st) (hcanon : ∀ c, (Laws.identity u cancel).clamp (st.rhs c) = st.rhs c)
    (hfix : RoundFixed (Laws.identity u cancel) st)
    (hRR : RuleRuleCP (Laws.identity u cancel) st.rules)
    (hu : ∀ A B, (A, B) ∈ st.rules → u ∉ A)
    (hcc : ∀ P c d, (P, c) ∈ st.active → (P, d) ∈ st.active → st.find c = st.find d)
    (hS : ∀ M N, (M, N) ∈ S →
      ∃ c d, (M, c) ∈ st.active ∧ (N, d) ∈ st.active ∧ st.find c = st.find d)
    (hcancel : cancel → ∀ M N X,
      Joinable (Rw (plain n) (st.rules ∪ (Laws.identity u cancel).axRules)) (M + X) (N + X) →
      Joinable (Rw (plain n) (st.rules ∪ (Laws.identity u cancel).axRules)) M N)
    {M N : Monomial n} {c d : Fin n} (hM : (M, c) ∈ st.active) (hN : (N, d) ∈ st.active)
    (hMN : E (Laws.identity u cancel) S M N) : st.find c = st.find d :=
  completion_complete_at_convergence h5₀ hrun ha h0 hcanon hfix (identity_hlaw u cancel)
    (identity_hnf_ax u cancel) (hcp_identity u cancel (rules_oriented st) hRR hu) hcc hS hcancel
    hM hN hMN

/-- Completeness at convergence for a nilpotent AC operator of order `k`
(`xᵏ = e`; the engine's `:nilpotent k`, counts reduced mod `k`). The law
contributes: rule-rule pairs joinable (`hRR`), left sides with counts
below `k` (`hfix`, what `nary_canon` stores), and the engine's axiom
critical pairs `(B ⊎ {a : k − m}, A − {a : m})` joinable (`hax`,
`egraph.rs:3047-3066`). -/
theorem completion_complete_nilpotent (k : ℕ) (hk : 2 ≤ k) (cancel : Prop)
    {S : Set (Monomial n × Monomial n)} {st : State n} {ss₀ ss : SlotState n}
    (h5₀ : SlotState.I5 ss₀) (hrun : SlotState.OpsStar ss₀ ss) (ha : SlotState.Agrees st ss)
    (h0 : I0Active st) (hcanon : ∀ c, (Laws.nilpotent k hk cancel).clamp (st.rhs c) = st.rhs c)
    (hfix : RoundFixed (Laws.nilpotent k hk cancel) st)
    (hRR : RuleRuleCP (Laws.nilpotent k hk cancel) st.rules)
    (hlhs : ∀ A B, (A, B) ∈ st.rules → ∀ a, A.count a < k)
    (hax : ∀ A B, (A, B) ∈ st.rules → ∀ a ∈ A,
      Joinable (Rw (plain n) (st.rules ∪ (Laws.nilpotent k hk cancel).axRules))
        (B + Multiset.replicate (k - A.count a) a) (A.filter (· ≠ a)))
    (hcc : ∀ P c d, (P, c) ∈ st.active → (P, d) ∈ st.active → st.find c = st.find d)
    (hS : ∀ M N, (M, N) ∈ S →
      ∃ c d, (M, c) ∈ st.active ∧ (N, d) ∈ st.active ∧ st.find c = st.find d)
    (hcancel : cancel → ∀ M N X,
      Joinable (Rw (plain n) (st.rules ∪ (Laws.nilpotent k hk cancel).axRules)) (M + X) (N + X) →
      Joinable (Rw (plain n) (st.rules ∪ (Laws.nilpotent k hk cancel).axRules)) M N)
    {M N : Monomial n} {c d : Fin n} (hM : (M, c) ∈ st.active) (hN : (N, d) ∈ st.active)
    (hMN : E (Laws.nilpotent k hk cancel) S M N) : st.find c = st.find d :=
  completion_complete_at_convergence h5₀ hrun ha h0 hcanon hfix nilpotent_hlaw nilpotent_hnf_ax
    (hcp_nilpotent k hk cancel (rules_oriented st) hRR hlhs hax) hcc hS hcancel hM hN hMN

/-- Completeness at convergence for an ACI operator (`x ∘ x = x`; the
engine's `Set` partition, dedup). The law contributes: rule-rule pairs
joinable (`hRR`), left sides without duplicates (`hlhs`), and the axiom
critical pairs `(B ⊎ {a}, A)` joinable (`hax`; implied by the engine's
`(dedup(B ⊎ {a}), B)`, `egraph.rs:3035-3046`, see `idempotent_engine_pair`). -/
theorem completion_complete_idempotent (cancel : Prop)
    {S : Set (Monomial n × Monomial n)} {st : State n} {ss₀ ss : SlotState n}
    (h5₀ : SlotState.I5 ss₀) (hrun : SlotState.OpsStar ss₀ ss) (ha : SlotState.Agrees st ss)
    (h0 : I0Active st) (hcanon : ∀ c, (Laws.idempotent cancel).clamp (st.rhs c) = st.rhs c)
    (hfix : RoundFixed (Laws.idempotent cancel) st)
    (hRR : RuleRuleCP (Laws.idempotent cancel) st.rules)
    (hlhs : ∀ A B, (A, B) ∈ st.rules → A.Nodup)
    (hax : ∀ A B, (A, B) ∈ st.rules → ∀ a ∈ A,
      Joinable (Rw (plain n) (st.rules ∪ (Laws.idempotent cancel).axRules)) (B + {a}) A)
    (hcc : ∀ P c d, (P, c) ∈ st.active → (P, d) ∈ st.active → st.find c = st.find d)
    (hS : ∀ M N, (M, N) ∈ S →
      ∃ c d, (M, c) ∈ st.active ∧ (N, d) ∈ st.active ∧ st.find c = st.find d)
    (hcancel : cancel → ∀ M N X,
      Joinable (Rw (plain n) (st.rules ∪ (Laws.idempotent cancel).axRules)) (M + X) (N + X) →
      Joinable (Rw (plain n) (st.rules ∪ (Laws.idempotent cancel).axRules)) M N)
    {M N : Monomial n} {c d : Fin n} (hM : (M, c) ∈ st.active) (hN : (N, d) ∈ st.active)
    (hMN : E (Laws.idempotent cancel) S M N) : st.find c = st.find d :=
  completion_complete_at_convergence h5₀ hrun ha h0 hcanon hfix idempotent_hlaw idempotent_hnf_ax
    (hcp_idempotent cancel (rules_oriented st) hRR hlhs hax) hcc hS hcancel hM hN hMN

/-- Completeness at convergence for an AC operator with an inverse
(`x ∘ inv x = e`, pair cancellation only). The law contributes: rule-rule
pairs joinable (`hRR`), the inverse graph a matching (`hmatch`), left sides
cancellation-normal (`hlhs`), and the inverse axiom critical pairs
`(B ⊎ {y}, A ∖ x)` joinable (`hax`). The engine generates neither the
law-law nor the rule-law inverse pairs (`egraph.rs:3068`); `hmatch` and
`hax` are therefore conditions on the input, not facts of the engine. -/
theorem completion_complete_inverse (inv : Fin n → Option (Fin n)) (cancel : Prop)
    {S : Set (Monomial n × Monomial n)} {st : State n} {ss₀ ss : SlotState n}
    (h5₀ : SlotState.I5 ss₀) (hrun : SlotState.OpsStar ss₀ ss) (ha : SlotState.Agrees st ss)
    (h0 : I0Active st) (hcanon : ∀ c, (Laws.inverse inv cancel).clamp (st.rhs c) = st.rhs c)
    (hfix : RoundFixed (Laws.inverse inv cancel) st)
    (hRR : RuleRuleCP (Laws.inverse inv cancel) st.rules)
    (hmatch : InvMatching inv)
    (hlhs : ∀ A B, (A, B) ∈ st.rules → InvNormal inv A)
    (hax : InverseAxiomCP (Laws.inverse inv cancel) inv st.rules)
    (hcc : ∀ P c d, (P, c) ∈ st.active → (P, d) ∈ st.active → st.find c = st.find d)
    (hS : ∀ M N, (M, N) ∈ S →
      ∃ c d, (M, c) ∈ st.active ∧ (N, d) ∈ st.active ∧ st.find c = st.find d)
    (hcancel : cancel → ∀ M N X,
      Joinable (Rw (plain n) (st.rules ∪ (Laws.inverse inv cancel).axRules)) (M + X) (N + X) →
      Joinable (Rw (plain n) (st.rules ∪ (Laws.inverse inv cancel).axRules)) M N)
    {M N : Monomial n} {c d : Fin n} (hM : (M, c) ∈ st.active) (hN : (N, d) ∈ st.active)
    (hMN : E (Laws.inverse inv cancel) S M N) : st.find c = st.find d :=
  completion_complete_at_convergence h5₀ hrun ha h0 hcanon hfix (inverse_hlaw inv cancel)
    (inverse_hnf_ax inv cancel)
    (hcp_inverse inv cancel (rules_oriented st) hRR hmatch hlhs hax) hcc hS hcancel hM hN hMN

/-- Completeness at convergence for the engine's composition identity,
nilpotent, inverse (`nary_canon.rs:122-137`), under `InvUnitFree` (the
unit is isolated in the inverse graph; otherwise the clamp is not a
normal form of the pooled laws, `combined_counterexample`). The law
contributes the hypotheses of `hcp_combined`. -/
theorem completion_complete_combined (u : Fin n) (k : ℕ) (hk : 2 ≤ k)
    (inv : Fin n → Option (Fin n)) (cancel : Prop) (hu : InvUnitFree inv u)
    {S : Set (Monomial n × Monomial n)} {st : State n} {ss₀ ss : SlotState n}
    (h5₀ : SlotState.I5 ss₀) (hrun : SlotState.OpsStar ss₀ ss) (ha : SlotState.Agrees st ss)
    (h0 : I0Active st)
    (hcanon : ∀ c, (Laws.combined u k hk inv cancel hu).clamp (st.rhs c) = st.rhs c)
    (hfix : RoundFixed (Laws.combined u k hk inv cancel hu) st)
    (hRR : RuleRuleCP (Laws.combined u k hk inv cancel hu) st.rules)
    (hmatch : InvMatching inv)
    (hlhs_u : ∀ A B, (A, B) ∈ st.rules → u ∉ A)
    (hlhs_k : ∀ A B, (A, B) ∈ st.rules → ∀ a, A.count a < k)
    (hlhs_inv : ∀ A B, (A, B) ∈ st.rules → InvNormal inv A)
    (hax_nil : ∀ A B, (A, B) ∈ st.rules → ∀ a ∈ A,
      Joinable (Rw (plain n) (st.rules ∪ (Laws.combined u k hk inv cancel hu).axRules))
        (B + Multiset.replicate (k - A.count a) a) (A.filter (· ≠ a)))
    (hax_inv : InverseAxiomCP (Laws.combined u k hk inv cancel hu) inv st.rules)
    (hnilinv : NilpotentInverseCP (st.rules ∪ (Laws.combined u k hk inv cancel hu).axRules) k inv)
    (hcc : ∀ P c d, (P, c) ∈ st.active → (P, d) ∈ st.active → st.find c = st.find d)
    (hS : ∀ M N, (M, N) ∈ S →
      ∃ c d, (M, c) ∈ st.active ∧ (N, d) ∈ st.active ∧ st.find c = st.find d)
    (hcancel : (Laws.combined u k hk inv cancel hu).cancellative → ∀ M N X,
      Joinable (Rw (plain n) (st.rules ∪ (Laws.combined u k hk inv cancel hu).axRules))
        (M + X) (N + X) →
      Joinable (Rw (plain n) (st.rules ∪ (Laws.combined u k hk inv cancel hu).axRules)) M N)
    {M N : Monomial n} {c d : Fin n} (hM : (M, c) ∈ st.active) (hN : (N, d) ∈ st.active)
    (hMN : E (Laws.combined u k hk inv cancel hu) S M N) : st.find c = st.find d :=
  completion_complete_at_convergence h5₀ hrun ha h0 hcanon hfix
    (combined_hlaw u k hk inv cancel hu) (combined_hnf_ax u k hk inv cancel hu)
    (hcp_combined u k hk inv cancel hu (rules_oriented st) hRR hmatch hlhs_u hlhs_k hlhs_inv
      hax_nil hax_inv hnilinv) hcc hS hcancel hM hN hMN

end SemperProofs.CC
