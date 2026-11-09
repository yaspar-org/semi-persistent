import SemperProofs.CC.Laws.Identity
import SemperProofs.CC.Laws.Nilpotent
import SemperProofs.CC.Laws.Idempotent
import SemperProofs.CC.Laws.Inverse
import SemperProofs.CC.Laws.Combined

/-!
# Critical pairs of the concrete law sets

For a normal-form law set `N`, `NFLaw.hcp_of_gen` reduces the critical
pairs of `R ∪ Ax` (infinitely many law instances) to those of `R ∪ gen`.
This file characterizes the overlaps of a completion rule with a
generator and of two generators, law by law, and states the rule-side
hypothesis under which every such pair is joinable. The rule-rule pairs
enter as the hypothesis `hRR`; `Main.lean` discharges it from the fixed
round (`ruleRuleCP_of_fixed`: the (B) close of completion and the
reducibility pass).

Throughout, joinability is under plain rewriting by `R ∪ L.axRules`, the
relation of `completion_complete_at_convergence`'s `hcp`.
-/

namespace SemperProofs.CC

open Relation

variable {n : ℕ}

/-- The rule-rule critical-pair hypothesis, in the relation of the final theorem. -/
def RuleRuleCP (L : Laws n) (R : Rules n) : Prop :=
  ∀ r₁ r₂, r₁ ∈ R → r₂ ∈ R → r₁ ≠ r₂ → Overlap r₁.1 r₂.1 →
    Joinable (Rw (plain n) (R ∪ L.axRules))
      (criticalPair (plain n) r₁ r₂).1 (criticalPair (plain n) r₁ r₂).2

/-- The `hcp` hypothesis of `completion_complete_at_convergence`. -/
def HCP (L : Laws n) (R : Rules n) : Prop :=
  ∀ r₁ r₂, r₁ ∈ R ∪ L.axRules → r₂ ∈ R ∪ L.axRules → r₁ ≠ r₂ → Overlap r₁.1 r₂.1 →
    Joinable (Rw (plain n) (R ∪ L.axRules))
      (criticalPair (plain n) r₁ r₂).1 (criticalPair (plain n) r₁ r₂).2

/-! ## Identity: no rule-law pair when left sides carry no unit -/

/-- `hcp` for the identity law. Hypotheses: the rule-rule pairs are joinable
and no left side carries the unit class (stored monomials never do:
`nary_canon.rs:122-124`). Rule-law and law-law pairs do not exist. -/
theorem hcp_identity (u : Fin n) (cancel : Prop) {R : Rules n} (hor : Oriented R)
    (hRR : RuleRuleCP (Laws.identity u cancel) R)
    (hu : ∀ A B, (A, B) ∈ R → u ∉ A) :
    HCP (Laws.identity u cancel) R := by
  apply (identityNF u cancel).hcp_of_gen hor
  refine hcp_split ((identityNF u cancel).hcp_rules_gen_of_ax hRR) ?_ ?_
  · rintro ⟨A, B⟩ r₂ h₁ h₂ _ hov
    rw [identityNF_gen_iff] at h₂
    subst h₂
    exact absurd ((overlap_unitGen_iff A).mp hov) (hu A B h₁)
  · intro r₁ r₂ h₁ h₂ hne _
    exact absurd (unitGen_gen_gen h₁ h₂) hne

/-! ## Count-threshold laws (nilpotent, idempotent): the axiom critical pairs -/

/-- `hcp` for a count-threshold law `C` from the rule-rule pairs, left sides
with counts below the threshold, and the axiom critical pairs
`(B + a^(p − count a A), A∖a + a^q)` for every `a ∈ A` (`CountMap.cp_rule_gen`). -/
theorem hcp_countMap (C : CountMap) (cancel : Prop) {R : Rules n} (hor : Oriented R)
    (hRR : RuleRuleCP (C.toNF cancel).toLaws R)
    (hfix : ∀ A B, (A, B) ∈ R → C.Fixed A)
    (hax : ∀ A B, (A, B) ∈ R → ∀ a ∈ A,
      Joinable (Rw (plain n) (R ∪ (C.toNF (n := n) cancel).toLaws.axRules))
        (B + Multiset.replicate (C.p - A.count a) a)
        (A.filter (· ≠ a) + Multiset.replicate C.q a)) :
    HCP (C.toNF cancel).toLaws R := by
  apply (C.toNF cancel).hcp_of_gen hor
  refine hcp_split ((C.toNF cancel).hcp_rules_gen_of_ax hRR) ?_ ?_
  · rintro ⟨A, B⟩ r₂ h₁ h₂ _ hov
    obtain ⟨a, rfl⟩ := h₂
    have ha : a ∈ A := (C.overlap_gen_iff A a).mp hov
    rw [C.cp_rule_gen (hfix A B h₁) ha]
    exact ((C.toNF cancel).joinable_iff _ _).mp (hax A B h₁ a ha)
  · intro r₁ r₂ h₁ h₂ hne hov
    exact absurd (C.gen_gen h₁ h₂ hov) hne

/-- `hcp` for the nilpotent law of order `k`. Beyond the rule-rule pairs:
every left side has counts below `k`, and for every rule `A → B` and
`a ∈ A` with count `m`, the engine's axiom critical pair
`(B ⊎ {a : k − m}, A − {a : m})` (`egraph.rs:3047-3066`) is joinable. -/
theorem hcp_nilpotent (k : ℕ) (hk : 2 ≤ k) (cancel : Prop) {R : Rules n} (hor : Oriented R)
    (hRR : RuleRuleCP (Laws.nilpotent k hk cancel) R)
    (hfix : ∀ A B, (A, B) ∈ R → ∀ a, A.count a < k)
    (hax : ∀ A B, (A, B) ∈ R → ∀ a ∈ A,
      Joinable (Rw (plain n) (R ∪ (Laws.nilpotent k hk cancel).axRules))
        (B + Multiset.replicate (k - A.count a) a) (A.filter (· ≠ a))) :
    HCP (Laws.nilpotent k hk cancel) R := by
  refine hcp_countMap (nilpotentMap k hk) cancel hor hRR hfix ?_
  intro A B h a ha
  have := hax A B h a ha
  simp only [nilpotentMap, Multiset.replicate_zero, add_zero]
  exact this

/-- `hcp` for the idempotent law. Beyond the rule-rule pairs: left sides
are sets, and for every rule `A → B` and `a ∈ A` the pair `(B ⊎ {a}, A)` is
joinable; the engine closes `(dedup(B ⊎ {a}), B)` (`egraph.rs:3035-3046`),
which implies it (`A → B` and `B ⊎ {a} → dedup(B ⊎ {a})`). -/
theorem hcp_idempotent (cancel : Prop) {R : Rules n} (hor : Oriented R)
    (hRR : RuleRuleCP (Laws.idempotent cancel) R)
    (hfix : ∀ A B, (A, B) ∈ R → A.Nodup)
    (hax : ∀ A B, (A, B) ∈ R → ∀ a ∈ A,
      Joinable (Rw (plain n) (R ∪ (Laws.idempotent cancel).axRules)) (B + {a}) A) :
    HCP (Laws.idempotent cancel) R := by
  refine hcp_countMap idempotentMap cancel hor hRR ?_ ?_
  · intro A B h a
    exact lt_of_le_of_lt ((Multiset.nodup_iff_count_le_one.mp (hfix A B h)) a) (by decide)
  · intro A B h a ha
    have h1 : (idempotentMap.p - A.count a) = 1 := by
      have := (Multiset.nodup_iff_count_le_one.mp (hfix A B h)) a
      have := Multiset.count_pos.mpr ha
      show 2 - A.count a = 1
      omega
    have h2 : A.filter (· ≠ a) + Multiset.replicate idempotentMap.q a = A := by
      show A.filter (· ≠ a) + Multiset.replicate 1 a = A
      ext b
      rw [Multiset.count_add, Multiset.count_filter, Multiset.count_replicate]
      by_cases hb : b = a
      · subst hb
        have := (Multiset.nodup_iff_count_le_one.mp (hfix A B h)) b
        have := Multiset.count_pos.mpr ha
        simp; omega
      · simp [hb, Ne.symm hb]
    rw [h1, h2, Multiset.replicate_one]
    exact hax A B h a ha

/-- The engine's idempotent axiom pair implies the one used above. -/
theorem idempotent_engine_pair {L : Laws n} {R : Rules n} {A B : Monomial n} {a : Fin n}
    (hAB : (A, B) ∈ R)
    (h : Joinable (Rw (plain n) (R ∪ L.axRules)) ((B + {a}).dedup) B)
    (hdedup : ∀ M, M.dedup = M ∨ L.lawRel M M.dedup) :
    Joinable (Rw (plain n) (R ∪ L.axRules)) (B + {a}) A := by
  obtain ⟨W, h₁, h₂⟩ := h
  have hA : Rw (plain n) (R ∪ L.axRules) A B :=
    ⟨A, B, Or.inl hAB, le_rfl, by rw [plain_clamp, tsub_self, zero_add]⟩
  refine ⟨W, ?_, ReflTransGen.head hA h₂⟩
  rcases hdedup (B + {a}) with e | e
  · rw [← e]; exact h₁
  · exact ReflTransGen.head ⟨_, _, Or.inr e, le_rfl, by rw [plain_clamp, tsub_self, zero_add]; rfl⟩ h₁

/-! ## Inverse: pair cancellation -/

/-- The rule-law critical pairs of the inverse law: for a rule `A → B`
and a generator `{x, y} → ∅` (`inv x = y`) sharing `x`, the pair
`(B ⊎ {y}, A ∖ x)`; sharing `y` only, `(B ⊎ {x}, A ∖ y)`. The engine
generates neither (`egraph.rs:3068`, `CompletionClamp::Multiset`). -/
def InverseAxiomCP (L : Laws n) (inv : Fin n → Option (Fin n)) (R : Rules n) : Prop :=
  ∀ A B, (A, B) ∈ R → ∀ x y, inv x = some y →
    (x ∈ A → Joinable (Rw (plain n) (R ∪ L.axRules)) (B + {y}) (A.erase x)) ∧
    (x ≠ y → y ∈ A → Joinable (Rw (plain n) (R ∪ L.axRules)) (B + {x}) (A.erase y))

/-- `hcp` for the inverse law. Hypotheses: rule-rule pairs joinable, the
inverse graph a matching (`hmatch`; without it two generators overlap
and the pair is not joinable, `invGen_cp_not_joinable`), left sides
cancellation-normal (`hfix`), and the rule-law pairs joinable (`hax`). -/
theorem hcp_inverse (inv : Fin n → Option (Fin n)) (cancel : Prop) {R : Rules n}
    (hor : Oriented R)
    (hRR : RuleRuleCP (Laws.inverse inv cancel) R)
    (hmatch : InvMatching inv)
    (hfix : ∀ A B, (A, B) ∈ R → InvNormal inv A)
    (hax : InverseAxiomCP (Laws.inverse inv cancel) inv R) :
    HCP (Laws.inverse inv cancel) R := by
  apply (inverseNF inv cancel).hcp_of_gen hor
  refine hcp_split ((inverseNF inv cancel).hcp_rules_gen_of_ax hRR) ?_ ?_
  · rintro ⟨A, B⟩ r₂ h₁ h₂ _ hov
    obtain ⟨x, y, hxy, rfl⟩ := h₂
    rcases (overlap_pair_iff A x y).mp hov with hx | hy
    · rw [cp_rule_invGen_left (hfix A B h₁) hxy hx]
      exact ((inverseNF inv cancel).joinable_iff _ _).mp ((hax A B h₁ x y hxy).1 hx)
    · by_cases hx : x ∈ A
      · rw [cp_rule_invGen_left (hfix A B h₁) hxy hx]
        exact ((inverseNF inv cancel).joinable_iff _ _).mp ((hax A B h₁ x y hxy).1 hx)
      · have hne : x ≠ y := fun h => hx (h ▸ hy)
        rw [cp_rule_invGen_right (hfix A B h₁) hxy hne hy]
        exact ((inverseNF inv cancel).joinable_iff _ _).mp ((hax A B h₁ x y hxy).2 hne hy)
  · intro r₁ r₂ h₁ h₂ hne hov
    exact absurd (invGen_gen_gen hmatch h₁ h₂ hov) hne

/-! ## The composition: cross-law pairs -/

/-- The law-law critical pairs between the nilpotent and the inverse
generators, which the engine does not generate: `aᵏ → ∅` against
`{x, y} → ∅` (`inv x = y`) overlapping in `x` gives `({y}, x^(k−1))`, in
`y` gives `({x}, y^(k−1))`; for a self-inverse `x` and `k > 2`,
`(∅, x^(k−2))`. For `k = 2` with a self-inverse class the two generators
coincide. -/
def NilpotentInverseCP (S : Rules n) (k : ℕ) (inv : Fin n → Option (Fin n)) : Prop :=
  ∀ x y, inv x = some y →
    (x ≠ y → Joinable (Rw (plain n) S) {y} (Multiset.replicate (k - 1) x) ∧
      Joinable (Rw (plain n) S) {x} (Multiset.replicate (k - 1) y)) ∧
    (x = y → 2 < k → Joinable (Rw (plain n) S) 0 (Multiset.replicate (k - 2) x))

theorem cp_unit_nil (u : Fin n) (k : ℕ) (hk : 1 ≤ k) :
    criticalPair (plain n) (({u} : Monomial n), 0) (Multiset.replicate k u, 0) =
      (Multiset.replicate (k - 1) u, 0) := by
  refine Prod.ext (Multiset.ext.mpr fun z => ?_) (Multiset.ext.mpr fun z => ?_) <;>
    simp only [criticalPair, plain_clamp, Multiset.count_add, Multiset.count_sub,
      Multiset.count_union, Multiset.count_replicate, Multiset.count_zero,
      Multiset.count_singleton] <;> split_ifs <;> omega

theorem cp_unit_inv (u : Fin n) :
    criticalPair (plain n) (({u} : Monomial n), 0) (({u, u} : Monomial n), 0) = ({u}, 0) := by
  refine Prod.ext (Multiset.ext.mpr fun z => ?_) (Multiset.ext.mpr fun z => ?_) <;>
    simp only [criticalPair, plain_clamp, Multiset.count_add, Multiset.count_sub,
      Multiset.count_union, count_pair, Multiset.count_zero,
      Multiset.count_singleton] <;> split_ifs <;> omega

theorem cp_nil_inv_left (k : ℕ) (hk : 1 ≤ k) {x y : Fin n} (hne : x ≠ y) :
    criticalPair (plain n) (Multiset.replicate k x, 0) (({x, y} : Monomial n), 0) =
      ({y}, Multiset.replicate (k - 1) x) := by
  refine Prod.ext (Multiset.ext.mpr fun z => ?_) (Multiset.ext.mpr fun z => ?_) <;>
    simp only [criticalPair, plain_clamp, Multiset.count_add, Multiset.count_sub,
      Multiset.count_union, count_pair, Multiset.count_zero, Multiset.count_replicate,
      Multiset.count_singleton] <;> split_ifs <;> omega

theorem cp_nil_inv_right (k : ℕ) (hk : 1 ≤ k) {x y : Fin n} (hne : x ≠ y) :
    criticalPair (plain n) (Multiset.replicate k y, 0) (({x, y} : Monomial n), 0) =
      ({x}, Multiset.replicate (k - 1) y) := by
  refine Prod.ext (Multiset.ext.mpr fun z => ?_) (Multiset.ext.mpr fun z => ?_) <;>
    simp only [criticalPair, plain_clamp, Multiset.count_add, Multiset.count_sub,
      Multiset.count_union, count_pair, Multiset.count_zero, Multiset.count_replicate,
      Multiset.count_singleton] <;> split_ifs <;> omega

theorem cp_nil_inv_self (k : ℕ) (hk : 2 ≤ k) (x : Fin n) :
    criticalPair (plain n) (Multiset.replicate k x, 0) (({x, x} : Monomial n), 0) =
      (0, Multiset.replicate (k - 2) x) := by
  refine Prod.ext (Multiset.ext.mpr fun z => ?_) (Multiset.ext.mpr fun z => ?_) <;>
    simp only [criticalPair, plain_clamp, Multiset.count_add, Multiset.count_sub,
      Multiset.count_union, count_pair, Multiset.count_zero, Multiset.count_replicate] <;> split_ifs <;> omega

theorem pair_self_eq_replicate (x : Fin n) : ({x, x} : Monomial n) = Multiset.replicate 2 x := by
  simp [Multiset.replicate_succ]

/-- `hcp` for the engine's composition identity-nilpotent-inverse. Beyond
the rule-rule pairs: the inverse graph is a matching, left sides are
canonical (no unit, counts below `k`, cancellation-normal), the nilpotent
axiom pairs (which the engine generates) and the inverse axiom pairs
(which it does not) are joinable, and the nilpotent-inverse law-law pairs
(which it does not generate either) are joinable. -/
theorem hcp_combined (u : Fin n) (k : ℕ) (hk : 2 ≤ k) (inv : Fin n → Option (Fin n))
    (cancel : Prop) (hu : InvUnitFree inv u) {R : Rules n} (hor : Oriented R)
    (hRR : RuleRuleCP (Laws.combined u k hk inv cancel hu) R)
    (hmatch : InvMatching inv)
    (hlhs_u : ∀ A B, (A, B) ∈ R → u ∉ A)
    (hlhs_k : ∀ A B, (A, B) ∈ R → ∀ a, A.count a < k)
    (hlhs_inv : ∀ A B, (A, B) ∈ R → InvNormal inv A)
    (hax_nil : ∀ A B, (A, B) ∈ R → ∀ a ∈ A,
      Joinable (Rw (plain n) (R ∪ (Laws.combined u k hk inv cancel hu).axRules))
        (B + Multiset.replicate (k - A.count a) a) (A.filter (· ≠ a)))
    (hax_inv : InverseAxiomCP (Laws.combined u k hk inv cancel hu) inv R)
    (hnilinv : NilpotentInverseCP (R ∪ (Laws.combined u k hk inv cancel hu).axRules) k inv) :
    HCP (Laws.combined u k hk inv cancel hu) R := by
  set N := combinedNF u k hk inv cancel hu with hN
  have hconv : ∀ M P, Joinable (Rw (plain n) (R ∪ N.toLaws.axRules)) M P →
      Joinable (Rw (plain n) (R ∪ N.gen)) M P := fun M P => (N.joinable_iff M P).mp
  have hgen : N.gen = (unitGen u ∪ (nilpotentNF k hk cancel).gen) ∪ invGen inv := rfl
  apply N.hcp_of_gen hor
  rw [hgen]
  -- rule-generator pairs
  have hRG : ∀ r₁ r₂, r₁ ∈ R → r₂ ∈ (unitGen u ∪ (nilpotentNF k hk cancel).gen) ∪ invGen inv →
      r₁ ≠ r₂ → Overlap r₁.1 r₂.1 →
      Joinable (Rw (plain n) (R ∪ N.gen))
        (criticalPair (plain n) r₁ r₂).1 (criticalPair (plain n) r₁ r₂).2 := by
    rintro ⟨A, B⟩ r₂ h₁ h₂ _ hov
    rcases h₂ with (h₂ | h₂) | h₂
    · have h₂' := Set.mem_singleton_iff.mp h₂
      subst h₂'
      exact absurd ((overlap_unitGen_iff A).mp hov) (hlhs_u A B h₁)
    · obtain ⟨a, rfl⟩ := (nilpotentNF_gen_iff _).mp h₂
      have ha : a ∈ A := ((nilpotentMap k hk).overlap_gen_iff A a).mp hov
      rw [nilpotent_cp_rule_gen hk (hlhs_k A B h₁) ha]
      exact hconv _ _ (hax_nil A B h₁ a ha)
    · obtain ⟨x, y, hxy, rfl⟩ := h₂
      rcases (overlap_pair_iff A x y).mp hov with hx | hy
      · rw [cp_rule_invGen_left (hlhs_inv A B h₁) hxy hx]
        exact hconv _ _ ((hax_inv A B h₁ x y hxy).1 hx)
      · by_cases hx : x ∈ A
        · rw [cp_rule_invGen_left (hlhs_inv A B h₁) hxy hx]
          exact hconv _ _ ((hax_inv A B h₁ x y hxy).1 hx)
        · have hne : x ≠ y := fun h => hx (h ▸ hy)
          rw [cp_rule_invGen_right (hlhs_inv A B h₁) hxy hne hy]
          exact hconv _ _ ((hax_inv A B h₁ x y hxy).2 hne hy)
  -- unit-nilpotent pairs
  have hUN : ∀ r₁ r₂, r₁ ∈ unitGen u → r₂ ∈ (nilpotentNF k hk cancel).gen → r₁ ≠ r₂ →
      Overlap r₁.1 r₂.1 →
      Joinable (Rw (plain n) (R ∪ N.gen))
        (criticalPair (plain n) r₁ r₂).1 (criticalPair (plain n) r₁ r₂).2 := by
    intro r₁ r₂ h₁ h₂ _ hov
    have h₁' := Set.mem_singleton_iff.mp h₁
    subst h₁'
    obtain ⟨a, rfl⟩ := (nilpotentNF_gen_iff _).mp h₂
    have hau : u ∈ Multiset.replicate k a := by
      obtain ⟨z, hz, hz'⟩ := hov
      rw [Multiset.mem_singleton] at hz
      exact hz ▸ hz'
    obtain ⟨-, rfl⟩ := Multiset.mem_replicate.mp hau
    rw [cp_unit_nil u k (by omega)]
    refine Joinable_of_rtg ?_
    have := Rw_rtg_mono (R := unitGen u) (S := R ∪ N.gen)
      (fun r hr => Or.inr (Or.inl (Or.inl hr))) (unitDrop_reach u (Multiset.replicate (k - 1) u))
    rwa [unitDrop_replicate_self] at this
  -- unit-inverse pairs
  have hUI : ∀ r₁ r₂, r₁ ∈ unitGen u → r₂ ∈ invGen inv → r₁ ≠ r₂ →
      Overlap r₁.1 r₂.1 →
      Joinable (Rw (plain n) (R ∪ N.gen))
        (criticalPair (plain n) r₁ r₂).1 (criticalPair (plain n) r₁ r₂).2 := by
    intro r₁ r₂ h₁ h₂ _ hov
    have h₁' := Set.mem_singleton_iff.mp h₁
    subst h₁'
    obtain ⟨x, y, hxy, rfl⟩ := h₂
    have hxu : x = u ∧ y = u := by
      obtain ⟨z, hz, hz'⟩ := hov
      rw [Multiset.mem_singleton] at hz
      subst hz
      simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hz'
      rcases hz' with rfl | rfl
      · exact ⟨rfl, (hu _ _ hxy).mp rfl⟩
      · exact ⟨(hu _ _ hxy).mpr rfl, rfl⟩
    obtain ⟨hx, hy⟩ := hxu
    rw [hx, hy, cp_unit_inv]
    refine Joinable_of_rtg (ReflTransGen.single ?_)
    have h := Rw_plain_of_le (R := R ∪ N.gen) (A := {u}) (B := 0) (U := {u})
      (Or.inr (Or.inl (Or.inl rfl))) le_rfl
    simpa using h
  -- nilpotent-inverse pairs
  have hNI : ∀ r₁ r₂, r₁ ∈ (nilpotentNF k hk cancel).gen → r₂ ∈ invGen inv → r₁ ≠ r₂ →
      Overlap r₁.1 r₂.1 →
      Joinable (Rw (plain n) (R ∪ N.gen))
        (criticalPair (plain n) r₁ r₂).1 (criticalPair (plain n) r₁ r₂).2 := by
    intro r₁ r₂ h₁ h₂ hne hov
    obtain ⟨a, rfl⟩ := (nilpotentNF_gen_iff _).mp h₁
    obtain ⟨x, y, hxy, rfl⟩ := h₂
    have hmem : a = x ∨ a = y := by
      obtain ⟨z, hz, hz'⟩ := hov
      obtain ⟨-, rfl⟩ := Multiset.mem_replicate.mp hz
      simpa only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] using hz'
    by_cases hxy' : x = y
    · subst hxy'
      have ha : a = x := by rcases hmem with h | h <;> exact h
      subst ha
      by_cases hk2 : 2 < k
      · rw [cp_nil_inv_self k hk]
        exact hconv _ _ ((hnilinv _ _ hxy).2 rfl hk2)
      · exfalso
        have hk' : k = 2 := by omega
        subst hk'
        exact hne (by rw [pair_self_eq_replicate])
    · rcases hmem with rfl | rfl
      · rw [cp_nil_inv_left k (by omega) hxy']
        exact hconv _ _ ((hnilinv _ _ hxy).1 hxy').1
      · rw [cp_nil_inv_right k (by omega) hxy']
        exact hconv _ _ ((hnilinv _ _ hxy).1 hxy').2
  have hUU : ∀ r₁ r₂, r₁ ∈ unitGen u → r₂ ∈ unitGen u → r₁ ≠ r₂ → Overlap r₁.1 r₂.1 →
      Joinable (Rw (plain n) (R ∪ N.gen))
        (criticalPair (plain n) r₁ r₂).1 (criticalPair (plain n) r₁ r₂).2 :=
    fun r₁ r₂ h₁ h₂ hne _ => absurd (unitGen_gen_gen h₁ h₂) hne
  have hNN : ∀ r₁ r₂, r₁ ∈ (nilpotentNF k hk cancel).gen → r₂ ∈ (nilpotentNF k hk cancel).gen →
      r₁ ≠ r₂ → Overlap r₁.1 r₂.1 →
      Joinable (Rw (plain n) (R ∪ N.gen))
        (criticalPair (plain n) r₁ r₂).1 (criticalPair (plain n) r₁ r₂).2 :=
    fun r₁ r₂ h₁ h₂ hne hov => absurd ((nilpotentMap k hk).gen_gen h₁ h₂ hov) hne
  have hII : ∀ r₁ r₂, r₁ ∈ invGen inv → r₂ ∈ invGen inv → r₁ ≠ r₂ → Overlap r₁.1 r₂.1 →
      Joinable (Rw (plain n) (R ∪ N.gen))
        (criticalPair (plain n) r₁ r₂).1 (criticalPair (plain n) r₁ r₂).2 :=
    fun r₁ r₂ h₁ h₂ hne hov => absurd (invGen_gen_gen hmatch h₁ h₂ hov) hne
  have hUNI : ∀ r₁ r₂, r₁ ∈ unitGen u ∪ (nilpotentNF k hk cancel).gen → r₂ ∈ invGen inv →
      r₁ ≠ r₂ → Overlap r₁.1 r₂.1 →
      Joinable (Rw (plain n) (R ∪ N.gen))
        (criticalPair (plain n) r₁ r₂).1 (criticalPair (plain n) r₁ r₂).2 := by
    rintro r₁ r₂ (h₁ | h₁) h₂ hne hov
    · exact hUI r₁ r₂ h₁ h₂ hne hov
    · exact hNI r₁ r₂ h₁ h₂ hne hov
  exact hcp_split (S := R ∪ N.gen) (N.hcp_rules_gen_of_ax hRR) hRG
    (hcp_split (hcp_split hUU hUN hNN) hUNI hII)

/-! ## Identity and inverse: the composition without nilpotent cases -/

/-- `hcp` for the composition identity-inverse (`:identity :inverse`
without `:nilpotent`): the hypotheses of `hcp_combined` minus the
nilpotent ones. -/
theorem hcp_identityInverse (u : Fin n) (inv : Fin n → Option (Fin n)) (cancel : Prop)
    (hu : InvUnitFree inv u) {R : Rules n} (hor : Oriented R)
    (hRR : RuleRuleCP (Laws.identityInverse u inv cancel hu) R)
    (hmatch : InvMatching inv)
    (hlhs_u : ∀ A B, (A, B) ∈ R → u ∉ A)
    (hlhs_inv : ∀ A B, (A, B) ∈ R → InvNormal inv A)
    (hax_inv : InverseAxiomCP (Laws.identityInverse u inv cancel hu) inv R) :
    HCP (Laws.identityInverse u inv cancel hu) R := by
  set N := identityInverseNF u inv cancel hu with hN
  have hconv : ∀ M P, Joinable (Rw (plain n) (R ∪ N.toLaws.axRules)) M P →
      Joinable (Rw (plain n) (R ∪ N.gen)) M P := fun M P => (N.joinable_iff M P).mp
  have hgen : N.gen = unitGen u ∪ invGen inv := rfl
  apply N.hcp_of_gen hor
  rw [hgen]
  -- rule-generator pairs
  have hRG : ∀ r₁ r₂, r₁ ∈ R → r₂ ∈ unitGen u ∪ invGen inv → r₁ ≠ r₂ → Overlap r₁.1 r₂.1 →
      Joinable (Rw (plain n) (R ∪ N.gen))
        (criticalPair (plain n) r₁ r₂).1 (criticalPair (plain n) r₁ r₂).2 := by
    rintro ⟨A, B⟩ r₂ h₁ h₂ _ hov
    rcases h₂ with h₂ | h₂
    · have h₂' := Set.mem_singleton_iff.mp h₂
      subst h₂'
      exact absurd ((overlap_unitGen_iff A).mp hov) (hlhs_u A B h₁)
    · obtain ⟨x, y, hxy, rfl⟩ := h₂
      rcases (overlap_pair_iff A x y).mp hov with hx | hy
      · rw [cp_rule_invGen_left (hlhs_inv A B h₁) hxy hx]
        exact hconv _ _ ((hax_inv A B h₁ x y hxy).1 hx)
      · by_cases hx : x ∈ A
        · rw [cp_rule_invGen_left (hlhs_inv A B h₁) hxy hx]
          exact hconv _ _ ((hax_inv A B h₁ x y hxy).1 hx)
        · have hne : x ≠ y := fun h => hx (h ▸ hy)
          rw [cp_rule_invGen_right (hlhs_inv A B h₁) hxy hne hy]
          exact hconv _ _ ((hax_inv A B h₁ x y hxy).2 hne hy)
  -- unit-inverse pairs
  have hUI : ∀ r₁ r₂, r₁ ∈ unitGen u → r₂ ∈ invGen inv → r₁ ≠ r₂ →
      Overlap r₁.1 r₂.1 →
      Joinable (Rw (plain n) (R ∪ N.gen))
        (criticalPair (plain n) r₁ r₂).1 (criticalPair (plain n) r₁ r₂).2 := by
    intro r₁ r₂ h₁ h₂ _ hov
    have h₁' := Set.mem_singleton_iff.mp h₁
    subst h₁'
    obtain ⟨x, y, hxy, rfl⟩ := h₂
    have hxu : x = u ∧ y = u := by
      obtain ⟨z, hz, hz'⟩ := hov
      rw [Multiset.mem_singleton] at hz
      subst hz
      simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hz'
      rcases hz' with rfl | rfl
      · exact ⟨rfl, (hu _ _ hxy).mp rfl⟩
      · exact ⟨(hu _ _ hxy).mpr rfl, rfl⟩
    obtain ⟨hx, hy⟩ := hxu
    rw [hx, hy, cp_unit_inv]
    refine Joinable_of_rtg (ReflTransGen.single ?_)
    have h := Rw_plain_of_le (R := R ∪ N.gen) (A := {u}) (B := 0) (U := {u})
      (Or.inr (Or.inl rfl)) le_rfl
    simpa using h
  have hUU : ∀ r₁ r₂, r₁ ∈ unitGen u → r₂ ∈ unitGen u → r₁ ≠ r₂ → Overlap r₁.1 r₂.1 →
      Joinable (Rw (plain n) (R ∪ N.gen))
        (criticalPair (plain n) r₁ r₂).1 (criticalPair (plain n) r₁ r₂).2 :=
    fun r₁ r₂ h₁ h₂ hne _ => absurd (unitGen_gen_gen h₁ h₂) hne
  have hII : ∀ r₁ r₂, r₁ ∈ invGen inv → r₂ ∈ invGen inv → r₁ ≠ r₂ → Overlap r₁.1 r₂.1 →
      Joinable (Rw (plain n) (R ∪ N.gen))
        (criticalPair (plain n) r₁ r₂).1 (criticalPair (plain n) r₁ r₂).2 :=
    fun r₁ r₂ h₁ h₂ hne hov => absurd (invGen_gen_gen hmatch h₁ h₂ hov) hne
  exact hcp_split (S := R ∪ N.gen) (N.hcp_rules_gen_of_ax hRR) hRG (hcp_split hUU hUI hII)

/-! ## Identity and idempotent -/

/-- `hcp` for the composition identity-idempotent (`:idempotent :identity`).
Beyond the rule-rule pairs: no left side carries the unit, left sides are
sets, and the idempotent axiom pairs `(B ⊎ {a}, A)` are joinable. The
unit generator and an idempotent generator never overlap (the idempotent
generators are at the classes other than the unit). -/
theorem hcp_idempotentIdentity (u : Fin n) (cancel : Prop) {R : Rules n} (hor : Oriented R)
    (hRR : RuleRuleCP (Laws.idempotentIdentity u cancel) R)
    (hlhs_u : ∀ A B, (A, B) ∈ R → u ∉ A)
    (hlhs : ∀ A B, (A, B) ∈ R → A.Nodup)
    (hax : ∀ A B, (A, B) ∈ R → ∀ a ∈ A,
      Joinable (Rw (plain n) (R ∪ (Laws.idempotentIdentity u cancel).axRules)) (B + {a}) A) :
    HCP (Laws.idempotentIdentity u cancel) R := by
  set N := idempotentIdentityNF u cancel with hN
  have hconv : ∀ M P, Joinable (Rw (plain n) (R ∪ N.toLaws.axRules)) M P →
      Joinable (Rw (plain n) (R ∪ N.gen)) M P := fun M P => (N.joinable_iff M P).mp
  have hgen : N.gen = unitGen u ∪ idemGenNe u := rfl
  apply N.hcp_of_gen hor
  rw [hgen]
  -- rule-generator pairs
  have hRG : ∀ r₁ r₂, r₁ ∈ R → r₂ ∈ unitGen u ∪ idemGenNe u → r₁ ≠ r₂ → Overlap r₁.1 r₂.1 →
      Joinable (Rw (plain n) (R ∪ N.gen))
        (criticalPair (plain n) r₁ r₂).1 (criticalPair (plain n) r₁ r₂).2 := by
    rintro ⟨A, B⟩ r₂ h₁ h₂ _ hov
    rcases h₂ with h₂ | ⟨a, -, rfl⟩
    · have h₂' := Set.mem_singleton_iff.mp h₂
      subst h₂'
      exact absurd ((overlap_unitGen_iff A).mp hov) (hlhs_u A B h₁)
    · have ha : a ∈ A := (idempotentMap.overlap_gen_iff A a).mp hov
      rw [idempotent_cp_rule_gen (hlhs A B h₁) ha]
      exact hconv _ _ (hax A B h₁ a ha)
  -- unit-idempotent pairs: none
  have hUI : ∀ r₁ r₂, r₁ ∈ unitGen u → r₂ ∈ idemGenNe u → r₁ ≠ r₂ → Overlap r₁.1 r₂.1 →
      Joinable (Rw (plain n) (R ∪ N.gen))
        (criticalPair (plain n) r₁ r₂).1 (criticalPair (plain n) r₁ r₂).2 := by
    intro r₁ r₂ h₁ h₂ _ hov
    have h₁' := Set.mem_singleton_iff.mp h₁
    subst h₁'
    obtain ⟨a, hau, rfl⟩ := h₂
    exfalso
    obtain ⟨z, hz, hz'⟩ := hov
    rw [Multiset.mem_singleton] at hz
    subst hz
    exact hau (Multiset.mem_replicate.mp hz').2.symm
  have hUU : ∀ r₁ r₂, r₁ ∈ unitGen u → r₂ ∈ unitGen u → r₁ ≠ r₂ → Overlap r₁.1 r₂.1 →
      Joinable (Rw (plain n) (R ∪ N.gen))
        (criticalPair (plain n) r₁ r₂).1 (criticalPair (plain n) r₁ r₂).2 :=
    fun r₁ r₂ h₁ h₂ hne _ => absurd (unitGen_gen_gen h₁ h₂) hne
  have hII : ∀ r₁ r₂, r₁ ∈ idemGenNe u → r₂ ∈ idemGenNe u → r₁ ≠ r₂ → Overlap r₁.1 r₂.1 →
      Joinable (Rw (plain n) (R ∪ N.gen))
        (criticalPair (plain n) r₁ r₂).1 (criticalPair (plain n) r₁ r₂).2 :=
    fun r₁ r₂ h₁ h₂ hne hov =>
      absurd (idempotentMap.gen_gen (idemGenNe_sub u h₁) (idemGenNe_sub u h₂) hov) hne
  exact hcp_split (S := R ∪ N.gen) (N.hcp_rules_gen_of_ax hRR) hRG (hcp_split hUU hUI hII)

end SemperProofs.CC
