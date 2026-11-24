import SemperProofs.CC.Lemmas

/-!
# L11: confluence modulo the laws

The original L11 statement (local confluence from rule-rule and rule-law pairs alone) is false
(see `stub_counterexample` below for the shape): with an abstract `clamp`,
joinability of the rule-rule and rule-law pairs does not give local
confluence of clamp-normalized rewriting, because two reducts can both be
clamped and joinability is not transitive. Kapur (Lemmas 5-9) proves the
modulo result by reading the laws as rewrite rules `Ax`, taking the
critical pairs of `R ∪ Ax` and using termination. That is the statement
proved here: under orientation of `R` and of the law instances, with
`clamp` producing `Ax`-normal forms, joinability of every critical pair of
`R ∪ Ax` under plain rewriting gives confluence (hence local confluence) of
clamp-normalized rewriting `Rw L R`.
-/

namespace SemperProofs.CC

open Relation

variable {n : ℕ}

/-- The law instances read as rewrite rules. -/
def Laws.axRules (L : Laws n) : Rules n := { p | L.lawRel p.1 p.2 }

/-- Plain rewriting: `clamp` is the identity. -/
abbrev plain (n : ℕ) : Laws n := Laws.plainAC n

theorem plain_clamp (M : Monomial n) : (plain n).clamp M = M := rfl

theorem Rw_mono {L : Laws n} {R S : Rules n} (hsub : R ⊆ S) {M N : Monomial n}
    (h : Rw L R M N) : Rw L S M N := by
  obtain ⟨A, B, hAB, hA, rfl⟩ := h
  exact ⟨A, B, hsub hAB, hA, rfl⟩

theorem Rw_rtg_mono {L : Laws n} {R S : Rules n} (hsub : R ⊆ S) {M N : Monomial n}
    (h : ReflTransGen (Rw L R) M N) : ReflTransGen (Rw L S) M N := by
  induction h with
  | refl => exact ReflTransGen.refl
  | tail _ hs ih => exact ih.tail (Rw_mono hsub hs)

/-- A clamp-normalized step is a plain step by the rule followed by at most
one law step. -/
theorem Rw_embed {L : Laws n} {R : Rules n} {M N : Monomial n} (h : Rw L R M N) :
    ReflTransGen (Rw (plain n) (R ∪ L.axRules)) M N := by
  obtain ⟨A, B, hAB, hA, rfl⟩ := h
  have h1 : Rw (plain n) (R ∪ L.axRules) M ((M - A) + B) := ⟨A, B, Or.inl hAB, hA, rfl⟩
  refine (ReflTransGen.single h1).trans ?_
  rcases L.clamp_law ((M - A) + B) with heq | hlaw
  · rw [heq]
  · refine ReflTransGen.single ⟨(M - A) + B, L.clamp ((M - A) + B), Or.inr hlaw, le_rfl, ?_⟩
    rw [plain_clamp, tsub_self, zero_add]

theorem Rw_rtg_embed {L : Laws n} {R : Rules n} {M N : Monomial n}
    (h : ReflTransGen (Rw L R) M N) :
    ReflTransGen (Rw (plain n) (R ∪ L.axRules)) M N := by
  induction h with
  | refl => exact ReflTransGen.refl
  | tail _ hs ih => exact ih.trans (Rw_embed hs)

theorem oriented_union {L : Laws n} {R : Rules n} (hR : Oriented R)
    (hlaw : ∀ P Q, L.lawRel P Q → degLex P Q) : Oriented (R ∪ L.axRules) := by
  intro A B hAB
  rcases hAB with h | h
  · exact hR A B h
  · exact hlaw A B h

/-- If `clamp` outputs are `Ax`-normal, `clamp` is idempotent. -/
theorem clamp_idem {L : Laws n}
    (hnf : ∀ M N, ¬ Rw (plain n) L.axRules (L.clamp M) N) (M : Monomial n) :
    L.clamp (L.clamp M) = L.clamp M := by
  rcases L.clamp_law (L.clamp M) with h | h
  · exact h
  · exact absurd ⟨L.clamp M, L.clamp (L.clamp M), h, le_rfl, by
      rw [plain_clamp, tsub_self, zero_add]⟩ (hnf M _)

/-- Every target of a clamp-normalized step is a `clamp` output. -/
theorem Rw_target_clamp {L : Laws n} {R : Rules n} {M N : Monomial n} (h : Rw L R M N) :
    ∃ P, N = L.clamp P := by
  obtain ⟨A, B, _, _, rfl⟩ := h
  exact ⟨_, rfl⟩

theorem Rw_rtg_target_clamp {L : Laws n} {R : Rules n} {M N : Monomial n}
    (h : ReflTransGen (Rw L R) M N) (hM : ∃ P, M = L.clamp P) : ∃ P, N = L.clamp P := by
  induction h with
  | refl => exact hM
  | tail _ hs _ => exact Rw_target_clamp hs

/-- A well-founded relation has normal forms. -/
theorem exists_nf {α : Type*} {r : α → α → Prop} (hwf : WellFounded (fun b a => r a b))
    (a : α) : ∃ b, ReflTransGen r a b ∧ ∀ c, ¬ r b c := by
  induction a using hwf.induction with
  | _ a ih =>
    by_cases h : ∃ c, r a c
    · obtain ⟨c, hc⟩ := h
      obtain ⟨b, hb, hnf⟩ := ih c hc
      exact ⟨b, ReflTransGen.head hc hb, hnf⟩
    · exact ⟨a, ReflTransGen.refl, fun c hc => h ⟨c, hc⟩⟩

/-- A `clamp` output that is normal for clamp-normalized rewriting is
normal for plain rewriting over `R ∪ Ax`. -/
theorem plain_normal_of_normal {L : Laws n} {R : Rules n}
    (hnf : ∀ M N, ¬ Rw (plain n) L.axRules (L.clamp M) N) {V : Monomial n}
    (hV : ∃ P, V = L.clamp P) (hnorm : ∀ N, ¬ Rw L R V N) :
    ∀ N, ¬ Rw (plain n) (R ∪ L.axRules) V N := by
  rintro N ⟨A, B, hAB, hA, rfl⟩
  rcases hAB with h | h
  · exact hnorm _ ⟨A, B, h, hA, rfl⟩
  · obtain ⟨P, rfl⟩ := hV
    exact hnf P _ ⟨A, B, h, hA, rfl⟩

/-- L11, corrected: confluence of clamp-normalized rewriting from the
critical pairs of `R ∪ Ax` (Kapur, Lemmas 5-9 read through Lemma 1 and
termination). Hypotheses: `R` oriented; every law instance decreases in
degree-lex; `clamp` outputs are `Ax`-normal; every critical pair of two
distinct overlapping rules of `R ∪ Ax` is joinable under plain rewriting. -/
theorem confluent_modulo' (L : Laws n) (R : Rules n)
    (hor : Oriented R)
    (hlaw : ∀ P Q, L.lawRel P Q → degLex P Q)
    (hnf : ∀ M N, ¬ Rw (plain n) L.axRules (L.clamp M) N)
    (hcp : ∀ r₁ r₂, r₁ ∈ R ∪ L.axRules → r₂ ∈ R ∪ L.axRules → r₁ ≠ r₂ →
      Overlap r₁.1 r₂.1 →
      Joinable (Rw (plain n) (R ∪ L.axRules))
        (criticalPair (plain n) r₁ r₂).1 (criticalPair (plain n) r₁ r₂).2) :
    Confluent (Rw L R) := by
  have hSor : Oriented (R ∪ L.axRules) := oriented_union hor hlaw
  have hconf : Confluent (Rw (plain n) (R ∪ L.axRules)) :=
    newman (Rw_wf hSor) (critical_pair_lemma (plain n) (fun _ => rfl) _ hcp)
  intro M N₁ N₂ h₁ h₂
  rcases h₁.cases_head with rfl | ⟨P₁, hP₁, h₁'⟩
  · exact ⟨N₂, h₂, ReflTransGen.refl⟩
  rcases h₂.cases_head with rfl | ⟨P₂, hP₂, h₂'⟩
  · exact ⟨N₁, ReflTransGen.refl, h₁⟩
  have hN₁ : ∃ P, N₁ = L.clamp P := Rw_rtg_target_clamp h₁' (Rw_target_clamp hP₁)
  have hN₂ : ∃ P, N₂ = L.clamp P := Rw_rtg_target_clamp h₂' (Rw_target_clamp hP₂)
  obtain ⟨V₁, hV₁, hn₁⟩ := exists_nf (Rw_wf (L := L) hor) N₁
  obtain ⟨V₂, hV₂, hn₂⟩ := exists_nf (Rw_wf (L := L) hor) N₂
  have hV₁c := Rw_rtg_target_clamp hV₁ hN₁
  have hV₂c := Rw_rtg_target_clamp hV₂ hN₂
  have hpn₁ := plain_normal_of_normal hnf hV₁c hn₁
  have hpn₂ := plain_normal_of_normal hnf hV₂c hn₂
  obtain ⟨U, hU₁, hU₂⟩ :=
    hconf M V₁ V₂ (Rw_rtg_embed (h₁.trans hV₁)) (Rw_rtg_embed (h₂.trans hV₂))
  have e₁ := rtg_of_normal hpn₁ hU₁
  have e₂ := rtg_of_normal hpn₂ hU₂
  refine ⟨V₁, hV₁, ?_⟩
  rw [e₁, ← e₂]
  exact hV₂

/-- L11, corrected, in the stub's shape: local confluence. -/
theorem critical_pair_lemma_modulo' (L : Laws n) (R : Rules n)
    (hor : Oriented R)
    (hlaw : ∀ P Q, L.lawRel P Q → degLex P Q)
    (hnf : ∀ M N, ¬ Rw (plain n) L.axRules (L.clamp M) N)
    (hcp : ∀ r₁ r₂, r₁ ∈ R ∪ L.axRules → r₂ ∈ R ∪ L.axRules → r₁ ≠ r₂ →
      Overlap r₁.1 r₂.1 →
      Joinable (Rw (plain n) (R ∪ L.axRules))
        (criticalPair (plain n) r₁ r₂).1 (criticalPair (plain n) r₁ r₂).2) :
    LocallyConfluent (Rw L R) :=
  fun a b c hab hac =>
    confluent_modulo' L R hor hlaw hnf hcp a b c (ReflTransGen.single hab)
      (ReflTransGen.single hac)

/-! ## The stub is false as stated

Pool `Fin 5` with `a = 0`, `b = 1`, `x = 2`, `c = 3`, `p = 4`. Rules
`{a, x} → {p}` and `{b, x} → {p}`; `clamp` contracts `{b, p}` and `{a, p}`
to `{p}` and is the identity elsewhere, with `lawRel M N := N = clamp M ∧
N ≠ M`. The one critical pair is `({p}, {p})`, joinable; no rule's left
side fits inside a law instance, so the rule-law hypothesis is vacuous.
From `M = {a, b, x, c}` the two steps give `{b, c, p}` and `{a, c, p}`,
both normal and distinct. -/

/-- The counterexample's clamp. -/
def clampCE (M : Monomial 5) : Monomial 5 :=
  if M = {1, 4} ∨ M = {0, 4} then {4} else M

/-- The counterexample's laws. -/
def lawsCE : Laws 5 where
  lawRel M N := N = clampCE M ∧ N ≠ M
  clamp := clampCE
  clamp_le M := by
    unfold clampCE
    split_ifs with h
    · rcases h with rfl | rfl <;> decide
    · exact le_rfl
  clamp_law M := by
    by_cases h : clampCE M = M
    · exact Or.inl h
    · exact Or.inr ⟨rfl, h⟩
  cancellative := False

/-- The counterexample's rules. -/
def rulesCE : Rules 5 := {(({0, 2} : Monomial 5), ({4} : Monomial 5)), (({1, 2} : Monomial 5), ({4} : Monomial 5))}

theorem rulesCE_mem {r : Monomial 5 × Monomial 5} (h : r ∈ rulesCE) :
    r = ({0, 2}, {4}) ∨ r = ({1, 2}, {4}) := by
  simpa [rulesCE] using h

theorem stub_counterexample :
    ¬ (∀ (L : Laws 5) (R : Rules 5),
      (∀ r₁ r₂, r₁ ∈ R → r₂ ∈ R → r₁ ≠ r₂ → Overlap r₁.1 r₂.1 →
        Joinable (Rw L R) (criticalPair L r₁ r₂).1 (criticalPair L r₁ r₂).2) →
      (∀ A B X Y, (A, B) ∈ R → L.lawRel (A + X) Y →
        Joinable (Rw L R) (L.clamp (B + X)) (L.clamp Y)) →
      LocallyConfluent (Rw L R)) := by
  intro h
  have hcp : ∀ r₁ r₂, r₁ ∈ rulesCE → r₂ ∈ rulesCE → r₁ ≠ r₂ → Overlap r₁.1 r₂.1 →
      Joinable (Rw lawsCE rulesCE) (criticalPair lawsCE r₁ r₂).1
        (criticalPair lawsCE r₁ r₂).2 := by
    intro r₁ r₂ h₁ h₂ hne _
    rcases rulesCE_mem h₁ with rfl | rfl <;> rcases rulesCE_mem h₂ with rfl | rfl
    · exact absurd rfl hne
    · have : criticalPair lawsCE ({0, 2}, {4}) ({1, 2}, {4}) = ({4}, {4}) := by decide
      rw [this]; exact ⟨_, ReflTransGen.refl, ReflTransGen.refl⟩
    · have : criticalPair lawsCE ({1, 2}, {4}) ({0, 2}, {4}) = ({4}, {4}) := by decide
      rw [this]; exact ⟨_, ReflTransGen.refl, ReflTransGen.refl⟩
    · exact absurd rfl hne
  have hlaw : ∀ A B X Y, (A, B) ∈ rulesCE → lawsCE.lawRel (A + X) Y →
      Joinable (Rw lawsCE rulesCE) (lawsCE.clamp (B + X)) (lawsCE.clamp Y) := by
    intro A B X Y hAB ⟨hY, hne⟩
    exfalso
    have hx : (2 : Fin 5) ∈ A + X := by
      rcases rulesCE_mem hAB with h | h <;> simp only [Prod.mk.injEq] at h <;>
        obtain ⟨rfl, -⟩ := h <;> simp
    apply hne
    rw [hY]
    show clampCE (A + X) = A + X
    unfold clampCE
    split_ifs with hc
    · exfalso
      rcases hc with hc | hc <;> rw [hc] at hx <;> revert hx <;> decide
    · rfl
  have hlc := h lawsCE rulesCE hcp hlaw
  have s₁ : Rw lawsCE rulesCE {0, 1, 2, 3} {1, 3, 4} :=
    ⟨{0, 2}, {4}, by simp [rulesCE], by decide, by decide⟩
  have s₂ : Rw lawsCE rulesCE {0, 1, 2, 3} {0, 3, 4} :=
    ⟨{1, 2}, {4}, by simp [rulesCE], by decide, by decide⟩
  obtain ⟨U, hU₁, hU₂⟩ := hlc _ _ _ s₁ s₂
  have n₁ : ∀ N, ¬ Rw lawsCE rulesCE {1, 3, 4} N := by
    rintro N ⟨A, B, hAB, hA, -⟩
    rcases rulesCE_mem hAB with h | h <;> simp only [Prod.mk.injEq] at h <;>
      obtain ⟨rfl, -⟩ := h <;> revert hA <;> decide
  have n₂ : ∀ N, ¬ Rw lawsCE rulesCE {0, 3, 4} N := by
    rintro N ⟨A, B, hAB, hA, -⟩
    rcases rulesCE_mem hAB with h | h <;> simp only [Prod.mk.injEq] at h <;>
      obtain ⟨rfl, -⟩ := h <;> revert hA <;> decide
  have e₁ := rtg_of_normal n₁ hU₁
  have e₂ := rtg_of_normal n₂ hU₂
  have : ({1, 3, 4} : Monomial 5) = {0, 3, 4} := e₁.trans e₂.symm
  revert this
  decide

end SemperProofs.CC
