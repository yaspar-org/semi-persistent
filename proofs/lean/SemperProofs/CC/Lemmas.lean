import SemperProofs.CC.Defs

/-!
# AC-congruence closure: lemmas L1-L16

Statements follow part (f) of the proof sketch "AC-congruence closure:
soundness and completeness" (notes.md). Each theorem's docstring names the
sketch item. Every lemma here is proved; L11 and L16 live in `Proofs/`.
-/

namespace SemperProofs.CC

open Relation

variable {n : ℕ}

/-! ## L1: `degLex` is a strict total order -/

/-- Colexicographic `<` on count vectors, as a `Pi.Lex` relation: largest
class first, then the smaller count. -/
theorem colex_lt_iff (x y : Colex (Fin n → ℕ)) :
    x < y ↔ ∃ c, (∀ d, c < d → ofColex x d = ofColex y d) ∧ ofColex x c < ofColex y c :=
  Iff.rfl

/-- L1, irreflexivity. -/
theorem degLex_irrefl (M : Monomial n) : ¬ degLex M M := by
  rw [degLex_iff, Prod.lex_def]
  rintro (h | ⟨_, h⟩)
  · exact lt_irrefl _ h
  · exact lt_irrefl _ h

/-- L1, transitivity. -/
theorem degLex_trans {M N P : Monomial n} (h₁ : degLex M N) (h₂ : degLex N P) :
    degLex M P := by
  rw [degLex_iff, Prod.lex_def] at *
  rcases h₁ with h₁ | ⟨e₁, h₁⟩ <;> rcases h₂ with h₂ | ⟨e₂, h₂⟩
  · exact Or.inl (lt_trans h₂ h₁)
  · exact Or.inl (e₂ ▸ h₁)
  · exact Or.inl (e₁ ▸ h₂)
  · exact Or.inr ⟨e₂.trans e₁, lt_trans h₂ h₁⟩

/-- Equal count vectors give equal monomials. -/
theorem countVec_injective {M N : Monomial n} (h : countVec M = countVec N) : M = N := by
  unfold countVec at h
  rw [toColex_inj] at h
  exact Multiset.ext' fun c => congrFun h c

/-- L1, trichotomy. -/
theorem degLex_trichotomous (M N : Monomial n) : degLex M N ∨ M = N ∨ degLex N M := by
  rcases lt_trichotomy (Multiset.card N) (Multiset.card M) with h | h | h
  · exact Or.inl (Or.inl h)
  · rcases lt_trichotomy (countVec N) (countVec M) with h' | h' | h'
    · exact Or.inl (Or.inr ⟨h, h'⟩)
    · exact Or.inr (Or.inl (countVec_injective h').symm)
    · exact Or.inr (Or.inr (Or.inr ⟨h.symm, h'⟩))
  · exact Or.inr (Or.inr (Or.inl h))

/-- L1: `degLex` is a strict total order. -/
instance degLex_isStrictTotalOrder : IsStrictTotalOrder (Monomial n) degLex where
  irrefl := degLex_irrefl
  trans _ _ _ := degLex_trans
  trichotomous a b h₁ h₂ := by
    rcases degLex_trichotomous a b with h | h | h
    · exact absurd h h₁
    · exact h
    · exact absurd h h₂

/-! ## L2: `degLex` is well-founded -/

/-- Colex on `Fin n → ℕ` is well-founded (`Pi.Lex.wellFounded` over the dual index order). -/
theorem colex_wf : WellFounded (fun x y : Colex (Fin n → ℕ) => x < y) :=
  Pi.Lex.wellFounded (ι := (Fin n)ᵒᵈ) (α := fun _ => ℕ) (· < ·)

/-- L2: there is no infinite `≫`-descending chain of monomials. -/
theorem degLex_wf : WellFounded (fun N M : Monomial n => degLex M N) := by
  have h : WellFounded (Prod.Lex (· < ·) (· < ·) : ℕ × Colex (Fin n → ℕ) → _ → Prop) :=
    WellFounded.prod_lex wellFounded_lt colex_wf
  refine Subrelation.wf ?_ (InvImage.wf (fun M : Monomial n => (Multiset.card M, countVec M)) h)
  intro N M hNM
  exact (degLex_iff M N).1 hNM

/-! ## L3: compatibility -/

/-- A strict sub-multiset is `≫`-smaller. -/
theorem degLex_of_lt {M N : Monomial n} (h : N < M) : degLex M N :=
  Or.inl (Multiset.card_lt_card h)

/-- L3, first half: replacing `A ⊆ M` by a `≫`-smaller `B` gives a `≫`-smaller
monomial (the "compatibility" of `multiset.rs:305-310`). -/
theorem degLex_compat {A B M : Monomial n} (hA : A ≤ M) (h : degLex A B) :
    degLex M ((M - A) + B) := by
  have hcard : Multiset.card ((M - A) + B) = Multiset.card M - Multiset.card A + Multiset.card B := by
    rw [Multiset.card_add, Multiset.card_sub hA]
  have hAM : Multiset.card A ≤ Multiset.card M := Multiset.card_le_card hA
  rcases h with h | ⟨hc, c, hup, hlt⟩
  · left; rw [hcard]; omega
  · right
    refine ⟨by rw [hcard]; omega, c, fun d hd => ?_, ?_⟩
    · rw [Multiset.count_add, Multiset.count_sub, hup d hd]
      have := Multiset.count_le_of_le d hA
      omega
    · rw [Multiset.count_add, Multiset.count_sub]
      have := Multiset.count_le_of_le c hA
      omega

/-- L3, second half: `clamp` never increases a monomial. -/
theorem degLex_clamp (L : Laws n) (M : Monomial n) : L.clamp M = M ∨ degLex M (L.clamp M) := by
  rcases (L.clamp_le M).lt_or_eq with h | h
  · exact Or.inr (degLex_of_lt h)
  · exact Or.inl h

/-- L3: a rewrite step by an oriented rule set is `≫`-decreasing. -/
theorem Rw_degLex {L : Laws n} {R : Rules n} (hR : Oriented R) {M N : Monomial n}
    (h : Rw L R M N) : degLex M N := by
  obtain ⟨A, B, hAB, hA, rfl⟩ := h
  have h₁ := degLex_compat hA (hR A B hAB)
  rcases degLex_clamp L ((M - A) + B) with h₂ | h₂
  · rw [h₂]; exact h₁
  · exact degLex_trans h₁ h₂

/-! ## L4: normalization terminates -/

/-- L4: under I1, one-step rewriting is well-founded. -/
theorem Rw_wf {L : Laws n} {R : Rules n} (hR : Oriented R) :
    WellFounded (fun N M : Monomial n => Rw L R M N) :=
  Subrelation.wf (fun h => Rw_degLex hR h) degLex_wf

/-! ## L5: soundness of a step -/

/-- L5: a rewrite step by rules that are `=_E`-consequences is an
`=_E`-consequence. -/
theorem Rw_sound {L : Laws n} {S : Set (Monomial n × Monomial n)} {R : Rules n}
    (hR : ∀ A B, (A, B) ∈ R → E L S A B) {M N : Monomial n} (h : Rw L R M N) :
    E L S M N := by
  obtain ⟨A, B, hAB, hA, rfl⟩ := h
  have hM : M - A + A = M := Multiset.sub_add_cancel hA
  have h₂ : E L S (M - A + A) (M - A + B) := by
    rw [add_comm (M - A) A, add_comm (M - A) B]
    exact E.congr _ (hR A B hAB)
  rw [hM] at h₂
  rcases L.clamp_law (M - A + B) with hc | hc
  · rw [hc]; exact h₂
  · exact E.trans h₂ (E.law hc)

/-- L5, iterated. -/
theorem Rw_rtg_sound {L : Laws n} {S : Set (Monomial n × Monomial n)} {R : Rules n}
    (hR : ∀ A B, (A, B) ∈ R → E L S A B) {M N : Monomial n}
    (h : ReflTransGen (Rw L R) M N) : E L S M N := by
  induction h with
  | refl => exact E.refl _
  | tail _ hstep ih => exact E.trans ih (Rw_sound hR hstep)

/-- The rules of a sound state are `=_E`-consequences. -/
theorem rules_sound {L : Laws n} {S : Set (Monomial n × Monomial n)} {st : State n}
    (h : I2 L S st) : ∀ A B, (A, B) ∈ st.rules → E L S A B := by
  rintro A B ⟨c, c', hA, hB, -, hBn, hcc⟩
  have hB' : B = st.rhs (st.find c) := hB
  subst hB'
  exact h A c _ c' hA.1 hBn hcc.symm

/-- Every step the loop takes between monomials of a sound state is an
`=_E`-consequence. -/
theorem Step_sound {L : Laws n} {S : Set (Monomial n × Monomial n)} {st : State n}
    (h : I2 L S st) {a b : Monomial n} (hs : st.Step L a b) : E L S a b := by
  rcases hs with hs | hs | hs | ⟨c, c', ha, hb, hcc⟩
  · exact Rw_sound (rules_sound h) hs
  · exact E.law hs
  · exact E.symm (E.law hs)
  · exact h a c b c' ha hb hcc

theorem Step_rtg_sound {L : Laws n} {S : Set (Monomial n × Monomial n)} {st : State n}
    (h : I2 L S st) {a b : Monomial n} (hs : ReflTransGen (st.Step L) a b) : E L S a b := by
  induction hs with
  | refl => exact E.refl _
  | tail _ hstep ih => exact E.trans ih (Step_sound h hstep)

/-! ## L6: every inference preserves I2 -/

/-- Merging two classes that hold `=_E`-equal nodes preserves I2. -/
theorem merge_I2 {L : Laws n} {S : Set (Monomial n × Monomial n)} {st : State n}
    (h : I2 L S st) {M N : Monomial n} {c d : Fin n}
    (hM : (M, c) ∈ st.nodes) (hN : (N, d) ∈ st.nodes) (hMN : E L S M N) :
    I2 L S (st.merge c d) := by
  intro P a Q b hP hQ hab
  simp only [State.merge] at hP hQ hab
  by_cases ha : st.find a = st.find c <;> by_cases hb : st.find b = st.find c <;>
    simp only [ha, hb, ite_true, ite_false] at hab
  · exact h P a Q b hP hQ (ha.trans hb.symm)
  · have h₁ := h P a M c hP hM ha
    have h₂ := h N d Q b hN hQ hab
    exact E.trans h₁ (E.trans hMN h₂)
  · have h₁ := h P a N d hP hN hab
    have h₂ := h M c Q b hM hQ hb.symm
    exact E.trans h₁ (E.trans (E.symm hMN) h₂)
  · exact h P a Q b hP hQ hab

/-- L6: each inference maps a state satisfying I2 to one satisfying I2. -/
theorem Infer_I2 {L : Laws n} {S : Set (Monomial n × Monomial n)} {st st' : State n}
    (hinf : Infer L st st') (h : I2 L S st) : I2 L S st' := by
  cases hinf with
  | mint hM hMN hfresh =>
    intro P a Q b hP hQ hab
    simp only [State.addNode, Set.mem_insert_iff, Prod.mk.injEq] at hP hQ
    rcases hP with ⟨rfl, rfl⟩ | hP <;> rcases hQ with ⟨rfl, rfl⟩ | hQ
    · exact E.refl _
    · exact absurd hab.symm (hfresh Q b hQ)
    · exact absurd hab (hfresh P a hP)
    · exact h P a Q b hP hQ hab
  | joinMerge hM hN hsteps => exact merge_I2 h hM hN (Step_rtg_sound h hsteps)
  | cancelMerge hc hMX hNX hcd hM hN =>
    exact merge_I2 h hM hN (E.cancel hc (h _ _ _ _ hMX hNX hcd))
  | retire _ => exact h
  | unretire _ _ => exact h
  | setRhs _ => exact h

/-! ## L7: soundness -/

/-- L7: every state reachable from a sound state is sound; the partition is
contained in `=_E`, whatever the outcome. -/
theorem soundness {L : Laws n} {S : Set (Monomial n × Monomial n)} {st₀ st : State n}
    (hreach : Reachable L st₀ st) (h₀ : I2 L S st₀) : I2 L S st := by
  induction hreach with
  | refl => exact h₀
  | tail _ hstep ih => exact Infer_I2 hstep ih

/-! ## L8-L11: confluence -/

/-- L9: Newman's lemma. Mathlib has `Relation.church_rosser` (a diamond
condition) but no statement from local confluence and termination, so it is
proved here by well-founded induction. -/
theorem newman {α : Type*} {r : α → α → Prop} (hwf : WellFounded (fun b a => r a b))
    (hlc : LocallyConfluent r) : Confluent r := by
  intro a
  induction a using hwf.induction with
  | _ a ih =>
    intro b c hab hac
    rcases hab.cases_head with rfl | ⟨a₁, ha₁, hb⟩
    · exact ⟨c, hac, ReflTransGen.refl⟩
    rcases hac.cases_head with rfl | ⟨a₂, ha₂, hc⟩
    · exact ⟨b, ReflTransGen.refl, hab⟩
    obtain ⟨d, hd₁, hd₂⟩ := hlc a a₁ a₂ ha₁ ha₂
    obtain ⟨e, he₁, he₂⟩ := ih a₁ ha₁ b d hb hd₁
    obtain ⟨f, hf₁, hf₂⟩ := ih a₂ ha₂ c e hc (hd₂.trans he₂)
    exact ⟨f, he₁.trans hf₂, hf₁⟩

/-- One rewrite step is compatible with union, when `clamp` is the identity. -/
theorem Rw_add {L : Laws n} {R : Rules n} (hclamp : ∀ M, L.clamp M = M) {M N : Monomial n}
    (X : Monomial n) (h : Rw L R M N) : Rw L R (M + X) (N + X) := by
  obtain ⟨A, B, hAB, hA, rfl⟩ := h
  refine ⟨A, B, hAB, le_add_right hA, ?_⟩
  rw [hclamp, hclamp, add_comm M X, add_tsub_assoc_of_le hA, add_comm X, add_assoc,
    add_comm B X, ← add_assoc]

theorem Rw_rtg_add {L : Laws n} {R : Rules n} (hclamp : ∀ M, L.clamp M = M) {M N : Monomial n}
    (X : Monomial n) (h : ReflTransGen (Rw L R) M N) :
    ReflTransGen (Rw L R) (M + X) (N + X) := by
  induction h with
  | refl => exact ReflTransGen.refl
  | tail _ hstep ih => exact ih.tail (Rw_add hclamp X hstep)

/-- L10: joinability is compatible with union, when `clamp` is the identity. -/
theorem Joinable_add {L : Laws n} {R : Rules n} (hclamp : ∀ M, L.clamp M = M)
    {M N : Monomial n} (X : Monomial n) (h : Joinable (Rw L R) M N) :
    Joinable (Rw L R) (M + X) (N + X) := by
  obtain ⟨P, hM, hN⟩ := h
  exact ⟨P + X, Rw_rtg_add hclamp X hM, Rw_rtg_add hclamp X hN⟩

/-- L8: the critical pair lemma for plain AC (`clamp` is the identity): if
every critical pair of two rules sharing a child is joinable, rewriting is
locally confluent (Kapur, Lemma 1). -/
theorem critical_pair_lemma (L : Laws n) (hclamp : ∀ M, L.clamp M = M) (R : Rules n)
    (h : ∀ r₁ r₂, r₁ ∈ R → r₂ ∈ R → r₁ ≠ r₂ → Overlap r₁.1 r₂.1 →
      Joinable (Rw L R) (criticalPair L r₁ r₂).1 (criticalPair L r₁ r₂).2) :
    LocallyConfluent (Rw L R) := by
  intro M N₁ N₂ h₁ h₂
  obtain ⟨A, A', hAA', hA, rfl⟩ := h₁
  obtain ⟨B, B', hBB', hB, rfl⟩ := h₂
  rw [hclamp, hclamp]
  by_cases heq : (A, A') = (B, B')
  · obtain ⟨rfl, rfl⟩ := Prod.mk.injEq _ _ _ _ ▸ heq
    exact ⟨_, ReflTransGen.refl, ReflTransGen.refl⟩
  by_cases hov : Overlap A B
  · -- the shared-child case: the critical pair, lifted by the common context `M - (A ∪ B)`
    have hcp := h (A, A') (B, B') hAA' hBB' heq hov
    simp only [criticalPair, hclamp] at hcp
    have hAB : A ∪ B ≤ M := Multiset.union_le hA hB
    have e₁ : M - A + A' = (M - (A ∪ B)) + ((A ∪ B) - A + A') := by
      rw [← add_assoc, tsub_add_tsub_cancel hAB Multiset.le_union_left]
    have e₂ : M - B + B' = (M - (A ∪ B)) + ((A ∪ B) - B + B') := by
      rw [← add_assoc, tsub_add_tsub_cancel hAB Multiset.le_union_right]
    rw [e₁, e₂, add_comm (M - (A ∪ B)), add_comm (M - (A ∪ B))]
    exact Joinable_add hclamp _ hcp
  · -- disjoint left sides commute
    have hdisj : ∀ x, x ∈ A → x ∉ B := fun x hxA hxB => hov ⟨x, hxA, hxB⟩
    have hBMA : B ≤ M - A := by
      rw [Multiset.le_iff_count]
      intro x
      rw [Multiset.count_sub]
      by_cases hxB : x ∈ B
      · have hxA : x ∉ A := fun hxA => hdisj x hxA hxB
        rw [Multiset.count_eq_zero_of_notMem hxA]
        have := Multiset.count_le_of_le x hB
        omega
      · rw [Multiset.count_eq_zero_of_notMem hxB]; omega
    have hAMB : A ≤ M - B := by
      rw [Multiset.le_iff_count]
      intro x
      rw [Multiset.count_sub]
      by_cases hxA : x ∈ A
      · have hxB : x ∉ B := hdisj x hxA
        rw [Multiset.count_eq_zero_of_notMem hxB]
        have := Multiset.count_le_of_le x hA
        omega
      · rw [Multiset.count_eq_zero_of_notMem hxA]; omega
    refine ⟨M - A - B + A' + B', ReflTransGen.single ⟨B, B', hBB', le_add_right hBMA, ?_⟩,
      ReflTransGen.single ⟨A, A', hAA', le_add_right hAMB, ?_⟩⟩
    · rw [hclamp, tsub_add_eq_add_tsub hBMA]
    · rw [hclamp, ← tsub_add_eq_add_tsub hAMB, tsub_right_comm]
      exact add_right_comm _ _ _

/-! L11 (critical pair lemma modulo the laws) is proved in corrected form in
`Proofs/CriticalPairModulo.lean` (`confluent_modulo'`); the original
statement is false, see `stub_counterexample` there. -/

/-! ## L12-L13: convergence and completeness -/

/-- I0 on the classes that hold an active node: such a class's stored
right-hand side is a node of the class. A class with no active node (a leaf
constant, or a class of another operator) is unconstrained. -/
def I0On (st : State n) : Prop :=
  ∀ M c, (M, c) ∈ st.active → ∃ c', (st.rhs (st.find c), c') ∈ st.nodes ∧ st.find c' = st.find c

theorem I0On_of_I0 {st : State n} (h : I0 st) : I0On st := fun _ c _ => h c

/-- L12: a state whose round changes nothing, with I0 on the classes holding
an active node, I5 and canonical right-hand sides, is converged. -/
theorem roundFixed_converged {L : Laws n} {st : State n} (h0 : I0On st) (h5 : I5 st)
    (hcanon : ∀ c, L.clamp (st.rhs c) = st.rhs c) (hfix : RoundFixed L st) :
    Converged L st := by
  refine ⟨hfix.cp_joinable, ?_⟩
  intro M c hM
  rcases h5 M c hM with h | h
  · rw [h]
  · obtain ⟨c', hc', hcc⟩ := h0 M c hM
    have hrule : (M, st.rhs (st.find c)) ∈ st.rules := ⟨c, c', hM, rfl, h, hc', hcc⟩
    refine ReflTransGen.single ⟨M, st.rhs (st.find c), hrule, le_rfl, ?_⟩
    rw [tsub_self, zero_add, hcanon]

/-- L13: completeness. Under confluence, with the asserted equalities, the
law instances, congruence and cancellation all joinable, `=_E` coincides
with joinability. The reverse direction is L5. -/
theorem completeness {L : Laws n} {S : Set (Monomial n × Monomial n)} {R : Rules n}
    (hconf : Confluent (Rw L R))
    (hS : ∀ M N, (M, N) ∈ S → Joinable (Rw L R) M N)
    (hlaw : ∀ M N, L.lawRel M N → Joinable (Rw L R) M N)
    (hcongr : ∀ M N X, Joinable (Rw L R) M N → Joinable (Rw L R) (M + X) (N + X))
    (hcancel : L.cancellative → ∀ M N X, Joinable (Rw L R) (M + X) (N + X) → Joinable (Rw L R) M N)
    (hsound : ∀ A B, (A, B) ∈ R → E L S A B) (M N : Monomial n) :
    E L S M N ↔ Joinable (Rw L R) M N := by
  constructor
  · intro h
    induction h with
    | ax h => exact hS _ _ h
    | refl M => exact ⟨M, ReflTransGen.refl, ReflTransGen.refl⟩
    | symm _ ih => obtain ⟨P, h₁, h₂⟩ := ih; exact ⟨P, h₂, h₁⟩
    | trans _ _ ih₁ ih₂ =>
      obtain ⟨P, h₁, h₂⟩ := ih₁
      obtain ⟨Q, h₃, h₄⟩ := ih₂
      obtain ⟨T, h₅, h₆⟩ := hconf _ _ _ h₂ h₃
      exact ⟨T, h₁.trans h₅, h₄.trans h₆⟩
    | congr X _ ih => exact hcongr _ _ X ih
    | law h => exact hlaw _ _ h
    | cancel hc _ ih => exact hcancel hc _ _ _ ih
  · rintro ⟨P, h₁, h₂⟩
    exact E.trans (Rw_rtg_sound hsound h₁) (E.symm (Rw_rtg_sound hsound h₂))

/-- A normal form rewrites only to itself. -/
theorem rtg_of_normal {α : Type*} {r : α → α → Prop} {a b : α} (hnf : ∀ c, ¬ r a c)
    (h : ReflTransGen r a b) : a = b := by
  rcases h.cases_head with h | ⟨c, hc, -⟩
  · exact h
  · exact absurd hc (hnf c)

/-- Corollary of L13 (sketch (e), last sentence): in a converged,
congruence-closed state whose right-hand sides are normal forms, two active
nodes that are `=_E`-equal are in one class. -/
theorem same_class {L : Laws n} {S : Set (Monomial n × Monomial n)} {st : State n}
    (hconv : Converged L st) (hconf : Confluent (Rw L st.rules)) (h0 : I0 st)
    (hnf : ∀ c P, ¬ Rw L st.rules (st.rhs (st.find c)) P)
    (hcc : ∀ P c d, (P, c) ∈ st.nodes → (P, d) ∈ st.nodes → st.find c = st.find d)
    (hjoin : ∀ M N, E L S M N → Joinable (Rw L st.rules) M N)
    {M N : Monomial n} {c d : Fin n} (hM : (M, c) ∈ st.active) (hN : (N, d) ∈ st.active)
    (hMN : E L S M N) : st.find c = st.find d := by
  obtain ⟨P, hMP, hNP⟩ := hjoin M N hMN
  have hMr := hconv.nodes_reduce M c hM
  have hNr := hconv.nodes_reduce N d hN
  obtain ⟨Q, hrQ, hPQ⟩ := hconf _ _ _ hMr hMP
  have hrQ' := rtg_of_normal (hnf c) hrQ
  obtain ⟨T, hrT, hPT⟩ := hconf _ _ _ hNr hNP
  have hrT' := rtg_of_normal (hnf d) hrT
  obtain ⟨U, hQU, hTU⟩ := hconf _ _ _ hPQ hPT
  rw [← hrQ'] at hQU
  rw [← hrT'] at hTU
  have e₁ := rtg_of_normal (hnf c) hQU
  have e₂ := rtg_of_normal (hnf d) hTU
  obtain ⟨c', hc', hcc'⟩ := h0 c
  obtain ⟨d', hd', hdd'⟩ := h0 d
  have := hcc _ c' d' hc' (by rw [e₁, ← e₂]; exact hd')
  rw [hcc', hdd'] at this
  exact this

/-! ## L14-L16: termination of the round sequence -/

/-- L14, Dickson's lemma for monomials over `Fin n`
(`Pi.wellQuasiOrderedLE` in Mathlib): every infinite sequence has
`i < j` with `l i ⊆ l j`. -/
theorem dickson (l : ℕ → Monomial n) : ∃ i j, i < j ∧ l i ≤ l j := by
  obtain ⟨i, j, hij, h⟩ :=
    (Pi.wellQuasiOrderedLE (ι := Fin n) (α := fun _ => ℕ)).wqo (fun i c => (l i).count c)
  exact ⟨i, j, hij, Multiset.le_iff_count.2 h⟩

/-- L14, Kapur's Theorem 2 adapted (sketch (d)): a completion run adds left
sides `l i` that are irreducible by the rules alive when they are added,
and retires a rule only when a newly added left side reduces it; such a run
is finite. `alive i j` says the rule added at step `i` is still active at
step `j`. -/
theorem kapur_termination (l : ℕ → Monomial n) (alive : ℕ → ℕ → Prop)
    (hself : ∀ i, alive i i)
    (hirr : ∀ i j, i < j → alive i j → ¬ l i ≤ l j)
    (hrem : ∀ i k, i < k → alive i (k - 1) → ¬ alive i k → l k ≤ l i ∧ l k ≠ l i) :
    False := by
  classical
  obtain ⟨i, j, hij, hle⟩ := dickson l
  have key : ∀ m i, j - i = m → i < j → l i ≤ l j → False := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro i hm hij hle
      have hnot : ¬ alive i j := fun h => hirr i j hij h hle
      have hex : ∃ k, i < k ∧ k ≤ j ∧ ¬ alive i k := ⟨j, hij, le_rfl, hnot⟩
      obtain ⟨k, hk, hmin⟩ : ∃ k, (i < k ∧ k ≤ j ∧ ¬ alive i k) ∧
          ∀ k', k' < k → ¬ (i < k' ∧ k' ≤ j ∧ ¬ alive i k') :=
        ⟨Nat.find hex, Nat.find_spec hex, fun k' hk' => Nat.find_min hex hk'⟩
      have halive : alive i (k - 1) := by
        by_cases h : k - 1 = i
        · rw [h]; exact hself i
        · by_contra hna
          exact hmin (k - 1) (by omega) ⟨by omega, by omega, hna⟩
      obtain ⟨hlek, hnek⟩ := hrem i k hk.1 halive hk.2.2
      by_cases hkj : k = j
      · subst hkj; exact hnek (le_antisymm hlek hle)
      · exact ih (j - k) (by omega) k rfl (by omega) (hlek.trans hle)
  exact key (j - i) i rfl hij hle

/-- Children of a rewrite reduct come from the redex or from a rule's
right-hand side. -/
theorem Rw_mem {L : Laws n} {st : State n} {pool : Finset (Fin n)} (h : I4 pool st)
    {M N : Monomial n} (hM : ∀ x ∈ M, x ∈ pool) (hMN : Rw L st.rules M N) :
    ∀ x ∈ N, x ∈ pool := by
  obtain ⟨A, B, ⟨c, c', -, hB, -, hBn, -⟩, hA, rfl⟩ := hMN
  intro x hx
  have hx' := Multiset.mem_of_le (L.clamp_le _) hx
  rcases Multiset.mem_add.1 hx' with hx' | hx'
  · exact hM x (Multiset.mem_of_le tsub_le_self hx')
  · exact h B c' hBn x hx'

theorem Rw_rtg_mem {L : Laws n} {st : State n} {pool : Finset (Fin n)} (h : I4 pool st)
    {M N : Monomial n} (hM : ∀ x ∈ M, x ∈ pool) (hMN : ReflTransGen (Rw L st.rules) M N) :
    ∀ x ∈ N, x ∈ pool := by
  induction hMN with
  | refl => exact hM
  | tail _ hstep ih => exact Rw_mem h ih hstep

/-- L15: the fixed summand pool I4 is preserved by every inference, since a
minted monomial is built from the children of existing nodes. -/
theorem Infer_I4 {L : Laws n} {st st' : State n} {pool : Finset (Fin n)}
    (hinf : Infer L st st') (h : I4 pool st) : I4 pool st' := by
  cases hinf with
  | mint hM hMN _ =>
    intro P a hP
    simp only [State.addNode, Set.mem_insert_iff, Prod.mk.injEq] at hP
    rcases hP with ⟨rfl, rfl⟩ | hP
    · exact Rw_rtg_mem h (h _ _ hM) hMN
    · exact h P a hP
  | joinMerge _ _ _ => exact h
  | cancelMerge _ _ _ _ _ _ => exact h
  | retire _ => exact h
  | unretire _ _ => exact h
  | setRhs _ => exact h

/-! ## Un-retirement

The engine clears `FLAG_AC_COLLAPSED` on a node that completion materializes
again or that recanonization changes, and refreshes the class's stored
minimal monomial with it (`materialize`, `recanonize_node`:
`refresh_min_monomial`). Modelled as `Infer.unretire` followed by
`Infer.setRhs (st.refreshRhs M c)`. Nodes and partition do not change, so I2
and I4 pass through (`Infer_I2`, `Infer_I4`); I0 and I5 need the refresh. -/

/-- Un-retiring keeps I0: nodes, partition and right-hand sides are unchanged. -/
theorem unretire_I0 {st : State n} (h : I0 st) (M : Monomial n) (c : Fin n) :
    I0 (st.unretire M c) := h

/-- The refresh keeps I0 when the node active again is a node: the class of
`c` stores `M`, a node of that class, or keeps its own right-hand side. -/
theorem refreshRhs_I0 {st : State n} (h : I0 st) {M : Monomial n} {c : Fin n}
    (hM : (M, c) ∈ st.nodes) : I0 { st with rhs := st.refreshRhs M c } := by
  intro d
  simp only [State.refreshRhs]
  by_cases hd : st.find d = st.find c ∧ degLex (st.rhs (st.find c)) M
  · rw [if_pos hd]
    exact ⟨c, hM, hd.1.symm⟩
  · rw [if_neg hd]
    exact h d

/-- Un-retiring without the refresh can break I5: the node active again may be
below the stored right-hand side. With the refresh I5 holds again. The
right-hand side of the class of `c` is `M` when `M` is below the old one, and
every active node of that class was at or above the old one. -/
theorem unretire_refresh_I5 {st : State n} (h5 : I5 st) (M : Monomial n) (c : Fin n) :
    I5 { st.unretire M c with rhs := st.refreshRhs M c } := by
  intro N d hN
  have hnodes : (N, d) ∈ st.nodes := hN.1
  have hcase : (N, d) ∈ st.retired → N = M ∧ d = c := by
    intro hret
    have hnot : (N, d) ∉ st.retired \ {(M, c)} := hN.2
    by_contra hne
    exact hnot ⟨hret, fun hmem => hne (Prod.mk.inj (Set.mem_singleton_iff.mp hmem))⟩
  show st.refreshRhs M c (st.find d) = N ∨ degLex N (st.refreshRhs M c (st.find d))
  unfold State.refreshRhs
  by_cases hdc : st.find d = st.find c
  · by_cases hlt : degLex (st.rhs (st.find c)) M
    · rw [if_pos ⟨hdc, hlt⟩]
      by_cases hret : (N, d) ∈ st.retired
      · exact Or.inl (hcase hret).1.symm
      · rcases h5 N d ⟨hnodes, hret⟩ with h | h
        · rw [hdc] at h; rw [← h]; exact Or.inr hlt
        · rw [hdc] at h; exact Or.inr (degLex_trans h hlt)
    · rw [if_neg (fun hh => hlt hh.2)]
      by_cases hret : (N, d) ∈ st.retired
      · obtain ⟨rfl, rfl⟩ := hcase hret
        rcases degLex_trichotomous N (st.rhs (st.find d)) with h | h | h
        · exact Or.inr h
        · exact Or.inl h.symm
        · exact absurd h hlt
      · exact h5 N d ⟨hnodes, hret⟩
  · rw [if_neg (fun hh => hdc hh.1)]
    by_cases hret : (N, d) ∈ st.retired
    · exact absurd (congrArg st.find (hcase hret).2) hdc
    · exact h5 N d ⟨hnodes, hret⟩

/-- The engine's un-retire is two inference steps. -/
theorem unretire_refresh_reachable {L : Laws n} {st : State n} {M : Monomial n} {c : Fin n}
    (hret : (M, c) ∈ st.retired) (hnf : ∀ P, ¬ Rw L st.rules M P) :
    Reachable L st { st.unretire M c with rhs := st.refreshRhs M c } :=
  Relation.ReflTransGen.tail (Relation.ReflTransGen.single (Infer.unretire hret hnf))
    (Infer.setRhs (st.refreshRhs M c))

/-! L16 (round termination) is proved in `Proofs/RunStabilizes.lean`
(`run_stabilizes'`) and re-exported from `Main.lean`. -/

end SemperProofs.CC
