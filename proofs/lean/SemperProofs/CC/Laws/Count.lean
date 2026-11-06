import SemperProofs.CC.Laws.Basic

/-!
# Count-threshold laws

The engine's nilpotent and idempotent normalizations act on each class
count independently: a map `φ : ℕ → ℕ` with a threshold `p` that fixes
counts below `p`, lands below `p`, and is invariant under the one-step
instance `aᵖ → aᵠ` (`step`). `CountMap` packages such a map; `toNF` reads
it as an `NFLaw` with generators `{aᵖ → aᵠ}`.
-/

namespace SemperProofs.CC

open Relation

variable {n : ℕ}

/-- A count map `φ` with threshold `p`: counts below `p` are fixed, outputs are below `p`,
and removing `p` copies while adding `q` does not change the output. -/
structure CountMap where
  φ : ℕ → ℕ
  p : ℕ
  q : ℕ
  q_lt : q < p
  fix : ∀ c, c < p → φ c = c
  bound : ∀ c, φ c < p
  step : ∀ c, p ≤ c → φ (c - p + q) = φ c

namespace CountMap

variable (C : CountMap)

/-- The normal form: apply `φ` to every count. -/
def nf (M : Monomial n) : Monomial n := ofCounts fun a => C.φ (M.count a)

/-- The one-step generators `aᵖ → aᵠ`. -/
def gen : Rules n :=
  {r | ∃ a : Fin n, r = (Multiset.replicate C.p a, Multiset.replicate C.q a)}

/-- Fixed monomials: every count is below `p`. -/
def Fixed (M : Monomial n) : Prop := ∀ a, M.count a < C.p

@[simp] theorem count_nf (M : Monomial n) (a : Fin n) :
    (C.nf M).count a = C.φ (M.count a) := by
  simp [nf]

theorem p_pos : 0 < C.p := lt_of_le_of_lt (Nat.zero_le _) C.q_lt

theorem φ_le (c : ℕ) : C.φ c ≤ c := by
  induction c using Nat.strong_induction_on with
  | _ c ih =>
    by_cases h : c < C.p
    · rw [C.fix c h]
    · rw [not_lt] at h
      rw [← C.step c h]
      have hq := C.q_lt
      have : c - C.p + C.q < c := by omega
      exact (ih _ this).trans this.le

theorem nf_le (M : Monomial n) : C.nf M ≤ M :=
  Multiset.le_iff_count.mpr fun a => by simp [C.φ_le]

theorem fixed_nf (M : Monomial n) : C.Fixed (C.nf M) := fun a => by simp [C.bound]

theorem fixed_sub (A M : Monomial n) (h : A ≤ M) (hM : C.Fixed M) : C.Fixed A :=
  fun a => lt_of_le_of_lt (Multiset.count_le_of_le a h) (hM a)

theorem nf_of_fixed (M : Monomial n) (hM : C.Fixed M) : C.nf M = M := by
  ext a; simp [C.fix _ (hM a)]

theorem fixed_iff_nf_eq (M : Monomial n) : C.Fixed M ↔ C.nf M = M :=
  ⟨C.nf_of_fixed M, fun h => h ▸ C.fixed_nf M⟩

/-- `M →*_gen nf M`: while some count reaches `p`, fire `aᵖ → aᵠ`. -/
theorem gen_reach (M : Monomial n) : ReflTransGen (Rw (plain n) C.gen) M (C.nf M) := by
  induction' h : Multiset.card M using Nat.strong_induction_on with k ih generalizing M
  by_cases hfix : C.Fixed M
  · rw [C.nf_of_fixed M hfix]
  · simp only [Fixed, not_forall, not_lt] at hfix
    obtain ⟨a, ha⟩ := hfix
    have hle : Multiset.replicate C.p a ≤ M := Multiset.le_count_iff_replicate_le.mp ha
    have hq := C.q_lt
    set M' := M - Multiset.replicate C.p a + Multiset.replicate C.q a with hM'
    have hstep : Rw (plain n) C.gen M M' := Rw_plain_of_le ⟨a, rfl⟩ hle
    have hnf : C.nf M' = C.nf M := by
      ext b
      simp only [count_nf, hM', Multiset.count_add, Multiset.count_sub, Multiset.count_replicate]
      by_cases hb : a = b
      · subst hb; simpa only [ite_true] using C.step _ ha
      · simp [hb]
    have hlt : M' < M := by
      refine lt_of_le_of_ne (Multiset.le_iff_count.mpr fun b => ?_) fun heq => ?_
      · simp only [hM', Multiset.count_add, Multiset.count_sub, Multiset.count_replicate]
        by_cases hb : a = b
        · subst hb; simp only [ite_true]; omega
        · simp [hb]
      · have := congrArg (Multiset.count a) heq
        simp only [hM', Multiset.count_add, Multiset.count_sub, Multiset.count_replicate_self] at this
        omega
    have hcard : Multiset.card M' < k := h ▸ Multiset.card_lt_card hlt
    rw [← hnf]
    exact ReflTransGen.head hstep (ih _ hcard M' rfl)

theorem gen_nf (L R : Monomial n) (h : (L, R) ∈ C.gen) : C.nf L = R ∧ R ≠ L := by
  obtain ⟨a, ha⟩ := h
  simp only [Prod.mk.injEq] at ha
  obtain ⟨rfl, rfl⟩ := ha
  have hq := C.q_lt
  constructor
  · ext b
    simp only [count_nf, Multiset.count_replicate]
    split_ifs with hb
    · have := C.step C.p le_rfl
      simp only [Nat.sub_self, Nat.zero_add] at this
      rw [← this, C.fix _ C.q_lt]
    · exact C.fix 0 C.p_pos
  · intro heq
    have := congrArg (Multiset.count a) heq
    simp only [Multiset.count_replicate_self] at this
    omega

/-- The `NFLaw` of a count map. -/
def toNF (cancel : Prop) : NFLaw n where
  nf := C.nf
  gen := C.gen
  Fixed := C.Fixed
  cancellative := cancel
  nf_le := C.nf_le
  fixed_nf := C.fixed_nf
  fixed_sub := C.fixed_sub
  nf_of_fixed := C.nf_of_fixed
  gen_reach := C.gen_reach
  gen_nf := C.gen_nf

@[simp] theorem toNF_nf (cancel : Prop) (M : Monomial n) : (C.toNF (n := n) cancel).nf M = C.nf M := rfl

@[simp] theorem toNF_gen (cancel : Prop) : (C.toNF (n := n) cancel).gen = C.gen := rfl

/-! ## Overlaps and critical pairs with the generators -/

/-- Two generators that share an element are the same generator. -/
theorem gen_gen {r₁ r₂ : Monomial n × Monomial n} (h₁ : r₁ ∈ C.gen) (h₂ : r₂ ∈ C.gen)
    (hov : Overlap r₁.1 r₂.1) : r₁ = r₂ := by
  obtain ⟨a, rfl⟩ := h₁
  obtain ⟨b, rfl⟩ := h₂
  obtain ⟨x, hx, hy⟩ := hov
  rw [Multiset.mem_replicate] at hx hy
  obtain ⟨-, rfl⟩ := hx
  obtain ⟨-, rfl⟩ := hy
  rfl

/-- A rule left side overlaps `aᵖ` exactly when it contains `a`. -/
theorem overlap_gen_iff (A : Monomial n) (a : Fin n) :
    Overlap A (Multiset.replicate C.p a) ↔ a ∈ A := by
  constructor
  · rintro ⟨x, hx, hy⟩
    rw [Multiset.mem_replicate] at hy
    exact hy.2 ▸ hx
  · intro h
    exact ⟨a, h, Multiset.mem_replicate.mpr ⟨C.p_pos.ne', rfl⟩⟩

set_option linter.unusedVariables false in
/-- The rule-generator critical pair of `(A, B)` with `aᵖ → aᵠ`, for `A` fixed and `a ∈ A`
(the hypothesis `ha` is not needed for the equation; it is kept for the intended use). -/
theorem cp_rule_gen {A B : Monomial n} {a : Fin n} (hA : C.Fixed A) (ha : a ∈ A) :
    criticalPair (plain n) (A, B) (Multiset.replicate C.p a, Multiset.replicate C.q a) =
      (B + Multiset.replicate (C.p - A.count a) a,
        A.filter (· ≠ a) + Multiset.replicate C.q a) := by
  have hlt := hA a
  have hq := C.q_lt
  simp only [criticalPair, plain_clamp]
  refine Prod.ext ?_ ?_ <;> ext b <;>
    simp only [Multiset.count_add, Multiset.count_sub, Multiset.count_union,
      Multiset.count_replicate, Multiset.count_filter]
  · by_cases hb : a = b
    · subst hb; simp only [ite_true]; omega
    · simp [hb]
  · by_cases hb : a = b
    · subst hb; simp only [ite_true, ne_eq, not_true_eq_false, ite_false]; omega
    · simp [hb, Ne.symm hb]

end CountMap

end SemperProofs.CC
