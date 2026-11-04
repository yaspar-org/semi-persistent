import SemperProofs.CC.Laws.Count

/-!
# The idempotent law `{a, a} = {a}`

The engine's ACI normalization (`nary_canon.rs:98-104`) dedups the child
multiset: every count `c ↦ min c 1`. This is the count map with threshold
`p := 2` and `q := 1`, so the generators are `{a, a} → {a}`. `clamp` is
`Multiset.dedup` (`idempotent_clamp_eq_dedup`).
-/

namespace SemperProofs.CC

open Relation

variable {n : ℕ}

/-- The count map `c ↦ min c 1`. -/
def idempotentMap : CountMap where
  φ c := min c 1
  p := 2
  q := 1
  q_lt := by omega
  fix c h := by omega
  bound c := by omega
  step c h := by omega

/-- The idempotent law as an `NFLaw`. -/
def idempotentNF (cancel : Prop) : NFLaw n := idempotentMap.toNF cancel

/-- The idempotent law as a `Laws`. -/
def Laws.idempotent (cancel : Prop) : Laws n := (idempotentNF cancel).toLaws

variable {cancel : Prop}

theorem idempotent_clamp (M : Monomial n) :
    (Laws.idempotent cancel).clamp M = ofCounts fun a => min (M.count a) 1 := rfl

@[simp] theorem count_idempotent_clamp (M : Monomial n) (a : Fin n) :
    ((Laws.idempotent cancel).clamp M).count a = min (M.count a) 1 := by
  rw [idempotent_clamp]; simp

theorem idempotent_clamp_eq_dedup (M : Monomial n) :
    (Laws.idempotent cancel).clamp M = M.dedup := by
  ext a
  rw [count_idempotent_clamp, Multiset.count_dedup]
  split_ifs with h
  · have := Multiset.count_pos.mpr h; omega
  · simp [Multiset.count_eq_zero.mpr h]

theorem idempotent_hlaw : ∀ P Q, (Laws.idempotent (n := n) cancel).lawRel P Q → degLex P Q :=
  (idempotentNF cancel).toLaws_hlaw

theorem idempotent_hnf_ax : ∀ M N, ¬ Rw (plain n) (Laws.idempotent cancel).axRules
    ((Laws.idempotent cancel).clamp M) N :=
  (idempotentNF cancel).toLaws_hnf_ax

theorem idempotentNF_gen_iff (r : Monomial n × Monomial n) :
    r ∈ (idempotentNF cancel).gen ↔ ∃ a, r = (Multiset.replicate 2 a, {a}) := by
  constructor <;> rintro ⟨a, rfl⟩ <;> exact ⟨a, rfl⟩

/-- The rule-generator critical pair of `(A, B)` with `{a, a} → {a}`, for `A` duplicate-free. -/
theorem idempotent_cp_rule_gen {A B : Monomial n} {a : Fin n} (hA : A.Nodup) (ha : a ∈ A) :
    criticalPair (plain n) (A, B) (Multiset.replicate 2 a, {a}) = (B + {a}, A) := by
  have hfix : idempotentMap.Fixed A := fun b => by
    have := Multiset.nodup_iff_count_le_one.mp hA b
    show A.count b < 2
    omega
  have h1 : A.count a = 1 := Multiset.count_eq_one_of_mem hA ha
  have := idempotentMap.cp_rule_gen (B := B) hfix ha
  simp only [idempotentMap, h1] at this
  rw [show (2 : ℕ) - 1 = 1 from rfl, Multiset.replicate_one] at this
  rw [this]
  refine Prod.ext rfl ?_
  show A.filter (· ≠ a) + Multiset.replicate 1 a = A
  ext b
  simp only [Multiset.count_add, Multiset.count_filter, Multiset.count_replicate]
  by_cases hb : b = a
  · subst hb; simp [h1]
  · simp [hb, Ne.symm hb]

end SemperProofs.CC
