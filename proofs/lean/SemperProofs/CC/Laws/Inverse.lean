import SemperProofs.CC.Laws.Basic

/-!
# The inverse law `{x, inv x} → ∅`

The engine's `cancel_inverse_pairs` (`nary_canon.rs:147-214`, `cancel_by`)
walks the child list, sorted by class, once in ascending order. At class
`x` with a positive count and `inverse_of x = some y`: if `y = x` the count
of `x` is reduced modulo 2 (`nary_canon.rs:189-193`); otherwise `y` is
binary-searched and `min(count x, count y)` is subtracted from both
(`nary_canon.rs:195-207`). Zeroed entries are dropped at the end
(`nary_canon.rs:209-212`). An absent class behaves like count `0`.

`invWalk` is that walk on monomials, `invGen` the one-step instances
`{x, inv x} → ∅`, and `inverseNF` packages them as an `NFLaw`. The
rule-law critical pairs have the explicit shape `cp_rule_invGen_left` /
`cp_rule_invGen_right`, two generators overlap only when they are equal
provided the inverse graph is a matching (`invGen_gen_gen`), and
`invGen_cp_not_joinable` shows the matching hypothesis is needed.
-/

namespace SemperProofs.CC

open Relation

variable {n : ℕ}

/-! ## The walk -/

/-- One visit of the walk at class `x` (`nary_canon.rs:182-207`). -/
def cancelAt (inv : Fin n → Option (Fin n)) (M : Monomial n) (x : Fin n) : Monomial n :=
  match inv x with
  | none => M
  | some y =>
    if y = x then M - Multiset.replicate (2 * (M.count x / 2)) x
    else M - (Multiset.replicate (min (M.count x) (M.count y)) x
              + Multiset.replicate (min (M.count x) (M.count y)) y)

/-- The engine's walk: ascending class order, `nary_canon.rs:168-214`. -/
def invWalk (inv : Fin n → Option (Fin n)) (M : Monomial n) : Monomial n :=
  (List.finRange n).foldl (cancelAt inv) M

/-- No cancellable pair remains. -/
def InvNormal (inv : Fin n → Option (Fin n)) (M : Monomial n) : Prop :=
  ∀ x y, inv x = some y → (y = x → M.count x ≤ 1) ∧ (y ≠ x → M.count x = 0 ∨ M.count y = 0)

/-- The one-step law instances `{x, inv x} → ∅` (`{x, x} → ∅` for a self-inverse class). -/
def invGen (inv : Fin n → Option (Fin n)) : Rules n :=
  {r | ∃ x y, inv x = some y ∧ r = (({x, y} : Monomial n), 0)}

/-- The inverse graph is a matching: no two classes share an inverse, and
the inverse of an inverse, when present, is the original class. -/
structure InvMatching (inv : Fin n → Option (Fin n)) : Prop where
  inj : ∀ x z y, inv x = some y → inv z = some y → x = z
  symm : ∀ x y, inv x = some y → inv y = none ∨ inv y = some x

/-! ### Counts of pairs -/

theorem count_pair (x y z : Fin n) :
    ({x, y} : Monomial n).count z = (if z = x then 1 else 0) + (if z = y then 1 else 0) := by
  simp only [Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton]
  omega

/-! ## 1. The walk only removes children -/

theorem cancelAt_le (inv : Fin n → Option (Fin n)) (M : Monomial n) (x : Fin n) :
    cancelAt inv M x ≤ M := by
  unfold cancelAt
  split
  · exact le_rfl
  · split <;> exact tsub_le_self

theorem foldl_cancelAt_le (inv : Fin n → Option (Fin n)) (l : List (Fin n)) (M : Monomial n) :
    l.foldl (cancelAt inv) M ≤ M := by
  induction l generalizing M with
  | nil => exact le_rfl
  | cons a l ih => exact (ih _).trans (cancelAt_le inv M a)

theorem invWalk_le (inv : Fin n → Option (Fin n)) (M : Monomial n) : invWalk inv M ≤ M :=
  foldl_cancelAt_le inv _ M

/-! ## 2. The walk's output is normal -/

/-- The `InvNormal` condition for one class `x`. -/
def InvNormalAt (inv : Fin n → Option (Fin n)) (M : Monomial n) (x : Fin n) : Prop :=
  ∀ y, inv x = some y → (y = x → M.count x ≤ 1) ∧ (y ≠ x → M.count x = 0 ∨ M.count y = 0)

theorem invNormalAt_sub {inv : Fin n → Option (Fin n)} {A M : Monomial n} {x : Fin n}
    (hle : A ≤ M) (h : InvNormalAt inv M x) : InvNormalAt inv A x := by
  intro y hy
  obtain ⟨h1, h2⟩ := h y hy
  refine ⟨fun e => (Multiset.count_le_of_le x hle).trans (h1 e), fun e => ?_⟩
  rcases h2 e with h0 | h0
  · exact Or.inl (Nat.le_zero.mp (h0 ▸ Multiset.count_le_of_le x hle))
  · exact Or.inr (Nat.le_zero.mp (h0 ▸ Multiset.count_le_of_le y hle))

theorem invNormalAt_cancelAt (inv : Fin n → Option (Fin n)) (M : Monomial n) (x : Fin n) :
    InvNormalAt inv (cancelAt inv M x) x := by
  intro y hy
  simp only [cancelAt, hy]
  by_cases hyx : y = x
  · subst hyx
    simp only [↓reduceIte, Multiset.count_sub, Multiset.count_replicate_self, ne_eq, not_true,
      false_implies, and_true]
    intro _
    omega
  · simp only [hyx, ↓reduceIte]
    refine ⟨fun e => e.elim, fun _ => ?_⟩
    simp only [Multiset.count_sub, Multiset.count_add, Multiset.count_replicate, hyx,
      Ne.symm hyx, ↓reduceIte]
    omega

theorem invNormalAt_foldl (inv : Fin n → Option (Fin n)) (l : List (Fin n)) (M : Monomial n)
    (x : Fin n) (hx : x ∈ l) : InvNormalAt inv (l.foldl (cancelAt inv) M) x := by
  induction l generalizing M with
  | nil => exact absurd hx (List.not_mem_nil)
  | cons a l ih =>
    rw [List.foldl_cons]
    by_cases hax : x = a
    · subst hax
      exact invNormalAt_sub (foldl_cancelAt_le inv l _) (invNormalAt_cancelAt inv M x)
    · exact ih _ (List.mem_of_ne_of_mem hax hx)

theorem invNormal_invWalk (inv : Fin n → Option (Fin n)) (M : Monomial n) :
    InvNormal inv (invWalk inv M) :=
  fun x => invNormalAt_foldl inv _ M x (List.mem_finRange x)

/-! ## 3. Normality is downward closed -/

theorem invNormal_sub {inv : Fin n → Option (Fin n)} {A M : Monomial n} (hle : A ≤ M)
    (h : InvNormal inv M) : InvNormal inv A :=
  fun x => invNormalAt_sub hle (h x)

/-! ## 4. The walk fixes normal monomials -/

theorem cancelAt_of_invNormal {inv : Fin n → Option (Fin n)} {M : Monomial n}
    (h : InvNormal inv M) (x : Fin n) : cancelAt inv M x = M := by
  unfold cancelAt
  split
  · rfl
  · rename_i y hy
    obtain ⟨h1, h2⟩ := h x y hy
    split
    · rename_i hyx
      have : M.count x / 2 = 0 := Nat.div_eq_of_lt (by have := h1 hyx; omega)
      rw [this, Nat.mul_zero, Multiset.replicate_zero, tsub_zero]
    · rename_i hyx
      have : min (M.count x) (M.count y) = 0 := by
        rcases h2 hyx with h0 | h0 <;> simp [h0]
      simp only [this, Multiset.replicate_zero, add_zero, tsub_zero]

theorem invWalk_of_invNormal {inv : Fin n → Option (Fin n)} {M : Monomial n}
    (h : InvNormal inv M) : invWalk inv M = M := by
  unfold invWalk
  induction List.finRange n with
  | nil => rfl
  | cons a l ih => rw [List.foldl_cons, cancelAt_of_invNormal h, ih]

/-! ## 5. The walk is reached by the generators -/

/-- `k` applications of a rule `L → ∅` from any `M ⊇ k • L`. -/
theorem rtg_sub_nsmul {R : Rules n} {L : Monomial n} (hL : (L, 0) ∈ R) (M : Monomial n) :
    ∀ k : ℕ, k • L ≤ M → ReflTransGen (Rw (plain n) R) M (M - k • L) := by
  intro k
  induction k with
  | zero => intro _; rw [zero_smul, tsub_zero]
  | succ k ih =>
    intro hk
    rw [succ_nsmul] at hk ⊢
    have hle : L ≤ M - k • L := le_tsub_of_add_le_left hk
    refine (ih (le_of_add_le_left hk)).tail ?_
    have := Rw_plain_of_le (U := M - k • L) hL hle
    rwa [add_zero, tsub_tsub] at this

theorem cancelAt_reach (inv : Fin n → Option (Fin n)) (M : Monomial n) (x : Fin n) :
    ReflTransGen (Rw (plain n) (invGen inv)) M (cancelAt inv M x) := by
  unfold cancelAt
  split
  · exact ReflTransGen.refl
  · rename_i y hy
    have hmem : (({x, y} : Monomial n), 0) ∈ invGen inv := ⟨x, y, hy, rfl⟩
    split
    · rename_i hyx
      subst hyx
      have e : Multiset.replicate (2 * (M.count y / 2)) y = (M.count y / 2) • ({y, y} : Monomial n) := by
        ext z
        rw [Multiset.count_nsmul, Multiset.count_replicate, count_pair]
        by_cases hz : y = z
        · subst hz; simp [mul_comm]
        · simp [hz, Ne.symm hz]
      rw [e]
      refine rtg_sub_nsmul hmem M _ ?_
      rw [← e, ← Multiset.le_count_iff_replicate_le]
      exact Nat.mul_div_le _ _
    · rename_i hyx
      have e : Multiset.replicate (min (M.count x) (M.count y)) x
          + Multiset.replicate (min (M.count x) (M.count y)) y
          = min (M.count x) (M.count y) • ({x, y} : Monomial n) := by
        ext z
        rw [Multiset.count_nsmul, Multiset.count_add, Multiset.count_replicate,
          Multiset.count_replicate, count_pair]
        by_cases hzx : z = x
        · subst hzx; simp [hyx, Ne.symm hyx]
        · by_cases hzy : z = y
          · subst hzy; simp [hyx, Ne.symm hyx]
          · simp [hzx, hzy, Ne.symm hzx, Ne.symm hzy]
      rw [e]
      refine rtg_sub_nsmul hmem M _ ?_
      rw [← e, Multiset.le_iff_count]
      intro z
      rw [Multiset.count_add, Multiset.count_replicate, Multiset.count_replicate]
      by_cases hzx : x = z
      · subst hzx
        simp only [hyx, ↓reduceIte]
        omega
      · by_cases hzy : y = z
        · subst hzy
          simp only [hzx, ↓reduceIte]
          omega
        · simp only [hzx, hzy, ↓reduceIte]
          omega

theorem foldl_cancelAt_reach (inv : Fin n → Option (Fin n)) (l : List (Fin n)) (M : Monomial n) :
    ReflTransGen (Rw (plain n) (invGen inv)) M (l.foldl (cancelAt inv) M) := by
  induction l generalizing M with
  | nil => exact ReflTransGen.refl
  | cons a l ih => exact (cancelAt_reach inv M a).trans (ih _)

theorem invWalk_reach (inv : Fin n → Option (Fin n)) (M : Monomial n) :
    ReflTransGen (Rw (plain n) (invGen inv)) M (invWalk inv M) :=
  foldl_cancelAt_reach inv _ M

/-! ## 6. The walk sends a generator's left side to `∅` -/

theorem cancelAt_zero (inv : Fin n → Option (Fin n)) (z : Fin n) : cancelAt inv 0 z = 0 :=
  Multiset.le_zero.mp (cancelAt_le inv 0 z)

theorem foldl_cancelAt_zero (inv : Fin n → Option (Fin n)) (l : List (Fin n)) :
    l.foldl (cancelAt inv) 0 = 0 :=
  Multiset.le_zero.mp (foldl_cancelAt_le inv l 0)

/-- The visit at `x` empties `{x, inv x}`. -/
theorem cancelAt_pair_self {inv : Fin n → Option (Fin n)} {x y : Fin n} (hxy : inv x = some y) :
    cancelAt inv ({x, y} : Monomial n) x = 0 := by
  simp only [cancelAt, hxy]
  by_cases hyx : y = x
  · subst hyx
    simp only [↓reduceIte]
    ext z
    rw [Multiset.count_sub, Multiset.count_replicate, count_pair, count_pair, Multiset.count_zero]
    by_cases hz : y = z
    · subst hz; simp
    · simp [hz, Ne.symm hz]
  · simp only [hyx, ↓reduceIte]
    ext z
    rw [Multiset.count_sub, Multiset.count_add, Multiset.count_replicate,
      Multiset.count_replicate, count_pair, count_pair, count_pair, Multiset.count_zero]
    by_cases hzx : z = x
    · subst hzx; simp [Ne.symm hyx, hyx]
    · by_cases hzy : z = y
      · subst hzy; simp [hyx, Ne.symm hyx]
      · simp [hzx, hzy, Ne.symm hzx, Ne.symm hzy]

/-- Every other visit keeps `{x, inv x}` or empties it. -/
theorem cancelAt_pair {inv : Fin n → Option (Fin n)} {x y : Fin n} (hxy : inv x = some y)
    (z : Fin n) :
    cancelAt inv ({x, y} : Monomial n) z = {x, y} ∨ cancelAt inv ({x, y} : Monomial n) z = 0 := by
  by_cases hzx : z = x
  · subst hzx; exact Or.inr (cancelAt_pair_self hxy)
  by_cases hzy : z = y
  · subst hzy
    unfold cancelAt
    split
    · exact Or.inl rfl
    · rename_i w hw
      split
      · rename_i hwz
        subst hwz
        left
        have : ({x, w} : Monomial n).count w / 2 = 0 := by
          simp [hzx, Ne.symm hzx]
        rw [this, Nat.mul_zero, Multiset.replicate_zero, tsub_zero]
      · rename_i hwz
        by_cases hwx : w = x
        · subst hwx
          right
          ext u
          rw [Multiset.count_sub, Multiset.count_add, Multiset.count_replicate,
            Multiset.count_replicate, count_pair, count_pair, count_pair, Multiset.count_zero]
          by_cases hux : u = w
          · subst hux; simp [hzx, Ne.symm hzx]
          · by_cases huz : u = z
            · subst huz; simp [hzx, Ne.symm hzx]
            · simp [hux, huz, Ne.symm hux, Ne.symm huz]
        · left
          have : min (({x, z} : Monomial n).count z) (({x, z} : Monomial n).count w) = 0 := by
            simp [hzx, Ne.symm hzx, hwx, hwz]
          simp only [this, Multiset.replicate_zero, add_zero, tsub_zero]
  · left
    have hz : ({x, y} : Monomial n).count z = 0 := by
      simp [hzx, hzy]
    unfold cancelAt
    split
    · rfl
    · split
      · rw [hz, Nat.zero_div, Nat.mul_zero, Multiset.replicate_zero, tsub_zero]
      · simp only [hz, Nat.zero_min, Multiset.replicate_zero, add_zero, tsub_zero]

theorem foldl_cancelAt_pair {inv : Fin n → Option (Fin n)} {x y : Fin n} (hxy : inv x = some y)
    (l : List (Fin n)) (hx : x ∈ l) : l.foldl (cancelAt inv) ({x, y} : Monomial n) = 0 := by
  induction l with
  | nil => exact absurd hx (List.not_mem_nil)
  | cons a l ih =>
    rw [List.foldl_cons]
    by_cases hax : a = x
    · subst hax
      rw [cancelAt_pair_self hxy, foldl_cancelAt_zero]
    · rcases cancelAt_pair hxy a with h | h
      · rw [h]
        exact ih (List.mem_of_ne_of_mem (Ne.symm hax) hx)
      · rw [h, foldl_cancelAt_zero]

theorem invWalk_pair {inv : Fin n → Option (Fin n)} {x y : Fin n} (hxy : inv x = some y) :
    invWalk inv ({x, y} : Monomial n) = 0 :=
  foldl_cancelAt_pair hxy _ (List.mem_finRange x)

/-! ## 7. The normal-form law set -/

/-- The inverse law as a normal-form law set: `nf := invWalk inv`,
`gen := invGen inv`, `Fixed := InvNormal inv`. -/
def inverseNF (inv : Fin n → Option (Fin n)) (cancel : Prop) : NFLaw n where
  nf := invWalk inv
  gen := invGen inv
  Fixed := InvNormal inv
  cancellative := cancel
  nf_le := invWalk_le inv
  fixed_nf := invNormal_invWalk inv
  fixed_sub _ _ h hM := invNormal_sub h hM
  nf_of_fixed _ hM := invWalk_of_invNormal hM
  gen_reach := invWalk_reach inv
  gen_nf L R h := by
    obtain ⟨x, y, hxy, hLR⟩ := h
    rw [Prod.mk.injEq] at hLR
    obtain ⟨rfl, rfl⟩ := hLR
    exact ⟨invWalk_pair hxy, (Multiset.cons_ne_zero (a := x) (m := {y})).symm⟩

/-- The inverse law as a `Laws`. -/
def Laws.inverse (inv : Fin n → Option (Fin n)) (cancel : Prop) : Laws n :=
  (inverseNF inv cancel).toLaws

/-! ## 8. The two law-only hypotheses of completeness -/

theorem inverse_hlaw (inv : Fin n → Option (Fin n)) (cancel : Prop) :
    ∀ P Q, (Laws.inverse inv cancel).lawRel P Q → degLex P Q :=
  (inverseNF inv cancel).toLaws_hlaw

theorem inverse_hnf_ax (inv : Fin n → Option (Fin n)) (cancel : Prop) :
    ∀ M N, ¬ Rw (plain n) (Laws.inverse inv cancel).axRules ((Laws.inverse inv cancel).clamp M) N :=
  (inverseNF inv cancel).toLaws_hnf_ax

/-! ## 9. Overlap with a pair -/

theorem overlap_pair_iff (A : Monomial n) (x y : Fin n) :
    Overlap A ({x, y} : Monomial n) ↔ x ∈ A ∨ y ∈ A := by
  constructor
  · rintro ⟨z, hzA, hz⟩
    rw [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact Or.inl hzA
    · exact Or.inr hzA
  · rintro (h | h)
    · exact ⟨x, h, Multiset.mem_cons_self x _⟩
    · exact ⟨y, h, Multiset.mem_cons_of_mem (Multiset.mem_singleton_self y)⟩

/-! ## 10. Two generators overlap only when equal (matching case) -/

theorem invGen_gen_gen {inv : Fin n → Option (Fin n)} (h : InvMatching inv)
    {r₁ r₂ : Monomial n × Monomial n} (h₁ : r₁ ∈ invGen inv) (h₂ : r₂ ∈ invGen inv)
    (hov : Overlap r₁.1 r₂.1) : r₁ = r₂ := by
  obtain ⟨x₁, y₁, hxy₁, rfl⟩ := h₁
  obtain ⟨x₂, y₂, hxy₂, rfl⟩ := h₂
  obtain ⟨z, hz₁, hz₂⟩ := hov
  simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hz₁ hz₂
  rcases hz₁ with rfl | rfl <;> rcases hz₂ with rfl | rfl
  · -- x₁ = x₂
    rw [hxy₁] at hxy₂
    rw [Option.some_inj.mp hxy₂]
  · -- x₁ = y₂: inv x₂ = some x₁; symm gives inv x₁ = some x₂
    rcases h.symm x₂ z hxy₂ with h0 | h0
    · rw [h0] at hxy₁; simp at hxy₁
    · rw [h0] at hxy₁
      rw [Option.some_inj.mp hxy₁, Multiset.pair_comm]
  · -- y₁ = x₂: inv x₁ = some x₂; symm gives inv x₂ = some x₁
    rcases h.symm x₁ z hxy₁ with h0 | h0
    · rw [h0] at hxy₂; simp at hxy₂
    · rw [h0] at hxy₂
      rw [Option.some_inj.mp hxy₂, Multiset.pair_comm]
  · -- y₁ = y₂: inj gives x₁ = x₂
    rw [h.inj x₁ x₂ z hxy₁ hxy₂]

/-! ## 11. Rule-law critical pairs -/

/-- The critical pair of a rule `(A, B)` with `{x, inv x} → ∅` when the overlap is at `x`. -/
theorem cp_rule_invGen_left {inv : Fin n → Option (Fin n)} {A B : Monomial n} {x y : Fin n}
    (hA : InvNormal inv A) (hxy : inv x = some y) (hx : x ∈ A) :
    criticalPair (plain n) (A, B) (({x, y} : Monomial n), 0) = (B + {y}, A.erase x) := by
  have hx1 : 1 ≤ A.count x := Multiset.one_le_count_iff_mem.mpr hx
  obtain ⟨h1, h2⟩ := hA x y hxy
  simp only [criticalPair, plain_clamp, add_zero]
  by_cases hyx : y = x
  · subst hyx
    have hc : A.count y = 1 := le_antisymm (h1 rfl) hx1
    refine Prod.ext ?_ ?_
    · ext z
      simp only [Multiset.count_add, Multiset.count_sub, Multiset.count_union, count_pair,
        Multiset.count_singleton]
      by_cases hz : z = y
      · subst hz; simp [hc]
        omega
      · simp [hz]
    · ext z
      simp only [Multiset.count_sub, Multiset.count_union, count_pair]
      by_cases hz : z = y
      · subst hz; simp [hc, Multiset.count_erase_self]
      · simp [hz, Multiset.count_erase_of_ne hz]
  · have hc : A.count y = 0 := by
      rcases h2 hyx with h0 | h0
      · omega
      · exact h0
    refine Prod.ext ?_ ?_
    · ext z
      simp only [Multiset.count_add, Multiset.count_sub, Multiset.count_union, count_pair,
        Multiset.count_singleton]
      by_cases hzx : z = x
      · subst hzx; simp [Ne.symm hyx]
        omega
      · by_cases hzy : z = y
        · subst hzy; simp [hyx, hc]
          omega
        · simp [hzx, hzy]
    · ext z
      simp only [Multiset.count_sub, Multiset.count_union, count_pair]
      by_cases hzx : z = x
      · subst hzx; simp [Ne.symm hyx, Multiset.count_erase_self]
        omega
      · by_cases hzy : z = y
        · subst hzy; simp [hyx, hc, Multiset.count_erase_of_ne hzx]
        · simp [hzx, hzy, Multiset.count_erase_of_ne hzx]

/-- The critical pair of a rule `(A, B)` with `{x, inv x} → ∅` when the overlap is at `inv x`. -/
theorem cp_rule_invGen_right {inv : Fin n → Option (Fin n)} {A B : Monomial n} {x y : Fin n}
    (hA : InvNormal inv A) (hxy : inv x = some y) (hne : x ≠ y) (hy : y ∈ A) :
    criticalPair (plain n) (A, B) (({x, y} : Monomial n), 0) = (B + {x}, A.erase y) := by
  have hy1 : 1 ≤ A.count y := Multiset.one_le_count_iff_mem.mpr hy
  obtain ⟨-, h2⟩ := hA x y hxy
  have hc : A.count x = 0 := by
    rcases h2 (Ne.symm hne) with h0 | h0
    · exact h0
    · omega
  simp only [criticalPair, plain_clamp, add_zero]
  refine Prod.ext ?_ ?_
  · ext z
    simp only [Multiset.count_add, Multiset.count_sub, Multiset.count_union, count_pair,
      Multiset.count_singleton]
    by_cases hzx : z = x
    · subst hzx; simp [hne, hc]
      omega
    · by_cases hzy : z = y
      · subst hzy; simp [Ne.symm hne]
        omega
      · simp [hzx, hzy]
  · ext z
    simp only [Multiset.count_sub, Multiset.count_union, count_pair]
    by_cases hzx : z = x
    · subst hzx; simp [hne, hc, Multiset.count_erase_of_ne hne]
    · by_cases hzy : z = y
      · subst hzy; simp [Ne.symm hne, Multiset.count_erase_self]
        omega
      · simp [hzx, hzy, Multiset.count_erase_of_ne hzy]

/-! ## 12. Without the matching hypothesis, generator pairs need not join -/

/-- `inv 0 = 1`, `inv 2 = 1`: two classes with the same inverse. -/
def inv3 : Fin 3 → Option (Fin 3) := ![some 1, none, some 1]

theorem inv3_not_matching : ¬ InvMatching inv3 := by
  intro h
  have := h.inj 0 2 1 (by decide) (by decide)
  exact absurd this (by decide)

theorem invGen_inv3_left : (({0, 1} : Monomial 3), 0) ∈ invGen inv3 :=
  ⟨0, 1, by decide, rfl⟩

theorem invGen_inv3_right : (({2, 1} : Monomial 3), 0) ∈ invGen inv3 :=
  ⟨2, 1, by decide, rfl⟩

theorem invGen_cp_example :
    criticalPair (plain 3) (({0, 1} : Monomial 3), 0) (({2, 1} : Monomial 3), 0)
      = (({2} : Monomial 3), ({0} : Monomial 3)) := by
  decide

/-- A monomial with at most one child is normal for every generator. -/
theorem invGen_normal_of_card_le_one (inv : Fin n → Option (Fin n)) {M : Monomial n}
    (hM : Multiset.card M ≤ 1) : ∀ N, ¬ Rw (plain n) (invGen inv) M N := by
  rintro N ⟨A, B, ⟨x, y, -, hAB⟩, hA, -⟩
  rw [Prod.mk.injEq] at hAB
  obtain ⟨rfl, -⟩ := hAB
  have := Multiset.card_le_card hA
  rw [Multiset.card_pair] at this
  omega

theorem invGen_cp_not_joinable :
    ¬ Joinable (Rw (plain 3) (invGen inv3)) ({2} : Monomial 3) ({0} : Monomial 3) := by
  rintro ⟨C, h₁, h₂⟩
  have e₁ := rtg_of_normal (invGen_normal_of_card_le_one inv3 (by simp)) h₁
  have e₂ := rtg_of_normal (invGen_normal_of_card_le_one inv3 (by simp)) h₂
  have : ({2} : Monomial 3) = {0} := e₁.trans e₂.symm
  exact absurd this (by decide)

end SemperProofs.CC
