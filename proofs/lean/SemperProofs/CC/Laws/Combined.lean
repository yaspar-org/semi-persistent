import SemperProofs.CC.Laws.Identity
import SemperProofs.CC.Laws.Nilpotent
import SemperProofs.CC.Laws.Idempotent
import SemperProofs.CC.Laws.Inverse

/-!
# The engine's composition: identity, then nilpotent, then inverse

`nary_canon::normalize_by` applies, after coalescing, the identity drop
(`nary_canon.rs:122-124`), the nilpotent clamp (`:125-132`) and the
inverse cancellation (`:133-137`), in that order. `Laws.combined` is that
composition as a normal-form law set, built with `NFLaw.comp`.

The composition is only a normal-form function for the pooled law
instances under `InvUnitFree`: no class other than the unit has its
inverse node in the unit class, and the unit's inverse node, if any, is
in the unit class. Otherwise the identity drop runs first and hides a
cancellable pair: with `inv x = u`, `{x, u}` drops to `{x}` while the
pair law gives `∅`, so `x = e` is a consequence the engine never derives
(`laws-repro/inv-into-unit.egg`, `unit-inverse.egg`, both fail
`check-eq`). `combined_counterexample` records the `{x, u}` case.

The two other compositions the engine accepts are here as well:
`Laws.identityInverse` (the identity drop, then the inverse cancellation;
`:identity :inverse` without `:nilpotent`), built with `NFLaw.comp` under
the same `InvUnitFree`, and `Laws.idempotentIdentity` (the identity drop
and the dedup; `:idempotent :identity`), built directly: the idempotent
generator at the unit, `{u, u} → {u}`, is not an instance of the composite
normal form (its left side normalizes to `∅`), so the generators are
`{u} → ∅` and `{a, a} → {a}` for `a ≠ u`.
-/

namespace SemperProofs.CC

open Relation

variable {n : ℕ}

/-- The unit class is isolated in the inverse graph, up to a self-loop. -/
def InvUnitFree (inv : Fin n → Option (Fin n)) (u : Fin n) : Prop :=
  ∀ x y, inv x = some y → (x = u ↔ y = u)

theorem unitDrop_replicate_self (u : Fin n) (k : ℕ) :
    unitDrop u (Multiset.replicate k u) = 0 := by
  ext a
  rw [count_unitDrop, Multiset.count_replicate, Multiset.count_zero]
  by_cases h : a = u <;> simp [h, Ne.symm]

/-- Identity then nilpotent. -/
def identityNilpotentNF (u : Fin n) (k : ℕ) (hk : 2 ≤ k) (cancel : Prop) : NFLaw n :=
  NFLaw.comp (identityNF u cancel) (nilpotentNF k hk cancel)
    (by
      rintro L R h
      rw [identityNF_gen_iff] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.injEq _ _ _ _ ▸ h
      exact (nilpotentNF k hk cancel).fixed_zero)
    (by
      intro L R h
      obtain ⟨a, h⟩ := (nilpotentNF_gen_iff (L, R)).mp h
      obtain ⟨rfl, rfl⟩ := Prod.mk.injEq _ _ _ _ ▸ h
      show (nilpotentNF k hk cancel).nf (unitDrop u (Multiset.replicate k a)) = 0
      by_cases hau : a = u
      · subst hau
        rw [unitDrop_replicate_self, NFLaw.nf_zero]
      · rw [unitDrop_of_notMem (by rw [Multiset.mem_replicate]; exact fun h => hau h.2.symm)]
        exact ((nilpotentNF k hk cancel).gen_nf _ _ ⟨a, rfl⟩).1)

/-- The nilpotent clamp fixes a pair of distinct classes, and a doubled
class when the order exceeds two. -/
theorem nilpotent_nf_pair (k : ℕ) (hk : 2 ≤ k) (cancel : Prop) (x y : Fin n)
    (h : x ≠ y ∨ 2 < k) :
    (nilpotentNF (n := n) k hk cancel).nf ({x, y} : Monomial n) = {x, y} := by
  apply (nilpotentNF k hk cancel).nf_of_fixed
  intro a
  show ({x, y} : Monomial n).count a < k
  rw [count_pair]
  rcases h with h | h
  · by_cases h1 : a = x
    · subst h1; simp only [ite_true, h, ite_false]; omega
    · simp only [h1, ite_false]; split_ifs <;> omega
  · split_ifs <;> omega

/-- Identity, then nilpotent, then inverse: the engine's `normalize`. -/
def combinedNF (u : Fin n) (k : ℕ) (hk : 2 ≤ k) (inv : Fin n → Option (Fin n))
    (cancel : Prop) (hu : InvUnitFree inv u) : NFLaw n :=
  NFLaw.comp (identityNilpotentNF u k hk cancel) (inverseNF inv cancel)
    (by
      rintro L R h
      rcases h with h | h
      · rw [identityNF_gen_iff] at h
        obtain ⟨rfl, rfl⟩ := Prod.mk.injEq _ _ _ _ ▸ h
        exact (inverseNF inv cancel).fixed_zero
      · obtain ⟨a, h⟩ := (nilpotentNF_gen_iff (L, R)).mp h
        obtain ⟨rfl, rfl⟩ := Prod.mk.injEq _ _ _ _ ▸ h
        exact (inverseNF inv cancel).fixed_zero)
    (by
      intro L R h
      obtain ⟨x, y, hxy, h⟩ := h
      obtain ⟨rfl, rfl⟩ := Prod.mk.injEq _ _ _ _ ▸ h
      show invWalk inv ((nilpotentNF k hk cancel).nf (unitDrop u {x, y})) = 0
      by_cases hxu : x = u
      · have hyu : y = u := (hu x y hxy).mp hxu
        have : unitDrop u ({x, y} : Monomial n) = 0 := by
          rw [hxu, hyu]
          have := unitDrop_replicate_self u 2
          simpa [Multiset.replicate_succ] using this
        rw [this, NFLaw.nf_zero]
        exact invWalk_of_invNormal (inverseNF inv cancel).fixed_zero
      · have hyu : y ≠ u := fun h => hxu ((hu x y hxy).mpr h)
        have hdrop : unitDrop u ({x, y} : Monomial n) = {x, y} := by
          apply unitDrop_of_notMem
          simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton, not_or]
          exact ⟨Ne.symm hxu, Ne.symm hyu⟩
        rw [hdrop]
        by_cases hk2 : x ≠ y ∨ 2 < k
        · rw [nilpotent_nf_pair k hk cancel x y hk2]
          exact invWalk_pair hxy
        · rw [not_or, not_not] at hk2
          obtain ⟨rfl, hk2⟩ := hk2
          have hk' : k = 2 := by omega
          subst hk'
          have : ({x, x} : Monomial n) = Multiset.replicate 2 x := by
            simp [Multiset.replicate_succ]
          have e : (nilpotentNF 2 hk cancel).nf (Multiset.replicate 2 x) = 0 :=
            ((nilpotentNF 2 hk cancel).gen_nf (Multiset.replicate 2 x) 0 ⟨x, rfl⟩).1
          rw [this, e]
          exact invWalk_of_invNormal (inverseNF inv cancel).fixed_zero)

/-- The engine's law set for an AC operator with identity `u`, nilpotent
order `k` and inverse `inv`. -/
def Laws.combined (u : Fin n) (k : ℕ) (hk : 2 ≤ k) (inv : Fin n → Option (Fin n))
    (cancel : Prop) (hu : InvUnitFree inv u) : Laws n :=
  (combinedNF u k hk inv cancel hu).toLaws

theorem combined_clamp (u : Fin n) (k : ℕ) (hk : 2 ≤ k) (inv : Fin n → Option (Fin n))
    (cancel : Prop) (hu : InvUnitFree inv u) (M : Monomial n) :
    (Laws.combined u k hk inv cancel hu).clamp M =
      invWalk inv (ofCounts fun a => (M.filter (· ≠ u)).count a % k) := rfl

theorem combined_hlaw (u : Fin n) (k : ℕ) (hk : 2 ≤ k) (inv : Fin n → Option (Fin n))
    (cancel : Prop) (hu : InvUnitFree inv u) :
    ∀ P Q, (Laws.combined u k hk inv cancel hu).lawRel P Q → degLex P Q :=
  (combinedNF u k hk inv cancel hu).toLaws_hlaw

theorem combined_hnf_ax (u : Fin n) (k : ℕ) (hk : 2 ≤ k) (inv : Fin n → Option (Fin n))
    (cancel : Prop) (hu : InvUnitFree inv u) :
    ∀ M N, ¬ Rw (plain n) (Laws.combined u k hk inv cancel hu).axRules
      ((Laws.combined u k hk inv cancel hu).clamp M) N :=
  (combinedNF u k hk inv cancel hu).toLaws_hnf_ax

theorem combinedNF_gen (u : Fin n) (k : ℕ) (hk : 2 ≤ k) (inv : Fin n → Option (Fin n))
    (cancel : Prop) (hu : InvUnitFree inv u) :
    (combinedNF u k hk inv cancel hu).gen = (unitGen u ∪ (nilpotentNF k hk cancel).gen) ∪ invGen inv :=
  rfl

/-! ## Identity, then inverse: `:identity :inverse` without `:nilpotent` -/

/-- Identity, then inverse: the engine's `normalize` without a nilpotent
order. The side condition is the one of `combinedNF`: under `InvUnitFree`
the identity drop hides no cancellable pair. -/
def identityInverseNF (u : Fin n) (inv : Fin n → Option (Fin n)) (cancel : Prop)
    (hu : InvUnitFree inv u) : NFLaw n :=
  NFLaw.comp (identityNF u cancel) (inverseNF inv cancel)
    (by
      rintro L R h
      rw [identityNF_gen_iff] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.injEq _ _ _ _ ▸ h
      exact (inverseNF inv cancel).fixed_zero)
    (by
      intro L R h
      obtain ⟨x, y, hxy, h⟩ := h
      obtain ⟨rfl, rfl⟩ := Prod.mk.injEq _ _ _ _ ▸ h
      show invWalk inv (unitDrop u {x, y}) = 0
      by_cases hxu : x = u
      · have hyu : y = u := (hu x y hxy).mp hxu
        have : unitDrop u ({x, y} : Monomial n) = 0 := by
          rw [hxu, hyu]
          have := unitDrop_replicate_self u 2
          simpa [Multiset.replicate_succ] using this
        rw [this]
        exact invWalk_of_invNormal (inverseNF inv cancel).fixed_zero
      · have hyu : y ≠ u := fun h => hxu ((hu x y hxy).mpr h)
        have hdrop : unitDrop u ({x, y} : Monomial n) = {x, y} := by
          apply unitDrop_of_notMem
          simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton, not_or]
          exact ⟨Ne.symm hxu, Ne.symm hyu⟩
        rw [hdrop]
        exact invWalk_pair hxy)

/-- The engine's law set for an AC operator with identity `u` and inverse
`inv`, without a nilpotent order. -/
def Laws.identityInverse (u : Fin n) (inv : Fin n → Option (Fin n)) (cancel : Prop)
    (hu : InvUnitFree inv u) : Laws n :=
  (identityInverseNF u inv cancel hu).toLaws

theorem identityInverse_clamp (u : Fin n) (inv : Fin n → Option (Fin n)) (cancel : Prop)
    (hu : InvUnitFree inv u) (M : Monomial n) :
    (Laws.identityInverse u inv cancel hu).clamp M = invWalk inv (M.filter (· ≠ u)) := rfl

theorem identityInverse_hlaw (u : Fin n) (inv : Fin n → Option (Fin n)) (cancel : Prop)
    (hu : InvUnitFree inv u) :
    ∀ P Q, (Laws.identityInverse u inv cancel hu).lawRel P Q → degLex P Q :=
  (identityInverseNF u inv cancel hu).toLaws_hlaw

theorem identityInverse_hnf_ax (u : Fin n) (inv : Fin n → Option (Fin n)) (cancel : Prop)
    (hu : InvUnitFree inv u) :
    ∀ M N, ¬ Rw (plain n) (Laws.identityInverse u inv cancel hu).axRules
      ((Laws.identityInverse u inv cancel hu).clamp M) N :=
  (identityInverseNF u inv cancel hu).toLaws_hnf_ax

theorem identityInverseNF_gen (u : Fin n) (inv : Fin n → Option (Fin n)) (cancel : Prop)
    (hu : InvUnitFree inv u) :
    (identityInverseNF u inv cancel hu).gen = unitGen u ∪ invGen inv := rfl

/-! ## Identity and idempotent: `:idempotent :identity`

The identity drop and the dedup act on each count independently and
commute. The idempotent generator at the unit, `{u, u} → {u}`, is not an
instance of the composite normal form (`{u, u}` normalizes to `∅`), so it
is left out of the generators; `{u} → ∅` derives it. -/

/-- The idempotent generators `{a, a} → {a}` of the classes other than `u`. -/
def idemGenNe (u : Fin n) : Rules n :=
  {r | ∃ a, a ≠ u ∧ r = (Multiset.replicate 2 a, ({a} : Monomial n))}

theorem idemGenNe_sub (u : Fin n) : idemGenNe u ⊆ idempotentMap.gen := by
  rintro r ⟨a, -, rfl⟩
  exact ⟨a, rfl⟩

/-- Every reduct under a decreasing rule set lies below the start. -/
theorem rtg_le_of_dec {R : Rules n} (hdec : ∀ A B, (A, B) ∈ R → B ≤ A) {X Y : Monomial n}
    (h : ReflTransGen (Rw (plain n) R) X Y) : Y ≤ X := by
  induction h with
  | refl => exact le_rfl
  | tail _ hs ih =>
    obtain ⟨A, B, hAB, hA, rfl⟩ := hs
    rw [plain_clamp]
    calc _ ≤ _ - A + A := add_le_add_right (hdec A B hAB) _
      _ = _ := tsub_add_cancel_of_le hA
      _ ≤ X := ih

/-- A path over a decreasing `R` from `X` is a path over `S` when every rule
of `R` that fits below `X` is in `S`. -/
theorem rtg_restrict {R S : Rules n} (hdec : ∀ A B, (A, B) ∈ R → B ≤ A) {X Y : Monomial n}
    (hS : ∀ A B, (A, B) ∈ R → A ≤ X → (A, B) ∈ S)
    (h : ReflTransGen (Rw (plain n) R) X Y) : ReflTransGen (Rw (plain n) S) X Y := by
  induction h with
  | refl => exact ReflTransGen.refl
  | @tail Y Z hXY hs ih =>
    obtain ⟨A, B, hAB, hA, rfl⟩ := hs
    exact ih.tail ⟨A, B, hS A B hAB (hA.trans (rtg_le_of_dec hdec hXY)), hA, rfl⟩

/-- Drop the unit, then dedup: the engine's normalization under
`:idempotent :identity`. -/
def idempotentIdentityNF (u : Fin n) (cancel : Prop) : NFLaw n where
  nf M := idempotentMap.nf (unitDrop u M)
  gen := unitGen u ∪ idemGenNe u
  Fixed M := u ∉ M ∧ idempotentMap.Fixed M
  cancellative := cancel
  nf_le M := (idempotentMap.nf_le _).trans (unitDrop_le u M)
  fixed_nf M :=
    ⟨fun h => notMem_unitDrop u M (Multiset.mem_of_le (idempotentMap.nf_le _) h),
      idempotentMap.fixed_nf _⟩
  fixed_sub A M h hM :=
    ⟨fun hu => hM.1 (Multiset.mem_of_le h hu), idempotentMap.fixed_sub A M h hM.2⟩
  nf_of_fixed M hM := by rw [unitDrop_of_notMem hM.1, idempotentMap.nf_of_fixed M hM.2]
  gen_reach M := by
    refine (Rw_rtg_mono Set.subset_union_left (unitDrop_reach u M)).trans ?_
    refine Rw_rtg_mono Set.subset_union_right ?_
    refine rtg_restrict ?_ ?_ (idempotentMap.gen_reach (unitDrop u M))
    · rintro A B ⟨a, h⟩
      obtain ⟨rfl, rfl⟩ := Prod.mk.injEq _ _ _ _ ▸ h
      show Multiset.replicate 1 a ≤ Multiset.replicate 2 a
      rw [Multiset.replicate_le_replicate]
      omega
    · rintro A B ⟨a, h⟩ hA
      obtain ⟨rfl, rfl⟩ := Prod.mk.injEq _ _ _ _ ▸ h
      refine ⟨a, fun hau => ?_, rfl⟩
      have : a ∈ unitDrop u M :=
        Multiset.mem_of_le hA (Multiset.mem_replicate.mpr ⟨by decide, rfl⟩)
      exact notMem_unitDrop u M (hau ▸ this)
  gen_nf L R h := by
    rcases h with h | ⟨a, hau, h⟩
    · have h' := Set.mem_singleton_iff.mp h
      obtain ⟨rfl, rfl⟩ := Prod.mk.injEq _ _ _ _ ▸ h'
      have e1 : unitDrop u ({u} : Monomial n) = 0 := ((identityNF u cancel).gen_nf _ _ rfl).1
      have e0 : idempotentMap.nf (0 : Monomial n) = 0 := (idempotentNF (n := n) cancel).nf_zero
      refine ⟨?_, by simp⟩
      show idempotentMap.nf (unitDrop u {u}) = 0
      rw [e1, e0]
    · obtain ⟨rfl, rfl⟩ := Prod.mk.injEq _ _ _ _ ▸ h
      show idempotentMap.nf (unitDrop u (Multiset.replicate 2 a)) = {a} ∧ {a} ≠ Multiset.replicate 2 a
      rw [unitDrop_of_notMem (by rw [Multiset.mem_replicate]; exact fun h => hau h.2.symm)]
      exact idempotentMap.gen_nf _ _ ⟨a, rfl⟩

/-- The engine's law set for an ACI operator with identity `u`. -/
def Laws.idempotentIdentity (u : Fin n) (cancel : Prop) : Laws n :=
  (idempotentIdentityNF u cancel).toLaws

theorem idempotentIdentity_clamp (u : Fin n) (cancel : Prop) (M : Monomial n) :
    (Laws.idempotentIdentity u cancel).clamp M =
      ofCounts fun a => min ((M.filter (· ≠ u)).count a) 1 := rfl

@[simp] theorem count_idempotentIdentity_clamp (u : Fin n) (cancel : Prop) (M : Monomial n)
    (a : Fin n) :
    ((Laws.idempotentIdentity u cancel).clamp M).count a =
      if a = u then 0 else min (M.count a) 1 := by
  show (idempotentMap.nf (unitDrop u M)).count a = _
  rw [CountMap.count_nf, count_unitDrop]
  split_ifs <;> simp [idempotentMap]

theorem idempotentIdentity_hlaw (u : Fin n) (cancel : Prop) :
    ∀ P Q, (Laws.idempotentIdentity u cancel).lawRel P Q → degLex P Q :=
  (idempotentIdentityNF u cancel).toLaws_hlaw

theorem idempotentIdentity_hnf_ax (u : Fin n) (cancel : Prop) :
    ∀ M N, ¬ Rw (plain n) (Laws.idempotentIdentity u cancel).axRules
      ((Laws.idempotentIdentity u cancel).clamp M) N :=
  (idempotentIdentityNF u cancel).toLaws_hnf_ax

theorem idempotentIdentityNF_gen (u : Fin n) (cancel : Prop) :
    (idempotentIdentityNF u cancel).gen = unitGen u ∪ idemGenNe u := rfl

/-! ## Without `InvUnitFree` the composition is not a normal form

With `inv 0 = some 1` and `1` the unit: the engine's clamp maps `{0, 1}`
to `{0}` (the drop runs first, then nothing cancels), while the pair law
cancels `{0, 1}` to `∅`. Both `{0}` and `∅` are clamp-fixed, so the
clamp picks one of two normal forms of the pooled laws and the derived
equation `0 = e` is lost. -/

def invCE : Fin 2 → Option (Fin 2) := ![some 1, none]

/-- The engine's composite clamp on `{0, 1}` with unit `1`. -/
def engineClampCE (M : Monomial 2) : Monomial 2 :=
  invWalk invCE ((nilpotentNF 2 (le_refl 2) False).nf (unitDrop 1 M))

theorem combined_counterexample :
    engineClampCE {0, 1} = {0} ∧ invWalk invCE ({0, 1} : Monomial 2) = 0 ∧
    engineClampCE {0} = {0} ∧ engineClampCE 0 = 0 := by
  refine ⟨?_, invWalk_pair (by decide), ?_, ?_⟩
  · have h1 : unitDrop 1 ({0, 1} : Monomial 2) = {0} := by decide
    have h2 : (nilpotentNF 2 (le_refl 2) False).nf ({0} : Monomial 2) = {0} :=
      (nilpotentNF 2 (le_refl 2) False).nf_of_fixed _ (fun a => by
        show ({0} : Monomial 2).count a < 2
        rw [Multiset.count_singleton]; split_ifs <;> omega)
    unfold engineClampCE
    rw [h1, h2]
    apply invWalk_of_invNormal
    intro x y hxy
    have : x = 0 ∧ y = 1 := by
      revert hxy; unfold invCE
      fin_cases x <;> fin_cases y <;> simp
    obtain ⟨rfl, rfl⟩ := this
    exact ⟨fun h => absurd h (by decide), fun _ => Or.inr (by decide)⟩
  · have h1 : unitDrop 1 ({0} : Monomial 2) = {0} := by decide
    have h2 : (nilpotentNF 2 (le_refl 2) False).nf ({0} : Monomial 2) = {0} :=
      (nilpotentNF 2 (le_refl 2) False).nf_of_fixed _ (fun a => by
        show ({0} : Monomial 2).count a < 2
        rw [Multiset.count_singleton]; split_ifs <;> omega)
    unfold engineClampCE
    rw [h1, h2]
    apply invWalk_of_invNormal
    intro x y hxy
    have : x = 0 ∧ y = 1 := by
      revert hxy; unfold invCE
      fin_cases x <;> fin_cases y <;> simp
    obtain ⟨rfl, rfl⟩ := this
    exact ⟨fun h => absurd h (by decide), fun _ => Or.inr (by decide)⟩
  · unfold engineClampCE
    have h1 : unitDrop 1 (0 : Monomial 2) = 0 := by decide
    rw [h1, NFLaw.nf_zero]
    exact invWalk_of_invNormal (inverseNF invCE False).fixed_zero

theorem invCE_not_unitFree : ¬ InvUnitFree invCE 1 := by
  intro h
  have := (h 0 1 (by decide)).mpr rfl
  exact absurd this (by decide)

end SemperProofs.CC
