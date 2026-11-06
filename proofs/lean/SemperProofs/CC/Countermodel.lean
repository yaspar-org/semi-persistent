import SemperProofs.CC.BoundedOracle

/-!
# Countermodels certify disequality

The certifying generator (`Conform/CC/Cert.lean`) emits `check-neq A B` only
when it has found a concrete commutative monoid `M` and a valuation `v` of
the summand classes such that every asserted equation holds, every law
instance holds, `M` is cancellative when the operator is, and `A`, `B`
evaluate to different elements. This file proves that such a pair is not
`=_E`-equal (`not_E_of_separates`), so a `check-neq` the engine fails on a
certified pair is an engine unsoundness.

* `ev v m` is the sum of the values of the summands of `m`.
* `IsModel L S v`: the asserted pairs `S` and the law instances of `L` hold
  under `ev v`, and `M` is cancellative when `L` is.
* `E_sound`: `E L S a b → ev v a = ev v b`, by induction on `E`.
* `isModel_pool`: for the oracle's one-step generators (`oracleGen`: unit,
  nilpotent, inverse pair, idempotent) the law hypothesis reduces to
  conditions on the atoms' values (`v u = 0`, `k • v a = 0`,
  `v x + v y = 0`, `v a + v a = v a`), which the generator checks.
* `not_E_nf_of_separates`: the same conclusion for a normal-form law set
  whose generators are oracle generators (e.g. `Laws.combined`, through
  `combinedNF_gen_sub`), via `NFLaw.E_iff`.
-/

namespace SemperProofs.CC.Countermodel

open SemperProofs.CC SemperProofs.CC.Bounded

variable {n : ℕ} {M : Type*} [AddCommMonoid M]

/-- The value of a monomial: the sum of its summands' values. -/
def ev (v : Fin n → M) (m : Monomial n) : M := (m.map v).sum

theorem ev_add (v : Fin n → M) (a b : Monomial n) : ev v (a + b) = ev v a + ev v b := by
  simp [ev, Multiset.map_add, Multiset.sum_add]

theorem ev_zero (v : Fin n → M) : ev v (0 : Monomial n) = 0 := by simp [ev]

theorem ev_single (v : Fin n → M) (a : Fin n) : ev v ({a} : Monomial n) = v a := by simp [ev]

theorem ev_replicate (v : Fin n → M) (k : ℕ) (a : Fin n) :
    ev v (Multiset.replicate k a) = k • v a := by
  simp [ev, Multiset.map_replicate, Multiset.sum_replicate]

theorem ev_pair (v : Fin n → M) (a b : Fin n) : ev v ({a, b} : Monomial n) = v a + v b := by
  simp [ev]

/-- A model of the asserted equations and the laws. -/
structure IsModel (L : Laws n) (S : Set (Monomial n × Monomial n)) (v : Fin n → M) : Prop where
  ax : ∀ p ∈ S, ev v p.1 = ev v p.2
  law : ∀ a b, L.lawRel a b → ev v a = ev v b
  cancel : L.cancellative → ∀ a b c : M, a + c = b + c → a = b

/-- **Soundness of evaluation**: `=_E`-equal monomials have equal values in
every model. -/
theorem E_sound {L : Laws n} {S : Set (Monomial n × Monomial n)} {v : Fin n → M}
    (h : IsModel L S v) {a b : Monomial n} (hE : E L S a b) : ev v a = ev v b := by
  induction hE with
  | ax hm => exact h.ax _ hm
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2
  | congr X _ ih => rw [ev_add, ev_add, ih]
  | law hl => exact h.law _ _ hl
  | cancel hc _ ih =>
    rw [ev_add, ev_add] at ih
    exact h.cancel hc _ _ _ ih

/-- **A countermodel certifies disequality**: a model that separates two
monomials shows they are not `=_E`-equal. -/
theorem not_E_of_separates {L : Laws n} {S : Set (Monomial n × Monomial n)} {v : Fin n → M}
    (h : IsModel L S v) {a b : Monomial n} (hne : ev v a ≠ ev v b) : ¬ E L S a b :=
  fun hE => hne (E_sound h hE)

/-- The oracle's law generators hold under `ev v` when the atoms satisfy
the unit, nilpotent, inverse-pair and idempotent conditions. -/
theorem isModel_pool {u : Option (Fin n)} {k : Option ℕ} {inv : Fin n → Option (Fin n)}
    {idem : Bool} {cancel : Prop} {S : Set (Monomial n × Monomial n)} {v : Fin n → M}
    (hS : ∀ p ∈ S, ev v p.1 = ev v p.2)
    (hu : ∀ w, u = some w → v w = 0)
    (hk : ∀ m, k = some m → ∀ a, m • v a = 0)
    (hi : ∀ x y, inv x = some y → v x + v y = 0)
    (hd : idem = true → ∀ a, v a + v a = v a)
    (hc : cancel → ∀ a b c : M, a + c = b + c → a = b) :
    IsModel (poolLaws (oracleGen u k inv idem) cancel) S v where
  ax := hS
  law a b hab := by
    rcases hab with ⟨w, hw, hr⟩ | ⟨m, x, hm, hr⟩ | ⟨x, y, hxy, hr⟩ | ⟨hid, x, hr⟩
    · cases hr; rw [ev_single, ev_zero, hu w hw]
    · cases hr; rw [ev_replicate, ev_zero, hk m hm x]
    · cases hr; rw [ev_pair, ev_zero, hi x y hxy]
    · cases hr; rw [ev_replicate, ev_single, two_nsmul, hd hid x]
  cancel := hc

/-- **Certified `check-neq` under a normal-form law set.** If `N`'s
generators are oracle generators, the atoms satisfy the law conditions, the
asserted pairs hold, and `M` is cancellative when `N` is, then a separated
pair is not `=_E`-equal under `N.toLaws`. -/
theorem not_E_nf_of_separates (N : NFLaw n) {u : Option (Fin n)} {k : Option ℕ}
    {inv : Fin n → Option (Fin n)} {idem : Bool} (hgen : N.gen ⊆ oracleGen u k inv idem)
    {S : Set (Monomial n × Monomial n)} {v : Fin n → M}
    (hS : ∀ p ∈ S, ev v p.1 = ev v p.2)
    (hu : ∀ w, u = some w → v w = 0)
    (hk : ∀ m, k = some m → ∀ a, m • v a = 0)
    (hi : ∀ x y, inv x = some y → v x + v y = 0)
    (hd : idem = true → ∀ a, v a + v a = v a)
    (hc : N.cancellative → ∀ a b c : M, a + c = b + c → a = b)
    {a b : Monomial n} (hne : ev v a ≠ ev v b) : ¬ E N.toLaws S a b := by
  rw [NFLaw.E_iff]
  intro hE
  have hm : IsModel N.genLaws S v :=
    { ax := hS
      law := fun x y hxy => (isModel_pool (cancel := N.cancellative) hS hu hk hi hd hc).law x y
        (hgen hxy)
      cancel := hc }
  exact hne (E_sound hm hE)

/-- Instance: the engine's combined law set (`:identity`, `:nilpotent k`,
`:inverse`, under `InvUnitFree`). -/
theorem not_E_combined_of_separates (u : Fin n) (k : ℕ) (hk2 : 2 ≤ k)
    (inv : Fin n → Option (Fin n)) (cancel : Prop) (hu : InvUnitFree inv u)
    {S : Set (Monomial n × Monomial n)} {v : Fin n → M}
    (hS : ∀ p ∈ S, ev v p.1 = ev v p.2) (hu0 : v u = 0) (hk : ∀ a, k • v a = 0)
    (hi : ∀ x y, inv x = some y → v x + v y = 0)
    (hc : (combinedNF u k hk2 inv cancel hu).cancellative → ∀ a b c : M, a + c = b + c → a = b)
    {a b : Monomial n} (hne : ev v a ≠ ev v b) :
    ¬ E (combinedNF u k hk2 inv cancel hu).toLaws S a b :=
  not_E_nf_of_separates _ (combinedNF_gen_sub u k hk2 inv cancel hu) hS
    (fun w hw => by cases hw; exact hu0) (fun m hm => by cases hm; exact hk) hi
    (fun h => by cases h) hc hne

/-! ## The concrete models the generator searches

`ZMod m` (a group, so cancellative; `k • x = 0` when `m ∣ k`), and the
cancellative `ℕ`-vectors, are instances of the hypotheses above; the
truncated and `max` models are commutative monoids used only for
non-cancellative operators (the `cancel` hypothesis is then vacuous). -/

theorem zmod_cancel (m : ℕ) : ∀ a b c : ZMod m, a + c = b + c → a = b :=
  fun _ _ _ h => add_right_cancel h

theorem zmod_nil (m k : ℕ) (hmk : m ∣ k) (x : ZMod m) : k • x = 0 := by
  rw [nsmul_eq_mul, (ZMod.natCast_eq_zero_iff k m).mpr hmk, zero_mul]

theorem natVec_cancel (d : ℕ) : ∀ a b c : Fin d → ℕ, a + c = b + c → a = b :=
  fun _ _ _ h => add_right_cancel h

end SemperProofs.CC.Countermodel
