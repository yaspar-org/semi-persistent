import SemperProofs.CC.Laws.InvRules
import SemperProofs.CC.Lattice

/-!
# A fixed round under R1-R5, and completeness for the inverse law sets

`RoundFixedInv`, `RoundFixedInvUnit` and `RoundFixedInvNil` say that every
premise of R1-R5 among the state's nodes already has its conclusion: the
classes are merged (R1, R2) or the built node is present in the class
(R3, R4, R5). From these and `InvNodes`, R1 gives `InvMatching`
(`invMatching_of_fixed`) and R2 gives `InvUnitFree` (`invUnitFree_of_fixed`),
the proof that `Laws.combined` and `Laws.identityInverse` carry.

The engine-level theorems `completion_complete_inverse_engine`,
`completion_complete_combined_engine` and
`completion_complete_identityInverse_engine` close the file. The engine
accepts `:inverse` only on a cancellative operator (`sortcheck.rs`) and runs
`lattice_round` for it at the completion fixpoint; that fixpoint is
lattice-closed (`Lattice.latticeClosed_of_engineFixed`), and lattice closure
with the asserted pairs among active classmates gives completeness for
every law set (`Lattice.complete_of_latticeClosed`). No critical pair of
the inverse law and no retirement discipline is needed.

R5 is not in `spec-inverse-rules.md`: for each `g(x)` in class `y ≠ x`,
assert `f{y : k−1} = x` (`E`: `y^(k−1) = y^(k−1) ⊎ {x, y} = yᵏ ⊎ {x} = {x}`).
R4 fires only for classes with an inverse node, and the law-law critical
pair of `yᵏ → ∅` with `{x, y} → ∅` exists whether or not `g(y)` does.
-/

namespace SemperProofs.CC

open Relation

variable {n : ℕ}

/-! ## The fixed-round conditions -/

/-- R1 and R3 have no pending instance. `clamp` is the engine's
normalization of a built node (`L.clamp`; a function parameter so that
the condition does not depend on the law set it is used for). -/
structure RoundFixedInv (clamp : Monomial n → Monomial n) (inv : Fin n → Option (Fin n))
    (st : State n) : Prop where
  /-- R1: `g(a)` in class `y`, `g(c)` in class `y'`, `y ~ y'`: then `a ~ c`. -/
  r1_inj : ∀ a c y y', inv a = some y → inv c = some y' → st.find y = st.find y' →
    st.find a = st.find c
  /-- R1: `g(x)` in class `y`, `g(y)` in class `z`: then `z ~ x`. -/
  r1_inv : ∀ x y z, inv x = some y → inv y = some z → st.find z = st.find x
  /-- R3: rule `A → B`, `a ∈ A`, `g(a)` in class `y`: the nodes `clamp(B ⊎ {y})`
  and `clamp(A ∖ {a})` are present in one class. -/
  r3_left : ∀ A B, (A, B) ∈ st.rules → ∀ a ∈ A, ∀ y, inv a = some y →
    ∃ c d, (clamp (B + {y}), c) ∈ st.nodes ∧ (clamp (A.erase a), d) ∈ st.nodes ∧
      st.find c = st.find d
  /-- R3: rule `A → B`, `y ∈ A`, `g(x)` in class `y`: the nodes `clamp(B ⊎ {x})`
  and `clamp(A ∖ {y})` are present in one class. -/
  r3_right : ∀ A B, (A, B) ∈ st.rules → ∀ x y, inv x = some y → y ∈ A →
    ∃ c d, (clamp (B + {x}), c) ∈ st.nodes ∧ (clamp (A.erase y), d) ∈ st.nodes ∧
      st.find c = st.find d

/-- R2 has no pending instance (unit class `u`). -/
structure RoundFixedInvUnit (inv : Fin n → Option (Fin n)) (u : Fin n) (st : State n) :
    Prop where
  /-- `g(x)` in the unit class: then `x ~ u`. -/
  r2_inv_unit : ∀ x y, inv x = some y → st.find y = st.find u → st.find x = st.find u
  /-- `g(x)` exists and `x ~ u`: then `g(x) ~ u`. -/
  r2_unit_inv : ∀ x y, inv x = some y → st.find x = st.find u → st.find y = st.find u

/-- R4 and R5 have no pending instance (nilpotent order `k`). -/
structure RoundFixedInvNil (clamp : Monomial n → Monomial n) (inv : Fin n → Option (Fin n))
    (k : ℕ) (st : State n) : Prop where
  /-- R4: `g(x)` in class `y`: the node `clamp(x^(k−1))` is present in class `y`. -/
  r4 : ∀ x y, inv x = some y →
    ∃ c d, (clamp (Multiset.replicate (k - 1) x), c) ∈ st.nodes ∧ ({y}, d) ∈ st.nodes ∧
      st.find c = st.find d
  /-- R5: `g(x)` in class `y ≠ x`: the node `clamp(y^(k−1))` is present in class `x`. -/
  r5 : ∀ x y, inv x = some y → x ≠ y →
    ∃ c d, (clamp (Multiset.replicate (k - 1) y), c) ∈ st.nodes ∧ ({x}, d) ∈ st.nodes ∧
      st.find c = st.find d

/-! ## R1 gives `InvMatching`, R2 gives `InvUnitFree` -/

theorem invMatching_of_fixed {clamp : Monomial n → Monomial n} {inv : Fin n → Option (Fin n)}
    {st : State n} {gnodes : Set (Fin n × Fin n)}
    (hfix : RoundFixedInv clamp inv st) (hinv : InvNodes st gnodes inv) : InvMatching inv where
  inj x z y hxy hzy := by
    have := hfix.r1_inj x z y y hxy hzy rfl
    rwa [hinv.rep_dom hxy, hinv.rep_dom hzy] at this
  symm x y hxy := by
    cases hz : inv y with
    | none => exact Or.inl rfl
    | some z =>
      right
      have := hfix.r1_inv x y z hxy hz
      rw [hinv.rep_dom hxy, hinv.rep_rng hz] at this
      rw [this]

theorem invUnitFree_of_fixed {inv : Fin n → Option (Fin n)} {u : Fin n} {st : State n}
    {gnodes : Set (Fin n × Fin n)}
    (hfix : RoundFixedInvUnit inv u st) (hinv : InvNodes st gnodes inv) (hu : st.find u = u) :
    InvUnitFree inv u := by
  intro x y hxy
  constructor
  · rintro rfl
    have := hfix.r2_unit_inv x y hxy rfl
    rwa [hinv.rep_rng hxy, hu] at this
  · rintro rfl
    have := hfix.r2_inv_unit x y hxy rfl
    rwa [hinv.rep_dom hxy, hu] at this

/-! ## Rewriting lemmas -/

theorem transGen_flip {α : Type*} {r : α → α → Prop} {a b : α} (h : TransGen r a b) :
    TransGen (fun y x => r x y) b a := by
  induction h with
  | single h => exact TransGen.single h
  | tail _ h ih => exact TransGen.head h ih

/-- `M →*_{R ∪ Ax} clamp M`. -/
theorem rtg_clamp (L : Laws n) (R : Rules n) (M : Monomial n) :
    ReflTransGen (RwAx L R) M (L.clamp M) := by
  rcases L.clamp_law M with h | h
  · rw [h]
  · exact ReflTransGen.single (RwAx_of_law h)

/-! ## Powers and the empty monomial -/

/-- The empty monomial has no step by a rule or a law. -/
theorem RwL_zero_normal {L : Laws n} {st : State n} : ∀ N, ¬ st.RwL L 0 N := by
  intro N h
  rcases RwL_degLex h with h' | ⟨-, c, -, h'⟩
  · simp at h'
  · simp at h'

/-- The empty monomial is normal for an oriented rule set. -/
theorem Rw_zero_normal {L : Laws n} {R : Rules n} (hor : Oriented R) :
    ∀ N, ¬ Rw L R 0 N := by
  rintro N ⟨A, B, hAB, hA, -⟩
  rw [Multiset.le_zero] at hA
  subst hA
  rcases hor 0 B hAB with h | ⟨-, c, -, h⟩
  · simp at h
  · simp at h

theorem replicate_sub_replicate (x : Fin n) (a b : ℕ) :
    Multiset.replicate a x - Multiset.replicate b x = Multiset.replicate (a - b) x := by
  ext z
  rw [Multiset.count_sub, Multiset.count_replicate, Multiset.count_replicate,
    Multiset.count_replicate]
  split_ifs <;> omega

/-- `x^m →* x^(m mod 2)` by the pair law `{x, x} → ∅`. -/
theorem rtg_replicate_mod_two {R : Rules n} {x : Fin n}
    (hpair : (({x, x} : Monomial n), (0 : Monomial n)) ∈ R) (m : ℕ) :
    ReflTransGen (Rw (plain n) R) (Multiset.replicate m x) (Multiset.replicate (m % 2) x) := by
  have e : (m / 2) • ({x, x} : Monomial n) = Multiset.replicate (2 * (m / 2)) x := by
    rw [pair_self_eq_replicate, Multiset.nsmul_replicate, mul_comm]
  have hle : (m / 2) • ({x, x} : Monomial n) ≤ Multiset.replicate m x := by
    rw [e, Multiset.replicate_le_replicate]
    omega
  have := rtg_sub_nsmul hpair (Multiset.replicate m x) (m / 2) hle
  rw [e, replicate_sub_replicate] at this
  have hm : m - 2 * (m / 2) = m % 2 := by omega
  rwa [hm] at this

/-! ## The engine's clamp on a self-inverse power -/

theorem cancelAt_replicate_ne (inv : Fin n → Option (Fin n)) (m : ℕ) {x z : Fin n} (hz : z ≠ x) :
    cancelAt inv (Multiset.replicate m x) z = Multiset.replicate m x := by
  have hc : (Multiset.replicate m x).count z = 0 := by
    simp [Multiset.count_replicate, Ne.symm hz]
  unfold cancelAt
  split
  · rfl
  · split
    · rw [hc, Nat.zero_div, Nat.mul_zero, Multiset.replicate_zero, tsub_zero]
    · rw [hc, Nat.zero_min, Multiset.replicate_zero, Multiset.replicate_zero, add_zero, tsub_zero]

theorem cancelAt_replicate_self {inv : Fin n → Option (Fin n)} {x : Fin n} (hxx : inv x = some x)
    (m : ℕ) : cancelAt inv (Multiset.replicate m x) x = Multiset.replicate (m % 2) x := by
  simp only [cancelAt, hxx, ↓reduceIte, Multiset.count_replicate_self]
  rw [replicate_sub_replicate]
  congr 1
  omega

theorem foldl_cancelAt_replicate_self {inv : Fin n → Option (Fin n)} {x : Fin n}
    (hxx : inv x = some x) (l : List (Fin n)) (m : ℕ) :
    l.foldl (cancelAt inv) (Multiset.replicate m x) =
      Multiset.replicate (if x ∈ l then m % 2 else m) x := by
  induction l generalizing m with
  | nil => simp
  | cons a l ih =>
    rw [List.foldl_cons]
    by_cases hax : a = x
    · subst hax
      rw [cancelAt_replicate_self hxx, ih]
      simp only [List.mem_cons_self, ↓reduceIte]
      congr 1
      split_ifs <;> omega
    · rw [cancelAt_replicate_ne inv m hax, ih]
      congr 1
      simp [List.mem_cons, Ne.symm hax]

/-- The engine's walk on a power of a self-inverse class reduces the
exponent mod 2. -/
theorem invWalk_replicate_self {inv : Fin n → Option (Fin n)} {x : Fin n} (hxx : inv x = some x)
    (m : ℕ) : invWalk inv (Multiset.replicate m x) = Multiset.replicate (m % 2) x := by
  unfold invWalk
  rw [foldl_cancelAt_replicate_self hxx]
  simp [List.mem_finRange]

/-- `Laws.combined`'s clamp sends an even power below `k` of a self-inverse
class to the empty monomial. -/
theorem combined_clamp_replicate_self (u : Fin n) (k : ℕ) (hk : 2 ≤ k)
    {inv : Fin n → Option (Fin n)} (cancel : Prop) (hu : InvUnitFree inv u) {x : Fin n}
    (hxx : inv x = some x) {m : ℕ} (hm : m < k) (hm2 : m % 2 = 0) :
    (Laws.combined u k hk inv cancel hu).clamp (Multiset.replicate m x) = 0 := by
  rw [combined_clamp]
  by_cases hxu : x = u
  · subst hxu
    have h1 : (Multiset.replicate m x).filter (· ≠ x) = 0 := unitDrop_replicate_self x m
    have h2 : ofCounts (fun a => ((0 : Monomial n)).count a % k) = 0 := by
      ext a; simp
    rw [h1, h2]
    exact invWalk_of_invNormal (inverseNF inv cancel).fixed_zero
  · have h1 : (Multiset.replicate m x).filter (· ≠ u) = Multiset.replicate m x := by
      apply Multiset.filter_eq_self.mpr
      intro a ha
      rw [Multiset.mem_replicate] at ha
      rw [ha.2]
      exact hxu
    have h2 : ofCounts (fun a => (Multiset.replicate m x).count a % k) = Multiset.replicate m x := by
      ext a
      simp only [count_ofCounts, Multiset.count_replicate]
      split_ifs
      · exact Nat.mod_eq_of_lt hm
      · rfl
    rw [h1, h2, invWalk_replicate_self hxx, hm2, Multiset.replicate_zero]

/-- The engine's composite clamp as a function, for stating the
fixed-round conditions without the `InvUnitFree` proof that
`Laws.combined` carries. -/
def combinedClamp (u : Fin n) (k : ℕ) (inv : Fin n → Option (Fin n)) (M : Monomial n) :
    Monomial n :=
  invWalk inv (ofCounts fun a => (M.filter (· ≠ u)).count a % k)

theorem combined_clamp_eq (u : Fin n) (k : ℕ) (hk : 2 ≤ k) (inv : Fin n → Option (Fin n))
    (cancel : Prop) (hu : InvUnitFree inv u) :
    (Laws.combined u k hk inv cancel hu).clamp = combinedClamp u k inv := rfl

/-- The engine's composite clamp without a nilpotent order, as a function
(as `combinedClamp`). -/
def identityInverseClamp (u : Fin n) (inv : Fin n → Option (Fin n)) (M : Monomial n) :
    Monomial n :=
  invWalk inv (M.filter (· ≠ u))

theorem identityInverse_clamp_eq (u : Fin n) (inv : Fin n → Option (Fin n)) (cancel : Prop)
    (hu : InvUnitFree inv u) :
    (Laws.identityInverse u inv cancel hu).clamp = identityInverseClamp u inv := rfl

/-! ## The engine-level completeness theorems

Each theorem concludes completeness for its law set from lattice closure of
the state (`hlat`) and the asserted pairs being pairs of active classmates
(`hS`). The engine establishes `hlat` by `lattice_round`, which it runs for
every cancellative operator after a completion round that changes nothing,
and it treats every `:inverse` operator as cancellative; at the fixpoint
of `lattice_round` the state is lattice-closed
(`Lattice.latticeClosed_of_engineFixed`). Lattice closure needs no
cancellation and no critical pair: `E_mem_lattice` holds for every law
set. -/

/-- **Completeness for the inverse law set at a lattice-closed state.** Two
active nodes `=_E`-equal under `Laws.inverse inv cancel` are in one class. -/
theorem completion_complete_inverse_engine (inv : Fin n → Option (Fin n)) (cancel : Prop)
    {S : Set (Monomial n × Monomial n)} {st : State n}
    (hlat : Lattice.LatticeClosed (Laws.inverse inv cancel) st)
    (hS : ∀ M N, (M, N) ∈ S →
      ∃ c d, (M, c) ∈ st.active ∧ (N, d) ∈ st.active ∧ st.find c = st.find d)
    {M N : Monomial n} {c d : Fin n} (hM : (M, c) ∈ st.active) (hN : (N, d) ∈ st.active)
    (hMN : E (Laws.inverse inv cancel) S M N) : st.find c = st.find d :=
  Lattice.complete_of_latticeClosed hlat hS hM hN (Lattice.E_union_left hMN)

/-- **Completeness for the combined law set (unit, nilpotent order,
inverse) at a lattice-closed state.** `hu` is the proof that
`Laws.combined` carries; the engine's fixed round under R2 supplies it
(`invUnitFree_of_fixed`). -/
theorem completion_complete_combined_engine (u : Fin n) (k : ℕ) (hk : 2 ≤ k)
    (inv : Fin n → Option (Fin n)) (cancel : Prop) (hu : InvUnitFree inv u)
    {S : Set (Monomial n × Monomial n)} {st : State n}
    (hlat : Lattice.LatticeClosed (Laws.combined u k hk inv cancel hu) st)
    (hS : ∀ M N, (M, N) ∈ S →
      ∃ c d, (M, c) ∈ st.active ∧ (N, d) ∈ st.active ∧ st.find c = st.find d)
    {M N : Monomial n} {c d : Fin n} (hM : (M, c) ∈ st.active) (hN : (N, d) ∈ st.active)
    (hMN : E (Laws.combined u k hk inv cancel hu) S M N) : st.find c = st.find d :=
  Lattice.complete_of_latticeClosed hlat hS hM hN (Lattice.E_union_left hMN)

/-- **Completeness for the unit-and-inverse law set at a lattice-closed
state.** `hu` as in `completion_complete_combined_engine`. -/
theorem completion_complete_identityInverse_engine (u : Fin n) (inv : Fin n → Option (Fin n))
    (cancel : Prop) (hu : InvUnitFree inv u)
    {S : Set (Monomial n × Monomial n)} {st : State n}
    (hlat : Lattice.LatticeClosed (Laws.identityInverse u inv cancel hu) st)
    (hS : ∀ M N, (M, N) ∈ S →
      ∃ c d, (M, c) ∈ st.active ∧ (N, d) ∈ st.active ∧ st.find c = st.find d)
    {M N : Monomial n} {c d : Fin n} (hM : (M, c) ∈ st.active) (hN : (N, d) ∈ st.active)
    (hMN : E (Laws.identityInverse u inv cancel hu) S M N) : st.find c = st.find d :=
  Lattice.complete_of_latticeClosed hlat hS hM hN (Lattice.E_union_left hMN)

end SemperProofs.CC
