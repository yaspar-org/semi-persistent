import SemperProofs.CC.Laws.InvRules

/-!
# A fixed round under R1-R5 discharges the inverse hypotheses

`RoundFixedInv`, `RoundFixedInvUnit` and `RoundFixedInvNil` say that every
premise of R1-R5 among the state's nodes already has its conclusion: the
classes are merged (R1, R2) or the built node is present in the class
(R3, R4, R5). From these and `InvNodes` the four law-side hypotheses of
`completion_complete_inverse` / `completion_complete_combined` follow:

* `invMatching_of_fixed` (R1), `invUnitFree_of_fixed` (R2),
* `inverseAxiomCP_of_fixed` (R3), `nilpotentInverseCP_of_fixed` (R4, R5).

The last two read "node present in the class" as joinability under
`R ∪ Ax` through `Converged.nodes_reduce`; a node asserted by a rule may
have been retired since, so the retired case goes through `I3`
(`nodes_reduce_all`). The engine-level theorems
`completion_complete_inverse_engine` and
`completion_complete_combined_engine` close the file.

R5 is not in `spec-inverse-rules.md`. `NilpotentInverseCP` demands the
pair `({x}, y^(k−1))` joinable for `inv x = y ≠ x` even when `g(y)` is
absent; the law-law critical pair of `yᵏ → ∅` with `{x, y} → ∅` exists
whether or not `g(y)` does, and R4 fires only for classes with an
inverse node. R5: for each `g(x)` in class `y ≠ x`, assert
`f{y : k−1} = x` (`E`: `y^(k−1) = y^(k−1) ⊎ {x, y} = yᵏ ⊎ {x} = {x}`).
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

/-! ## Nodes present in one class are joinable -/

theorem transGen_flip {α : Type*} {r : α → α → Prop} {a b : α} (h : TransGen r a b) :
    TransGen (fun y x => r x y) b a := by
  induction h with
  | single h => exact TransGen.single h
  | tail _ h ih => exact TransGen.head h ih

/-- Every node, retired or not, rewrites to its class's right-hand side:
`Converged.nodes_reduce` for active nodes, `I3` and well-founded
induction on `→_R` for retired ones. -/
theorem nodes_reduce_all {L : Laws n} {st : State n} (hconv : Converged L st) (h3 : I3 L st) :
    ∀ M c, (M, c) ∈ st.nodes → ReflTransGen (Rw L st.rules) M (st.rhs (st.find c)) := by
  have hwf := (Rw_wf (L := L) (R := st.rules) (rules_oriented st)).transGen
  intro M
  induction M using hwf.induction with
  | _ M ih =>
    intro c hM
    by_cases hr : (M, c) ∈ st.retired
    · obtain ⟨M', c', hMM', hM', hc'⟩ := h3 M c hr
      have := ih M' (transGen_flip hMM') c' hM'
      rw [hc'] at this
      exact hMM'.to_reflTransGen.trans this
    · exact hconv.nodes_reduce M c ⟨hM, hr⟩

/-- `M →*_{R ∪ Ax} clamp M`. -/
theorem rtg_clamp (L : Laws n) (R : Rules n) (M : Monomial n) :
    ReflTransGen (RwAx L R) M (L.clamp M) := by
  rcases L.clamp_law M with h | h
  · rw [h]
  · exact ReflTransGen.single (RwAx_of_law h)

/-- Two nodes of one class are joinable under `R ∪ Ax`. -/
theorem joinable_of_nodes {L : Laws n} {st : State n} (hconv : Converged L st) (h3 : I3 L st)
    {M N : Monomial n} {c d : Fin n} (hM : (M, c) ∈ st.nodes) (hN : (N, d) ∈ st.nodes)
    (hcd : st.find c = st.find d) : Joinable (RwAx L st.rules) M N := by
  refine ⟨st.rhs (st.find c), Rw_rtg_embed (nodes_reduce_all hconv h3 M c hM), ?_⟩
  rw [hcd]
  exact Rw_rtg_embed (nodes_reduce_all hconv h3 N d hN)

/-- Two monomials whose normalized nodes are in one class are joinable. -/
theorem joinable_of_clamp_nodes {L : Laws n} {st : State n} (hconv : Converged L st)
    (h3 : I3 L st) {M N : Monomial n} {c d : Fin n} (hM : (L.clamp M, c) ∈ st.nodes)
    (hN : (L.clamp N, d) ∈ st.nodes) (hcd : st.find c = st.find d) :
    Joinable (RwAx L st.rules) M N := by
  obtain ⟨P, h₁, h₂⟩ := joinable_of_nodes hconv h3 hM hN hcd
  exact ⟨P, (rtg_clamp L _ M).trans h₁, (rtg_clamp L _ N).trans h₂⟩

/-- A normalized node and a plain node of one class. -/
theorem joinable_of_clamp_node_left {L : Laws n} {st : State n} (hconv : Converged L st)
    (h3 : I3 L st) {M N : Monomial n} {c d : Fin n} (hM : (L.clamp M, c) ∈ st.nodes)
    (hN : (N, d) ∈ st.nodes) (hcd : st.find c = st.find d) :
    Joinable (RwAx L st.rules) M N := by
  obtain ⟨P, h₁, h₂⟩ := joinable_of_nodes hconv h3 hM hN hcd
  exact ⟨P, (rtg_clamp L _ M).trans h₁, h₂⟩

/-! ## R3 gives `InverseAxiomCP` -/

theorem inverseAxiomCP_of_fixed {L : Laws n} {inv : Fin n → Option (Fin n)} {st : State n}
    (hconv : Converged L st) (h3 : I3 L st) (hfix : RoundFixedInv L.clamp inv st) :
    InverseAxiomCP L inv st.rules := by
  intro A B hAB x y hxy
  constructor
  · intro hx
    obtain ⟨c, d, hc, hd, hcd⟩ := hfix.r3_left A B hAB x hx y hxy
    exact joinable_of_clamp_nodes hconv h3 hc hd hcd
  · intro _ hy
    obtain ⟨c, d, hc, hd, hcd⟩ := hfix.r3_right A B hAB x y hxy hy
    exact joinable_of_clamp_nodes hconv h3 hc hd hcd

/-! ## R4 and R5 give `NilpotentInverseCP` -/

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

/-- `NilpotentInverseCP` from a fixed round under R4 and R5. The
self-inverse case with odd `k` needs the normalized node `clamp(x^(k−1))`
to be the empty monomial (`hself`; `combined_clamp_replicate_self` below
proves it for the engine's clamp). -/
theorem nilpotentInverseCP_of_fixed {L : Laws n} {inv : Fin n → Option (Fin n)} {k : ℕ}
    {st : State n} (hconv : Converged L st) (h3 : I3 L st) (hinv : L.HasInv inv)
    (hfix : RoundFixedInvNil L.clamp inv k st)
    (hself : ∀ x, inv x = some x → 2 < k → k % 2 = 1 →
      L.clamp (Multiset.replicate (k - 1) x) = 0) :
    NilpotentInverseCP (st.rules ∪ L.axRules) k inv := by
  intro x y hxy
  constructor
  · intro hne
    constructor
    · obtain ⟨c, d, hc, hd, hcd⟩ := hfix.r4 x y hxy
      exact Joinable_symm (joinable_of_clamp_node_left hconv h3 hc hd hcd)
    · obtain ⟨c, d, hc, hd, hcd⟩ := hfix.r5 x y hxy hne
      exact Joinable_symm (joinable_of_clamp_node_left hconv h3 hc hd hcd)
  · rintro rfl hk2
    have hpair : (({x, x} : Monomial n), (0 : Monomial n)) ∈ st.rules ∪ L.axRules :=
      Or.inr (hinv x x hxy)
    have hred := rtg_replicate_mod_two hpair (k - 2)
    by_cases hpar : (k - 2) % 2 = 0
    · rw [hpar, Multiset.replicate_zero] at hred
      exact ⟨0, ReflTransGen.refl, hred⟩
    · have hodd : (k - 2) % 2 = 1 := by omega
      rw [hodd, Multiset.replicate_one] at hred
      obtain ⟨c, d, hc, hd, hcd⟩ := hfix.r4 x x hxy
      rw [hself x hxy hk2 (by omega)] at hc
      have h0 : st.rhs (st.find c) = 0 :=
        (rtg_of_normal (Rw_zero_normal (rules_oriented st)) (nodes_reduce_all hconv h3 _ c hc)).symm
      have hx : ReflTransGen (RwAx L st.rules) {x} 0 := by
        have := Rw_rtg_embed (nodes_reduce_all hconv h3 _ d hd)
        rwa [← hcd, h0] at this
      exact ⟨0, ReflTransGen.refl, hred.trans hx⟩

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

/-! ## The engine-level completeness theorems -/

/-- `completion_complete_inverse` with `hmatch` and `hax` replaced by a
fixed round under R1 and R3 (`hfixinv`), `inv` reading the `g`-nodes
(`hinv`), and the retirement discipline `I3` (`h3`: a retired node
rewrites to a node of its class; needed because a node asserted by R3
may have been retired since). -/
theorem completion_complete_inverse_engine (inv : Fin n → Option (Fin n)) (cancel : Prop)
    {S : Set (Monomial n × Monomial n)} {st : State n} {ss₀ ss : SlotState n}
    {gnodes : Set (Fin n × Fin n)}
    (h5₀ : SlotState.I5 ss₀) (hrun : SlotState.OpsStar ss₀ ss) (ha : SlotState.Agrees st ss)
    (h0 : I0Active st) (hcanon : ∀ c, (Laws.inverse inv cancel).clamp (st.rhs c) = st.rhs c)
    (hfix : RoundFixed (Laws.inverse inv cancel) st)
    (h3 : I3 (Laws.inverse inv cancel) st)
    (hfixinv : RoundFixedInv (invWalk inv) inv st)
    (hinv : InvNodes st gnodes inv)
    (hRR : RuleRuleCP (Laws.inverse inv cancel) st.rules)
    (hlhs : ∀ A B, (A, B) ∈ st.rules → InvNormal inv A)
    (hcc : ∀ P c d, (P, c) ∈ st.nodes → (P, d) ∈ st.nodes → st.find c = st.find d)
    (hS : ∀ M N, (M, N) ∈ S →
      ∃ c d, (M, c) ∈ st.active ∧ (N, d) ∈ st.active ∧ st.find c = st.find d)
    (hcancel : cancel → ∀ M N X,
      Joinable (Rw (plain n) (st.rules ∪ (Laws.inverse inv cancel).axRules)) (M + X) (N + X) →
      Joinable (Rw (plain n) (st.rules ∪ (Laws.inverse inv cancel).axRules)) M N)
    {M N : Monomial n} {c d : Fin n} (hM : (M, c) ∈ st.active) (hN : (N, d) ∈ st.active)
    (hMN : E (Laws.inverse inv cancel) S M N) : st.find c = st.find d := by
  have h5 : I5 st := SlotState.state_I5_of_slot (SlotState.reachable_I5 h5₀ hrun) ha
  have hconv : Converged (Laws.inverse inv cancel) st :=
    roundFixed_converged (I0_of_active h0) h5 hcanon hfix
  exact completion_complete_inverse inv cancel h5₀ hrun ha h0 hcanon hfix hRR
    (invMatching_of_fixed hfixinv hinv) hlhs (inverseAxiomCP_of_fixed hconv h3 hfixinv)
    hcc hS hcancel hM hN hMN

/-- `completion_complete_combined` with `hu`, `hmatch`, `hax_inv` and
`hnilinv` replaced by a fixed round under R1-R5 (`hfixinv`, `hfixu`,
`hfixk`), `inv` reading the `g`-nodes (`hinv`), the unit class canonical
(`hurep`) and the retirement discipline `I3` (`h3`). The law set is
`Laws.combined` at the `InvUnitFree` proof that R2 supplies. -/
theorem completion_complete_combined_engine (u : Fin n) (k : ℕ) (hk : 2 ≤ k)
    (inv : Fin n → Option (Fin n)) (cancel : Prop)
    {S : Set (Monomial n × Monomial n)} {st : State n} {ss₀ ss : SlotState n}
    {gnodes : Set (Fin n × Fin n)}
    (hurep : st.find u = u)
    (hfixu : RoundFixedInvUnit inv u st)
    (hinv : InvNodes st gnodes inv)
    (hfixinv : RoundFixedInv (combinedClamp u k inv) inv st)
    (hfixk : RoundFixedInvNil (combinedClamp u k inv) inv k st)
    (h5₀ : SlotState.I5 ss₀) (hrun : SlotState.OpsStar ss₀ ss) (ha : SlotState.Agrees st ss)
    (h0 : I0Active st)
    (hcanon : ∀ c, (Laws.combined u k hk inv cancel (invUnitFree_of_fixed hfixu hinv hurep)).clamp
      (st.rhs c) = st.rhs c)
    (hfix : RoundFixed (Laws.combined u k hk inv cancel (invUnitFree_of_fixed hfixu hinv hurep)) st)
    (h3 : I3 (Laws.combined u k hk inv cancel (invUnitFree_of_fixed hfixu hinv hurep)) st)
    (hRR : RuleRuleCP (Laws.combined u k hk inv cancel (invUnitFree_of_fixed hfixu hinv hurep))
      st.rules)
    (hlhs_u : ∀ A B, (A, B) ∈ st.rules → u ∉ A)
    (hlhs_k : ∀ A B, (A, B) ∈ st.rules → ∀ a, A.count a < k)
    (hlhs_inv : ∀ A B, (A, B) ∈ st.rules → InvNormal inv A)
    (hax_nil : ∀ A B, (A, B) ∈ st.rules → ∀ a ∈ A,
      Joinable (Rw (plain n) (st.rules ∪
          (Laws.combined u k hk inv cancel (invUnitFree_of_fixed hfixu hinv hurep)).axRules))
        (B + Multiset.replicate (k - A.count a) a) (A.filter (· ≠ a)))
    (hcc : ∀ P c d, (P, c) ∈ st.nodes → (P, d) ∈ st.nodes → st.find c = st.find d)
    (hS : ∀ M N, (M, N) ∈ S →
      ∃ c d, (M, c) ∈ st.active ∧ (N, d) ∈ st.active ∧ st.find c = st.find d)
    (hcancel : (Laws.combined u k hk inv cancel (invUnitFree_of_fixed hfixu hinv hurep)).cancellative →
      ∀ M N X,
      Joinable (Rw (plain n) (st.rules ∪
          (Laws.combined u k hk inv cancel (invUnitFree_of_fixed hfixu hinv hurep)).axRules))
        (M + X) (N + X) →
      Joinable (Rw (plain n) (st.rules ∪
          (Laws.combined u k hk inv cancel (invUnitFree_of_fixed hfixu hinv hurep)).axRules)) M N)
    {M N : Monomial n} {c d : Fin n} (hM : (M, c) ∈ st.active) (hN : (N, d) ∈ st.active)
    (hMN : E (Laws.combined u k hk inv cancel (invUnitFree_of_fixed hfixu hinv hurep)) S M N) :
    st.find c = st.find d := by
  set hu := invUnitFree_of_fixed hfixu hinv hurep
  set L := Laws.combined u k hk inv cancel hu with hL
  have h5 : I5 st := SlotState.state_I5_of_slot (SlotState.reachable_I5 h5₀ hrun) ha
  have hconv : Converged L st := roundFixed_converged (I0_of_active h0) h5 hcanon hfix
  have hclamp : L.clamp = combinedClamp u k inv := rfl
  have hfixinv' : RoundFixedInv L.clamp inv st := by rw [hclamp]; exact hfixinv
  have hfixk' : RoundFixedInvNil L.clamp inv k st := by rw [hclamp]; exact hfixk
  exact completion_complete_combined u k hk inv cancel hu h5₀ hrun ha h0 hcanon hfix hRR
    (invMatching_of_fixed hfixinv hinv) hlhs_u hlhs_k hlhs_inv hax_nil
    (inverseAxiomCP_of_fixed hconv h3 hfixinv')
    (nilpotentInverseCP_of_fixed hconv h3 (combined_hasInv u k hk inv cancel hu) hfixk'
      (fun x hxx hk2 hodd =>
        combined_clamp_replicate_self u k hk cancel hu hxx (by omega) (by omega)))
    hcc hS hcancel hM hN hMN

end SemperProofs.CC
