import SemperProofs.CC.Laws.Main

/-!
# The inverse rules R1-R5: inference steps and soundness

`spec-inverse-rules.md` asks the engine to assert four consequences of the
inverse law whenever their premises hold among existing nodes. This file
models them as inference steps on the abstract completion `State` and
proves that each preserves the soundness invariant `I2`, so that
`completion_sound` extends to runs that interleave them with `Infer`.

Notation. `inv x = some y` reads "the `g`-node over the class `x` sits in
the class `y`" (`InvNodes` relates `inv` to the set of `g`-nodes; the
rules are stated on `inv` because the law set `Laws.inverse inv _` is
built from the same map). The unit class is `u`, the nilpotent order `k`.
The class `x` of a `g`-node's child and the class of the `g`-node itself
are *atomic* (a non-`f` node lives in or under them), so the model gives
each the `f`-node `{x}` (sketch (a), "Nodes and rules": `r(c) = {find c}`
for an atomic class); the merges below are stated on those atomic nodes.

* `InvInfer L inv`: a hash-cons of a built node in a fresh class
  (`mint`), R1 (two forms) and R3 (two forms).
* `InvInferUK L inv u k`: R2 (two forms), R4 and the mirror rule R5 that
  the spec is missing (see `InvRulesMain.lean`).
* `invInfer_I2`, `invInferUK_I2`: each step preserves `I2`;
  `inv_rules_sound`, `inv_rules_sound_uk`: soundness of a run.

The law-side facts the derivations use are `Laws.HasInv` (`{x, inv x} → ∅`
is a law instance), `Laws.HasUnit` (`{u} → ∅`) and `Laws.HasNil`
(`xᵏ → ∅`); `Laws.inverse` has the first, `Laws.combined` all three.
-/

namespace SemperProofs.CC

open Relation

variable {n : ℕ}

/-! ## Law instances the derivations use -/

/-- `{x, inv x} → ∅` is a law instance for every `x` with an inverse node. -/
def Laws.HasInv (L : Laws n) (inv : Fin n → Option (Fin n)) : Prop :=
  ∀ x y, inv x = some y → L.lawRel ({x, y} : Monomial n) 0

/-- `{u} → ∅` is a law instance. -/
def Laws.HasUnit (L : Laws n) (u : Fin n) : Prop :=
  L.lawRel ({u} : Monomial n) 0

/-- `xᵏ → ∅` is a law instance for every class `x`. -/
def Laws.HasNil (L : Laws n) (k : ℕ) : Prop :=
  ∀ x : Fin n, L.lawRel (Multiset.replicate k x) 0

theorem inverse_hasInv (inv : Fin n → Option (Fin n)) (cancel : Prop) :
    (Laws.inverse inv cancel).HasInv inv :=
  fun x y hxy => (inverseNF inv cancel).gen_sub_axRules ⟨x, y, hxy, rfl⟩

theorem combined_hasInv (u : Fin n) (k : ℕ) (hk : 2 ≤ k) (inv : Fin n → Option (Fin n))
    (cancel : Prop) (hu : InvUnitFree inv u) :
    (Laws.combined u k hk inv cancel hu).HasInv inv :=
  fun x y hxy => (combinedNF u k hk inv cancel hu).gen_sub_axRules (Or.inr ⟨x, y, hxy, rfl⟩)

theorem combined_hasUnit (u : Fin n) (k : ℕ) (hk : 2 ≤ k) (inv : Fin n → Option (Fin n))
    (cancel : Prop) (hu : InvUnitFree inv u) :
    (Laws.combined u k hk inv cancel hu).HasUnit u :=
  (combinedNF u k hk inv cancel hu).gen_sub_axRules (Or.inl (Or.inl rfl))

theorem combined_hasNil (u : Fin n) (k : ℕ) (hk : 2 ≤ k) (inv : Fin n → Option (Fin n))
    (cancel : Prop) (hu : InvUnitFree inv u) :
    (Laws.combined u k hk inv cancel hu).HasNil k := by
  intro x
  exact (combinedNF u k hk inv cancel hu).gen_sub_axRules
    (Or.inl (Or.inr ((nilpotentNF_gen_iff _).mpr ⟨x, rfl⟩)))

/-! ## Equational helpers -/

theorem pair_eq_add (x y : Fin n) : ({x, y} : Monomial n) = {x} + {y} := by
  rw [Multiset.insert_eq_cons, Multiset.singleton_add]

/-- Congruence on the left summand. -/
theorem E.congr_left {L : Laws n} {S : Set (Monomial n × Monomial n)} {M N : Monomial n}
    (X : Monomial n) (h : E L S M N) : E L S (X + M) (X + N) := by
  rw [add_comm X M, add_comm X N]
  exact h.congr X

/-- `clamp M =_E M`. -/
theorem E_clamp (L : Laws n) (S : Set (Monomial n × Monomial n)) (M : Monomial n) :
    E L S (L.clamp M) M := by
  rcases L.clamp_law M with h | h
  · rw [h]; exact E.refl _
  · exact (E.law h).symm

/-- `{x} + {inv x} =_E ∅`. -/
theorem E_pair_zero {L : Laws n} {inv : Fin n → Option (Fin n)} (hinv : L.HasInv inv)
    (S : Set (Monomial n × Monomial n)) {x y : Fin n} (hxy : inv x = some y) :
    E L S ({x} + {y}) 0 := by
  rw [← pair_eq_add]
  exact E.law (hinv x y hxy)

/-- Two atomic nodes of one class are `=_E`-equal. -/
theorem E_atoms {L : Laws n} {S : Set (Monomial n × Monomial n)} {st : State n}
    (h : I2 L S st) {x y cx cy : Fin n} (hx : ({x}, cx) ∈ st.nodes) (hy : ({y}, cy) ∈ st.nodes)
    (hc : st.find cx = st.find cy) : E L S ({x} : Monomial n) {y} :=
  h _ _ _ _ hx hy hc

/-! ## `inv` reads the `g`-nodes of a state -/

/-- `inv` is the inverse map the state defines: `inv x = some y` exactly
when `x` and `y` are representatives and some `g`-node `(x', y')`
(child class `x'`, node class `y'`) has `find x' = x` and `find y' = y`.
Reading `inv` as a function presupposes that all `g`-nodes over one class
are in one class (congruence closure for `g`, which holds at every round
end). The child class and the node class of a `g`-node are atomic, so the
state holds their singleton `f`-nodes. -/
structure InvNodes (st : State n) (gnodes : Set (Fin n × Fin n))
    (inv : Fin n → Option (Fin n)) : Prop where
  inv_iff : ∀ x y, inv x = some y ↔
    st.find x = x ∧ st.find y = y ∧ ∃ x' y', (x', y') ∈ gnodes ∧ st.find x' = x ∧ st.find y' = y
  atom_child : ∀ x y, (x, y) ∈ gnodes → ∃ c, ({st.find x}, c) ∈ st.nodes ∧ st.find c = st.find x
  atom_class : ∀ x y, (x, y) ∈ gnodes → ∃ c, ({st.find y}, c) ∈ st.nodes ∧ st.find c = st.find y

namespace InvNodes

variable {st : State n} {gnodes : Set (Fin n × Fin n)} {inv : Fin n → Option (Fin n)}

theorem rep_dom (h : InvNodes st gnodes inv) {x y : Fin n} (hxy : inv x = some y) :
    st.find x = x :=
  ((h.inv_iff x y).mp hxy).1

theorem rep_rng (h : InvNodes st gnodes inv) {x y : Fin n} (hxy : inv x = some y) :
    st.find y = y :=
  ((h.inv_iff x y).mp hxy).2.1

/-- The atomic node of a class in the domain of `inv`. -/
theorem atom_dom (h : InvNodes st gnodes inv) {x y : Fin n} (hxy : inv x = some y) :
    ∃ c, ({x}, c) ∈ st.nodes ∧ st.find c = st.find x := by
  obtain ⟨hx, -, x', y', hg, hx', -⟩ := (h.inv_iff x y).mp hxy
  obtain ⟨c, hc, hcx⟩ := h.atom_child x' y' hg
  rw [hx'] at hc hcx
  exact ⟨c, hc, by rw [hcx, hx]⟩

/-- The atomic node of a class in the range of `inv`. -/
theorem atom_rng (h : InvNodes st gnodes inv) {x y : Fin n} (hxy : inv x = some y) :
    ∃ c, ({y}, c) ∈ st.nodes ∧ st.find c = st.find y := by
  obtain ⟨-, hy, x', y', hg, -, hy'⟩ := (h.inv_iff x y).mp hxy
  obtain ⟨c, hc, hcy⟩ := h.atom_class x' y' hg
  rw [hy'] at hc hcy
  exact ⟨c, hc, by rw [hcy, hy]⟩

end InvNodes

/-! ## The inference steps -/

/-- R1 and R3 (`spec-inverse-rules.md`), plus the hash-cons of a built node.

* `mint`: a node built by R3/R4/R5 is hash-consed into a fresh class
  before its union (the engine's `add`; for `I2` any node in a fresh
  class is sound).
* `r1_inj`: `g(a)` in class `y`, `g(c)` in class `y'`, `y ~ y'`: union
  `a` and `c` (stated on the atomic nodes of `a` and `c`).
* `r1_inv`: `g(x)` in class `y` and `g(y)` in class `z`: union `z` and `x`.
* `r3_left`: rule `A → B`, `a ∈ A`, `g(a)` in class `y`: union the nodes
  `clamp(B ⊎ {y})` and `clamp(A ∖ {a})` (both built, so normalized).
* `r3_right`: rule `A → B`, `y ∈ A`, `g(x)` in class `y`: union the nodes
  `clamp(B ⊎ {x})` and `clamp(A ∖ {y})`. -/
inductive InvInfer (L : Laws n) (inv : Fin n → Option (Fin n)) : State n → State n → Prop
  | mint {st : State n} {N : Monomial n} {d : Fin n} :
      st.Fresh d → InvInfer L inv st (st.addNode N d)
  | r1_inj {st : State n} {a c y y' ca cc cy cy' : Fin n} :
      inv a = some y → inv c = some y' →
      ({y}, cy) ∈ st.nodes → ({y'}, cy') ∈ st.nodes → st.find cy = st.find cy' →
      ({a}, ca) ∈ st.nodes → ({c}, cc) ∈ st.nodes →
      InvInfer L inv st (st.merge ca cc)
  | r1_inv {st : State n} {x y z cx cz : Fin n} :
      inv x = some y → inv y = some z →
      ({x}, cx) ∈ st.nodes → ({z}, cz) ∈ st.nodes →
      InvInfer L inv st (st.merge cz cx)
  | r3_left {st : State n} {A B : Monomial n} {a y c d : Fin n} :
      (A, B) ∈ st.rules → a ∈ A → inv a = some y →
      (L.clamp (B + {y}), c) ∈ st.nodes → (L.clamp (A.erase a), d) ∈ st.nodes →
      InvInfer L inv st (st.merge c d)
  | r3_right {st : State n} {A B : Monomial n} {x y c d : Fin n} :
      (A, B) ∈ st.rules → inv x = some y → y ∈ A →
      (L.clamp (B + {x}), c) ∈ st.nodes → (L.clamp (A.erase y), d) ∈ st.nodes →
      InvInfer L inv st (st.merge c d)

/-- R2, R4 and R5, for an operator with unit class `u` and nilpotent order `k`.

* `r2_inv_unit`: `g(x)` in class `y ~ u`: union `x` and `u`.
* `r2_unit_inv`: `g(x)` in class `y`, `x ~ u`: union `y` and `u`.
* `r4`: `g(x)` in class `y`: union the node `clamp(x^(k−1))` with `y`.
* `r5` (missing from the spec; the mirror of `r4`): `g(x)` in class
  `y ≠ x`: union the node `clamp(y^(k−1))` with `x`. -/
inductive InvInferUK (L : Laws n) (inv : Fin n → Option (Fin n)) (u : Fin n) (k : ℕ) :
    State n → State n → Prop
  | r2_inv_unit {st : State n} {x y cx cy cu : Fin n} :
      inv x = some y → ({y}, cy) ∈ st.nodes → ({u}, cu) ∈ st.nodes → st.find cy = st.find cu →
      ({x}, cx) ∈ st.nodes →
      InvInferUK L inv u k st (st.merge cx cu)
  | r2_unit_inv {st : State n} {x y cx cy cu : Fin n} :
      inv x = some y → ({x}, cx) ∈ st.nodes → ({u}, cu) ∈ st.nodes → st.find cx = st.find cu →
      ({y}, cy) ∈ st.nodes →
      InvInferUK L inv u k st (st.merge cy cu)
  | r4 {st : State n} {x y c d : Fin n} :
      inv x = some y → (L.clamp (Multiset.replicate (k - 1) x), c) ∈ st.nodes →
      ({y}, d) ∈ st.nodes →
      InvInferUK L inv u k st (st.merge c d)
  | r5 {st : State n} {x y c d : Fin n} :
      inv x = some y → x ≠ y → (L.clamp (Multiset.replicate (k - 1) y), c) ∈ st.nodes →
      ({x}, d) ∈ st.nodes →
      InvInferUK L inv u k st (st.merge c d)

/-! ## Soundness of each step -/

/-- Adding a node in a fresh class preserves `I2`. -/
theorem addNode_fresh_I2 {L : Laws n} {S : Set (Monomial n × Monomial n)} {st : State n}
    (h : I2 L S st) {N : Monomial n} {d : Fin n} (hfresh : st.Fresh d) :
    I2 L S (st.addNode N d) := by
  intro P a Q b hP hQ hab
  simp only [State.addNode, Set.mem_insert_iff, Prod.mk.injEq] at hP hQ
  rcases hP with ⟨rfl, rfl⟩ | hP <;> rcases hQ with ⟨rfl, rfl⟩ | hQ
  · exact E.refl _
  · exact absurd hab.symm (hfresh Q b hQ)
  · exact absurd hab (hfresh P a hP)
  · exact h P a Q b hP hQ hab

/-- R1, injectivity: `{a} + {y} =_E ∅ =_E {c} + {y'}` and `{y} =_E {y'}`
give `{a} + {y'} =_E {c} + {y'}`; cancel `{y'}`. -/
theorem E_r1_inj {L : Laws n} {inv : Fin n → Option (Fin n)} (hinv : L.HasInv inv)
    (hc : L.cancellative) {S : Set (Monomial n × Monomial n)} {a c y y' : Fin n}
    (hay : inv a = some y) (hcy : inv c = some y') (hyy : E L S ({y} : Monomial n) {y'}) :
    E L S ({a} : Monomial n) {c} := by
  refine E.cancel (X := {y'}) hc ?_
  have h₁ : E L S ({a} + {y'}) ({a} + {y}) := E.congr_left {a} hyy.symm
  exact h₁.trans ((E_pair_zero hinv S hay).trans (E_pair_zero hinv S hcy).symm)

/-- R1, involution: `{x} + {y} =_E ∅ =_E {z} + {y}`; cancel `{y}`. -/
theorem E_r1_inv {L : Laws n} {inv : Fin n → Option (Fin n)} (hinv : L.HasInv inv)
    (hc : L.cancellative) {S : Set (Monomial n × Monomial n)} {x y z : Fin n}
    (hxy : inv x = some y) (hyz : inv y = some z) :
    E L S ({z} : Monomial n) {x} := by
  refine E.cancel (X := {y}) hc ?_
  have h₂ : E L S ({y} + {z}) 0 := E_pair_zero hinv S hyz
  rw [add_comm] at h₂
  exact h₂.trans (E_pair_zero hinv S hxy).symm

/-- R2, inverse in the unit class: `{x} =_E {x} + {u} =_E {x} + {y} =_E ∅ =_E {u}`. -/
theorem E_r2_inv_unit {L : Laws n} {inv : Fin n → Option (Fin n)} {u : Fin n}
    (hinv : L.HasInv inv) (hu : L.HasUnit u) {S : Set (Monomial n × Monomial n)} {x y : Fin n}
    (hxy : inv x = some y) (hyu : E L S ({y} : Monomial n) {u}) :
    E L S ({x} : Monomial n) {u} := by
  have hu0 : E L S ({u} : Monomial n) 0 := E.law hu
  have h₁ : E L S ({x} : Monomial n) ({x} + {u}) := by
    have := E.congr_left (L := L) (S := S) {x} hu0
    rw [add_zero] at this
    exact this.symm
  have h₂ : E L S ({x} + {u}) ({x} + {y}) := E.congr_left {x} hyu.symm
  exact h₁.trans (h₂.trans ((E_pair_zero hinv S hxy).trans hu0.symm))

/-- R2, child in the unit class: `{y} =_E {y} + {u} =_E {y} + {x} =_E ∅ =_E {u}`. -/
theorem E_r2_unit_inv {L : Laws n} {inv : Fin n → Option (Fin n)} {u : Fin n}
    (hinv : L.HasInv inv) (hu : L.HasUnit u) {S : Set (Monomial n × Monomial n)} {x y : Fin n}
    (hxy : inv x = some y) (hxu : E L S ({x} : Monomial n) {u}) :
    E L S ({y} : Monomial n) {u} := by
  have hu0 : E L S ({u} : Monomial n) 0 := E.law hu
  have h₁ : E L S ({y} : Monomial n) ({y} + {u}) := by
    have := E.congr_left (L := L) (S := S) {y} hu0
    rw [add_zero] at this
    exact this.symm
  have h₂ : E L S ({y} + {u}) ({y} + {x}) := E.congr_left {y} hxu.symm
  have h₃ : E L S ({y} + {x}) 0 := by rw [add_comm]; exact E_pair_zero hinv S hxy
  exact h₁.trans (h₂.trans (h₃.trans hu0.symm))

/-- R3: `B + {y} =_E A + {y} = (A ∖ a) + ({a} + {y}) =_E A ∖ a`. -/
theorem E_r3 {L : Laws n} {inv : Fin n → Option (Fin n)} (hinv : L.HasInv inv)
    {S : Set (Monomial n × Monomial n)} {A B : Monomial n} {a y : Fin n}
    (hAB : E L S A B) (ha : a ∈ A) (hay : inv a = some y) :
    E L S (B + {y}) (A.erase a) := by
  have hA : A = A.erase a + {a} := by
    rw [add_comm, Multiset.singleton_add, Multiset.cons_erase ha]
  have h₁ : E L S (B + {y}) (A + {y}) := hAB.symm.congr {y}
  have h₂ : E L S (A + {y}) (A.erase a + ({a} + {y})) := by
    rw [hA, add_assoc, Multiset.erase_add_right_pos _ (Multiset.mem_singleton_self a),
      Multiset.erase_singleton, add_zero]
    exact E.refl _
  have h₃ : E L S (A.erase a + ({a} + {y})) (A.erase a + 0) :=
    E.congr_left _ (E_pair_zero hinv S hay)
  rw [add_zero] at h₃
  exact h₁.trans (h₂.trans h₃)

/-- R3, overlap at `inv x`: `B + {x} =_E A + {x} = (A ∖ y) + ({x} + {y}) =_E A ∖ y`. -/
theorem E_r3_right {L : Laws n} {inv : Fin n → Option (Fin n)} (hinv : L.HasInv inv)
    {S : Set (Monomial n × Monomial n)} {A B : Monomial n} {x y : Fin n}
    (hAB : E L S A B) (hxy : inv x = some y) (hy : y ∈ A) :
    E L S (B + {x}) (A.erase y) := by
  have hA : A = A.erase y + {y} := by
    rw [add_comm, Multiset.singleton_add, Multiset.cons_erase hy]
  have h₁ : E L S (B + {x}) (A + {x}) := hAB.symm.congr {x}
  have h₂ : E L S (A + {x}) (A.erase y + ({x} + {y})) := by
    rw [hA, add_assoc, Multiset.erase_add_right_pos _ (Multiset.mem_singleton_self y),
      Multiset.erase_singleton, add_zero, add_comm ({x} : Monomial n)]
    exact E.refl _
  have h₃ : E L S (A.erase y + ({x} + {y})) (A.erase y + 0) :=
    E.congr_left _ (E_pair_zero hinv S hxy)
  rw [add_zero] at h₃
  exact h₁.trans (h₂.trans h₃)

/-- R4: `x^(k−1) + {x} = xᵏ =_E ∅ =_E {y} + {x}`; cancel `{x}`. -/
theorem E_r4 {L : Laws n} {inv : Fin n → Option (Fin n)} {k : ℕ} (hinv : L.HasInv inv)
    (hnil : L.HasNil k) (hc : L.cancellative) (hk : 1 ≤ k) {S : Set (Monomial n × Monomial n)}
    {x y : Fin n} (hxy : inv x = some y) :
    E L S (Multiset.replicate (k - 1) x) {y} := by
  refine E.cancel (X := {x}) hc ?_
  have e : Multiset.replicate (k - 1) x + {x} = Multiset.replicate k x := by
    rw [add_comm, Multiset.singleton_add, ← Multiset.replicate_succ]
    congr 1; omega
  rw [e]
  have h₂ : E L S ({x} + {y}) 0 := E_pair_zero hinv S hxy
  rw [add_comm] at h₂
  exact (E.law (hnil x)).trans h₂.symm

/-- R5: `y^(k−1) + {y} = yᵏ =_E ∅ =_E {x} + {y}`; cancel `{y}`. -/
theorem E_r5 {L : Laws n} {inv : Fin n → Option (Fin n)} {k : ℕ} (hinv : L.HasInv inv)
    (hnil : L.HasNil k) (hc : L.cancellative) (hk : 1 ≤ k) {S : Set (Monomial n × Monomial n)}
    {x y : Fin n} (hxy : inv x = some y) :
    E L S (Multiset.replicate (k - 1) y) {x} := by
  refine E.cancel (X := {y}) hc ?_
  have e : Multiset.replicate (k - 1) y + {y} = Multiset.replicate k y := by
    rw [add_comm, Multiset.singleton_add, ← Multiset.replicate_succ]
    congr 1; omega
  rw [e]
  exact (E.law (hnil y)).trans (E_pair_zero hinv S hxy).symm

/-- Each R1/R3 step preserves `I2`. -/
theorem invInfer_I2 {L : Laws n} {inv : Fin n → Option (Fin n)} (hinv : L.HasInv inv)
    (hc : L.cancellative) {S : Set (Monomial n × Monomial n)} {st st' : State n}
    (hstep : InvInfer L inv st st') (h : I2 L S st) : I2 L S st' := by
  cases hstep with
  | mint hfresh => exact addNode_fresh_I2 h hfresh
  | r1_inj hay hcy hy hy' hyy ha hc' =>
    exact merge_I2 h ha hc' (E_r1_inj hinv hc hay hcy (E_atoms h hy hy' hyy))
  | r1_inv hxy hyz hx hz => exact merge_I2 h hz hx (E_r1_inv hinv hc hxy hyz)
  | r3_left hAB ha hay hBy hAa =>
    refine merge_I2 h hBy hAa ?_
    exact (E_clamp L S _).trans ((E_r3 hinv (rules_sound h _ _ hAB) ha hay).trans
      (E_clamp L S _).symm)
  | r3_right hAB hxy hy hBx hAy =>
    refine merge_I2 h hBx hAy ?_
    exact (E_clamp L S _).trans ((E_r3_right hinv (rules_sound h _ _ hAB) hxy hy).trans
      (E_clamp L S _).symm)

/-- Each R2/R4/R5 step preserves `I2`. -/
theorem invInferUK_I2 {L : Laws n} {inv : Fin n → Option (Fin n)} {u : Fin n} {k : ℕ}
    (hinv : L.HasInv inv) (hu : L.HasUnit u) (hnil : L.HasNil k) (hc : L.cancellative)
    (hk : 1 ≤ k) {S : Set (Monomial n × Monomial n)} {st st' : State n}
    (hstep : InvInferUK L inv u k st st') (h : I2 L S st) : I2 L S st' := by
  cases hstep with
  | r2_inv_unit hxy hy hu' hyu hx =>
    exact merge_I2 h hx hu' (E_r2_inv_unit hinv hu hxy (E_atoms h hy hu' hyu))
  | r2_unit_inv hxy hx hu' hxu hy =>
    exact merge_I2 h hy hu' (E_r2_unit_inv hinv hu hxy (E_atoms h hx hu' hxu))
  | r4 hxy hxk hy =>
    exact merge_I2 h hxk hy ((E_clamp L S _).trans (E_r4 hinv hnil hc hk hxy))
  | r5 hxy hne hyk hx =>
    exact merge_I2 h hyk hx ((E_clamp L S _).trans (E_r5 hinv hnil hc hk hxy))

/-! ## Soundness of a run -/

/-- Reachability under `Infer` and the R1/R3 steps. -/
def ReachableInv (L : Laws n) (inv : Fin n → Option (Fin n)) : State n → State n → Prop :=
  ReflTransGen (fun s t => Infer L s t ∨ InvInfer L inv s t)

/-- Reachability under `Infer` and all of R1-R5. -/
def ReachableInvUK (L : Laws n) (inv : Fin n → Option (Fin n)) (u : Fin n) (k : ℕ) :
    State n → State n → Prop :=
  ReflTransGen (fun s t => Infer L s t ∨ InvInfer L inv s t ∨ InvInferUK L inv u k s t)

/-- `completion_sound` extended by R1 and R3: every state reachable from a
sound state is sound. -/
theorem inv_rules_sound {L : Laws n} {inv : Fin n → Option (Fin n)} (hinv : L.HasInv inv)
    (hc : L.cancellative) {S : Set (Monomial n × Monomial n)} {st₀ st : State n}
    (hreach : ReachableInv L inv st₀ st) (h₀ : I2 L S st₀) : I2 L S st := by
  induction hreach with
  | refl => exact h₀
  | tail _ hstep ih =>
    rcases hstep with hstep | hstep
    · exact Infer_I2 hstep ih
    · exact invInfer_I2 hinv hc hstep ih

/-- `completion_sound` extended by R1-R5. -/
theorem inv_rules_sound_uk {L : Laws n} {inv : Fin n → Option (Fin n)} {u : Fin n} {k : ℕ}
    (hinv : L.HasInv inv) (hu : L.HasUnit u) (hnil : L.HasNil k) (hc : L.cancellative)
    (hk : 1 ≤ k) {S : Set (Monomial n × Monomial n)} {st₀ st : State n}
    (hreach : ReachableInvUK L inv u k st₀ st) (h₀ : I2 L S st₀) : I2 L S st := by
  induction hreach with
  | refl => exact h₀
  | tail _ hstep ih =>
    rcases hstep with hstep | hstep | hstep
    · exact Infer_I2 hstep ih
    · exact invInfer_I2 hinv hc hstep ih
    · exact invInferUK_I2 hinv hu hnil hc hk hstep ih

/-- The instance for `Laws.inverse`: `:inverse` implies cancellative. -/
theorem inv_rules_sound_inverse (inv : Fin n → Option (Fin n)) (cancel : Prop) (hc : cancel)
    {S : Set (Monomial n × Monomial n)} {st₀ st : State n}
    (hreach : ReachableInv (Laws.inverse inv cancel) inv st₀ st)
    (h₀ : I2 (Laws.inverse inv cancel) S st₀) : I2 (Laws.inverse inv cancel) S st :=
  inv_rules_sound (inverse_hasInv inv cancel) hc hreach h₀

/-- The instance for `Laws.combined`. -/
theorem inv_rules_sound_combined (u : Fin n) (k : ℕ) (hk : 2 ≤ k) (inv : Fin n → Option (Fin n))
    (cancel : Prop) (hu : InvUnitFree inv u) (hc : cancel)
    {S : Set (Monomial n × Monomial n)} {st₀ st : State n}
    (hreach : ReachableInvUK (Laws.combined u k hk inv cancel hu) inv u k st₀ st)
    (h₀ : I2 (Laws.combined u k hk inv cancel hu) S st₀) :
    I2 (Laws.combined u k hk inv cancel hu) S st :=
  inv_rules_sound_uk (combined_hasInv u k hk inv cancel hu) (combined_hasUnit u k hk inv cancel hu)
    (combined_hasNil u k hk inv cancel hu) (Or.inl (Or.inl hc)) (by omega) hreach h₀

end SemperProofs.CC
