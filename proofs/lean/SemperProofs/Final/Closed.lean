import SemperProofs.Final.Store
import SemperProofs.Fidelity.RecanonComplete
import SemperProofs.CC.Laws.InvRules

/-!
# The store's closure under the theory, from the completion state

`saturation_complete_closed` (`Fidelity/RecanonComplete.lean`) takes
`TheoryClosed A.Sa L`: two classes of the store equal modulo the laws and the
store's equations are one class. This file derives it from the completion
hypotheses across the correspondence `SubRep`, the inverse direction of
`ACStep.mapE`: a chain of normalization steps on the store (splices through
stored nodes, unit drops, nilpotent clamps, inverse cancellations) is read
as an `=_E`-equality between monomials of the completion state, and
`ac_equal_same_class` puts the two classes together.

* `Noded`, `HoldsAtom`: a store class holds a node of the state, or the
  one-element monomial of an atom. `readClass` reads a store class as the
  monomial of one such node (`0` for a class holding none); `readMset`
  reads a child multiset as the sum of its elements' readings. Two nodes
  of one class are `=_E`-equal (`I2`), so the reading is determined up to
  the theory (`read_eq_node`).
* `LawsRead`: the laws of `f` as the store reads them (`OpLaws`) agree with
  the laws of the state: the unit's class holds the empty node, the
  nilpotent order is a law instance of order at least two, and an inverse
  pair is a law instance on the two atoms its classes hold.
* `SummandsAtomic`: the class of each summand of a stored `f`-node holds
  its one-element monomial, which the completion view `withAtoms` supplies
  for the atomic classes (`summandsAtomic_withAtoms`).
* `ACStep.readE`, `EqAC.readE`: one step, then a chain, is an `=_E`-equality
  of the readings. `ACStep.count_mod`, `EqAC.count_mod`: the count of a
  class holding no node is invariant modulo the nilpotent order, so a chain
  between two singletons starts and ends at noded classes or is trivial
  (`eq_of_chain_not_noded`).
* `closedAC_of_complete_covered`: the store is closed under the theory of
  `f`; `theoryClosed_of_complete_covered`: `TheoryClosed` from it, the
  remainder `TheoryClosedRest` (the other operators and the ACI and A
  theories), the hash-cons dedup and sorted pairs. A retired node is
  `=_E`-equal to an active node of its class by `RetiredCovered` and `I2`.
* `saturation_complete_closed_of_complete_covered`, `_atoms_covered`:
  `saturation_complete_closed` with the completion hypotheses in place of
  `TheoryClosed`.

`Final/Witness.lean` proves every hypothesis on the run of the witness
(`witness_theoryClosed`, `witness_saturation_complete_closed`).
-/

namespace SemperProofs.Final

open Semper.EMatch Semper.EMatch.Fidelity SemperProofs.CC SemperProofs.CC.Bridge

variable {n : ℕ}

/-! ## Reading the store's classes in the state -/

/-- The store class `x` holds a node of the state: some node `(M, d)` of
`st` has its class read in the store as `x`. -/
def Noded (st : State n) (x : C) : Prop :=
  ∃ (M : Monomial n) (d : Fin n), (M, d) ∈ st.nodes ∧ clsId (st.find d) = x

/-- The store class `x` holds the atom `y`: the one-element monomial `{y}`
is a node of `st` in a class read as `x`. -/
def HoldsAtom (st : State n) (x : C) (y : Fin n) : Prop :=
  ∃ c, (({y} : Monomial n), c) ∈ st.nodes ∧ clsId (st.find c) = x

theorem HoldsAtom.noded {st : State n} {x : C} {y : Fin n} (h : HoldsAtom st x y) : Noded st x :=
  let ⟨c, hc, hx⟩ := h; ⟨_, c, hc, hx⟩

theorem clsId_inj {a b : Fin n} (h : clsId a = clsId b) : a = b := Fin.ext h

open Classical in
/-- The reading of a store class: the monomial of a node of the state in
that class, or `0` when the class holds none. -/
noncomputable def readClass (st : State n) (x : C) : Monomial n :=
  if h : Noded st x then h.choose else 0

theorem readClass_spec {st : State n} {x : C} (h : Noded st x) :
    ∃ d, (readClass st x, d) ∈ st.nodes ∧ clsId (st.find d) = x := by
  rw [readClass, dif_pos h]
  exact h.choose_spec

theorem readClass_of_not {st : State n} {x : C} (h : ¬ Noded st x) : readClass st x = 0 := by
  rw [readClass, dif_neg h]

/-- The reading of a child multiset: the sum of the readings. -/
noncomputable def readMset (st : State n) (m : Multiset C) : Monomial n :=
  (m.map (readClass st)).sum

@[simp] theorem readMset_add (st : State n) (m m' : Multiset C) :
    readMset st (m + m') = readMset st m + readMset st m' := by
  simp [readMset]

@[simp] theorem readMset_singleton (st : State n) (x : C) : readMset st {x} = readClass st x := by
  simp [readMset]

theorem readMset_nsmul (st : State n) (r : ℕ) (m : Multiset C) :
    readMset st (r • m) = r • readMset st m := by
  simp [readMset, Multiset.map_nsmul, Multiset.sum_nsmul]

/-- Under `I2`, the reading of a class is `=_E`-equal to every node of the
state in that class. -/
theorem read_eq_node {L : Laws n} {S : Set (Monomial n × Monomial n)} {st : State n}
    (h2 : I2 L S st) {x : C} {M : Monomial n} {d : Fin n} (hM : (M, d) ∈ st.nodes)
    (hx : clsId (st.find d) = x) : E L S (readClass st x) M := by
  obtain ⟨d', hd', hx'⟩ := readClass_spec ⟨M, d, hM, hx⟩
  exact h2 _ _ _ _ hd' hM (clsId_inj (hx'.trans hx.symm))

/-! ## Lemmas on `=_E` -/

theorem E_add_add {L : Laws n} {S : Set (Monomial n × Monomial n)} {a b c d : Monomial n}
    (h₁ : E L S a b) (h₂ : E L S c d) : E L S (a + c) (b + d) := by
  have e₁ : E L S (a + c) (b + c) := E.congr c h₁
  have e₂ : E L S (c + b) (d + b) := E.congr b h₂
  rw [add_comm c b, add_comm d b] at e₂
  exact e₁.trans e₂

theorem E_sum_map {L : Laws n} {S : Set (Monomial n × Monomial n)} {α : Type}
    (m : Multiset α) {a b : α → Monomial n} (h : ∀ y ∈ m, E L S (a y) (b y)) :
    E L S (m.map a).sum (m.map b).sum := by
  induction m using Multiset.induction_on with
  | empty => simp only [Multiset.map_zero, Multiset.sum_zero]; exact E.refl _
  | cons y m ih =>
      simp only [Multiset.map_cons, Multiset.sum_cons]
      exact E_add_add (h y (Multiset.mem_cons_self y m))
        (ih (fun z hz => h z (Multiset.mem_cons_of_mem hz)))

/-- The nilpotent law on atoms lifts to every monomial. -/
theorem E_nsmul_zero {L : Laws n} {S : Set (Monomial n × Monomial n)} {r : ℕ} (hr : L.HasNil r)
    (M : Monomial n) : E L S (r • M) 0 := by
  induction M using Multiset.induction_on with
  | empty => simp only [smul_zero]; exact E.refl _
  | cons y M ih =>
      rw [← Multiset.singleton_add, nsmul_add, Multiset.nsmul_singleton]
      have h := E_add_add (E.law (L := L) (S := S) (hr y)) ih
      rwa [add_zero] at h

/-! ## The laws and the summands across the correspondence -/

/-- The laws of `f` as the store reads them agree with the laws of the
state: the unit's class holds the empty node; the nilpotent order is at
least two and a law instance on every atom (`Laws.HasNil`); for an inverse
pair, the cancelled class and the class of the stored `inv` node hold two
atoms whose pair is a law instance (`Laws.HasInv`). -/
structure LawsRead (S : Store) (L : Sym → OpLaws) (f : Sym) (st : State n) (Lc : Laws n) :
    Prop where
  unit : ∀ u, (L f).unit = some u →
    ∃ c, ((0 : Monomial n), c) ∈ st.nodes ∧ clsId (st.find c) = S.find u
  nil : ∀ r, (L f).nilpotent = some r → 2 ≤ r ∧ Lc.HasNil r
  inv : ∀ g, (L f).invOp = some g → ∀ id x, (id, ⟨g, .tuple [x]⟩) ∈ S.nodes →
    ∃ x' y', HoldsAtom st x x' ∧ HoldsAtom st (S.find id) y' ∧
      Lc.lawRel ({x', y'} : Monomial n) 0

/-- An operator the store reads with no law. -/
theorem LawsRead.of_none {S : Store} {L : Sym → OpLaws} {f : Sym} {st : State n} {Lc : Laws n}
    (hu : (L f).unit = none) (hn : (L f).nilpotent = none) (hi : (L f).invOp = none) :
    LawsRead S L f st Lc where
  unit u h := by rw [hu] at h; cases h
  nil r h := by rw [hn] at h; cases h
  inv g h := by rw [hi] at h; cases h

/-- The class of every summand of a stored `f`-node holds the summand's
one-element monomial. -/
def SummandsAtomic (st : State n) (N : Finset (Monomial n × Fin n)) : Prop :=
  ∀ p ∈ N, ∀ y ∈ p.1, HoldsAtom st (clsId (st.find y)) y

/-- The completion view supplies it for summands in the atomic set. -/
theorem summandsAtomic_withAtoms {st : State n} {X : Set (Fin n)} {u : Option (Fin n)}
    {N : Finset (Monomial n × Fin n)} (hX : ∀ p ∈ N, ∀ y ∈ p.1, y ∈ X) :
    SummandsAtomic (st.withAtoms X u) N :=
  fun p hp y hy => ⟨y, Or.inr (Or.inl ⟨hX p hp y hy, rfl⟩), rfl⟩

theorem Stored.withAtoms {st : State n} {N : Finset (Monomial n × Fin n)} (h : Stored st N)
    (X : Set (Fin n)) (u : Option (Fin n)) : Stored (st.withAtoms X u) N :=
  fun p hp => Or.inl (h p hp)

/-! ## One step, then a chain, read in the state -/

section Chain

variable {Lc : Laws n} {St : Set (Monomial n × Monomial n)} {st : State n} {S : Store}
  {f : Sym} {N : Finset (Monomial n × Fin n)} {ι : Monomial n × Fin n → NodeId}
  {L : Sym → OpLaws}

/-- A stored `f`-node is the node of some `p ∈ N`, with the children of
`mkNode st f p` and the class `st` gives it. -/
theorem stored_node_eq (hk : S.graph.KeysNodup) (hs : SubRep S.graph st f N ι)
    (hcov : FCover S.graph f N ι) {id : NodeId} {m : Multiset C}
    (hmem : (id, ⟨f, .mset m⟩) ∈ S.nodes) :
    ∃ p ∈ N, id = ι p ∧ m = p.1.map (fun x => clsId (st.find x)) ∧
      S.find id = clsId (st.find p.2) := by
  obtain ⟨p, hp, rfl⟩ := hcov id _ hmem rfl
  have hnd := hs.node_eq hk hp hmem
  simp only [mkNode, Node.mk.injEq, Children.mset.injEq] at hnd
  exact ⟨p, hp, rfl, hnd.2, hs.find p hp⟩

/-- **One normalization step on the store is an `=_E`-equality of the
readings.** A splice through the node of `p` reads as `p.1` against the
readings of its summands' classes; a unit drop as the empty node; a
nilpotent clamp as the law on every atom; an inverse cancellation as the
law on the two atoms. -/
theorem ACStep.readE (hk : S.graph.KeysNodup) (hN : Stored st N) (hs : SubRep S.graph st f N ι)
    (hcov : FCover S.graph f N ι) (hsum : SummandsAtomic st N) (hlaws : LawsRead S L f st Lc)
    (h2 : I2 Lc St st) {m m' : Multiset C} (hstep : ACStep S.graph L f m m') :
    E Lc St (readMset st m) (readMset st m') := by
  cases hstep with
  | @splice m₁ rest id hmem =>
      obtain ⟨p, hp, rfl, rfl, hfind⟩ := stored_node_eq hk hs hcov hmem
      rw [readMset_add, readMset_add, readMset_singleton]
      apply E.congr
      refine (read_eq_node h2 (hN p hp) hfind.symm).trans ?_
      show E Lc St p.1 ((p.1.map (fun x => clsId (st.find x))).map (readClass st)).sum
      rw [Multiset.map_map]
      conv_lhs => rw [← Multiset.sum_map_singleton p.1]
      apply E_sum_map
      intro y hy
      obtain ⟨c, hc, hcy⟩ := hsum p hp y hy
      exact (read_eq_node h2 hc hcy).symm
  | @unit u rest hu =>
      obtain ⟨c, hc, hcu⟩ := hlaws.unit u hu
      rw [readMset_add, readMset_singleton]
      have h := E.congr (readMset st m') (read_eq_node h2 hc hcu)
      rwa [zero_add] at h
  | @nil r x rest hr =>
      obtain ⟨-, hnil⟩ := hlaws.nil r hr
      rw [readMset_add, readMset_nsmul, readMset_singleton]
      have h := E.congr (readMset st m') (E_nsmul_zero (S := St) hnil (readClass st x))
      rwa [zero_add] at h
  | @inv g x id rest hg hmem =>
      obtain ⟨x', y', ⟨c, hc, hcx⟩, ⟨c', hc', hcy⟩, hlaw⟩ := hlaws.inv g hg id x hmem
      rw [readMset_add, readMset_add, readMset_singleton, readMset_singleton]
      have e₁ := E_add_add (read_eq_node h2 hc hcx) (read_eq_node h2 hc' hcy)
      have e₂ : E Lc St ({x'} + {y'}) 0 := by
        have h := E.law (L := Lc) (S := St) hlaw
        rwa [Multiset.insert_eq_cons, ← Multiset.singleton_add] at h
      have h := E.congr (readMset st m') (e₁.trans e₂)
      rwa [zero_add] at h

/-- A chain of steps is an `=_E`-equality of the readings. -/
theorem EqAC.readE (hk : S.graph.KeysNodup) (hN : Stored st N) (hs : SubRep S.graph st f N ι)
    (hcov : FCover S.graph f N ι) (hsum : SummandsAtomic st N) (hlaws : LawsRead S L f st Lc)
    (h2 : I2 Lc St st) {m m' : Multiset C} (h : EqAC S.graph L f m m') :
    E Lc St (readMset st m) (readMset st m') := by
  induction h with
  | rel _ _ hab => exact ACStep.readE hk hN hs hcov hsum hlaws h2 hab
  | refl => exact E.refl _
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- The nilpotent order the store reads, `0` when there is none. -/
def nilOrder (L : Sym → OpLaws) (f : Sym) : ℕ := ((L f).nilpotent).getD 0

theorem count_singleton_of_ne {z x : C} (h : z ≠ x) : Multiset.count z ({x} : Multiset C) = 0 := by
  rw [Multiset.count_singleton, if_neg h]

/-- **The count of a class holding no node is invariant modulo the
nilpotent order.** Every class a splice, a unit drop or an inverse
cancellation touches holds a node; a nilpotent clamp moves `r` copies. -/
theorem ACStep.count_mod (hk : S.graph.KeysNodup) (hN : Stored st N)
    (hs : SubRep S.graph st f N ι) (hcov : FCover S.graph f N ι) (hsum : SummandsAtomic st N)
    (hlaws : LawsRead S L f st Lc) {z : C} (hz : ¬ Noded st z) {m m' : Multiset C}
    (hstep : ACStep S.graph L f m m') :
    m.count z % nilOrder L f = m'.count z % nilOrder L f := by
  cases hstep with
  | @splice m₁ rest id hmem =>
      obtain ⟨p, hp, rfl, rfl, hfind⟩ := stored_node_eq hk hs hcov hmem
      have h₁ : z ≠ S.graph.find (ι p) := fun h => hz ⟨p.1, p.2, hN p hp, by rw [h]; exact hfind.symm⟩
      have h₂ : z ∉ p.1.map (fun x => clsId (st.find x)) := by
        intro hzm
        obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 hzm
        exact hz (hsum p hp y hy).noded
      rw [Multiset.count_add, Multiset.count_add, count_singleton_of_ne h₁,
        Multiset.count_eq_zero.2 h₂]
  | @unit u rest hu =>
      obtain ⟨c, hc, hcu⟩ := hlaws.unit u hu
      have h₁ : z ≠ S.graph.find u := fun h => hz ⟨0, c, hc, by rw [h]; exact hcu⟩
      rw [Multiset.count_add, count_singleton_of_ne h₁, zero_add]
  | @nil r x rest hr =>
      have hord : nilOrder L f = r := by simp [nilOrder, hr]
      rw [Multiset.count_add, Multiset.count_nsmul, hord, Nat.mul_add_mod]
  | @inv g x id rest hg hmem =>
      obtain ⟨x', y', hx, hy, -⟩ := hlaws.inv g hg id x hmem
      have h₁ : z ≠ x := fun h => hz (h ▸ hx.noded)
      have h₂ : z ≠ S.graph.find id := fun h => hz (h ▸ hy.noded)
      rw [Multiset.count_add, Multiset.count_add, count_singleton_of_ne h₁,
        count_singleton_of_ne h₂, zero_add, zero_add]

theorem EqAC.count_mod (hk : S.graph.KeysNodup) (hN : Stored st N)
    (hs : SubRep S.graph st f N ι) (hcov : FCover S.graph f N ι) (hsum : SummandsAtomic st N)
    (hlaws : LawsRead S L f st Lc) {z : C} (hz : ¬ Noded st z) {m m' : Multiset C}
    (h : EqAC S.graph L f m m') : m.count z % nilOrder L f = m'.count z % nilOrder L f :=
  eqvGen_invariant (fun m : Multiset C => m.count z % nilOrder L f)
    (fun _ _ hs' => ACStep.count_mod hk hN hs hcov hsum hlaws hz hs') h

/-- A chain between two singletons whose first class holds no node is
trivial: the count of that class moves by multiples of the nilpotent order,
which is `0` (no nilpotent law) or at least `2`. -/
theorem eq_of_chain_not_noded (hk : S.graph.KeysNodup) (hN : Stored st N)
    (hs : SubRep S.graph st f N ι) (hcov : FCover S.graph f N ι) (hsum : SummandsAtomic st N)
    (hlaws : LawsRead S L f st Lc) {x x' : C} (hx : ¬ Noded st x)
    (h : EqAC S.graph L f {x} {x'}) : x = x' := by
  by_contra hne
  have hc := EqAC.count_mod hk hN hs hcov hsum hlaws hx h
  rw [Multiset.count_singleton_self, count_singleton_of_ne hne, Nat.zero_mod] at hc
  have hone : nilOrder L f = 1 := Nat.dvd_one.1 (Nat.dvd_of_mod_eq_zero hc)
  unfold nilOrder at hone
  cases hr : (L f).nilpotent with
  | none => rw [hr] at hone; cases hone
  | some r =>
      rw [hr] at hone
      have := (hlaws.nil r hr).1
      simp only [Option.getD_some] at hone
      omega

/-- **The store is closed under the theory of `f`.** A chain between the
singletons of two classes reads as an `=_E`-equality between nodes of the
state in those classes; each is `=_E`-equal to an active node of its class
(`heq`: `node_equal_active_covered` from `RetiredCovered`), and two `=_E`-equal active nodes of a converged
state are in one class (`ac_equal_same_class`). A class holding no node
ends no chain but the trivial one. -/
theorem closedAC_of_complete_of (hcomp : CompleteHyps Lc St st) (h2 : I2 Lc St st)
    (heq : ∀ M c, (M, c) ∈ st.nodes → ∃ q ∈ st.active, E Lc St M q.1 ∧ st.find q.2 = st.find c)
    (hk : S.graph.KeysNodup) (hN : Stored st N) (hs : SubRep S.graph st f N ι)
    (hcov : FCover S.graph f N ι) (hsum : SummandsAtomic st N) (hlaws : LawsRead S L f st Lc) :
    ClosedAC S L f := by
  intro c c' h
  by_cases hx : Noded st (S.find c)
  · by_cases hx' : Noded st (S.find c')
    · obtain ⟨d, hd, hdx⟩ := readClass_spec hx
      obtain ⟨d', hd', hdx'⟩ := readClass_spec hx'
      have hE := EqAC.readE hk hN hs hcov hsum hlaws h2 h
      rw [readMset_singleton, readMset_singleton] at hE
      obtain ⟨q, hq, hEq, hqd⟩ := heq _ _ hd
      obtain ⟨q', hq', hEq', hqd'⟩ := heq _ _ hd'
      have hqq : E Lc St q.1 q'.1 := hEq.symm.trans (hE.trans hEq')
      have hfind := ac_equal_same_class hcomp hq hq' hqq
      rw [← hdx, ← hdx', ← hqd, ← hqd', hfind]
    · exact (eq_of_chain_not_noded hk hN hs hcov hsum hlaws hx' (Relation.EqvGen.symm _ _ h)).symm
  · exact eq_of_chain_not_noded hk hN hs hcov hsum hlaws hx h

/-- **The store is closed under the theory of `f`, from the completion
state.** A node of the state is `=_E`-equal to an active node of its class
by `RetiredCovered` and `I2` (`node_equal_active_covered`). -/
theorem closedAC_of_complete_covered (hcomp : CompleteHyps Lc St st) (h2 : I2 Lc St st)
    (hrc : RetiredCovered st) (hk : S.graph.KeysNodup) (hN : Stored st N)
    (hs : SubRep S.graph st f N ι) (hcov : FCover S.graph f N ι) (hsum : SummandsAtomic st N)
    (hlaws : LawsRead S L f st Lc) : ClosedAC S L f :=
  closedAC_of_complete_of hcomp h2 (fun _ _ h => node_equal_active_covered h2 hrc h) hk hN hs hcov
    hsum hlaws

/-- **`TheoryClosed` from the completion state.** The closure under the
theory of `f` is derived (`closedAC_of_complete_covered`); the remainder
(`TheoryClosedRest`: the other AC operators, the ACI and A theories), the
hash-cons dedup and the sorted pairs are the store's. -/
theorem theoryClosed_of_complete_covered (hcomp : CompleteHyps Lc St st) (h2 : I2 Lc St st)
    (hrc : RetiredCovered st) (hk : S.graph.KeysNodup) (hN : Stored st N)
    (hs : SubRep S.graph st f N ι) (hcov : FCover S.graph f N ι) (hsum : SummandsAtomic st N)
    (hlaws : LawsRead S L f st Lc)
    (hdedup : ∀ id₁ id₂ nd, (id₁, nd) ∈ S.nodes → (id₂, nd) ∈ S.nodes → S.find id₁ = S.find id₂)
    (hsorted : PairsSorted S) (hrest : TheoryClosedRest S L f) : TheoryClosed S L :=
  TheoryClosed.ofParts (closedAC_of_complete_covered hcomp h2 hrc hk hN hs hcov hsum hlaws) hrest
    hdedup hsorted

end Chain

/-! ## Saturation with completion on, from the completion state -/

/-- **`saturation_complete_closed` with the completion hypotheses in place
of `TheoryClosed`.** The run is that of `saturation_complete_closed`; the
store after the fixpoint round holds the nodes of the state's `f`-nodes `N`
(`SubRep` on the store, `FCover`: no other `f`-node, `Stored`), with atomic
summands and the laws read alike; `I2` and `RetiredCovered` make a retired
node `=_E`-equal to an active one of its class
(`theoryClosed_of_complete_covered`). The dedup is the round's
(`StoreWF.dedup`). -/
theorem saturation_complete_closed_of_complete_covered {sig : Sym → Kind} {rules : List Rule}
    {L : Sym → OpLaws} (A₀ : SActRoundN L) (As : List (SActRoundN L)) (hmatch : MatchersOK rules)
    (h₀ : RulesWF sig A₀.R.before rules) (hok : ∀ A ∈ A₀ :: As, RoundOKE sig rules A)
    (hemit₀ : EmitsAllN A₀ rules) (hchain : SChainE rules A₀ As)
    {A : SActRoundN L} (hA : A ∈ A₀ :: As) (hfix : A.Unchanged)
    {Lc : Laws n} {St : Set (Monomial n × Monomial n)} {st : State n}
    (hcomp : CompleteHyps Lc St st) (h2 : I2 Lc St st) (hrc : RetiredCovered st)
    (hk : A.Sa.graph.KeysNodup) {f : Sym} {N : Finset (Monomial n × Fin n)}
    {ι : Monomial n × Fin n → NodeId} (hN : Stored st N) (hs : SubRep A.Sa.graph st f N ι)
    (hcov : FCover A.Sa.graph f N ι) (hsum : SummandsAtomic st N)
    (hlaws : LawsRead A.Sa L f st Lc) (hsorted : PairsSorted A.Sa)
    (hrest : TheoryClosedRest A.Sa L f) :
    ∀ rule ∈ rules, ∀ σ, Matches A.Sa.index rule.atoms σ →
      FiredE A.Sa.graph L σ rule ∧
      ∀ a b, Action.union a b ∈ rule.actions →
        ∀ c₁ c₂, DenN A.Sa.graph L σ a c₁ → DenN A.Sa.graph L σ b c₂ → c₁ = c₂ :=
  saturation_complete_closed A₀ As hmatch h₀ hok hemit₀ hchain hA hfix
    (theoryClosed_of_complete_covered hcomp h2 hrc hk hN hs hcov hsum hlaws (hok A hA).store.dedup
      hsorted hrest)

/-- The same with a completion state with leaf constants: `I2` and the laws
are read on the completion view `st.withAtoms X u`, whose implicit nodes
make every summand in `X` atomic, and `RetiredCovered` of the stored state
is carried to the view (`RetiredCovered.withAtoms`). -/
theorem saturation_complete_closed_of_complete_atoms_covered {sig : Sym → Kind} {rules : List Rule}
    {L : Sym → OpLaws} (A₀ : SActRoundN L) (As : List (SActRoundN L)) (hmatch : MatchersOK rules)
    (h₀ : RulesWF sig A₀.R.before rules) (hok : ∀ A ∈ A₀ :: As, RoundOKE sig rules A)
    (hemit₀ : EmitsAllN A₀ rules) (hchain : SChainE rules A₀ As)
    {A : SActRoundN L} (hA : A ∈ A₀ :: As) (hfix : A.Unchanged)
    {Lc : Laws n} {St : Set (Monomial n × Monomial n)} {st : State n} {X : Set (Fin n)}
    {u : Option (Fin n)} (hcomp : CompleteAtoms Lc St st X u)
    (h2 : I2 Lc St (st.withAtoms X u)) (hrc : RetiredCovered st)
    (hk : A.Sa.graph.KeysNodup) {f : Sym} {N : Finset (Monomial n × Fin n)}
    {ι : Monomial n × Fin n → NodeId} (hN : Stored st N) (hs : SubRep A.Sa.graph st f N ι)
    (hcov : FCover A.Sa.graph f N ι) (hX : ∀ p ∈ N, ∀ y ∈ p.1, y ∈ X)
    (hlaws : LawsRead A.Sa L f (st.withAtoms X u) Lc) (hsorted : PairsSorted A.Sa)
    (hrest : TheoryClosedRest A.Sa L f) :
    ∀ rule ∈ rules, ∀ σ, Matches A.Sa.index rule.atoms σ →
      FiredE A.Sa.graph L σ rule ∧
      ∀ a b, Action.union a b ∈ rule.actions →
        ∀ c₁ c₂, DenN A.Sa.graph L σ a c₁ → DenN A.Sa.graph L σ b c₂ → c₁ = c₂ :=
  saturation_complete_closed_of_complete_covered A₀ As hmatch h₀ hok hemit₀ hchain hA hfix
    (CompleteHyps.ofAtoms hcomp) h2 (RetiredCovered.withAtoms hrc X u) hk (Stored.withAtoms hN X u)
    (hs.withAtoms X u) hcov (summandsAtomic_withAtoms hX) hlaws hsorted hrest

end SemperProofs.Final
