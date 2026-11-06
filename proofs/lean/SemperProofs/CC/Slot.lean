import SemperProofs.CC.Lemmas

/-!
# The min-monomial slot: the refresh fix makes I5 an invariant

Slot-level model of the engine's per-class, per-operator stored minimum
(`classes.min_monomial`): for one AC operator, each class holds a finite set
of active monomials and an optional slot. The engine writes the slot at node
creation (`register_if_fresh`, `egraph.rs:3800-3818`: a fresh node starts a
singleton class whose slot is the node) and folds it on merge
(`fold_min_monomial`, `egraph.rs:1520-1551`: the `degLex`-least of the two
slots). An in-place shrink of a node by recanonization never touches the
slot: that is `shrinkNoRefresh`, and `shrinkNoRefresh_breaks_I5` is the
confirmed repro. The fix is `shrinkRefresh`: fold the shrunk monomial into
the slot. `reachable_I5` shows I5 survives every operation of the fixed
engine, and `fix_sufficient` discharges the I5 hypothesis of
`roundFixed_converged`, so `same_class` applies at convergence.

Retirement (`set_cc_collapsed`, `egraph.rs:3304-3310`, "merge first, mark
second") does not touch the slot either. Its precondition here is the
engine's: the retired node is reducible, so its normal form, a strictly
smaller active node, has been merged into the class before the flag is set.
Under I5 the slot is then at most that normal form, hence not the retired
node, and I5 survives.
-/

namespace SemperProofs.CC

open Relation

variable {n : ℕ}

/-- Per-class state for one operator: the active monomials and the slot. -/
structure SlotState (n : ℕ) where
  active : Fin n → Finset (Monomial n)
  slot : Fin n → Option (Monomial n)

namespace SlotState

/-- Fold two slots: the `degLex`-least, `none` acting as the identity
(`fold_min_monomial`, both `None` arms). -/
def omin (x y : Option (Monomial n)) : Option (Monomial n) :=
  match x, y with
  | none, y => y
  | some a, none => some a
  | some a, some b => if degLex a b then some b else some a

/-- `m` is the `degLex`-least element of `A`. -/
def IsMin (m : Monomial n) (A : Finset (Monomial n)) : Prop :=
  m ∈ A ∧ ∀ m' ∈ A, m' = m ∨ degLex m' m

/-- A slot is good for a set when it names the set's least element, and is
`none` exactly when the set is empty. -/
def Good (x : Option (Monomial n)) (A : Finset (Monomial n)) : Prop :=
  (A.Nonempty → ∃ m, x = some m ∧ IsMin m A) ∧ (A = ∅ → x = none)

/-- I5 at slot level: every class's slot is good for its active set. -/
def I5 (st : SlotState n) : Prop := ∀ c, Good (st.slot c) (st.active c)

variable (st : SlotState n)

/-- A fresh node in a fresh class (`register_if_fresh`): the slot is the node. -/
def mint (c : Fin n) (M : Monomial n) : SlotState n :=
  ⟨fun x => if x = c then {M} else st.active x,
   fun x => if x = c then some M else st.slot x⟩

/-- A node added to an existing class with the slot folded. The engine never
does this directly (a fresh node always starts a singleton class, then
merges), but it is the composite of `mint` and `merge`. -/
def mintInto (c : Fin n) (M : Monomial n) : SlotState n :=
  ⟨fun x => if x = c then insert M (st.active x) else st.active x,
   fun x => if x = c then omin (st.slot x) (some M) else st.slot x⟩

/-- Merge `c` into `d` (`fold_min_monomial`): `d` survives with the union of
the active sets and the folded slot; `c` is emptied. -/
def merge (c d : Fin n) : SlotState n :=
  ⟨fun x => if x = d then st.active c ∪ st.active d else if x = c then ∅ else st.active x,
   fun x => if x = d then omin (st.slot c) (st.slot d) else if x = c then none else st.slot x⟩

/-- In-place shrink of an active node `M` of class `c` to `M'`, slot
untouched: the engine as it stands. -/
def shrinkNoRefresh (c : Fin n) (M M' : Monomial n) : SlotState n :=
  ⟨fun x => if x = c then insert M' ((st.active x).erase M) else st.active x, st.slot⟩

/-- The fix: the same shrink with the shrunk monomial folded into the slot. -/
def shrinkRefresh (c : Fin n) (M M' : Monomial n) : SlotState n :=
  ⟨fun x => if x = c then insert M' ((st.active x).erase M) else st.active x,
   fun x => if x = c then omin (st.slot x) (some M') else st.slot x⟩

/-- Retire an active node (`FLAG_AC_COLLAPSED`); the slot is untouched. -/
def retire (c : Fin n) (M : Monomial n) : SlotState n :=
  ⟨fun x => if x = c then (st.active x).erase M else st.active x, st.slot⟩

/-- The operations of the fixed engine, with the engine's preconditions. -/
inductive Op : SlotState n → SlotState n → Prop
  | mint {st : SlotState n} {c : Fin n} {M : Monomial n} :
      st.active c = ∅ → Op st (st.mint c M)
  | mintInto {st : SlotState n} {c : Fin n} {M : Monomial n} :
      Op st (st.mintInto c M)
  | merge {st : SlotState n} {c d : Fin n} :
      c ≠ d → Op st (st.merge c d)
  | shrink {st : SlotState n} {c : Fin n} {M M' : Monomial n} :
      M ∈ st.active c → degLex M M' → Op st (st.shrinkRefresh c M M')
  | retire {st : SlotState n} {c : Fin n} {M : Monomial n} :
      M ∈ st.active c → (∃ N ∈ st.active c, degLex M N) → Op st (st.retire c M)

/-- Runs of the fixed engine. -/
def OpsStar : SlotState n → SlotState n → Prop := ReflTransGen Op

/-! ## Good slots under each operation -/

theorem good_empty : Good (none : Option (Monomial n)) ∅ :=
  ⟨fun h => absurd h Finset.not_nonempty_empty, fun _ => rfl⟩

theorem good_singleton (M : Monomial n) : Good (some M) {M} :=
  ⟨fun _ => ⟨M, rfl, Finset.mem_singleton_self M,
      fun _ hm' => Or.inl (Finset.mem_singleton.mp hm')⟩,
   fun h => absurd h (Finset.singleton_ne_empty M)⟩

theorem isMin_union_left {a b : Monomial n} {A B : Finset (Monomial n)}
    (ha : IsMin a A) (hb : IsMin b B) (hab : ¬ degLex a b) : IsMin a (A ∪ B) := by
  refine ⟨Finset.mem_union_left _ ha.1, fun m' hm' => ?_⟩
  rcases Finset.mem_union.mp hm' with h | h
  · exact ha.2 m' h
  · rcases hb.2 m' h with h' | h'
    · subst h'
      rcases degLex_trichotomous a m' with h'' | h'' | h''
      · exact absurd h'' hab
      · exact Or.inl h''.symm
      · exact Or.inr h''
    · rcases degLex_trichotomous a b with h'' | h'' | h''
      · exact absurd h'' hab
      · subst h''; exact Or.inr h'
      · exact Or.inr (degLex_trans h' h'')

theorem good_omin {x y : Option (Monomial n)} {A B : Finset (Monomial n)}
    (hx : Good x A) (hy : Good y B) : Good (omin x y) (A ∪ B) := by
  constructor
  · intro hne
    by_cases hA : A = ∅
    · subst hA
      have := hx.2 rfl
      subst this
      simp only [Finset.empty_union] at hne ⊢
      obtain ⟨m, hm, hmin⟩ := hy.1 hne
      exact ⟨m, by simp [omin, hm], hmin⟩
    · obtain ⟨a, ha, hamin⟩ := hx.1 (Finset.nonempty_iff_ne_empty.mpr hA)
      by_cases hB : B = ∅
      · subst hB
        have := hy.2 rfl
        subst this
        simp only [Finset.union_empty]
        exact ⟨a, by simp [omin, ha], hamin⟩
      · obtain ⟨b, hb, hbmin⟩ := hy.1 (Finset.nonempty_iff_ne_empty.mpr hB)
        subst ha; subst hb
        by_cases hab : degLex a b
        · refine ⟨b, by simp [omin, hab], ?_⟩
          rw [Finset.union_comm]
          refine isMin_union_left hbmin hamin ?_
          intro h; exact degLex_irrefl a (degLex_trans hab h)
        · exact ⟨a, by simp [omin, hab], isMin_union_left hamin hbmin hab⟩
  · intro h
    rw [Finset.union_eq_empty] at h
    rw [hx.2 h.1, hy.2 h.2]
    rfl

theorem good_shrink {x : Option (Monomial n)} {A : Finset (Monomial n)} {M M' : Monomial n}
    (hx : Good x A) (hM : M ∈ A) (hMM' : degLex M M') :
    Good (omin x (some M')) (insert M' (A.erase M)) := by
  obtain ⟨m, hm, hmin⟩ := hx.1 ⟨M, hM⟩
  subst hm
  refine ⟨fun _ => ?_, fun h => absurd h (Finset.insert_ne_empty _ _)⟩
  by_cases hmM' : degLex m M'
  · refine ⟨M', by simp [omin, hmM'], Finset.mem_insert_self _ _, fun m' hm' => ?_⟩
    rcases Finset.mem_insert.mp hm' with h | h
    · exact Or.inl h
    · have hm'A := Finset.mem_of_mem_erase h
      rcases hmin.2 m' hm'A with h' | h'
      · subst h'; exact Or.inr hmM'
      · exact Or.inr (degLex_trans h' hmM')
  · have hmne : m ≠ M := by
      intro h; subst h; exact hmM' hMM'
    refine ⟨m, by simp [omin, hmM'], Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hmne, hmin.1⟩),
      fun m' hm' => ?_⟩
    rcases Finset.mem_insert.mp hm' with h | h
    · subst h
      rcases degLex_trichotomous m m' with h'' | h'' | h''
      · exact absurd h'' hmM'
      · exact Or.inl h''.symm
      · exact Or.inr h''
    · exact hmin.2 m' (Finset.mem_of_mem_erase h)

theorem good_retire {x : Option (Monomial n)} {A : Finset (Monomial n)} {M : Monomial n}
    (hx : Good x A) (hM : M ∈ A) (hN : ∃ N ∈ A, degLex M N) : Good x (A.erase M) := by
  obtain ⟨N, hNA, hMN⟩ := hN
  obtain ⟨m, hm, hmin⟩ := hx.1 ⟨M, hM⟩
  subst hm
  have hNM : N ≠ M := by
    intro h; subst h; exact degLex_irrefl N hMN
  have hmne : m ≠ M := by
    intro h; subst h
    rcases hmin.2 N hNA with h' | h'
    · exact hNM h'
    · exact degLex_irrefl N (degLex_trans h' hMN)
  refine ⟨fun _ => ⟨m, rfl, Finset.mem_erase.mpr ⟨hmne, hmin.1⟩,
      fun m' hm' => hmin.2 m' (Finset.mem_of_mem_erase hm')⟩, fun h => ?_⟩
  exact absurd (Finset.mem_erase.mpr ⟨hNM, hNA⟩) (by rw [h]; exact Finset.notMem_empty N)

/-! ## I5 under each operation -/

theorem mint_I5 {st : SlotState n} (h : I5 st) {c : Fin n} (hc : st.active c = ∅)
    (M : Monomial n) : I5 (st.mint c M) := by
  intro x
  by_cases hx : x = c
  · subst hx; simp only [mint, ite_true]; exact good_singleton M
  · simp only [mint, hx, ite_false]; exact h x

theorem mintInto_I5 {st : SlotState n} (h : I5 st) (c : Fin n) (M : Monomial n) :
    I5 (st.mintInto c M) := by
  intro x
  by_cases hx : x = c
  · subst hx
    simp only [mintInto, ite_true]
    rw [Finset.insert_eq, Finset.union_comm]
    exact good_omin (h x) (good_singleton M)
  · simp only [mintInto, hx, ite_false]; exact h x

theorem merge_I5 {st : SlotState n} (h : I5 st) {c d : Fin n} (hcd : c ≠ d) :
    I5 (st.merge c d) := by
  intro x
  by_cases hxd : x = d
  · subst hxd; simp only [merge, ite_true]; exact good_omin (h c) (h x)
  · by_cases hxc : x = c
    · subst hxc; simp only [merge, hxd, ite_false, ite_true]; exact good_empty
    · simp only [merge, hxd, hxc, ite_false]; exact h x

theorem shrinkRefresh_I5 {st : SlotState n} (h : I5 st) {c : Fin n} {M M' : Monomial n}
    (hM : M ∈ st.active c) (hMM' : degLex M M') : I5 (st.shrinkRefresh c M M') := by
  intro x
  by_cases hx : x = c
  · subst hx; simp only [shrinkRefresh, ite_true]; exact good_shrink (h x) hM hMM'
  · simp only [shrinkRefresh, hx, ite_false]; exact h x

theorem retire_I5 {st : SlotState n} (h : I5 st) {c : Fin n} {M : Monomial n}
    (hM : M ∈ st.active c) (hN : ∃ N ∈ st.active c, degLex M N) : I5 (st.retire c M) := by
  intro x
  by_cases hx : x = c
  · subst hx; simp only [retire, ite_true]; exact good_retire (h x) hM hN
  · simp only [retire, hx, ite_false]; exact h x

theorem op_I5 {st st' : SlotState n} (h : I5 st) (hop : Op st st') : I5 st' := by
  cases hop with
  | mint hc => exact mint_I5 h hc _
  | mintInto => exact mintInto_I5 h _ _
  | merge hcd => exact merge_I5 h hcd
  | shrink hM hMM' => exact shrinkRefresh_I5 h hM hMM'
  | retire hM hN => exact retire_I5 h hM hN

/-- I5 is an invariant of every run of the fixed engine. -/
theorem reachable_I5 {st₀ st : SlotState n} (h₀ : I5 st₀) (hrun : OpsStar st₀ st) : I5 st := by
  induction hrun with
  | refl => exact h₀
  | tail _ hop ih => exact op_I5 ih hop

/-! ## The repro: without the refresh, one shrink breaks I5 -/

/-- Classes `p = 0 < q = 1 < a = 2 < b = 3`, `r = 4`; class `5` holds
`Add{a, b}` and `Add{p, q, r}` with slot `Add{a, b}`. -/
def reproBefore : SlotState 7 :=
  ⟨fun x => if x = 5 then {({2, 3} : Monomial 7), {0, 1, 4}} else ∅,
   fun x => if x = 5 then some ({2, 3} : Monomial 7) else none⟩

theorem repro_I5_before : I5 reproBefore := by
  intro x
  by_cases hx : x = 5
  · subst hx
    simp only [reproBefore, ite_true]
    refine ⟨fun _ => ⟨{2, 3}, rfl, Finset.mem_insert_self _ _, fun m' hm' => ?_⟩,
      fun h => absurd h (Finset.insert_ne_empty _ _)⟩
    rcases Finset.mem_insert.mp hm' with h | h
    · exact Or.inl h
    · rw [Finset.mem_singleton] at h
      subst h
      exact Or.inr (by decide)
  · simp only [reproBefore, hx, ite_false]; exact good_empty

/-- Merging `r` with the identity shrinks `Add{p, q, r}` to `Add{p, q}`,
which is `degLex`-below `Add{a, b}` (equal size, largest differing class
`b`). Without the refresh the slot still says `Add{a, b}`: I5 fails. -/
theorem shrinkNoRefresh_breaks_I5 :
    I5 reproBefore ∧ ¬ I5 (reproBefore.shrinkNoRefresh 5 {0, 1, 4} {0, 1}) := by
  refine ⟨repro_I5_before, fun h => ?_⟩
  have hgood := h 5
  simp only [shrinkNoRefresh, reproBefore, ite_true] at hgood
  obtain ⟨m, hm, hmin⟩ := hgood.1 ⟨{0, 1}, Finset.mem_insert_self _ _⟩
  have hm' : m = ({2, 3} : Monomial 7) := by
    injection hm with hm; exact hm.symm
  subst hm'
  rcases hmin.2 {0, 1} (Finset.mem_insert_self _ _) with h' | h'
  · exact absurd h' (by decide)
  · exact absurd h' (by decide)

/-- With the refresh, the same shrink keeps I5. -/
theorem shrinkRefresh_keeps_I5_repro :
    I5 (reproBefore.shrinkRefresh 5 {0, 1, 4} {0, 1}) :=
  shrinkRefresh_I5 repro_I5_before (by simp [reproBefore]) (by decide)

/-! ## Bridge to the completion state and the completeness theorem -/

/-- A completion state agrees with a slot state when active nodes of a class
are the slot state's active set of its representative, and the stored
right-hand side of a nonempty class is its slot. -/
def Agrees (st : State n) (ss : SlotState n) : Prop :=
  (∀ M c, (M, c) ∈ st.active → M ∈ ss.active (st.find c)) ∧
  (∀ c, (ss.active (st.find c)).Nonempty → ss.slot (st.find c) = some (st.rhs (st.find c)))

/-- Slot-level I5 gives the completion state's I5. -/
theorem state_I5_of_slot {st : State n} {ss : SlotState n} (h5 : I5 ss) (ha : Agrees st ss) :
    SemperProofs.CC.I5 st := by
  intro M c hM
  have hmem := ha.1 M c hM
  obtain ⟨m, hm, hmin⟩ := (h5 (st.find c)).1 ⟨M, hmem⟩
  rw [ha.2 c ⟨M, hmem⟩] at hm
  injection hm with hm
  subst hm
  rcases hmin.2 M hmem with h | h
  · exact Or.inl h.symm
  · exact Or.inr h

/-- The fix is sufficient: along any run of the fixed engine from a state
satisfying I5, a round that changes nothing is converged, and two
`=_E`-equal active nodes are in one class. The I5 hypothesis of
`roundFixed_converged` is discharged by `reachable_I5`; the other
hypotheses of `same_class` are kept explicit. -/
theorem fix_sufficient {L : Laws n} {S : Set (Monomial n × Monomial n)}
    {st : State n} {ss₀ ss : SlotState n}
    (h5₀ : I5 ss₀) (hrun : OpsStar ss₀ ss) (ha : Agrees st ss)
    (h0 : I0 st) (hcanon : ∀ c, L.clamp (st.rhs c) = st.rhs c) (hfix : RoundFixed L st)
    (hconf : Confluent (Rw L st.rules))
    (hnf : ∀ c P, ¬ Rw L st.rules (st.rhs (st.find c)) P)
    (hcc : ∀ P c d, (P, c) ∈ st.nodes → (P, d) ∈ st.nodes → st.find c = st.find d)
    (hjoin : ∀ M N, E L S M N → Joinable (Rw L st.rules) M N)
    {M N : Monomial n} {c d : Fin n} (hM : (M, c) ∈ st.active) (hN : (N, d) ∈ st.active)
    (hMN : E L S M N) : st.find c = st.find d :=
  same_class (roundFixed_converged (I0On_of_I0 h0) (state_I5_of_slot (reachable_I5 h5₀ hrun) ha) hcanon hfix)
    hconf h0 hnf hcc hjoin hM hN hMN

end SlotState

end SemperProofs.CC
