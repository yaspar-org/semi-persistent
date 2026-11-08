import SemperProofs.CC.Lemmas

/-!
# L16: round termination (`run_stabilizes'`)

Along any infinite run of inferences the node set and the partition are
eventually constant. The measure is the number of fresh classes plus the
number of representatives: a mint consumes one fresh class (the minted
class), a merge of two distinct classes removes one representative, and
no inference creates a fresh class or a representative. Every other
inference leaves nodes and partition unchanged.
-/

namespace SemperProofs.CC

open Relation

variable {n : ℕ}

/-- Fresh classes plus representatives. -/
noncomputable def measure (st : State n) : ℕ :=
  ({d | st.Fresh d} : Set (Fin n)).ncard + (Set.range st.find).ncard

theorem measure_congr {st st' : State n} (hn : st'.nodes = st.nodes)
    (hf : st'.find = st.find) : measure st' = measure st := by
  unfold measure
  have : {d | st'.Fresh d} = {d | st.Fresh d} := by
    ext d
    simp only [Set.mem_ofPred_eq, State.Fresh, hn, hf]
  rw [this, hf]

/-! ### Mint -/

theorem fresh_addNode_subset (st : State n) (N : Monomial n) (d : Fin n) :
    {d' | (st.addNode N d).Fresh d'} ⊆ {d' | st.Fresh d'} := by
  intro d' hd' M c hMc
  exact hd' M c (Set.mem_insert_of_mem _ hMc)

theorem not_fresh_addNode (st : State n) (N : Monomial n) (d : Fin n) :
    ¬ (st.addNode N d).Fresh d := by
  intro h
  exact h N d (Set.mem_insert _ _) rfl

theorem measure_addNode_lt (st : State n) {N : Monomial n} {d : Fin n}
    (hd : st.Fresh d) : measure (st.addNode N d) < measure st := by
  unfold measure
  have hss : {d' | (st.addNode N d).Fresh d'} ⊂ {d' | st.Fresh d'} :=
    (fresh_addNode_subset st N d).ssubset_of_not_subset
      fun h => not_fresh_addNode st N d (h hd)
  have h1 := Set.ncard_lt_ncard hss (Set.toFinite _)
  have h2 : Set.range (st.addNode N d).find = Set.range st.find := rfl
  rw [h2]
  omega

/-! ### Merge -/

theorem merge_find_apply (st : State n) (a b x : Fin n) :
    (st.merge a b).find x =
      if st.find x = st.find a then st.find b else st.find x := rfl

theorem merge_find_eq (st : State n) {a b : Fin n} (h : st.find a = st.find b) :
    (st.merge a b).find = st.find := by
  funext x
  rw [merge_find_apply]
  split_ifs with hx
  · rw [← h, hx]
  · rfl

theorem merge_find_congr (st : State n) (a b : Fin n) {x y : Fin n}
    (h : st.find x = st.find y) : (st.merge a b).find x = (st.merge a b).find y := by
  rw [merge_find_apply, merge_find_apply, h]

theorem fresh_merge_subset (st : State n) (a b : Fin n) :
    {d' | (st.merge a b).Fresh d'} ⊆ {d' | st.Fresh d'} := by
  intro d' hd' M c hMc heq
  exact hd' M c hMc (merge_find_congr st a b heq)

theorem range_merge_subset (st : State n) (a b : Fin n) :
    Set.range (st.merge a b).find ⊆ Set.range st.find := by
  rintro y ⟨x, rfl⟩
  rw [merge_find_apply]
  split_ifs
  · exact ⟨b, rfl⟩
  · exact ⟨x, rfl⟩

theorem find_notMem_range_merge (st : State n) {a b : Fin n}
    (h : st.find a ≠ st.find b) : st.find a ∉ Set.range (st.merge a b).find := by
  rintro ⟨x, hx⟩
  rw [merge_find_apply] at hx
  split_ifs at hx with hxa
  · exact h hx.symm
  · exact hxa hx

theorem measure_merge_lt (st : State n) {a b : Fin n} (h : st.find a ≠ st.find b) :
    measure (st.merge a b) < measure st := by
  unfold measure
  have h1 := Set.ncard_le_ncard (fresh_merge_subset st a b) (Set.toFinite _)
  have hss : Set.range (st.merge a b).find ⊂ Set.range st.find :=
    (range_merge_subset st a b).ssubset_of_not_subset
      fun hsub => find_notMem_range_merge st h (hsub ⟨a, rfl⟩)
  have h2 := Set.ncard_lt_ncard hss (Set.toFinite _)
  omega

theorem measure_merge (st : State n) (a b : Fin n) :
    ((st.merge a b).nodes = st.nodes ∧ (st.merge a b).find = st.find) ∨
      measure (st.merge a b) < measure st := by
  by_cases h : st.find a = st.find b
  · exact Or.inl ⟨rfl, merge_find_eq st h⟩
  · exact Or.inr (measure_merge_lt st h)

/-! ### One inference -/

/-- Every inference leaves nodes and partition unchanged or strictly
decreases the measure. -/
theorem Infer_measure {L : Laws n} {st st' : State n} (hinf : Infer L st st') :
    (st'.nodes = st.nodes ∧ st'.find = st.find) ∨ measure st' < measure st := by
  cases hinf with
  | mint _ _ hd => exact Or.inr (measure_addNode_lt st hd)
  | joinMerge _ _ _ => exact measure_merge st _ _
  | cancelMerge _ _ _ _ _ _ => exact measure_merge st _ _
  | retire _ => exact Or.inl ⟨rfl, rfl⟩
  | unretire _ _ => exact Or.inl ⟨rfl, rfl⟩
  | setRhs _ => exact Or.inl ⟨rfl, rfl⟩

theorem Infer_measure_le {L : Laws n} {st st' : State n} (hinf : Infer L st st') :
    measure st' ≤ measure st := by
  rcases Infer_measure hinf with ⟨hn, hf⟩ | hlt
  · exact (measure_congr hn hf).le
  · exact hlt.le

/-! ### The run -/

/-- L16 (sketch (d), last paragraph): along an infinite run the node set
and the partition are eventually constant. -/
theorem run_stabilizes' {L : Laws n} (run : ℕ → State n)
    (hrun : ∀ i, Infer L (run i) (run (i + 1))) :
    ∃ k, ∀ i, k ≤ i → (run i).nodes = (run k).nodes ∧ (run i).find = (run k).find := by
  classical
  have hmono : ∀ k i, k ≤ i → measure (run i) ≤ measure (run k) := by
    intro k i hki
    induction i, hki using Nat.le_induction with
    | base => exact le_rfl
    | succ i _ ih => exact (Infer_measure_le (hrun i)).trans ih
  have hex : ∃ v, ∃ k, measure (run k) = v := ⟨_, 0, rfl⟩
  obtain ⟨k, hk⟩ := Nat.find_spec hex
  have hmin : ∀ i, measure (run k) ≤ measure (run i) := by
    intro i
    rw [hk]
    exact Nat.find_min' hex ⟨i, rfl⟩
  refine ⟨k, fun i hki => ?_⟩
  induction i, hki using Nat.le_induction with
  | base => exact ⟨rfl, rfl⟩
  | succ i hki ih =>
    rcases Infer_measure (hrun i) with ⟨hn, hf⟩ | hlt
    · exact ⟨hn.trans ih.1, hf.trans ih.2⟩
    · exact absurd (lt_of_lt_of_le hlt (hmono k i hki)) (not_lt.2 (hmin (i + 1)))

end SemperProofs.CC
