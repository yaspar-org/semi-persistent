import SemperProofs.EMatch.Engine.Plan

/-!
# Runtime scheduling (spec-scheduler §4)

`runND` is the nondeterministic interpreter of the adaptive scheduler: at
each decision point it runs the eager fixpoint (lowest-index eager atom
first, as `lower_eager` does), then lets a choice function pick any
remaining scanning atom, lowers it under the current bound set, and
continues on every emitted binding with its own masks. The choice function
sees the current binding and the candidate set (the engine's `choose_atom`
reads bucket lengths through the current environment).

`runND_matches`: whatever the choice function, the emitted set is exactly
`Matches`; `runND_indep`: hence independent of the choice function, and
equal to the set every `PlanOK` plan emits (`plan_matches`).
-/

namespace Semper.EMatch

/-- Boolean form of `eagerFree`. -/
def QAtom.eagerFreeB : QAtom → Finset Var → Bool
  | .scan _, _ => false
  | .eq x y, B => decide (x ∈ B) || decide (y ∈ B)

theorem eagerFreeB_iff (q : QAtom) (B : Finset Var) : q.eagerFreeB B = true ↔ q.eagerFree B := by
  cases q <;> simp [QAtom.eagerFreeB, QAtom.eagerFree]

def QAtom.isScan : QAtom → Bool
  | .scan _ => true
  | .eq _ _ => false

/-- The lowest-index unused eager atom accepted under `B` (`lower_eager`'s
index sweep). -/
def eagerCandidate (atoms : List QAtom) (used : Finset Nat) (B : Finset Var) : Option Nat :=
  (List.range atoms.length).find? (fun i =>
    decide (i ∉ used) && (match atoms[i]? with | some q => q.eagerFreeB B | none => false))

/-- The unused scanning atoms. -/
def unusedScan (atoms : List QAtom) (used : Finset Nat) : Finset Nat :=
  (Finset.range atoms.length).filter (fun i => i ∉ used ∧ atoms[i]?.map QAtom.isScan = some true)

theorem eagerCandidate_some {atoms : List QAtom} {used : Finset Nat} {B : Finset Var} {i : Nat}
    (h : eagerCandidate atoms used B = some i) :
    ∃ q, atoms[i]? = some q ∧ i ∉ used ∧ q.eagerFree B := by
  unfold eagerCandidate at h
  have hp := List.find?_some h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
  obtain ⟨hu, hq⟩ := hp
  cases hi : atoms[i]? with
  | none => rw [hi] at hq; simp at hq
  | some q => rw [hi] at hq; exact ⟨q, rfl, hu, (eagerFreeB_iff q B).1 hq⟩

theorem eagerCandidate_none {atoms : List QAtom} {used : Finset Nat} {B : Finset Var}
    (h : eagerCandidate atoms used B = none) :
    ∀ (i : Nat) (q : QAtom), atoms[i]? = some q → i ∉ used → ¬ q.eagerFree B := by
  intro i q hq hu hf
  unfold eagerCandidate at h
  rw [List.find?_eq_none] at h
  have hi : i < atoms.length := (List.getElem?_eq_some_iff.1 hq).1
  have := h i (List.mem_range.2 hi)
  simp only [Bool.and_eq_true, decide_eq_true_eq, not_and] at this
  rw [hq] at this
  exact (this hu) ((eagerFreeB_iff q B).2 hf)

theorem mem_unusedScan {atoms : List QAtom} {used : Finset Nat} {i : Nat} :
    i ∈ unusedScan atoms used ↔ i ∉ used ∧ ∃ a, atoms[i]? = some (.scan a) := by
  unfold unusedScan
  rw [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hi, hu, hs⟩
    refine ⟨hu, ?_⟩
    cases hq : atoms[i]? with
    | none => rw [hq] at hs; simp at hs
    | some q =>
        rw [hq] at hs
        cases q with
        | scan a => exact ⟨a, rfl⟩
        | eq x y => simp [QAtom.isScan] at hs
  · rintro ⟨hu, a, ha⟩
    exact ⟨(List.getElem?_eq_some_iff.1 ha).1, hu, by simp [ha, QAtom.isScan]⟩

/-- Spec §4, `runND`. `fuel` bounds the number of decisions; `atoms.length`
suffices from the initial state. -/
def runND (G : Graph) (atoms : List QAtom) (choose : Binding → Finset Nat → Nat) :
    Nat → Finset Nat → Finset Var → Binding → List Binding
  | 0, _, _, σ => [σ]
  | fuel + 1, used, B, σ =>
      match eagerCandidate atoms used B with
      | some i =>
          match atoms[i]? with
          | some q => (run G (q.eagerLower B) σ).flatMap (runND G atoms choose fuel (insert i used) (B ∪ q.binds))
          | none => []
      | none =>
          if hS : (unusedScan atoms used).Nonempty then
            let i := if choose σ (unusedScan atoms used) ∈ unusedScan atoms used
              then choose σ (unusedScan atoms used) else (unusedScan atoms used).min' hS
            match atoms[i]? with
            | some (.scan a) =>
                (run G (lower a B) σ).flatMap (runND G atoms choose fuel (insert i used) (B ∪ a.binds))
            | _ => []
          else [σ]

/-- The unused valid indices. -/
def unusedCount (atoms : List QAtom) (used : Finset Nat) : Nat :=
  ((Finset.range atoms.length).filter (· ∉ used)).card

theorem unusedCount_insert {atoms : List QAtom} {used : Finset Nat} {i : Nat}
    (hi : i < atoms.length) (hu : i ∉ used) :
    unusedCount atoms (insert i used) + 1 = unusedCount atoms used := by
  unfold unusedCount
  have : (Finset.range atoms.length).filter (· ∉ insert i used) =
      ((Finset.range atoms.length).filter (· ∉ used)).erase i := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert, not_or, Finset.mem_erase]
    tauto
  rw [this, Finset.card_erase_of_mem (by simp [hi, hu])]
  have : 0 < ((Finset.range atoms.length).filter (· ∉ used)).card :=
    Finset.card_pos.2 ⟨i, by simp [hi, hu]⟩
  omega

theorem unusedCount_zero {atoms : List QAtom} {used : Finset Nat} (h : unusedCount atoms used = 0) :
    ∀ (i : Nat) (q : QAtom), atoms[i]? = some q → i ∈ used := by
  intro i q hq
  by_contra hu
  have hi : i < atoms.length := (List.getElem?_eq_some_iff.1 hq).1
  have : i ∈ (Finset.range atoms.length).filter (· ∉ used) := by simp [hi, hu]
  unfold unusedCount at h
  rw [Finset.card_eq_zero] at h
  rw [h] at this
  simp at this

theorem runND_run {G : Graph} {sig : Sym → Kind} {atoms : List QAtom} {pre : Finset Var}
    (choose : Binding → Finset Nat → Nat) (hwf : AtomsWF G sig atoms) :
    ∀ (fuel : Nat) (used : Finset Nat) (B : Finset Var) (σ : Binding),
    Inv G (fun _ => false) atoms (fun _ => .full) pre used B σ → unusedCount atoms used ≤ fuel →
    ∀ σ', σ' ∈ runND G atoms choose fuel used B σ ↔
      RunSpec G (fun _ => false) atoms (fun _ => .full) used B σ σ' := by
  intro fuel
  induction fuel with
  | zero =>
      intro used B σ hinv hfuel σ'
      have hall := unusedCount_zero (Nat.le_zero.1 hfuel)
      simp only [runND, List.mem_singleton]
      exact runSpec_done hwf hinv (fun i a ha => hall i _ ha) (fun i q hq hu => absurd (hall i q hq) hu)
  | succ fuel ih =>
      intro used B σ hinv hfuel σ'
      simp only [runND]
      cases hc : eagerCandidate atoms used B with
      | some i =>
          obtain ⟨q, hq, hu, hf⟩ := eagerCandidate_some hc
          simp only [hq]
          have hi : i < atoms.length := (List.getElem?_eq_some_iff.1 hq).1
          have hfuel' : unusedCount atoms (insert i used) ≤ fuel := by
            have := unusedCount_insert hi hu; omega
          exact step_eager_iff hwf hinv hq hu hf _ (fun σ₁ hinv₁ => ih _ _ σ₁ hinv₁ hfuel') σ'
      | none =>
          have hnone := eagerCandidate_none hc
          simp only
          split
          · rename_i hS
            set i := (if choose σ (unusedScan atoms used) ∈ unusedScan atoms used
              then choose σ (unusedScan atoms used) else (unusedScan atoms used).min' hS) with hi_def
            have hiS : i ∈ unusedScan atoms used := by
              rw [hi_def]; split
              · assumption
              · exact Finset.min'_mem _ _
            obtain ⟨hu, a, ha⟩ := mem_unusedScan.1 hiS
            simp only [ha]
            have hi : i < atoms.length := (List.getElem?_eq_some_iff.1 ha).1
            have hfuel' : unusedCount atoms (insert i used) ≤ fuel := by
              have := unusedCount_insert hi hu; omega
            refine step_pick_iff hwf hinv ha hu _ ?_ _ (fun σ₁ hinv₁ => ih _ _ σ₁ hinv₁ hfuel') σ'
            intro σ₁
            constructor
            · intro h₁
              obtain ⟨hn, hrf⟩ := hinv.pick_conditions hwf ha hu
              have hs := lower_sound hwf.keys hwf.conf (hwf.wk a (mem_of_getElem? ha)) hinv.clsDom hn hrf h₁
              obtain ⟨id, -, hid, -⟩ := hs.sat
              exact ⟨h₁, id, hid, rfl⟩
            · exact And.left
          · rename_i hS
            simp only [List.mem_singleton]
            have hall : ∀ (i : Nat) (a : RAtom), atoms[i]? = some (.scan a) → i ∈ used := by
              intro i a ha
              by_contra hu
              exact hS ⟨i, mem_unusedScan.2 ⟨hu, a, ha⟩⟩
            exact runSpec_done hwf hinv hall hnone

/-- Spec §4, `runND_matches`: for every choice function, the runtime
scheduler emits exactly `Matches`. -/
theorem runND_matches {G : Graph} {sig : Sym → Kind} {atoms : List QAtom}
    (choose : Binding → Finset Nat → Nat) (hwf : AtomsWF G sig atoms) :
    ∀ σ', σ' ∈ runND G atoms choose atoms.length ∅ ∅ Binding.empty ↔ Matches G atoms σ' := by
  intro σ'
  rw [runND_run choose hwf atoms.length ∅ ∅ Binding.empty (Inv.empty G _ atoms _)
    (by unfold unusedCount; simp), runSpec_empty_iff]
  constructor
  · exact And.left
  · intro hm; exact ⟨hm, modeOk_full _ _ _ hm⟩

/-- Spec §4, `runND_indep`: the emitted set does not depend on the choice
function. -/
theorem runND_indep {G : Graph} {sig : Sym → Kind} {atoms : List QAtom}
    (choose₁ choose₂ : Binding → Finset Nat → Nat) (hwf : AtomsWF G sig atoms) :
    ∀ σ', σ' ∈ runND G atoms choose₁ atoms.length ∅ ∅ Binding.empty ↔
      σ' ∈ runND G atoms choose₂ atoms.length ∅ ∅ Binding.empty := by
  intro σ'
  rw [runND_matches choose₁ hwf, runND_matches choose₂ hwf]

/-- The runtime scheduler and every static plan emit the same set. -/
theorem runND_eq_plan {G : Graph} {sig : Sym → Kind} {atoms : List QAtom} {plan : Plan}
    (choose : Binding → Finset Nat → Nat) (hwf : AtomsWF G sig atoms) (h : PlanOK atoms plan) :
    ∀ σ', σ' ∈ runND G atoms choose atoms.length ∅ ∅ Binding.empty ↔ σ' ∈ run G plan Binding.empty := by
  intro σ'
  rw [runND_matches choose hwf, plan_matches hwf h]

end Semper.EMatch
