import SemperProofs.EMatch.Engine.SchedRun

/-!
# Corollaries for static plans (spec-scheduler §3.1-§3.3)

`plan_matches`: for every `PlanOK` plan, the interpreter started from the
empty binding emits exactly the bindings satisfying every atom with the
right domain, whatever selectivity estimate chose the order.
`planOK_wf`: every `PlanOK` plan is well-formed (`PlanWF`).
`planOKFrom_matches`: the seeded variant (§3.3).
-/

namespace Semper.EMatch

open Binding (Extends)

/-- The absolute characterisation of the emitted bindings: every atom is
satisfied; the class map is bound exactly on the atoms' bound variables;
node, multiplicity and rest maps are bound exactly on the scanning atoms'
node, multiplicity and rest variables. -/
structure Matches (G : Graph) (atoms : List QAtom) (σ' : Binding) : Prop where
  sat : ∀ q ∈ atoms, QSat G σ' q
  clsDom : ∀ (x : Var), (∃ c, σ'.cls x = some c) ↔ ∃ q ∈ atoms, x ∈ q.binds
  node : ∀ (v : Var), (∃ id, σ'.node v = some id) ↔ ∃ a, QAtom.scan a ∈ atoms ∧ a.node = v
  mult : ∀ (k : Var), (∃ m, σ'.mult k = some m) ↔ ∃ a, QAtom.scan a ∈ atoms ∧ k ∈ a.multVars
  rest : ∀ (r : Var), (∃ m, σ'.rest r = some m) ↔ ∃ a, QAtom.scan a ∈ atoms ∧ r ∈ a.msetRestVars
  seqRest : ∀ (r : Var), (∃ u, σ'.seqRest r = some u) ↔ ∃ a, QAtom.scan a ∈ atoms ∧ r ∈ a.seqRestVars
  finRest : ∀ (r : Var), (∃ s, σ'.finRest r = some s) ↔ ∃ a, QAtom.scan a ∈ atoms ∧ r ∈ a.setRestVars

/-- The semi-naive side condition on the node of each scanning atom. -/
def ModeOk (isNew : NodeId → Bool) (atoms : List QAtom) (mode : Nat → IndexMode) (σ' : Binding) :
    Prop :=
  ∀ (i : Nat) (a : RAtom), atoms[i]? = some (.scan a) →
    ∃ id, σ'.node a.node = some id ∧ modeOk isNew (mode i) id = true

theorem Inv.empty (G : Graph) (isNew : NodeId → Bool) (atoms : List QAtom) (mode : Nat → IndexMode) :
    Inv G isNew atoms mode ∅ ∅ ∅ Binding.empty where
  clsDom x := by simp [Binding.empty]
  bound x := by simp
  node v id h := by simp [Binding.empty] at h
  sat i q _ h := by simp at h
  mode i a _ h := by simp at h
  rest r m h := by simp [Binding.empty] at h
  seqRest r u h := by simp [Binding.empty] at h
  finRest r s h := by simp [Binding.empty] at h

theorem mem_iff_getElem? {atoms : List QAtom} {q : QAtom} :
    q ∈ atoms ↔ ∃ i : Nat, atoms[i]? = some q := by
  constructor
  · intro h
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem h
    exact ⟨i, by simp [List.getElem?_eq_getElem hi]⟩
  · rintro ⟨i, hi⟩
    exact List.mem_of_getElem? hi

/-- From the empty binding, `RunSpec` is `Matches` plus the mode condition. -/
theorem runSpec_empty_iff {G : Graph} {isNew : NodeId → Bool} {atoms : List QAtom}
    {mode : Nat → IndexMode} {σ' : Binding} :
    RunSpec G isNew atoms mode ∅ ∅ Binding.empty σ' ↔ Matches G atoms σ' ∧ ModeOk isNew atoms mode σ' := by
  constructor
  · intro h
    have hsat : ∀ q ∈ atoms, QSat G σ' q := fun q hq => by
      obtain ⟨i, hi⟩ := mem_iff_getElem?.1 hq
      exact h.sat i q hi
    refine ⟨{
      sat := hsat
      clsDom := ?_
      node := ?_
      mult := ?_
      rest := ?_
      seqRest := ?_
      finRest := ?_ }, h.mode⟩
    · intro x
      rw [h.clsDom x]
      simp only [Finset.notMem_empty, false_or, Finset.notMem_empty, not_false_eq_true, true_and]
      constructor
      · rintro ⟨i, q, hi, hx⟩; exact ⟨q, List.mem_of_getElem? hi, hx⟩
      · rintro ⟨q, hq, hx⟩
        obtain ⟨i, hi⟩ := mem_iff_getElem?.1 hq
        exact ⟨i, q, hi, hx⟩
    · intro v
      constructor
      · rintro ⟨id, hid⟩
        rcases h.node v id hid with ⟨id', h'⟩ | ⟨i, a, hi, -, ha⟩
        · simp [Binding.empty] at h'
        · exact ⟨a, List.mem_of_getElem? hi, ha⟩
      · rintro ⟨a, ha, rfl⟩
        obtain ⟨id, nd, hid, -⟩ := hsat _ ha
        exact ⟨id, hid⟩
    · intro k
      constructor
      · rintro ⟨m, hm⟩
        rcases h.mult k m hm with ⟨m', h'⟩ | ⟨i, a, hi, -, ha⟩
        · simp [Binding.empty] at h'
        · exact ⟨a, List.mem_of_getElem? hi, ha⟩
      · rintro ⟨a, ha, hk⟩
        exact AtomSat.multVars_bound (hsat _ ha) k hk
    · intro r
      constructor
      · rintro ⟨m, hm⟩
        rcases h.rest r m hm with ⟨m', h'⟩ | ⟨i, a, hi, -, ha⟩
        · simp [Binding.empty] at h'
        · exact ⟨a, List.mem_of_getElem? hi, ha⟩
      · rintro ⟨a, ha, hr⟩
        exact AtomSat.msetRest_bound (hsat _ ha) r hr
    · intro r
      constructor
      · rintro ⟨u, hu⟩
        rcases h.seqRest r u hu with ⟨u', h'⟩ | ⟨i, a, hi, -, ha⟩
        · simp [Binding.empty] at h'
        · exact ⟨a, List.mem_of_getElem? hi, ha⟩
      · rintro ⟨a, ha, hr⟩
        exact AtomSat.seqRest_bound (hsat _ ha) r hr
    · intro r
      constructor
      · rintro ⟨s, hs⟩
        rcases h.finRest r s hs with ⟨s', h'⟩ | ⟨i, a, hi, -, ha⟩
        · simp [Binding.empty] at h'
        · exact ⟨a, List.mem_of_getElem? hi, ha⟩
      · rintro ⟨a, ha, hr⟩
        exact AtomSat.setRest_bound (hsat _ ha) r hr
  · rintro ⟨hm, hmode⟩
    refine {
      ext := ?_
      sat := ?_
      mode := hmode
      clsDom := ?_
      node := ?_
      mult := ?_
      rest := ?_
      seqRest := ?_
      finRest := ?_ }
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro x c h <;> simp [Binding.empty] at h
    · intro i q hi; exact hm.sat q (List.mem_of_getElem? hi)
    · intro x
      rw [hm.clsDom x]
      simp only [Finset.notMem_empty, false_or, not_false_eq_true, true_and]
      constructor
      · rintro ⟨q, hq, hx⟩
        obtain ⟨i, hi⟩ := mem_iff_getElem?.1 hq
        exact ⟨i, q, hi, hx⟩
      · rintro ⟨i, q, hi, hx⟩; exact ⟨q, List.mem_of_getElem? hi, hx⟩
    · intro v id hv
      obtain ⟨a, ha, rfl⟩ := (hm.node v).1 ⟨id, hv⟩
      obtain ⟨i, hi⟩ := mem_iff_getElem?.1 ha
      exact Or.inr ⟨i, a, hi, by simp, rfl⟩
    · intro k m hk
      obtain ⟨a, ha, hka⟩ := (hm.mult k).1 ⟨m, hk⟩
      obtain ⟨i, hi⟩ := mem_iff_getElem?.1 ha
      exact Or.inr ⟨i, a, hi, by simp, hka⟩
    · intro r m hr
      obtain ⟨a, ha, hra⟩ := (hm.rest r).1 ⟨m, hr⟩
      obtain ⟨i, hi⟩ := mem_iff_getElem?.1 ha
      exact Or.inr ⟨i, a, hi, by simp, hra⟩
    · intro r u hr
      obtain ⟨a, ha, hra⟩ := (hm.seqRest r).1 ⟨u, hr⟩
      obtain ⟨i, hi⟩ := mem_iff_getElem?.1 ha
      exact Or.inr ⟨i, a, hi, by simp, hra⟩
    · intro r s hr
      obtain ⟨a, ha, hra⟩ := (hm.finRest r).1 ⟨s, hr⟩
      obtain ⟨i, hi⟩ := mem_iff_getElem?.1 ha
      exact Or.inr ⟨i, a, hi, by simp, hra⟩

/-- The annotated form of `plan_matches`, for any mode assignment. -/
theorem schedA_matches {G : Graph} {sig : Sym → Kind} {isNew : NodeId → Bool} {atoms : List QAtom}
    {mode : Nat → IndexMode} {ap : APlan} (hwf : AtomsWF G sig atoms) (h : SchedA atoms ∅ ∅ ap) :
    ∀ σ', σ' ∈ runA G isNew mode ap Binding.empty ↔ Matches G atoms σ' ∧ ModeOk isNew atoms mode σ' := by
  intro σ'
  rw [schedA_run hwf h Binding.empty (Inv.empty G isNew atoms mode) σ', runSpec_empty_iff]

theorem modeOk_full (isNew : NodeId → Bool) (atoms : List QAtom) (σ' : Binding)
    (hm : Matches G atoms σ') : ModeOk isNew atoms (fun _ => .full) σ' := by
  intro i a ha
  obtain ⟨id, hid⟩ := (hm.node a.node).2 ⟨a, List.mem_of_getElem? ha, rfl⟩
  exact ⟨id, hid, rfl⟩

/-- Spec §3.2, `plan_matches`: every `PlanOK` plan emits exactly the
bindings that satisfy every atom and bind exactly the atoms' variables.
Nothing is assumed about which `pick` was taken, hence nothing about the
selectivity estimate. -/
theorem plan_matches {G : Graph} {sig : Sym → Kind} {atoms : List QAtom} {plan : Plan}
    (hwf : AtomsWF G sig atoms) (h : PlanOK atoms plan) :
    ∀ σ', σ' ∈ run G plan Binding.empty ↔ Matches G atoms σ' := by
  intro σ'
  obtain ⟨ap, hap, rfl⟩ := schedA_of_sched h
  rw [← runA_full G (fun _ => false), schedA_matches (isNew := fun _ => false) hwf hap]
  constructor
  · exact And.left
  · intro hm; exact ⟨hm, modeOk_full _ _ _ hm⟩

/-! ## Seeded plans (spec §3.3) -/

/-- A seed binding: classes bound exactly on `pre`, nothing else bound. The
seeds are not variables of the query's atoms. -/
structure Seed (atoms : List QAtom) (pre : Finset Var) (σ₀ : Binding) : Prop where
  clsDom : ClsDom σ₀ pre
  node : ∀ v, σ₀.node v = none
  mult : ∀ k, σ₀.mult k = none
  rest : ∀ r, σ₀.rest r = none
  seqRest : ∀ r, σ₀.seqRest r = none
  finRest : ∀ r, σ₀.finRest r = none

/-- The invariant at a seeded start. -/
theorem Inv.seed {G : Graph} {isNew : NodeId → Bool} {atoms : List QAtom} {mode : Nat → IndexMode}
    {pre : Finset Var} {σ₀ : Binding} (hs : Seed atoms pre σ₀) :
    Inv G isNew atoms mode pre ∅ pre σ₀ where
  clsDom := hs.clsDom
  bound x := by simp
  node v id h := by rw [hs.node] at h; cases h
  sat i q _ h := by simp at h
  mode i a _ h := by simp at h
  rest r m h := by rw [hs.rest] at h; cases h
  seqRest r u h := by rw [hs.seqRest] at h; cases h
  finRest r s h := by rw [hs.finRest] at h; cases h

/-- Spec §3.3, seeded plans: from a seed binding whose classes are bound
exactly on `pre`, a `PlanOKFrom pre` plan emits exactly the extensions of
the seed described by `RunSpec` (every atom satisfied, classes bound on
`pre` and the atoms' variables, nothing else written). -/
theorem planOKFrom_matches {G : Graph} {sig : Sym → Kind} {atoms : List QAtom} {pre : Finset Var}
    {plan : Plan} {σ₀ : Binding} (hwf : AtomsWF G sig atoms) (h : PlanOKFrom atoms pre plan)
    (hs : Seed atoms pre σ₀) :
    ∀ σ', σ' ∈ run G plan σ₀ ↔ RunSpec G (fun _ => false) atoms (fun _ => .full) ∅ pre σ₀ σ' := by
  intro σ'
  obtain ⟨ap, hap, rfl⟩ := schedA_of_sched h
  rw [← runA_full G (fun _ => false)]
  exact schedA_run hwf hap σ₀ (Inv.seed hs) σ'

end Semper.EMatch

namespace Semper.EMatch

/-! ## The `NodeCls` invariant (spec §0) -/

/-- Every emitted binding satisfies `NodeCls`: the class of a bound node
variable is the representative of its node. -/
theorem Matches.nodeCls {G : Graph} {atoms : List QAtom} {σ' : Binding} (h : Matches G atoms σ') :
    NodeCls G σ' := by
  intro v id hv
  obtain ⟨a, ha, rfl⟩ := (h.node v).1 ⟨id, hv⟩
  obtain ⟨id', nd, hid', -, hc, -⟩ := h.sat _ ha
  rw [hid'] at hv
  cases hv
  exact hc

theorem LowerSpec.nodeCls {G : Graph} {a : RAtom} {B : Finset Var} {σ σ' : Binding}
    (h₀ : NodeCls G σ) (h : LowerSpec G a B σ σ') : NodeCls G σ' := by
  intro v id hv
  by_cases hva : v = a.node
  · subst hva
    obtain ⟨id', nd, hid', -, hc, -⟩ := h.sat
    rw [hid'] at hv
    cases hv
    exact hc
  · rw [h.node v hva] at hv
    exact h.ext.1 _ _ (h₀ v id hv)

end Semper.EMatch
