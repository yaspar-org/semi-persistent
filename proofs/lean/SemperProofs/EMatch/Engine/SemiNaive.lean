import SemperProofs.EMatch.Engine.Plan

/-!
# Semi-naive variants (spec-scheduler §6)

Variant `k` of a plan runs the join of atom `k` on the delta index, the
joins of atoms `j < k` on the full index minus the delta, and the joins of
atoms `j > k` on the full index; every other step is mode-blind. With
`isNew` the membership predicate of the delta (the touched ids of the
round), `variant_partition` says variant `k` emits a binding iff the naive
run emits it, the node of atom `k` is new, and the nodes of the join atoms
before `k` are old. Hence the variants are pairwise disjoint and their
union is the set of naive matches with at least one new join-atom node.
-/

namespace Semper.EMatch

/-- The mode assignment of variant `k` (`I:956-963`), by atom index. -/
def variantMode (k : Nat) : Nat → IndexMode :=
  fun j => if j = k then .delta else if j < k then .fullMinusDelta else .full

/-- The run of variant `k` of an annotated plan. -/
def runVariant (G : Graph) (isNew : NodeId → Bool) (k : Nat) (ap : APlan) : List Binding :=
  runA G isNew (variantMode k) ap Binding.empty

/-- The naive run of the same plan. -/
def runNaive (G : Graph) (ap : APlan) : List Binding := run G (ap.map (·.2)) Binding.empty

/-- For a match, the mode condition of variant `k` says the node of atom
`k` is new and the nodes of the scanning atoms before `k` are old. -/
theorem modeOk_variant_iff {G : Graph} {isNew : NodeId → Bool} {atoms : List QAtom} {σ' : Binding}
    {k : Nat} {ak : RAtom} (hk : atoms[k]? = some (.scan ak)) (hm : Matches G atoms σ') :
    ModeOk isNew atoms (variantMode k) σ' ↔
      (∃ id, σ'.node ak.node = some id ∧ isNew id = true) ∧
        ∀ (j : Nat) (a : RAtom), j < k → atoms[j]? = some (.scan a) →
          ∃ id, σ'.node a.node = some id ∧ isNew id = false := by
  constructor
  · intro hmode
    refine ⟨?_, ?_⟩
    · obtain ⟨id, hid, hok⟩ := hmode k ak hk
      exact ⟨id, hid, by simpa [variantMode, modeOk] using hok⟩
    · intro j a hj ha
      obtain ⟨id, hid, hok⟩ := hmode j a ha
      refine ⟨id, hid, ?_⟩
      have hne : j ≠ k := by omega
      simpa [variantMode, hne, hj, modeOk] using hok
  · rintro ⟨⟨id, hid, hnew⟩, hold⟩
    intro j a ha
    by_cases hjk : j = k
    · subst hjk
      rw [hk] at ha
      cases Option.some.inj ha
      exact ⟨id, hid, by simp [variantMode, modeOk, hnew]⟩
    · by_cases hlt : j < k
      · obtain ⟨id', hid', hold'⟩ := hold j a hlt ha
        exact ⟨id', hid', by simp [variantMode, hjk, hlt, modeOk, hold']⟩
      · obtain ⟨id', hid'⟩ := (hm.node a.node).2 ⟨a, mem_of_getElem? ha, rfl⟩
        exact ⟨id', hid', by simp [variantMode, hjk, hlt, modeOk]⟩

/-- A match with a new scanning node satisfies the mode condition of the
variant of its least new scanning atom. -/
theorem matches_cover_new {G : Graph} {isNew : NodeId → Bool} {atoms : List QAtom} {σ' : Binding}
    (hm : Matches G atoms σ')
    (hex : ∃ (j : Nat) (a : RAtom), atoms[j]? = some (.scan a) ∧
      ∃ id, σ'.node a.node = some id ∧ isNew id = true) :
    ∃ (k : Nat) (ak : RAtom), atoms[k]? = some (.scan ak) ∧ ModeOk isNew atoms (variantMode k) σ' := by
  classical
  let P : Nat → Prop := fun j => ∃ a, atoms[j]? = some (.scan a) ∧ ∃ id, σ'.node a.node = some id ∧ isNew id = true
  have hP : ∃ j, P j := by obtain ⟨j, a, ha, hid⟩ := hex; exact ⟨j, a, ha, hid⟩
  let k := Nat.find hP
  obtain ⟨ak, hk, hnew⟩ : P k := Nat.find_spec hP
  refine ⟨k, ak, hk, (modeOk_variant_iff hk hm).2 ⟨hnew, ?_⟩⟩
  intro j a hj ha
  obtain ⟨id, hid⟩ := (hm.node a.node).2 ⟨a, mem_of_getElem? ha, rfl⟩
  refine ⟨id, hid, ?_⟩
  by_contra hnew'
  have : P j := ⟨a, ha, id, hid, by simpa using hnew'⟩
  exact Nat.find_min hP hj this

/-- Spec §6, `variant_partition`. -/
theorem variant_partition {G : Graph} {sig : Sym → Kind} {isNew : NodeId → Bool} {atoms : List QAtom}
    {ap : APlan} (hwf : AtomsWF G sig atoms) (h : SchedA atoms ∅ ∅ ap) {k : Nat} {ak : RAtom}
    (hk : atoms[k]? = some (.scan ak)) :
    ∀ σ', σ' ∈ runVariant G isNew k ap ↔
      σ' ∈ runNaive G ap ∧ (∃ id, σ'.node ak.node = some id ∧ isNew id = true) ∧
        ∀ (j : Nat) (a : RAtom), j < k → atoms[j]? = some (.scan a) →
          ∃ id, σ'.node a.node = some id ∧ isNew id = false := by
  intro σ'
  unfold runVariant runNaive
  rw [schedA_matches hwf h, ← runA_full G isNew, schedA_matches hwf h]
  constructor
  · rintro ⟨hm, hmode⟩
    exact ⟨⟨hm, modeOk_full _ _ _ hm⟩, (modeOk_variant_iff hk hm).1 hmode⟩
  · rintro ⟨⟨hm, -⟩, hv⟩
    exact ⟨hm, (modeOk_variant_iff hk hm).2 hv⟩

/-- The variants are pairwise disjoint. -/
theorem variants_disjoint {G : Graph} {sig : Sym → Kind} {isNew : NodeId → Bool} {atoms : List QAtom}
    {ap : APlan} (hwf : AtomsWF G sig atoms) (h : SchedA atoms ∅ ∅ ap) {k k' : Nat} {ak ak' : RAtom}
    (hk : atoms[k]? = some (.scan ak)) (hk' : atoms[k']? = some (.scan ak')) (hne : k ≠ k') :
    ∀ σ', ¬ (σ' ∈ runVariant G isNew k ap ∧ σ' ∈ runVariant G isNew k' ap) := by
  intro σ' ⟨h₁, h₂⟩
  rw [variant_partition hwf h hk] at h₁
  rw [variant_partition hwf h hk'] at h₂
  obtain ⟨-, ⟨id, hid, hnew⟩, hold⟩ := h₁
  obtain ⟨-, ⟨id', hid', hnew'⟩, hold'⟩ := h₂
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · obtain ⟨id'', hid'', hold''⟩ := hold' k ak hlt hk
    rw [hid] at hid''
    cases hid''
    rw [hnew] at hold''
    cases hold''
  · obtain ⟨id'', hid'', hold''⟩ := hold k' ak' hlt hk'
    rw [hid'] at hid''
    cases hid''
    rw [hnew'] at hold''
    cases hold''

/-- The union of the variants is the set of naive matches with at least one
new join-atom node (spec §6, `variants_cover_new`). -/
theorem variants_cover_new {G : Graph} {sig : Sym → Kind} {isNew : NodeId → Bool} {atoms : List QAtom}
    {ap : APlan} (hwf : AtomsWF G sig atoms) (h : SchedA atoms ∅ ∅ ap) :
    ∀ σ', (∃ (k : Nat) (ak : RAtom), atoms[k]? = some (.scan ak) ∧ σ' ∈ runVariant G isNew k ap) ↔
      σ' ∈ runNaive G ap ∧ ∃ (j : Nat) (a : RAtom), atoms[j]? = some (.scan a) ∧
        ∃ id, σ'.node a.node = some id ∧ isNew id = true := by
  intro σ'
  constructor
  · rintro ⟨k, ak, hk, hv⟩
    rw [variant_partition hwf h hk] at hv
    exact ⟨hv.1, k, ak, hk, hv.2.1⟩
  · rintro ⟨hn, hex⟩
    have hm : Matches G atoms σ' := by
      unfold runNaive at hn
      rw [← runA_full G isNew, schedA_matches hwf h] at hn
      exact hn.1
    obtain ⟨k, ak, hk, hmode⟩ := matches_cover_new hm hex
    refine ⟨k, ak, hk, ?_⟩
    unfold runVariant
    exact (schedA_matches hwf h σ').2 ⟨hm, hmode⟩

end Semper.EMatch
