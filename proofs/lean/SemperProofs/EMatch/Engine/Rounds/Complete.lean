import SemperProofs.EMatch.Engine.Rounds.Delta

/-!
# Cross-round completeness of the semi-naive loop (spec-semi-naive-rounds §D)

`semi_naive_round_complete` composes `delta_complete` with the within-round
theorem `variants_cover_new`: in round `r`, the union of the variants
emits every binding the naive run would emit on the snapshot of round `r`
and would not have emitted on the snapshot of round `r-1`.
`semi_naive_complete` iterates it over a chain of rounds: every naive
match of the last snapshot is a naive match of round 0 (which the loop
runs naive, `saturate.rs:917-942`) or is emitted by a variant of some
later round.
-/

namespace Semper.EMatch

/-- The naive run's emitted set is `Matches` (`schedA_matches` with the
constant `full` mode). -/
theorem mem_runNaive_iff {G : Graph} {sig : Sym → Kind} {atoms : List QAtom} {ap : APlan}
    (hwf : AtomsWF G sig atoms) (h : SchedA atoms ∅ ∅ ap) (σ' : Binding) :
    σ' ∈ runNaive G ap ↔ Matches G atoms σ' := by
  unfold runNaive
  rw [← runA_full G (fun _ => false), schedA_matches hwf h]
  exact ⟨fun h => h.1, fun hm => ⟨hm, modeOk_full _ _ _ hm⟩⟩

/-- One round: a naive match of the after-snapshot that is not a naive
match of the before-snapshot is emitted by the variant of its first new
join atom. -/
theorem semi_naive_round_complete {R : Round} (hwf : R.WF) (htr : R.tracking = true)
    {sig : Sym → Kind} {atoms : List QAtom} {ap : APlan}
    (hwf₀ : AtomsWF R.before sig atoms) (hwf₁ : AtomsWF R.after sig atoms)
    (h : SchedA atoms ∅ ∅ ap) {σ' : Binding}
    (hnew : σ' ∈ runNaive R.after ap) (hold : σ' ∉ runNaive R.before ap) :
    ∃ (k : Nat) (ak : RAtom), atoms[k]? = some (.scan ak) ∧
      σ' ∈ runVariant R.after R.isNew k ap := by
  have hm := (mem_runNaive_iff hwf₁ h σ').1 hnew
  rw [mem_runNaive_iff hwf₀ h] at hold
  obtain ⟨k, ak, hk, id, hid, hn⟩ := delta_complete hwf htr hm hold
  exact (variants_cover_new hwf₁ h σ').2 ⟨hnew, k, ak, hk, id, hid, hn⟩

/-- The same as an inclusion of emitted sets: naive on the after-snapshot
is covered by naive on the before-snapshot and the round's variants. -/
theorem runNaive_subset_round {R : Round} (hwf : R.WF) (htr : R.tracking = true)
    {sig : Sym → Kind} {atoms : List QAtom} {ap : APlan}
    (hwf₀ : AtomsWF R.before sig atoms) (hwf₁ : AtomsWF R.after sig atoms)
    (h : SchedA atoms ∅ ∅ ap) :
    ∀ σ' ∈ runNaive R.after ap, σ' ∈ runNaive R.before ap ∨
      ∃ (k : Nat) (ak : RAtom), atoms[k]? = some (.scan ak) ∧
        σ' ∈ runVariant R.after R.isNew k ap := by
  intro σ' hnew
  by_cases hold : σ' ∈ runNaive R.before ap
  · exact Or.inl hold
  · exact Or.inr (semi_naive_round_complete hwf htr hwf₀ hwf₁ h hnew hold)

/-- A chain of rounds starting from the snapshot `G`: each round starts
where the previous one ended. -/
def Chain : Graph → List Round → Prop
  | _, [] => True
  | G, R :: Rs => R.before = G ∧ Chain R.after Rs

/-- The snapshot at the end of a chain. -/
def finalGraph : Graph → List Round → Graph
  | G, [] => G
  | _, R :: Rs => finalGraph R.after Rs

/-- Every naive match of the final snapshot is a naive match of the
initial snapshot (round 0 runs naive) or is emitted by a variant of some
round of the chain. -/
theorem semi_naive_complete {sig : Sym → Kind} {atoms : List QAtom} {ap : APlan}
    (G₀ : Graph) (Rs : List Round) (hchain : Chain G₀ Rs)
    (hR : ∀ R ∈ Rs, R.WF ∧ R.tracking = true)
    (hatoms₀ : AtomsWF G₀ sig atoms) (hatoms : ∀ R ∈ Rs, AtomsWF R.after sig atoms)
    (h : SchedA atoms ∅ ∅ ap) {σ' : Binding} (hσ : σ' ∈ runNaive (finalGraph G₀ Rs) ap) :
    σ' ∈ runNaive G₀ ap ∨
      ∃ R ∈ Rs, ∃ (k : Nat) (ak : RAtom), atoms[k]? = some (.scan ak) ∧
        σ' ∈ runVariant R.after R.isNew k ap := by
  induction Rs generalizing G₀ with
  | nil => exact Or.inl hσ
  | cons R Rs ih =>
    obtain ⟨hb, hc⟩ := hchain
    subst hb
    have hRwf := hR R (by simp)
    have hRa := hatoms R (by simp)
    rcases ih R.after hc (fun R' hR' => hR R' (by simp [hR'])) hRa
        (fun R' h' => hatoms R' (by simp [h'])) hσ with hin | ⟨R', hR', hv⟩
    · rcases runNaive_subset_round hRwf.1 hRwf.2 hatoms₀ hRa h σ' hin with hold | hv
      · exact Or.inl hold
      · exact Or.inr ⟨R, by simp, hv⟩
    · exact Or.inr ⟨R', by simp [hR'], hv⟩

end Semper.EMatch
