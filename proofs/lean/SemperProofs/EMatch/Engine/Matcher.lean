import SemperProofs.EMatch.Engine.Choose
import SemperProofs.EMatch.Engine.Rounds.Complete

/-!
# A rule's matcher (spec-actions §F, the matching side)

A compiled rule matches through one of two procedures: the static plan
`schedule_with_stats` built for it, run by `run_query_into`, or the
adaptive scheduler, which lowers one atom at a time from the bindings in
hand (`run_query_scheduled_into`, `ematch.rs:1244-1281`; the engine
selects per thread, `SchedulingMode`, `ematch.rs:1337-1341`). Both read
the snapshot through the round's `VariantIndex`: the naive run with every
atom on the full index, variant `k` with the modes `variantMode k`.

`Matcher` abstracts the procedure as the set of bindings it emits on a
snapshot for a new-node predicate and a per-atom mode. `MatcherOK atoms m`
is what the saturation theorems need of it: on a graph where the atoms are
well formed, `m` emits exactly the matches the modes admit. The static plan
satisfies it when the plan is in the scheduler grammar (`matcherOK_static`,
from `schedA_matches`), which the plan `schedule_with_stats` builds is
(`scheduleEngine_schedA`, `matcherOK_static_engine`, `Schedule.lean`); the
adaptive scheduler satisfies it for every choice function
(`matcherOK_runtime`, from `runNDA_matches`), in particular for the
engine's (`matcherOK_engine`). The semi-naive facts the saturation
invariant uses, `MatcherOK.naive_iff` and `MatcherOK.round_complete`, are
`mem_runNaive_iff` and `semi_naive_round_complete` restated on a matcher.
-/

namespace Semper.EMatch

/-- A matching procedure: the bindings it emits on a snapshot, for a new-node
predicate and a per-atom index mode. -/
abbrev Matcher := Graph → (NodeId → Bool) → (Nat → IndexMode) → List Binding

/-- The matcher emits exactly the matches the modes admit, on every graph
where the atoms are well formed. -/
def MatcherOK (atoms : List QAtom) (m : Matcher) : Prop :=
  ∀ {G : Graph} {sig : Sym → Kind} (isNew : NodeId → Bool) (mode : Nat → IndexMode),
    AtomsWF G sig atoms → ∀ σ', σ' ∈ m G isNew mode ↔ Matches G atoms σ' ∧ ModeOk isNew atoms mode σ'

namespace Matcher

/-- The static plan, run by `run_query_into` under the round's modes. -/
def static (ap : APlan) : Matcher := fun G isNew mode => runA G isNew mode ap Binding.empty

/-- The adaptive scheduler with a choice function that may read the
snapshot, the delta and the modes (as `choose_atom` reads bucket lengths). -/
def runtime (atoms : List QAtom)
    (choose : Graph → (NodeId → Bool) → (Nat → IndexMode) → Binding → Finset Nat → Nat) : Matcher :=
  fun G isNew mode => runNDA G isNew mode atoms (choose G isNew mode) atoms.length ∅ ∅ Binding.empty

/-- The adaptive scheduler with the engine's choice function. -/
def engine (atoms : List QAtom) : Matcher := fun G isNew mode => runEngine G isNew mode atoms

/-- The naive run: every atom reads the full index (`VariantIndex::naive`). -/
def naive (m : Matcher) (G : Graph) : List Binding := m G (fun _ => false) (fun _ => .full)

/-- Variant `k`: atom `k` reads the delta, the atoms before it the full
index minus the delta, the rest the full index (`variantMode`). -/
def variant (m : Matcher) (G : Graph) (isNew : NodeId → Bool) (k : Nat) : List Binding :=
  m G isNew (variantMode k)

end Matcher

theorem matcherOK_static {atoms : List QAtom} {ap : APlan} (h : SchedA atoms ∅ ∅ ap) :
    MatcherOK atoms (.static ap) :=
  fun _ _ hwf σ' => schedA_matches hwf h σ'

theorem matcherOK_runtime (atoms : List QAtom)
    (choose : Graph → (NodeId → Bool) → (Nat → IndexMode) → Binding → Finset Nat → Nat) :
    MatcherOK atoms (.runtime atoms choose) :=
  fun isNew mode hwf σ' => runNDA_matches (choose _ isNew mode) hwf σ'

theorem matcherOK_engine (atoms : List QAtom) : MatcherOK atoms (.engine atoms) :=
  fun _ _ hwf σ' => runEngine_matches hwf σ'

theorem Matcher.engine_eq_runtime (atoms : List QAtom) :
    Matcher.engine atoms = Matcher.runtime atoms (fun G isNew mode => chooseEngine G isNew mode atoms) := rfl

namespace MatcherOK

variable {atoms : List QAtom} {m : Matcher}

/-- `mem_runNaive_iff` on a matcher: the naive run emits exactly `Matches`. -/
theorem naive_iff (hM : MatcherOK atoms m) {G : Graph} {sig : Sym → Kind} (hwf : AtomsWF G sig atoms)
    (σ' : Binding) : σ' ∈ m.naive G ↔ Matches G atoms σ' := by
  unfold Matcher.naive
  rw [hM _ _ hwf]
  exact ⟨And.left, fun hm => ⟨hm, modeOk_full _ _ _ hm⟩⟩

/-- `variant_partition` on a matcher. -/
theorem variant_iff (hM : MatcherOK atoms m) {G : Graph} {sig : Sym → Kind} (hwf : AtomsWF G sig atoms)
    {isNew : NodeId → Bool} {k : Nat} {ak : RAtom} (hk : atoms[k]? = some (.scan ak)) (σ' : Binding) :
    σ' ∈ m.variant G isNew k ↔
      σ' ∈ m.naive G ∧ (∃ id, σ'.node ak.node = some id ∧ isNew id = true) ∧
        ∀ (j : Nat) (a : RAtom), j < k → atoms[j]? = some (.scan a) →
          ∃ id, σ'.node a.node = some id ∧ isNew id = false := by
  unfold Matcher.variant
  rw [hM _ _ hwf, hM.naive_iff hwf]
  constructor
  · rintro ⟨hm, hmode⟩
    exact ⟨hm, (modeOk_variant_iff hk hm).1 hmode⟩
  · rintro ⟨hm, hv⟩
    exact ⟨hm, (modeOk_variant_iff hk hm).2 hv⟩

/-- `semi_naive_round_complete` on a matcher: a match of the after
snapshot that is not a match of the before snapshot is emitted by the
variant of its first new scanning atom. -/
theorem round_complete (hM : MatcherOK atoms m) {R : Round} (hwf : R.WF) (htr : R.tracking = true)
    {sig : Sym → Kind} (hwf₀ : AtomsWF R.before sig atoms) (hwf₁ : AtomsWF R.after sig atoms)
    {σ' : Binding} (hnew : σ' ∈ m.naive R.after) (hold : σ' ∉ m.naive R.before) :
    ∃ (k : Nat) (ak : RAtom), atoms[k]? = some (.scan ak) ∧ σ' ∈ m.variant R.after R.isNew k := by
  have hm := (hM.naive_iff hwf₁ σ').1 hnew
  rw [hM.naive_iff hwf₀] at hold
  obtain ⟨k, ak, hk, id, hid, hn⟩ := delta_complete hwf htr hm hold
  obtain ⟨k', ak', hk', hmode⟩ := matches_cover_new hm ⟨k, ak, hk, id, hid, hn⟩
  refine ⟨k', ak', hk', ?_⟩
  unfold Matcher.variant
  exact (hM _ _ hwf₁ σ').2 ⟨hm, hmode⟩

end MatcherOK

/-- The static matcher of a `SchedA` plan is the plan's naive run. -/
theorem Matcher.static_naive (ap : APlan) (G : Graph) :
    (Matcher.static ap).naive G = runNaive G ap := by
  unfold Matcher.static Matcher.naive runNaive
  exact runA_full G _ ap Binding.empty

/-- The static matcher's variant `k` is the plan's variant `k`. -/
theorem Matcher.static_variant (ap : APlan) (G : Graph) (isNew : NodeId → Bool) (k : Nat) :
    (Matcher.static ap).variant G isNew k = runVariant G isNew k ap := rfl

end Semper.EMatch
