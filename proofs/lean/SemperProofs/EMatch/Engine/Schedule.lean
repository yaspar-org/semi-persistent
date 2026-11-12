import SemperProofs.EMatch.Engine.Matcher

/-!
# The static scheduler (fidelity: `schedule_with_stats`)

The static plan of a rule is built once per round by `schedule_inner`
(`egraph/src/schedule.rs:865-954`), which `schedule_with_stats` (`:820`),
`schedule_with_stats_sampled` (`:834`) and `schedule_with_bound` (`:857`)
call with their statistics, sampler and seed. The loop (`:880-934`) runs
two phases until no scanning atom is left: the eager pass `lower_eager`
(`:1102-1139`) lowers every unused atom the bound set makes free, to a
fixpoint; then the cheapest unused scanning atom under `estimate_cost`
(`:889-903`) is lowered by `emit_atom` (`:1141-1398`). `scheduleEngine`
transcribes the loop on the atoms this development models, scanning atoms
and `Eq` atoms, with the price as a parameter: the plan is in the scheduler
grammar whatever the price (`scheduleEngine_schedA`), so the saturation
theorems' `MatchersOK` is a theorem for the static scheduler too
(`matcherOK_static_engine`), with no hypothesis, as `matcherOK_engine` is
for the adaptive one.

The transcription, line by line:

* the state is the used set, the bound set and the steps so far
  (`used`, `bound`, `steps`, `:871-874`); `bound` starts at the seed `pre`
  (`:872-874`, empty for `schedule_with_stats`);
* `lower_eager` sweeps the indices in order (`:1110`), skipping used atoms
  (`:1112-1114`), and lowers through `try_eager_lower` (`:1411-1507`): an
  `Eq` with a bound side is checked or copied (`:1418-1436`, `eagerLower`),
  a plain atom whose node is bound is re-joined in its class and its
  children read (`:1484-1495`, which is `lower a B` with `a.node ∈ B`:
  `joinLookups` gives `[byRepr, byOp]`, `childSteps` is
  `emit_read_children`); the sweep repeats while one lowered something
  (`:1107-1109`). The guards, the literal atoms, the disequalities and the
  global equalities (`:1120-1131`, `:1439-1483`) are outside the model.
  `eagerAt` is one index of the sweep, `eagerSweep` one sweep, `eagerFix`
  the loop; the fuel `atoms.length + 1` is exact, each productive sweep
  uses an atom (`eagerFix_fixed`);
* phase B scans the indices in order (`:890`), skips the used atoms and the
  atoms with no join (`:891-897`, which leaves the unused scanning atoms),
  prices each candidate (`:898`) and keeps the first, replacing it only on a
  strict improvement (`:899-901`), so a tie keeps the lowest index
  (`pickStep`, `pickBest`); no candidate ends the loop (`:905`);
* the chosen atom is lowered by `emit_atom` under the bound set in hand
  (`:931`, `lower a B`: `Lower.lean`), marked used (`:932`), and the loop
  returns to the eager pass. A `Collect` atom (`:906-930`) is outside the
  model. The main loop's fuel `atoms.length` is exact, each iteration uses
  an atom.

The price `cost steps B i` is what `estimate_cost` (`:711`) gives atom `i`
under the bound set `B`, from the statistics, the emitters (`record_emitters`,
a function of the atoms used so far) and the sampler's draws, all of which
the plan emitted so far determines; the proof never reads it, and `κ` with
its strict order stands for `f64` under `<` (`:900`). The plan differs from
the engine's where `lower` differs from `emit_atom` (a `:comm` atom's
`byContains` lookups, `engineJoinLookups`, `Choose.lean`); the unit test
`static_plan_agrees_with_the_model_on_the_rounds_corpus` (`schedule.rs`)
compares the engine's plan with a transliteration of `scheduleEngine` that
reads the engine's prices and emits `engineJoinLookups`.
-/

namespace Semper.EMatch

/-- The scheduler's state (`schedule_inner`, `:871-874`): the atoms lowered
so far, the class variables bound so far and the steps emitted so far. -/
structure SchedState where
  used : Finset Nat
  B : Finset Var
  steps : APlan

variable {κ : Type} [LT κ] [DecidableRel (α := κ) (· < ·)]

/-! ## The eager pass -/

/-- One index of a sweep of `lower_eager` (`:1111-1136`): a used atom is
skipped; an `Eq` with a bound side is lowered (`try_eager_lower`,
`:1418-1436`); a plain atom whose node is bound is re-joined in its class
and its children read (`:1484-1495`). The flag is `progress`. -/
def eagerAt (atoms : List QAtom) (st : SchedState) (i : Nat) : SchedState × Bool :=
  if i ∈ st.used then (st, false)
  else
    match atoms[i]? with
    | some (.eq x y) =>
        if x ∈ st.B ∨ y ∈ st.B then
          (⟨insert i st.used, st.B ∪ (QAtom.eq x y).binds,
            st.steps ++ ((QAtom.eq x y).eagerLower st.B).map (i, ·)⟩, true)
        else (st, false)
    | some (.scan a) =>
        match a.shape with
        | .plain _ =>
            if a.node ∈ st.B then
              (⟨insert i st.used, st.B ∪ a.binds, st.steps ++ (lower a st.B).map (i, ·)⟩, true)
            else (st, false)
        | _ => (st, false)
    | none => (st, false)

/-- One sweep of `lower_eager` over the indices (`:1110-1137`), carrying
`progress`. -/
def eagerSweep (atoms : List QAtom) : List Nat → SchedState → Bool → SchedState × Bool
  | [], st, p => (st, p)
  | i :: is, st, p =>
      let r := eagerAt atoms st i
      eagerSweep atoms is r.1 (p || r.2)

/-- `lower_eager` (`:1102-1139`): sweep while a sweep lowered something. -/
def eagerFix (atoms : List QAtom) : Nat → SchedState → SchedState
  | 0, st => st
  | fuel + 1, st =>
      let r := eagerSweep atoms (List.range atoms.length) st false
      if r.2 then eagerFix atoms fuel r.1 else r.1

/-! ## Phase B -/

/-- One index of the scan of phase B (`:890-903`): skip a used atom and an
atom with no join; price a candidate; keep the first, replace it only by a
strictly cheaper one (`is_none_or(|(_, b)| c < b)`, `:900`). -/
def pickStep (atoms : List QAtom) (used : Finset Nat) (price : Nat → κ)
    (best : Option (Nat × κ)) (i : Nat) : Option (Nat × κ) :=
  if i ∈ used then best
  else
    match atoms[i]? with
    | some (.scan _) =>
        let c := price i
        match best with
        | none => some (i, c)
        | some (j, b) => if c < b then some (i, c) else some (j, b)
    | _ => best

/-- Phase B (`:889-905`): the cheapest unused scanning atom, lowest index
first on a tie; `none` when every scanning atom is used. -/
def pickBest (atoms : List QAtom) (used : Finset Nat) (price : Nat → κ) : Option Nat :=
  ((List.range atoms.length).foldl (pickStep atoms used price) none).map (·.1)

/-! ## The loop -/

/-- The loop of `schedule_inner` (`:880-934`): the eager pass, then the
pick, then `emit_atom` on the chosen atom, under the bound set in hand.
`cost steps B i` prices atom `i` after the steps `steps` under `B`. -/
def schedLoop (cost : APlan → Finset Var → Nat → κ) (atoms : List QAtom) :
    Nat → SchedState → APlan
  | 0, st => st.steps
  | fuel + 1, st =>
      let st₁ := eagerFix atoms (atoms.length + 1) st
      match pickBest atoms st₁.used (cost st₁.steps st₁.B) with
      | none => st₁.steps
      | some i =>
          match atoms[i]? with
          | some (.scan a) =>
              schedLoop cost atoms fuel
                ⟨insert i st₁.used, st₁.B ∪ a.binds, st₁.steps ++ (lower a st₁.B).map (i, ·)⟩
          | _ => st₁.steps

/-- `schedule_inner` (`:865-954`) on the atoms, with the seed `pre`
(`schedule_with_bound`; `∅` for `schedule_with_stats`). -/
def scheduleEngine (cost : APlan → Finset Var → Nat → κ) (pre : Finset Var) (atoms : List QAtom) :
    APlan :=
  schedLoop cost atoms atoms.length ⟨∅, pre, []⟩

/-! ## The plan is in the scheduler grammar -/

/-- `st'` extends `st` by a block the grammar admits: whatever continuation
is valid from `st'`, the block followed by it is valid from `st`. -/
def Prefix (atoms : List QAtom) (st st' : SchedState) : Prop :=
  ∃ blk, st'.steps = st.steps ++ blk ∧
    ∀ rest, SchedA atoms st'.used st'.B rest → SchedA atoms st.used st.B (blk ++ rest)

theorem Prefix.refl (atoms : List QAtom) (st : SchedState) : Prefix atoms st st :=
  ⟨[], by simp, fun rest h => h⟩

theorem Prefix.trans {atoms : List QAtom} {st₁ st₂ st₃ : SchedState}
    (h₁ : Prefix atoms st₁ st₂) (h₂ : Prefix atoms st₂ st₃) : Prefix atoms st₁ st₃ := by
  obtain ⟨b₁, hs₁, h₁⟩ := h₁
  obtain ⟨b₂, hs₂, h₂⟩ := h₂
  refine ⟨b₁ ++ b₂, by rw [hs₂, hs₁, List.append_assoc], fun rest h => ?_⟩
  rw [List.append_assoc]
  exact h₁ _ (h₂ _ h)

/-- The unused valid indices, on a state. -/
def SchedState.unused (atoms : List QAtom) (st : SchedState) : Nat := unusedCount atoms st.used

theorem unusedCount_le_length (atoms : List QAtom) (used : Finset Nat) :
    unusedCount atoms used ≤ atoms.length := by
  unfold unusedCount
  exact (Finset.card_filter_le _ _).trans (by simp)

/-- One index of the eager sweep: no change, or a block of the grammar on a
fresh atom. -/
theorem eagerAt_spec (atoms : List QAtom) (st : SchedState) (i : Nat) :
    (eagerAt atoms st i).2 = false ∧ (eagerAt atoms st i).1 = st ∨
    (eagerAt atoms st i).2 = true ∧ Prefix atoms st (eagerAt atoms st i).1 ∧
      i < atoms.length ∧ i ∉ st.used ∧ (eagerAt atoms st i).1.used = insert i st.used := by
  unfold eagerAt
  split
  · exact Or.inl ⟨rfl, rfl⟩
  · rename_i hu
    split
    · rename_i x y hq
      split
      · rename_i hf
        refine Or.inr ⟨rfl, ⟨_, rfl, fun rest h => SchedA.eager hq hu hf h⟩,
          (List.getElem?_eq_some_iff.1 hq).1, hu, rfl⟩
      · exact Or.inl ⟨rfl, rfl⟩
    · rename_i a hq
      split
      · split
        · refine Or.inr ⟨rfl, ⟨_, rfl, fun rest h => SchedA.pick hq hu h⟩,
            (List.getElem?_eq_some_iff.1 hq).1, hu, rfl⟩
        · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inl ⟨rfl, rfl⟩

theorem eagerAt_prefix (atoms : List QAtom) (st : SchedState) (i : Nat) :
    Prefix atoms st (eagerAt atoms st i).1 := by
  rcases eagerAt_spec atoms st i with ⟨-, h⟩ | ⟨-, h, -⟩
  · rw [h]; exact Prefix.refl atoms st
  · exact h

theorem eagerAt_unused (atoms : List QAtom) (st : SchedState) (i : Nat) :
    unusedCount atoms (eagerAt atoms st i).1.used ≤ unusedCount atoms st.used ∧
    ((eagerAt atoms st i).2 = true →
      unusedCount atoms (eagerAt atoms st i).1.used < unusedCount atoms st.used) := by
  rcases eagerAt_spec atoms st i with ⟨hp, h⟩ | ⟨hp, -, hi, hu, h⟩
  · rw [h]; exact ⟨le_rfl, fun h' => by rw [hp] at h'; cases h'⟩
  · rw [h]
    have := unusedCount_insert (used := st.used) hi hu
    exact ⟨by omega, fun _ => by omega⟩

/-- A false flag means the index changed nothing. -/
theorem eagerAt_false {atoms : List QAtom} {st : SchedState} {i : Nat}
    (h : (eagerAt atoms st i).2 = false) : (eagerAt atoms st i).1 = st := by
  rcases eagerAt_spec atoms st i with ⟨-, h'⟩ | ⟨hp, -⟩
  · exact h'
  · rw [hp] at h; cases h

theorem eagerSweep_prefix (atoms : List QAtom) :
    ∀ (is : List Nat) (st : SchedState) (p : Bool), Prefix atoms st (eagerSweep atoms is st p).1 := by
  intro is
  induction is with
  | nil => intro st p; exact Prefix.refl atoms st
  | cons i is ih =>
      intro st p
      simp only [eagerSweep]
      exact (eagerAt_prefix atoms st i).trans (ih _ _)

theorem eagerSweep_unused (atoms : List QAtom) :
    ∀ (is : List Nat) (st : SchedState) (p : Bool),
      unusedCount atoms (eagerSweep atoms is st p).1.used ≤ unusedCount atoms st.used ∧
      (p = false → (eagerSweep atoms is st p).2 = true →
        unusedCount atoms (eagerSweep atoms is st p).1.used < unusedCount atoms st.used) := by
  intro is
  induction is with
  | nil => intro st p; exact ⟨le_rfl, fun hp h => by simp [eagerSweep, hp] at h⟩
  | cons i is ih =>
      intro st p
      simp only [eagerSweep]
      obtain ⟨h₁, h₂⟩ := eagerAt_unused atoms st i
      obtain ⟨h₃, h₄⟩ := ih (eagerAt atoms st i).1 (p || (eagerAt atoms st i).2)
      refine ⟨h₃.trans h₁, fun hp h => ?_⟩
      subst hp
      cases hq : (eagerAt atoms st i).2 with
      | true => rw [hq] at h₃; exact lt_of_le_of_lt h₃ (h₂ hq)
      | false =>
          rw [hq] at h₄ h
          exact lt_of_lt_of_le (h₄ rfl h) h₁

/-- The flag is monotone: once set, a sweep returns it set. -/
theorem eagerSweep_true (atoms : List QAtom) :
    ∀ (is : List Nat) (st : SchedState), (eagerSweep atoms is st true).2 = true := by
  intro is
  induction is with
  | nil => intro st; rfl
  | cons i is ih => intro st; simp only [eagerSweep, Bool.true_or]; exact ih _

/-- A sweep that made no progress changed nothing, and every index of it
changes nothing from the state it returned. -/
theorem eagerSweep_fixed (atoms : List QAtom) :
    ∀ (is : List Nat) (st : SchedState), (eagerSweep atoms is st false).2 = false →
      (eagerSweep atoms is st false).1 = st ∧ ∀ i ∈ is, (eagerAt atoms st i).2 = false := by
  intro is
  induction is with
  | nil => intro st _; exact ⟨rfl, by simp⟩
  | cons i is ih =>
      intro st h
      simp only [eagerSweep, Bool.false_or] at h ⊢
      cases hq : (eagerAt atoms st i).2 with
      | true => rw [hq, eagerSweep_true] at h; cases h
      | false =>
          rw [hq] at h
          rw [eagerAt_false hq] at h ⊢
          obtain ⟨h₁, h₂⟩ := ih st h
          refine ⟨h₁, fun j hj => ?_⟩
          rcases List.mem_cons.1 hj with rfl | hj
          · exact hq
          · exact h₂ j hj

theorem eagerFix_prefix (atoms : List QAtom) :
    ∀ (fuel : Nat) (st : SchedState), Prefix atoms st (eagerFix atoms fuel st) := by
  intro fuel
  induction fuel with
  | zero => intro st; exact Prefix.refl atoms st
  | succ fuel ih =>
      intro st
      simp only [eagerFix]
      split
      · exact (eagerSweep_prefix atoms _ st false).trans (ih _)
      · exact eagerSweep_prefix atoms _ st false

theorem eagerFix_unused (atoms : List QAtom) :
    ∀ (fuel : Nat) (st : SchedState),
      unusedCount atoms (eagerFix atoms fuel st).used ≤ unusedCount atoms st.used := by
  intro fuel
  induction fuel with
  | zero => intro st; exact le_rfl
  | succ fuel ih =>
      intro st
      simp only [eagerFix]
      split
      · exact (ih _).trans (eagerSweep_unused atoms _ st false).1
      · exact (eagerSweep_unused atoms _ st false).1

/-- With enough fuel, the eager pass ends at a fixpoint: no unused atom is
free. Each productive sweep uses an atom, so `unusedCount + 1` sweeps
suffice. -/
theorem eagerFix_fixed (atoms : List QAtom) :
    ∀ (fuel : Nat) (st : SchedState), unusedCount atoms st.used < fuel →
      ∀ (i : Nat) (q : QAtom), atoms[i]? = some q → i ∉ (eagerFix atoms fuel st).used →
        ¬ q.eagerFree (eagerFix atoms fuel st).B := by
  intro fuel
  induction fuel with
  | zero => intro st h; omega
  | succ fuel ih =>
      intro st hfuel i q hq hu hf
      simp only [eagerFix] at hu hf
      split at hu
      · rename_i hp
        have hlt := (eagerSweep_unused atoms _ st false).2 rfl hp
        simp only [hp, ↓reduceIte] at hf
        exact ih _ (by omega) i q hq hu hf
      · rename_i hp
        simp only [hp] at hf
        have hp' : (eagerSweep atoms (List.range atoms.length) st false).2 = false := by
          simpa using hp
        obtain ⟨hst, hall⟩ := eagerSweep_fixed atoms _ st hp'
        rw [hst] at hu hf
        have hi : i < atoms.length := (List.getElem?_eq_some_iff.1 hq).1
        have hz := hall i (List.mem_range.2 hi)
        cases q with
        | scan a => exact hf
        | eq x y =>
            unfold eagerAt at hz
            simp only [hu, ↓reduceIte, hq] at hz
            split at hz
            · cases hz
            · rename_i hnf
              exact hnf hf

/-- The best so far, if any, is an unused scanning atom. -/
def PickOk (atoms : List QAtom) (used : Finset Nat) : Option (Nat × κ) → Prop
  | none => True
  | some (i, _) => i ∉ used ∧ ∃ a, atoms[i]? = some (.scan a)

theorem pickStep_ok {atoms : List QAtom} {used : Finset Nat} {price : Nat → κ}
    {best : Option (Nat × κ)} {i : Nat} (h : PickOk atoms used best) :
    PickOk atoms used (pickStep atoms used price best i) := by
  unfold pickStep
  split
  · exact h
  · rename_i hu
    split
    · rename_i a hq
      cases best with
      | none => exact ⟨hu, a, hq⟩
      | some p =>
          obtain ⟨j, b⟩ := p
          simp only
          split
          · exact ⟨hu, a, hq⟩
          · exact h
    · exact h

theorem pickStep_isSome {atoms : List QAtom} {used : Finset Nat} {price : Nat → κ}
    {best : Option (Nat × κ)} {i : Nat} (h : best.isSome = true) :
    (pickStep atoms used price best i).isSome = true := by
  unfold pickStep
  split
  · exact h
  · split
    · cases best with
      | none => rfl
      | some p => obtain ⟨j, b⟩ := p; simp only; split <;> rfl
    · exact h

theorem pickStep_mem_isSome {atoms : List QAtom} {used : Finset Nat} {price : Nat → κ}
    {best : Option (Nat × κ)} {i : Nat} {a : RAtom} (hu : i ∉ used) (hq : atoms[i]? = some (.scan a)) :
    (pickStep atoms used price best i).isSome = true := by
  unfold pickStep
  simp only [hu, ↓reduceIte, hq]
  cases best with
  | none => rfl
  | some p => obtain ⟨j, b⟩ := p; simp only; split <;> rfl

theorem foldl_pickStep_ok (atoms : List QAtom) (used : Finset Nat) (price : Nat → κ) :
    ∀ (l : List Nat) (best : Option (Nat × κ)), PickOk atoms used best →
      PickOk atoms used (l.foldl (pickStep atoms used price) best) := by
  intro l
  induction l with
  | nil => intro best h; exact h
  | cons i l ih => intro best h; exact ih _ (pickStep_ok h)

theorem foldl_pickStep_isSome (atoms : List QAtom) (used : Finset Nat) (price : Nat → κ) :
    ∀ (l : List Nat) (best : Option (Nat × κ)), best.isSome = true →
      (l.foldl (pickStep atoms used price) best).isSome = true := by
  intro l
  induction l with
  | nil => intro best h; exact h
  | cons i l ih => intro best h; exact ih _ (pickStep_isSome h)

theorem foldl_pickStep_some (atoms : List QAtom) (used : Finset Nat) (price : Nat → κ) :
    ∀ (l : List Nat) (best : Option (Nat × κ)),
      (∃ i ∈ l, i ∉ used ∧ ∃ a, atoms[i]? = some (.scan a)) →
      (l.foldl (pickStep atoms used price) best).isSome = true := by
  intro l
  induction l with
  | nil => rintro best ⟨i, hi, -⟩; simp at hi
  | cons j l ih =>
      rintro best ⟨i, hi, hu, a, hq⟩
      simp only [List.mem_cons] at hi
      simp only [List.foldl_cons]
      rcases hi with rfl | hi
      · exact foldl_pickStep_isSome atoms used price l _ (pickStep_mem_isSome hu hq)
      · exact ih _ ⟨i, hi, hu, a, hq⟩

/-- A pick is an unused scanning atom. -/
theorem pickBest_some {atoms : List QAtom} {used : Finset Nat} {price : Nat → κ} {i : Nat}
    (h : pickBest atoms used price = some i) : i ∉ used ∧ ∃ a, atoms[i]? = some (.scan a) := by
  unfold pickBest at h
  have hok := foldl_pickStep_ok atoms used price (List.range atoms.length) none trivial
  revert h hok
  cases (List.range atoms.length).foldl (pickStep atoms used price) none with
  | none => intro h; simp at h
  | some p =>
      obtain ⟨j, b⟩ := p
      intro h hok
      simp only [Option.map_some, Option.some.injEq] at h
      subst h
      exact hok

/-- No pick means every scanning atom is used. -/
theorem pickBest_none {atoms : List QAtom} {used : Finset Nat} {price : Nat → κ}
    (h : pickBest atoms used price = none) :
    ∀ (i : Nat) (a : RAtom), atoms[i]? = some (.scan a) → i ∈ used := by
  intro i a hq
  by_contra hu
  have hs := foldl_pickStep_some atoms used price (List.range atoms.length) none
    ⟨i, List.mem_range.2 (List.getElem?_eq_some_iff.1 hq).1, hu, a, hq⟩
  unfold pickBest at h
  rw [Option.map_eq_none_iff] at h
  rw [h] at hs
  cases hs

/-- The loop from any state with enough fuel emits its steps followed by a
plan the grammar admits from that state. -/
theorem schedLoop_schedA (cost : APlan → Finset Var → Nat → κ) (atoms : List QAtom) :
    ∀ (fuel : Nat) (st : SchedState), unusedCount atoms st.used ≤ fuel →
      ∃ rest, schedLoop cost atoms fuel st = st.steps ++ rest ∧ SchedA atoms st.used st.B rest := by
  intro fuel
  induction fuel with
  | zero =>
      intro st h
      refine ⟨[], by simp [schedLoop], SchedA.done ?_ ?_⟩
      · intro i a hq
        exact unusedCount_zero (Nat.le_zero.1 h) i _ hq
      · intro i q hq hu
        exact absurd (unusedCount_zero (Nat.le_zero.1 h) i q hq) hu
  | succ fuel ih =>
      intro st hfuel
      simp only [schedLoop]
      obtain ⟨blk, hblk, hpre⟩ := eagerFix_prefix atoms (atoms.length + 1) st
      have hfix := eagerFix_fixed atoms (atoms.length + 1) st
        (Nat.lt_succ_of_le (unusedCount_le_length atoms st.used))
      have hun := eagerFix_unused atoms (atoms.length + 1) st
      generalize hst₁ : eagerFix atoms (atoms.length + 1) st = st₁ at hblk hpre hfix hun
      split
      · rename_i hnone
        exact ⟨blk, hblk, by simpa using hpre [] (SchedA.done (pickBest_none hnone) hfix)⟩
      · rename_i i hsome
        obtain ⟨hu, a, hq⟩ := pickBest_some hsome
        rw [hq]
        have hi : i < atoms.length := (List.getElem?_eq_some_iff.1 hq).1
        have hcount := unusedCount_insert (used := st₁.used) hi hu
        obtain ⟨rest, hrest, hsched⟩ := ih
          ⟨insert i st₁.used, st₁.B ∪ a.binds, st₁.steps ++ (lower a st₁.B).map (i, ·)⟩
          (by simp only; omega)
        simp only at hrest
        refine ⟨blk ++ ((lower a st₁.B).map (i, ·) ++ rest), ?_, ?_⟩
        · show schedLoop cost atoms fuel _ = _
          rw [hrest, hblk, List.append_assoc, List.append_assoc]
        · exact hpre _ (SchedA.pick hq hu hsched)

/-- The static scheduler's plan is in the scheduler grammar, whatever the
price and the seed. -/
theorem scheduleEngine_schedA (cost : APlan → Finset Var → Nat → κ) (pre : Finset Var)
    (atoms : List QAtom) : SchedA atoms ∅ pre (scheduleEngine cost pre atoms) := by
  obtain ⟨rest, h, hs⟩ := schedLoop_schedA cost atoms atoms.length ⟨∅, pre, []⟩
    (unusedCount_le_length atoms ∅)
  unfold scheduleEngine
  rw [h]
  simpa using hs

/-- `PlanOK` of the erased plan of `schedule_with_stats`. -/
theorem scheduleEngine_planOK (cost : APlan → Finset Var → Nat → κ) (atoms : List QAtom) :
    PlanOK atoms ((scheduleEngine cost ∅ atoms).map (·.2)) :=
  sched_of_schedA (scheduleEngine_schedA cost ∅ atoms)

/-- The matcher of a rule compiled by `schedule_with_stats`: the static plan
under `run_query_into`. -/
def Matcher.staticEngine (cost : APlan → Finset Var → Nat → κ) (atoms : List QAtom) : Matcher :=
  .static (scheduleEngine cost ∅ atoms)

/-- `MatcherOK` for the static scheduler, with no hypothesis: the
counterpart of `matcherOK_engine` for the shipped default. -/
theorem matcherOK_static_engine (cost : APlan → Finset Var → Nat → κ) (atoms : List QAtom) :
    MatcherOK atoms (.staticEngine cost atoms) :=
  matcherOK_static (scheduleEngine_schedA cost ∅ atoms)

/-- The static scheduler's naive run emits exactly `Matches`. -/
theorem scheduleEngine_naive_matches {G : Graph} {sig : Sym → Kind} {atoms : List QAtom}
    (cost : APlan → Finset Var → Nat → κ) (hwf : AtomsWF G sig atoms) :
    ∀ σ', σ' ∈ run G ((scheduleEngine cost ∅ atoms).map (·.2)) Binding.empty ↔ Matches G atoms σ' :=
  plan_matches hwf (scheduleEngine_planOK cost atoms)

/-- The static and the adaptive scheduler emit the same set under the same
index settings. -/
theorem scheduleEngine_eq_runEngine {G : Graph} {sig : Sym → Kind} {isNew : NodeId → Bool}
    {mode : Nat → IndexMode} {atoms : List QAtom} (cost : APlan → Finset Var → Nat → κ)
    (hwf : AtomsWF G sig atoms) :
    ∀ σ', σ' ∈ Matcher.staticEngine cost atoms G isNew mode ↔ σ' ∈ runEngine G isNew mode atoms :=
  fun σ' => (runEngine_eq_plan hwf (scheduleEngine_schedA cost ∅ atoms) σ').symm

end Semper.EMatch
