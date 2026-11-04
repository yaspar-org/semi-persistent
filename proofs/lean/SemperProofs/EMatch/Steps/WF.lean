import SemperProofs.EMatch.Steps.Simple

/-!
# Extended plan well-formedness (A.7: tracking literal variables)

`XPlanWF B Bl plan`: `B` the class/node variables bound when the plan
starts, `Bl` the literal variables; every step reads bound variables and
adds the ones it binds. On core steps it is `PlanWF` (`XPlanWF_of_PlanWF`,
`PlanWF_of_XPlanWF`).

`xplan_wf_sound`: along any run of a well-formed plan, a `CheckPred` step
only reads bound literal slots; so the model's "unbound slot" fault never
fires, and a guard fault (`evalPred = none`) comes from a primitive being
undefined.

Correction to the brief's `writeEnv_lit_mono`: `fill` *overwrites* a
literal scalar (`set_lit_val`, no undo), so a bound slot stays bound but
not necessarily with the same value; the monotonicity is on `isSome`
(`writeEnv_lit_isSome`).
-/

namespace Semper.EMatch.Steps

open Semper.EMatch

/-! ## Reads and binds of the core steps -/

/-- The class/node variables a core step reads (as `PlanWF`). -/
def _root_.Semper.EMatch.Step.reads : Step → List Var
  | .join _ ls => ls.flatMap Lookup.reads
  | .extractChild v _ _ => [v]
  | .checkChildEq v _ x => [v, x]
  | .checkEq x y => [x, y]
  | .copyBinding _ o => [o]
  | .decomposeAC v _ _ => [v]
  | .decomposeACI v _ _ => [v]
  | .expandA v _ _ _ => [v]
  | .decomposeComm v _ _ => [v]

/-- The variables a core step binds (as `PlanWF`). -/
def _root_.Semper.EMatch.Step.binds : Step → List Var
  | .join t _ => [t]
  | .extractChild _ _ out => [out]
  | .checkChildEq _ _ _ => []
  | .checkEq _ _ => []
  | .copyBinding t _ => [t]
  | .decomposeAC _ elems rest => acBinds elems rest
  | .decomposeACI _ elems rest => elems ++ rest.toList
  | .expandA _ pre elems suf => pre.toList ++ elems ++ suf.toList
  | .decomposeComm _ x y => [x, y]

/-- The class/node variables a `Collect` step binds: the node and
multiplicity scalars, the filters' element rests and class columns, the
bare rest. -/
def SeqSpec.collectBinds (S : SeqSpec) : List Var :=
  S.layout.scalars.filterMap (fun sr => match sr with
    | .node v => some v | .mult v => some v | .lit _ => none) ++
  S.layout.filters.flatMap (fun fl =>
    (match fl.elems with | .seq v => v | .set v => v | .mset v => v) ::
      fl.cols.filterMap (fun cr => match cr with | .node v => some v | _ => none)) ++
  (match S.layout.bare with
    | some (.seq v) => [v] | some (.set v) => [v] | some (.mset v) => [v] | none => [])

/-- The literal slots a `Collect` step binds: its literal scalars. (Its
literal columns go to `litSeq`, which no guard reads.) -/
def SeqSpec.collectLitBinds (S : SeqSpec) : List Var :=
  S.layout.scalars.filterMap (fun sr => match sr with | .lit v => some v | _ => none)

/-- `XPlanWF B Bl plan`. -/
inductive XPlanWF : List Var → List Var → XPlan → Prop
  | nil {B Bl : List Var} : XPlanWF B Bl []
  | core {B Bl : List Var} {s : Step} {ss : XPlan} :
      (∀ x ∈ s.reads, x ∈ B) → XPlanWF (s.binds ++ B) Bl ss → XPlanWF B Bl (.core s :: ss)
  | checkNeq {B Bl : List Var} {x y : Var} {ss : XPlan} :
      x ∈ B → y ∈ B → XPlanWF B Bl ss → XPlanWF B Bl (.checkNeq x y :: ss)
  | checkEqGlobal {B Bl : List Var} {x : Var} {g : GVar} {ss : XPlan} :
      x ∈ B → XPlanWF B Bl ss → XPlanWF B Bl (.checkEqGlobal x g :: ss)
  | bindGlobal {B Bl : List Var} {x : Var} {g : GVar} {ss : XPlan} :
      XPlanWF (x :: B) Bl ss → XPlanWF B Bl (.bindGlobal x g :: ss)
  | copyBinding {B Bl : List Var} {x y : Var} {ss : XPlan} :
      y ∈ B → XPlanWF (x :: B) Bl ss → XPlanWF B Bl (.copyBinding x y :: ss)
  | extractLitVal {B Bl : List Var} {v l : Var} {ss : XPlan} :
      v ∈ B → XPlanWF B (l :: Bl) ss → XPlanWF B Bl (.extractLitVal v l :: ss)
  | checkLit {B Bl : List Var} {v : Var} {c : LVal} {ss : XPlan} :
      v ∈ B → XPlanWF B Bl ss → XPlanWF B Bl (.checkLit v c :: ss)
  | checkPred {B Bl : List Var} {p : PredExpr} {ss : XPlan} :
      (∀ l ∈ p.litVars, l ∈ Bl) → XPlanWF B Bl ss → XPlanWF B Bl (.checkPred p :: ss)
  | collect {B Bl : List Var} {v : Var} {S : SeqSpec} {ss : XPlan} :
      XPlanWF (S.collectBinds ++ B) (S.collectLitBinds ++ Bl) ss →
      XPlanWF B Bl (.collect v S :: ss)

/-- On core plans, `XPlanWF` is `PlanWF`. -/
theorem XPlanWF_of_PlanWF {B : List Var} (Bl : List Var) {ss : Plan} (h : PlanWF B ss) :
    XPlanWF B Bl (ss.map .core) := by
  induction h with
  | nil => exact .nil
  | join hr _ ih =>
      exact .core (fun x hx => by
        simp only [Step.reads, List.mem_flatMap] at hx
        obtain ⟨l, hl, hx⟩ := hx
        exact hr l hl x hx) ih
  | extractChild hv _ ih => exact .core (by simp [Step.reads, hv]) ih
  | checkChildEq hv hx _ ih => exact .core (by simp [Step.reads, hv, hx]) ih
  | checkEq hx hy _ ih => exact .core (by simp [Step.reads, hx, hy]) ih
  | copyBinding ho _ ih => exact .core (by simp [Step.reads, ho]) ih
  | decomposeAC hv _ ih => exact .core (by simp [Step.reads, hv]) ih
  | decomposeACI hv _ ih => exact .core (by simp [Step.reads, hv]) ih
  | expandA hv _ ih => exact .core (by simp [Step.reads, hv]) ih
  | decomposeComm hv _ ih => exact .core (by simp [Step.reads, hv]) ih

theorem PlanWF_of_XPlanWF {B Bl : List Var} : ∀ {ss : Plan},
    XPlanWF B Bl (ss.map .core) → PlanWF B ss
  | [], _ => .nil
  | s :: ss, h => by
      cases h with
      | core hr h' =>
          have ih := PlanWF_of_XPlanWF h'
          cases s with
          | join t ls =>
              exact .join (fun l hl x hx => hr x (by
                simp only [Step.reads, List.mem_flatMap]; exact ⟨l, hl, hx⟩)) ih
          | extractChild v pos out => exact .extractChild (by simpa [Step.reads] using hr) ih
          | checkChildEq v pos x =>
              exact .checkChildEq (by simpa [Step.reads] using hr v) (by simpa [Step.reads] using hr x) ih
          | checkEq x y =>
              exact .checkEq (by simpa [Step.reads] using hr x) (by simpa [Step.reads] using hr y) ih
          | copyBinding t o => exact .copyBinding (by simpa [Step.reads] using hr) ih
          | decomposeAC v elems rest => exact .decomposeAC (by simpa [Step.reads] using hr) ih
          | decomposeACI v elems rest => exact .decomposeACI (by simpa [Step.reads] using hr) ih
          | expandA v pre elems suf => exact .expandA (by simpa [Step.reads] using hr) ih
          | decomposeComm v x y => exact .decomposeComm (by simpa [Step.reads] using hr) ih

/-! ## Literal slots along a run -/

/-- Every literal variable of `Bl` is bound in `σ`. -/
def LitBound (σ : XBinding) (Bl : List Var) : Prop := ∀ l ∈ Bl, (σ.lit l).isSome

/-- The literal slots a step reads. -/
def XStep.litReads : XStep → List Var
  | .checkPred p => p.litVars
  | _ => []

/-- The scalar slots of every match at every node have at least the
layout's scalars (true of the engine's sources: a row of a simple item is
a full scalar vector, `seq_engine.rs:390-425`). -/
def SeqSpec.ScalarsOk (S : SeqSpec) (X : XGraph) (Γ : GVar → C) : Prop :=
  ∀ kids e, e ∈ assemble S (S.src X Γ) kids → S.layout.scalars.length ≤ e.scalars.length

theorem writeRest_lit (σ : XBinding) (rr : RestRef) (es : List C) (ms : List Nat) :
    (writeRest σ rr es ms).lit = σ.lit := by
  cases rr <;> rfl

theorem writeCol_lit (σ : XBinding) (cr : ColRef) (col : List (Option Val)) :
    (writeCol σ cr col).lit = σ.lit := by
  cases cr <;> rfl

theorem foldl_writeCol_lit (ps : List (ColRef × List (Option Val))) (σ : XBinding) :
    (ps.foldl (fun σ p => writeCol σ p.1 p.2) σ).lit = σ.lit := by
  induction ps generalizing σ with
  | nil => rfl
  | cons p ps ih => rw [List.foldl_cons, ih, writeCol_lit]

theorem writeFilter_lit (σ : XBinding) (fl : FilterLayout) (fb : Option FBind) :
    (writeFilter σ fl fb).lit = σ.lit := by
  cases fb with
  | none => rfl
  | some fb => simp only [writeFilter]; rw [foldl_writeCol_lit, writeRest_lit]

theorem foldl_writeFilter_lit (ps : List (FilterLayout × Option FBind)) (σ : XBinding) :
    (ps.foldl (fun σ p => writeFilter σ p.1 p.2) σ).lit = σ.lit := by
  induction ps generalizing σ with
  | nil => rfl
  | cons p ps ih => rw [List.foldl_cons, ih, writeFilter_lit]

theorem writeScalar_lit_isSome (σ : XBinding) (sr : ScalarRef) (w : Option Val) (l : Var)
    (h : (σ.lit l).isSome) : ((writeScalar σ sr w).lit l).isSome := by
  unfold writeScalar
  split
  · exact h
  · rw [lit_setLit]; split <;> simp [h]
  · exact h
  · exact h

theorem foldl_writeScalar_lit_isSome (ps : List (ScalarRef × Option Val)) (σ : XBinding)
    (l : Var) (h : (σ.lit l).isSome) :
    ((ps.foldl (fun σ p => writeScalar σ p.1 p.2) σ).lit l).isSome := by
  induction ps generalizing σ with
  | nil => exact h
  | cons p ps ih => exact ih _ (writeScalar_lit_isSome _ _ _ _ h)

/-- A written literal scalar is bound after the fold. -/
theorem foldl_writeScalar_lit_of_mem (ps : List (ScalarRef × Option Val)) (σ : XBinding)
    (l : Var) (x : Lit) (h : (.lit l, some (.lit x)) ∈ ps) :
    ((ps.foldl (fun σ p => writeScalar σ p.1 p.2) σ).lit l).isSome := by
  induction ps generalizing σ with
  | nil => simp at h
  | cons p ps ih =>
      rw [List.foldl_cons]
      rcases List.mem_cons.1 h with rfl | h
      · apply foldl_writeScalar_lit_isSome
        simp [writeScalar, lit_setLit]
      · exact ih _ h

/-- `fill` keeps every bound literal slot bound (it may overwrite it). -/
theorem writeEnv_lit_isSome (S : SeqSpec) (σ : XBinding) (e : Env) (l : Var)
    (h : (σ.lit l).isSome) : ((writeEnv S σ e).lit l).isSome := by
  unfold writeEnv
  apply foldl_writeScalar_lit_isSome
  have h1 : ((((S.layout.filters.zip e.filt).foldl (fun σ p => writeFilter σ p.1 p.2) σ)).lit l).isSome := by
    rw [foldl_writeFilter_lit]; exact h
  split
  · rw [writeRest_lit]; exact h1
  · exact h1

/-- `fill` binds every literal scalar of the layout, when it succeeds and
the match has the layout's scalars. -/
theorem writeEnv_collectLitBinds (S : SeqSpec) (σ : XBinding) (e : Env)
    (hok : fillOk S e = true) (hlen : S.layout.scalars.length ≤ e.scalars.length) :
    LitBound (writeEnv S σ e) S.collectLitBinds := by
  intro l hl
  simp only [SeqSpec.collectLitBinds, List.mem_filterMap] at hl
  obtain ⟨sr, hsr, hl⟩ := hl
  obtain ⟨v, rfl⟩ : ∃ v, sr = .lit v := by
    cases sr <;> simp_all
  simp at hl; subst hl
  obtain ⟨i, hi, hget⟩ := List.getElem_of_mem hsr
  have hi' : i < (S.layout.scalars.zip e.scalars).length := by
    simp [List.length_zip]; omega
  have hmem : (S.layout.scalars.zip e.scalars)[i] ∈ S.layout.scalars.zip e.scalars :=
    List.getElem_mem hi'
  rw [List.getElem_zip, hget] at hmem
  simp only [fillOk, Bool.and_eq_true, List.all_eq_true] at hok
  have hk := hok.2 _ hmem
  obtain ⟨x, hx⟩ : ∃ x, e.scalars[i] = some (.lit x) := by
    revert hk
    generalize e.scalars[i] = w
    cases w with
    | none => simp
    | some w => cases w <;> simp
  rw [hx] at hmem
  unfold writeEnv
  exact foldl_writeScalar_lit_of_mem _ _ _ x hmem

/-- No step unbinds a literal slot. -/
theorem stepList_lit_isSome {X : XGraph} {Γ : GVar → C} {M : PredModel} {s : XStep}
    {σ σ' : XBinding} (h : σ' ∈ stepList X Γ M s σ) (l : Var) (hl : (σ.lit l).isSome) :
    (σ'.lit l).isSome := by
  cases s with
  | core s => rw [(mem_stepList_core.1 h).2.1]; exact hl
  | checkNeq x y => rw [(checkNeq_sound h).1]; exact hl
  | checkEqGlobal x g => rw [(checkEqGlobal_sound h).1]; exact hl
  | bindGlobal x g => rw [bindGlobal_iff.1 h]; exact hl
  | copyBinding x y => obtain ⟨c, _, rfl⟩ := copyBinding_iff.1 h; exact hl
  | extractLitVal v l' =>
      obtain ⟨id, x, _, _, rfl⟩ := extractLitVal_iff.1 h
      rw [lit_setLit]; split <;> simp [hl]
  | checkLit v c => rw [(checkLit_sound h).1]; exact hl
  | checkPred p => rw [(checkPred_sound h).1]; exact hl
  | collect v S =>
      simp only [stepList] at h
      split at h
      · split at h
        · obtain ⟨e, _, rfl⟩ := List.mem_map.1 h
          exact writeEnv_lit_isSome _ _ _ _ hl
        · simp at h
      · obtain ⟨id, _, h⟩ := List.mem_flatMap.1 h
        split at h
        · obtain ⟨e, _, rfl⟩ := List.mem_map.1 h
          exact writeEnv_lit_isSome _ _ _ _ hl
        · simp at h

/-- A reached `Collect` output: its match passed `fill` (no fault) and has
the layout's scalars. -/
theorem collect_output_litBound {X : XGraph} {Γ : GVar → C} {M : PredModel} {v : Var}
    {S : SeqSpec} {σ σ' : XBinding} (h : σ' ∈ stepList X Γ M (.collect v S) σ)
    (hf : stepFault X Γ M (.collect v S) σ = false) (hS : S.ScalarsOk X Γ) :
    LitBound σ' S.collectLitBinds := by
  simp only [stepList] at h
  split at h
  · rename_i id hid
    split at h
    · rename_i kids hk
      simp only [stepFault, hid, hk] at hf
      obtain ⟨e, he, rfl⟩ := List.mem_map.1 h
      have hok : fillOk S e = true := by
        have := List.any_eq_false.1 hf _ he
        simpa using this
      exact writeEnv_collectLitBinds S _ e hok (hS kids e he)
    · simp at h
  · rename_i hid
    simp only [stepFault, hid] at hf
    obtain ⟨id, hidm, h⟩ := List.mem_flatMap.1 h
    split at h
    · rename_i kids hk
      obtain ⟨e, he, rfl⟩ := List.mem_map.1 h
      have hok : fillOk S e = true := by
        have := List.any_eq_false.1 hf _ hidm
        rw [hk] at this
        rw [Bool.not_eq_true] at this
        simpa using List.any_eq_false.1 this _ he
      exact writeEnv_collectLitBinds S _ e hok (hS kids e he)
    · simp at h

/-- The literal invariant is preserved by every step of a well-formed plan
(given, for `Collect`, no fault and the scalars condition). -/
theorem litBound_step {X : XGraph} {Γ : GVar → C} {M : PredModel} {B Bl : List Var}
    {s : XStep} {ss : XPlan} {σ σ' : XBinding}
    (h : XPlanWF B Bl (s :: ss)) (hσ : LitBound σ Bl) (hs : σ' ∈ stepList X Γ M s σ)
    (hcol : ∀ v S, s = .collect v S →
      stepFault X Γ M (.collect v S) σ = false ∧ S.ScalarsOk X Γ) :
    ∃ B' Bl', XPlanWF B' Bl' ss ∧ LitBound σ' Bl' := by
  have hmono : ∀ Bl', LitBound σ Bl' → LitBound σ' Bl' := fun Bl' hb l hl =>
    stepList_lit_isSome hs l (hb l hl)
  cases h with
  | core _ h' => exact ⟨_, _, h', hmono _ hσ⟩
  | checkNeq _ _ h' => exact ⟨_, _, h', hmono _ hσ⟩
  | checkEqGlobal _ h' => exact ⟨_, _, h', hmono _ hσ⟩
  | bindGlobal h' => exact ⟨_, _, h', hmono _ hσ⟩
  | copyBinding _ h' => exact ⟨_, _, h', hmono _ hσ⟩
  | extractLitVal _ h' =>
      refine ⟨_, _, h', ?_⟩
      obtain ⟨id, x, _, _, rfl⟩ := extractLitVal_iff.1 hs
      intro l' hl'
      rw [lit_setLit]
      split
      · simp
      · rcases List.mem_cons.1 hl' with rfl | hl'
        · simp_all
        · exact hσ l' hl'
  | checkLit _ h' => exact ⟨_, _, h', hmono _ hσ⟩
  | checkPred _ h' => exact ⟨_, _, h', hmono _ hσ⟩
  | collect h' =>
      refine ⟨_, _, h', ?_⟩
      obtain ⟨hf, hS⟩ := hcol _ _ rfl
      intro l hl
      rcases List.mem_append.1 hl with hl | hl
      · exact collect_output_litBound hs hf hS l hl
      · exact hmono _ hσ l hl

/-- A well-formed plan never reads an unbound literal slot: every step
reached along a run from a binding bound on `Bl` finds its literal reads
bound. Hypotheses: `hcol`, every reached `Collect` passes `fill` and its
spec satisfies `ScalarsOk` (both hold of the engine; a `fill` fault aborts
the run anyway). -/
theorem xplan_wf_sound {X : XGraph} {Γ : GVar → C} {M : PredModel} {plan : XPlan}
    {σ τ : XBinding} {s : XStep}
    (hr : Reaches X Γ M plan σ s τ) :
    ∀ {B Bl : List Var}, XPlanWF B Bl plan → LitBound σ Bl →
    (∀ v S τ', Reaches X Γ M plan σ (.collect v S) τ' →
      stepFault X Γ M (.collect v S) τ' = false ∧ S.ScalarsOk X Γ) →
    ∀ l ∈ s.litReads, (τ.lit l).isSome := by
  induction hr with
  | here =>
      intro B Bl h hσ _ l hl
      cases h with
      | checkPred hp _ => exact hσ l (hp l hl)
      | _ => simp [XStep.litReads] at hl
  | @there s₀ t ss σ₀ σ₁ τ hmem _ ih =>
      intro B Bl h hσ hcol
      obtain ⟨B', Bl', h', hσ'⟩ := litBound_step h hσ hmem
        (fun v S hs => hcol v S σ₀ (by subst hs; exact .here))
      exact ih h' hσ' (fun v S τ' hr' => hcol v S τ' (.there hmem hr'))

/-- Corollary: a guard fault of a well-formed plan is a primitive being
undefined, never an unbound slot: every `.val` leaf of a reached
`CheckPred` is bound. -/
theorem xplan_wf_no_unbound_fault {X : XGraph} {Γ : GVar → C} {M : PredModel} {plan : XPlan}
    {σ τ : XBinding} {p : PredExpr} {B Bl : List Var}
    (h : XPlanWF B Bl plan) (hσ : LitBound σ Bl)
    (hcol : ∀ v S τ', Reaches X Γ M plan σ (.collect v S) τ' →
      stepFault X Γ M (.collect v S) τ' = false ∧ S.ScalarsOk X Γ)
    (hr : Reaches X Γ M plan σ (.checkPred p) τ) :
    ∀ l ∈ p.litVars, (τ.lit l).isSome :=
  xplan_wf_sound hr h hσ hcol

end Semper.EMatch.Steps
