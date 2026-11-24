import SemperProofs.EMatch.Steps.Assemble

/-!
# The extended interpreter

`stepList` is the per-step enumeration (the spec's `runStep` clauses, A.1
to A.8, with a fault as "no match"); `stepFault` says when the engine
records a fault instead (A.7: an undefined guard; A.8.3: a `fill` error);
`runXStep` combines them into an `XRes`, and `runX` runs a plan, a fault
anywhere making the run a fault (the driver aborts the run,
`apply.rs:1402-1404`).

The `core` clause runs the core interpreter on the wrapped binding and
leaves the literal fields alone, so every theorem of `EMatch/Main.lean`
lifts through `runXStep_core`.
-/

namespace Semper.EMatch.Steps

open Semper.EMatch

/-- Node bound to a node variable. -/
def XBinding.nodeOf (σ : XBinding) (X : XGraph) (v : Var) : Option Node :=
  σ.base.nodeOf X.G v

/-- One step's bindings (`run_step`, `ematch.rs`). -/
def stepList (X : XGraph) (Γ : GVar → C) (M : PredModel) : XStep → XBinding → List XBinding
  | .core s, σ => (runStep X.G s σ.base).map σ.withBase
  | .checkNeq x y, σ =>
      match σ.base.cls x, σ.base.cls y with
      | some a, some b => if a ≠ b then [σ] else []
      | _, _ => []
  | .checkEqGlobal x g, σ =>
      match σ.base.cls x with
      | some c => if c = Γ g then [σ] else []
      | none => []
  | .bindGlobal x g, σ => [σ.setCls x (Γ g)]
  | .copyBinding x y, σ =>
      match σ.base.cls y with
      | some c => [σ.setCls x c]
      | none => []
  | .extractLitVal v l, σ =>
      match σ.base.node v with
      | some id =>
          match X.litOf id with
          | some x => [σ.setLit l x]
          | none => []
      | none => []
  | .checkLit v c, σ =>
      match σ.base.node v with
      | some id => if (X.litOf id).map X.litVal = some c then [σ] else []
      | none => []
  | .checkPred p, σ =>
      match evalPred X M σ p with
      | some v => if M.truthy v then [σ] else []
      | none => []
  | .collect v S, σ =>
      match σ.base.node v with
      | some id =>
          match (X.G.lookupNode id).bind (fun n => kidsOf n.children) with
          | some kids => (assemble S (S.src X Γ) kids).map (writeEnv S σ)
          | none => []
      | none =>
          (X.G.byOp S.op).flatMap (fun id =>
            match (X.G.lookupNode id).bind (fun n => kidsOf n.children) with
            | some kids => (assemble S (S.src X Γ) kids).map (writeEnv S (σ.setNode v id))
            | none => [])

/-- The matches of a `Collect` step at a bound node (the root drive). -/
theorem stepList_collect_bound (X : XGraph) (Γ : GVar → C) (M : PredModel) (v : Var)
    (S : SeqSpec) (σ : XBinding) (id : NodeId) (n : Node) (kids : List (C × Nat))
    (hv : σ.base.node v = some id) (hn : X.G.lookupNode id = some n)
    (hk : kidsOf n.children = some kids) :
    stepList X Γ M (.collect v S) σ = (assemble S (S.src X Γ) kids).map (writeEnv S σ) := by
  simp [stepList, hv, hn, hk]

/-- Whether the engine records a fault at this step on this binding. -/
def stepFault (X : XGraph) (Γ : GVar → C) (M : PredModel) : XStep → XBinding → Bool
  | .checkPred p, σ => (evalPred X M σ p).isNone
  | .collect v S, σ =>
      match σ.base.node v with
      | some id =>
          match (X.G.lookupNode id).bind (fun n => kidsOf n.children) with
          | some kids => (assemble S (S.src X Γ) kids).any (fun e => !fillOk S e)
          | none => false
      | none =>
          (X.G.byOp S.op).any (fun id =>
            match (X.G.lookupNode id).bind (fun n => kidsOf n.children) with
            | some kids => (assemble S (S.src X Γ) kids).any (fun e => !fillOk S e)
            | none => false)
  | _, _ => false

/-- One step. -/
def runXStep (X : XGraph) (Γ : GVar → C) (M : PredModel) (s : XStep) (σ : XBinding) : XRes :=
  if stepFault X Γ M s σ then .fault else .ok (stepList X Γ M s σ)

/-- Run a continuation on every binding; a fault anywhere is a fault. -/
def XRes.bindAll (bs : List XBinding) (k : XBinding → XRes) : XRes :=
  bs.foldr (fun b acc =>
    match k b, acc with
    | .ok xs, .ok ys => .ok (xs ++ ys)
    | _, _ => .fault) (.ok [])

/-- Depth-first search over the plan, faults propagated. -/
def runX (X : XGraph) (Γ : GVar → C) (M : PredModel) : XPlan → XBinding → XRes
  | [], σ => .ok [σ]
  | s :: ss, σ =>
      match runXStep X Γ M s σ with
      | .fault => .fault
      | .ok bs => XRes.bindAll bs (runX X Γ M ss)

/-- The fault-free semantics: the bindings, faults as "no match". -/
def runXL (X : XGraph) (Γ : GVar → C) (M : PredModel) : XPlan → XBinding → List XBinding
  | [], σ => [σ]
  | s :: ss, σ => (stepList X Γ M s σ).flatMap (runXL X Γ M ss)

/-- `Reaches plan σ s τ`: running `plan` from `σ` reaches step `s` with
binding `τ`. -/
inductive Reaches (X : XGraph) (Γ : GVar → C) (M : PredModel) :
    XPlan → XBinding → XStep → XBinding → Prop
  | here {s : XStep} {ss : XPlan} {σ : XBinding} : Reaches X Γ M (s :: ss) σ s σ
  | there {s t : XStep} {ss : XPlan} {σ σ' τ : XBinding} :
      σ' ∈ stepList X Γ M s σ → Reaches X Γ M ss σ' t τ → Reaches X Γ M (s :: ss) σ t τ

/-- The run is faulty: some reached step faults. -/
def Faulty (X : XGraph) (Γ : GVar → C) (M : PredModel) (plan : XPlan) (σ : XBinding) : Prop :=
  ∃ s τ, Reaches X Γ M plan σ s τ ∧ stepFault X Γ M s τ = true

/-! ## Basic facts -/

/-- A core step is the core interpreter on the wrapped binding; the
literal fields are untouched. -/
theorem runXStep_core (X : XGraph) (Γ : GVar → C) (M : PredModel) (s : Step) (σ : XBinding) :
    runXStep X Γ M (.core s) σ = .ok ((runStep X.G s σ.base).map σ.withBase) := by
  simp [runXStep, stepFault, stepList]

theorem mem_stepList_core {X : XGraph} {Γ : GVar → C} {M : PredModel} {s : Step}
    {σ σ' : XBinding} :
    σ' ∈ stepList X Γ M (.core s) σ ↔
      σ'.base ∈ runStep X.G s σ.base ∧ σ'.lit = σ.lit ∧ σ'.litSeq = σ.litSeq := by
  simp only [stepList, List.mem_map]
  constructor
  · rintro ⟨b, hb, rfl⟩
    exact ⟨hb, rfl, rfl⟩
  · rintro ⟨hb, hl, hls⟩
    refine ⟨σ'.base, hb, ?_⟩
    cases σ'
    simp only [XBinding.withBase] at *
    cases hl; cases hls; rfl

/-- A core plan lifted: the fault-free run is the core run on the wrapped
binding. -/
theorem runXL_core (X : XGraph) (Γ : GVar → C) (M : PredModel) (ss : Plan) (σ : XBinding) :
    runXL X Γ M (ss.map .core) σ = (run X.G ss σ.base).map σ.withBase := by
  induction ss generalizing σ with
  | nil => simp [runXL, run, XBinding.withBase]
  | cons s ss ih =>
      simp only [List.map_cons, runXL, stepList, run, List.flatMap_map, List.map_flatMap]
      congr 1
      funext b
      rw [ih]
      rfl

theorem XRes.bindAll_ok {bs : List XBinding} {k : XBinding → XRes} {f : XBinding → List XBinding}
    (h : ∀ b ∈ bs, k b = .ok (f b)) : XRes.bindAll bs k = .ok (bs.flatMap f) := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
      simp only [XRes.bindAll, List.foldr_cons, List.flatMap_cons]
      rw [h b (List.mem_cons_self), ← XRes.bindAll, ih (fun b hb => h b (List.mem_cons_of_mem _ hb))]

theorem XRes.bindAll_fault {bs : List XBinding} {k : XBinding → XRes} {b : XBinding}
    (hb : b ∈ bs) (h : k b = .fault) : XRes.bindAll bs k = .fault := by
  induction bs with
  | nil => simp at hb
  | cons c cs ih =>
      simp only [XRes.bindAll, List.foldr_cons]
      rw [← XRes.bindAll]
      rcases List.mem_cons.1 hb with rfl | hb'
      · cases hk : XRes.bindAll cs k <;> simp [h, hk]
      · cases hk : k c <;> simp [hk, ih hb']

/-- Fault propagation: a faulty run is a fault. -/
theorem runX_fault {X : XGraph} {Γ : GVar → C} {M : PredModel} {plan : XPlan} {σ : XBinding}
    (h : Faulty X Γ M plan σ) : runX X Γ M plan σ = .fault := by
  obtain ⟨s, τ, hr, hf⟩ := h
  induction hr with
  | here =>
      simp [runX, runXStep, hf]
  | @there s' t ss σ₀ σ₁ τ' hmem _ ih =>
      simp only [runX]
      cases hs : runXStep X Γ M s' σ₀ with
      | fault => rfl
      | ok bs =>
          have : σ₁ ∈ bs := by
            unfold runXStep at hs
            split at hs
            · cases hs
            · cases hs; exact hmem
          exact XRes.bindAll_fault this (ih hf)

/-- The fault-free case: a run without faults emits the fault-free list. -/
theorem runX_eq_ok {X : XGraph} {Γ : GVar → C} {M : PredModel} {plan : XPlan} {σ : XBinding}
    (h : ¬ Faulty X Γ M plan σ) : runX X Γ M plan σ = .ok (runXL X Γ M plan σ) := by
  induction plan generalizing σ with
  | nil => rfl
  | cons s ss ih =>
      have hs : stepFault X Γ M s σ = false := by
        by_contra hc
        exact h ⟨s, σ, .here, by simpa using hc⟩
      simp only [runX, runXStep, hs, Bool.false_eq_true, ↓reduceIte, runXL]
      apply XRes.bindAll_ok
      intro b hb
      apply ih
      rintro ⟨t, τ, hr, hf⟩
      exact h ⟨t, τ, .there hb hr, hf⟩

/-- Membership in the fault-free run of a plan. -/
theorem mem_runXL_cons {X : XGraph} {Γ : GVar → C} {M : PredModel} {s : XStep} {ss : XPlan}
    {σ σ' : XBinding} :
    σ' ∈ runXL X Γ M (s :: ss) σ ↔ ∃ τ ∈ stepList X Γ M s σ, σ' ∈ runXL X Γ M ss τ := by
  simp [runXL]

end Semper.EMatch.Steps
