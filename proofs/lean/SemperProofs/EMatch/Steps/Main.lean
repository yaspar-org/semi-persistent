import SemperProofs.EMatch.Steps.Simple
import SemperProofs.EMatch.Steps.WF
import SemperProofs.EMatch.Steps.Collect

/-!
# Remaining plan steps: final theorems

Re-exports, under the names of section A of `spec-steps-env.md`, the
theorems of `Steps/{Interp,Simple,WF,Collect}.lean`. Each is a one-line
application; the statements are the proved (corrected) ones. See
`steps-lean-status.md` for the hypotheses in prose.
-/

namespace Semper.EMatch.Steps

open Semper.EMatch

/-! ## The interpreter -/

/-- A core step runs the core interpreter on the wrapped binding: every
theorem of `EMatch/Main.lean` lifts. -/
theorem core_lifts (X : XGraph) (Γ : GVar → C) (M : PredModel) (ss : Plan) (σ : XBinding) :
    runXL X Γ M (ss.map .core) σ = (run X.G ss σ.base).map σ.withBase :=
  runXL_core X Γ M ss σ

/-- Fault propagation: a reached faulting step makes the run a fault. -/
theorem run_fault_propagates {X : XGraph} {Γ : GVar → C} {M : PredModel} {plan : XPlan}
    {σ : XBinding} (h : Faulty X Γ M plan σ) : runX X Γ M plan σ = .fault :=
  runX_fault h

/-- The fault-free case: the run emits the fault-free list. -/
theorem run_fault_free {X : XGraph} {Γ : GVar → C} {M : PredModel} {plan : XPlan}
    {σ : XBinding} (h : ¬ Faulty X Γ M plan σ) :
    runX X Γ M plan σ = .ok (runXL X Γ M plan σ) :=
  runX_eq_ok h

/-! ## The simple steps (A.1 to A.7) -/

/-- The lowering table is sound: a lowered atom's step emits only
extensions satisfying the atom. Hypotheses: the variable a bind-mode step
writes is unbound (`hfresh`), the literal slot `ExtractLitVal` writes is
unbound (`hfreshLit`: the engine overwrites it with no undo). -/
theorem step_sound {X : XGraph} {Γ : GVar → C} {M : PredModel} {B Bl : List Var} {a : Atom}
    {s : XStep} {σ σ' : XBinding}
    (hl : lower B Bl a = some s)
    (hfresh : ∀ x, s.bindTarget = some x → σ.base.cls x = none)
    (hfreshLit : ∀ l, s.litTarget = some l → σ.lit l = none)
    (h : σ' ∈ stepList X Γ M s σ) :
    XBinding.Extends σ σ' ∧ Atom.Holds X Γ M a σ' :=
  lower_sound hl hfresh hfreshLit h

/-- The lowering table is complete: every extension satisfying the atom is
reached by the lowered step. Hypotheses: the bound sets are bound in `σ`
(`hB`, `hBl`), the node variables a literal atom reads are bound (`hN`). -/
theorem step_complete {X : XGraph} {Γ : GVar → C} {M : PredModel} {B Bl : List Var}
    {a : Atom} {s : XStep} {σ σ' : XBinding}
    (hl : lower B Bl a = some s)
    (hB : ∀ x ∈ B, (σ.base.cls x).isSome) (hBl : ∀ l ∈ Bl, (σ.lit l).isSome)
    (hN : ∀ v ∈ a.nodeReads, (σ.base.node v).isSome)
    (hext : XBinding.Extends σ σ') (h : Atom.Holds X Γ M a σ') :
    ∃ σ'' ∈ stepList X Γ M s σ, XBinding.Extends σ'' σ' :=
  lower_complete hl hB hBl hN hext h

/-- `CheckPred` faults exactly when the guard is undefined. -/
theorem check_pred_fault {X : XGraph} {Γ : GVar → C} {M : PredModel} {p : PredExpr}
    {σ : XBinding} :
    stepFault X Γ M (.checkPred p) σ = true ↔ evalPred X M σ p = none :=
  checkPred_fault

/-- The literal pattern `Pat.lit f c` (A.6): a join on `f` then `CheckLit`
matches exactly the literal nodes of head `f` with value `c`. -/
theorem lit_pattern {X : XGraph} {Γ : GVar → C} {M : PredModel} {v : Var} {f : Sym}
    {c : LVal} {σ σ' : XBinding} :
    σ' ∈ runXL X Γ M [.core (.join v [.byOp f]), .checkLit v c] σ ↔
      ∃ id n, σ' = σ.joinBind X v id ∧ (id, n) ∈ X.G.nodes ∧ n.op = f ∧
        (X.litOf id).map X.litVal = some c :=
  lit_pattern_iff

/-- The literal-binding pattern `Pat.litBind f l` (A.5). -/
theorem litBind_pattern {X : XGraph} {Γ : GVar → C} {M : PredModel} {v l : Var} {f : Sym}
    {σ σ' : XBinding} :
    σ' ∈ runXL X Γ M [.core (.join v [.byOp f]), .extractLitVal v l] σ ↔
      ∃ id n x, σ' = (σ.joinBind X v id).setLit l x ∧ (id, n) ∈ X.G.nodes ∧ n.op = f ∧
        X.litOf id = some x :=
  litBind_pattern_iff

/-! ## Plan well-formedness -/

/-- A core plan is well-formed iff it is well-formed for `PlanWF`. -/
theorem xplan_wf_core {B Bl : List Var} {ss : Plan} :
    XPlanWF B Bl (ss.map .core) ↔ PlanWF B ss :=
  ⟨PlanWF_of_XPlanWF, XPlanWF_of_PlanWF Bl⟩

/-- A well-formed plan never reads an unbound literal variable: at every
reached step, the literal slots it reads are bound. Hypotheses: the
initial binding binds `Bl`; every reached `Collect` writes its matches
without a `fill` fault and with full scalar rows (`ScalarsOk`, true of the
engine's row sources). -/
theorem xplan_wf_sound' {X : XGraph} {Γ : GVar → C} {M : PredModel} {plan : XPlan}
    {σ τ : XBinding} {s : XStep} {B Bl : List Var}
    (h : XPlanWF B Bl plan) (hσ : LitBound σ Bl)
    (hcol : ∀ v S τ', Reaches X Γ M plan σ (.collect v S) τ' →
      stepFault X Γ M (.collect v S) τ' = false ∧ S.ScalarsOk X Γ)
    (hr : Reaches X Γ M plan σ s τ) :
    ∀ l ∈ s.litReads, (τ.lit l).isSome :=
  xplan_wf_sound hr h hσ hcol

/-! ## `Collect` (A.8) -/

/-- Soundness of the sequence assembler: every environment it emits at a
node is a match of the relation `SeqMatch`. -/
theorem collect_sound' (S : SeqSpec) (src : Source) (kids : List (C × Nat)) (env : Env)
    (h : env ∈ assemble S src kids) : SeqMatch S src kids env :=
  collect_sound S src kids env h

/-- Completeness of the sequence assembler: at a node under the
`MAX_MATCHES` bound every match is emitted. -/
theorem collect_complete' (S : SeqSpec) (src : Source) (kids : List (C × Nat)) (env : Env)
    (hbound : (rawMatches S src kids).length ≤ MAX_MATCHES)
    (h : SeqMatch S src kids env) : env ∈ assemble S src kids :=
  collect_complete S src kids env hbound h

/-- A node's matches are a set. -/
theorem collect_nodup (S : SeqSpec) (src : Source) (kids : List (C × Nat)) :
    (assemble S src kids).Nodup :=
  assemble_nodup S src kids

/-- The `Collect` step at a bound node (root drive): its bindings are
exactly the matches, written in the rule's layout. -/
theorem collect_step' (X : XGraph) (Γ : GVar → C) (M : PredModel) (v : Var) (S : SeqSpec)
    (σ σ' : XBinding) (id : NodeId) (n : Node) (kids : List (C × Nat))
    (hv : σ.base.node v = some id) (hn : X.G.lookupNode id = some n)
    (hk : kidsOf n.children = some kids)
    (hbound : (rawMatches S (S.src X Γ) kids).length ≤ MAX_MATCHES) :
    σ' ∈ stepList X Γ M (.collect v S) σ ↔
      ∃ env, SeqMatch S (S.src X Γ) kids env ∧ σ' = writeEnv S σ env :=
  collect_step X Γ M v S σ σ' id n kids hv hn hk hbound

end Semper.EMatch.Steps
