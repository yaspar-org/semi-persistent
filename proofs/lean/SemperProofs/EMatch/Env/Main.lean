import SemperProofs.EMatch.Env.Refine
import SemperProofs.EMatch.Env.Dup
import SemperProofs.EMatch.Env.Snapshot

/-!
# The engine's environment with undo refines the reference interpreter

Final theorems of `SemperProofs.EMatch.Env` (spec `spec-steps-env.md`,
sections B, C, D), re-exported from:

* `Model.lean`: `Env` (the engine's `Match`), `abs`, `EnvOk`, `WF`,
  `Graph.ChildrenCanon`, `Graph.FindIdem`;
* `Exec.lean`: `exec`, the CPS `run_step` over `Env`;
* `Refine.lean`: `exec_spec`, `restore`, `refine`;
* `Dup.lean`: the commutative-pair duplicate and `decomposeAC_nodup`;
* `Snapshot.lean`: `RoundSnapshot`.
-/

namespace Semper.EMatch.Env

open Semper.EMatch

/-- **(Restore)** (spec B.2). For a `WF` plan and an entry environment
bounded by its bound set, `run_step` returns the environment it was given,
on `nodes`, `mults` and the three rest pools and spans. Out of scope, as
the spec lists: `lit_vals` (`ExtractLitVal`) and the `mults` written by
`Collect`'s `fill`. -/
theorem env_restore (G : Graph) (κ : Var → Bool) (hG : G.ChildrenCanon) (hidem : G.FindIdem)
    {B : List Var} {plan : Plan} (hwf : WF κ B plan) (e : Env) (he : EnvOk e B) :
    (exec G κ plan e).2 = e :=
  restore G κ hG hidem hwf e he

/-- **Refinement** (spec B.4). The environments the recursive engine emits
from `e` are, as a set, the bindings of the reference interpreter from
`abs G κ e`. Hypotheses: H2 (`ChildrenCanon`), `find` idempotent, `WF`
plan (`PlanWF` plus the write-once and classification conditions, see
`WF`), entry environment bounded by the plan's bound set. -/
theorem env_refine (G : Graph) (κ : Var → Bool) (hG : G.ChildrenCanon) (hidem : G.FindIdem)
    {B : List Var} {plan : Plan} (hwf : WF κ B plan) (e : Env) (he : EnvOk e B) (σ : Binding) :
    σ ∈ (exec G κ plan e).1 ↔ σ ∈ run G plan (abs G κ e) :=
  refine G κ hG hidem hwf e he σ

/-- The refinement from `Match::new`. -/
theorem env_refine_empty (G : Graph) (κ : Var → Bool) (hG : G.ChildrenCanon)
    (hidem : G.FindIdem) {plan : Plan} (hwf : WF κ [] plan) (σ : Binding) :
    σ ∈ (exec G κ plan Env.empty).1 ↔ σ ∈ run G plan Binding.empty :=
  refine_empty G κ hG hidem hwf σ

/-- `WF` is a strengthening of `PlanWF`. -/
theorem env_wf_planWF {κ : Var → Bool} {B : List Var} {plan : Plan} (h : WF κ B plan) :
    PlanWF B plan :=
  h.toPlanWF

/-- Spec C.1: a commutative pattern on `Eq(a, a)` with both variables
unbound yields the same binding twice, in the reference and in the engine
(`comm_pair_duplicate_run`, `comm_pair_duplicate_exec` on `pairGraph`,
`pairPlan`). So completeness is "at least once". -/
theorem comm_pair_duplicate :
    (∃ σ, run pairGraph pairPlan Binding.empty = [σ, σ] ∧
      σ.cls 1 = some 1 ∧ σ.cls 2 = some 1) ∧
    (∃ σ, (exec pairGraph pairκ pairPlan Env.empty).1 = [σ, σ] ∧
      σ.cls 1 = some 1 ∧ σ.cls 2 = some 1) :=
  ⟨comm_pair_duplicate_run, comm_pair_duplicate_exec⟩

/-- Finding: with the pair's first element already bound and `a = b`, the
reference emits the binding twice and the engine once; `env_refine` is a
set equality for this reason. -/
theorem comm_bound_first_counts :
    (run pairGraph pairPlanBound Binding.empty).length = 2 ∧
    (exec pairGraph pairκ pairPlanBound Env.empty).1.length = 1 :=
  ⟨comm_bound_first_run, comm_bound_first_exec⟩

/-- Spec C.2: on a residual with distinct classes (H2; `Multiset.entries`
always is), the AC decomposition emits no binding twice. -/
theorem ac_nodup (elems : List (Var × Mult)) (rest : Option Var) (m : Multiset C) (σ : Binding) :
    (decomposeAC elems rest (Multiset.entries m) σ).Nodup :=
  decomposeAC_nodup elems rest _ σ (entries_fst_nodup m)

end Semper.EMatch.Env
