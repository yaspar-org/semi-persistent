import SemperProofs.EMatch.Flatten.EngineComplete
import SemperProofs.EMatch.Flatten.Plan
import SemperProofs.EMatch.Flatten.FoldPlan

/-! Axiom audit for the engine-faithful `:flatten` model: the engine's demand
rule, flag and pruning (`EngineRule.lean`), its completeness
(`EngineComplete.lean`) and the flattened plan with several view registers
(`Plan.lean`). Expected: only `propext`, `Classical.choice`, `Quot.sound`. -/

#print axioms Semper.EMatch.Flatten.DemandL.acceptsEB_iff
#print axioms Semper.EMatch.Flatten.DemandL.acceptsE_ac_iff
#print axioms Semper.EMatch.Flatten.DemandL.acceptsE_imp_acceptsLaws
#print axioms Semper.EMatch.Flatten.acceptsE_iff_altsEAccept
#print axioms Semper.EMatch.Flatten.nonInertEng_eq
#print axioms Semper.EMatch.Flatten.nonInertB_imp_mayNonInert
#print axioms Semper.EMatch.Flatten.prune_engine
#print axioms Semper.EMatch.Flatten.demand_engine_complete_ac
#print axioms Semper.EMatch.Flatten.twoClassesL_of_members
#print axioms Semper.EMatch.Flatten.demand_engine_complete_aci
#print axioms Semper.EMatch.Flatten.demand_engine_complete_assoc
#print axioms Semper.EMatch.Flatten.takenOf_takeable
#print axioms Semper.EMatch.Flatten.lowerF_sound
#print axioms Semper.EMatch.Flatten.lowerF_complete
#print axioms Semper.EMatch.Flatten.AtomSatG.mono
#print axioms Semper.EMatch.Flatten.planF_sound
#print axioms Semper.EMatch.Flatten.planF_complete
#print axioms Semper.EMatch.Flatten.flatten_plan_sound
#print axioms Semper.EMatch.Flatten.flatten_plan_complete
#print axioms Semper.EMatch.Flatten.fold_open_off_spine_unsound
#print axioms Semper.EMatch.Flatten.otLeft_sound
#print axioms Semper.EMatch.Flatten.otRight_sound
#print axioms Semper.EMatch.Flatten.enumerateLD_both
#print axioms Semper.EMatch.Flatten.runED_both

namespace Semper.EMatch.Flatten
open Semper.EMatch

/-! A nested flattened atom (`flatten_nested.egg` inside an AC root): `And`
(op 8) is ACI, `Add` (op 7) AC. Classes `p = 1, q = 2, r = 3, K = 4, T = 5,
b = 6, top = 9`; `T ∋ And{p, K}`, `K ∋ And{q, r}`, `top ∋ Add{T, b}`. The
pattern `(Add (And x y ..r) z) :flatten` has two n-ary atoms, so the plan
has two `Flatten` steps (registers 0 and 1). The `And` atom matches on the
views `{p, K}` (no opening: every pair) and `{p, q, r}` (leaf `(K, [q, r])`:
a pair holding `q` or `r`), eight bindings, each with `z = b`. -/
def exNestG : Graph :=
  ⟨[(10, ⟨8, .set {1, 4}⟩), (11, ⟨8, .set {2, 3}⟩), (12, ⟨7, .mset {5, 6}⟩)],
    fun id => if id = 10 then 5 else if id = 11 then 4 else if id = 12 then 9 else id⟩

def exNestC : FCtx := ⟨exNestG, fun _ => true, fun _ => Laws.free⟩

def exNestP : Pat :=
  .ac 7 [(.aci 8 [.var 0, .var 1] (some 3), .exact 1), (.var 2, .exact 1)] none

/- The plan: two `Flatten` steps, registers 0 and 1. -/
#eval (planF (atoms exNestP 100) ∅ 0).filterMap (fun s => match s with
  | .flatten v f _ out _ => some (v, f, out)
  | _ => none)

/- The emitted `(x, y, z)`: eight bindings. -/
#eval (runE exNestC (planF (atoms exNestP 100) ∅ 0) EEnv.empty).map
  (fun env => (env.σ.cls 0, env.σ.cls 1, env.σ.cls 2))

/-! The fold reproducer (`flatten_fold_spine.egg`): `Sub[a, K]`, `K ∋ Sub[b, c]`.
The unrestricted enumerator (the engine before the fix) gives the view
`[a, b, c]`; the left-fold enumerator only `[a, K]`; the right-fold one
both (for a right fold the last child is the spine). -/
#eval (enumerateL exFold Laws.free exFoldRoot).map Prod.fst
#eval (enumerateLD exFold .left Laws.free exFoldRoot).map Prod.fst
#eval (enumerateLD exFold .right Laws.free exFoldRoot).map Prod.fst

end Semper.EMatch.Flatten
