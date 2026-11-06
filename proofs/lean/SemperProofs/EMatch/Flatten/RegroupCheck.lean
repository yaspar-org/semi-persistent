import SemperProofs.EMatch.Flatten.RegroupNested

/-! Axiom audit for regrouped views (`RegroupDefs.lean`, `Regroup.lean`,
`RegroupSound.lean`, `RegroupComplete.lean`, `RegroupFits.lean`, `RegroupChain.lean`,
`RegroupNested.lean`) and the plan theorems over any
enumeration (`Plan.lean`). Expected: only `propext`, `Classical.choice`,
`Quot.sound`. -/

#print axioms Semper.EMatch.Flatten.Enumerator.base_spec
#print axioms Semper.EMatch.Flatten.flatten_plan_sound_of_spec
#print axioms Semper.EMatch.Flatten.flatten_plan_complete_of_spec
#print axioms Semper.EMatch.Flatten.needLeaf_okE
#print axioms Semper.EMatch.Flatten.needLeaf_okL
#print axioms Semper.EMatch.Flatten.mem_dedupH
#print axioms Semper.EMatch.Flatten.regroupLevelsCapped_eq
#print axioms Semper.EMatch.Flatten.mem_regroupLevels_iff
#print axioms Semper.EMatch.Flatten.mem_withinLimit
#print axioms Semper.EMatch.Flatten.acceptsE_enumerateFromR
#print axioms Semper.EMatch.Flatten.takeableR_down
#print axioms Semper.EMatch.Flatten.takenOf_takeableR
#print axioms Semper.EMatch.Flatten.keepRec_of_accept
#print axioms Semper.EMatch.Flatten.prune_regroup
#print axioms Semper.EMatch.Flatten.regroup_spec
#print axioms Semper.EMatch.Flatten.regroup_plan_sound
#print axioms Semper.EMatch.Flatten.regroup_plan_complete
#print axioms Semper.EMatch.Flatten.subEntries_spec
#print axioms Semper.EMatch.Flatten.regroup_step_sound_ac
#print axioms Semper.EMatch.Flatten.regroup_step_sound_aci
#print axioms Semper.EMatch.Flatten.regroup_step_sound_assoc
#print axioms Semper.EMatch.Flatten.regroup_views_sound_ac
#print axioms Semper.EMatch.Flatten.regroup_views_sound_aci
#print axioms Semper.EMatch.Flatten.regroup_views_sound_assoc
#print axioms Semper.EMatch.Flatten.regroup_step_sound_left
#print axioms Semper.EMatch.Flatten.regroup_step_sound_right
#print axioms Semper.EMatch.Flatten.regroup_off_spine_unsound
#print axioms Semper.EMatch.Flatten.fitsR_ac_complete
#print axioms Semper.EMatch.Flatten.regroup_chain_ac
#print axioms Semper.EMatch.Flatten.regroup_view_complete_ac
#print axioms Semper.EMatch.Flatten.regroup_match_complete_ac
#print axioms Semper.EMatch.Flatten.fitsR_aci_complete
#print axioms Semper.EMatch.Flatten.fitsR_assoc_complete
#print axioms Semper.EMatch.Flatten.fitsR_left_complete
#print axioms Semper.EMatch.Flatten.fitsR_right_complete
#print axioms Semper.EMatch.Flatten.viewOK_base
#print axioms Semper.EMatch.Flatten.kept_mem_baseRecsR
#print axioms Semper.EMatch.Flatten.regroupsTo_left_iff
#print axioms Semper.EMatch.Flatten.regroupsTo_right_iff
#print axioms Semper.EMatch.Flatten.regroupStep_ac
#print axioms Semper.EMatch.Flatten.regroupStep_aci
#print axioms Semper.EMatch.Flatten.regroupStep_assoc
#print axioms Semper.EMatch.Flatten.regroupStep_mem
#print axioms Semper.EMatch.Flatten.regroupChain_mem_levels
#print axioms Semper.EMatch.Flatten.regroup_view_complete
#print axioms Semper.EMatch.Flatten.regroup_match_complete
#print axioms Semper.EMatch.Flatten.fitsR_ms
#print axioms Semper.EMatch.Flatten.regroupsTo_of_fitsR
#print axioms Semper.EMatch.Flatten.regroupStep_of_mem
#print axioms Semper.EMatch.Flatten.regroupChain_of_mem_levels
#print axioms Semper.EMatch.Flatten.regroup_views_iff
#print axioms Semper.EMatch.Flatten.regroup_match_iff
#print axioms Semper.EMatch.Flatten.regroupStep_ac_of
#print axioms Semper.EMatch.Flatten.regroup_nested_matches
#print axioms Semper.EMatch.Flatten.regroup_fold_nested

namespace Semper.EMatch.Flatten
open Semper.EMatch

/-! The motivating case (`flatten_regroup_ac.egg`): `Add` (op 7) AC, classes
`a = 1, b = 2, c = 3`, `G = 4 ∋ Add{a, b}` (node 10), the root
`Add{a, b, c}` (node 11, class 5). The walk gives the stored view only; the
regrouped view `{c, G}` needs `G` taken. -/
def exRegG : Graph :=
  ⟨[(10, ⟨7, .mset {1, 2}⟩), (11, ⟨7, .mset {1, 2, 3}⟩)],
    fun id => if id = 10 then 4 else if id = 11 then 5 else id⟩

def exRegCtx : Ctx := ⟨exRegG, 7, .ac, fun _ => true⟩

/- The views with their demand: `{a, b, c}` unconditional, `{c, G}` needing `G`. -/
#eval (enumerateR exRegCtx .both Laws.free 2 ⟨7, .mset {1, 2, 3}⟩).map
  (fun wd => (wd.1, wd.2.unconditional, wd.2.alts.map (List.map (fun l => l.1.g))))

/- One item: `(Add x ..r)` may take `G` (limit 1); no item: no regrouping. -/
#eval (enumerateR exRegCtx .both Laws.free 0 ⟨7, .mset {1, 2, 3}⟩).map Prod.fst

end Semper.EMatch.Flatten
