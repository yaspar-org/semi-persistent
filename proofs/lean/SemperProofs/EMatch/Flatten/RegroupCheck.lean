import SemperProofs.EMatch.Flatten.RegroupNested
import SemperProofs.EMatch.Flatten.RegroupSkip
import SemperProofs.EMatch.Flatten.RegroupBounds
import SemperProofs.EMatch.Flatten.RegroupLaws
import SemperProofs.EMatch.Flatten.FoldRegroup
import SemperProofs.EMatch.Flatten.RegroupOverlapBounds

/-! Axiom audit for regrouped views (`RegroupDefs.lean`, `Regroup.lean`,
`RegroupSound.lean`, `RegroupComplete.lean`, `RegroupFits.lean`, `RegroupChain.lean`,
`RegroupNested.lean`), the engine's regrouping with its skips
(`RegroupSkipDefs.lean`, `RegroupSkip.lean`), the overlap stage under
idempotence (`RegroupOverlapDefs.lean`, `RegroupOverlap.lean`,
`RegroupOverlapBounds.lean`) and the plan theorems over any
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
#print axioms Semper.EMatch.Flatten.regroupRec_shrink
#print axioms Semper.EMatch.Flatten.mem_regroupLevels_iff_reach
#print axioms Semper.EMatch.Flatten.mem_regroupAll_iff_reach
#print axioms Semper.EMatch.Flatten.Cov.accepts
#print axioms Semper.EMatch.Flatten.Cov.acceptsL
#print axioms Semper.EMatch.Flatten.Cov.length
#print axioms Semper.EMatch.Flatten.Cov.derive
#print axioms Semper.EMatch.Flatten.cov_uncond
#print axioms Semper.EMatch.Flatten.cov_of_same
#print axioms Semper.EMatch.Flatten.mem_groupsOfEngine
#print axioms Semper.EMatch.Flatten.addTarget_spec
#print axioms Semper.EMatch.Flatten.fitStep_spec
#print axioms Semper.EMatch.Flatten.regroupView_spec
#print axioms Semper.EMatch.Flatten.next_spec
#print axioms Semper.EMatch.Flatten.step_spec
#print axioms Semper.EMatch.Flatten.run_finished
#print axioms Semper.EMatch.Flatten.init_inv
#print axioms Semper.EMatch.Flatten.regroupSkipG_spec
#print axioms Semper.EMatch.Flatten.regroupSkipG_iff
#print axioms Semper.EMatch.Flatten.regroupSkipG_iffL
#print axioms Semper.EMatch.Flatten.baseGood_baseRecsR
#print axioms Semper.EMatch.Flatten.enumerateRSkip_iff
#print axioms Semper.EMatch.Flatten.enumerateRDSkip_iff
#print axioms Semper.EMatch.Flatten.regroupSkip_spec
#print axioms Semper.EMatch.Flatten.atomSat_regroupSkip_iff
#print axioms Semper.EMatch.Flatten.regroupSkip_plan_sound
#print axioms Semper.EMatch.Flatten.regroupSkip_plan_complete
#print axioms Semper.EMatch.Flatten.regroupSkip_plan_complete_full
#print axioms Semper.EMatch.Flatten.regroupSkip_views_iff
#print axioms Semper.EMatch.Flatten.regroupSkip_match_iff
#print axioms Semper.EMatch.Flatten.regroupSkip_match_complete

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

/- The engine's loop on the same node: the same views and demands. -/
#eval (enumerateRSkip exRegCtx .both Laws.free 2 ⟨7, .mset {1, 2, 3}⟩).map
  (fun wd => (wd.1, wd.2.unconditional, wd.2.alts.map (List.map (fun l => l.1.g))))

/- The nested case of `RegroupNested.lean`: the view `{e, f, G1, G2}` is
reached by regrouping `{a, b}` then `{c, d}` and in the other order; the two
records need the same classes, listed in a different order, so the engine
keeps the first and drops the second by its signature. The full levels hold
six records, the engine's loop five. -/
#eval (regroupAll exNestCtx .both Laws.free 6
  (baseRecsR exNestCtx .both Laws.free exNestRoot)).length
#eval (regroupAllSkip exNestCtx .both Laws.free
  (baseRecsR exNestCtx .both Laws.free exNestRoot)).length

end Semper.EMatch.Flatten

/-! The engine's regrouping bounds (`RegroupBoundsDefs.lean`, `RegroupBounds.lean`). -/

#print axioms Semper.EMatch.Flatten.regroupBounded_cases
#print axioms Semper.EMatch.Flatten.regroupBounded_none_records
#print axioms Semper.EMatch.Flatten.regroupBounded_halt_iff
#print axioms Semper.EMatch.Flatten.regroupBounded_halt_ok
#print axioms Semper.EMatch.Flatten.regroupBounded_truncated_iff
#print axioms Semper.EMatch.Flatten.regroupBounded_exact
#print axioms Semper.EMatch.Flatten.regroupBounded_sub
#print axioms Semper.EMatch.Flatten.regroupBounded_sub_skip
#print axioms Semper.EMatch.Flatten.regroupBounded_reach
#print axioms Semper.EMatch.Flatten.isCand_of_fitsR
#print axioms Semper.EMatch.Flatten.fitsR_nil_of_not_cand
#print axioms Semper.EMatch.Flatten.regroupAllSkipAt_eq
#print axioms Semper.EMatch.Flatten.groupsOfEngineAt_candSupAt
#print axioms Semper.EMatch.Flatten.takeableRCap_down
#print axioms Semper.EMatch.Flatten.takenOf_takeableRCap
#print axioms Semper.EMatch.Flatten.regroupSkipCap_spec
#print axioms Semper.EMatch.Flatten.atomSat_regroupSkipCap_iff
#print axioms Semper.EMatch.Flatten.enumerateRDBounded_le
#print axioms Semper.EMatch.Flatten.enumerateRDBounded_ge
#print axioms Semper.EMatch.Flatten.runEG_le
#print axioms Semper.EMatch.Flatten.runB_fst
#print axioms Semper.EMatch.Flatten.runB_ge
#print axioms Semper.EMatch.Flatten.regroupBounded_plan_sound
#print axioms Semper.EMatch.Flatten.regroupBounded_plan_complete
#print axioms Semper.EMatch.Flatten.regroupBounded_query_exact
#print axioms Semper.EMatch.Flatten.regroupBounded_match_exact
#print axioms Semper.EMatch.Flatten.mem_base_of_reach

namespace Semper.EMatch.Flatten

/-- The nested case of `RegroupNested.lean` under the bounds `B`, every use
list of length one. -/
def exNestBounded (B : Bounds) : BSt :=
  regroupBoundedG B (Ix.nat (fun _ => 1)) exNestCtx .both Laws.free (groupsOfEngine exNestCtx)
    (baseRecsR exNestCtx .both Laws.free exNestRoot)

/- Under the engine's bounds the run does not stop and ends with the loop's
five records: stopped, views counter, work counter, records. -/
#eval let b := exNestBounded Bounds.engine
  (b.halt.isSome, b.views, b.work, b.st.records.length)

/- With a bound of one regrouped record the run is truncated at the second,
and keeps the walk's record and the first regrouped one. -/
#eval let b := exNestBounded ⟨some 1, Option.none, Option.none⟩
  (repr b.halt, b.views, b.st.records.length)

end Semper.EMatch.Flatten

/-! Regrouped views under the operator's laws (`RegroupLaws.lean`): soundness in
models of the laws, the exact chain characterization for any laws, and the
matches the normalization's dropped classes no longer lose, and the
counter-models of the matches chains miss. -/

#print axioms Semper.EMatch.Flatten.denAC_normalizeList
#print axioms Semper.EMatch.Flatten.denACI_normalizeList
#print axioms Semper.EMatch.Flatten.denA_normalizeList
#print axioms Semper.EMatch.Flatten.regroup_step_sound_ac_laws
#print axioms Semper.EMatch.Flatten.regroup_step_sound_aci_laws
#print axioms Semper.EMatch.Flatten.regroup_step_sound_assoc_laws
#print axioms Semper.EMatch.Flatten.regroup_views_sound_ac_laws
#print axioms Semper.EMatch.Flatten.regroup_views_sound_aci_laws
#print axioms Semper.EMatch.Flatten.regroup_views_sound_assoc_laws
#print axioms Semper.EMatch.Flatten.regroupSkip_views_sound_ac_laws
#print axioms Semper.EMatch.Flatten.regroupSkip_views_sound_aci_laws
#print axioms Semper.EMatch.Flatten.regroupSkip_views_sound_assoc_laws
#print axioms Semper.EMatch.Flatten.normalize_free_of_node
#print axioms Semper.EMatch.Flatten.viewOK_normalize
#print axioms Semper.EMatch.Flatten.regroupStepL_mem
#print axioms Semper.EMatch.Flatten.regroupStepL_of_mem
#print axioms Semper.EMatch.Flatten.regroupStepL_iff
#print axioms Semper.EMatch.Flatten.regroupStepL_free_iff
#print axioms Semper.EMatch.Flatten.regroupChainL_iff
#print axioms Semper.EMatch.Flatten.regroup_views_iff_laws
#print axioms Semper.EMatch.Flatten.regroup_match_iff_laws
#print axioms Semper.EMatch.Flatten.regroupSkip_views_iff_laws
#print axioms Semper.EMatch.Flatten.regroupSkip_match_iff_laws
#print axioms Semper.EMatch.Flatten.regroupSkip_match_complete_laws
#print axioms Semper.EMatch.Flatten.regroupSkip_plan_complete_laws
#print axioms Semper.EMatch.Flatten.canDrop_of_gone
#print axioms Semper.EMatch.Flatten.mayNonInert_of_canDrop
#print axioms Semper.EMatch.Flatten.reach_needs_held
#print axioms Semper.EMatch.Flatten.needs_taken_of_all
#print axioms Semper.EMatch.Flatten.fit_of_regroupsTo
#print axioms Semper.EMatch.Flatten.regroup_drop_need_unit
#print axioms Semper.EMatch.Flatten.regroup_drop_need_nilpotent
#print axioms Semper.EMatch.Flatten.regroup_drop_need_inverse
#print axioms Semper.EMatch.Flatten.regroup_drop_need_leaf
#print axioms Semper.EMatch.Flatten.regroup_insert_unit_lost
#print axioms Semper.EMatch.Flatten.regroup_idem_overlap_sound
#print axioms Semper.EMatch.Flatten.regroup_idem_overlap_loop_lost

namespace Semper.EMatch.Flatten

/- `regroup_drop_need_unit`: the engine's views of `add{a, b, c, d}` with
`zero ∋ add{a, b}`: the stored view and `{c, d}`, both unconditional (the
regrouped record needs nothing: the unit `zero`, class 9, is dropped). -/
#eval (enumerateRSkip exUnitCtx .both exUnitLaws 2 exUnitRoot).map
  (fun wd => (wd.1, wd.2.unconditional, wd.2.alts.map (List.map (fun l => l.1.g))))

end Semper.EMatch.Flatten

namespace Semper.EMatch.Flatten

/-! The item-less match of `flatten_regroup_laws_no_item.egg`: `add` (op 7) AC
with identity `zero`, classes `A = 1, B = 2, C = 3, D = 4, zero = 5`,
`zero ∋ add{A, B}` (node 10), `t = add{A, B, C, D}` (node 11, class 6). The
pattern `(add ..r)` has no item; the laws can drop a class, so the engine
regroups, and `{zero, C, D}` normalizes to `{C, D}`, a view needing no class. -/
def exNoItemG : Graph :=
  ⟨[(10, ⟨7, .mset {1, 2}⟩), (11, ⟨7, .mset {1, 2, 3, 4}⟩)],
    fun id => if id = 10 then 5 else if id = 11 then 6 else id⟩

def exNoItemCtx : Ctx := ⟨exNoItemG, 7, .ac, fun _ => true⟩

def exNoItemLaws : Laws := ⟨some 5, none, none⟩

/-- The engine's enumeration of `t` for a decomposition with no item. -/
def exNoItem (laws : Laws) : BOut :=
  enumerateRDBounded Bounds.engine (Ix.nat (fun _ => 1)) (takeableRCap exNoItemCtx Binding.empty [])
    exNoItemCtx .both laws 0 ⟨7, .mset {1, 2, 3, 4}⟩

/- With the identity: the stored view and `{C, D}`, both unconditional; not
truncated, not skipped, no overflow. -/
#eval let o := exNoItem exNoItemLaws
  (o.views.map (fun wd => (wd.1, wd.2.unconditional)), o.truncated, o.skipped, o.ovf)

/- Laws-free, the stored view only: no regrouping can drop a class. -/
#eval (exNoItem Laws.free).views.map Prod.fst

end Semper.EMatch.Flatten

/-! The executable fold enumerator against the spine trees (`FoldEnum.lean`) and
regrouped views of folds (`FoldRegroup.lean`). -/

#print axioms Semper.EMatch.Flatten.rawNodeD_sub_both
#print axioms Semper.EMatch.Flatten.baseRecsR_sub_both
#print axioms Semper.EMatch.Flatten.rawNodeD_left_sound
#print axioms Semper.EMatch.Flatten.rawNodeD_left_complete
#print axioms Semper.EMatch.Flatten.rawNodeD_left_iff
#print axioms Semper.EMatch.Flatten.rawViews_left_iff
#print axioms Semper.EMatch.Flatten.rawNodeD_right_sound
#print axioms Semper.EMatch.Flatten.rawNodeD_right_complete
#print axioms Semper.EMatch.Flatten.rawNodeD_right_iff
#print axioms Semper.EMatch.Flatten.rawViews_right_iff
#print axioms Semper.EMatch.Flatten.enumerateLD_left_iff
#print axioms Semper.EMatch.Flatten.enumerateLD_right_iff
#print axioms Semper.EMatch.Flatten.lfold_splice
#print axioms Semper.EMatch.Flatten.rfold_splice
#print axioms Semper.EMatch.Flatten.otLeft_sound
#print axioms Semper.EMatch.Flatten.otRight_sound
#print axioms Semper.EMatch.Flatten.consistentL_cyclic_satisfiable
#print axioms Semper.EMatch.Flatten.consistentL_cyclic_free_unsat
#print axioms Semper.EMatch.Flatten.baseRecsR_left_lfold
#print axioms Semper.EMatch.Flatten.baseRecsR_right_rfold
#print axioms Semper.EMatch.Flatten.enumerateLD_left_sound
#print axioms Semper.EMatch.Flatten.enumerateLD_right_sound
#print axioms Semper.EMatch.Flatten.regroupsTo_left_sound
#print axioms Semper.EMatch.Flatten.regroupsTo_right_sound
#print axioms Semper.EMatch.Flatten.regroupStep_left_sound
#print axioms Semper.EMatch.Flatten.regroupStep_right_sound
#print axioms Semper.EMatch.Flatten.regroupChain_left_sound
#print axioms Semper.EMatch.Flatten.regroupChain_right_sound
#print axioms Semper.EMatch.Flatten.baseRecsR_views_iff
#print axioms Semper.EMatch.Flatten.baseRecsR_left_views_iff
#print axioms Semper.EMatch.Flatten.baseRecsR_right_views_iff
#print axioms Semper.EMatch.Flatten.reach_lfold_left
#print axioms Semper.EMatch.Flatten.reach_rfold_right
#print axioms Semper.EMatch.Flatten.regroup_views_sound_left
#print axioms Semper.EMatch.Flatten.regroupSkip_views_sound_left
#print axioms Semper.EMatch.Flatten.regroup_views_sound_right
#print axioms Semper.EMatch.Flatten.regroupSkip_views_sound_right
#print axioms Semper.EMatch.Flatten.regroup_chain_left_sound
#print axioms Semper.EMatch.Flatten.regroup_chain_right_sound
#print axioms Semper.EMatch.Flatten.reach_den_assoc_dir
#print axioms Semper.EMatch.Flatten.regroup_views_sound_assoc_laws_dir
#print axioms Semper.EMatch.Flatten.regroupSkip_views_sound_assoc_laws_dir

namespace Semper.EMatch.Flatten

/- The reproducer of `Fold.lean` (`Sub[a, K]`, `K ∋ Sub[b, c]`, a left fold):
the left-fold enumerator keeps `K` (the second position is off the spine),
the unrestricted one also opens it into `[a, b, c]`. -/
#eval (rawNodeD exFold .left (fuelOf exFold.G) exFoldRoot 1 ∅).map Prod.fst
#eval (rawNodeD exFold .both (fuelOf exFold.G) exFoldRoot 1 ∅).map Prod.fst

/- The mirror image `Sub[K, c]` as a right fold keeps `K` too; as a left fold
it opens it into `[b, c, c]`. -/
#eval (rawNodeD exFold .right (fuelOf exFold.G) ⟨7, .seq [4, 3]⟩ 1 ∅).map Prod.fst
#eval (rawNodeD exFold .left (fuelOf exFold.G) ⟨7, .seq [4, 3]⟩ 1 ∅).map Prod.fst

end Semper.EMatch.Flatten
#print axioms Semper.EMatch.Flatten.overlap_step_sound_aci
#print axioms Semper.EMatch.Flatten.overlap_step_sound_aci_laws
#print axioms Semper.EMatch.Flatten.regroupO_views_sound_aci_laws
#print axioms Semper.EMatch.Flatten.regroupSkipO_views_sound_aci_laws
#print axioms Semper.EMatch.Flatten.enumerateRO_eq_of_not_aci
#print axioms Semper.EMatch.Flatten.enumerateRSkipO_eq_of_not_aci
#print axioms Semper.EMatch.Flatten.overlapAll_spec
#print axioms Semper.EMatch.Flatten.regroupSkipO_spec
#print axioms Semper.EMatch.Flatten.regroupSkipO_iff
#print axioms Semper.EMatch.Flatten.enumerateRSkipO_iff
#print axioms Semper.EMatch.Flatten.regroupAllSkipOAt_eq
#print axioms Semper.EMatch.Flatten.prune_regroupO
#print axioms Semper.EMatch.Flatten.regroupO_spec
#print axioms Semper.EMatch.Flatten.regroupSkipO_specE
#print axioms Semper.EMatch.Flatten.atomSat_regroupSkipO_iff
#print axioms Semper.EMatch.Flatten.regroupSkipO_plan_sound
#print axioms Semper.EMatch.Flatten.regroupSkipO_plan_complete
#print axioms Semper.EMatch.Flatten.overlapStepL_iff
#print axioms Semper.EMatch.Flatten.regroupO_views_iff_laws
#print axioms Semper.EMatch.Flatten.regroupO_match_iff_laws
#print axioms Semper.EMatch.Flatten.regroupSkipO_views_iff_laws
#print axioms Semper.EMatch.Flatten.regroupSkipO_match_iff_laws
#print axioms Semper.EMatch.Flatten.regroupSkipO_plan_complete_laws
#print axioms Semper.EMatch.Flatten.regroupChainO_iff_of_not_aci
#print axioms Semper.EMatch.Flatten.regroup_idem_overlap_found
#print axioms Semper.EMatch.Flatten.regroupBoundedO_cases
#print axioms Semper.EMatch.Flatten.regroupBoundedO_halt_iff
#print axioms Semper.EMatch.Flatten.regroupBoundedO_exact
#print axioms Semper.EMatch.Flatten.regroupBoundedO_sub
#print axioms Semper.EMatch.Flatten.regroupBoundedO_reach
#print axioms Semper.EMatch.Flatten.enumerateRDBoundedO_le
#print axioms Semper.EMatch.Flatten.enumerateRDBoundedO_ge
#print axioms Semper.EMatch.Flatten.regroupBoundedO_plan_sound
#print axioms Semper.EMatch.Flatten.regroupBoundedO_plan_complete
#print axioms Semper.EMatch.Flatten.regroupBoundedO_query_exact
#print axioms Semper.EMatch.Flatten.regroupBoundedO_match_exact
