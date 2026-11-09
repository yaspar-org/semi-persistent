import SemperProofs.EMatch.Main
import SemperProofs.EMatch.Engine.Main
import SemperProofs.EMatch.Engine.Runtime
import SemperProofs.EMatch.Engine.Choose
import SemperProofs.EMatch.Engine.Matcher
import SemperProofs.EMatch.Engine.Schedule
import SemperProofs.EMatch.Engine.SemiNaive
import SemperProofs.EMatch.Engine.WF
import SemperProofs.EMatch.Engine.ByOp
import SemperProofs.EMatch.Engine.Cursor

/-! Axiom audit for the engine development. Expected: only `propext`,
`Classical.choice`, `Quot.sound`. -/

#print axioms Semper.EMatch.lower_sound_complete
#print axioms Semper.EMatch.plan_matches
#print axioms Semper.EMatch.planOKFrom_matches
#print axioms Semper.EMatch.planOK_wf
#print axioms Semper.EMatch.runND_indep
#print axioms Semper.EMatch.runND_matches
#print axioms Semper.EMatch.runNDA_matches
#print axioms Semper.EMatch.runNDA_eq_runA
#print axioms Semper.EMatch.runNDA_full_iff
#print axioms Semper.EMatch.chooseEngine_mem
#print axioms Semper.EMatch.chooseEngine_unusedScan
#print axioms Semper.EMatch.boundSet_eq
#print axioms Semper.EMatch.runEngine_matches
#print axioms Semper.EMatch.runEngine_naive_matches
#print axioms Semper.EMatch.runEngine_indep
#print axioms Semper.EMatch.runEngine_eq_plan
#print axioms Semper.EMatch.matcherOK_static
#print axioms Semper.EMatch.matcherOK_runtime
#print axioms Semper.EMatch.matcherOK_engine
#print axioms Semper.EMatch.eagerFix_fixed
#print axioms Semper.EMatch.scheduleEngine_schedA
#print axioms Semper.EMatch.scheduleEngine_planOK
#print axioms Semper.EMatch.matcherOK_static_engine
#print axioms Semper.EMatch.scheduleEngine_naive_matches
#print axioms Semper.EMatch.scheduleEngine_eq_runEngine
#print axioms Semper.EMatch.MatcherOK.naive_iff
#print axioms Semper.EMatch.MatcherOK.variant_iff
#print axioms Semper.EMatch.MatcherOK.round_complete
#print axioms Semper.EMatch.modeOk_variant_iff
#print axioms Semper.EMatch.matches_cover_new
#print axioms Semper.EMatch.byOp_demotion
#print axioms Semper.EMatch.byOp_demotion_op
#print axioms Semper.EMatch.variant_partition
#print axioms Semper.EMatch.variants_cover_new
#print axioms Semper.EMatch.variants_disjoint
#print axioms Semper.EMatch.Matches.nodeCls
#print axioms Semper.EMatch.atoms_iff_match
#print axioms Semper.EMatch.atoms_atomsWF
#print axioms Semper.EMatch.engine_plan_sound
#print axioms Semper.EMatch.engine_plan_complete
#print axioms Semper.EMatch.engine_plan_matches
#print axioms Semper.EMatch.runND_eq_plan
#print axioms Semper.EMatch.ematch_sound
#print axioms Semper.EMatch.ematch_complete
#print axioms Semper.EMatch.Cursor.Ops.findLoop_terminates
#print axioms Semper.EMatch.Cursor.Ops.findFirst_terminates
#print axioms Semper.EMatch.Cursor.Ops.advance_terminates
#print axioms Semper.EMatch.Cursor.preFix_cycles
#print axioms Semper.EMatch.Cursor.preFix_diverges
#print axioms Semper.EMatch.Cursor.Ops.drive_eq_enum
#print axioms Semper.EMatch.Cursor.acLaws
#print axioms Semper.EMatch.Cursor.acFrame_eq_decomposeAC
#print axioms Semper.EMatch.Cursor.decomposeAC_nodup
#print axioms Semper.EMatch.Cursor.aciLaws
#print axioms Semper.EMatch.Cursor.aciFrame_eq_decomposeACI
#print axioms Semper.EMatch.Cursor.decomposeACI_nodup
