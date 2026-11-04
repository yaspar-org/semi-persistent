import SemperProofs.EMatch.Main
import SemperProofs.EMatch.Engine.Main
import SemperProofs.EMatch.Engine.Runtime
import SemperProofs.EMatch.Engine.SemiNaive
import SemperProofs.EMatch.Engine.WF
import SemperProofs.EMatch.Engine.ByOp

/-! Axiom audit for the engine development. Expected: only `propext`,
`Classical.choice`, `Quot.sound`. -/

#print axioms Semper.EMatch.lower_sound_complete
#print axioms Semper.EMatch.plan_matches
#print axioms Semper.EMatch.planOKFrom_matches
#print axioms Semper.EMatch.planOK_wf
#print axioms Semper.EMatch.runND_indep
#print axioms Semper.EMatch.runND_matches
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
