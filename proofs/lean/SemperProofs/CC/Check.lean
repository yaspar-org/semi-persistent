import SemperProofs.CC.Main
import SemperProofs.CC.EngineSteps

/-! Axiom audit for the AC-congruence-closure development. The only axioms
expected are `propext`, `Classical.choice` and `Quot.sound`. -/

#print axioms SemperProofs.CC.completion_sound
#print axioms SemperProofs.CC.completion_complete_at_convergence
#print axioms SemperProofs.CC.completion_complete_at_convergence_of_join
#print axioms SemperProofs.CC.completion_complete_at_convergence_of_all
#print axioms SemperProofs.CC.E_joinable_RwAx
#print axioms SemperProofs.CC.rhs_normal
#print axioms SemperProofs.CC.RoundFixed.cp_joinable_all
#print axioms SemperProofs.CC.ruleRuleCP_of_fixed
#print axioms SemperProofs.CC.hcp_of_fixed
#print axioms SemperProofs.CC.AxiomCP.of_no_ax
#print axioms SemperProofs.CC.rules_oriented
#print axioms SemperProofs.CC.SlotState.fix_sufficient
#print axioms SemperProofs.CC.SlotState.reachable_I5
#print axioms SemperProofs.CC.SlotState.shrinkNoRefresh_breaks_I5
#print axioms SemperProofs.CC.SlotState.unretire_I5
#print axioms SemperProofs.CC.SlotState.unretireNoRefresh_breaks_I5
#print axioms SemperProofs.CC.unretire_I0
#print axioms SemperProofs.CC.refreshRhs_I0
#print axioms SemperProofs.CC.unretire_refresh_I5
#print axioms SemperProofs.CC.unretire_refresh_reachable
#print axioms SemperProofs.CC.newman
#print axioms SemperProofs.CC.kapur_termination
#print axioms SemperProofs.CC.run_stabilizes
#print axioms SemperProofs.CC.confluent_modulo
#print axioms SemperProofs.CC.Infer_I2
#print axioms SemperProofs.CC.Infer_I4
#print axioms SemperProofs.CC.E_eqs_sound
#print axioms SemperProofs.CC.Infer.joinMerge_of_steps
#print axioms SemperProofs.CC.Infer.cancelMerge
#print axioms SemperProofs.CC.run_stabilizes'
#print axioms SemperProofs.CC.materialize_merge_infer
#print axioms SemperProofs.CC.pair_infer
#print axioms SemperProofs.CC.superpose_infer
#print axioms SemperProofs.CC.axiomPair_infer
#print axioms SemperProofs.CC.cancelClose_infer
#print axioms SemperProofs.CC.inverseRepair_infer
#print axioms SemperProofs.CC.exSt_criticalPair
#print axioms SemperProofs.CC.superpose_example
