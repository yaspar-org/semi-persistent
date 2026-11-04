import SemperProofs.EMatch.Steps.Main

/-! Axiom audit for the remaining plan steps. Expected: only `propext`,
`Classical.choice`, `Quot.sound`. -/

#print axioms Semper.EMatch.Steps.core_lifts
#print axioms Semper.EMatch.Steps.run_fault_propagates
#print axioms Semper.EMatch.Steps.run_fault_free
#print axioms Semper.EMatch.Steps.step_sound
#print axioms Semper.EMatch.Steps.step_complete
#print axioms Semper.EMatch.Steps.check_pred_fault
#print axioms Semper.EMatch.Steps.lit_pattern
#print axioms Semper.EMatch.Steps.litBind_pattern
#print axioms Semper.EMatch.Steps.xplan_wf_core
#print axioms Semper.EMatch.Steps.xplan_wf_sound'
#print axioms Semper.EMatch.Steps.collect_sound'
#print axioms Semper.EMatch.Steps.collect_complete'
#print axioms Semper.EMatch.Steps.collect_nodup
#print axioms Semper.EMatch.Steps.collect_step'
#print axioms Semper.EMatch.Steps.AParse.spans_chain
#print axioms Semper.EMatch.Steps.admit_spec
