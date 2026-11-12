import SemperProofs.CC.Reactivate

/-! Axiom audit of the reactivation pass and `I3` at its fixpoint. Expected:
only `propext`, `Classical.choice`, `Quot.sound`. -/

#print axioms SemperProofs.CC.reducible_iff_RwL
#print axioms SemperProofs.CC.reducible_iff_RwAx
#print axioms SemperProofs.CC.reactivate_fixed_iff
#print axioms SemperProofs.CC.reactivateOn_eq
#print axioms SemperProofs.CC.reactivate_reachable
#print axioms SemperProofs.CC.reactivate_I2
#print axioms SemperProofs.CC.reactivate_I4
#print axioms SemperProofs.CC.reactivate_I5
#print axioms SemperProofs.CC.reactivate_idem
#print axioms SemperProofs.CC.I3_of_reducible
#print axioms SemperProofs.CC.I3_of_reactivate_fixed
#print axioms SemperProofs.CC.ReactivateCE.reactivate_fixed_not_I3
#print axioms SemperProofs.CC.RwL_wf
#print axioms SemperProofs.CC.RwL_rtg_sound
#print axioms SemperProofs.CC.RwL_rtg_embed
#print axioms SemperProofs.CC.I3_of_rw
#print axioms SemperProofs.CC.reactivate_retiredCovered
#print axioms SemperProofs.CC.Infer_retiredCovered
#print axioms SemperProofs.CC.reachable_retiredCovered
#print axioms SemperProofs.CC.retiredCovered_of_reachable
#print axioms SemperProofs.CC.node_equal_active_covered
