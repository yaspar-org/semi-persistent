import SemperProofs.EMatch.Main

/-! Axiom audit for the e-matching development. Expected: only `propext`,
`Classical.choice`, `Quot.sound`. -/

#print axioms Semper.EMatch.ematch_sound
#print axioms Semper.EMatch.ematch_complete
#print axioms Semper.EMatch.join_complete
#print axioms Semper.EMatch.decompose_ac_complete
#print axioms Semper.EMatch.compile_wf
