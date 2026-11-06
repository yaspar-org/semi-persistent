import SemperProofs.CC.ARound

/-! Axiom audit for the A-only inter-reduction model. The only axioms expected
are `propext`, `Classical.choice` and `Quot.sound`. -/

#print axioms SemperProofs.CC.ARound.rewrite_left_sound
#print axioms SemperProofs.CC.ARound.rewrite_right_sound
#print axioms SemperProofs.CC.ARound.rewrite_both_sound
#print axioms SemperProofs.CC.ARound.den_both_eq_foldR
#print axioms SemperProofs.CC.ARound.aRStep_sound_left
#print axioms SemperProofs.CC.ARound.aRStep_sound_right
#print axioms SemperProofs.CC.ARound.aRStep_sound_both
#print axioms SemperProofs.CC.ARound.aRStep_theq
#print axioms SemperProofs.CC.ARound.left_off_spine_unsound
#print axioms SemperProofs.CC.ARound.right_off_spine_unsound
#print axioms SemperProofs.CC.ARound.aRStepAny_unsound_left
#print axioms SemperProofs.CC.ARound.aRStepAny_unsound_right
#print axioms SemperProofs.CC.ARound.aRound_sound
#print axioms SemperProofs.CC.ARound.aRound_reachable_sound
-- orientation, least spelling, choice of occurrence
#print axioms SemperProofs.CC.ARound.isLeastSpelling_exists
#print axioms SemperProofs.CC.ARound.isLeastSpelling_unique
#print axioms SemperProofs.CC.ARound.rule_of_ne_least
#print axioms SemperProofs.CC.ARound.rewriteAt_shortlex
#print axioms SemperProofs.CC.ARound.orientedRewrite_wf
#print axioms SemperProofs.CC.ARound.chooseOffset_sound
#print axioms SemperProofs.CC.ARound.chooseOffset_complete
#print axioms SemperProofs.CC.ARound.chooseOffset_first
#print axioms SemperProofs.CC.ARound.engineRewrite_aRStep
#print axioms SemperProofs.CC.ARound.engineRewrite_complete
#print axioms SemperProofs.CC.ARound.engineRewrite_fold
#print axioms SemperProofs.CC.ARound.firstRule_aRStep
#print axioms SemperProofs.CC.ARound.firstRule_complete
#print axioms SemperProofs.CC.ARound.firstRule_theq
-- hash-consed store and termination
#print axioms SemperProofs.CC.ARound.aRoundH_toA
#print axioms SemperProofs.CC.ARound.aRoundH_sound
#print axioms SemperProofs.CC.ARound.aRoundH_reachable_sound
#print axioms SemperProofs.CC.ARound.aRoundH_potential_lt
#print axioms SemperProofs.CC.ARound.aRoundH_wf
#print axioms SemperProofs.CC.ARound.aRoundH_chain_bound
-- nested same-operator children
#print axioms SemperProofs.CC.ARound.splice_den_left
#print axioms SemperProofs.CC.ARound.splice_den_right
#print axioms SemperProofs.CC.ARound.splice_den_both
#print axioms SemperProofs.CC.ARound.splice_theq
#print axioms SemperProofs.CC.ARound.spliceStar_theq
#print axioms SemperProofs.CC.ARound.aRound_spliced_sound
#print axioms SemperProofs.CC.ARound.spineImpure_no_splice
#print axioms SemperProofs.CC.ARound.aRStep_spineImpure
#print axioms SemperProofs.CC.ARound.splice_off_spine_unsound_left
#print axioms SemperProofs.CC.ARound.splice_off_spine_unsound_right
