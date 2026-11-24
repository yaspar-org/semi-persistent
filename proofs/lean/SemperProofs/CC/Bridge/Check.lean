import SemperProofs.CC.Bridge.Modulo

/-! Axiom audit for the bridge. Expected: only `propext`, `Classical.choice`,
`Quot.sound`. -/

#print axioms SemperProofs.CC.Bridge.represents_keysNodup
#print axioms SemperProofs.CC.Bridge.represents_conforms
#print axioms SemperProofs.CC.Bridge.represents_childrenCanon
#print axioms SemperProofs.CC.Bridge.represents_findIdem
#print axioms SemperProofs.CC.Bridge.ac_equal_same_class
#print axioms SemperProofs.CC.Bridge.ac_equal_same_class_graph
#print axioms SemperProofs.CC.Bridge.matches_closed_under_theory
#print axioms SemperProofs.CC.Bridge.classMatches_congr
#print axioms SemperProofs.CC.Bridge.eterm_matches
#print axioms SemperProofs.CC.Bridge.per_node_form_fails
#print axioms SemperProofs.CC.Bridge.engine_match_modulo_complete
#print axioms SemperProofs.CC.Bridge.engine_match_modulo_sound
