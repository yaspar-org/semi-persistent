import SemperProofs.EMatch.Env.Main

/-! Axiom audit for the environment refinement. Expected: only `propext`,
`Classical.choice`, `Quot.sound`. -/

#print axioms Semper.EMatch.Env.env_restore
#print axioms Semper.EMatch.Env.env_refine
#print axioms Semper.EMatch.Env.env_refine_empty
#print axioms Semper.EMatch.Env.comm_pair_duplicate
#print axioms Semper.EMatch.Env.comm_bound_first_counts
#print axioms Semper.EMatch.Env.ac_nodup
#print axioms Semper.EMatch.Env.RoundSnapshot.canon_node
