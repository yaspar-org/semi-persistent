import SemperProofs.CC.Laws.Main
import SemperProofs.CC.Laws.AxiomCP

/-! Axiom audit for the concrete law sets. Expected: `propext`,
`Classical.choice`, `Quot.sound` only. -/

#print axioms SemperProofs.CC.NFLaw.toLaws_hlaw
#print axioms SemperProofs.CC.NFLaw.toLaws_hnf_ax
#print axioms SemperProofs.CC.NFLaw.hcp_of_gen
#print axioms SemperProofs.CC.NFLaw.E_iff
#print axioms SemperProofs.CC.identity_hlaw
#print axioms SemperProofs.CC.identity_hnf_ax
#print axioms SemperProofs.CC.nilpotent_hlaw
#print axioms SemperProofs.CC.nilpotent_hnf_ax
#print axioms SemperProofs.CC.idempotent_hlaw
#print axioms SemperProofs.CC.idempotent_hnf_ax
#print axioms SemperProofs.CC.idempotent_clamp_eq_dedup
#print axioms SemperProofs.CC.inverse_hlaw
#print axioms SemperProofs.CC.inverse_hnf_ax
#print axioms SemperProofs.CC.invNormal_invWalk
#print axioms SemperProofs.CC.invGen_cp_not_joinable
#print axioms SemperProofs.CC.combined_hlaw
#print axioms SemperProofs.CC.combined_hnf_ax
#print axioms SemperProofs.CC.combined_counterexample
#print axioms SemperProofs.CC.identityInverse_hlaw
#print axioms SemperProofs.CC.identityInverse_hnf_ax
#print axioms SemperProofs.CC.rtg_restrict
#print axioms SemperProofs.CC.idempotentIdentity_hlaw
#print axioms SemperProofs.CC.idempotentIdentity_hnf_ax
#print axioms SemperProofs.CC.count_idempotentIdentity_clamp
#print axioms SemperProofs.CC.hcp_identity
#print axioms SemperProofs.CC.hcp_nilpotent
#print axioms SemperProofs.CC.hcp_idempotent
#print axioms SemperProofs.CC.hcp_inverse
#print axioms SemperProofs.CC.hcp_combined
#print axioms SemperProofs.CC.hcp_identityInverse
#print axioms SemperProofs.CC.hcp_idempotentIdentity
#print axioms SemperProofs.CC.completion_complete_identity
#print axioms SemperProofs.CC.completion_complete_nilpotent
#print axioms SemperProofs.CC.completion_complete_idempotent
#print axioms SemperProofs.CC.completion_complete_inverse
#print axioms SemperProofs.CC.completion_complete_combined
#print axioms SemperProofs.CC.completion_complete_identityInverse
#print axioms SemperProofs.CC.completion_complete_idempotentIdentity
#print axioms SemperProofs.CC.AxiomCP.of_hcp
#print axioms SemperProofs.CC.LawSpec.hlaw
#print axioms SemperProofs.CC.LawSpec.hnf_ax
#print axioms SemperProofs.CC.LawSpec.hcp
#print axioms SemperProofs.CC.axiomCP_of_laws
#print axioms SemperProofs.CC.LawSpec.conds_inverse_of_fixed
#print axioms SemperProofs.CC.LawSpec.conds_combined_of_fixed
#print axioms SemperProofs.CC.LawSpec.conds_identityInverse_of_fixed
