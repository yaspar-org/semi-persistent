import SemperProofs.CC.AtomsWitness
import SemperProofs.CC.AtomsEngine

/-! Axiom audit for leaf constants (`Atoms.lean`, `AtomsEngine.lean`,
`AtomsWitness.lean`). Expected: only `propext`, `Classical.choice`,
`Quot.sound`. -/

#print axioms SemperProofs.CC.roundFixedA_iff
#print axioms SemperProofs.CC.RoundFixedA.materialized
#print axioms SemperProofs.CC.RoundFixedA.congr
#print axioms SemperProofs.CC.completion_complete_atoms
#print axioms SemperProofs.CC.CompleteAtoms.same_class
#print axioms SemperProofs.CC.CompleteAtoms.atom_class
#print axioms SemperProofs.CC.CompleteAtoms.atoms
#print axioms SemperProofs.CC.CompleteAtoms.unit_class
#print axioms SemperProofs.CC.CompleteAtoms.materialized
#print axioms SemperProofs.CC.I3_withAtoms
#print axioms SemperProofs.CC.invNodes_withAtoms
#print axioms SemperProofs.CC.completion_complete_cancellative_engine_atoms
#print axioms SemperProofs.CC.completion_complete_inverse_engine_atoms
#print axioms SemperProofs.CC.completion_complete_combined_engine_atoms
#print axioms SemperProofs.CC.AtomsWitness.witness_fixed
#print axioms SemperProofs.CC.AtomsWitness.witness_complete
#print axioms SemperProofs.CC.AtomsWitness.witness_not_all
