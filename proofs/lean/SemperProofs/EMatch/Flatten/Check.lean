import SemperProofs.EMatch.Flatten.Main

/-! Axiom audit for the `:flatten` development. Expected: only `propext`,
`Classical.choice`, `Quot.sound`. -/

#print axioms Semper.EMatch.Flatten.views_sound
#print axioms Semper.EMatch.Flatten.views_complete
#print axioms Semper.EMatch.Flatten.prune_irrelevant
#print axioms Semper.EMatch.Flatten.flatten_match_sound_ac
#print axioms Semper.EMatch.Flatten.flatten_match_complete_ac
#print axioms Semper.EMatch.Flatten.flatten_match_sound_aci
#print axioms Semper.EMatch.Flatten.flatten_match_complete_aci
#print axioms Semper.EMatch.Flatten.flatten_match_sound_assoc
#print axioms Semper.EMatch.Flatten.flatten_match_complete_assoc
#print axioms Semper.EMatch.Flatten.demand_refold_ac
#print axioms Semper.EMatch.Flatten.demand_refold_aci
#print axioms Semper.EMatch.Flatten.refold_assoc_pre
#print axioms Semper.EMatch.Flatten.refold_assoc_suf

namespace Semper.EMatch.Flatten
open Semper.EMatch

/-! Spec §2.4 example D: `Plus` AC, class 1 ∋ node 0 = `Plus{a, 1}` with
`a = 2`. Expected views: `{a, C}` (unconditional) and `{a:2, C}` with the
single alternative `[[a, C]]`. -/
def exD : Ctx :=
  ⟨⟨[(0, ⟨7, .mset {2, 1}⟩)], fun _ => 1⟩, 7, .ac, fun _ => true⟩

#eval (enumerate exD Laws.free ⟨7, .mset {2, 1}⟩).map
  (fun wd => (wd.1, wd.2.unconditional, wd.2.alts))

/-! Spec §2.4 example B: `Add` AC (op 9). Classes: A = 10, c1 = 1, c2 = 2,
c3 = 3, c4 = 4, X = 11, Y = 12, Z = 13. Nodes: c1 ∋ Add{A, c2}, c2 ∋
Add{c3, c4, Y}, c3 ∋ Add{X, c4}, c4 ∋ Add{Y, Z}. Expected: five distinct
views, with `{A, X, c4, Y:2, Z}` having the two alternatives
`[[Y, Z]]` and `[[X, c4], [Y, Z]]`. -/
def exB : Ctx :=
  ⟨⟨[(1, ⟨9, .mset {10, 2}⟩), (2, ⟨9, .mset {3, 4, 12}⟩), (3, ⟨9, .mset {11, 4}⟩),
      (4, ⟨9, .mset {12, 13}⟩)], fun id => id⟩, 9, .ac, fun _ => true⟩

#eval (enumerate exB Laws.free ⟨9, .mset {10, 2}⟩).map
  (fun wd => (wd.1, wd.2.unconditional, wd.2.alts))

end Semper.EMatch.Flatten
