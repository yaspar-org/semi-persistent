import SemperProofs.EMatch.Flatten.FixKind

/-! Axiom audit for the corrected demand rule. Expected: only `propext`,
`Classical.choice`, `Quot.sound`. -/

#print axioms Semper.EMatch.Flatten.enumerateX_proj
#print axioms Semper.EMatch.Flatten.views_soundX
#print axioms Semper.EMatch.Flatten.views_completeX
#print axioms Semper.EMatch.Flatten.flatten_fix_sound_ac
#print axioms Semper.EMatch.Flatten.flatten_fix_sound_aci
#print axioms Semper.EMatch.Flatten.flatten_fix_sound_assoc
#print axioms Semper.EMatch.Flatten.flatten_fix_complete_ac
#print axioms Semper.EMatch.Flatten.flatten_fix_complete_aci
#print axioms Semper.EMatch.Flatten.flatten_fix_complete_assoc
#print axioms Semper.EMatch.Flatten.demand_fix_complete_ac
#print axioms Semper.EMatch.Flatten.demand_fix_complete_aci
#print axioms Semper.EMatch.Flatten.demand_fix_complete_assoc
#print axioms Semper.EMatch.Flatten.demand_fix_no_redundancy_ac
#print axioms Semper.EMatch.Flatten.demand_fix_no_redundancy_aci
#print axioms Semper.EMatch.Flatten.demand_fix_no_redundancy_assoc
#print axioms Semper.EMatch.Flatten.accepts_imp_acceptsFix
#print axioms Semper.EMatch.Flatten.demand_orig_complete_aci
#print axioms Semper.EMatch.Flatten.demand_orig_complete_assoc
#print axioms Semper.EMatch.Flatten.demand_orig_no_redundancy_aci
#print axioms Semper.EMatch.Flatten.demand_orig_no_redundancy_assoc
#print axioms Semper.EMatch.Flatten.flatten_kind_sound_ac
#print axioms Semper.EMatch.Flatten.flatten_kind_sound_aci
#print axioms Semper.EMatch.Flatten.flatten_kind_sound_assoc
#print axioms Semper.EMatch.Flatten.flatten_kind_complete_ac
#print axioms Semper.EMatch.Flatten.flatten_kind_complete_aci
#print axioms Semper.EMatch.Flatten.flatten_kind_complete_assoc
#print axioms Semper.EMatch.Flatten.demand_kind_complete_ac
#print axioms Semper.EMatch.Flatten.demand_kind_complete_aci
#print axioms Semper.EMatch.Flatten.demand_kind_complete_assoc

namespace Semper.EMatch.Flatten
open Semper.EMatch

/-! The lost match of `demand-gap.egg`: `Plus` AC (op 7), classes
`X = 1, c = 2, Y = 3, d = 4, Z = 5`; nodes `Y ∋ Plus{X, c}`, `Z ∋ Plus{Y, d}`,
`n = Plus{Y, Z}`. The view `{X, c, Y, d}` has the single tree with leaves
`(Y, [X, c])` and `(Z, [Y, d])`; with `taken = [Y, d]` the original demand
rejects it (leaf `[X, c]` unhit) and the corrected one accepts it (the leaf
opened `Y`, which is taken). -/
def exGap : Ctx :=
  ⟨⟨[(10, ⟨7, .mset {1, 2}⟩), (11, ⟨7, .mset {3, 4}⟩)],
      fun id => if id = 10 then 3 else if id = 11 then 5 else id⟩, 7, .ac, fun _ => true⟩

def exGapN : Node := ⟨7, .mset {3, 5}⟩

#eval (enumerateX exGap Laws.free exGapN).map
  (fun wd => (wd.1, wd.2.unconditional, wd.2.alts))

/- The original rule rejects `taken = [Y, d]` on `{X, c, Y, d}`. -/
#eval (enumerate exGap Laws.free exGapN).filterMap
  (fun wd => if wd.1 = [(1, 1), (2, 1), (3, 1), (4, 1)] then some (wd.2.acceptsB [3, 4]) else none)

/- The per-kind rule (AC: `merge_on_close`) accepts it. -/
#eval (enumerateX exGap Laws.free exGapN).filterMap
  (fun wd => if wd.1 = [(1, 1), (2, 1), (3, 1), (4, 1)] then some (wd.2.acceptsKindB .ac [3, 4]) else none)

/- The corrected rule accepts it. -/
#eval (enumerateX exGap Laws.free exGapN).filterMap
  (fun wd => if wd.1 = [(1, 1), (2, 1), (3, 1), (4, 1)] then some (wd.2.acceptsFixB [3, 4]) else none)

end Semper.EMatch.Flatten
