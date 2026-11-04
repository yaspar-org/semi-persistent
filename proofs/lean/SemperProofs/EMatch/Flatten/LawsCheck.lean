import SemperProofs.EMatch.Flatten.LawsMain

/-! Axiom audit for the demand rule under laws. Expected: only `propext`,
`Classical.choice`, `Quot.sound`. -/

#print axioms Semper.EMatch.Flatten.walk_passive
#print axioms Semper.EMatch.Flatten.cntOf_cancel
#print axioms Semper.EMatch.Flatten.cntOf_normalizeList_ac
#print axioms Semper.EMatch.Flatten.cntNF_refold_ac
#print axioms Semper.EMatch.Flatten.refold_ac_inert
#print axioms Semper.EMatch.Flatten.refold_normalize_inert
#print axioms Semper.EMatch.Flatten.refold_ac_lift
#print axioms Semper.EMatch.Flatten.views_soundL
#print axioms Semper.EMatch.Flatten.views_completeL
#print axioms Semper.EMatch.Flatten.acceptsLaws_iff_altsLAccept
#print axioms Semper.EMatch.Flatten.accepts_imp_acceptsLaws
#print axioms Semper.EMatch.Flatten.acceptsFix_imp_acceptsLaws
#print axioms Semper.EMatch.Flatten.demand_laws_complete_ac
#print axioms Semper.EMatch.Flatten.demand_laws_no_redundancy_ac
#print axioms Semper.EMatch.Flatten.demand_laws_complete_aci
#print axioms Semper.EMatch.Flatten.demand_laws_no_redundancy_aci
#print axioms Semper.EMatch.Flatten.demand_laws_complete_assoc
#print axioms Semper.EMatch.Flatten.demand_laws_no_redundancy_assoc

namespace Semper.EMatch.Flatten
open Semper.EMatch

/-! ## The three laws defeat the corrected (kept-count) rule

`add` AC (op 7). Classes `b = 1, c = 2, t = 3, X = 4`; `X ∋ add{b, c}`,
`n = add{t, X}`. The opened view `{t, b, c}` matches `(add (t) ..rest)` with
`taken = [t]`, `rest = {b, c}`; its only tree has the leaf `(X, 1, [b, c])`,
which the kept-count rule `acceptsFix` rejects (`X ∉ taken`, no taken class
in the group); closing it gives the raw view `{t, X}`, whose normal form is
not a node under each law, so the match exists on no other view. -/
def exInv : Ctx :=
  ⟨⟨[(10, ⟨7, .mset {1, 2}⟩)], fun id => if id = 10 then 4 else id⟩, 7, .ac, fun _ => true⟩

def exInvN : Node := ⟨7, .mset {3, 4}⟩

/-- `inv X = t` (the class of `neg X` is `t`). -/
def lawsInvX : Laws := ⟨none, none, some (fun c => if c = 4 then some 3 else none)⟩

/-- `X` is the unit. -/
def lawsUnitX : Laws := ⟨some 4, none, none⟩

def showL (e : List (List (C × Nat) × DemandL)) :
    List (List (C × Nat) × Bool × List (List (C × Nat × List C × Bool))) :=
  e.map (fun wd => (wd.1, wd.2.unconditional,
    wd.2.alts.map (fun ls => ls.map (fun l => (l.1.X, l.1.k, l.1.g, l.2)))))

/- Inverse: the view `{t, b, c}` is emitted with its leaf flagged non-inert
(`inv X = t` is present), and the rule under laws accepts `taken = [t]`
while the kept-count rule rejects. The refold `{t, X}` is no view. -/
#eval showL (enumerateL exInv lawsInvX exInvN)
#eval (enumerateL exInv lawsInvX exInvN).map (fun wd => (wd.1, wd.2.acceptsLawsB [3]))
#eval (enumerateX exInv lawsInvX exInvN).map (fun wd => (wd.1, wd.2.acceptsFixB [3]))

/- Identity: the same with `X` the unit. -/
#eval showL (enumerateL exInv lawsUnitX exInvN)
#eval (enumerateL exInv lawsUnitX exInvN).map (fun wd => (wd.1, wd.2.acceptsLawsB [3]))
#eval (enumerateX exInv lawsUnitX exInvN).map (fun wd => (wd.1, wd.2.acceptsFixB [3]))

/-! Nilpotent (order 2): `n = add{X, Y}`, `Y ∋ add{X, t}`, `X ∋ add{b, c}`.
The tree opening both gives `{b, c, X, t}`; `(add (t) ..rest)` matches with
`rest = {b, c, X}`; the leaf `(Y, 1, [X, t])` is hit, the leaf
`(X, 1, [b, c])` is not, and closing it gives `{X, X, t}`, clamped to `{t}`.
Classes `b = 1, c = 2, t = 3, X = 4, Y = 5`. -/
def exNil : Ctx :=
  ⟨⟨[(10, ⟨7, .mset {1, 2}⟩), (11, ⟨7, .mset {4, 3}⟩)],
      fun id => if id = 10 then 4 else if id = 11 then 5 else id⟩, 7, .ac, fun _ => true⟩

def exNilN : Node := ⟨7, .mset {4, 5}⟩

def lawsNil2 : Laws := ⟨some 0, some 2, none⟩

#eval showL (enumerateL exNil lawsNil2 exNilN)
#eval (enumerateL exNil lawsNil2 exNilN).map (fun wd => (wd.1, wd.2.acceptsLawsB [3]))
#eval (enumerateX exNil lawsNil2 exNilN).map (fun wd => (wd.1, wd.2.acceptsFixB [3]))

/-! ## The leaf side matters: the candidate clause with `X`-side tests only

`n = add{t, t, X}`, `X ∋ add{b, c}`, `inv b = t` (the class of `neg b` is
`t`). The opened view `{t:2, b, c}` normalizes to `{t, c}` (`b` cancels one
`t`); `(add (t) ..rest)` matches with `t` exact 1 and `rest = {c}`. The leaf
`(X, 1, [b, c])` passes every `X`-side test (`X` is not the unit, does not
clamp, has no inverse and is nobody's inverse), so a clause testing `X`
alone rejects it; closing it gives `{t:2, X}`, where `t` has count 2, and
no other view carries the match. The rule under laws flags the leaf
(`b` has an inverse present). -/
def exLeaf : Ctx :=
  ⟨⟨[(10, ⟨7, .mset {1, 2}⟩)], fun id => if id = 10 then 4 else id⟩, 7, .ac, fun _ => true⟩

def exLeafN : Node := ⟨7, .mset {3, 3, 4}⟩

def lawsInvB : Laws := ⟨none, none, some (fun c => if c = 1 then some 3 else none)⟩

/-- The candidate's `X`-side-only test. -/
def nonInertXOnly (laws : Laws) (v : List (C × Nat)) (l : LeafL) : Bool :=
  decide (laws.unit = some l.X) ||
  (match laws.nilpotent with
   | none => false
   | some r => decide (refoldCount v l % r = 0)) ||
  (match laws.inv with
   | none => false
   | some inv =>
       (match inv l.X with
        | none => false
        | some y => decide (y ∈ presentL v l)) ||
       (presentL v l).any (fun y => match inv y with
         | none => false
         | some z => decide (z = l.X)))

#eval showL (enumerateL exLeaf lawsInvB exLeafN)
#eval (enumerateL exLeaf lawsInvB exLeafN).map (fun wd => (wd.1, wd.2.acceptsLawsB [3]))
/- The `X`-side-only flag of the leaf of the view `{c, t}` is `false`. -/
#eval nonInertXOnly lawsInvB [(3, 2), (1, 1), (2, 1)] ⟨4, 1, [(1, 1), (2, 1)]⟩
#eval nonInertAC lawsInvB [(3, 2), (1, 1), (2, 1)] ⟨4, 1, [(1, 1), (2, 1)]⟩

end Semper.EMatch.Flatten
