import SemperProofs.EMatch.Flatten.RegroupDefs

/-!
# `:flatten`: regrouping as the engine runs it, with its skips

`regroupAll` (`RegroupDefs.lean`) derives every regrouped record, level by
level. The engine (`FlattenScratch::regroup`, `flatten.rs`) regroups view by
view instead, and skips records whose matches another record of the same
view already admits. This file is that loop, step for step:

* the distinct views are the entries, in the order they appear: the walk's
  views in the order of its records, then each new target as it is found;
  a view's records are kept in insertion order (`SkipSt`);
* the next view is the one not yet regrouped with the largest total count,
  the latest entry among equal counts (`SkipSt.next`: the `BinaryHeap` of
  `(size, entry)` pairs pops the maximum);
* for each candidate group (`groupsOfEngine`: the `f`-members by node id,
  as the engine sorts its candidates), each fit, each normalized target
  (`SkipSt.regroupView`):
  - a target with an unconditional record (no leaf, no needed class) gains
    nothing;
  - the source's records are its first unconditional record if it has one,
    otherwise all of them (`srcRecs`);
  - a derived record whose signature (`recSig`: the leaves' opened classes,
    flags and sorted classes, and the needed classes, compared as
    multisets: `RecSig.same`) the target already has is dropped
    (`SkipSt.addRec`).

`regroupAllSkip` runs the loop from the walk's records until no view is
left; `enumerateRSkip`, `enumerateRDSkip` and `Enumerator.regroupSkip` are
`enumerateR`, `enumerateRD` and `Enumerator.regroup` with it in place of
`regroupAll`. `RegroupSkip.lean` proves that the two enumerations accept
the same matches on every view.

The engine's bounds (`MAX_REGROUP_VIEWS`, `MAX_REGROUP_WORK`, `MAX_ELEMS`),
past which it stops regrouping and reports the node, and the count overflow
of normalization (`Normal::Overflow`) are added in `RegroupBoundsDefs.lean`.
-/

namespace Semper.EMatch.Flatten

open Semper.EMatch

/-- A view. -/
abbrev View := List (C × Nat)

/-- A leaf's signature: its opened class, its non-inertness flag, and its
classes sorted (`Sig` in `flatten.rs`). -/
abbrev LeafSig := C × Bool × List C

/-- A record's signature: its leaves' signatures and its needed classes. -/
abbrev RecSig := List LeafSig × List C

def leafSig (l : LeafF) : LeafSig := (l.1.X, l.2, l.1.g.mergeSort (· ≤ ·))

def recSig (r : RecR) : RecSig := (r.2.1.map leafSig, r.2.2)

/-- Equal signatures: the engine sorts both lists and compares them, that is,
compares them as multisets. -/
def RecSig.same (s s' : RecSig) : Bool := s.1.isPerm s'.1 && s.2.isPerm s'.2

/-- A record admitting every match: no leaf and no needed class. -/
def RecR.uncond (r : RecR) : Bool := r.2.1.isEmpty && r.2.2.isEmpty

/-- The records a source derives from: its first unconditional record if it
has one, otherwise all of them. -/
def srcRecs (rs : List RecR) : List RecR :=
  match rs.find? RecR.uncond with
  | some u => [u]
  | none => rs

/-- The record a regrouping by the group of class `g` (classes `grp`) to the
target `t` derives from `r`. -/
def deriveRec (t : View) (g : C) (grp : List C) (r : RecR) : RecR :=
  (t, r.2.1.map (addG g grp (t.map Prod.fst)), needsAfter g grp (t.map Prod.fst) r.2.2)

/-- The candidate groups in the engine's order: the filed `f`-members sorted
by node id, each with its class and children. -/
def groupsOfEngine (ctx : Ctx) : List (C × List (C × Nat)) :=
  (((ctx.G.nodes.filter (fun p => ctx.filed p.1 && decide (p.2.op = ctx.f))).mergeSort
    (fun a b => decide (a.1 ≤ b.1))).map (fun p => (ctx.G.find p.1, kids ctx.κ p.2.children)))

/-- `gs` holds every filed `f`-member with a fit in the view `w`. The engine
reads the candidates of `w` from the use lists `by_contains[c]` of its
classes, so a member holding no class of `w` is not a candidate; such a
member has no fit (`fitsR_nil_of_not_cand`, `RegroupBounds.lean`), and the
loop needs only the members with one. -/
def CandSupAt (ctx : Ctx) (dir : Dir) (w : View) (gs : List (C × List (C × Nat))) : Prop :=
  ∀ gg ∈ groupsOf ctx, ∀ raw, raw ∈ fitsR ctx.κ dir w gg.1 gg.2 → gg ∈ gs

/-- `CandSupAt` for every view. -/
def CandSup (ctx : Ctx) (dir : Dir) (gs : List (C × List (C × Nat))) : Prop :=
  ∀ w, CandSupAt ctx dir w gs

theorem candSup_of_sup {ctx : Ctx} (dir : Dir) {gs : List (C × List (C × Nat))}
    (h : ∀ gg ∈ groupsOf ctx, gg ∈ gs) : CandSup ctx dir gs :=
  fun _ gg hgg _ _ => h gg hgg

/-- The state of the engine's loop: the entries (distinct views) in order,
each view's records in insertion order, whether it was regrouped, and the
signatures of the records regrouping added to it. -/
structure SkipSt where
  order : List View
  recs : View → List RecR
  done : View → Bool
  sigs : View → List RecSig

/-- Add the derived record `d` to the target `t`, unless `t` already has a
record of the same signature. -/
def SkipSt.addRec (t : View) (st : SkipSt) (d : RecR) : SkipSt :=
  if (st.sigs t).any (RecSig.same (recSig d)) then st
  else { st with
    sigs := Function.update st.sigs t (st.sigs t ++ [recSig d])
    recs := Function.update st.recs t (st.recs t ++ [d]) }

/-- One target of a source: entered when new; given nothing when it has an
unconditional record; otherwise given the derived records `ds` one by one. A
target is never a view already regrouped (`addTarget_spec`,
`RegroupSkip.lean`): the engine asserts it, in debug builds, where it once
skipped such a target. -/
def SkipSt.addTarget (st : SkipSt) (t : View) (ds : List RecR) : SkipSt :=
  let st := if t ∈ st.order then st else { st with order := st.order ++ [t] }
  if (st.recs t).any RecR.uncond then st else ds.foldl (SkipSt.addRec t) st

/-- One fit `raw` of the group `gg` in the source view `w`: normalized, a
target, with the records derived from the source's. -/
def SkipSt.fitStep (ctx : Ctx) (laws : Laws) (w : View) (gg : C × List (C × Nat))
    (st : SkipSt) (raw : List (C × Nat)) : SkipSt :=
  match normalize ctx.κ laws raw with
  | .node t => st.addTarget t ((srcRecs (st.recs w)).map (deriveRec t gg.1 (gg.2.map Prod.fst)))
  | _ => st

/-- One candidate group `gg` of the source view `w`: every fit. -/
def SkipSt.groupStep (ctx : Ctx) (dir : Dir) (laws : Laws) (w : View) (st : SkipSt)
    (gg : C × List (C × Nat)) : SkipSt :=
  (fitsR ctx.κ dir w gg.1 gg.2).foldl (SkipSt.fitStep ctx laws w gg) st

/-- Regroup the view `w`: every candidate group, every fit, every target. -/
def SkipSt.regroupView (ctx : Ctx) (dir : Dir) (laws : Laws)
    (gs : List (C × List (C × Nat))) (w : View) (st : SkipSt) : SkipSt :=
  gs.foldl (SkipSt.groupStep ctx dir laws w) st

/-- One entry of the scan for the next view: a view not regrouped replaces the
best so far unless smaller. -/
def SkipSt.pickStep (st : SkipSt) (best : Option View) (w : View) : Option View :=
  if st.done w then best else
  match best with
  | some b => if viewSize w < viewSize b then some b else some w
  | none => some w

/-- The next view to regroup: among those not regrouped, the largest total
count, the latest entry among equal counts. -/
def SkipSt.next (st : SkipSt) : Option View := st.order.foldl st.pickStep none

/-- Mark `w` regrouped. -/
def SkipSt.mark (st : SkipSt) (w : View) : SkipSt :=
  { st with done := Function.update st.done w true }

/-- The loop: pop the next view, mark it, regroup it; until none is left (or
the fuel runs out, which `regroupAllSkip`'s fuel never does). -/
def SkipSt.run (ctx : Ctx) (dir : Dir) (laws : Laws) (gs : List (C × List (C × Nat))) :
    Nat → SkipSt → SkipSt
  | 0, st => st
  | n + 1, st =>
      match st.next with
      | none => st
      | some w => SkipSt.run ctx dir laws gs n (SkipSt.regroupView ctx dir laws gs w (st.mark w))

/-- The loop with the candidates chosen per view: `SkipSt.run` with `gs w`
for the view `w` (the engine reads them from the use lists of `w`'s
classes, `groupsOfEngineAt`, `RegroupBoundsDefs.lean`). -/
def SkipSt.runAt (ctx : Ctx) (dir : Dir) (laws : Laws)
    (gs : View → List (C × List (C × Nat))) : Nat → SkipSt → SkipSt
  | 0, st => st
  | n + 1, st =>
      match st.next with
      | none => st
      | some w => SkipSt.runAt ctx dir laws gs n (SkipSt.regroupView ctx dir laws (gs w) w (st.mark w))

/-- Enter one walk record. -/
def SkipSt.enter (st : SkipSt) (r : RecR) : SkipSt :=
  { st with
    order := if r.1 ∈ st.order then st.order else st.order ++ [r.1]
    recs := Function.update st.recs r.1 (st.recs r.1 ++ [r]) }

def SkipSt.empty : SkipSt := ⟨[], fun _ => [], fun _ => false, fun _ => []⟩

/-- The entries of the walk's records. -/
def SkipSt.init (base : List RecR) : SkipSt := base.foldl SkipSt.enter SkipSt.empty

/-- Every record of the state, view by view. -/
def SkipSt.records (st : SkipSt) : List RecR := st.order.flatMap st.recs

/-- A bound on the loop's iterations: each regroups a distinct view, and
every view is one of the full enumeration's (`RegroupSkip.lean`). -/
def skipFuel (ctx : Ctx) (dir : Dir) (laws : Laws) (base : List RecR) : Nat :=
  (regroupAll ctx dir laws (regroupFuel base) base).length + 1

/-- The loop from the walk's records with the fuel `fuel`. -/
def regroupSkipN (ctx : Ctx) (dir : Dir) (laws : Laws) (gs : List (C × List (C × Nat)))
    (fuel : Nat) (base : List RecR) : List RecR :=
  (SkipSt.run ctx dir laws gs fuel (SkipSt.init base)).records

/-- The engine's regrouping, with the candidate groups `gs`. -/
def regroupSkipG (ctx : Ctx) (dir : Dir) (laws : Laws) (gs : List (C × List (C × Nat)))
    (base : List RecR) : List RecR :=
  regroupSkipN ctx dir laws gs (skipFuel ctx dir laws base) base

/-- The engine's regrouping, candidates in the engine's order. -/
def regroupAllSkip (ctx : Ctx) (dir : Dir) (laws : Laws) (base : List RecR) : List RecR :=
  regroupSkipG ctx dir laws (groupsOfEngine ctx) base

/-- `enumerateRD` with the engine's regrouping. -/
def enumerateRDSkip (T : C → Bool) (ctx : Ctx) (dir : Dir) (laws : Laws) (limit : Nat)
    (n : Node) : List (List (C × Nat) × DemandL) :=
  enumerateFromR (withinLimit limit (regroupAllSkip ctx dir laws
    ((baseRecsR ctx dir laws n).filter (keepRec ctx.κ T laws))))

/-- `enumerateR` with the engine's regrouping. -/
def enumerateRSkip (ctx : Ctx) (dir : Dir) (laws : Laws) (limit : Nat) (n : Node) :
    List (List (C × Nat) × DemandL) :=
  enumerateFromR (withinLimit limit (regroupAllSkip ctx dir laws (baseRecsR ctx dir laws n)))

/-- `Enumerator.regroup` with the engine's regrouping. -/
def Enumerator.regroupSkip (dir : Sym → Dir) : Enumerator :=
  ⟨fun ctx laws items n => enumerateRSkip ctx (dir ctx.f) laws items.length n,
    fun ctx laws σ items n =>
      enumerateRDSkip (takeableR ctx σ items) ctx (dir ctx.f) laws items.length n⟩

/-- The flattened plan with the engine's regrouping. -/
abbrev runERSkip (c : FCtx) (dir : Sym → Dir) : List EStep → EEnv → List EEnv :=
  runEG (Enumerator.regroupSkip dir) c

end Semper.EMatch.Flatten
