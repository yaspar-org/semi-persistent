import Conform.Rounds.Dump
import Conform.Oracle

/-!
# Multi-round conformance programs: the oracle

Two snapshots of the naive run, read back from the engine's dumps: `G₁`
after `(run k-1)` (the snapshot round `k` matches on) and `G₂` after
`(run k)` (the final state). The model's lagged invariant
(`Saturate.InvLag`, `Saturate/Invariant.lean`) says every match of every
rule on `G₁` is `Fired` on `G₂`; when the run saturated, `G₁ = G₂` and this
is `Saturate.Inv` on the final state (`saturation_complete`).

Matches are computed with the reference interpreter (`run (compile P)` of
`EMatch/Ref.lean`, one plan per body pattern, concatenated, the equalities
applied as filters) on `DG.graph G₁`. The consequence of each action is
built in `G₂` from the ground terms of the bound classes (extracted from
`G₁`): a union's two sides must evaluate to one class, an insert's term to
some class. Each fired consequence becomes a `check-eq` of the final
program; the engine then rebuilds the same ground terms in its own final
state under every evaluation mode.

State checks (the differential oracle's checks): for every class of `G₂`,
`check-eq` between its term and up to three of its other nodes, and
`check-neq` between the terms of distinct classes (sampled).
-/

namespace Conform.Rounds

open Semper.EMatch Conform

def ruleVars (r : RRule) : List Var :=
  ((r.body.flatMap Pat.vars) ++ (List.range r.body.length).map rootOf).eraseDups.filter (!isGlobVar ·)

def argOf (σ : Binding) (v : Var) : Option Arg :=
  if v < 100 ∨ v ≥ 1000 then (σ.cls v).map Arg.cls
  else if v < 200 then (σ.mult v).map Arg.mult
  else if v < 300 then (σ.rest v).map (fun m => Arg.mset (Semper.EMatch.Multiset.entries m))
  else if v < 400 then (σ.finRest v).map (fun s => Arg.fset (s.sort (· ≤ ·)))
  else (σ.seqRest v).map Arg.seq

/-- The matches of a rule on a snapshot, as variable assignments. -/
def matchesOf (d : DG) (globals : List Nat) (r : RRule) : List (List (Var × Arg)) :=
  let G := d.graph
  let plan : Plan := (r.body.zipIdx).flatMap fun (p, i) => compile p (rootOf i)
  let vars := ruleVars r
  let ok (σ : Binding) : Bool := r.eqs.all fun e =>
    if isGlobVar e.y then
      match σ.cls e.x, d.constCls (globals.getD (e.y - 90) 0) with
      | some a, some b => a = b
      | _, _ => false
    else
      match σ.cls e.x, σ.cls e.y with
      | some a, some b => a = b
      | _, _ => false
  ((run G plan Binding.empty).filter ok |>.filterMap fun σ =>
    vars.mapM fun v => (argOf σ v).map (v, ·)).eraseDups

/-- The ground term of a right-hand side under an assignment; classes are
named by their terms in the matched snapshot. -/
partial def gtOf (cg : Nat → Option GT) (globals : List Nat) (inst : List (Var × Arg)) :
    Pat → Option GT
  | .var x =>
      if isGlobVar x then some (.glob (x - 90) (globals.getD (x - 90) 0))
      else match inst.lookup x with
        | some (.cls c) => cg c
        | _ => none
  | .plain f args => do
      let ks ← args.mapM (gtOf cg globals inst)
      return .app f (ks.map (·, 1))
  | .comm f p q => do
      return .app f [(← gtOf cg globals inst p, 1), (← gtOf cg globals inst q, 1)]
  | .assoc f pre args suf => do
      let restOf (r : Option Var) : Option (List (GT × Nat)) :=
        match r with
        | none => some []
        | some r => match inst.lookup r with
          | some (.seq l) => l.mapM fun c => (cg c).map (·, 1)
          | _ => none
      let u ← restOf pre
      let v ← restOf suf
      let ks ← args.mapM (gtOf cg globals inst)
      return .app f (u ++ ks.map (·, 1) ++ v)
  | .ac f elems rest => do
      let es ← elems.mapM fun (p, μ) => do
        let k ← match μ with
          | .exact k => some k
          | .var k _ _ => match inst.lookup k with | some (.mult m) => some m | _ => none
        if k = 0 then return none
        return some (← gtOf cg globals inst p, k)
      let rs ← match rest with
        | none => some []
        | some r => match inst.lookup r with
          | some (.mset e) => e.mapM fun (c, k) => (cg c).map (·, k)
          | _ => none
      return .app f (es.filterMap id ++ rs)
  | .aci f elems rest => do
      let ks ← elems.mapM (gtOf cg globals inst)
      let rs ← match rest with
        | none => some []
        | some r => match inst.lookup r with
          | some (.fset l) => l.mapM fun c => (cg c).map (·, 1)
          | _ => none
      return .app f (ks.map (·, 1) ++ rs)

inductive Outcome where
  | fired (line : String)
  | trivial
  | sens
  | unfired (line : String)
  | noTerm

structure Report where
  nMatch : Nat := 0
  fired : List String := []
  trivial : Nat := 0
  sens : Nat := 0
  unfired : List String := []
  noTerm : Nat := 0

def Report.add (rp : Report) : Outcome → Report
  | .fired l => { rp with fired := rp.fired ++ [l] }
  | .trivial => { rp with trivial := rp.trivial + 1 }
  | .sens => { rp with sens := rp.sens + 1 }
  | .unfired l => { rp with unfired := rp.unfired ++ [l] }
  | .noTerm => { rp with noTerm := rp.noTerm + 1 }

/-- The consequence of one action of one match, checked in `G₂`. -/
def actOutcome (d₂ : DG) (cg₁ cg₂ : Nat → Option GT) (globals : List Nat)
    (inst : List (Var × Arg)) : Act → Outcome
  | .union a b =>
      match gtOf cg₁ globals inst a, gtOf cg₁ globals inst b with
      | some ga, some gb =>
          let line := s!"(check-eq {ga.render} {gb.render})"
          match d₂.eval ga, d₂.eval gb with
          | .sens, _ => .sens
          | _, .sens => .sens
          | .ok x, .ok y => if x = y then
              (if ga.render = gb.render then .trivial else .fired line) else .unfired line
          | _, _ => .unfired line
      | _, _ => .noTerm
  | .insert t =>
      match gtOf cg₁ globals inst t with
      | some gt =>
          match d₂.eval gt with
          | .sens => .sens
          | .ok c => match cg₂ c with
              | some gc => if gc.render = gt.render then .trivial
                  else .fired s!"(check-eq {gt.render} {gc.render})"
              | none => .noTerm
          | .absent => .unfired s!"(check {gt.render})"
      | none => .noTerm

/-- Every match of every rule on `G₁`, its consequences in `G₂`. -/
def firedReport (d₁ d₂ : DG) (cs : RCase) (perRule : Nat) : Report := Id.run do
  let b₁ := d₁.best
  let b₂ := d₂.best
  let cg₁ := d₁.classGT b₁
  let cg₂ := d₂.classGT b₂
  let mut rp : Report := {}
  for r in cs.rules do
    let ms := matchesOf d₁ cs.globals r
    rp := { rp with nMatch := rp.nMatch + ms.length }
    let mut taken := 0
    for inst in ms do
      for a in r.acts do
        let o := actOutcome d₂ cg₁ cg₂ cs.globals inst a
        match o with
        | .fired l =>
            if taken < perRule ∧ !(rp.fired.contains l) then
              rp := rp.add o
              taken := taken + 1
        | _ => rp := rp.add o
  return rp

/-- The state checks of the final snapshot. -/
def stateChecks (d : DG) (maxNeq : Nat) : List String := Id.run do
  let b := d.best
  let mut eqs : List String := []
  let mut reps : List (Nat × String) := []
  for c in List.range d.nC do
    let some t := d.classGT b c | continue
    unless d.eval t = .ok c do continue
    let tr := t.render
    reps := reps ++ [(c, tr)]
    let mut n := 0
    for x in d.nodes.toList do
      if x.cls ≠ c ∨ n ≥ 3 then continue
      let some g := d.nodeGT b x | continue
      unless d.eval g = .ok c do continue
      let gr := g.render
      if gr = tr then continue
      eqs := eqs ++ [s!"(check-eq {tr} {gr})"]
      n := n + 1
  let pairs := (reps.zipIdx).flatMap fun ((_, a), i) =>
    (reps.drop (i + 1)).map fun (_, b) => s!"(check-neq {a} {b})"
  let stride := pairs.length / maxNeq + 1
  let neqs := (pairs.zipIdx).filterMap fun (l, i) => if i % stride = 0 then some l else none
  return eqs.eraseDups ++ neqs

end Conform.Rounds
