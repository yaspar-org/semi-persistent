import Conform.CC.Case

/-!
# AC-congruence conformance: the `.egg` program of a case

Declarations, `(set-option :completion eager)`, the actions in order
(`(union (Neg x) y)`, `(union M N)`), then the checks:

* `check-eq` for every pair the oracle identifies at bound `B`, written as a
  star from the class's smallest member (transitivity covers the other
  pairs). Monomials carrying the unit are left out (each equals its
  unit-free part by the identity generator); the empty monomial is the unit
  term. A failing `check-eq` is a genuine engine incompleteness: the pair is
  `=_E`-equal (`SemperProofs.CC.Bounded.run_sound`).
* `check-neq` only for pairs separated at `B` and still separated at
  `B + 2`. This is evidence, not proof: an `E`-derivation may pass through
  monomials larger than `B + 2` (cancellation in particular can need the
  sum of both sides), so a failing `check-neq` is first checked against a
  larger bound before it is called an engine divergence.
-/

namespace Conform.CC

def CCase.op (cs : CCase) : String := if cs.idem then "And" else "Add"
def CCase.unitName (cs : CCase) : String := if cs.idem then "(Top)" else "(Zero)"

def CCase.atom (cs : CCase) (a : Nat) : String :=
  if a < cs.nC then s!"(C{a})" else cs.unitName

/-- Runs of equal atoms of a sorted list. -/
def runs : List Nat → List (Nat × Nat)
  | [] => []
  | x :: xs =>
    match runs xs with
    | (y, k) :: rest => if x = y then (y, k + 1) :: rest else (x, 1) :: (y, k) :: rest
    | [] => [(x, 1)]

def CCase.mono (cs : CCase) (m : List Nat) : String :=
  match m.mergeSort with
  | [] => cs.unitName
  | [a] => cs.atom a
  | m =>
    let kids := if cs.idem then m.map cs.atom
      else (runs m).map fun (a, k) => if k = 1 then cs.atom a else s!"{cs.atom a}:{k}"
    s!"({cs.op} {" ".intercalate kids})"

def CCase.decls (cs : CCase) : List String :=
  ["(sort E)"] ++ (List.range cs.nC).map (fun c => s!"(function C{c} () E)") ++
  (if cs.unit then [s!"(function {if cs.idem then "Top" else "Zero"} () E)"] else []) ++
  (if cs.hasInv then ["(function Neg (E) E)"] else []) ++
  [if cs.idem then
     s!"(function And (E) E :assoc-comm-idem{if cs.unit then " :identity (Top)" else ""})"
   else
     "(function Add (E) E :assoc-comm" ++ (if cs.unit then " :identity (Zero)" else "") ++
     (match cs.nil with | some k => s!" :nilpotent {k}" | none => "") ++
     (if cs.hasInv then " :inverse Neg" else "") ++
     (if cs.cancel then " :cancellative" else "") ++ ")"]

def CCase.act (cs : CCase) : Act → String
  | .neg x y => s!"(union (Neg {cs.atom x}) {cs.atom y})"
  | .eq m n => s!"(union {cs.mono m} {cs.mono n})"

/-- A monomial a check may name: no unit atom; empty only when there is a unit. -/
def CCase.emittable (cs : CCase) (m : List Nat) : Bool :=
  m.all (· < cs.nC) && (cs.unit || !m.isEmpty)

structure Checks where
  eqs : List (List Nat × List Nat)
  neqs : List (List Nat × List Nat)

def checksOf (cs : CCase) : Checks := Id.run do
  let th := cs.theory
  let r := solve th cs.B
  let r2 := solve th (cs.B + 2)
  let U := r.univ
  -- star per class, from the smallest emittable member
  let mut first : Std.HashMap Nat (List Nat) := {}
  let mut eqs : Array (List Nat × List Nat) := #[]
  let mut mins : Array (List Nat) := #[]
  for i in [0:U.mons.size] do
    let m := U.mons[i]!
    if cs.emittable m then
      let k := SemperProofs.CC.Bounded.find r.rep i
      match first[k]? with
      | some m0 => eqs := eqs.push (m0, m)
      | none => first := first.insert k m; mins := mins.push m
  -- disequality candidates: constants pairwise, equation sides, neighbouring class minima
  let small := mins.toList.filter (·.length ≤ 1)
  let mut cand : Array (List Nat × List Nat) := #[]
  for p in small do
    for q in small do
      if p.length < q.length || (p.length == q.length && compare p q == .lt) then
        cand := cand.push (p, q)
  for e in th.eqs do
    for q in small do
      if cs.emittable e.1 then cand := cand.push (e.1, q)
  let ms := mins.toList.filter (·.length ≤ 2)
  for k in [0:ms.length] do
    cand := cand.push (ms.getD k [], ms.getD (k + 1) [])
    cand := cand.push (ms.getD k [], ms.getD (k + 2) [])
  let mut neqs : Array (List Nat × List Nat) := #[]
  for (p, q) in cand.toList do
    if neqs.size < 24 && p != q && cs.emittable p && cs.emittable q &&
        (r.cls? p).isSome && (r.cls? q).isSome &&
        !r.same p q && !r2.same p q && !neqs.contains (p, q) && !neqs.contains (q, p) then
      neqs := neqs.push (p, q)
  return { eqs := eqs.toList, neqs := neqs.toList }

def pad4 (n : Nat) : String :=
  let s := toString n
  "".pushn '0' (4 - s.length) ++ s

def fileName (seed idx : Nat) : String := s!"cc{seed}_{pad4 idx}.egg"

def program (cs : CCase) (ck : Checks) : String :=
  let header := [
    ";; Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.",
    ";; SPDX-License-Identifier: Apache-2.0",
    ";; EXPECT: ok",
    ";; TYPES: machine",
    s!";; semper-conform-cc seed={cs.seed} case={cs.idx} family={cs.family} bound={cs.B} classes={cs.nC}",
    ";; Generated by the AC-congruence conformance generator (proofs/lean/Conform/CC). Every",
    ";; check-eq pair is =_E-equal (bounded oracle, SemperProofs/CC/BoundedOracle.lean);",
    ";; every check-neq pair is separated by the oracle at the bound and at bound + 2.",
    s!";;   lake exe semper-conform-cc {cs.seed} <count> <dir>   (file {fileName cs.seed cs.idx})",
    s!";; check-eq: {ck.eqs.length}, check-neq: {ck.neqs.length}"]
  "\n".intercalate (header ++ cs.decls ++ ["(set-option :completion eager)"] ++
    cs.acts.map cs.act ++
    ck.eqs.map (fun (p, q) => s!"(check-eq {cs.mono p} {cs.mono q})") ++
    ck.neqs.map (fun (p, q) => s!"(check-neq {cs.mono p} {cs.mono q})")) ++ "\n"

end Conform.CC
