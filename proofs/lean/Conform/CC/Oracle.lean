import SemperProofs.CC.BoundedOracle
import Std.Data.HashMap

/-!
# AC-congruence conformance: the bounded oracle

An atom is a summand class (`C0`.., then the unit when there is one); a
monomial is a nondecreasing list of atoms. `Univ na B` enumerates every
monomial of total count at most `B` over `na` atoms, by size then
lexicographically, so index order refines size order and the surviving
(smallest) representative of a class is one of its smallest members. The
`add` table maps `(i, x)` to the index of `mons[i] + {x}` when that stays
within the bound; an entry is set only when the stored monomial is the
sorted insertion (`I (add i x) = I i + {x}` for `I i := mons[i]`, the
hypothesis `hadd` of `SemperProofs.CC.Bounded.run_sound`).

`solve` instantiates `SemperProofs.CC.Bounded.run` (the proven core): base
pairs are the asserted equations and the one-step law instances; the pass
candidates (single-summand congruence of each index with its
representative, and cancellation grouped by representative and summand)
are a heuristic, re-validated by `pairOf` inside the core.
-/

namespace Conform.CC

open SemperProofs.CC.Bounded

def insertSorted (x : Nat) : List Nat → List Nat
  | [] => [x]
  | y :: ys => if x ≤ y then x :: y :: ys else y :: insertSorted x ys

/-- Nondecreasing lists of length `s` over `[lo, na)`. -/
def monosOfLen (na : Nat) : Nat → Nat → List (List Nat)
  | 0, _ => [[]]
  | s + 1, lo =>
    ((List.range na).filter (· ≥ lo)).flatMap fun a => (monosOfLen na s a).map (a :: ·)

structure Univ where
  na : Nat
  B : Nat
  mons : Array (List Nat)
  idx : Std.HashMap (List Nat) Nat
  addT : Array (Array (Option Nat))

def mkUniv (na B : Nat) : Univ :=
  let mons := ((List.range (B + 1)).flatMap fun s => monosOfLen na s 0).toArray
  let idx : Std.HashMap (List Nat) Nat :=
    (mons.zipIdx).foldl (fun h p => h.insert p.1 p.2) {}
  let addT := mons.map fun m => (Array.range na).map fun x =>
    if m.length < B then
      let key := insertSorted x m
      match idx[key]? with
      | some j => if mons[j]! == key then some j else none
      | none => none
    else none
  { na, B, mons, idx, addT }

def Univ.add (U : Univ) (i x : Nat) : Option Nat :=
  match U.addT[i]? with
  | some row => row[x]?.getD none
  | none => none

def Univ.index? (U : Univ) (m : List Nat) : Option Nat := U.idx[m.mergeSort]?

/-- Pass candidates: congruence of every index with its representative, and
cancellation of two members of one class that share a summand. -/
def cands (U : Univ) (cancel : Bool) (rep : Array Nat) : List Cand := Id.run do
  let mut out : Array Cand := #[]
  for i in [0:rep.size] do
    let r := rep[i]!
    if r != i then
      for x in [0:U.na] do
        out := out.push (.congr i r x)
  if cancel then
    let mut first : Std.HashMap (Nat × Nat) Nat := {}
    for j in [0:rep.size] do
      let m := U.mons[j]!
      for x in m.eraseDups do
        match U.index? (m.erase x) with
        | some i =>
          match first[(rep[j]!, x)]? with
          | some i0 => out := out.push (.cancel i0 i x)
          | none => first := first.insert (rep[j]!, x) i
        | none => pure ()
  return out.toList

/-- The laws and asserted equations of a case, over atoms. -/
structure Theory where
  na : Nat
  unit : Option Nat
  nil : Option Nat
  inv : List (Nat × Nat)
  idem : Bool
  cancel : Bool
  eqs : List (List Nat × List Nat)

/-- Asserted pairs and one-step law instances, as monomials. -/
def Theory.basePairs (th : Theory) : List (List Nat × List Nat) :=
  th.eqs ++
  (match th.unit with | some u => [([u], [])] | none => []) ++
  (match th.nil with
    | some k => (List.range th.na).map fun a => (List.replicate k a, [])
    | none => []) ++
  th.inv.map (fun p => ([p.1, p.2], [])) ++
  (if th.idem then (List.range th.na).map fun a => ([a, a], [a]) else [])

structure Result where
  univ : Univ
  rep : Array Nat

def solve (th : Theory) (B : Nat) : Result :=
  let U := mkUniv th.na B
  let base := th.basePairs.filterMap fun p =>
    match U.index? p.1, U.index? p.2 with
    | some i, some j => some (i, j)
    | _, _ => none
  let T : Spec := { size := U.mons.size, add := U.add, base, cancel := th.cancel,
                    cands := cands U th.cancel, fuel := U.mons.size + 1 }
  { univ := U, rep := run T }

/-- The representative of a monomial, if it is within the bound. -/
def Result.cls? (r : Result) (m : List Nat) : Option Nat :=
  (r.univ.index? m).map (find r.rep)

def Result.same (r : Result) (a b : List Nat) : Bool :=
  match r.cls? a, r.cls? b with
  | some x, some y => x == y
  | _, _ => false

end Conform.CC
