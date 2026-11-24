import Conform.Rng
import Conform.CC.Oracle

/-!
# AC-congruence conformance: cases

A case declares `nC` summand classes `C0`.. (nullary constructors), one AC
operator (`Add`, `:assoc-comm`, optional `:identity (Zero)`, `:nilpotent 2|3`,
`:inverse Neg`, `:cancellative`) or one ACI operator (`And`,
`:assoc-comm-idem`, optional `:identity (Top)`), and a sequence of actions:
an inverse node `(union (Neg x) y)` or an asserted equation between two
monomials. Atom `nC` is the unit when there is one.

Every case is drawn from a family biased toward one of the known gaps of the
completion:

* `crit`: two equations whose left sides overlap (a critical pair);
* `slot`: a node asserted equal to a smaller one, then shrunk by a later
  equation (the min-slot refresh);
* `inv`: inverse nodes merged with each other, with the unit, with their
  argument, the unit's inverse, chains `Neg (Neg x)`, an equation under an
  inverse (the rule/inverse critical pair);
* `nil`: nilpotent order 2 or 3 with inverses;
* `cancel`: a cancellative operator (common summand, SC2's disjoint pair,
  two left sides with one right side);
* `aci`: an idempotent operator;
* `rand`: random equations under random laws.

`:assoc` without `:comm` is not generated: its completion is incomplete by
design (`assoc-incomplete.egg`).

Engine registration rules respected (`sortcheck.rs`): `:nilpotent` and
`:inverse` only with `:identity`; ACI with neither, nor `:cancellative`.
-/

namespace Conform.CC

open Conform

inductive Act where
  | neg (x y : Nat)
  | eq (m n : List Nat)
  deriving Repr, Inhabited

structure CCase where
  seed : Nat
  idx : Nat
  family : String
  nC : Nat
  unit : Bool
  idem : Bool
  nil : Option Nat
  cancel : Bool
  B : Nat
  acts : List Act

def CCase.na (cs : CCase) : Nat := cs.nC + if cs.unit then 1 else 0
def CCase.u? (cs : CCase) : Option Nat := if cs.unit then some cs.nC else none
def CCase.hasInv (cs : CCase) : Bool := cs.acts.any fun | .neg .. => true | _ => false

def CCase.theory (cs : CCase) : Theory :=
  let negs := cs.acts.filterMap fun | .neg x y => some (x, y) | _ => none
  -- `Neg x` is one term: two inverse nodes of one argument assert their classes equal
  let negEqs := negs.flatMap fun p => (negs.filter fun q => q.1 = p.1 ∧ q.2 ≠ p.2).map
    fun q => ([p.2], [q.2])
  -- `:inverse` and `:nilpotent` (with `:identity`) make the operator a group: every
  -- element has an inverse (`Neg x`, resp. `x^(k-1)`), so it is cancellative
  { na := cs.na, unit := cs.u?, nil := cs.nil, idem := cs.idem,
    cancel := cs.cancel || cs.hasInv || cs.nil.isSome,
    inv := negs,
    eqs := (cs.acts.filterMap fun | .eq m n => some (m.mergeSort, n.mergeSort) | _ => none)
      ++ negEqs }

/-- `k` atoms among the classes, possibly repeated with probability 1/5. -/
def atoms (nC k : Nat) : Gen (List Nat) := do
  let mut out := []
  for _ in List.range k do
    if !out.isEmpty && (← chance 1 5) then out := out ++ [← pick out 0]
    else out := out ++ [← nat 0 (nC - 1)]
  return out

def randMono (nC lo hi : Nat) : Gen (List Nat) := do
  atoms nC (← nat lo hi)

/-- A random equation between a monomial of size 2..3 and one of size 1..2. -/
def randEq (nC : Nat) : Gen Act := do
  let l ← randMono nC 2 3
  let r ← randMono nC 1 2
  return .eq l r

def family : Gen String := do
  let k ← nat 1 13
  return if k ≤ 2 then "crit" else if k ≤ 4 then "slot" else if k ≤ 7 then "inv"
    else if k ≤ 9 then "nil" else if k ≤ 11 then "cancel" else if k ≤ 12 then "aci" else "rand"

/-- Number of monomials of size at most `B` over `na` atoms. -/
def univSize (na B : Nat) : Nat := Nat.choose (na + B) B

def genCase (seed idx : Nat) : Gen CCase := do
  let fam ← family
  let nC ← nat 3 5
  let mut unit ← chance 1 2
  let mut idem := false
  let mut nil : Option Nat := none
  let mut cancel ← chance 1 5
  let mut acts : List Act := []
  let d ← distinct 5 (List.range nC) 0
  let a := d.getD 0 0; let b := d.getD 1 0; let c := d.getD 2 0
  let e := d.getD 3 c; let f := d.getD 4 e
  match fam with
  | "crit" =>
    match ← nat 0 2 with
    | 0 => acts := [.eq [a, b] [c], .eq [b, e] [f]]
    | 1 => acts := [.eq [a, a] [c], .eq [a, b] [e]]
    | _ => acts := [.eq [a, b, c] [e], .eq [c, a] [b, f]]
  | "slot" =>
    unit ← chance 7 10
    let big := [c, e, f]
    acts := [.eq [a, b] big]
    let shrink ← nat 0 2
    if unit && shrink == 0 then acts := acts ++ [.eq [f] [nC]]
    else if shrink == 1 then acts := acts ++ [.eq [e, f] [a]]
    else acts := acts ++ [.eq [f] [c]]
    if ← chance 1 2 then acts := acts ++ [← randEq nC]
  | "inv" =>
    unit := true
    if ← chance 1 4 then nil := some (← nat 2 3)
    let u := nC
    let sub ← distinct (← nat 1 2) [0, 1, 2, 3, 4, 5] 0
    for s in sub do
      match s with
      | 0 => acts := acts ++ [.neg a c, .neg b c]          -- merged with each other
      | 1 => acts := acts ++ [.neg a u]                   -- with the unit
      | 2 => acts := acts ++ [.neg b b]                   -- with its argument
      | 3 => acts := acts ++ [.neg u e]                   -- the unit's inverse
      | 4 => acts := acts ++ [.neg a b, .neg b e]          -- a chain
      | _ => acts := acts ++ [.neg a e, .eq [a, c] [f]]   -- rule/inverse pair
    if ← chance 1 3 then acts := acts ++ [← randEq nC]
  | "nil" =>
    unit := true
    nil := some (← nat 2 3)
    if ← chance 7 10 then acts := acts ++ [.neg a (← pick [a, b, nC] b)]
    match ← nat 0 2 with
    | 0 => acts := acts ++ [.eq [b, b] [c]]
    | 1 => acts := acts ++ [.eq [a, b] [c]]
    | _ => acts := acts ++ [.eq [a, c] [b, e]]
  | "cancel" =>
    cancel := true
    unit ← chance 2 5
    match ← nat 0 2 with
    | 0 => acts := [.eq [a, c] [b, c]]
    | 1 => acts := [.eq [a, a, a] [b, b], .eq [b, b, b] [a, a]]
    | _ => acts := [.eq [a, b] [c], .eq [a, e] [c]]
    if ← chance 1 3 then acts := acts ++ [← randEq nC]
  | "aci" =>
    idem := true
    cancel := false
    acts := [.eq [a, b] [c]]
    if ← chance 1 2 then acts := acts ++ [.eq [c, e] [a]]
    if ← chance 1 2 then acts := acts ++ [← randEq nC]
  | _ =>
    for _ in List.range (← nat 1 3) do acts := acts ++ [← randEq nC]
  -- random extra laws for the families that do not fix them
  if fam == "crit" || fam == "slot" || fam == "rand" then
    if unit && (← chance 1 6) then nil := some (← nat 2 3)
    if unit && (← chance 1 6) then acts := acts ++ [.neg (← nat 0 (nC - 1)) (← nat 0 nC)]
  if (fam == "inv" || fam == "nil") && (← chance 1 5) then cancel := true
  if ← chance 1 4 then
    let l ← acts.mapM fun x => do return (← nat 0 1000, x)
    -- shuffle the actions (order matters for the slot family: keep it there)
    if fam != "slot" then acts := (l.mergeSort (fun p q => p.1 ≤ q.1)).map (·.2)
  let na := nC + if unit then 1 else 0
  let bs := [3, 4, 5].filter fun B => univSize na (B + 2) ≤ 2000 && univSize nC B ≤ 130
  let B ← pick bs 3
  return { seed, idx, family := fam, nC, unit, idem, nil, cancel, B, acts }

/-- Case `idx` of `seed`: its own generator state, independent of the others. -/
def caseOf (seed idx : Nat) : CCase :=
  -- neighbouring `StdGen` seeds give correlated first draws: mix the seed first
  let h := ((seed * 1000003 + idx) * 2654435761 + 40503) % 4294967291
  (genCase seed idx).run' (mkStdGen h)

end Conform.CC
