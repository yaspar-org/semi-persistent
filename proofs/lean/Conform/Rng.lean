import SemperProofs.EMatch.Flatten.LawsMain

/-!
# Conformance generator: deterministic randomness

A `StateM` over Lean's `StdGen`. The same seed gives the same draws on every
platform (the generator is pure integer arithmetic), which is what pins the
emitted programs to the seed.
-/

namespace Conform

abbrev Gen := StateM StdGen

/-- A uniform draw in `[lo, hi]`. -/
def nat (lo hi : Nat) : Gen Nat := do
  let g ← get
  let (n, g') := randNat g lo hi
  set g'
  return n

/-- A uniform element of `l`, or `dflt` when `l` is empty. -/
def pick {α : Type} (l : List α) (dflt : α) : Gen α := do
  if l.isEmpty then return dflt
  let i ← nat 0 (l.length - 1)
  return l.getD i dflt

/-- True with probability `num / den`. -/
def chance (num den : Nat) : Gen Bool := do
  let n ← nat 1 den
  return n ≤ num

/-- `k` distinct elements of `l`, in draw order (fewer when `l` is short). -/
def distinct {α : Type} [DecidableEq α] (k : Nat) (l : List α) (dflt : α) :
    Gen (List α) := do
  let mut rest := l
  let mut out : List α := []
  for _ in List.range k do
    if rest.isEmpty then break
    let x ← pick rest dflt
    out := out ++ [x]
    rest := rest.erase x
  return out

end Conform
