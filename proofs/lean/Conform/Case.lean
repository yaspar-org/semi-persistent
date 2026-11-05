import Conform.Rng

/-!
# Conformance generator: cases

A case is a small e-graph in the model's vocabulary (`Graph`, `Node`,
`Children`), the laws of its AC operator, a pattern (`Pat`) over one of
five operators, one per child shape, and whether the rule is tagged
`:flatten`. Generation is biased toward the shapes the known bugs had: a
class with count above one, a class present at the root and inside a
member, a member whose children include the root's other child, the unit
and inverse classes present, two items that could take the same class.

Every stored node is generated in the normal form the engine keeps
(`normalizeList` of the model is the oracle for that too), so the engine
builds exactly the model's nodes: no unit child, counts under the
nilpotent order, no cancelling pair, no single-child n-ary node, and no two
nodes of the same content in different classes.
-/

namespace Conform

open Semper.EMatch Semper.EMatch.Flatten

/-- The five child shapes, one operator each. -/
inductive Shape where
  | plain | comm | seq | mset | set
  deriving DecidableEq, Repr, Inhabited

def Shape.sym : Shape → Sym
  | .plain => 0 | .comm => 1 | .seq => 2 | .mset => 3 | .set => 4

def Shape.name : Shape → String
  | .plain => "F" | .comm => "G" | .seq => "Cat" | .mset => "Add" | .set => "And"

def Shape.ofSym : Sym → Shape
  | 0 => .plain | 1 => .comm | 2 => .seq | 3 => .mset | _ => .set

/-- The `:flatten` kind of an n-ary shape. -/
def Shape.kind? : Shape → Option FlatKind
  | .seq => some .assoc | .mset => some .ac | .set => some .aci | _ => none

def Shape.all : List Shape := [.plain, .comm, .seq, .mset, .set]

/-- The laws of the AC operator: the unit class, the nilpotent order and the
inverse map as `(x, y)` pairs meaning the class of `Neg x` is `y`. -/
structure LawsSpec where
  unit : Option C := none
  nilpotent : Option Nat := none
  inv : List (C × C) := []
  deriving Repr, Inhabited

def LawsSpec.toLaws (l : LawsSpec) : Laws :=
  ⟨l.unit, l.nilpotent, if l.inv.isEmpty then none else some (fun c => l.inv.lookup c)⟩

def LawsSpec.present (l : LawsSpec) : Bool := l.unit.isSome

structure Case where
  seed : Nat
  idx : Nat
  nC : Nat
  arity : Nat
  nodes : List (NodeId × Node)
  cls : List C
  lawsAC : LawsSpec
  aciUnit : Option C
  root : Shape
  pat : Pat
  flatten : Bool

instance : Inhabited Pat := ⟨.var 0⟩
instance : Inhabited Node := ⟨⟨0, .tuple []⟩⟩

def Case.graph (cs : Case) : Graph := ⟨cs.nodes, fun id => cs.cls.getD id 0⟩

def Case.classes (cs : Case) : List C := List.range cs.nC

def Case.aciLaws (cs : Case) : Laws := ⟨cs.aciUnit, none, none⟩

/-- Whether the shape's laws are present: the AC laws for `mset`, the
ACI unit for `set`; a sequence has no laws. -/
def Case.hasLaws (cs : Case) (sh : Shape) : Bool :=
  match sh with
  | .mset => cs.lawsAC.present
  | .set => cs.aciUnit.isSome
  | _ => false

/-! ## Graph generation -/

/-- The classes of a node's children. -/
def childClasses : Children → List C
  | .tuple cs => cs
  | .spair a b => [a, b]
  | .seq cs => cs
  | .mset m => (Semper.EMatch.Multiset.entries m).map Prod.fst
  | .set s => s.sort (· ≤ ·)

structure GState where
  nodes : List (NodeId × Node) := []
  cls : List C := []

/-- A class that already matters: a child of some node, a class holding a
node, the unit or an inverse class. -/
def preferred (cs : List C) (lawsAC : LawsSpec) (st : GState) : List C :=
  let fromNodes := st.nodes.flatMap (fun p => childClasses p.2.children) ++ st.cls
  let fromLaws := lawsAC.unit.toList ++ lawsAC.inv.flatMap (fun p => [p.1, p.2])
  (fromNodes ++ fromLaws).filter (· ∈ cs) |>.eraseDups

def genClass (cs : List C) (lawsAC : LawsSpec) (st : GState) : Gen C := do
  let pref := preferred cs lawsAC st
  if (← chance 3 5) && !pref.isEmpty then pick pref 0 else pick cs 0

def genCount : Gen Nat := do
  let r ← nat 1 20
  return if r ≤ 12 then 1 else if r ≤ 19 then 2 else 3

/-- Children of a node of shape `sh`, in the engine's normal form; `none`
when the draw does not normalize to a node. -/
def genChildren (sh : Shape) (arity : Nat) (cs : List C) (lawsAC : LawsSpec)
    (aciUnit : Option C) (st : GState) : Gen (Option Children) := do
  match sh with
  | .plain =>
      let args ← (List.range arity).mapM (fun _ => genClass cs lawsAC st)
      return some (.tuple args)
  | .comm =>
      let a ← genClass cs lawsAC st
      let b ← genClass cs lawsAC st
      return some (.spair (min a b) (max a b))
  | .seq =>
      let n ← nat 2 4
      let args ← (List.range n).mapM (fun _ => genClass cs lawsAC st)
      return some (.seq args)
  | .mset =>
      let k ← nat 1 3
      -- distinct non-unit classes, biased: draw each with the class bias, then dedup
      let cs' := cs.filter (fun c => lawsAC.unit ≠ some c)
      let draws ← (List.range (k + 2)).mapM (fun _ => genClass cs' lawsAC st)
      let classes := (draws.filter (· ∈ cs')).eraseDups.take k
      let entries ← classes.mapM (fun c => do
        let n ← genCount
        let n := match lawsAC.nilpotent with | some r => min n (r - 1) | none => n
        return (c, n))
      let v := entries.mergeSort (fun a b => a.1 ≤ b.1)
      let laws := lawsAC.toLaws
      if normalizeList .ac laws v = v ∧ (v.map Prod.snd).sum ≥ 2 then
        return some (.mset (ofEntries v))
      else return none
  | .set =>
      let k ← nat 2 3
      let cs' := cs.filter (fun c => aciUnit ≠ some c)
      let draws ← (List.range (k + 2)).mapM (fun _ => genClass cs' lawsAC st)
      let classes := (draws.filter (· ∈ cs')).eraseDups.take k
      let v := (classes.mergeSort (· ≤ ·)).map (fun c => (c, 1))
      let laws : Laws := ⟨aciUnit, none, none⟩
      if normalizeList .aci laws v = v ∧ v.length ≥ 2 then
        return some (.set classes.toFinset)
      else return none

def genLaws (cs : List C) : Gen LawsSpec := do
  if !(← chance 1 2) then return {}
  let u ← pick cs 0
  let nonUnit := cs.filter (· ≠ u)
  let nilp : Option Nat ← if (← chance 1 3) then (some <$> nat 2 3) else pure none
  -- The inverse map is injective, chain-free and absent under `:nilpotent`:
  -- the engine asserts the consequences of the inverse law among existing
  -- nodes (`g(g(x)) ~ x`, `g(a) ~ g(c) ⇒ a ~ c`, and under `:nilpotent k`
  -- the node `x^(k-1)` in the class of `g(x)`), which the model's graph
  -- does not hold.
  let inv : List (C × C) ←
    if nilp.isNone ∧ (← chance 1 2) ∧ nonUnit.length ≥ 2 then do
      let n ← nat 1 2
      let xs ← distinct (2 * n) nonUnit 0
      let srcs := xs.take n
      let tgts := xs.drop n
      pure (srcs.zip tgts)
    else pure []
  return ⟨some u, nilp, inv⟩

def genRootShape : Gen Shape := do
  let r ← nat 1 10
  return if r ≤ 4 then .mset else if r ≤ 6 then .set else if r ≤ 8 then .seq
    else if r = 9 then .plain else .comm

/-! ## Pattern generation -/

structure PState where
  nextCls : Nat := 0
  used : List Var := []
  nextMult : Nat := 100
  usedMult : List Var := []
  nextAc : Nat := 200
  nextAci : Nat := 300
  nextPre : Nat := 400
  nextSuf : Nat := 500

abbrev PGen := StateT PState Gen

def genVar : PGen Pat := do
  let st ← get
  let reuse ← if st.used.isEmpty then pure false
    else if st.nextCls ≥ 4 then pure true else chance 1 5
  if reuse then
    let v ← pick st.used 0
    return .var v
  else
    set { st with nextCls := st.nextCls + 1, used := st.used ++ [st.nextCls] }
    return .var st.nextCls

def genMult : PGen Mult := do
  let r ← nat 1 20
  if r ≤ 12 then return .exact 1
  else if r ≤ 15 then return .exact 2
  else if r ≤ 16 then return .exact 3
  else
    let st ← get
    let reuse ← if st.usedMult.isEmpty then pure false else chance 1 4
    let k ← if reuse then pick st.usedMult 100 else do
      set { st with nextMult := st.nextMult + 1, usedMult := st.usedMult ++ [st.nextMult] }
      pure st.nextMult
    return .var k (if r ≤ 19 then 1 else 2) none

def freshRest (f : PState → Nat) (upd : PState → PState) : PGen Var := do
  let st ← get
  set (upd st)
  return f st

/-- An application of shape `sh`; `fuel` bounds the nesting depth,
`nest` lists the shapes a nested item may take. -/
partial def genApp (fuel : Nat) (arity : Nat) (widths : Shape → List Nat) (nest : List Shape)
    (sh : Shape) : PGen Pat := do
  let item : PGen Pat := do
    if fuel > 0 ∧ !nest.isEmpty ∧ (← chance 3 10) then
      let s ← pick nest .plain
      genApp (fuel - 1) arity widths nest s
    else genVar
  -- the item count: up to the width of some node of the shape, so that the
  -- pattern can match
  let items : PGen Nat := do
    let w ← pick (widths sh) 3
    nat 1 (min 3 w)
  match sh with
  | .plain =>
      let args ← (List.range arity).mapM (fun _ => item)
      return .plain sh.sym args
  | .comm =>
      let p ← item
      let q ← item
      return .comm sh.sym p q
  | .seq =>
      let pre ← if (← chance 1 2) then
          some <$> freshRest (·.nextPre) (fun s => { s with nextPre := s.nextPre + 1 })
        else pure none
      let n ← items
      let args ← (List.range n).mapM (fun _ => item)
      let suf ← if (← chance 1 2) then
          some <$> freshRest (·.nextSuf) (fun s => { s with nextSuf := s.nextSuf + 1 })
        else pure none
      return .assoc sh.sym pre args suf
  | .mset =>
      let n ← items
      let elems ← (List.range n).mapM (fun _ => do
        let p ← item
        let μ ← genMult
        return (p, μ))
      let rest ← if (← chance 1 2) then
          some <$> freshRest (·.nextAc) (fun s => { s with nextAc := s.nextAc + 1 })
        else pure none
      return .ac sh.sym elems rest
  | .set =>
      let n ← items
      let elems ← (List.range n).mapM (fun _ => item)
      let rest ← if (← chance 1 2) then
          some <$> freshRest (·.nextAci) (fun s => { s with nextAci := s.nextAci + 1 })
        else pure none
      return .aci sh.sym elems rest

/-! ## The size of the view enumeration -/

/-- The number of raw views `rawOptX` enumerates for one child position:
one for keeping the class, plus the product over each member's children
when the class is not on the path. -/
partial def countOpt (ctx : Ctx) (fuel : Nat) (X : C) (P : Finset C) : Nat :=
  match fuel with
  | 0 => 1
  | fuel + 1 =>
      1 + (if X ∈ P then 0 else
        ((ctx.members X).map (fun p =>
          ((kids ctx.κ p.2.children).map (fun e => countOpt ctx fuel e.1 (insert X P))).prod)).sum)

/-- The number of raw views of node `n`. -/
def countViews (ctx : Ctx) (n : Node) : Nat :=
  ((kids ctx.κ n.children).map (fun e => countOpt ctx (fuelOf ctx.G) e.1 ∅)).prod

/-- The largest raw-view count over the nodes of the root operator. -/
def maxViews (G : Graph) (root : Shape) : Nat :=
  match root.kind? with
  | none => 0
  | some κ =>
      let ctx : Ctx := ⟨G, root.sym, κ, fun _ => true⟩
      (G.nodes.filterMap (fun p => if p.2.op = root.sym then some (countViews ctx p.2) else none)).foldl max 0

/-- Raw views per node beyond which a case is not tagged `:flatten`: the
reference enumerator deduplicates views quadratically. -/
def viewCap : Nat := 300

/-! ## A case -/

def genCase (seed idx : Nat) : Gen Case := do
  let nC ← nat 2 6
  let cs := List.range nC
  let arity ← nat 1 3
  let root ← genRootShape
  let lawsAC ← genLaws cs
  let aciUnit ← do
    let others := cs.filter (fun c => lawsAC.unit ≠ some c)
    if (← chance 1 4) ∧ !others.isEmpty then some <$> pick others 0 else pure none
  let nN ← nat 2 7
  let mut st : GState := {}
  for i in List.range nN do
    let sh ← if i = 0 then pure root else if (← chance 1 2) then pure root
      else pick Shape.all .plain
    let ch? ← genChildren sh arity cs lawsAC aciUnit st
    match ch? with
    | none => pure ()
    | some ch =>
        let n : Node := ⟨sh.sym, ch⟩
        if st.nodes.any (fun p => decide (p.2 = n)) then pure ()
        else
          let c ← genClass cs lawsAC st
          st := { nodes := st.nodes ++ [(st.nodes.length, n)], cls := st.cls ++ [c] }
  let flatten ← if root.kind?.isSome then chance 1 2 else pure false
  let G : Graph := ⟨st.nodes, fun id => st.cls.getD id 0⟩
  let flatten := flatten && maxViews G root ≤ viewCap
  let present := Shape.all.filter (fun s => st.nodes.any (fun p => p.2.op = s.sym))
  -- Under `:flatten` the engine opens every n-ary atom of the rule, the
  -- model only the root: a flattened case nests plain and commutative
  -- applications only.
  let nest := if flatten then present.filter (fun s => s.kind?.isNone) else present
  let widths := fun (sh : Shape) => st.nodes.filterMap (fun p =>
    if p.2.op = sh.sym then some (childClasses p.2.children).length else none)
  let (pat, _) ← (genApp 2 arity widths nest root).run {}
  return Case.mk seed idx nC arity st.nodes st.cls lawsAC aciUnit root pat flatten

/-- The case of a seed and an index: an independent generator per case, so
that case `i` does not depend on how many cases precede it. -/
def caseOf (seed idx : Nat) : Case :=
  (genCase seed idx).run' (mkStdGen (seed * 1000003 + idx))

end Conform
