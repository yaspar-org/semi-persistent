import Conform.Emit
import SemperProofs.EMatch.Flatten.FoldPlan

/-!
# `:flatten` conformance generator: cases

The shapes the seed-1 generator (`Conform.Case`) leaves out of `:flatten`
rules: n-ary applications nested in the pattern (every n-ary atom of a
flattened rule opens views, each with its own register), laws on two
operators of one pattern (`Add` with `:identity`/`:nilpotent`/`:inverse`
and `And` with `:identity`), cyclic classes (a class holding a node over
itself), several nodes of one operator in one class, sequences with prefix
and suffix rests, the folds `SubL` (`:assoc-left`) and `SubR`
(`:assoc-right`), and graphs whose nodes have many raw views.

The engine stores a fold node as a sequence and flattens it with
`FlatKind::Assoc` (`schedule.rs:1246-1305`), opening only the fold's spine:
the first position of a left fold, the last of a right fold, at the root and
in every opened member. The oracle reads a fold as an `assoc` operator with
that direction (`FCase.dirOf`, `runED` of `FoldPlan.lean`).

A case draws a family (the shape it stresses), then a graph and a pattern.
Every stored node is generated in the normal form the engine keeps, as in
`Conform.Case`: no unit child, counts under the nilpotent order, no
cancelling pair, at least two entries, no two nodes of one content in
different classes, and the inverse map injective, chain-free and absent
under `:nilpotent` (`Conform.genLaws`).
-/

namespace ConformF

open Semper.EMatch Semper.EMatch.Flatten
open Conform (Gen nat pick chance LawsSpec PState PGen genVar genMult freshRest
  childClasses genLaws genCount countOpt viewCap)

/-- The operators: the five of `Conform.Shape` and the two folds. -/
inductive FShape where
  | plain | comm | seq | mset | set | foldL | foldR
  deriving DecidableEq, Repr, Inhabited

def FShape.sym : FShape → Sym
  | .plain => 0 | .comm => 1 | .seq => 2 | .mset => 3 | .set => 4 | .foldL => 5 | .foldR => 6

def FShape.name : FShape → String
  | .plain => "F" | .comm => "G" | .seq => "Cat" | .mset => "Add" | .set => "And"
  | .foldL => "SubL" | .foldR => "SubR"

def FShape.ofSym : Sym → FShape
  | 0 => .plain | 1 => .comm | 2 => .seq | 3 => .mset | 4 => .set | 5 => .foldL | _ => .foldR

/-- The `:flatten` kind: a fold flattens as a sequence. -/
def FShape.kind? : FShape → Option FlatKind
  | .seq | .foldL | .foldR => some .assoc
  | .mset => some .ac
  | .set => some .aci
  | _ => none

def FShape.isSeq (s : FShape) : Bool := s.kind? = some .assoc
def FShape.isFold (s : FShape) : Bool := s = .foldL || s = .foldR

/-- Whether the generator draws the folds `SubL` and `SubR`. -/
def foldsEnabled : Bool := true

/-- The shapes the generator may draw. -/
def allowed (l : List FShape) : List FShape := l.filter (fun s => foldsEnabled || !s.isFold)

def FShape.all : List FShape := allowed [.plain, .comm, .seq, .mset, .set, .foldL, .foldR]
def FShape.nary : List FShape := allowed [.seq, .mset, .set, .foldL, .foldR]

/-- The families: the shape a case stresses. -/
inductive Family where
  | nested | laws2 | cyclic | multi | seq | fold | nearCap | mixed | control
  deriving DecidableEq, Repr, Inhabited

def Family.name : Family → String
  | .nested => "nested" | .laws2 => "laws2" | .cyclic => "cyclic" | .multi => "multi"
  | .seq => "seq" | .fold => "fold" | .nearCap => "nearcap" | .mixed => "mixed"
  | .control => "control"

structure FCase where
  seed : Nat
  idx : Nat
  family : Family
  nC : Nat
  arity : Nat
  nodes : List (NodeId × Node)
  cls : List C
  lawsAC : LawsSpec
  aciUnit : Option C
  root : FShape
  pat : Pat
  flatten : Bool

instance : Inhabited Pat := ⟨.var 0⟩

def FCase.graph (cs : FCase) : Graph := ⟨cs.nodes, fun id => cs.cls.getD id 0⟩
def FCase.classes (cs : FCase) : List C := List.range cs.nC
def FCase.aciLaws (cs : FCase) : Laws := ⟨cs.aciUnit, none, none⟩

/-- The laws of each operator: the case's AC laws for `Add`, the ACI unit
for `And`, none otherwise. -/
def FCase.lawsOf (cs : FCase) (f : Sym) : Laws :=
  if f = FShape.mset.sym then cs.lawsAC.toLaws
  else if f = FShape.set.sym then cs.aciLaws
  else Laws.free

/-- The fold direction of each operator. -/
def FCase.dirOf (_ : FCase) (f : Sym) : Dir :=
  if f = FShape.foldL.sym then .left
  else if f = FShape.foldR.sym then .right
  else .both

/-! ## Graph generation -/

structure GState where
  nodes : List (NodeId × Node) := []
  cls : List C := []

def preferred (cs : List C) (lawsAC : LawsSpec) (st : GState) : List C :=
  let fromNodes := st.nodes.flatMap (fun p => childClasses p.2.children) ++ st.cls
  let fromLaws := lawsAC.unit.toList ++ lawsAC.inv.flatMap (fun p => [p.1, p.2])
  (fromNodes ++ fromLaws).filter (· ∈ cs) |>.eraseDups

def genClass (cs : List C) (lawsAC : LawsSpec) (st : GState) : Gen C := do
  let pref := preferred cs lawsAC st
  if (← chance 3 5) && !pref.isEmpty then pick pref 0 else pick cs 0

/-- Children of a node of shape `sh`, in the engine's normal form; `none`
when the draw does not normalize to a node. -/
def genChildren (sh : FShape) (arity : Nat) (cs : List C) (lawsAC : LawsSpec)
    (aciUnit : Option C) (st : GState) : Gen (Option Children) := do
  match sh with
  | .plain =>
      let args ← (List.range arity).mapM (fun _ => genClass cs lawsAC st)
      return some (.tuple args)
  | .comm =>
      let a ← genClass cs lawsAC st
      let b ← genClass cs lawsAC st
      return some (.spair (min a b) (max a b))
  | .seq | .foldL | .foldR =>
      let n ← nat 2 4
      let args ← (List.range n).mapM (fun _ => genClass cs lawsAC st)
      return some (.seq args)
  | .mset =>
      let k ← nat 1 3
      let cs' := cs.filter (fun c => lawsAC.unit ≠ some c)
      let draws ← (List.range (k + 2)).mapM (fun _ => genClass cs' lawsAC st)
      let classes := (draws.filter (· ∈ cs')).eraseDups.take k
      let entries ← classes.mapM (fun c => do
        let n ← genCount
        let n := match lawsAC.nilpotent with | some r => min n (r - 1) | none => n
        return (c, n))
      let v := entries.mergeSort (fun a b => a.1 ≤ b.1)
      if normalizeList .ac lawsAC.toLaws v = v ∧ (v.map Prod.snd).sum ≥ 2 then
        return some (.mset (ofEntries v))
      else return none
  | .set =>
      let k ← nat 2 3
      let cs' := cs.filter (fun c => aciUnit ≠ some c)
      let draws ← (List.range (k + 2)).mapM (fun _ => genClass cs' lawsAC st)
      let classes := (draws.filter (· ∈ cs')).eraseDups.take k
      let v := (classes.mergeSort (· ≤ ·)).map (fun c => (c, 1))
      if normalizeList .aci ⟨aciUnit, none, none⟩ v = v ∧ v.length ≥ 2 then
        return some (.set classes.toFinset)
      else return none

/-- The class of a new node: for a cyclic draw one of its own children
(the class then holds a node over itself), for a multi-member draw a class
already holding a node of the same operator, otherwise the biased draw. -/
def chooseClass (cs : List C) (lawsAC : LawsSpec) (aciUnit : Option C) (st : GState)
    (sh : FShape) (ch : Children) (pCyc pMulti : Nat) : Gen C := do
  let units := lawsAC.unit.toList ++ aciUnit.toList
  let own := (childClasses ch).filter (fun c => c ∉ units)
  let same := (st.nodes.zip st.cls).filterMap (fun p =>
    if p.1.2.op = sh.sym then some p.2 else none)
  if (← chance pCyc 10) && !own.isEmpty then pick own 0
  else if (← chance pMulti 10) && !same.isEmpty then pick same 0
  else genClass cs lawsAC st

/-- One graph: `nN` draws of a node, each of the root shape with
probability `pRoot`/10, otherwise of a shape of `palette`. -/
def genGraph (nN : Nat) (root : FShape) (palette : List FShape) (pRoot pCyc pMulti : Nat)
    (arity : Nat) (cs : List C) (lawsAC : LawsSpec) (aciUnit : Option C) : Gen GState := do
  let mut st : GState := {}
  for i in List.range nN do
    let sh ← if i = 0 then pure root else if (← chance pRoot 10) then pure root
      else pick palette .plain
    let ch? ← genChildren sh arity cs lawsAC aciUnit st
    match ch? with
    | none => pure ()
    | some ch =>
        let n : Node := ⟨sh.sym, ch⟩
        if st.nodes.any (fun p => decide (p.2 = n)) then pure ()
        else
          let c ← chooseClass cs lawsAC aciUnit st sh ch pCyc pMulti
          st := { nodes := st.nodes ++ [(st.nodes.length, n)], cls := st.cls ++ [c] }
  return st

/-! ## Pattern generation -/

/-- An application of shape `sh`. `fuel` bounds the depth, `nest` lists the
shapes a nested item may take, `pNest`/10 is the chance an item nests,
`force` makes the first item an application of that shape, `pRest`/4 the
chance of each rest. -/
partial def genApp (fuel : Nat) (arity : Nat) (widths : FShape → List Nat) (nest : List FShape)
    (pNest pRest : Nat) (force : Option FShape) (sh : FShape) : PGen Pat := do
  let item (i : Nat) : PGen Pat := do
    match force, i with
    | some s, 0 => genApp (fuel - 1) arity widths nest pNest pRest none s
    | _, _ =>
      if fuel > 0 ∧ !nest.isEmpty ∧ (← chance pNest 10) then
        let s ← pick nest .plain
        genApp (fuel - 1) arity widths nest pNest pRest none s
      else genVar
  let items : PGen Nat := do
    let w ← pick (widths sh) 3
    nat 1 (min 3 w)
  match sh with
  | .plain =>
      let args ← (List.range arity).mapM item
      return .plain sh.sym args
  | .comm =>
      let p ← item 0
      let q ← item 1
      return .comm sh.sym p q
  | .seq | .foldL | .foldR =>
      let pre ← if (← chance pRest 4) then
          some <$> freshRest (·.nextPre) (fun s => { s with nextPre := s.nextPre + 1 })
        else pure none
      let n ← items
      let args ← (List.range n).mapM item
      let suf ← if (← chance pRest 4) then
          some <$> freshRest (·.nextSuf) (fun s => { s with nextSuf := s.nextSuf + 1 })
        else pure none
      return .assoc sh.sym pre args suf
  | .mset =>
      let n ← items
      let elems ← (List.range n).mapM (fun i => do
        let p ← item i
        let μ ← genMult
        return (p, μ))
      let rest ← if (← chance pRest 4) then
          some <$> freshRest (·.nextAc) (fun s => { s with nextAc := s.nextAc + 1 })
        else pure none
      return .ac sh.sym elems rest
  | .set =>
      let n ← items
      let elems ← (List.range n).mapM item
      let rest ← if (← chance pRest 4) then
          some <$> freshRest (·.nextAci) (fun s => { s with nextAci := s.nextAci + 1 })
        else pure none
      return .aci sh.sym elems rest

/-- The operators of the applications of a pattern, root first. -/
partial def patOps : Pat → List Sym
  | .var _ => []
  | .plain f args => f :: args.flatMap patOps
  | .comm f p q => f :: (patOps p ++ patOps q)
  | .assoc f _ args _ => f :: args.flatMap patOps
  | .ac f elems _ => f :: elems.flatMap (fun e => patOps e.1)
  | .aci f elems _ => f :: elems.flatMap patOps

/-- Whether an n-ary application occurs under another application. -/
def nestedNary (P : Pat) : Bool :=
  ((patOps P).drop 1).any (fun f => (FShape.ofSym f).kind?.isSome)

/-- Whether a sequence application of the pattern has a prefix or suffix rest. -/
partial def seqRest : Pat → Bool
  | .var _ => false
  | .plain _ args => args.any seqRest
  | .comm _ p q => seqRest p || seqRest q
  | .assoc _ pre args suf => pre.isSome || suf.isSome || args.any seqRest
  | .ac _ elems _ => elems.any (fun e => seqRest e.1)
  | .aci _ elems _ => elems.any seqRest

/-! ## View counts -/

/-- The raw-view count of every node of operator `f` (kind `κ`). -/
def viewCounts (G : Graph) (f : Sym) (κ : FlatKind) : List Nat :=
  let ctx : Ctx := ⟨G, f, κ, fun _ => true⟩
  G.nodes.filterMap (fun p =>
    if p.2.op = f then
      some (((kids κ p.2.children).map (fun e => countOpt ctx (fuelOf G) e.1 ∅)).prod)
    else none)

/-- The largest raw-view count of a node of an n-ary operator of the
pattern, and the product over the pattern's n-ary applications of the raw
views of all nodes of its operator (the oracle's work, roughly). -/
def viewStats (G : Graph) (P : Pat) : Nat × Nat :=
  (patOps P).foldl (fun acc f =>
    match (FShape.ofSym f).kind? with
    | none => acc
    | some κ =>
        let vs := viewCounts G f κ
        (max acc.1 (vs.foldl max 0), acc.2 * max 1 vs.sum)) (0, 1)

/-- The oracle's work bound: the product of `viewStats`. -/
def workCap : Nat := 20000

/-! ## A case -/

/-- The family of case `idx`: `(7 idx mod 20) + 1` read as a draw in
`[1, 20]`, so that every 20 consecutive cases hold each family in its
proportion (the first draw of `mkStdGen` over consecutive seeds is far from
uniform). -/
def familyOf (idx : Nat) : Family :=
  let r := (7 * idx) % 20 + 1
  if r ≤ 5 then .nested else if r ≤ 8 then .laws2 else if r ≤ 10 then .cyclic
    else if r ≤ 12 then .multi else if r ≤ 14 then .seq
    else if r ≤ 16 then (if foldsEnabled then .fold else .seq)
    else if r ≤ 18 then .nearCap else if r = 19 then .mixed else .control

/-- The root shape of a family. -/
def genRoot (fam : Family) : Gen FShape := do
  match fam with
  | .laws2 => pick [.mset, .set] .mset
  | .seq => pick (allowed [.seq, .seq, .foldL, .foldR]) .seq
  | .fold => pick (allowed [.foldL, .foldR]) .seq
  | .nested => pick (allowed [.mset, .mset, .set, .seq, .foldL, .foldR, .plain, .comm]) .mset
  | _ => pick (allowed [.mset, .mset, .set, .seq, .foldL, .foldR, .plain, .comm]) .mset

/-- One draw of a case of family `fam`; `none` when the draw is over the
view cap (the caller redraws). -/
def genOnce (seed idx : Nat) (fam : Family) : Gen (Option FCase) := do
  let nC ← if fam = .nearCap then nat 3 4 else nat 2 6
  let cs := List.range nC
  let arity ← nat 1 2
  let root ← genRoot fam
  let lawsAC ← if fam = .laws2 then do
      let l ← genLaws cs
      if l.present then pure l else do
        let u ← pick cs 0
        pure { unit := some u }
    else genLaws cs
  let aciUnit ← do
    let others := cs.filter (fun c => lawsAC.unit ≠ some c)
    let p := if fam = .laws2 then 4 else 1
    if (← chance p 4) ∧ !others.isEmpty then some <$> pick others 0 else pure none
  -- the palette of other shapes in the graph
  let palette : List FShape ← match fam with
    | .laws2 => pure [.mset, .set, .plain]
    | .fold => pure (allowed [.foldL, .foldR, .seq, .mset])
    | .seq => pure (allowed [.seq, .foldL, .foldR, .set])
    | .nested => do
        let a ← pick FShape.nary .mset
        let b ← pick FShape.nary .set
        let c ← pick FShape.all .plain
        pure [a, b, c]
    | .nearCap => pure [root]
    | _ => do
        let a ← pick FShape.all .mset
        let b ← pick FShape.all .set
        pure [a, b]
  let nN ← match fam with
    | .nearCap => nat 6 9
    | .multi | .cyclic => nat 3 8
    | _ => nat 2 7
  let pRoot := match fam with | .nearCap => 8 | .nested | .laws2 => 4 | _ => 5
  let pCyc := match fam with | .cyclic => 5 | .nearCap => 2 | .mixed => 3 | _ => 1
  let pMulti := match fam with | .multi => 6 | .nearCap => 6 | .mixed => 3 | _ => 1
  let st ← genGraph nN root palette pRoot pCyc pMulti arity cs lawsAC aciUnit
  let G : Graph := ⟨st.nodes, fun id => st.cls.getD id 0⟩
  let present := FShape.all.filter (fun s => st.nodes.any (fun p => p.2.op = s.sym))
  let widths := fun (sh : FShape) => st.nodes.filterMap (fun p =>
    if p.2.op = sh.sym then some (childClasses p.2.children).length else none)
  let nestable := present.filter (fun s => s ≠ root || fam = .nested || fam = .fold)
  let pNest := match fam with | .nested => 6 | .laws2 | .fold => 4 | .nearCap => 1 | _ => 3
  let pRest := match fam with | .seq => 3 | _ => 2
  let other : FShape := if root = .mset then .set else .mset
  let force : Option FShape := match fam with
    | .laws2 => if present.contains other then some other else none
    | .nested => if root.kind?.isNone then
        (present.filter (fun s => s.kind?.isSome)).head? else none
    | _ => none
  let (pat, _) ← (genApp 2 arity widths nestable pNest pRest force root).run {}
  let flatten := fam ≠ .control && (patOps pat).any (fun f => (FShape.ofSym f).kind?.isSome)
  let (mx, work) := viewStats G pat
  if flatten && (mx > viewCap || work > workCap) then return none
  -- a draw of the nested family must nest an n-ary application, one of the
  -- laws family must hold both `Add` and `And`
  let ops := patOps pat
  if fam = .nested && !nestedNary pat then return none
  if fam = .laws2 && !(ops.contains FShape.mset.sym && ops.contains FShape.set.sym) then
    return none
  return some ⟨seed, idx, fam, nC, arity, st.nodes, st.cls, lawsAC, aciUnit, root, pat, flatten⟩

end ConformF
