import Conform.Case

/-!
# Conformance generator: the oracle

The expected match set of a case is computed by the reference interpreter
`run (compile P)` of `EMatch/Ref.lean` on the stored nodes, and for a case
tagged `:flatten` on every canonical view of every node of the root
operator (`enumerateX`, with the per-kind demand rule `acceptsKindB`; under
laws `enumerateL` with `acceptsLawsB`), the view standing in for the
stored node through a fresh node id in a fresh class.

A match is reported as the root class and the list of tag arguments: the
pattern's variables in order of first occurrence, each bound to a class, a
multiplicity, a multiset, set or sequence rest.
-/

namespace Conform

open Semper.EMatch Semper.EMatch.Flatten

inductive Arg where
  | cls (c : C)
  | mult (m : Nat)
  | mset (e : List (C × Nat))
  | fset (l : List C)
  | seq (l : List C)
  deriving DecidableEq, Repr, Inhabited

structure Match where
  root : C
  args : List Arg
  deriving DecidableEq, Repr, Inhabited

/-- The node variable of the root, as `compile P rootVar` names it. -/
def rootVar : Var := 1000
/-- The id and class of the node standing in for a view. -/
def viewId : NodeId := 5000
def viewCls : C := 999

/-- The pattern's variables in order of first occurrence. -/
def tagVars (P : Pat) : List Var := P.vars.eraseDups

def isClsVar (v : Var) : Bool := v < 100
def isMultVar (v : Var) : Bool := 100 ≤ v ∧ v < 200
def isAcRest (v : Var) : Bool := 200 ≤ v ∧ v < 300
def isAciRest (v : Var) : Bool := 300 ≤ v ∧ v < 400
def isSeqRest (v : Var) : Bool := 400 ≤ v

def argsOf (P : Pat) (σ : Binding) : Option (List Arg) :=
  (tagVars P).mapM fun v =>
    if isClsVar v then (σ.cls v).map Arg.cls
    else if isMultVar v then (σ.mult v).map Arg.mult
    else if isAcRest v then (σ.rest v).map (fun m => Arg.mset (Semper.EMatch.Multiset.entries m))
    else if isAciRest v then (σ.finRest v).map (fun s => Arg.fset (s.sort (· ≤ ·)))
    else (σ.seqRest v).map Arg.seq

/-- The class variables of the root's items, as the compiler names them
(`compileAt` draws them from `rootVar + 1`). -/
def itemVars (P : Pat) : List Var :=
  match P with
  | .ac _ elems _ => ((elemVarsAC elems (rootVar + 1)).1).map Prod.fst
  | .aci _ elems _ => (elemVars elems (rootVar + 1)).1
  | .assoc _ _ args _ => (elemVars args (rootVar + 1)).1
  | _ => []

/-- Matches on the stored nodes. -/
def matchesStored (cs : Case) : List Match :=
  let G := cs.graph
  let plan := compile cs.pat rootVar
  (run G plan Binding.empty).filterMap fun σ => do
    let id ← σ.node rootVar
    let args ← argsOf cs.pat σ
    pure ⟨G.find id, args⟩

/-- The views of node `n` with their demand test. -/
def viewsOf (cs : Case) (ctx : Ctx) (laws : Laws) (n : Node) :
    List (List (C × Nat) × (List C → Bool)) :=
  if cs.hasLaws cs.root then
    (enumerateL ctx laws n).map (fun wd => (wd.1, fun t => wd.2.acceptsLawsB t))
  else
    (enumerateX ctx laws n).map (fun wd => (wd.1, fun t => wd.2.acceptsKindB ctx.κ t))

/-- Matches through the views, for a `:flatten` case of kind `κ`. -/
def matchesFlat (cs : Case) (κ : FlatKind) : List Match :=
  let G := cs.graph
  let f := cs.root.sym
  let laws : Laws := match κ with
    | .aci => cs.aciLaws
    | .ac => cs.lawsAC.toLaws
    | .assoc => Laws.free
  let ctx : Ctx := ⟨G, f, κ, fun _ => true⟩
  let items := itemVars cs.pat
  let plan := compile cs.pat rootVar
  cs.nodes.flatMap fun p =>
    if p.2.op ≠ f then [] else
    (viewsOf cs ctx laws p.2).flatMap fun wa =>
      let G' : Graph := ⟨G.nodes ++ [(viewId, ⟨f, ofView κ wa.1⟩)],
        fun i => if i = viewId then viewCls else G.find i⟩
      (run G' plan Binding.empty).filterMap fun σ =>
        if σ.node rootVar ≠ some viewId then none
        else if !(wa.2 (takenOf σ items)) then none
        else (argsOf cs.pat σ).map fun args => ⟨G.find p.1, args⟩

/-- The expected match set. -/
def expected (cs : Case) : List Match :=
  let ms := match cs.flatten, cs.root.kind? with
    | true, some κ => matchesFlat cs κ
    | _, _ => matchesStored cs
  ms.eraseDups

/-! ## Rejected candidates -/

def replaceAt (l : List Arg) (i : Nat) (a : Arg) : List Arg :=
  l.set i a

/-- Mutants of a match: swapped or replaced classes, a bumped multiplicity,
a rest with one element fewer or a taken class more. -/
def mutants (classes : List C) (m : Match) : List Match :=
  let args := m.args
  let n := args.length
  let taken : List C := args.filterMap (fun a => match a with | .cls c => some c | _ => none)
  let idx := List.range n
  let swaps := idx.flatMap fun i => idx.flatMap fun j =>
    if i < j then
      match (args[i]? : Option Arg), (args[j]? : Option Arg) with
      | some (.cls a), some (.cls b) =>
          if a ≠ b then [replaceAt (replaceAt args i (.cls b)) j (.cls a)] else []
      | _, _ => []
    else []
  let repls := idx.flatMap fun i =>
    match (args[i]? : Option Arg) with
    | some (.cls a) => classes.filterMap fun c => if c ≠ a then some (replaceAt args i (.cls c)) else none
    | some (.mult k) => [replaceAt args i (.mult (k + 1))] ++
        (if k > 1 then [replaceAt args i (.mult (k - 1))] else [])
    | some (.mset e) =>
        let fewer := (List.range e.length).filterMap fun j =>
          match e[j]? with
          | some (c, k) => some (replaceAt args i (.mset
              (if k > 1 then e.set j (c, k - 1) else e.eraseIdx j)))
          | none => none
        let more := taken.map fun c =>
          replaceAt args i (.mset (Semper.EMatch.Multiset.entries (ofEntries e + {c})))
        fewer ++ more
    | some (.fset l) =>
        let fewer := l.map fun c => replaceAt args i (.fset (l.erase c))
        let more := taken.filterMap fun c =>
          if c ∈ l then none else some (replaceAt args i (.fset ((c :: l).mergeSort (· ≤ ·))))
        fewer ++ more
    | some (.seq l) =>
        let fewer := (List.range l.length).map fun j => replaceAt args i (.seq (l.eraseIdx j))
        let rev := if l.reverse ≠ l then [replaceAt args i (.seq l.reverse)] else []
        let more := taken.map fun c => replaceAt args i (.seq (l ++ [c]))
        fewer ++ rev ++ more
    | none => []
  (swaps ++ repls).map fun a => ⟨m.root, a⟩

/-- Whether two roots of different classes share a tag term: the rewrite
then merges the classes, and a rejected candidate can no longer be checked
by class inequality alone. -/
def rootsMerge (ms : List Match) : Bool :=
  ms.any fun a => ms.any fun b => a.args = b.args ∧ a.root ≠ b.root

/-- Candidates at a node of the root operator built without matching: the
class variables take the node's child classes in order (cycling), a
multiplicity is 1, a rest is empty or holds the children left over. These
pin the engine's rejections on a case the model finds no match for. -/
def naive (cs : Case) : List Match :=
  let vars := tagVars cs.pat
  let nCls := (vars.filter isClsVar).length
  cs.nodes.flatMap fun p =>
    if p.2.op ≠ cs.root.sym then [] else
    let kids := childClasses p.2.children
    if kids.isEmpty then [] else
    let root := cs.graph.find p.1
    let taken := (List.range nCls).map fun i => kids.getD (i % kids.length) 0
    let left := taken.foldl (fun l c => l.erase c) kids
    let args (leftover : Bool) : List Arg :=
      (vars.foldl (fun (acc : List Arg × Nat) v =>
        if isClsVar v then (acc.1 ++ [.cls (taken.getD acc.2 0)], acc.2 + 1)
        else if isMultVar v then (acc.1 ++ [.mult 1], acc.2)
        else if isAcRest v then
          (acc.1 ++ [.mset (if leftover then Semper.EMatch.Multiset.entries (left : Multiset C) else [])], acc.2)
        else if isAciRest v then
          (acc.1 ++ [.fset (if leftover then left.eraseDups.mergeSort (· ≤ ·) else [])], acc.2)
        else (acc.1 ++ [.seq (if leftover then left else [])], acc.2)) ([], 0)).1
    [⟨root, args false⟩, ⟨root, args true⟩]

/-- Up to `limit` rejected candidates: mutants of the accepted matches, and
the naive candidates, that are accepted at no root of the same class. -/
def rejected (cs : Case) (ms : List Match) (limit : Nat) : List Match :=
  if rootsMerge ms then [] else
  let all := (ms.flatMap (mutants cs.classes) ++ naive cs).eraseDups
  (all.filter fun m => !(ms.any fun a => a.root = m.root ∧ a.args = m.args)).take limit

end Conform
