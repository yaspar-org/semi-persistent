import Conform.Rounds.Gen
import Lean.Data.Json

/-!
# Multi-round conformance programs: reading an engine dump

`(dump-egraph t :file f)` writes every member of every class of the rebuilt
graph (congruent duplicates omitted, subsumed nodes flagged), with classes and
nodes named by a content colour, so two runs that end in the same e-graph
write the same file. A node's children name nodes; the child class is the
`eclass` of the named node. `Add` nodes carry `mults`.

`DG` is the dump read back: classes are numbered `0..nC-1` in name order,
node `i` has id `nC + i`, and `DG.graph` is the model's `Graph` over the
nodes the index scans (subsumed nodes skipped, `index.rs:521-523`) with
`find` the class of a node and the identity on classes.

Ground terms (`GT`) name a class by a term over the graph's nodes; `DG.eval`
looks a ground term up the way `add` builds it: children first, then the
node with those children (a hash-cons probe). Three deviations of `add` from
the model's `Den` (spec-actions §C.1) are mirrored or flagged: a degenerate
n-ary arity (one child of count one) is that child's class; an n-ary
application one of whose child classes holds a node of the same operator is
`sens` (the engine splices such a child, `egraph.rs:1047-1057`, and the
model does not); so is a ground application written directly inside one of
the same n-ary operator (spliced syntactically when the term is built).
-/

namespace Conform.Rounds

open Semper.EMatch Conform Lean

structure DNode where
  cls : Nat
  op : Sym
  kids : List (Nat × Nat)
  subsumed : Bool
  deriving Inhabited

structure DG where
  nC : Nat
  nodes : Array DNode
  deriving Inhabited

def symOf (s : String) : Option Sym :=
  match s with
  | "F" => some 0 | "G" => some 1 | "Cat" => some 2 | "Add" => some 3 | "And" => some 4
  | _ =>
      match s.toList with
      | 'C' :: rest => (String.ofList rest).toNat?.map (10 + ·)
      | _ => none

def msetOf (l : List (Nat × Nat)) : Multiset Nat :=
  l.foldl (fun m (c, k) => m + Multiset.replicate k c) 0

/-- The model node of an operator and its (class, count) children. -/
def mkNode (f : Sym) (kids : List (Nat × Nat)) : Node :=
  match f with
  | 1 => match kids with
      | [(a, _), (b, _)] => ⟨1, .spair (min a b) (max a b)⟩
      | _ => ⟨1, .tuple (kids.map (·.1))⟩
  | 2 => ⟨2, .seq (kids.flatMap fun (c, k) => List.replicate k c)⟩
  | 3 => ⟨3, .mset (msetOf kids)⟩
  | 4 => ⟨4, .set (kids.map (·.1)).toFinset⟩
  | f => ⟨f, .tuple (kids.map (·.1))⟩

def DNode.node (n : DNode) : Node := mkNode n.op n.kids

def parseDump (txt : String) : Except String DG := do
  let j ← Json.parse txt
  let nodesJ ← j.getObjVal? "nodes"
  let obj ← nodesJ.getObj?
  let entries := obj.toList
  let mut names : Array String := #[]
  for (_, v) in entries do
    let c ← v.getObjValAs? String "eclass"
    unless names.contains c do names := names.push c
  names := names.qsort (· < ·)
  let clsIdx : String → Nat := fun c => (names.findIdx? (· == c)).getD 0
  let mut keyCls : Std.HashMap String Nat := {}
  for (k, v) in entries do
    keyCls := keyCls.insert k (clsIdx (← v.getObjValAs? String "eclass"))
  let mut nodes : Array DNode := #[]
  for (_, v) in entries do
    let opName ← v.getObjValAs? String "op"
    let some op := symOf opName | throw s!"unknown operator {opName}"
    let ch ← v.getObjValAs? (Array String) "children"
    let mults : Array Nat := (v.getObjValAs? (Array Nat) "mults").toOption.getD (ch.map fun _ => 1)
    let sub := (v.getObjValAs? Bool "subsumed").toOption.getD false
    let kids := (ch.toList.zip mults.toList).map fun (k, m) => (keyCls.getD k 0, m)
    nodes := nodes.push ⟨clsIdx (← v.getObjValAs? String "eclass"), op, kids, sub⟩
  return ⟨names.size, nodes⟩

def DG.graph (d : DG) : Graph :=
  ⟨(d.nodes.toList.zipIdx).filterMap (fun (n, i) =>
      if n.subsumed then none else some (d.nC + i, n.node)),
   fun id => if id < d.nC then id else ((d.nodes[id - d.nC]?).map (·.cls)).getD id⟩

def DG.hasOp (d : DG) (c : Nat) (f : Sym) : Bool :=
  d.nodes.any fun n => n.cls = c ∧ n.op = f

def isNary (f : Sym) : Bool := f = 2 ∨ f = 3 ∨ f = 4

/-- `add` may splice a child of this application (`egraph.rs:1047-1057`):
an `A` child is spliced when every node of its class is a sequence of the
operator (`pure_seq_node`, `egraph.rs:4680`); an AC or ACI child when its
class is not `atomic` (no node outside the n-ary operators, never a child)
and holds a node of the operator (`flatten_ac_children`,
`flatten_mset_children`). Flagged conservatively: every node of the child
class is n-ary and one has the operator. -/
def DG.sensitive (d : DG) (f : Sym) (kids : List (Nat × Nat)) : Bool :=
  isNary f ∧ kids.any fun (c, _) =>
    d.hasOp c f ∧ d.nodes.all fun n => n.cls ≠ c ∨ (if f = 2 then n.op = 2 else isNary n.op)

/-- The class of constant `Ci`, if it was built. -/
def DG.constCls (d : DG) (i : Nat) : Option Nat :=
  (d.nodes.find? fun n => n.op = constSym i).map (·.cls)

inductive GT where
  | app (op : Sym) (kids : List (GT × Nat))
  | glob (j : Nat) (c : Nat)
  deriving Inhabited

partial def GT.render : GT → String
  | .glob j _ => s!"g{j}"
  | .app f [] => s!"({opName f})"
  | .app f ks => s!"({opName f} " ++ " ".intercalate (ks.map fun (t, m) =>
      t.render ++ (if m = 1 then "" else s!":{m}")) ++ ")"

inductive EV where
  | ok (c : Nat)
  | sens
  | absent
  deriving DecidableEq, Inhabited

/-- Build a ground term in the graph, the way `add` does, without adding. -/
partial def DG.eval (d : DG) : GT → EV
  | .glob _ c => match d.constCls c with | some k => .ok k | none => .absent
  | .app f ks =>
      -- a ground n-ary application nested in one of the same operator is
      -- spliced syntactically when the term is built (`(Cat (Cat a b) c)` is
      -- `(Cat a b c)`, `AP:849-887`), whatever the stored node says
      let nested := isNary f ∧ ks.any fun (t, _) => match t with | .app g _ => g = f | _ => false
      let vs := ks.map fun (t, m) => (d.eval t, m)
      if nested ∨ vs.any (·.1 = .sens) then .sens
      else if vs.any (·.1 = .absent) then .absent
      else
        let kids := (vs.filterMap fun (e, m) => match e with | .ok c => some (c, m) | _ => none).filter (·.2 ≠ 0)
        if d.sensitive f kids then .sens
        else
          let n := mkNode f kids
          let degenerate : Option Nat := match n.children with
            | .seq [c] => some c
            | .set s => if s.card = 1 then (s.sort (· ≤ ·)).head? else none
            | .mset m => if m.card = 1 then (Multiset.entries m).head?.map (·.1) else none
            | _ => none
          match degenerate with
          | some c => .ok c
          | none =>
              if isNary f ∧ kids.isEmpty then .absent else
              match d.nodes.find? (fun x => x.op = f ∧ decide (x.node = n)) with
              | some x => .ok x.cls
              | none => .absent

/-- The cheapest node of every class (size of the extracted term, nodes the
evaluation flags `sens` excluded), by fixpoint. -/
def DG.best (d : DG) : Array (Option Nat) := Id.run do
  let inf := 1000000000
  let mut cost : Array Nat := Array.replicate d.nC inf
  let mut best : Array (Option Nat) := Array.replicate d.nC none
  for _ in List.range (d.nodes.size + 1) do
    let mut changed := false
    for i in List.range d.nodes.size do
      let n := d.nodes[i]!
      if d.sensitive n.op n.kids then continue
      let c := n.kids.foldl (fun acc (k, m) => acc + m * cost[k]!) 1
      if c < cost[n.cls]! then
        cost := cost.set! n.cls c
        best := best.set! n.cls (some i)
        changed := true
    if !changed then break
  return best

/-- The extracted ground term of a class. -/
partial def DG.classGT (d : DG) (best : Array (Option Nat)) (c : Nat) : Option GT := do
  let i ← best[c]!
  let n := d.nodes[i]!
  let ks ← n.kids.mapM fun (k, m) => do pure (← d.classGT best k, m)
  return .app n.op ks

/-- The ground term of a node, its children named by their classes' terms. -/
def DG.nodeGT (d : DG) (best : Array (Option Nat)) (n : DNode) : Option GT := do
  let ks ← n.kids.mapM fun (k, m) => do pure (← d.classGT best k, m)
  return .app n.op ks

end Conform.Rounds
