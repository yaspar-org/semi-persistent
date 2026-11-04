import SemperProofs.EMatch.Defs

/-!
# E-matching: reference interpreter over lists

Formalizes part (d) of the proof sketch `notes-ematch-proof.md` as a
reference implementation: the four index families as filters, the join as
an intersection, the decompositions as list-enumerating functions, the plan
as a list of steps, and a left-to-right compiler from patterns to plans.

Differences from the engine, by design of the model:
* the leapfrog cursors are replaced by `List.filter` over buckets (the
  cursor correctness is a separate lemma on sorted lists, sketch lemma 2);
* an AC decomposition reads the node's children as the sorted entry list
  `Multiset.entries` (class, count) instead of the engine's residual
  register;
* a decomposition element is a class *variable* with its annotation: the
  resolved atom carries the variable, and a nested application pattern is
  its own atom re-joined through `byRepr` (sketch (d), "nested atoms");
* the compiler is left-to-right with no selectivity scheduling; the
  theorems quantify over its output only.
-/

namespace Semper.EMatch

/-! ## Index families (sketch (d), "Indexes") -/

/-- `by_op[f] = {n | op(n) = f}`. -/
def Graph.byOp (G : Graph) (f : Sym) : List NodeId :=
  (G.nodes.filter (fun p => p.2.op = f)).map (·.1)

/-- `by_repr[c] = {n | find(n) = c}`. -/
def Graph.byRepr (G : Graph) (c : C) : List NodeId :=
  (G.nodes.filter (fun p => G.find p.1 = c)).map (·.1)

/-- `by_child_pos[(pos, c)] = {n | the child of n at pos has class c}`. -/
def Graph.byChildPos (G : Graph) (pos : Nat) (c : C) : List NodeId :=
  (G.nodes.filter (fun p => p.2.children.childAt pos = some c)).map (·.1)

/-- `by_contains[c] = {n variadic | c is a child class of n}`. -/
def Graph.byContains (G : Graph) (c : C) : List NodeId :=
  (G.nodes.filter
    (fun p => p.2.children.isVariadic && p.2.children.containsClass c)).map (·.1)

/-- Node content by id. -/
def Graph.lookupNode (G : Graph) (id : NodeId) : Option Node :=
  (G.nodes.find? (fun p => p.1 = id)).map (·.2)

/-- A lookup of a `Join` step. Class keys are read from the binding. -/
inductive Lookup where
  | byOp (f : Sym)
  | byRepr (x : Var)
  | byChildPos (pos : Nat) (x : Var)
  | byContains (x : Var)
  deriving DecidableEq

/-- The bucket a lookup reads; `none` when its class variable is unbound. -/
def Lookup.bucket (G : Graph) (σ : Binding) : Lookup → Option (List NodeId)
  | .byOp f => some (G.byOp f)
  | .byRepr x => (σ.cls x).map G.byRepr
  | .byChildPos pos x => (σ.cls x).map (G.byChildPos pos)
  | .byContains x => (σ.cls x).map G.byContains

/-- The predicate a lookup serves (sketch (d), index exactness). -/
def Lookup.pred (G : Graph) (σ : Binding) : Lookup → NodeId → Prop
  | .byOp f, id => ∃ n, (id, n) ∈ G.nodes ∧ n.op = f
  | .byRepr x, id => (∃ n, (id, n) ∈ G.nodes) ∧ σ.cls x = some (G.find id)
  | .byChildPos pos x, id =>
      ∃ n c, (id, n) ∈ G.nodes ∧ σ.cls x = some c ∧
        n.children.childAt pos = some c
  | .byContains x, id =>
      ∃ n c, (id, n) ∈ G.nodes ∧ σ.cls x = some c ∧
        n.children.isVariadic = true ∧ n.children.containsClass c = true

/-- The class variables a lookup reads. -/
def Lookup.reads : Lookup → List Var
  | .byOp _ => []
  | .byRepr x => [x]
  | .byChildPos _ x => [x]
  | .byContains x => [x]

/-- The join: all node ids, filtered by membership in every bucket. An
unbound lookup yields no candidate. -/
def candidates (G : Graph) (σ : Binding) (ls : List Lookup) : List NodeId :=
  ls.foldl
    (fun acc l =>
      match l.bucket G σ with
      | some b => acc.filter (fun id => decide (id ∈ b))
      | none => [])
    (G.nodes.map (·.1))

/-! ## Multiplicity constraints -/

/-- `lo ≤ m ≤ hi`, with `hi = none` unbounded. -/
def inInterval (lo : Nat) (hi : Option Nat) (m : Nat) : Bool :=
  decide (lo ≤ m) && (match hi with | none => true | some h => decide (m ≤ h))

/-- `mult_matches` (`ematch.rs:2285-2300`): accept count `m` for the
annotation, binding a multiplicity variable on first use. -/
def multMatches (σ : Binding) : Mult → Nat → Option Binding
  | .exact k, m => if m = k then some σ else none
  | .var k lo hi, m =>
      if inInterval lo hi m then
        match σ.mult k with
        | some m' => if m' = m then some σ else none
        | none => some (σ.setMult k m)
      else none

/-! ## Decompositions -/

/-- The (class, count) entries of a multiset, in increasing class order. -/
def Multiset.entries (m : Multiset C) : List (C × Nat) :=
  (m.toFinset.sort (· ≤ ·)).map (fun c => (c, m.count c))

/-- Zero the count of class `c` in a residual. -/
def zeroEntry (c : C) (res : List (C × Nat)) : List (C × Nat) :=
  res.map (fun e => if e.1 = c then (c, 0) else e)

/-- The multiset of a residual. -/
def ofEntries (res : List (C × Nat)) : Multiset C :=
  (res.map (fun e => Multiset.replicate e.2 e.1)).sum

/-- `decompose_ac_elem` (`ematch.rs:2360-2470`): walk the elements over a
residual copy of the children; a bound element finds its class and checks
the count, an unbound element branches over every live entry; the rest
takes the live entries that remain. -/
def decomposeAC : List (Var × Mult) → Option Var → List (C × Nat) → Binding →
    List Binding
  | [], rest, res, σ =>
      let left := res.filter (fun e => e.2 ≠ 0)
      match rest with
      | none => if left.isEmpty then [σ] else []
      | some r => [σ.setRest r (ofEntries left)]
  | (x, μ) :: es, rest, res, σ =>
      match σ.cls x with
      | some c =>
          match res.find? (fun e => e.1 = c ∧ e.2 ≠ 0) with
          | some e =>
              match multMatches σ μ e.2 with
              | some σ' => decomposeAC es rest (zeroEntry c res) σ'
              | none => []
          | none => []
      | none =>
          res.flatMap (fun e =>
            if e.2 = 0 then []
            else
              match multMatches σ μ e.2 with
              | some σ' => decomposeAC es rest (zeroEntry e.1 res) (σ'.setCls x e.1)
              | none => [])

/-- The set analogue, counts all one. -/
def decomposeACI : List Var → Option Var → List C → Binding → List Binding
  | [], rest, res, σ =>
      match rest with
      | none => if res.isEmpty then [σ] else []
      | some r => [σ.setSetRest r res.toFinset]
  | x :: es, rest, res, σ =>
      match σ.cls x with
      | some c => if c ∈ res then decomposeACI es rest (res.erase c) σ else []
      | none => res.flatMap (fun c => decomposeACI es rest (res.erase c) (σ.setCls x c))

/-- Bind or check element variables against a list of classes, in order. -/
def bindElems : List Var → List C → Binding → Option Binding
  | [], [], σ => some σ
  | x :: xs, c :: cs, σ =>
      match σ.cls x with
      | some c' => if c' = c then bindElems xs cs σ else none
      | none => bindElems xs cs (σ.setCls x c)
  | _, _, _ => none

/-- Bind an optional sequence rest variable. -/
def bindSeq (r : Option Var) (u : List C) (σ : Binding) : Binding :=
  match r with
  | none => σ
  | some r => σ.setSeqRest r u

/-- `ExpandA`: every split of the children into prefix, `k` fixed positions
and suffix consistent with the rest variables (sketch (d)). -/
def expandA (pre : Option Var) (elems : List Var) (suf : Option Var)
    (cs : List C) (σ : Binding) : List Binding :=
  (List.range (cs.length + 1)).flatMap (fun k =>
    let u := cs.take k
    let tl := cs.drop k
    let mid := tl.take elems.length
    let v := tl.drop elems.length
    if mid.length ≠ elems.length then []
    else if pre.isNone ∧ u ≠ [] then []
    else if suf.isNone ∧ v ≠ [] then []
    else
      match bindElems elems mid σ with
      | none => []
      | some σ' => [bindSeq suf v (bindSeq pre u σ')])

/-- `DecomposeAC` on a commutative pair: both orders (sketch (d),
`RAtom::Comm`). -/
def decomposeComm (x y : Var) (a b : C) (σ : Binding) : List Binding :=
  (bindElems [x, y] [a, b] σ).toList ++ (bindElems [x, y] [b, a] σ).toList

/-! ## Plans and the interpreter -/

/-- Steps (`schedule.rs:60-135`, the subset the model covers). -/
inductive Step where
  | join (target : Var) (lookups : List Lookup)
  | extractChild (node : Var) (pos : Nat) (out : Var)
  | checkChildEq (node : Var) (pos : Nat) (x : Var)
  | checkEq (x y : Var)
  /-- `CopyBinding{target, other}` (`schedule.rs`, eager `Eq` lowering):
  bind the class of `target` to the class of `other`. -/
  | copyBinding (target other : Var)
  | decomposeAC (node : Var) (elems : List (Var × Mult)) (rest : Option Var)
  | decomposeACI (node : Var) (elems : List Var) (rest : Option Var)
  | expandA (node : Var) (pre : Option Var) (elems : List Var) (suf : Option Var)
  | decomposeComm (node : Var) (x y : Var)
  deriving DecidableEq

abbrev Plan := List Step

/-- Node bound to a node variable. -/
def Binding.nodeOf (σ : Binding) (G : Graph) (v : Var) : Option Node :=
  (σ.node v).bind G.lookupNode

/-- The write of a `Join` (`ematch.rs:2972`, spec §0): the engine's one
slot holds the node id, and its class is `canon(id) = G.find id`; in the
model the join writes both `node t` and `cls t`. -/
def joinBind (G : Graph) (σ : Binding) (t : Var) (id : NodeId) : Binding :=
  (σ.setNode t id).setCls t (G.find id)

/-- `NodeCls G σ`: every bound node variable has its class bound to the
representative of its node (spec §0). Preserved by every step. -/
def NodeCls (G : Graph) (σ : Binding) : Prop :=
  ∀ v id, σ.node v = some id → σ.cls v = some (G.find id)

/-- One step: enumerate candidates for an unbound variable or check a
condition on bound ones (`ematch.rs`, `run_step`). -/
def runStep (G : Graph) : Step → Binding → List Binding
  | .join t ls, σ => (candidates G σ ls).map (joinBind G σ t)
  | .extractChild v pos out, σ =>
      match σ.nodeOf G v with
      | some n =>
          match n.children.childAt pos with
          | some c =>
              match σ.cls out with
              | some c' => if c' = c then [σ] else []
              | none => [σ.setCls out c]
          | none => []
      | none => []
  | .checkChildEq v pos x, σ =>
      match σ.nodeOf G v, σ.cls x with
      | some n, some c => if n.children.childAt pos = some c then [σ] else []
      | _, _ => []
  | .checkEq x y, σ =>
      match σ.cls x, σ.cls y with
      | some a, some b => if a = b then [σ] else []
      | _, _ => []
  | .copyBinding t o, σ =>
      match σ.cls o with
      | some c =>
          match σ.cls t with
          | some c' => if c' = c then [σ] else []
          | none => [σ.setCls t c]
      | none => []
  | .decomposeAC v elems rest, σ =>
      match σ.nodeOf G v with
      | some ⟨_, .mset m⟩ => decomposeAC elems rest (Multiset.entries m) σ
      | _ => []
  | .decomposeACI v elems rest, σ =>
      match σ.nodeOf G v with
      | some ⟨_, .set s⟩ => decomposeACI elems rest (s.sort (· ≤ ·)) σ
      | _ => []
  | .expandA v pre elems suf, σ =>
      match σ.nodeOf G v with
      | some ⟨_, .seq cs⟩ => expandA pre elems suf cs σ
      | _ => []
  | .decomposeComm v x y, σ =>
      match σ.nodeOf G v with
      | some ⟨_, .spair a b⟩ => decomposeComm x y a b σ
      | _ => []

/-- Depth-first search over the plan. -/
def run (G : Graph) : Plan → Binding → List Binding
  | [], σ => [σ]
  | s :: ss, σ => (runStep G s σ).flatMap (run G ss)

/-! ## Plan well-formedness (sketch lemma 10, as a predicate) -/

/-- Variables a decomposition binds: element class variables, multiplicity
variables and the rest. -/
def acBinds (elems : List (Var × Mult)) (rest : Option Var) : List Var :=
  elems.map (·.1) ++
    elems.filterMap (fun e => match e.2 with | .var k _ _ => some k | _ => none) ++
    rest.toList

/-- `PlanWF B plan`: every variable a step reads is in the bound set `B`
when the step runs, and each binding step adds the variables it binds. -/
inductive PlanWF : List Var → Plan → Prop
  | nil {B : List Var} : PlanWF B []
  | join {B : List Var} {t : Var} {ls : List Lookup} {ss : Plan} :
      (∀ l ∈ ls, ∀ x ∈ l.reads, x ∈ B) → PlanWF (t :: B) ss →
      PlanWF B (.join t ls :: ss)
  | extractChild {B : List Var} {v out : Var} {pos : Nat} {ss : Plan} :
      v ∈ B → PlanWF (out :: B) ss → PlanWF B (.extractChild v pos out :: ss)
  | checkChildEq {B : List Var} {v x : Var} {pos : Nat} {ss : Plan} :
      v ∈ B → x ∈ B → PlanWF B ss → PlanWF B (.checkChildEq v pos x :: ss)
  | checkEq {B : List Var} {x y : Var} {ss : Plan} :
      x ∈ B → y ∈ B → PlanWF B ss → PlanWF B (.checkEq x y :: ss)
  | copyBinding {B : List Var} {t o : Var} {ss : Plan} :
      o ∈ B → PlanWF (t :: B) ss → PlanWF B (.copyBinding t o :: ss)
  | decomposeAC {B : List Var} {v : Var} {elems : List (Var × Mult)}
      {rest : Option Var} {ss : Plan} :
      v ∈ B → PlanWF (acBinds elems rest ++ B) ss →
      PlanWF B (.decomposeAC v elems rest :: ss)
  | decomposeACI {B : List Var} {v : Var} {elems : List Var}
      {rest : Option Var} {ss : Plan} :
      v ∈ B → PlanWF (elems ++ rest.toList ++ B) ss →
      PlanWF B (.decomposeACI v elems rest :: ss)
  | expandA {B : List Var} {v : Var} {pre suf : Option Var} {elems : List Var}
      {ss : Plan} :
      v ∈ B → PlanWF (pre.toList ++ elems ++ suf.toList ++ B) ss →
      PlanWF B (.expandA v pre elems suf :: ss)
  | decomposeComm {B : List Var} {v x y : Var} {ss : Plan} :
      v ∈ B → PlanWF (x :: y :: B) ss → PlanWF B (.decomposeComm v x y :: ss)

/-! ## A left-to-right compiler (sketch (d), "Atoms") -/

mutual
/-- The variables of a pattern. -/
def Pat.vars : Pat → List Var
  | .var x => [x]
  | .plain _ args => Pat.varsList args
  | .comm _ p q => p.vars ++ q.vars
  | .assoc _ pre args suf => pre.toList ++ Pat.varsList args ++ suf.toList
  | .ac _ elems rest => Pat.varsElems elems ++ rest.toList
  | .aci _ elems rest => Pat.varsList elems ++ rest.toList
def Pat.varsList : List Pat → List Var
  | [] => []
  | p :: ps => p.vars ++ Pat.varsList ps
def Pat.varsElems : List (Pat × Mult) → List Var
  | [] => []
  | (p, .var k _ _) :: es => p.vars ++ k :: Pat.varsElems es
  | (p, .exact _) :: es => p.vars ++ Pat.varsElems es
end

/-- The class variable of an element pattern: the variable itself, or a
fresh one for an application. -/
def elemVar (p : Pat) (fresh : Nat) : Var × Nat :=
  match p with
  | .var x => (x, fresh)
  | _ => (fresh, fresh + 1)

/-- Class variables of a list of element patterns. -/
def elemVars : List Pat → Nat → List Var × Nat
  | [], fresh => ([], fresh)
  | p :: ps, fresh =>
      let (v, fr₁) := elemVar p fresh
      let (vs, fr₂) := elemVars ps fr₁
      (v :: vs, fr₂)

/-- Class variables of AC element patterns, paired with their annotations. -/
def elemVarsAC : List (Pat × Mult) → Nat → List (Var × Mult) × Nat
  | [], fresh => ([], fresh)
  | (p, μ) :: es, fresh =>
      let (v, fr₁) := elemVar p fresh
      let (vs, fr₂) := elemVarsAC es fr₁
      ((v, μ) :: vs, fr₂)

/-- The join step of an application with head `f`, at the root or inside
the class bound to `cv`. -/
def joinStep (nv : Var) (f : Sym) (cv : Option Var) : Step :=
  .join nv (match cv with
    | some z => [.byRepr z, .byOp f]
    | none => [.byOp f])

mutual
/-- The compiler. `compileAt P cv fresh` compiles an application pattern
`P` whose node must lie in the class bound to `cv` (`none` at the root),
drawing fresh variables from `fresh` upward. It returns the plan and the
next fresh variable. The node variable of `P` is `fresh` itself. A root
variable pattern compiles to the empty plan. -/
def compileAt (P : Pat) (cv : Option Var) (fresh : Nat) : Plan × Nat :=
  match P with
  | .var x =>
      (match cv with | some z => [.checkEq z x] | none => [], fresh)
  | .plain f args =>
      let (s, fr) := compilePlainArgs args fresh 0 (fresh + 1)
      (joinStep fresh f cv :: s, fr)
  | .comm f p q =>
      let (vp, fr₁) := elemVar p (fresh + 1)
      let (vq, fr₂) := elemVar q fr₁
      let (sp, fr₃) := compileNested p vp fr₂
      let (sq, fr₄) := compileNested q vq fr₃
      (joinStep fresh f cv :: .decomposeComm fresh vp vq :: sp ++ sq, fr₄)
  | .assoc f pre args suf =>
      let (vs, fr₁) := elemVars args (fresh + 1)
      let (s, fr₂) := compileNestedList args vs fr₁
      (joinStep fresh f cv :: .expandA fresh pre vs suf :: s, fr₂)
  | .ac f elems rest =>
      let (vs, fr₁) := elemVarsAC elems (fresh + 1)
      let (s, fr₂) := compileNestedAC elems (vs.map (·.1)) fr₁
      (joinStep fresh f cv :: .decomposeAC fresh vs rest :: s, fr₂)
  | .aci f elems rest =>
      let (vs, fr₁) := elemVars elems (fresh + 1)
      let (s, fr₂) := compileNestedList elems vs fr₁
      (joinStep fresh f cv :: .decomposeACI fresh vs rest :: s, fr₂)
termination_by (sizeOf P, 0)
decreasing_by all_goals (simp_wf; omega)
/-- Plain arguments: extract each child into the argument's variable, then
compile a nested application. -/
def compilePlainArgs (args : List Pat) (nv : Var) (i : Nat) (fresh : Nat) :
    Plan × Nat :=
  match args with
  | [] => ([], fresh)
  | p :: ps =>
      let (v, fr₁) := elemVar p fresh
      let (sp, fr₂) := compileNested p v fr₁
      let (s, fr₃) := compilePlainArgs ps nv (i + 1) fr₂
      (.extractChild nv i v :: sp ++ s, fr₃)
termination_by (sizeOf args, 0)
decreasing_by all_goals (simp_wf; omega)
/-- Compile an element pattern bound to class variable `v`: nothing for a
variable, a nested plan for an application. -/
def compileNested (p : Pat) (v : Var) (fresh : Nat) : Plan × Nat :=
  match p with
  | .var _ => ([], fresh)
  | .plain f args => compileAt (.plain f args) (some v) fresh
  | .comm f p q => compileAt (.comm f p q) (some v) fresh
  | .assoc f pre args suf => compileAt (.assoc f pre args suf) (some v) fresh
  | .ac f elems rest => compileAt (.ac f elems rest) (some v) fresh
  | .aci f elems rest => compileAt (.aci f elems rest) (some v) fresh
termination_by (sizeOf p, 1)
decreasing_by all_goals (simp_wf; omega)
def compileNestedList (ps : List Pat) (vs : List Var) (fresh : Nat) :
    Plan × Nat :=
  match ps, vs with
  | p :: ps, v :: vs =>
      let (sp, fr₁) := compileNested p v fresh
      let (s, fr₂) := compileNestedList ps vs fr₁
      (sp ++ s, fr₂)
  | _, _ => ([], fresh)
termination_by (sizeOf ps, 0)
decreasing_by all_goals (simp_wf; omega)
def compileNestedAC (es : List (Pat × Mult)) (vs : List Var) (fresh : Nat) :
    Plan × Nat :=
  match es, vs with
  | (p, _) :: es, v :: vs =>
      let (sp, fr₁) := compileNested p v fresh
      let (s, fr₂) := compileNestedAC es vs fr₁
      (sp ++ s, fr₂)
  | _, _ => ([], fresh)
termination_by (sizeOf es, 0)
decreasing_by all_goals (simp_wf; omega)
end
/-- The plan of a root pattern, and its node variable. -/
def compile (P : Pat) (fresh : Nat) : Plan := (compileAt P none fresh).1

end Semper.EMatch
