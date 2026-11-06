import SemperProofs.EMatch.Proofs.Interp

/-!
# Engine atoms (spec-scheduler §1.2, §1.3)

The resolved atoms of the Semper matcher restricted to the scanning atoms
this development covers: `Plain`, `Comm`, the four A shapes, `ACExact`/`ACSub`
and `ACIExact`/`ACISub`. An atom is a node variable, an operator and a shape
whose element positions are class *variables* (a nested application is its
own atom, re-joined through the shared variable).

`AtomSat G σ a` is the semantics of one atom: the node variable is bound to
a stored node of the atom's operator, its class variable to the node's
representative, and the node matches the atom's *shallow* pattern (the
application pattern with variable arguments) under `MatchN`.

`atoms P r` is the post-order flattening of a pattern (spec §1.1): one atom
per application node, children before parents, node variables drawn above
every variable of the pattern.
-/

namespace Semper.EMatch

/-- The shape of a resolved scanning atom: its element class variables and
annotations, by operator kind. -/
inductive Shape where
  /-- `Plain{children}`: one variable per argument position. -/
  | plain (cs : List Var)
  /-- `Comm{elems = [(a,1),(b,1)]}`. -/
  | comm (a b : Var)
  /-- `AExact / APrefix / ASuffix / ABoth`: optional prefix rest, fixed
  positions, optional suffix rest. -/
  | assoc (pre : Option Var) (fixed : List Var) (suf : Option Var)
  /-- `ACExact / ACSub`: elements with multiplicities, optional multiset rest. -/
  | ac (elems : List (Var × Mult)) (rest : Option Var)
  /-- `ACIExact / ACISub`: elements, optional set rest. -/
  | aci (elems : List Var) (rest : Option Var)
  deriving DecidableEq

/-- A resolved scanning atom (`RAtom` in `resolve.rs`). -/
structure RAtom where
  node : Var
  op : Sym
  shape : Shape
  deriving DecidableEq

namespace RAtom

/-- The shallow pattern of an atom: the application with variable arguments
(spec §1.3). -/
def shallow (a : RAtom) : Pat :=
  match a.shape with
  | .plain cs => .plain a.op (cs.map .var)
  | .comm x y => .comm a.op (.var x) (.var y)
  | .assoc pre fx suf => .assoc a.op pre (fx.map .var) suf
  | .ac es rest => .ac a.op (es.map fun e => (.var e.1, e.2)) rest
  | .aci es rest => .aci a.op (es.map .var) rest

/-- The element class variables (children, pair, fixed positions, elements). -/
def elems (a : RAtom) : List Var :=
  match a.shape with
  | .plain cs => cs
  | .comm x y => [x, y]
  | .assoc _ fx _ => fx
  | .ac es _ => es.map (·.1)
  | .aci es _ => es

/-- The multiplicity variables of an AC atom. -/
def multVars (a : RAtom) : List Var :=
  match a.shape with
  | .ac es _ => Semper.EMatch.multVars es
  | _ => []

/-- The sequence rest variables (prefix, suffix) of an A atom. -/
def seqRestVars (a : RAtom) : List Var :=
  match a.shape with
  | .assoc pre _ suf => pre.toList ++ suf.toList
  | _ => []

/-- The multiset rest variable of an AC atom. -/
def msetRestVars (a : RAtom) : List Var :=
  match a.shape with
  | .ac _ rest => rest.toList
  | _ => []

/-- The set rest variable of an ACI atom. -/
def setRestVars (a : RAtom) : List Var :=
  match a.shape with
  | .aci _ rest => rest.toList
  | _ => []

/-- All rest variables. -/
def restVars (a : RAtom) : List Var := a.seqRestVars ++ a.msetRestVars ++ a.setRestVars

/-- The class variables the lowering of the atom binds (spec §3.1,
`binds a B = {n} ∪ locals(children/elements)`); multiplicity and rest
variables are not tracked in the bound set. -/
def binds (a : RAtom) : Finset Var := insert a.node a.elems.toFinset

/-- Every variable the atom mentions. -/
def vars (a : RAtom) : List Var := a.node :: a.elems ++ a.multVars ++ a.restVars

end RAtom

/-- Semantics of one atom (spec §1.3). -/
def AtomSat (G : Graph) (σ : Binding) (a : RAtom) : Prop :=
  ∃ id n, σ.node a.node = some id ∧ (id, n) ∈ G.nodes ∧ σ.cls a.node = some (G.find id) ∧
    n.op = a.op ∧ MatchN G a.shallow n σ

/-! ## Flattening (spec §1.1) -/

/-! The class variable of a child pattern and its atoms: a variable is
itself, with no atom; an application gets the fresh node variable `fresh`
and is flattened at it with the counter advanced. Children are flattened
before the parent's atom is pushed (post-order). -/
mutual
/-- Atoms of an application pattern `P` whose node variable is `n`,
drawing fresh variables from `fresh` upward; returns the atoms in
post-order and the next fresh variable. A variable pattern has no atom. -/
def atomsAt (P : Pat) (n : Var) (fresh : Nat) : List RAtom × Nat :=
  match P with
  | .var _ => ([], fresh)
  | .plain f args =>
      let (vs, as, fr) := atomsChildren args fresh
      (as ++ [⟨n, f, .plain vs⟩], fr)
  | .comm f p q =>
      let (vp, ap, fr₁) := atomsChild p fresh
      let (vq, aq, fr₂) := atomsChild q fr₁
      (ap ++ aq ++ [⟨n, f, .comm vp vq⟩], fr₂)
  | .assoc f pre args suf =>
      let (vs, as, fr) := atomsChildren args fresh
      (as ++ [⟨n, f, .assoc pre vs suf⟩], fr)
  | .ac f elems rest =>
      let (vs, as, fr) := atomsChildrenAC elems fresh
      (as ++ [⟨n, f, .ac vs rest⟩], fr)
  | .aci f elems rest =>
      let (vs, as, fr) := atomsChildren elems fresh
      (as ++ [⟨n, f, .aci vs rest⟩], fr)
termination_by (sizeOf P, 1)
decreasing_by all_goals (simp_wf; omega)
/-- One child: its class variable, its atoms, the next fresh variable. -/
def atomsChild (p : Pat) (fresh : Nat) : Var × List RAtom × Nat :=
  match p with
  | .var x => (x, [], fresh)
  | .plain f args =>
      let (as, fr) := atomsAt (.plain f args) fresh (fresh + 1)
      (fresh, as, fr)
  | .comm f p q =>
      let (as, fr) := atomsAt (.comm f p q) fresh (fresh + 1)
      (fresh, as, fr)
  | .assoc f pre args suf =>
      let (as, fr) := atomsAt (.assoc f pre args suf) fresh (fresh + 1)
      (fresh, as, fr)
  | .ac f elems rest =>
      let (as, fr) := atomsAt (.ac f elems rest) fresh (fresh + 1)
      (fresh, as, fr)
  | .aci f elems rest =>
      let (as, fr) := atomsAt (.aci f elems rest) fresh (fresh + 1)
      (fresh, as, fr)
termination_by (sizeOf p, 2)
decreasing_by all_goals (simp_wf; omega)
def atomsChildren (ps : List Pat) (fresh : Nat) : List Var × List RAtom × Nat :=
  match ps with
  | [] => ([], [], fresh)
  | p :: ps =>
      let (v, ap, fr₁) := atomsChild p fresh
      let (vs, as, fr₂) := atomsChildren ps fr₁
      (v :: vs, ap ++ as, fr₂)
termination_by (sizeOf ps, 0)
decreasing_by all_goals (simp_wf; omega)
def atomsChildrenAC (es : List (Pat × Mult)) (fresh : Nat) :
    List (Var × Mult) × List RAtom × Nat :=
  match es with
  | [] => ([], [], fresh)
  | (p, μ) :: es =>
      let (v, ap, fr₁) := atomsChild p fresh
      let (vs, as, fr₂) := atomsChildrenAC es fr₁
      ((v, μ) :: vs, ap ++ as, fr₂)
termination_by (sizeOf es, 0)
decreasing_by all_goals (simp_wf; omega)
end

/-- A bound above every variable of `P` and above `r`. -/
def Pat.freshAbove (P : Pat) (r : Var) : Nat := (P.vars.foldr max r) + 1

/-- The atoms of a root application pattern `P` with root node variable `r`
(spec §1.1, §1.3): post-order, node variables above `P.vars` and `r`. -/
def atoms (P : Pat) (r : Var) : List RAtom := (atomsAt P r (P.freshAbove r)).1

/-- Two bindings agree on the variables `V` on every map but `node`. -/
def AgreeOn (V : List Var) (σ σ' : Binding) : Prop :=
  ∀ x ∈ V, σ.cls x = σ'.cls x ∧ σ.mult x = σ'.mult x ∧ σ.rest x = σ'.rest x ∧
    σ.seqRest x = σ'.seqRest x ∧ σ.finRest x = σ'.finRest x

end Semper.EMatch
