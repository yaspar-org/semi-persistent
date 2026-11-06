import SemperProofs.EMatch.Ref

/-!
# E-matching, remaining plan steps: definitions

Section A of `spec-steps-env.md`: the plan steps the core model
(`Defs.lean`/`Ref.lean`) lacks: inequality (`CheckNeq`), globals
(`CheckEqGlobal`, `BindGlobal`), binding copies (`CopyBinding`), literals
(`ExtractLitVal`, `CheckLit`), predicates (`CheckPred`) and the sequence
pattern step (`Collect`).

Modelling choices:
* the binding is extended, not replaced: `XBinding` wraps a core `Binding`
  with the literal slots `lit` (`lit_vals`) and the literal columns
  `litSeq` (`lit_seq_pool`); a core step runs on the wrapped binding, so
  every theorem of `Main.lean` lifts (`runXStep_core`);
* the graph is extended likewise: `XGraph` wraps a `Graph` with the literal
  payload `litOf` (`get_lit_val_id`, `some` iff the node is a literal node)
  and the interpretation `litVal` (`eg.lits().get`);
* globals are a total map `Γ : GVar → C`, already canonical (A.0.2);
* a step's result is `XRes`: the emitted bindings, or a fault (A.7: an
  undefined guard; A.8.3: a `fill` error). An unbound literal slot read
  by a guard is a fault in the model (the engine reads a stale default
  value; `WF.lean` shows a well-formed plan never does);
* `Collect` is stratified over the ordinary engine: the sub-queries of the
  items are a `Source` of rows (`seq_collect.rs`, trait `Source`), a
  parameter of the spec; `Collect.lean` instantiates it from plans run by
  `runX` (the root drive's probe).
-/

namespace Semper.EMatch.Steps

open Semper.EMatch

/-- Interned literal id (`Cfg::V`). -/
abbrev Lit := Nat
/-- Literal value (`L`); a modelling abbreviation, only equality is used. -/
abbrev LVal := Nat
/-- Global variable (`PatVar::Global`). -/
abbrev GVar := Nat
/-- Guard primitive (`RPredExpr::App`'s `op`). -/
abbrev Prim := Nat

/-! ## Extended binding and graph -/

/-- The core binding with the literal slots and columns (A.0, rows
`lit_vals` and `lit_seq_pool`). -/
structure XBinding where
  base : Binding
  lit : Var → Option Lit
  litSeq : Var → Option (List Lit)

namespace XBinding

def empty : XBinding := ⟨Binding.empty, fun _ => none, fun _ => none⟩

/-- Replace the core binding. -/
def withBase (σ : XBinding) (b : Binding) : XBinding := { σ with base := b }

def setCls (σ : XBinding) (x : Var) (c : C) : XBinding := σ.withBase (σ.base.setCls x c)
def setNode (σ : XBinding) (v : Var) (id : NodeId) : XBinding :=
  σ.withBase (σ.base.setNode v id)
def setMult (σ : XBinding) (k : Var) (m : Nat) : XBinding :=
  σ.withBase (σ.base.setMult k m)
def setRest (σ : XBinding) (r : Var) (m : Multiset C) : XBinding :=
  σ.withBase (σ.base.setRest r m)
def setSeqRest (σ : XBinding) (r : Var) (u : List C) : XBinding :=
  σ.withBase (σ.base.setSeqRest r u)
def setSetRest (σ : XBinding) (r : Var) (s : Finset C) : XBinding :=
  σ.withBase (σ.base.setSetRest r s)
def setLit (σ : XBinding) (l : Var) (x : Lit) : XBinding :=
  { σ with lit := Function.update σ.lit l (some x) }
def setLitSeq (σ : XBinding) (l : Var) (xs : List Lit) : XBinding :=
  { σ with litSeq := Function.update σ.litSeq l (some xs) }

/-- `Extends σ σ'`: every entry bound in `σ` is bound to the same value in
`σ'`, on the core fields and the literal fields. -/
def Extends (σ σ' : XBinding) : Prop :=
  σ.base.Extends σ'.base ∧
  (∀ l x, σ.lit l = some x → σ'.lit l = some x) ∧
  (∀ l xs, σ.litSeq l = some xs → σ'.litSeq l = some xs)

theorem Extends.refl (σ : XBinding) : Extends σ σ :=
  ⟨Binding.Extends.refl _, fun _ _ h => h, fun _ _ h => h⟩

theorem Extends.trans {σ₁ σ₂ σ₃ : XBinding} (h₁ : Extends σ₁ σ₂) (h₂ : Extends σ₂ σ₃) :
    Extends σ₁ σ₃ :=
  ⟨h₁.1.trans h₂.1, fun l x h => h₂.2.1 l x (h₁.2.1 l x h),
    fun l xs h => h₂.2.2 l xs (h₁.2.2 l xs h)⟩

end XBinding

/-- The core graph with the literal payloads (A.0.3). -/
structure XGraph where
  G : Graph
  /-- `eg.get_lit_val_id(n)`: `some` iff `n` is a literal node. -/
  litOf : NodeId → Option Lit
  /-- `eg.lits().get(id)`. -/
  litVal : Lit → LVal

/-! ## Guards (A.7) -/

/-- `RPredExpr` (`resolve.rs:258-275`). -/
inductive PredExpr where
  | val (l : Var)
  | const (c : LVal)
  | app (f : Prim) (args : List PredExpr)

/-- The literal model a guard runs under: the primitives' evaluators
(`None` = undefined) and the truth test. -/
structure PredModel where
  evalPrim : Prim → List LVal → Option LVal
  truthy : LVal → Bool

mutual
/-- `eval_pred_expr` (`ematch.rs:2114-2140`); `none` is a fault. -/
def evalPred (X : XGraph) (M : PredModel) (σ : XBinding) : PredExpr → Option LVal
  | .val l => (σ.lit l).map X.litVal
  | .const c => some c
  | .app f args => (evalPreds X M σ args).bind (M.evalPrim f)
/-- Arguments, left to right. -/
def evalPreds (X : XGraph) (M : PredModel) (σ : XBinding) : List PredExpr → Option (List LVal)
  | [] => some []
  | a :: as => (evalPred X M σ a).bind (fun v => (evalPreds X M σ as).map (v :: ·))
end

mutual
/-- The literal variables a guard reads. -/
def PredExpr.litVars : PredExpr → List Var
  | .val l => [l]
  | .const _ => []
  | .app _ args => PredExpr.litVarsList args
def PredExpr.litVarsList : List PredExpr → List Var
  | [] => []
  | a :: as => a.litVars ++ PredExpr.litVarsList as
end

/-! ## Sequence patterns (A.8): the spec, the rows, the environments -/

/-- `MultCheck` (`seq_collect.rs:105-118`): the interval `[lo, hi]`, an
excluded value and the multiplicity variable's scalar slot. -/
structure MultCheck where
  lo : Nat
  hi : Nat
  ne : Option Nat
  slot : Option Nat
  deriving DecidableEq

def MultCheck.accepts (mc : MultCheck) (m : Nat) : Bool :=
  decide (mc.lo ≤ m) && decide (m ≤ mc.hi) && decide (mc.ne ≠ some m)

/-- `SItem`: a simple item (the `j`-th, with its multiplicity annotation),
the bare sequence, or the `i`-th filter. Names are indices. -/
inductive SItem where
  | one (j : Nat) (μ : Option MultCheck)
  | bare
  | filter (i : Nat)
  deriving DecidableEq

/-- `SFilter`: the number of variables of the filter's sub-pattern (its
columns; the multiplicity variable last when annotated), the `:except`
sibling, the annotation. -/
structure SFilter where
  nvars : Nat
  except : Option Nat
  mult : Option MultCheck
  deriving DecidableEq

/-- A scalar value of a match (`Value`, the non-sequence cases). -/
inductive Val where
  | cls (c : C)
  | lit (x : Lit)
  | count (m : Nat)
  deriving DecidableEq

/-- Variable slots, bound or not (`Slots`). -/
abbrev Slots := List (Option Val)

/-- The rows of the items' sub-queries (`Source`, `seq_collect.rs:148-166`):
`one j c sc` the rows of simple item `j` at class `c` joined with the
scalar slots `sc` (each row a full scalar vector extending `sc`);
`filter i c init` the rows of filter `i` at class `c` extending `init`
(the filter's slots with its multiplicity variable bound). -/
structure Source where
  one : Nat → C → Slots → List Slots
  filter : Nat → C → Slots → List Slots

/-- A filter's binding in a match: the children it took, their
multiplicities (AC only) and one column per variable. -/
structure FBind where
  elems : List C
  mults : List Nat
  cols : List (List (Option Val))
  deriving DecidableEq

/-- The bare sequence's binding. -/
structure BBind where
  elems : List C
  mults : List Nat
  deriving DecidableEq

/-- A match environment (`Env`), by layout rather than by name: the scalar
slots, one entry per filter (`none` when the filter was not bound: under A
a filter absent from the items), the bare sequence. Structural equality is
`env_eq`. -/
structure Env where
  scalars : Slots
  filt : List (Option FBind)
  bare : Option BBind
  deriving DecidableEq

/-- Where a scalar is written by `fill` (`ScalarRef`). -/
inductive ScalarRef where
  | node (v : Var)
  | lit (v : Var)
  | mult (v : Var)
  deriving DecidableEq

/-- Where a sequence's elements are written (`RestRef`), by the root kind. -/
inductive RestRef where
  | seq (v : Var)
  | set (v : Var)
  | mset (v : Var)
  deriving DecidableEq

/-- Where a filter column is written (`ColRef`); a multiplicity column is
carried by the elements' `mset` entry. -/
inductive ColRef where
  | node (v : Var)
  | lit (v : Var)
  | mult
  deriving DecidableEq

structure FilterLayout where
  elems : RestRef
  cols : List ColRef
  deriving DecidableEq

/-- The rule's layout (`Layout`, `seq_engine.rs`). -/
structure SeqLayout where
  scalars : List ScalarRef
  filters : List FilterLayout
  bare : Option RestRef
  deriving DecidableEq

/-- A sequence rule's left-hand side as `assemble` reads it (`Spec`), with
its root operator, its layout and its row source. The source is a
function of the graph and the globals: the sub-queries are ordinary
queries, run by the ordinary engine (`Collect.lean`, `Source.ofPlans`). -/
structure SeqSpec where
  op : Sym
  assoc : Bool
  ac : Bool
  items : List SItem
  filters : List SFilter
  nScalars : Nat
  layout : SeqLayout
  src : XGraph → (GVar → C) → Source

/-- `MAX_MATCHES`. -/
def MAX_MATCHES : Nat := 2 ^ 20

/-! ## Steps -/

/-- The extended step type: a core step, or one of the steps of section A. -/
inductive XStep where
  | core (s : Step)
  | checkNeq (x y : Var)
  | checkEqGlobal (x : Var) (g : GVar)
  | bindGlobal (x : Var) (g : GVar)
  | copyBinding (x y : Var)
  | extractLitVal (v : Var) (l : Var)
  | checkLit (v : Var) (c : LVal)
  | checkPred (p : PredExpr)
  | collect (v : Var) (S : SeqSpec)

abbrev XPlan := List XStep

/-- A step's outcome: the emitted bindings, or a fault. -/
inductive XRes where
  | ok (bs : List XBinding)
  | fault

end Semper.EMatch.Steps
