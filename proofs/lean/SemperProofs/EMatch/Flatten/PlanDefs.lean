import SemperProofs.EMatch.Flatten.EngineRule
import SemperProofs.EMatch.Flatten.Interp
import SemperProofs.EMatch.Engine.Lower

/-!
# `:flatten` plans: every n-ary atom flattened, one view register each

The engine flattens **every** n-ary atom of a rule tagged `:flatten`
(`schedule.rs:1148-1165, 1246-1388`): the atom's join (no `by_contains`
filter, `schedule.rs:1520-1530`), then `Step::Flatten` writing the plan's
`k`-th register, then the decomposition reading that register
(`ematch.rs:1920-2047`). A `Comm` atom and a plain atom are lowered as
without the tag. This file defines that plan, executably, for any order of
the atoms (the scheduler's choice):

* `EEnv`: the binding and the register file (view, demand);
* `EStep`: reference steps, `flatten` (with the decomposition's item
  variables, from which the step computes `takeable`, `ematch.rs:1928-1944`),
  and the three view-reading decompositions;
* `runEStep`/`runE`: `run_step` with the pruned enumeration
  (`enumeratePrunedE`) and the engine's `Demand::accepts` (`acceptsEB`);
* `lowerF a B r`: one atom; `planF as B r`: the atoms in order, the `k`-th
  n-ary atom writing register `r + k`;
* `AtomSatF`: the semantics of one atom under `:flatten`: a plain or `Comm`
  atom as `AtomSat`; an n-ary atom matches its shallow pattern on some view
  of a stored node of its class whose demand accepts the item classes.

Theorems in `Plan.lean`.
-/

namespace Semper.EMatch.Flatten

open Semper.EMatch

/-- The binding and the view register file (`ematch.rs:486-492`): per
register, the view and its demand. -/
structure EEnv where
  σ : Binding
  views : Nat → Option (List (C × Nat) × DemandL)

/-- The empty environment. -/
def EEnv.empty : EEnv := ⟨Binding.empty, fun _ => none⟩

/-- Plan steps with the view mechanism. `flatten` carries the item variables
of the decomposition after it, which the engine reads off that next step
(`ematch.rs:1931-1935`). -/
inductive EStep where
  | base (s : Step)
  | flatten (node : Var) (f : Sym) (κ : FlatKind) (out : Nat) (items : List Var)
  | decomposeAC (node : Var) (elems : List (Var × Mult)) (rest : Option Var) (view : Nat)
  | decomposeACI (node : Var) (elems : List Var) (rest : Option Var) (view : Nat)
  | expandA (node : Var) (pre : Option Var) (elems : List Var) (suf : Option Var) (view : Nat)

/-- `takeable` (`ematch.rs:1937-1944`): when every item is bound, only
their classes; otherwise every class. An empty item list is all bound, so
nothing is takeable (spec §5 Q15). -/
def takeableOf (σ : Binding) (items : List Var) : C → Bool :=
  match items.mapM σ.cls with
  | some bound => fun c => decide (c ∈ bound)
  | none => fun _ => true

def EEnv.setView (env : EEnv) (r : Nat) (wd : List (C × Nat) × DemandL) : EEnv :=
  { env with views := Function.update env.views r (some wd) }

def EEnv.withBinding (env : EEnv) (σ : Binding) : EEnv := { env with σ := σ }

/-- The enumeration a `Flatten` step runs. `full ctx laws items n` is the
node's every view with its demand, for the decomposition's item variables
`items`; `pruned ctx laws σ items n` is what the step computes under the
binding `σ`, pruned by the `takeable` set it reads off `σ` and `items`. The
opening walk alone is `Enumerator.base`; with regrouped views,
`Enumerator.regroup` (`RegroupDefs.lean`). -/
structure Enumerator where
  full : Ctx → Laws → List Var → Node → List (List (C × Nat) × DemandL)
  pruned : Ctx → Laws → Binding → List Var → Node → List (List (C × Nat) × DemandL)

/-- The opening walk: `enumerateL`, pruned by `takeableOf`. -/
def Enumerator.base : Enumerator :=
  ⟨fun ctx laws _ n => enumerateL ctx laws n,
    fun ctx laws σ items n => enumeratePrunedE (takeableOf σ items) ctx laws n⟩

/-- `run_step` for the flattened plan, with the enumeration `E`. -/
def runEStepG (E : Enumerator) (c : FCtx) : EStep → EEnv → List EEnv
  | .base s, env => (runStep c.G s env.σ).map env.withBinding
  | .flatten v f κ out items, env =>
      match env.σ.nodeOf c.G v with
      | some n => (E.pruned (c.ctx f κ) (c.laws f) env.σ items n).map (env.setView out)
      | none => []
  | .decomposeAC _ elems rest r, env =>
      match env.views r with
      | some (w, d) =>
          ((decomposeAC elems rest w env.σ).filter
            (fun σ' => d.acceptsEB .ac (takenOf σ' (elems.map Prod.fst)))).map env.withBinding
      | none => []
  | .decomposeACI _ elems rest r, env =>
      match env.views r with
      | some (w, d) =>
          ((decomposeACI elems rest (w.map Prod.fst) env.σ).filter
            (fun σ' => d.acceptsEB .aci (takenOf σ' elems))).map env.withBinding
      | none => []
  | .expandA _ pre elems suf r, env =>
      match env.views r with
      | some (w, d) =>
          ((expandA pre elems suf (w.map Prod.fst) env.σ).filter
            (fun σ' => d.acceptsEB .assoc (takenOf σ' elems))).map env.withBinding
      | none => []

/-- Depth-first search over a flattened plan, with the enumeration `E`. -/
def runEG (E : Enumerator) (c : FCtx) : List EStep → EEnv → List EEnv
  | [], env => [env]
  | s :: ss, env => (runEStepG E c s env).flatMap (runEG E c ss)

/-- `run_step` for the flattened plan with the opening walk. -/
abbrev runEStep (c : FCtx) : EStep → EEnv → List EEnv := runEStepG Enumerator.base c

/-- Depth-first search over a flattened plan with the opening walk. -/
abbrev runE (c : FCtx) : List EStep → EEnv → List EEnv := runEG Enumerator.base c

/-- The `:flatten` kind of an atom's shape (`none`: plain, `Comm`). -/
def _root_.Semper.EMatch.Shape.flatKind : Shape → Option FlatKind
  | .assoc _ _ _ => some .assoc
  | .ac _ _ => some .ac
  | .aci _ _ => some .aci
  | _ => none

/-- The join of a flattened n-ary atom: `by_op`, and `by_repr` when the node
variable is bound; never `by_contains` (`schedule.rs:1520-1530`). -/
def flatJoin (a : RAtom) (B : Finset Var) : List Lookup :=
  if a.node ∈ B then [.byRepr a.node, .byOp a.op] else [.byOp a.op]

/-- One atom of a flattened query, its `Flatten` step writing register `r`. -/
def lowerF (a : RAtom) (B : Finset Var) (r : Nat) : List EStep :=
  match a.shape with
  | .assoc pre fx suf =>
      [.base (.join a.node (flatJoin a B)), .flatten a.node a.op .assoc r fx,
        .expandA a.node pre fx suf r]
  | .ac es rest =>
      [.base (.join a.node (flatJoin a B)), .flatten a.node a.op .ac r (es.map Prod.fst),
        .decomposeAC a.node es rest r]
  | .aci es rest =>
      [.base (.join a.node (flatJoin a B)), .flatten a.node a.op .aci r es,
        .decomposeACI a.node es rest r]
  | _ => (lower a B).map .base

/-- The register count an atom uses. -/
def regsOf (a : RAtom) : Nat := if a.shape.flatKind.isSome then 1 else 0

/-- A flattened plan: the atoms in the order the scheduler picked, each
lowered under the variables bound before it, the `k`-th n-ary atom writing
register `r + k` (`schedule.rs:1154-1158`). -/
def planF : List RAtom → Finset Var → Nat → List EStep
  | [], _, _ => []
  | a :: as, B, r => lowerF a B r ++ planF as (B ∪ a.binds) (r + regsOf a)

/-- Semantics of one atom under `:flatten`, with the enumeration `E`: a plain
or `Comm` atom as `AtomSat`; an n-ary atom matches its shallow pattern on
some view of `E.full` of a stored node of its class whose demand accepts the
item classes. -/
def AtomSatG (E : Enumerator) (c : FCtx) (σ : Binding) (a : RAtom) : Prop :=
  match a.shape.flatKind with
  | none => AtomSat c.G σ a
  | some κ =>
      ∃ id n, σ.node a.node = some id ∧ (id, n) ∈ c.G.nodes ∧
        σ.cls a.node = some (c.G.find id) ∧ n.op = a.op ∧
        ∃ w d, (w, d) ∈ E.full (c.ctx a.op κ) (c.laws a.op) a.elems n ∧
          MatchN c.G a.shallow ⟨a.op, ofView κ w⟩ σ ∧
          d.acceptsE κ (takenOf σ a.elems)

/-- Semantics of one atom under `:flatten` with the opening walk. -/
abbrev AtomSatF (c : FCtx) (σ : Binding) (a : RAtom) : Prop := AtomSatG Enumerator.base c σ a

end Semper.EMatch.Flatten
