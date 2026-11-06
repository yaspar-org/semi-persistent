import Conform.Flatten.Case
import SemperProofs.EMatch.Flatten.RegroupDefs

/-!
# `:flatten` conformance generator: the oracle

A rule tagged `:flatten` runs the flattened plan of `PlanDefs.lean`, with the
fold-restricted views of `FoldPlan.lean` and the regrouped views of
`RegroupDefs.lean` (`runER`): the
pattern's atoms in post-order (`atoms P rootVar`), every n-ary atom joined
by operator, flattened into its own view register (`enumerateRD`: the walk's
records pruned by `takeableR`, regrouped with at most one regrouped class per
item) and decomposed on the view, the decomposition kept when the engine's demand rule
`DemandL.acceptsEB` accepts the classes it took. An untagged rule runs the
reference interpreter `run (compile P rootVar)` on the stored nodes, as in
`Conform.Oracle`. A match is the root class and the tag arguments
(`Conform.argsOf`).
-/

namespace ConformF

open Semper.EMatch Semper.EMatch.Flatten
open Conform (Gen chance Arg Match argsOf tagVars isClsVar isMultVar isAcRest isAciRest rootVar
  mutants rootsMerge childClasses)

/-- Matches of the flattened plan. -/
def matchesFlat (cs : FCase) : List Match :=
  let G := cs.graph
  let c : FCtx := ⟨G, fun _ => true, cs.lawsOf⟩
  (runER c cs.dirOf (planF (atoms cs.pat rootVar) ∅ 0) EEnv.empty).filterMap fun env => do
    let id ← env.σ.node rootVar
    let args ← argsOf cs.pat env.σ
    pure ⟨G.find id, args⟩

/-- The cost guard of a draw: the flattened plan run breadth-first (the same
steps as `runER`, level by level), giving up when a level holds more than
`envCap` environments, a `Flatten` step would enumerate more than
`enumCap` raw views over the level, or regroup past `regroupCap`. -/
def envCap : Nat := 5000
def enumCap : Nat := 30000

/-- Whether the regrouping of a `Flatten` step stays within the budget
`regroupCap` (`regroupLevelsCapped`); past it the engine may stop at its own
bounds, so a draw past the budget is redrawn. -/
def withinRegroupBudget (c : FCtx) (dir : Sym → Dir) (v : Var) (f : Sym) (κ : FlatKind)
    (items : List Var) (env : EEnv) : Bool :=
  match env.σ.nodeOf c.G v with
  | some n =>
      let ctx := c.ctx f κ
      let base := baseRecsR ctx (dir f) (c.laws f) n
      (regroupLevelsCapped ctx (dir f) (c.laws f) items.length regroupCap (regroupFuel base)
        (base.filter (keepRec κ (takeableR ctx env.σ items) (c.laws f)))).isSome
  | none => true

def affordable (cs : FCase) : Bool :=
  let G := cs.graph
  let c : FCtx := ⟨G, fun _ => true, cs.lawsOf⟩
  let rec go : List EStep → List EEnv → Bool
    | [], _ => true
    | s :: ss, envs =>
        let ok := match s with
          | .flatten v f κ _ items =>
              envs.length * max 1 ((viewCounts G f κ).foldl max 0) ≤ enumCap &&
                envs.all (fun env => withinRegroupBudget c cs.dirOf v f κ items env)
          | _ => true
        if !ok then false else
        let envs' := envs.flatMap (runEStepR c cs.dirOf s)
        if envs'.length > envCap then false else go ss envs'
  go (planF (atoms cs.pat rootVar) ∅ 0) [EEnv.empty]

/-- Matches on the stored nodes (untagged rule). -/
def matchesStored (cs : FCase) : List Match :=
  let G := cs.graph
  (run G (compile cs.pat rootVar) Binding.empty).filterMap fun σ => do
    let id ← σ.node rootVar
    let args ← argsOf cs.pat σ
    pure ⟨G.find id, args⟩

def expected (cs : FCase) : List Match :=
  (if cs.flatten then matchesFlat cs else matchesStored cs).eraseDups

/-- Expected matches per case beyond which a draw is redrawn: the program
carries one `check-eq` per match. -/
def matchCap : Nat := 400

/-- A case: up to twenty draws of the family, each kept when its views and
its match set are within the caps and its plan is `affordable`; for four cases in five the first sixteen
draws must also have a match (a `:flatten` draw matches rarely when the
pattern nests); past them, a control case. -/
def genCase (seed idx : Nat) : Gen FCase := do
  let fam := familyOf idx
  let wantMatch ← chance 4 5
  let mut out : Option FCase := none
  for i in List.range 20 do
    if out.isNone then
      match ← genOnce seed idx fam with
      | some c =>
          if c.flatten && !affordable c then continue
          let n := (expected c).length
          if n ≤ matchCap && (n > 0 || !wantMatch || i ≥ 16) then out := some c
      | none => pure ()
  match out with
  | some c => return c
  | none =>
      let c? ← genOnce seed idx .control
      return c?.getD ⟨seed, idx, .control, 2, 1, [], [], {}, none, .plain, .var 0, false⟩

/-- The case of a seed and an index, drawn from its own generator. -/
def caseOf (seed idx : Nat) : FCase :=
  (genCase seed idx).run' (mkStdGen (seed * 1000003 + idx + 77))

/-- Candidates at a node of the root operator built without matching, as
`Conform.naive`. -/
def naive (cs : FCase) : List Match :=
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

/-- Up to `limit` rejected candidates, as `Conform.rejected`. -/
def rejected (cs : FCase) (ms : List Match) (limit : Nat) : List Match :=
  if rootsMerge ms then [] else
  let all := ((ms.take 20).flatMap (mutants cs.classes) ++ naive cs).eraseDups
  (all.filter fun m => !(ms.any fun a => a.root = m.root ∧ a.args = m.args)).take limit

end ConformF
