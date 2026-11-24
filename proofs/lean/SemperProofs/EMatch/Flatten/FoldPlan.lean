import SemperProofs.EMatch.Flatten.Plan
import SemperProofs.EMatch.Flatten.Fold

/-!
# `:flatten` plans over folds: the spine-restricted enumerator

The executable model of the engine after the fold fix (`flatten::spine`):
the enumerator of `Laws.lean` with each child position allowed to open only
when it lies on the operator's spine (`Dir.left`: the first child of every
node, `Dir.right`: the last, `Dir.both`: every child). `runED` is `runE`
with the enumerator chosen by the operator's direction; it is what the
conformance oracle runs.

`rawOptD_both`, `enumerateLD_both`, `runED_both`: with every operator
`Dir.both` (no fold in the query) the restricted model is the proved one
(`runE`, `flatten_plan_sound`/`flatten_plan_complete`). For a fold, the
views are those of the spine trees (`OTLeft`/`OTRight`, `Fold.lean`), whose
term reading is the node's (`otLeft_sound`/`otRight_sound`).
-/

namespace Semper.EMatch.Flatten

open Semper.EMatch

/-- An operator's fold direction (`registry::AssocDir`). -/
inductive Dir where
  | both
  | left
  | right
  deriving DecidableEq, Repr

/-- `flatten::spine`: may position `i` of `len` children open? -/
def spineB : Dir → Nat → Nat → Bool
  | .both, _, _ => true
  | .left, i, _ => i == 0
  | .right, i, len => i + 1 == len

/-- `kidsOfL` with each position's index, so the option function knows
whether the position may open. -/
def kidsOfD (opt : Bool → C → Nat → Finset C → List RawL) (dir : Dir) (len : Nat) :
    List (C × Nat) → Nat → Nat → Finset C → List RawL
  | [], _, _, _ => [([], [])]
  | (X, j) :: rest, i, k, P =>
      (opt (spineB dir i len) X (k * j) P).flatMap (fun r₁ =>
        (kidsOfD opt dir len rest (i + 1) k P).map (fun r₂ => (r₁.1 ++ r₂.1, r₁.2 ++ r₂.2)))

/-- `rawOptL` with the spine restriction: a position off the spine is kept. -/
def rawOptD (ctx : Ctx) (dir : Dir) : Nat → Bool → C → Nat → Finset C → List RawL
  | 0, _, X, k, _ => [([(X, k)], [])]
  | fuel + 1, b, X, k, P =>
      ([(X, k)], []) ::
        (if b = false ∨ X ∈ P then []
         else (ctx.members X).flatMap (fun p =>
           (kidsOfD (rawOptD ctx dir fuel) dir (kids ctx.κ p.2.children).length
              (kids ctx.κ p.2.children) 0 k (insert X P)).map
             (fun r => (r.1, leafifyL X k r.1 r.2))))

def rawNodeD (ctx : Ctx) (dir : Dir) (fuel : Nat) (m : Node) (k : Nat) (P : Finset C) :
    List RawL :=
  kidsOfD (rawOptD ctx dir fuel) dir (kids ctx.κ m.children).length (kids ctx.κ m.children) 0 k P

def rawRecordsLD (ctx : Ctx) (dir : Dir) (laws : Laws) (n : Node) : List RecL :=
  (rawNodeD ctx dir (fuelOf ctx.G) n 1 ∅).filterMap (fun r =>
    match normalize ctx.κ laws r.1 with
    | .node w => some (w, flagLeaves ctx.κ laws r.1 r.2)
    | _ => none)

def enumerateLD (ctx : Ctx) (dir : Dir) (laws : Laws) (n : Node) :
    List (List (C × Nat) × DemandL) :=
  enumerateFromL (rawRecordsLD ctx dir laws n)

def enumeratePrunedED (T : C → Bool) (ctx : Ctx) (dir : Dir) (laws : Laws) (n : Node) :
    List (List (C × Nat) × DemandL) :=
  enumerateFromL ((rawRecordsLD ctx dir laws n).filter
    (fun r => r.2.all (fun lf => keepLeaf ctx.κ T laws lf.1)))

/-! ## `Dir.both` is the proved enumerator -/

theorem kidsOfD_both (opt : Bool → C → Nat → Finset C → List RawL) (len : Nat) :
    ∀ (ks : List (C × Nat)) (i k : Nat) (P : Finset C),
      kidsOfD opt .both len ks i k P = kidsOfL (opt true) ks k P
  | [], _, _, _ => rfl
  | (X, j) :: rest, i, k, P => by
      simp only [kidsOfD, kidsOfL, spineB, kidsOfD_both opt len rest (i + 1) k P]

theorem rawOptD_both (ctx : Ctx) :
    ∀ (fuel : Nat), rawOptD ctx .both fuel true = rawOptL ctx fuel
  | 0 => rfl
  | fuel + 1 => by
      funext X k P
      simp only [rawOptD, rawOptL, kidsOfD_both, rawOptD_both ctx fuel]
      simp

theorem rawNodeD_both (ctx : Ctx) (fuel : Nat) (m : Node) (k : Nat) (P : Finset C) :
    rawNodeD ctx .both fuel m k P = rawNodeL ctx fuel m k P := by
  simp only [rawNodeD, rawNodeL, kidsOfD_both, rawOptD_both]

theorem enumerateLD_both (ctx : Ctx) (laws : Laws) (n : Node) :
    enumerateLD ctx .both laws n = enumerateL ctx laws n := by
  unfold enumerateLD rawRecordsLD
  rw [rawNodeD_both]
  rfl

theorem enumeratePrunedED_both (T : C → Bool) (ctx : Ctx) (laws : Laws) (n : Node) :
    enumeratePrunedED T ctx .both laws n = enumeratePrunedE T ctx laws n := by
  unfold enumeratePrunedED rawRecordsLD
  rw [rawNodeD_both]
  rfl

/-! ## The interpreter with fold directions -/

/-- `runEStep` with the enumerator of each operator's direction. -/
def runEStepD (c : FCtx) (dir : Sym → Dir) : EStep → EEnv → List EEnv
  | .flatten v f κ out items, env =>
      match env.σ.nodeOf c.G v with
      | some n =>
          (enumeratePrunedED (takeableOf env.σ items) (c.ctx f κ) (dir f) (c.laws f) n).map
            (env.setView out)
      | none => []
  | s, env => runEStep c s env

def runED (c : FCtx) (dir : Sym → Dir) : List EStep → EEnv → List EEnv
  | [], env => [env]
  | s :: ss, env => (runEStepD c dir s env).flatMap (runED c dir ss)

theorem runEStepD_both (c : FCtx) (s : EStep) (env : EEnv) :
    runEStepD c (fun _ => .both) s env = runEStep c s env := by
  cases s with
  | flatten v f κ out items =>
      simp only [runEStepD, runEStep, enumeratePrunedED_both]
      rfl
  | _ => rfl

/-- **With no fold, the fold-aware interpreter is the proved one.** -/
theorem runED_both (c : FCtx) : ∀ (ss : List EStep) (env : EEnv),
    runED c (fun _ => .both) ss env = runE c ss env
  | [], _ => rfl
  | s :: ss, env => by
      simp only [runED, runE, runEStepD_both]
      congr 1
      funext env₁
      exact runED_both c ss env₁

end Semper.EMatch.Flatten
