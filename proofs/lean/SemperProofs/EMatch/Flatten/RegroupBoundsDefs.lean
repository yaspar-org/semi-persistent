import SemperProofs.EMatch.Flatten.RegroupSkipDefs
import SemperProofs.EMatch.Flatten.Regroup

/-!
# `:flatten`: the engine's regrouping with its bounds

`RegroupSkipDefs.lean` models the engine's regrouping loop
(`FlattenScratch::regroup`, `flatten.rs`) with its skips and no bound. The
engine also counts and bounds its work per node. This file adds the
counters, checked where the engine checks them:

* `views` counts the regrouped records added, after the three skips and the
  signature deduplication: incremented once per record about to be added,
  then checked against `MAX_REGROUP_VIEWS` (`maxRegroupViews`, 2^14); past
  it, the run stops before adding the record (`BSt.addRec`);
* `work` counts the candidates examined: when a view is popped (after it is
  marked), the length of the use list `by_contains[c]` of each distinct class
  `c` of the view (`Ix.useLen`), every member of any operator, then, per
  candidate group (an `f`-member over a class of the view), the length of its
  children list, each checked against `MAX_REGROUP_WORK`
  (`maxRegroupWork`, 2^20) before the group's fits are read. The engine adds
  the use-list lengths one at a time and checks after each; the counter is
  at most the bound when the view is popped, so the run stops there iff the
  sum is past the bound, which is the check `BSt.regroupView` makes once; a
  target created and then skipped (an unconditional record) still costs its
  source's work;
* `elems` and `gelems` count the stored view elements (`elems`) and leaf
  elements (`group_elems`), from the walk's records (`BSt.init`): a new target
  is checked (`elems + |t| > MAX_ELEMS`) before it is stored, and a record
  (`gelems + elems > MAX_ELEMS`) after the `views` check and before its leaves
  are stored. Past `MAX_ELEMS` (`maxElems`, 2^24) the engine returns
  `OVER_BOUND`: the node is skipped and counted in `flatten_skipped`, not in
  `flatten_regroup_truncated` (`Halt.overBound`);
* `ovf` counts the fits whose normalization overflows the configured
  multiplicity width (`Normal::Overflow`): the fit is skipped and counted
  (`Ix.wide`, a predicate on the raw fit: the model's counts are `Nat`).

Truncation (`Halt.truncated`) and `OVER_BOUND` stop the run at once; the
records added so far are kept (`BSt.records`). Every step on a stopped run is
the identity.

The bounds are parameters (`Bounds`, `none` for no bound): `Bounds.engine`
is the engine's, `Bounds.none` counts without stopping, so that the stopping
condition can be compared with the totals of the run that does not stop
(`RegroupBounds.lean`).

`enumerateRDBounded` is `Step::Flatten` (`ematch.rs`) with these bounds: the
takeable set with the engine's cap on the closure (`takeableRCap`), the
walk's records pruned by it, regrouped when the decomposition has items or
the laws can drop a class (`canDrop`, `laws_drop` in `enumerate`), within the
item limit, the distinct views. `runB` runs a flattened plan with it and sums the three per-query
counters of `MatchPool` (`flatten_regroup_truncated`, `flatten_skipped`,
`flatten_overflowed`) over its `Flatten` steps.
-/

namespace Semper.EMatch.Flatten

open Semper.EMatch

/-- `MAX_REGROUP_VIEWS`: regrouped records added at one node. -/
def maxRegroupViews : Nat := 2 ^ 14

/-- `MAX_REGROUP_WORK`: regrouping candidates examined at one node. -/
def maxRegroupWork : Nat := 2 ^ 20

/-- `MAX_ELEMS`: view and leaf elements stored for one node. -/
def maxElems : Nat := 2 ^ 24

/-- The cap on the takeable closure (`CAP` in `Step::Flatten`, `ematch.rs`). -/
def takeCap : Nat := 4096

/-- Bounds of a run; `none` is no bound. -/
structure Bounds where
  views : Option Nat
  work : Option Nat
  elems : Option Nat

/-- The engine's bounds. -/
def Bounds.engine : Bounds := ⟨some maxRegroupViews, some maxRegroupWork, some maxElems⟩

/-- No bound: the run counts and never stops. -/
def Bounds.none : Bounds := ⟨Option.none, Option.none, Option.none⟩

/-- `x` is past the bound `b`. -/
def pastB : Option Nat → Nat → Bool
  | some b, x => decide (b < x)
  | Option.none, _ => false

/-- Why a run stopped: a regrouping bound (`regroup_truncated`, the node's
views found so far are matched) or `MAX_ELEMS` (`OVER_BOUND`, the node is
skipped). -/
inductive Halt where
  | truncated
  | overBound
  deriving DecidableEq, Repr

/-- What the bounded run reads of the round's snapshot beyond the model's
graph: the length of the use list `by_contains[c]` (every variadic member
over `c`, any operator, each node once), and whether the normalization of a
raw fit overflows the configured multiplicity width under the given laws. -/
structure Ix where
  useLen : C → Nat
  wide : Laws → List (C × Nat) → Bool

/-- The model's widths: no count overflows. -/
def Ix.nat (useLen : C → Nat) : Ix := ⟨useLen, fun _ _ => false⟩

/-- The leaf elements a record stores (`group_elems`). -/
def leafElems (r : RecR) : Nat := (r.2.1.map (fun l => l.1.L.length)).sum

/-- The state of the bounded loop: the loop's state and the counters.
`peak` is the largest element count the `MAX_ELEMS` checks have read. -/
structure BSt where
  st : SkipSt
  views : Nat
  work : Nat
  elems : Nat
  gelems : Nat
  peak : Nat
  ovf : Nat
  halt : Option Halt

/-- Add one derived record to the target `t`: dropped when `t` has its
signature; otherwise counted and checked against the views bound, then the
elements bound, then stored. -/
def BSt.addRec (B : Bounds) (t : View) (b : BSt) (d : RecR) : BSt :=
  if b.halt.isSome then b else
  if (b.st.sigs t).any (RecSig.same (recSig d)) then b else
  if pastB B.views (b.views + 1) then { b with views := b.views + 1, halt := some .truncated } else
  if pastB B.elems (b.gelems + b.elems) then
    { b with
      views := b.views + 1
      peak := max b.peak (b.gelems + b.elems)
      halt := some .overBound } else
  { b with
    views := b.views + 1
    peak := max b.peak (b.gelems + b.elems)
    gelems := b.gelems + leafElems d
    st := b.st.addRec t d }

/-- Enter a new target: checked against the elements bound, then stored. -/
def BSt.enterTarget (B : Bounds) (t : View) (b : BSt) : BSt :=
  if b.halt.isSome then b else
  if t ∈ b.st.order then b else
  if pastB B.elems (b.elems + t.length) then
    { b with peak := max b.peak (b.elems + t.length), halt := some .overBound } else
  { b with
    peak := max b.peak (b.elems + t.length)
    elems := b.elems + t.length
    st := { b.st with order := b.st.order ++ [t] } }

/-- One target of a source (`SkipSt.addTarget`, with the bounds). -/
def BSt.addTarget (B : Bounds) (b : BSt) (t : View) (ds : List RecR) : BSt :=
  if b.halt.isSome then b else
  let b := b.enterTarget B t
  if b.halt.isSome then b else
  if (b.st.recs t).any RecR.uncond then b else ds.foldl (BSt.addRec B t) b

/-- One fit (`SkipSt.fitStep`): a fit whose normalization overflows the
width is counted and skipped. -/
def BSt.fitStep (B : Bounds) (ix : Ix) (ctx : Ctx) (laws : Laws) (w : View)
    (gg : C × List (C × Nat)) (b : BSt) (raw : List (C × Nat)) : BSt :=
  if b.halt.isSome then b else
  if ix.wide laws raw then { b with ovf := b.ovf + 1 } else
  match normalize ctx.κ laws raw with
  | .node t => b.addTarget B t ((srcRecs (b.st.recs w)).map (deriveRec t gg.1 (gg.2.map Prod.fst)))
  | _ => b

/-- The group `gg` is a candidate of the view `w`: a member over a class of
`w`, so on the use list of that class. -/
def isCand (w : View) (gg : C × List (C × Nat)) : Bool :=
  gg.2.any (fun e => decide (e.1 ∈ w.map Prod.fst))

/-- The candidates of the view `w` as the engine gathers them: the filed
`f`-members on the use list `by_contains[c]` of a class `c` of the view,
that is, holding a class of the view, sorted by node id. -/
def groupsOfEngineAt (ctx : Ctx) (w : View) : List (C × List (C × Nat)) :=
  (groupsOfEngine ctx).filter (isCand w)

/-- The engine's regrouping with the candidates of each view read from the
use lists of its classes (`regroupAllSkip` reads every filed `f`-member for
every view; `regroupAllSkipAt_eq`, `RegroupBounds.lean`, equates them). -/
def regroupAllSkipAt (ctx : Ctx) (dir : Dir) (laws : Laws) (base : List RecR) : List RecR :=
  (SkipSt.runAt ctx dir laws (groupsOfEngineAt ctx) (skipFuel ctx dir laws base)
    (SkipSt.init base)).records

/-- One candidate group (`SkipSt.groupStep`): its children counted and
checked against the work bound, then every fit. A group that is not a
candidate is not examined. -/
def BSt.groupStep (B : Bounds) (ix : Ix) (ctx : Ctx) (dir : Dir) (laws : Laws) (w : View)
    (b : BSt) (gg : C × List (C × Nat)) : BSt :=
  if b.halt.isSome then b else
  if !isCand w gg then b else
  if pastB B.work (b.work + gg.2.length) then
    { b with work := b.work + gg.2.length, halt := some .truncated } else
  (fitsR ctx.κ dir w gg.1 gg.2).foldl (BSt.fitStep B ix ctx laws w gg)
    { b with work := b.work + gg.2.length }

/-- The use lists read when the view `w` is popped: one per distinct class. -/
def useWork (ix : Ix) (w : View) : Nat := ((w.map Prod.fst).dedup.map ix.useLen).sum

/-- Regroup the view `w` (`SkipSt.regroupView`): its use lists counted and
checked against the work bound, then every candidate group. -/
def BSt.regroupView (B : Bounds) (ix : Ix) (ctx : Ctx) (dir : Dir) (laws : Laws)
    (gs : List (C × List (C × Nat))) (w : View) (b : BSt) : BSt :=
  if b.halt.isSome then b else
  if pastB B.work (b.work + useWork ix w) then
    { b with work := b.work + useWork ix w, halt := some .truncated } else
  gs.foldl (BSt.groupStep B ix ctx dir laws w) { b with work := b.work + useWork ix w }

/-- Mark `w` regrouped. -/
def BSt.mark (b : BSt) (w : View) : BSt := { b with st := b.st.mark w }

/-- The loop (`SkipSt.run`), stopping at a bound. -/
def BSt.run (B : Bounds) (ix : Ix) (ctx : Ctx) (dir : Dir) (laws : Laws)
    (gs : List (C × List (C × Nat))) : Nat → BSt → BSt
  | 0, b => b
  | n + 1, b =>
      if b.halt.isSome then b else
      match b.st.next with
      | Option.none => b
      | some w => BSt.run B ix ctx dir laws gs n (BSt.regroupView B ix ctx dir laws gs w (b.mark w))

/-- The state after the walk: its records entered, their view and leaf
elements stored. -/
def BSt.init (base : List RecR) : BSt :=
  ⟨SkipSt.init base, 0, 0, (base.map (fun r => r.1.length)).sum, (base.map leafElems).sum, 0, 0,
    Option.none⟩

/-- The bounded regrouping of the walk's records `base`, candidates `gs`. -/
def regroupBoundedG (B : Bounds) (ix : Ix) (ctx : Ctx) (dir : Dir) (laws : Laws)
    (gs : List (C × List (C × Nat))) (base : List RecR) : BSt :=
  BSt.run B ix ctx dir laws gs (skipFuel ctx dir laws base) (BSt.init base)

/-- `takeable` with the engine's cap (`Step::Flatten`, `ematch.rs`): when
every item is bound, the closure of their classes below through
`f`-members, unless an insertion takes it past `takeCap` classes, in which
case every class (as `takeableR` when the closure does not close). -/
def takeableRCap (ctx : Ctx) (σ : Binding) (items : List Var) : C → Bool :=
  match items.mapM σ.cls with
  | some bound =>
      let S := belowIter ctx ((classesOf ctx.G).card + 1) bound
      if belowStep ctx S ⊆ S ∧ ¬(takeCap < S.length ∧ bound.dedup.length < S.length) then
        fun c => decide (c ∈ S)
      else fun _ => true
  | Option.none => fun _ => true

/-- The outcome of one `Step::Flatten` evaluation: its views, whether
regrouping was truncated, whether the node was skipped (`OVER_BOUND`), and
the fits skipped for the width. -/
structure BOut where
  views : List (List (C × Nat) × DemandL)
  truncated : Bool
  skipped : Bool
  ovf : Nat

/-- `enumerate` with regrouping and its bounds: the walk's records pruned by
`T`, regrouped when `limit > 0` or the laws can drop a class (`canDrop`,
`laws_drop` in `flatten.rs`), the records
within the limit, the distinct views; no view when the node is skipped. -/
def enumerateRDBounded (B : Bounds) (ix : Ix) (T : C → Bool) (ctx : Ctx) (dir : Dir)
    (laws : Laws) (limit : Nat) (n : Node) : BOut :=
  let base := (baseRecsR ctx dir laws n).filter (keepRec ctx.κ T laws)
  if limit = 0 ∧ canDrop ctx.κ laws = false then ⟨enumerateFromR base, false, false, 0⟩ else
  let b := regroupBoundedG B ix ctx dir laws (groupsOfEngine ctx) base
  match b.halt with
  | some .overBound => ⟨[], false, true, 0⟩
  | h => ⟨enumerateFromR (withinLimit limit b.st.records), h == some .truncated, false, b.ovf⟩

/-- `Enumerator.regroupSkip` with the engine's capped takeable set. -/
def Enumerator.regroupSkipCap (dir : Sym → Dir) : Enumerator :=
  ⟨fun ctx laws items n => enumerateRSkip ctx (dir ctx.f) laws items.length n,
    fun ctx laws σ items n =>
      enumerateRDSkip (takeableRCap ctx σ items) ctx (dir ctx.f) laws items.length n⟩

/-- The engine's enumeration with its bounds: the pruned side is
`enumerateRDBounded`; the full side, which only states what a match is, is
the unbounded one. -/
def Enumerator.regroupBounded (B : Bounds) (ix : Ix) (dir : Sym → Dir) : Enumerator :=
  ⟨fun ctx laws items n => enumerateRSkip ctx (dir ctx.f) laws items.length n,
    fun ctx laws σ items n =>
      (enumerateRDBounded B ix (takeableRCap ctx σ items) ctx (dir ctx.f) laws items.length n).views⟩

/-- The per-query counters of `MatchPool` (`ematch.rs`) that the `Flatten`
step feeds: `flatten_regroup_truncated`, `flatten_skipped`,
`flatten_overflowed`. -/
structure Counts where
  truncated : Nat
  skipped : Nat
  overflowed : Nat
  deriving DecidableEq, Repr

instance : Zero Counts := ⟨⟨0, 0, 0⟩⟩

def Counts.add (a b : Counts) : Counts :=
  ⟨a.truncated + b.truncated, a.skipped + b.skipped, a.overflowed + b.overflowed⟩

instance : Add Counts := ⟨Counts.add⟩

/-- The counters one `Flatten` evaluation adds. -/
def BOut.counts (o : BOut) : Counts :=
  ⟨if o.truncated then 1 else 0, if o.skipped then 1 else 0, o.ovf⟩

/-- `run_step` with the bounded enumeration, and the counters it adds. -/
def runStepB (B : Bounds) (ix : Ix) (dir : Sym → Dir) (c : FCtx) :
    EStep → EEnv → List EEnv × Counts
  | .flatten v f κ out items, env =>
      match env.σ.nodeOf c.G v with
      | some n =>
          let o := enumerateRDBounded B ix (takeableRCap (c.ctx f κ) env.σ items) (c.ctx f κ)
            (dir f) (c.laws f) items.length n
          (o.views.map (env.setView out), o.counts)
      | Option.none => ([], 0)
  | s, env => (runEStepG (Enumerator.regroupBounded B ix dir) c s env, 0)

/-- Depth-first search over a flattened plan with the bounded enumeration:
the environments emitted, and the counters summed over every `Flatten`
evaluation, as the engine sums them over one query. -/
def runB (B : Bounds) (ix : Ix) (dir : Sym → Dir) (c : FCtx) :
    List EStep → EEnv → List EEnv × Counts
  | [], env => ([env], 0)
  | s :: ss, env =>
      let r := runStepB B ix dir c s env
      let rs := r.1.map (runB B ix dir c ss)
      (rs.flatMap Prod.fst, r.2 + (rs.map Prod.snd).foldr (· + ·) 0)

end Semper.EMatch.Flatten
