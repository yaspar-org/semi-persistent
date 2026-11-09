import SemperProofs.EMatch.Flatten.RegroupBoundsDefs

/-!
# `:flatten`: overlap views under idempotence, executably

A regrouping replaces a group of a view's entries by the class `g` of an
`f`-member over that group, and never keeps a member of the group beside
`g`. Under idempotence a member kept beside its class changes nothing:
`S{a, b, c} = S{a, c, G}` when `G ∋ S{a, b}`, in every join semilattice where
the members denote their classes. The engine (`FlattenScratch::regroup`,
`flatten.rs`, the stage after the regrouping loop) therefore also matches,
for an `:assoc-comm-idem` operator, the *overlap views* of every view the
loop ends with: the view with `g` added and some members of the group
dropped, as many as the pattern's item count fixes. This file is that stage,
executably, in the three forms of the regrouping model:

* `overlapFits κ limit view g grp` is the family of raw overlap views of one
  candidate group in one view, empty unless `κ = .aci`: the group's classes
  (`groupClasses`, sorted and distinct) must number at least two, lie in the
  view and not hold `g`; with `base` the entries of the view plus one when
  `g` is new, the drop count is `k = base - limit`, so that the raw view has
  `limit` entries, one per item; `k` must leave a member (`k < |group|`), and
  `k = 0` with `g` already in the view would repeat the view. Each raw view
  drops one `k`-element sublist `D` of the group's classes (`dropSets`, in
  the order of `List.sublists`, the engine's order of combinations) and
  appends `(g, 1)`; it is normalized as any view. A dropped member is
  covered by `g`, a kept member stays in the pool;
* `overlapRec` is the overlap records of one record, every candidate group,
  every fit, with the derived leaves and needed classes of a regrouping by
  the same group (`deriveRec`: a leaf holding a class of the group also holds
  `g`, the needs lose the classes the group absorbs and gain `g`, of those
  the classes the view holds); `overlapStage` adds them to a record list,
  `regroupAllO` runs it after `regroupAll`, and `enumerateRO`,
  `enumerateRDO`, `Enumerator.regroupO` and `runERO` are the enumerations
  and the plan with it;
* `SkipSt.overlapAll` is the engine's stage over the loop's final state,
  run for a set operator and a pattern with items only: for each view of
  the loop, in entry order, each candidate group and each fit,
  the normalized target is entered when new, given nothing when it has an
  unconditional record, and otherwise given the records derived from the
  loop's records of the source view (`srcRecs`: the first unconditional one
  alone, else all), each dropped when the target has its signature
  (`SkipSt.addRec`). A target already regrouped is not skipped: the stage
  regroups nothing, and its views are not overlapped again, so an overlap
  view is one overlap step from a view of the loop. `regroupSkipO`,
  `regroupAllSkipO`, `regroupAllSkipOAt` (candidates per view),
  `enumerateRSkipO`, `enumerateRDSkipO`, `Enumerator.regroupSkipO` and
  `runERSkipO` are the loop with the stage;
* `BSt.overlapAll` is the stage with the engine's counters: the use lists of
  the source view, the children of each candidate and one unit per raw fit
  count against `MAX_REGROUP_WORK`, each record added counts against
  `MAX_REGROUP_VIEWS`, elements against `MAX_ELEMS`, checked where the
  engine checks them; a stopped run stays stopped. `regroupBoundedO`,
  `enumerateRDBoundedO`, `Enumerator.regroupBoundedO`, `runStepBO` and
  `runBO` are the bounded engine with the stage.

For an operator without idempotence every family is empty and each
definition is the one without the stage (`RegroupOverlap.lean`).
-/

namespace Semper.EMatch.Flatten

open Semper.EMatch

/-! ## The overlap family -/

/-- The `k`-element sublists of `l`, in the order of `List.sublists`: the
engine enumerates the combinations of `k` members in the same order
(`next_colex`, `flatten.rs`). -/
def dropSets (l : List C) (k : Nat) : List (List C) :=
  l.sublists.filter (fun d => d.length == k)

/-- The classes of a candidate group, sorted and distinct. -/
def groupClasses (grp : List (C × Nat)) : List C := (dedupAci grp).map Prod.fst

/-- The number of members an overlap view of the group `grp` (class `g`) in
`view` drops so that it has `limit` entries; `none` when the group yields no
overlap view: another kind than a set, `g` among the members, fewer than two
members, a member outside the view, more items than entries, no member left,
or `g` already in the view with nothing dropped. -/
def overlapDrops (κ : FlatKind) (limit : Nat) (view : View) (g : C) (grp : List (C × Nat)) :
    Option Nat :=
  if κ != .aci then none else
  let cs := groupClasses grp
  let vs := view.map Prod.fst
  if g ∈ cs ∨ cs.length < 2 ∨ ¬ (∀ c ∈ cs, c ∈ vs) then none else
  let base := view.length + (if g ∈ vs then 0 else 1)
  if base < limit then none else
  let k := base - limit
  if cs.length ≤ k ∨ (k = 0 ∧ g ∈ vs) then none else some k

/-- The raw overlap views of the group `grp` (class `g`) in `view` for a
pattern of `limit` items: the view less each `k`-element sublist of the
group's classes, with `(g, 1)` appended. -/
def overlapFits (κ : FlatKind) (limit : Nat) (view : View) (g : C) (grp : List (C × Nat)) :
    List View :=
  match overlapDrops κ limit view g grp with
  | none => []
  | some k =>
      (dropSets (groupClasses grp) k).map
        (fun D => view.filter (fun e => decide (e.1 ∉ D)) ++ [(g, 1)])

/-! ## The stage over record lists -/

/-- The overlap records of one record: every candidate group, every fit,
normalized, with the leaves and needs of a regrouping by the group. -/
def overlapRec (ctx : Ctx) (laws : Laws) (limit : Nat) (r : RecR) : List RecR :=
  (groupsOf ctx).flatMap fun gg =>
    (overlapFits ctx.κ limit r.1 gg.1 gg.2).filterMap fun raw =>
      match normalize ctx.κ laws raw with
      | .node w => some (deriveRec w gg.1 (gg.2.map Prod.fst) r)
      | _ => none

/-- The records with their overlap records, each once. -/
def overlapStage (ctx : Ctx) (laws : Laws) (limit : Nat) (recs : List RecR) : List RecR :=
  recs ++ dedupH (recs.flatMap (overlapRec ctx laws limit))

/-- `regroupAll` followed by the overlap stage. -/
def regroupAllO (ctx : Ctx) (dir : Dir) (laws : Laws) (limit fuel : Nat) (recs : List RecR) :
    List RecR :=
  overlapStage ctx laws limit (regroupAll ctx dir laws fuel recs)

/-- `enumerateRD` with the overlap stage. -/
def enumerateRDO (T : C → Bool) (ctx : Ctx) (dir : Dir) (laws : Laws) (limit : Nat)
    (n : Node) : List (List (C × Nat) × DemandL) :=
  let base := baseRecsR ctx dir laws n
  enumerateFromR (withinLimit limit (regroupAllO ctx dir laws limit (regroupFuel base)
    (base.filter (keepRec ctx.κ T laws))))

/-- `enumerateR` with the overlap stage. -/
def enumerateRO (ctx : Ctx) (dir : Dir) (laws : Laws) (limit : Nat) (n : Node) :
    List (List (C × Nat) × DemandL) :=
  let base := baseRecsR ctx dir laws n
  enumerateFromR (withinLimit limit (regroupAllO ctx dir laws limit (regroupFuel base) base))

/-- `Enumerator.regroup` with the overlap stage. -/
def Enumerator.regroupO (dir : Sym → Dir) : Enumerator :=
  ⟨fun ctx laws items n => enumerateRO ctx (dir ctx.f) laws items.length n,
    fun ctx laws σ items n =>
      enumerateRDO (takeableR ctx σ items) ctx (dir ctx.f) laws items.length n⟩

/-- `run_step` with regrouped and overlap views. -/
abbrev runEStepRO (c : FCtx) (dir : Sym → Dir) : EStep → EEnv → List EEnv :=
  runEStepG (Enumerator.regroupO dir) c

/-- The flattened plan with regrouped and overlap views. -/
abbrev runERO (c : FCtx) (dir : Sym → Dir) : List EStep → EEnv → List EEnv :=
  runEG (Enumerator.regroupO dir) c

/-! ## The engine's stage -/

/-- One target of the stage: entered when new, given nothing when it has an
unconditional record, otherwise given the derived records `ds` one by one.
A target already regrouped is not skipped (`SkipSt.addTarget`): the stage
regroups nothing. -/
def SkipSt.addTargetO (st : SkipSt) (t : View) (ds : List RecR) : SkipSt :=
  let st := if t ∈ st.order then st else { st with order := st.order ++ [t] }
  if (st.recs t).any RecR.uncond then st else ds.foldl (SkipSt.addRec t) st

/-- One raw overlap fit of the group `gg`, derived from the source's loop
records `srcs`. -/
def SkipSt.overlapFitStep (ctx : Ctx) (laws : Laws) (srcs : List RecR)
    (gg : C × List (C × Nat)) (st : SkipSt) (raw : List (C × Nat)) : SkipSt :=
  match normalize ctx.κ laws raw with
  | .node t => st.addTargetO t ((srcRecs srcs).map (deriveRec t gg.1 (gg.2.map Prod.fst)))
  | _ => st

/-- One candidate group of the source view `w`: every overlap fit. -/
def SkipSt.overlapGroupStep (ctx : Ctx) (laws : Laws) (limit : Nat) (w : View)
    (srcs : List RecR) (st : SkipSt) (gg : C × List (C × Nat)) : SkipSt :=
  (overlapFits ctx.κ limit w gg.1 gg.2).foldl (SkipSt.overlapFitStep ctx laws srcs gg) st

/-- The overlap views of the source view `w`: every candidate group. -/
def SkipSt.overlapView (ctx : Ctx) (laws : Laws) (limit : Nat)
    (gs : List (C × List (C × Nat))) (w : View) (srcs : List RecR) (st : SkipSt) : SkipSt :=
  gs.foldl (SkipSt.overlapGroupStep ctx laws limit w srcs) st

/-- The stage: every view of the loop's final state `st₀`, in entry order,
with its records in `st₀`. -/
def SkipSt.overlapAll (ctx : Ctx) (laws : Laws) (limit : Nat) (gs : List (C × List (C × Nat)))
    (st₀ : SkipSt) : SkipSt :=
  if ctx.κ != .aci || limit == 0 then st₀ else
  st₀.order.foldl (fun st w => SkipSt.overlapView ctx laws limit gs w (st₀.recs w) st) st₀

/-- The stage with the candidates chosen per view (`groupsOfEngineAt`). -/
def SkipSt.overlapAllAt (ctx : Ctx) (laws : Laws) (limit : Nat)
    (gs : View → List (C × List (C × Nat))) (st₀ : SkipSt) : SkipSt :=
  if ctx.κ != .aci || limit == 0 then st₀ else
  st₀.order.foldl (fun st w => SkipSt.overlapView ctx laws limit (gs w) w (st₀.recs w) st) st₀

/-- The engine's regrouping with the overlap stage, candidates `gs`. -/
def regroupSkipO (ctx : Ctx) (dir : Dir) (laws : Laws) (limit : Nat)
    (gs : List (C × List (C × Nat))) (base : List RecR) : List RecR :=
  (SkipSt.overlapAll ctx laws limit gs
    (SkipSt.run ctx dir laws gs (skipFuel ctx dir laws base) (SkipSt.init base))).records

/-- The engine's regrouping with the overlap stage, candidates in the
engine's order. -/
def regroupAllSkipO (ctx : Ctx) (dir : Dir) (laws : Laws) (limit : Nat) (base : List RecR) :
    List RecR :=
  regroupSkipO ctx dir laws limit (groupsOfEngine ctx) base

/-- The same with the candidates of each view read from the use lists of its
classes (`regroupAllSkipAt`). -/
def regroupAllSkipOAt (ctx : Ctx) (dir : Dir) (laws : Laws) (limit : Nat) (base : List RecR) :
    List RecR :=
  (SkipSt.overlapAllAt ctx laws limit (groupsOfEngineAt ctx)
    (SkipSt.runAt ctx dir laws (groupsOfEngineAt ctx) (skipFuel ctx dir laws base)
      (SkipSt.init base))).records

/-- `enumerateRDSkip` with the overlap stage. -/
def enumerateRDSkipO (T : C → Bool) (ctx : Ctx) (dir : Dir) (laws : Laws) (limit : Nat)
    (n : Node) : List (List (C × Nat) × DemandL) :=
  enumerateFromR (withinLimit limit (regroupAllSkipO ctx dir laws limit
    ((baseRecsR ctx dir laws n).filter (keepRec ctx.κ T laws))))

/-- `enumerateRSkip` with the overlap stage. -/
def enumerateRSkipO (ctx : Ctx) (dir : Dir) (laws : Laws) (limit : Nat) (n : Node) :
    List (List (C × Nat) × DemandL) :=
  enumerateFromR (withinLimit limit (regroupAllSkipO ctx dir laws limit (baseRecsR ctx dir laws n)))

/-- `Enumerator.regroupSkip` with the overlap stage. -/
def Enumerator.regroupSkipO (dir : Sym → Dir) : Enumerator :=
  ⟨fun ctx laws items n => enumerateRSkipO ctx (dir ctx.f) laws items.length n,
    fun ctx laws σ items n =>
      enumerateRDSkipO (takeableR ctx σ items) ctx (dir ctx.f) laws items.length n⟩

/-- The flattened plan with the engine's regrouping and the overlap stage. -/
abbrev runERSkipO (c : FCtx) (dir : Sym → Dir) : List EStep → EEnv → List EEnv :=
  runEG (Enumerator.regroupSkipO dir) c

/-! ## The stage with the bounds -/

/-- One target of the stage with the bounds (`BSt.addTarget` without the
skip of a regrouped target). -/
def BSt.addTargetO (B : Bounds) (b : BSt) (t : View) (ds : List RecR) : BSt :=
  if b.halt.isSome then b else
  let b := b.enterTarget B t
  if b.halt.isSome then b else
  if (b.st.recs t).any RecR.uncond then b else ds.foldl (BSt.addRec B t) b

/-- One raw overlap fit: one unit of work, checked; a fit whose normalization
overflows the width is counted and skipped. -/
def BSt.overlapFitStep (B : Bounds) (ix : Ix) (ctx : Ctx) (laws : Laws) (srcs : List RecR)
    (gg : C × List (C × Nat)) (b : BSt) (raw : List (C × Nat)) : BSt :=
  if b.halt.isSome then b else
  if pastB B.work (b.work + 1) then { b with work := b.work + 1, halt := some .truncated } else
  let b := { b with work := b.work + 1 }
  if ix.wide laws raw then { b with ovf := b.ovf + 1 } else
  match normalize ctx.κ laws raw with
  | .node t => b.addTargetO B t ((srcRecs srcs).map (deriveRec t gg.1 (gg.2.map Prod.fst)))
  | _ => b

/-- One candidate group of the source view `w`: its children counted and
checked, then every overlap fit. A group that is not a candidate is not
examined. -/
def BSt.overlapGroupStep (B : Bounds) (ix : Ix) (ctx : Ctx) (laws : Laws) (limit : Nat)
    (w : View) (srcs : List RecR) (b : BSt) (gg : C × List (C × Nat)) : BSt :=
  if b.halt.isSome then b else
  if !isCand w gg then b else
  if pastB B.work (b.work + gg.2.length) then
    { b with work := b.work + gg.2.length, halt := some .truncated } else
  (overlapFits ctx.κ limit w gg.1 gg.2).foldl (BSt.overlapFitStep B ix ctx laws srcs gg)
    { b with work := b.work + gg.2.length }

/-- The overlap views of the source view `w`: its use lists counted and
checked, then every candidate group. -/
def BSt.overlapView (B : Bounds) (ix : Ix) (ctx : Ctx) (laws : Laws) (limit : Nat)
    (gs : List (C × List (C × Nat))) (w : View) (srcs : List RecR) (b : BSt) : BSt :=
  if b.halt.isSome then b else
  if pastB B.work (b.work + useWork ix w) then
    { b with work := b.work + useWork ix w, halt := some .truncated } else
  gs.foldl (BSt.overlapGroupStep B ix ctx laws limit w srcs) { b with work := b.work + useWork ix w }

/-- The stage over the loop's final state `b₀`: every view of the loop, in
entry order, with its records in `b₀`. -/
def BSt.overlapAll (B : Bounds) (ix : Ix) (ctx : Ctx) (laws : Laws) (limit : Nat)
    (gs : List (C × List (C × Nat))) (b₀ : BSt) : BSt :=
  if ctx.κ != .aci || limit == 0 then b₀ else
  if b₀.halt.isSome then b₀ else
  b₀.st.order.foldl (fun b w => BSt.overlapView B ix ctx laws limit gs w (b₀.st.recs w) b) b₀

/-- The bounded regrouping with the overlap stage. -/
def regroupBoundedO (B : Bounds) (ix : Ix) (ctx : Ctx) (dir : Dir) (laws : Laws) (limit : Nat)
    (gs : List (C × List (C × Nat))) (base : List RecR) : BSt :=
  BSt.overlapAll B ix ctx laws limit gs (regroupBoundedG B ix ctx dir laws gs base)

/-- `enumerateRDBounded` with the overlap stage. -/
def enumerateRDBoundedO (B : Bounds) (ix : Ix) (T : C → Bool) (ctx : Ctx) (dir : Dir)
    (laws : Laws) (limit : Nat) (n : Node) : BOut :=
  let base := (baseRecsR ctx dir laws n).filter (keepRec ctx.κ T laws)
  if limit = 0 ∧ canDrop ctx.κ laws = false then ⟨enumerateFromR base, false, false, 0⟩ else
  let b := regroupBoundedO B ix ctx dir laws limit (groupsOfEngine ctx) base
  match b.halt with
  | some .overBound => ⟨[], false, true, 0⟩
  | h => ⟨enumerateFromR (withinLimit limit b.st.records), h == some .truncated, false, b.ovf⟩

/-- `Enumerator.regroupSkipO` with the engine's capped takeable set. -/
def Enumerator.regroupSkipOCap (dir : Sym → Dir) : Enumerator :=
  ⟨fun ctx laws items n => enumerateRSkipO ctx (dir ctx.f) laws items.length n,
    fun ctx laws σ items n =>
      enumerateRDSkipO (takeableRCap ctx σ items) ctx (dir ctx.f) laws items.length n⟩

/-- The engine's enumeration with its bounds and the overlap stage. -/
def Enumerator.regroupBoundedO (B : Bounds) (ix : Ix) (dir : Sym → Dir) : Enumerator :=
  ⟨fun ctx laws items n => enumerateRSkipO ctx (dir ctx.f) laws items.length n,
    fun ctx laws σ items n =>
      (enumerateRDBoundedO B ix (takeableRCap ctx σ items) ctx (dir ctx.f) laws
        items.length n).views⟩

/-- `run_step` with the bounded enumeration and the stage, and the counters it adds. -/
def runStepBO (B : Bounds) (ix : Ix) (dir : Sym → Dir) (c : FCtx) :
    EStep → EEnv → List EEnv × Counts
  | .flatten v f κ out items, env =>
      match env.σ.nodeOf c.G v with
      | some n =>
          let o := enumerateRDBoundedO B ix (takeableRCap (c.ctx f κ) env.σ items) (c.ctx f κ)
            (dir f) (c.laws f) items.length n
          (o.views.map (env.setView out), o.counts)
      | Option.none => ([], 0)
  | s, env => (runEStepG (Enumerator.regroupBoundedO B ix dir) c s env, 0)

/-- The flattened plan with the bounded enumeration and the stage: the
environments emitted and the counters summed over every `Flatten`
evaluation. -/
def runBO (B : Bounds) (ix : Ix) (dir : Sym → Dir) (c : FCtx) :
    List EStep → EEnv → List EEnv × Counts
  | [], env => ([env], 0)
  | s :: ss, env =>
      let r := runStepBO B ix dir c s env
      let rs := r.1.map (runBO B ix dir c ss)
      (rs.flatMap Prod.fst, r.2 + (rs.map Prod.snd).foldr (· + ·) 0)

end Semper.EMatch.Flatten
