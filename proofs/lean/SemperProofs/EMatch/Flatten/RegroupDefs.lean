import SemperProofs.EMatch.Flatten.FoldPlan
import Std.Data.HashSet
import Std.Data.HashMap

/-!
# `:flatten`: regrouped views, executably

Maximum partition gives each scalar item one entry of a view, so `(f x y)`
does not match `f{a, b, c}` with `x` the class of `f{a, b}`. The engine
(`flatten::FlattenScratch::regroup`, `flatten.rs`) therefore also matches
every *regrouped* view: a view in which a group of entries is replaced by
the class `g` of an `f`-member over exactly that group. This file is that
step, executably, over the records the opening walk produces:

* `fitsR κ dir view g grp` is `fits`: the raw views that replace one
  occurrence of the group `grp` (the children of an `f`-member of class
  `g`) in `view` by `g`. The group is a sub-multiset (AC), a subset (ACI)
  or a contiguous run (`:assoc`) of at least two entries, a prefix for a
  left fold and a suffix for a right fold (`spineRun`), and never the
  whole view; a member over its own class (`g ∋ f{g, c}`) is not a group;
* `regroupRec` is one regrouping of a record: the raw view normalized as
  any view, the source's flagged leaves with `g` added to a leaf holding a
  class of the group (`addG`, which flags the leaf non-inert when the
  normalization dropped `g`), and the regrouped classes the matches must
  take (`needs`: the source's, less those the group absorbs, and `g`, of
  those only the classes the normalized view holds);
* `regroupLevels` / `regroupAll` iterate it, level by level, from the
  walk's records, as many levels as the largest view has entries
  (`regroupFuel`), with no bound on the needed classes along the way: a
  later regrouping may absorb needed classes, so a record needing more
  classes than the items may lead to one needing fewer;
* `withinLimit` keeps the records a match may use: those needing at most
  `limit` classes (`Demand::needs`, one per item), since each needed class
  is taken by a distinct item;
* `enumerateFromR` builds the distinct views with their demand: a needed
  class is a leaf `needLeaf g` satisfied exactly when `g` is taken, so the
  demand is a `DemandL` and every demand rule of the model reads it
  unchanged (`needLeaf_okE`, `needLeaf_okL`);
* `takeableR` is the `takeable` set of `Step::Flatten` with regrouping on
  (`ematch.rs`): the bound item classes and every class below one through
  `f`-members;
* `enumerateRD` is the enumeration of `Step::Flatten`: the walk's records
  pruned by `takeableR`, regrouped, then the distinct views; `enumerateR`
  the same without pruning;
* `Enumerator.regroup` packs the two for the plan interpreter `runEG`;
  `runER` is the flattened plan with regrouped views.

The engine regroups view by view, largest first, and skips records another
record of the same view covers (a target with an unconditional record, a
source with one, the signature deduplication): `RegroupSkipDefs.lean` models
that loop and `RegroupSkip.lean` proves it accepts the same matches as
`regroupAll`. The engine's own bounds (`MAX_REGROUP_VIEWS`,
`MAX_REGROUP_WORK`, the cap on the takeable closure) are not modelled: past
a bound the engine reports the node.
-/

namespace Semper.EMatch.Flatten

open Semper.EMatch

/-- A record with the regrouped classes its matches must take. -/
abbrev RecR := List (C × Nat) × List LeafF × List C

/-- The leaf standing for a needed class `g`: its opened class and its only
element are `g`, its flag is off, so every leaf test holds exactly when `g`
is taken. -/
def needLeaf (g : C) : LeafF := (⟨g, 1, [(g, 1)]⟩, false)

theorem needLeaf_okE (κ : FlatKind) (taken : List C) (g : C) :
    (needLeaf g).okE κ taken ↔ g ∈ taken := by
  simp [needLeaf, LeafF.okE, LeafL.g]

theorem needLeaf_okL (taken : List C) (g : C) : (needLeaf g).okL taken ↔ g ∈ taken := by
  simp [needLeaf, LeafF.okL, LeafL.g]

/-- `flatten::spine` for a run: may the run of `k` entries at `p` in a view
of `len` entries be regrouped (`fits`, `:assoc` arm)? -/
def spineRun : Dir → Nat → Nat → Nat → Bool
  | .both, _, _, _ => true
  | .left, p, _, _ => p == 0
  | .right, p, k, len => p + k == len

/-- Subtract the canonical group `norm` from `view` entry by entry (`fits`,
multiset arm); `none` when some class lacks the count. -/
def subEntries (view : List (C × Nat)) : List (C × Nat) → Option (List (C × Nat))
  | [] => some (view.filter (fun e => e.2 ≠ 0))
  | (c, k) :: rest =>
      match view.find? (fun e => e.1 = c) with
      | some (_, x) =>
          if k ≤ x then subEntries (view.map (fun e => if e.1 = c then (c, x - k) else e)) rest
          else none
      | none => none

/-- The group as the multiset arm of `fits` reads it: summed counts (AC),
deduplicated with count one (ACI). -/
def groupNorm (κ : FlatKind) (grp : List (C × Nat)) : List (C × Nat) :=
  match κ with
  | .ac => coalesce grp
  | _ => dedupAci grp

/-- `fits` (`flatten.rs`): every raw view replacing one occurrence of the
group `grp`, the children of an `f`-member of class `g`, in `view` by `g`. -/
def fitsR (κ : FlatKind) (dir : Dir) (view : List (C × Nat)) (g : C)
    (grp : List (C × Nat)) : List (List (C × Nat)) :=
  if grp.any (fun e => e.1 = g) then [] else
  match κ with
  | .assoc =>
      let k := grp.length
      if k < 2 ∨ view.length ≤ k then [] else
      (List.range (view.length - k + 1)).filterMap fun p =>
        if spineRun dir p k view.length &&
            ((view.drop p).take k).map Prod.fst == grp.map Prod.fst then
          some (view.take p ++ (g, 1) :: view.drop (p + k))
        else none
  | _ =>
      let norm := groupNorm κ grp
      let two := decide (2 ≤ norm.length) || (norm.head?.map (fun e => decide (1 < e.2))).getD false
      if !two || norm == view then [] else
      match subEntries view norm with
      | some v => [v ++ [(g, 1)]]
      | none => []

/-- The candidate groups: per filed `f`-member, its class and its children
(the use lists `by_contains` of the round, filtered by operator; a member
whose children are not entries of the view never fits). -/
def groupsOf (ctx : Ctx) : List (C × List (C × Nat)) :=
  ((ctx.G.nodes.filter (fun p => ctx.filed p.1 && decide (p.2.op = ctx.f))).map
    (fun p => (ctx.G.find p.1, kids ctx.κ p.2.children))).dedup

/-- A regrouped record's leaf: a leaf holding a class of the group also
holds `g`, so an item taking `g` takes from the leaf. When the regrouped view
`ws` (its classes) does not hold `g`, the laws dropped it (the unit, a count
clamped to zero, a cancelled inverse): no item can take it, and the leaf is
flagged non-inert, satisfied without it. -/
def addG (g : C) (grp : List C) (ws : List C) (l : LeafF) : LeafF :=
  if g ∉ l.1.g ∧ l.1.g.any (fun c => decide (c ∈ grp)) then
    ({ l.1 with L := l.1.L ++ [(g, 1)] }, l.2 || decide (g ∉ ws))
  else l

/-- The regrouped classes a regrouped record needs taken: the source's, less
those the group absorbs, and `g`; of those, the classes the regrouped view
`ws` holds (the laws may drop `g` or an earlier needed class). -/
def needsAfter (g : C) (grp : List C) (ws : List C) (needs : List C) : List C :=
  let ns := needs.filter (fun c => decide (c ∉ grp))
  (if g ∈ ns then ns else ns ++ [g]).filter (fun c => decide (c ∈ ws))

/-- One regrouping of a record, every candidate group, every fit. -/
def regroupRec (ctx : Ctx) (dir : Dir) (laws : Laws) (r : RecR) : List RecR :=
  (groupsOf ctx).flatMap fun gg =>
    (fitsR ctx.κ dir r.1 gg.1 gg.2).filterMap fun raw =>
      match normalize ctx.κ laws raw with
      | .node w =>
          some (w, r.2.1.map (addG gg.1 (gg.2.map Prod.fst) (w.map Prod.fst)),
            needsAfter gg.1 (gg.2.map Prod.fst) (w.map Prod.fst) r.2.2)
      | _ => none

instance : Hashable LeafL := ⟨fun l => mixHash (hash l.X) (mixHash (hash l.k) (hash l.L))⟩

/-- Duplicates removed through a hash set, first occurrences kept in order
(`mem_dedupH`: the same members). -/
def dedupH {α : Type} [BEq α] [Hashable α] (l : List α) : List α :=
  (l.foldl (fun (acc : List α × Std.HashSet α) x =>
    if acc.2.contains x then acc else (x :: acc.1, acc.2.insert x)) ([], ∅)).1.reverse

/-- Regrouping level by level: the records, then the regroupings of each
level's records. -/
def regroupLevels (ctx : Ctx) (dir : Dir) (laws : Laws) :
    Nat → List RecR → List RecR
  | 0, recs => recs
  | fuel + 1, recs =>
      recs ++ regroupLevels ctx dir laws fuel (dedupH (recs.flatMap (regroupRec ctx dir laws)))

/-- `regroupLevels` with a budget for the conformance generators: `none` when
the levels hold more than `cap` records in all (`regroupLevelsCapped_eq`:
otherwise the levels). The engine has bounds of its own (`MAX_REGROUP_VIEWS`,
`MAX_REGROUP_WORK`), past which it reports the node; a generator does not
emit an exact case for a node past the budget. -/
def regroupLevelsCapped (ctx : Ctx) (dir : Dir) (laws : Laws) (cap : Nat) :
    Nat → List RecR → Option (List RecR)
  | 0, recs => some recs
  | fuel + 1, recs =>
      if cap < recs.length then none
      else (regroupLevelsCapped ctx dir laws (cap - recs.length) fuel
        (dedupH (recs.flatMap (regroupRec ctx dir laws)))).map (recs ++ ·)

/-- The generators' budget on the regrouped records of one node. -/
def regroupCap : Nat := 45000

/-- The total count of a view, the order in which the engine regroups. A
regrouping replaces at least two counts by one and normalization never adds
any, so a chain of regroupings from a view is shorter than its size. -/
def viewSize (w : List (C × Nat)) : Nat := (w.map Prod.snd).sum

/-- The number of levels regrouping runs from the records `recs`: the
largest view size among them. -/
def regroupFuel (recs : List RecR) : Nat := (recs.map (fun r => viewSize r.1)).foldl max 0

/-- Every regrouped record of the records `recs`, `fuel` levels deep. -/
def regroupAll (ctx : Ctx) (dir : Dir) (laws : Laws) (fuel : Nat) (recs : List RecR) :
    List RecR :=
  regroupLevels ctx dir laws fuel recs

/-- The records a match may use: those needing at most `limit` regrouped
classes. Each needed class is taken by a distinct item, so a record needing
more classes than the decomposition has items never matches; the engine
filters its records the same way after regrouping. -/
def withinLimit (limit : Nat) (recs : List RecR) : List RecR :=
  recs.filter (fun r => decide (r.2.2.length ≤ limit))

/-- A record's demand alternative: its leaves and one leaf per needed class. -/
def RecR.alt (r : RecR) : List LeafF := r.2.1 ++ r.2.2.map needLeaf

/-- Per view, the demand alternatives of its records. -/
def altsMap (recs : List RecR) : Std.HashMap (List (C × Nat)) (List (List LeafF)) :=
  recs.foldl (fun m r => m.insert r.1 (r.alt :: m.getD r.1 [])) ∅

/-- The demand of a view from its alternatives (`demandOfL`): unconditional
when some record needs nothing. -/
def demandOfAlts (alts : List (List LeafF)) : DemandL :=
  if [] ∈ alts then ⟨true, []⟩ else ⟨false, alts⟩

/-- The distinct views and their demand (`enumerateFromL`, with the records
grouped by view through a hash map). -/
def enumerateFromR (recs : List RecR) : List (List (C × Nat) × DemandL) :=
  let m := altsMap recs
  (dedupH (recs.map Prod.fst)).map (fun w => (w, demandOfAlts (m.getD w [])))

/-- The walk's records as regrouping reads them: no class needed. -/
def RecL.toR (r : RecL) : RecR := (r.1, r.2, [])

/-- The classes below `S` through `f`-members, one round. -/
def belowStep (ctx : Ctx) (S : List C) : List C :=
  (S ++ S.flatMap (fun x => (ctx.members x).flatMap
    (fun p => (kids ctx.κ p.2.children).map Prod.fst))).dedup

def belowIter (ctx : Ctx) : Nat → List C → List C
  | 0, S => S
  | n + 1, S => belowIter ctx n (belowStep ctx S)

/-- `takeable` with regrouping on (`ematch.rs`, `Step::Flatten`): when every
item is bound, their classes and every class below one of them through
`f`-members; otherwise every class. The closure is iterated once per class
of the graph and checked; a set not closed by then makes every class
takeable, as the engine's cap on the closure does. -/
def takeableR (ctx : Ctx) (σ : Binding) (items : List Var) : C → Bool :=
  match items.mapM σ.cls with
  | some bound =>
      let S := belowIter ctx ((classesOf ctx.G).card + 1) bound
      if belowStep ctx S ⊆ S then fun c => decide (c ∈ S) else fun _ => true
  | none => fun _ => true

/-- The walk's records of node `n` with every operator direction (`rawRecordsLD`). -/
def baseRecsR (ctx : Ctx) (dir : Dir) (laws : Laws) (n : Node) : List RecR :=
  (rawRecordsLD ctx dir laws n).map RecL.toR

/-- The walk's pruning (`enumeratePrunedED`): every leaf kept under `T`. -/
def keepRec (κ : FlatKind) (T : C → Bool) (laws : Laws) (r : RecR) : Bool :=
  r.2.1.all (fun lf => keepLeaf κ T laws lf.1)

/-- The enumeration of `Step::Flatten` with regrouping: the walk's records
pruned by `T`, regrouped, those with at most `limit` needed classes kept,
the distinct views. Regrouping runs as many levels as the largest view of the unpruned
walk has entries. -/
def enumerateRD (T : C → Bool) (ctx : Ctx) (dir : Dir) (laws : Laws) (limit : Nat)
    (n : Node) : List (List (C × Nat) × DemandL) :=
  let base := baseRecsR ctx dir laws n
  enumerateFromR (withinLimit limit (regroupAll ctx dir laws (regroupFuel base)
    (base.filter (keepRec ctx.κ T laws))))

/-- The same without pruning: every view a match may use. -/
def enumerateR (ctx : Ctx) (dir : Dir) (laws : Laws) (limit : Nat) (n : Node) :
    List (List (C × Nat) × DemandL) :=
  let base := baseRecsR ctx dir laws n
  enumerateFromR (withinLimit limit (regroupAll ctx dir laws (regroupFuel base) base))

/-- The enumeration of a `Flatten` step with regrouped views, every operator
with its fold direction: the records with at most one regrouped class per
item. -/
def Enumerator.regroup (dir : Sym → Dir) : Enumerator :=
  ⟨fun ctx laws items n => enumerateR ctx (dir ctx.f) laws items.length n,
    fun ctx laws σ items n =>
      enumerateRD (takeableR ctx σ items) ctx (dir ctx.f) laws items.length n⟩

/-- `run_step` with regrouped views. -/
abbrev runEStepR (c : FCtx) (dir : Sym → Dir) : EStep → EEnv → List EEnv :=
  runEStepG (Enumerator.regroup dir) c

/-- The flattened plan with regrouped views (`flatten.rs`, "Regrouped views"). -/
abbrev runER (c : FCtx) (dir : Sym → Dir) : List EStep → EEnv → List EEnv :=
  runEG (Enumerator.regroup dir) c

end Semper.EMatch.Flatten
