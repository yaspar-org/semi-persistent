import SemperProofs.EMatch.Steps.Defs

/-!
# The sequence-pattern assembler (A.8.2, `seq_collect.rs::assemble`)

A reference implementation over lists of the matches of a sequence
pattern at one node, given its children `kids` (class, multiplicity) and a
row `Source`:

* under A (`match_assoc`): `assocParses` enumerates the parses of the
  child list by the item list (a span per item, a row per filtered child, a
  joined scalar row per simple item), `maximalA` is the gap condition
  (`assoc_maximal`), `envOfA` builds the environment;
* under AC/ACI (`assign_ones`, `assign_filters`): `assignOnes` enumerates
  the injective assignments of the simple items, `assignFilters` the
  choices of (filter, row) per remaining child, `envOfAC` builds the
  environment;
* `assemble` deduplicates (`EnvSet`) under the `MAX_MATCHES` bound; a node
  over the bound yields no match (it is skipped, A.8.2).

Differences from the engine, by design of the model: the enumeration order
and the first-seen order of the deduplication are not preserved
(`List.dedup` keeps last occurrences; the theorems are about membership
and duplicate-freedom); rows for an item index out of range are those of a
default empty filter rather than a panic.
-/

namespace Semper.EMatch.Steps

open Semper.EMatch

/-- `vec![None; n]`. -/
def blank (n : Nat) : Slots := List.replicate n none

def SeqSpec.filterAt (S : SeqSpec) (fi : Nat) : SFilter :=
  S.filters.getD fi ⟨0, none, none⟩

/-- Whether the items hold a bare sequence. -/
def SeqSpec.hasBare (S : SeqSpec) : Bool := S.items.any (fun i => decide (i = .bare))

/-- The simple items, in item order (`ones`). -/
def SeqSpec.ones (S : SeqSpec) : List (Nat × Option MultCheck) :=
  S.items.filterMap (fun i => match i with | .one j μ => some (j, μ) | _ => none)

/-- A filter's columns from its chosen rows: `cols[slot] = rows.map (·[slot])`. -/
def colsOf (nvars : Nat) (rows : List Slots) : List (List (Option Val)) :=
  (List.range nvars).map (fun slot => rows.map (fun r => r.getD slot none))

/-! ## Under A -/

/-- The rows of filter `fi` at a child class under A (`match_assoc`, phase 1):
the filter's sub-query with nothing bound, deduplicated by bindings. -/
def matchedA (S : SeqSpec) (src : Source) (fi : Nat) (c : C) : List Slots :=
  (src.filter fi c (blank (S.filterAt fi).nvars)).dedup

/-- One item's part of a parse: a simple item at a position, a bare span
`[s, e)`, a filter span `[s, e)` with the chosen row of each child. -/
inductive ABind where
  | one (pos : Nat)
  | bare (s e : Nat)
  | filter (fi : Nat) (s e : Nat) (rows : List Slots)
  deriving DecidableEq

/-- `assoc_go`: the parses of `kids` from position `pos` by the remaining
items, with the scalar slots `sc`; each parse with its final scalars. -/
def assocParses (S : SeqSpec) (src : Source) (kids : List C) :
    List SItem → Nat → Slots → List (List ABind × Slots)
  | [], pos, sc => if pos = kids.length then [([], sc)] else []
  | .one j _ :: items, pos, sc =>
      match kids[pos]? with
      | none => []
      | some k =>
          (src.one j k sc).flatMap (fun b =>
            (assocParses S src kids items (pos + 1) b).map (fun r => (.one pos :: r.1, r.2)))
  | .bare :: items, pos, sc =>
      (List.range' pos (kids.length + 1 - pos)).flatMap (fun e =>
        (assocParses S src kids items e sc).map (fun r => (.bare pos e :: r.1, r.2)))
  | .filter fi :: items, pos, sc =>
      (List.range' pos (kids.length + 1 - pos)).flatMap (fun e =>
        (List.sections (((kids.drop pos).take (e - pos)).map (matchedA S src fi))).flatMap
          (fun rows =>
            (assocParses S src kids items e sc).map (fun r => (.filter fi pos e rows :: r.1, r.2))))

/-- The rows of filter `fi` at the child at position `k`; none out of range. -/
def matchedAt (S : SeqSpec) (src : Source) (kids : List C) (fi k : Nat) : List Slots :=
  match kids[k]? with
  | some c => matchedA S src fi c
  | none => []

/-- `assoc_maximal`: a run next to a gap is maximal toward it. -/
def maximalA (S : SeqSpec) (src : Source) (kids : List C) : List ABind → Bool
  | .filter fi _ _ _ :: .bare s e :: rest =>
      (!decide (s < e) || (matchedAt S src kids fi s).isEmpty) &&
        maximalA S src kids (.bare s e :: rest)
  | .bare s e :: .filter fi s' e' rows :: rest =>
      (!decide (s < e) || (matchedAt S src kids fi (e - 1)).isEmpty) &&
        maximalA S src kids (.filter fi s' e' rows :: rest)
  | _ :: rest => maximalA S src kids rest
  | [] => true

/-- The environment of a parse. -/
def envOfA (S : SeqSpec) (kids : List C) (bs : List ABind) (sc : Slots) : Env :=
  { scalars := sc
    filt := (List.range S.filters.length).map (fun fi =>
      bs.findSome? (fun b => match b with
        | .filter fi' s e rows =>
            if fi' = fi then
              some ⟨(kids.drop s).take (e - s), [], colsOf (S.filterAt fi).nvars rows⟩
            else none
        | _ => none))
    bare := bs.findSome? (fun b => match b with
      | .bare s e => some ⟨(kids.drop s).take (e - s), []⟩
      | _ => none) }

/-- `match_assoc`: the maximal parses' environments, before deduplication. -/
def rawA (S : SeqSpec) (src : Source) (kids : List C) : List Env :=
  ((assocParses S src kids S.items 0 (blank S.nScalars)).filter
    (fun r => maximalA S src kids r.1)).map (fun r => envOfA S kids r.1 r.2)

/-! ## Under AC / ACI -/

/-- Admissibility of a child of multiplicity `m` for a simple item
(`assign_ones`, `seq_collect.rs:527-541`): the scalars with the
multiplicity variable bound, or `none`. -/
def admit (ac : Bool) (μ : Option MultCheck) (m : Nat) (sc : Slots) : Option Slots :=
  match μ with
  | none => if ac && m ≠ 1 then none else some sc
  | some mc =>
      if mc.accepts m then
        match mc.slot with
        | none => some sc
        | some s =>
            match sc.getD s none with
            | some old => if old = .count m then some sc else none
            | none => some (sc.set s (some (.count m)))
      else none

/-- `assign_ones`: the injective assignments of the simple items to child
positions, each with the joined scalars; `used` the positions taken so
far, in item order. -/
def assignOnes (S : SeqSpec) (src : Source) (kids : List (C × Nat)) :
    List (Nat × Option MultCheck) → List Nat → Slots → List (List Nat × Slots)
  | [], used, sc => [(used, sc)]
  | (j, μ) :: os, used, sc =>
      (List.range kids.length).flatMap (fun p =>
        if p ∈ used then []
        else
          match kids[p]? with
          | none => []
          | some (k, m) =>
              match admit S.ac μ m sc with
              | none => []
              | some base =>
                  (src.one j k base).flatMap (fun b => assignOnes S src kids os (used ++ [p]) b))

/-- The remaining children: those at positions not used, in stored order. -/
def restOf (kids : List (C × Nat)) (used : List Nat) : List (C × Nat) :=
  (List.range kids.length).filterMap (fun p => if p ∈ used then none else kids[p]?)

/-- `assign_filters`, phase 1: the rows of filter `fi` at a remaining child
`(k, m)`, the multiplicity gate first, deduplicated. -/
def filterRowsAC (S : SeqSpec) (src : Source) (fi : Nat) (k : C) (m : Nat) : List Slots :=
  let f := S.filterAt fi
  let init := blank f.nvars
  (match f.mult with
    | some mc =>
        if mc.accepts m then
          src.filter fi k (match mc.slot with | some s => init.set s (some (.count m)) | none => init)
        else []
    | none => if m = 1 then src.filter fi k init else []).dedup

/-- Phase 2: the (filter, row) choices of a remaining child, `:except`
applied. -/
def choicesAt (S : SeqSpec) (src : Source) (kid : C × Nat) : List (Nat × Slots) :=
  (List.range S.filters.length).flatMap (fun fi =>
    let f := S.filterAt fi
    if (match f.except with
        | some o => !(filterRowsAC S src o kid.1 kid.2).isEmpty
        | none => false) then []
    else (filterRowsAC S src fi kid.1 kid.2).map (fun r => (fi, r)))

/-- A child's options in the odometer: its choices, or the bare sequence. -/
def pickOpts (cs : List (Nat × Slots)) : List (Option (Nat × Slots)) :=
  if cs.isEmpty then [none] else cs.map some

/-- The environment of one pick: per filter the children that chose it, in
`rest` order, with their multiplicities (AC) and columns; the bare sequence
gets the children with no choice; the scalars. -/
def envOfAC (S : SeqSpec) (rest : List (C × Nat)) (sc : Slots)
    (pick : List (Option (Nat × Slots))) : Env :=
  let zipped := rest.zip pick
  let toBare := zipped.filterMap (fun z => if z.2.isNone then some z.1 else none)
  { scalars := sc
    filt := (List.range S.filters.length).map (fun fi =>
      let taken := zipped.filterMap (fun z => match z.2 with
        | some (cf, r) => if cf = fi then some (z.1, r) else none
        | none => none)
      some ⟨taken.map (·.1.1), if S.ac then taken.map (·.1.2) else [],
        colsOf (S.filterAt fi).nvars (taken.map (·.2))⟩)
    bare := if S.hasBare then
      some ⟨toBare.map (·.1), if S.ac then toBare.map (·.2) else []⟩ else none }

/-- `assign_filters`: no match when a child has no choice and there is no
bare item; else one environment per element of the product of the choice
lists. -/
def assignFilters (S : SeqSpec) (src : Source) (rest : List (C × Nat)) (sc : Slots) :
    List Env :=
  if !S.hasBare && rest.any (fun kid => (choicesAt S src kid).isEmpty) then []
  else (List.sections (rest.map (fun kid => pickOpts (choicesAt S src kid)))).map
    (envOfAC S rest sc)

/-- The AC/ACI matches before deduplication. -/
def rawAC (S : SeqSpec) (src : Source) (kids : List (C × Nat)) : List Env :=
  (assignOnes S src kids S.ones [] (blank S.nScalars)).flatMap (fun r =>
    assignFilters S src (restOf kids r.1) r.2)

/-! ## The node's match set -/

/-- The candidate matches, before deduplication (what the bound counts). -/
def rawMatches (S : SeqSpec) (src : Source) (kids : List (C × Nat)) : List Env :=
  if S.assoc then rawA S src (kids.map (·.1)) else rawAC S src kids

/-- `assemble`: the set of matches, or nothing for a node over the bound. -/
def assemble (S : SeqSpec) (src : Source) (kids : List (C × Nat)) : List Env :=
  let raw := rawMatches S src kids
  if raw.length ≤ MAX_MATCHES then raw.dedup else []

/-- The children of a variadic node as (class, multiplicity) in stored
order (`for_each_child`; a multiset's entries in class order). -/
def kidsOf : Children → Option (List (C × Nat))
  | .seq cs => some (cs.map (fun c => (c, 1)))
  | .mset m => some (Multiset.entries m)
  | .set s => some ((s.sort (· ≤ ·)).map (fun c => (c, 1)))
  | _ => none

/-! ## `fill`: writing a match into the binding (A.8.3) -/

/-- The classes of a column; non-classes dropped (`fillOk` rejects them). -/
def colClasses (col : List (Option Val)) : List C :=
  col.filterMap (fun v => match v with | some (.cls c) => some c | _ => none)

def colLits (col : List (Option Val)) : List Lit :=
  col.filterMap (fun v => match v with | some (.lit x) => some x | _ => none)

def writeRest (σ : XBinding) (rr : RestRef) (elems : List C) (mults : List Nat) : XBinding :=
  match rr with
  | .seq v => σ.setSeqRest v elems
  | .set v => σ.setSetRest v elems.toFinset
  | .mset v => σ.setRest v (ofEntries (elems.zip mults))

def writeCol (σ : XBinding) (cr : ColRef) (col : List (Option Val)) : XBinding :=
  match cr with
  | .node v => σ.setSeqRest v (colClasses col)
  | .lit v => σ.setLitSeq v (colLits col)
  | .mult => σ

def writeScalar (σ : XBinding) (sr : ScalarRef) (v : Option Val) : XBinding :=
  match sr, v with
  | .node x, some (.cls c) => σ.setCls x c
  | .lit x, some (.lit l) => σ.setLit x l
  | .mult x, some (.count m) => σ.setMult x m
  | _, _ => σ

def writeFilter (σ : XBinding) (fl : FilterLayout) (fb : Option FBind) : XBinding :=
  match fb with
  | none => σ
  | some fb =>
      ((fl.cols.zip fb.cols).foldl (fun σ p => writeCol σ p.1 p.2)
        (writeRest σ fl.elems fb.elems fb.mults))

/-- `fill`: the match in the rule's layout. -/
def writeEnv (S : SeqSpec) (σ : XBinding) (e : Env) : XBinding :=
  let σ₁ := (S.layout.filters.zip e.filt).foldl (fun σ p => writeFilter σ p.1 p.2) σ
  let σ₂ := match S.layout.bare, e.bare with
    | some rr, some bb => writeRest σ₁ rr bb.elems bb.mults
    | _, _ => σ₁
  (S.layout.scalars.zip e.scalars).foldl (fun σ p => writeScalar σ p.1 p.2) σ₂

/-- Whether `fill` succeeds: every filter of the layout bound, its class
and literal columns of the right kind, the bare sequence bound when the
layout has one, every scalar of the kind its slot expects. -/
def fillOk (S : SeqSpec) (e : Env) : Bool :=
  (S.layout.filters.zip e.filt).all (fun p =>
    match p.2 with
    | none => false
    | some fb =>
        (p.1.cols.zip fb.cols).all (fun q =>
          match q.1 with
          | .node _ => q.2.all (fun v => match v with | some (.cls _) => true | _ => false)
          | .lit _ => q.2.all (fun v => match v with | some (.lit _) => true | _ => false)
          | .mult => true)) &&
  (match S.layout.bare, e.bare with
    | some _, none => false
    | _, _ => true) &&
  (S.layout.scalars.zip e.scalars).all (fun p =>
    match p.1, p.2 with
    | .node _, some (.cls _) => true
    | .lit _, some (.lit _) => true
    | .mult _, some (.count _) => true
    | _, _ => false)

end Semper.EMatch.Steps
