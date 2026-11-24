import SemperProofs.EMatch.Steps.Interp

/-!
# `Collect`: the sequence-pattern matching relation and its assembler

The declarative relation `SeqMatch` of A.8.2, stated by node over the
children `kids` and a row `Source`:

* under A, `AParse`: a parse of the child list by the items in written
  order (a span per item, one chosen row per filtered child, the simple
  items' rows joined through the scalars), and `MaximalA`: the gap
  condition of `assoc_maximal`;
* under AC/ACI, `OnesAssign`: the injective assignment of the simple
  items to child positions with the multiplicity gates (`admit_spec`), then
  per remaining child a choice `PickOk` among the (filter, row) pairs
  `choicesAt` (`:except` applied), the children without a choice to the
  bare sequence, or no match without one.

`collect_sound` / `collect_complete`: membership in `assemble` is the
relation, for a node under the `MAX_MATCHES` bound (hypothesis `hbound`);
`assemble_nodup`: the match set is a set. `collect_step` lifts this to the
`Collect` step at a bound node (the root drive). `Source.ofPlans` is the
row source of the engine's probe, stratified over `runXL`.
-/

namespace Semper.EMatch.Steps

open Semper.EMatch

/-! ## Under A -/

/-- The parse relation (`assoc_go`): `AParse items pos sc bs sc'` says the
items parse `kids` from `pos` to the end with item bindings `bs`, the
scalars going from `sc` to `sc'`. -/
inductive AParse (S : SeqSpec) (src : Source) (kids : List C) :
    List SItem → Nat → Slots → List ABind → Slots → Prop
  | nil {sc : Slots} : AParse S src kids [] kids.length sc [] sc
  | one {j : Nat} {μ : Option MultCheck} {items : List SItem} {pos : Nat} {sc b sc' : Slots}
      {k : C} {bs : List ABind} :
      kids[pos]? = some k → b ∈ src.one j k sc →
      AParse S src kids items (pos + 1) b bs sc' →
      AParse S src kids (.one j μ :: items) pos sc (.one pos :: bs) sc'
  | bare {items : List SItem} {pos e : Nat} {sc sc' : Slots} {bs : List ABind} :
      pos ≤ e → e ≤ kids.length → AParse S src kids items e sc bs sc' →
      AParse S src kids (.bare :: items) pos sc (.bare pos e :: bs) sc'
  | filter {fi : Nat} {items : List SItem} {pos e : Nat} {sc sc' : Slots}
      {rows : List Slots} {bs : List ABind} :
      pos ≤ e → e ≤ kids.length →
      List.Forall₂ (fun r c => r ∈ matchedA S src fi c) rows ((kids.drop pos).take (e - pos)) →
      AParse S src kids items e sc bs sc' →
      AParse S src kids (.filter fi :: items) pos sc (.filter fi pos e rows :: bs) sc'

theorem mem_assocParses (S : SeqSpec) (src : Source) (kids : List C) (items : List SItem) :
    ∀ (pos : Nat) (sc : Slots) (bs : List ABind) (sc' : Slots),
      (bs, sc') ∈ assocParses S src kids items pos sc ↔
        AParse S src kids items pos sc bs sc' := by
  induction items with
  | nil =>
      intro pos sc bs sc'
      simp only [assocParses]
      constructor
      · intro h
        split at h
        · simp only [List.mem_singleton, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          subst ‹pos = kids.length›
          exact .nil
        · simp at h
      · intro h
        cases h
        simp
  | cons it items ih =>
      intro pos sc bs sc'
      cases it with
      | one j μ =>
          simp only [assocParses]
          constructor
          · intro h
            split at h
            · simp at h
            · rename_i k hk
              simp only [List.mem_flatMap, List.mem_map, Prod.mk.injEq] at h
              obtain ⟨b, hb, ⟨bs₁, sc₁⟩, hmem, rfl, rfl⟩ := h
              exact .one hk hb ((ih _ _ _ _).1 hmem)
          · intro h
            cases h with
            | one hk hb hp =>
                rw [hk]
                simp only [List.mem_flatMap, List.mem_map, Prod.mk.injEq]
                exact ⟨_, hb, ⟨_, _⟩, (ih _ _ _ _).2 hp, rfl, rfl⟩
      | bare =>
          simp only [assocParses]
          constructor
          · intro h
            simp only [List.mem_flatMap, List.mem_range'_1, List.mem_map, Prod.mk.injEq] at h
            obtain ⟨e, ⟨h₁, h₂⟩, ⟨bs₁, sc₁⟩, hmem, rfl, rfl⟩ := h
            exact .bare h₁ (by omega) ((ih _ _ _ _).1 hmem)
          · intro h
            cases h with
            | bare h₁ h₂ hp =>
                simp only [List.mem_flatMap, List.mem_range'_1, List.mem_map, Prod.mk.injEq]
                exact ⟨_, ⟨h₁, by omega⟩, ⟨_, _⟩, (ih _ _ _ _).2 hp, rfl, rfl⟩
      | filter fi =>
          simp only [assocParses]
          constructor
          · intro h
            simp only [List.mem_flatMap, List.mem_range'_1, List.mem_map, Prod.mk.injEq] at h
            obtain ⟨e, ⟨h₁, h₂⟩, rows, hrows, ⟨bs₁, sc₁⟩, hmem, rfl, rfl⟩ := h
            rw [List.mem_sections, List.forall₂_map_right_iff] at hrows
            exact .filter h₁ (by omega) hrows ((ih _ _ _ _).1 hmem)
          · intro h
            cases h with
            | filter h₁ h₂ hrows hp =>
                simp only [List.mem_flatMap, List.mem_range'_1, List.mem_map, Prod.mk.injEq]
                refine ⟨_, ⟨h₁, by omega⟩, _, ?_, ⟨_, _⟩, (ih _ _ _ _).2 hp, rfl, rfl⟩
                rw [List.mem_sections, List.forall₂_map_right_iff]
                exact hrows

/-- The span of an item binding. -/
def ABind.span : ABind → Nat × Nat
  | .one pos => (pos, pos + 1)
  | .bare s e => (s, e)
  | .filter _ s e _ => (s, e)

/-- The end of the span before position `w`, or `pos` at the start. -/
def spanBefore (bs : List ABind) (pos : Nat) : Nat → Nat
  | 0 => pos
  | w + 1 => (bs[w]?.map (fun b => (ABind.span b).2)).getD pos

/-- The spans of a parse are contiguous (`p_0 = pos`, `p_t = N`, one span
per item), the spec's reading of a parse. -/
theorem AParse.spans_chain {S : SeqSpec} {src : Source} {kids : List C} :
    ∀ {items : List SItem} {pos : Nat} {sc : Slots} {bs : List ABind} {sc' : Slots},
      AParse S src kids items pos sc bs sc' →
        bs.length = items.length ∧
        (∀ (w : Nat) (b : ABind), bs[w]? = some b →
          (ABind.span b).1 = spanBefore bs pos w ∧ (ABind.span b).1 ≤ (ABind.span b).2) ∧
        ((bs.getLast?.map (fun b => (ABind.span b).2)).getD pos = kids.length) := by
  intro h
  induction h with
  | nil => simp
  | one hk hb _ ih => exact spans_step ih (by simp [ABind.span])
  | bare h₁ h₂ _ ih => exact spans_step ih (by simp [ABind.span, h₁])
  | filter h₁ h₂ _ _ ih => exact spans_step ih (by simp [ABind.span, h₁])
where
  spans_step {b : ABind} {bs : List ABind} {pos e N : Nat} {n : Nat}
      (ih : bs.length = n ∧
        (∀ (w : Nat) (b' : ABind), bs[w]? = some b' →
          (ABind.span b').1 = spanBefore bs e w ∧ (ABind.span b').1 ≤ (ABind.span b').2) ∧
        ((bs.getLast?.map (fun b => (ABind.span b).2)).getD e = N))
      (hb : ABind.span b = (pos, e) ∧ pos ≤ e) :
      (b :: bs).length = n + 1 ∧
        (∀ (w : Nat) (b' : ABind), (b :: bs)[w]? = some b' →
          (ABind.span b').1 = spanBefore (b :: bs) pos w ∧
            (ABind.span b').1 ≤ (ABind.span b').2) ∧
        (((b :: bs).getLast?.map (fun b => (ABind.span b).2)).getD pos = N) := by
    obtain ⟨hlen, hw, hlast⟩ := ih
    refine ⟨by simp [hlen], ?_, ?_⟩
    · intro w b' hb'
      cases w with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hb'
          subst hb'
          simp [spanBefore, hb.1, hb.2]
      | succ w =>
          simp only [List.getElem?_cons_succ] at hb'
          obtain ⟨h1, h2⟩ := hw w b' hb'
          refine ⟨?_, h2⟩
          cases w with
          | zero => simpa [spanBefore, hb.1] using h1
          | succ w =>
              simp only [spanBefore, List.getElem?_cons_succ] at h1 ⊢
              rw [h1]
              have : w < bs.length := by
                have := (List.getElem?_eq_some_iff.1 hb').1
                omega
              simp [List.getElem?_eq_getElem this]
    · cases bs with
      | nil => simpa [hb.1] using hlast
      | cons c cs =>
          rw [List.getLast?_cons_cons]
          obtain ⟨x, hx⟩ : ∃ x, (c :: cs).getLast? = some x :=
            ⟨_, List.getLast?_eq_getLast (by simp)⟩
          rw [hx] at hlast ⊢
          simpa using hlast

/-- The gap condition between an item binding and its successor
(`assoc_maximal`, one pair): a filter run followed by a nonempty gap
whose first child the filter matches, or a nonempty gap followed by a
filter run whose last child the filter matches, is not maximal. -/
def adjOk (S : SeqSpec) (src : Source) (kids : List C) : ABind → Option ABind → Bool
  | .filter fi _ _ _, some (.bare s e) =>
      !decide (s < e) || (matchedAt S src kids fi s).isEmpty
  | .bare s e, some (.filter fi _ _ _) =>
      !decide (s < e) || (matchedAt S src kids fi (e - 1)).isEmpty
  | _, _ => true

theorem maximalA_cons (S : SeqSpec) (src : Source) (kids : List C) (x : ABind)
    (rest : List ABind) :
    maximalA S src kids (x :: rest) = (adjOk S src kids x rest[0]? && maximalA S src kids rest) := by
  cases x <;> cases rest with
  | nil => simp [maximalA, adjOk]
  | cons y rest => cases y <;> simp [maximalA, adjOk]

/-- Maximality, declaratively: every adjacent pair of item bindings is a
maximal pair. -/
def MaximalA (S : SeqSpec) (src : Source) (kids : List C) (bs : List ABind) : Prop :=
  ∀ w x, bs[w]? = some x → adjOk S src kids x bs[w + 1]? = true

theorem maximalA_iff (S : SeqSpec) (src : Source) (kids : List C) (bs : List ABind) :
    maximalA S src kids bs = true ↔ MaximalA S src kids bs := by
  induction bs with
  | nil => simp [maximalA, MaximalA]
  | cons x rest ih =>
      rw [maximalA_cons, Bool.and_eq_true, ih]
      constructor
      · rintro ⟨h₀, h⟩ w y hy
        cases w with
        | zero => simp at hy; subst hy; simpa using h₀
        | succ w => exact h w y hy
      · intro h
        refine ⟨by simpa using h 0 x rfl, fun w y hy => h (w + 1) y hy⟩

/-- The matches under A (A.8.2, "Under A"). -/
def SeqMatchA (S : SeqSpec) (src : Source) (kids : List C) (env : Env) : Prop :=
  ∃ bs sc, AParse S src kids S.items 0 (blank S.nScalars) bs sc ∧
    MaximalA S src kids bs ∧ env = envOfA S kids bs sc

theorem mem_rawA (S : SeqSpec) (src : Source) (kids : List C) (env : Env) :
    env ∈ rawA S src kids ↔ SeqMatchA S src kids env := by
  simp only [rawA, List.mem_map, List.mem_filter, SeqMatchA]
  constructor
  · rintro ⟨⟨bs, sc⟩, ⟨hmem, hmax⟩, rfl⟩
    exact ⟨bs, sc, (mem_assocParses _ _ _ _ _ _ _ _).1 hmem, (maximalA_iff _ _ _ _).1 hmax, rfl⟩
  · rintro ⟨bs, sc, hp, hmax, rfl⟩
    exact ⟨⟨bs, sc⟩, ⟨(mem_assocParses _ _ _ _ _ _ _ _).2 hp, (maximalA_iff _ _ _ _).2 hmax⟩, rfl⟩

/-! ## Under AC / ACI -/

/-- Admissibility of a child for a simple item, declaratively
(`seq_collect.rs:527-541`): an unannotated item takes multiplicity 1 under
AC and anything under ACI; an annotated one a multiplicity its annotation
accepts, its multiplicity variable (slot `s`) unbound and then bound to
the count, or already bound to it. -/
theorem admit_spec (ac : Bool) (μ : Option MultCheck) (m : Nat) (sc base : Slots) :
    admit ac μ m sc = some base ↔
      (μ = none ∧ (ac = false ∨ m = 1) ∧ base = sc) ∨
      (∃ mc, μ = some mc ∧ mc.accepts m = true ∧
        ((mc.slot = none ∧ base = sc) ∨
          ∃ s, mc.slot = some s ∧
            ((sc.getD s none = some (.count m) ∧ base = sc) ∨
              (sc.getD s none = none ∧ base = sc.set s (some (.count m)))))) := by
  cases μ with
  | none =>
      simp only [admit, reduceCtorEq, false_and, exists_false, or_false, true_and]
      cases ac <;> by_cases hm : m = 1 <;> simp [hm, eq_comm]
  | some mc =>
      simp only [admit, reduceCtorEq, false_and, false_or, Option.some.injEq, exists_eq_left']
      by_cases ha : mc.accepts m
      · simp only [ha, ↓reduceIte, true_and]
        cases hs : mc.slot with
        | none => simp [eq_comm]
        | some s =>
            simp only [reduceCtorEq, false_and, false_or, Option.some.injEq, exists_eq_left']
            cases ho : sc.getD s none with
            | none => simp [eq_comm]
            | some old =>
                by_cases hold : old = .count m
                · subst hold; simp [eq_comm]
                · simp [hold]
      · simp [ha]

/-- The injective assignment of the simple items (`assign_ones`):
`OnesAssign os used sc used' sc'` says the items `os`, from the positions
`used` taken so far and scalars `sc`, take distinct further positions
(appended in item order) ending at `used'` with the joined scalars `sc'`. -/
inductive OnesAssign (S : SeqSpec) (src : Source) (kids : List (C × Nat)) :
    List (Nat × Option MultCheck) → List Nat → Slots → List Nat → Slots → Prop
  | nil {used : List Nat} {sc : Slots} : OnesAssign S src kids [] used sc used sc
  | cons {j : Nat} {μ : Option MultCheck} {os : List (Nat × Option MultCheck)}
      {used used' : List Nat} {sc base b sc' : Slots} {p : Nat} {k : C} {m : Nat} :
      p ∉ used → kids[p]? = some (k, m) → admit S.ac μ m sc = some base →
      b ∈ src.one j k base → OnesAssign S src kids os (used ++ [p]) b used' sc' →
      OnesAssign S src kids ((j, μ) :: os) used sc used' sc'

theorem mem_assignOnes (S : SeqSpec) (src : Source) (kids : List (C × Nat))
    (os : List (Nat × Option MultCheck)) :
    ∀ (used : List Nat) (sc : Slots) (used' : List Nat) (sc' : Slots),
      (used', sc') ∈ assignOnes S src kids os used sc ↔
        OnesAssign S src kids os used sc used' sc' := by
  induction os with
  | nil =>
      intro used sc used' sc'
      simp only [assignOnes, List.mem_singleton, Prod.mk.injEq]
      constructor
      · rintro ⟨rfl, rfl⟩; exact .nil
      · intro h; cases h; exact ⟨rfl, rfl⟩
  | cons o os ih =>
      intro used sc used' sc'
      obtain ⟨j, μ⟩ := o
      simp only [assignOnes, List.mem_flatMap, List.mem_range]
      constructor
      · rintro ⟨p, hp, h⟩
        split at h
        · simp at h
        · split at h
          · simp at h
          · rename_i hused _ k m hk
            split at h
            · simp at h
            · rename_i _ base hadm
              simp only [List.mem_flatMap] at h
              obtain ⟨b, hb, hmem⟩ := h
              exact .cons hused hk hadm hb ((ih _ _ _ _).1 hmem)
      · intro h
        cases h with
        | cons hused hk hadm hb hrest =>
            rename_i p k m
            refine ⟨p, ?_, ?_⟩
            · exact (List.getElem?_eq_some_iff.1 hk).1
            · simp only [hused, ↓reduceIte, hk, hadm, List.mem_flatMap]
              exact ⟨_, hb, (ih _ _ _ _).2 hrest⟩

/-- The rows of a filter at a remaining child, declaratively: the
multiplicity gate (an annotated filter takes a multiplicity its annotation
accepts, its variable pre-bound; an unannotated filter takes multiplicity 1
only), then the sub-query's rows. -/
theorem mem_filterRowsAC (S : SeqSpec) (src : Source) (fi : Nat) (k : C) (m : Nat) (r : Slots) :
    r ∈ filterRowsAC S src fi k m ↔
      (match (S.filterAt fi).mult with
        | some mc => mc.accepts m = true ∧
            r ∈ src.filter fi k (match mc.slot with
              | some s => (blank (S.filterAt fi).nvars).set s (some (.count m))
              | none => blank (S.filterAt fi).nvars)
        | none => m = 1 ∧ r ∈ src.filter fi k (blank (S.filterAt fi).nvars)) := by
  simp only [filterRowsAC, List.mem_dedup]
  cases (S.filterAt fi).mult with
  | none => by_cases hm : m = 1 <;> simp [hm]
  | some mc => by_cases ha : mc.accepts m <;> cases hs : mc.slot <;> simp [ha, hs]

/-- The choices of a remaining child, declaratively: a filter `fi` with a
row at the child, unless its `:except` sibling has a row there. -/
theorem mem_choicesAt (S : SeqSpec) (src : Source) (kid : C × Nat) (fi : Nat) (r : Slots) :
    (fi, r) ∈ choicesAt S src kid ↔
      fi < S.filters.length ∧
      (∀ o, (S.filterAt fi).except = some o → filterRowsAC S src o kid.1 kid.2 = []) ∧
      r ∈ filterRowsAC S src fi kid.1 kid.2 := by
  simp only [choicesAt, List.mem_flatMap, List.mem_range, List.mem_ite_nil_left, List.mem_map,
    Prod.mk.injEq, exists_eq_right_right, Bool.not_eq_true]
  constructor
  · rintro ⟨fi', hfi, hc, hr, rfl⟩
    refine ⟨hfi, ?_, hr⟩
    intro o ho
    rw [ho] at hc
    simpa using hc
  · rintro ⟨hfi, hexc, hr⟩
    refine ⟨fi, hfi, ?_, hr, rfl⟩
    cases h : (S.filterAt fi).except with
    | none => rfl
    | some o => simp [hexc o h]

/-- A child's pick: none when it has no choice (it goes to the bare
sequence), else one of its choices. -/
def PickOk (S : SeqSpec) (src : Source) (kid : C × Nat) (p : Option (Nat × Slots)) : Prop :=
  (p = none ∧ choicesAt S src kid = []) ∨ (∃ c, p = some c ∧ c ∈ choicesAt S src kid)

theorem mem_pickOpts (cs : List (Nat × Slots)) (p : Option (Nat × Slots)) :
    p ∈ pickOpts cs ↔ (p = none ∧ cs = []) ∨ (∃ c, p = some c ∧ c ∈ cs) := by
  simp only [pickOpts]
  by_cases h : cs.isEmpty
  · simp only [h, ↓reduceIte, List.mem_singleton]
    rw [List.isEmpty_iff] at h
    subst h
    simp
  · simp only [h, Bool.false_eq_true, ↓reduceIte, List.mem_map]
    rw [List.isEmpty_iff] at h
    constructor
    · rintro ⟨c, hc, rfl⟩; exact Or.inr ⟨c, rfl, hc⟩
    · rintro (⟨_, hcs⟩ | ⟨c, rfl, hc⟩)
      · exact absurd hcs h
      · exact ⟨c, hc, rfl⟩

theorem mem_assignFilters (S : SeqSpec) (src : Source) (rest : List (C × Nat)) (sc : Slots)
    (env : Env) :
    env ∈ assignFilters S src rest sc ↔
      (S.hasBare = false → ∀ kid ∈ rest, choicesAt S src kid ≠ []) ∧
      ∃ pick, List.Forall₂ (PickOk S src) rest pick ∧ env = envOfAC S rest sc pick := by
  simp only [assignFilters]
  have hpick : ∀ pick, pick ∈ List.sections (rest.map (fun kid => pickOpts (choicesAt S src kid))) ↔
      List.Forall₂ (PickOk S src) rest pick := by
    intro pick
    rw [List.mem_sections, List.forall₂_map_right_iff]
    constructor
    · intro h
      refine h.flip.imp ?_
      intro kid p hp
      exact (mem_pickOpts _ _).1 hp
    · intro h
      refine h.flip.imp ?_
      intro p kid hp
      exact (mem_pickOpts _ _).2 hp
  split
  · rename_i hcond
    simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, List.any_eq_true,
      List.isEmpty_iff] at hcond
    simp only [List.not_mem_nil, false_iff, not_and, not_exists]
    intro hb
    obtain ⟨kid, hkid, hempty⟩ := hcond.2
    exact absurd hempty (hb hcond.1 kid hkid)
  · rename_i hcond
    simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, List.any_eq_true,
      List.isEmpty_iff, not_and, not_exists] at hcond
    simp only [List.mem_map]
    constructor
    · rintro ⟨pick, hp, rfl⟩
      exact ⟨fun hb kid hkid => hcond hb kid hkid, pick, (hpick pick).1 hp, rfl⟩
    · rintro ⟨_, pick, hp, rfl⟩
      exact ⟨pick, (hpick pick).2 hp, rfl⟩

/-- The matches under AC / ACI (A.8.2, "Under AC / ACI"). -/
def SeqMatchAC (S : SeqSpec) (src : Source) (kids : List (C × Nat)) (env : Env) : Prop :=
  ∃ used sc, OnesAssign S src kids S.ones [] (blank S.nScalars) used sc ∧
    (S.hasBare = false → ∀ kid ∈ restOf kids used, choicesAt S src kid ≠ []) ∧
    ∃ pick, List.Forall₂ (PickOk S src) (restOf kids used) pick ∧
      env = envOfAC S (restOf kids used) sc pick

theorem mem_rawAC (S : SeqSpec) (src : Source) (kids : List (C × Nat)) (env : Env) :
    env ∈ rawAC S src kids ↔ SeqMatchAC S src kids env := by
  simp only [rawAC, List.mem_flatMap, SeqMatchAC]
  constructor
  · rintro ⟨⟨used, sc⟩, hmem, h⟩
    obtain ⟨hb, pick, hp, rfl⟩ := (mem_assignFilters _ _ _ _ _).1 h
    exact ⟨used, sc, (mem_assignOnes _ _ _ _ _ _ _ _).1 hmem, hb, pick, hp, rfl⟩
  · rintro ⟨used, sc, hmem, hb, pick, hp, rfl⟩
    exact ⟨⟨used, sc⟩, (mem_assignOnes _ _ _ _ _ _ _ _).2 hmem,
      (mem_assignFilters _ _ _ _ _).2 ⟨hb, pick, hp, rfl⟩⟩

/-! ## The node's match set -/

/-- `SeqMatch S src kids env`: `env` is a match of the sequence pattern at
a node with children `kids`. -/
def SeqMatch (S : SeqSpec) (src : Source) (kids : List (C × Nat)) (env : Env) : Prop :=
  if S.assoc then SeqMatchA S src (kids.map (·.1)) env else SeqMatchAC S src kids env

theorem mem_rawMatches (S : SeqSpec) (src : Source) (kids : List (C × Nat)) (env : Env) :
    env ∈ rawMatches S src kids ↔ SeqMatch S src kids env := by
  simp only [rawMatches, SeqMatch]
  split
  · exact mem_rawA _ _ _ _
  · exact mem_rawAC _ _ _ _

/-- Soundness of the assembler: every environment it emits is a match. -/
theorem collect_sound (S : SeqSpec) (src : Source) (kids : List (C × Nat)) (env : Env)
    (h : env ∈ assemble S src kids) : SeqMatch S src kids env := by
  simp only [assemble] at h
  split at h
  · exact (mem_rawMatches _ _ _ _).1 (List.mem_dedup.1 h)
  · simp at h

/-- Completeness of the assembler: every match of a node under the bound
is emitted. -/
theorem collect_complete (S : SeqSpec) (src : Source) (kids : List (C × Nat)) (env : Env)
    (hbound : (rawMatches S src kids).length ≤ MAX_MATCHES)
    (h : SeqMatch S src kids env) : env ∈ assemble S src kids := by
  simp only [assemble, hbound, ↓reduceIte]
  exact List.mem_dedup.2 ((mem_rawMatches _ _ _ _).2 h)

/-- A node's matches are a set. -/
theorem assemble_nodup (S : SeqSpec) (src : Source) (kids : List (C × Nat)) :
    (assemble S src kids).Nodup := by
  simp only [assemble]
  split
  · exact List.nodup_dedup _
  · exact List.nodup_nil

/-- A node over the bound is skipped. -/
theorem assemble_over_bound (S : SeqSpec) (src : Source) (kids : List (C × Nat))
    (h : MAX_MATCHES < (rawMatches S src kids).length) : assemble S src kids = [] := by
  simp [assemble, Nat.not_le.2 h]

/-- The `Collect` step at a bound node (the root drive): its bindings are
exactly the matches written into the binding in the rule's layout. -/
theorem collect_step (X : XGraph) (Γ : GVar → C) (M : PredModel) (v : Var) (S : SeqSpec)
    (σ σ' : XBinding) (id : NodeId) (n : Node) (kids : List (C × Nat))
    (hv : σ.base.node v = some id) (hn : X.G.lookupNode id = some n)
    (hk : kidsOf n.children = some kids)
    (hbound : (rawMatches S (S.src X Γ) kids).length ≤ MAX_MATCHES) :
    σ' ∈ stepList X Γ M (.collect v S) σ ↔
      ∃ env, SeqMatch S (S.src X Γ) kids env ∧ σ' = writeEnv S σ env := by
  rw [stepList_collect_bound X Γ M v S σ id n kids hv hn hk]
  simp only [List.mem_map]
  constructor
  · rintro ⟨env, henv, rfl⟩
    exact ⟨env, collect_sound _ _ _ _ henv, rfl⟩
  · rintro ⟨env, henv, rfl⟩
    exact ⟨env, collect_complete _ _ _ _ hbound henv, rfl⟩

/-- The `Collect` step faults at a bound node iff some match cannot be
written in the layout (`fill` error, A.8.3). -/
theorem collect_fault (X : XGraph) (Γ : GVar → C) (M : PredModel) (v : Var) (S : SeqSpec)
    (σ : XBinding) (id : NodeId) (n : Node) (kids : List (C × Nat))
    (hv : σ.base.node v = some id) (hn : X.G.lookupNode id = some n)
    (hk : kidsOf n.children = some kids) :
    stepFault X Γ M (.collect v S) σ = true ↔
      ∃ env ∈ assemble S (S.src X Γ) kids, fillOk S env = false := by
  simp [stepFault, hv, hn, hk]

/-! ## The engine's row source, stratified over the ordinary engine (A.8.1) -/

/-- A variable of a sub-query's row (`SubVar`): read as a class or a literal. -/
inductive SubVar where
  | cls (x : Var)
  | lit (l : Var)
  deriving DecidableEq

/-- A sub-query (`SubQuery`): its plan, scheduled with the root class
variable seeded, and the variables of its rows. -/
structure SubQuery where
  plan : XPlan
  root : Var
  vars : List SubVar

def readVar (σ : XBinding) : SubVar → Option Val
  | .cls x => (σ.base.cls x).map Val.cls
  | .lit l => (σ.lit l).map Val.lit

/-- The rows of a sub-query at a class (`probe`, `seq_query.rs:204-237`):
the matches of the plan seeded with the root at the class, projected on
the variables (a match leaving one unbound is dropped; the engine's rows
are total for a well-formed plan). -/
def rowsOf (X : XGraph) (Γ : GVar → C) (M : PredModel) (q : SubQuery) (c : C) : List (List Val) :=
  (runXL X Γ M q.plan (XBinding.empty.setCls q.root c)).filterMap (fun σ => q.vars.mapM (readVar σ))

/-- One step of `Source::one`'s join: write the value into its scalar
slot, or fail when an earlier item bound the slot to a different value. -/
def joinStepF (acc : Option Slots) (p : Nat × Val) : Option Slots :=
  acc.bind (fun b =>
    match b.getD p.1 none with
    | some old => if old = p.2 then some b else none
    | none => some (b.set p.1 (some p.2)))

/-- `Source::one`'s join (`seq_engine.rs:404-415`): write each value into
its scalar slot, skipping the row when an earlier item bound the slot to a
different value. -/
def joinRow (slots : List Nat) (sc : Slots) (vals : List Val) : Option Slots :=
  (slots.zip vals).foldl joinStepF (some sc)

/-- `Source::filter`'s overwrite (`seq_engine.rs:450-455`). -/
def overwrite (init : Slots) (vals : List Val) : Slots :=
  (List.range init.length).map (fun i => match vals[i]? with
    | some v => some v
    | none => init.getD i none)

/-- The engine's `Probe` source: a plan per simple item with its scalar
slots, a plan per filter. -/
def Source.ofPlans (X : XGraph) (Γ : GVar → C) (M : PredModel)
    (ones : List (SubQuery × List Nat)) (filters : List SubQuery) : Source :=
  { one := fun j c sc =>
      match ones[j]? with
      | some (q, slots) => (rowsOf X Γ M q c).filterMap (joinRow slots sc)
      | none => []
    filter := fun i c init =>
      match filters[i]? with
      | some q => (rowsOf X Γ M q c).map (overwrite init)
      | none => [] }

theorem foldl_joinStepF_none (ps : List (Nat × Val)) : ps.foldl joinStepF none = none := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [List.foldl_cons, joinStepF, ih]

theorem foldl_joinStepF_extends (ps : List (Nat × Val)) :
    ∀ (sc b : Slots), ps.foldl joinStepF (some sc) = some b →
      ∀ i v, sc.getD i none = some v → b.getD i none = some v := by
  induction ps with
  | nil =>
      intro sc b hb i v hv
      simp only [List.foldl_nil, Option.some.injEq] at hb
      subst hb
      exact hv
  | cons p ps ih =>
      intro sc b hb i v hv
      simp only [List.foldl_cons, joinStepF, Option.bind_some] at hb
      split at hb
      · split at hb
        · exact ih sc b hb i v hv
        · rw [foldl_joinStepF_none] at hb; cases hb
      · rename_i hnone
        refine ih _ b hb i v ?_
        by_cases hi : i = p.1
        · subst hi; rw [hnone] at hv; cases hv
        · rw [List.getD_eq_getElem?_getD, List.getElem?_set_ne (fun h => hi h.symm),
            ← List.getD_eq_getElem?_getD]
          exact hv

/-- A simple item's rows extend the scalars they were joined with. -/
theorem joinRow_extends (slots : List Nat) (vals : List Val) (sc b : Slots)
    (hb : joinRow slots sc vals = some b) :
    ∀ i v, sc.getD i none = some v → b.getD i none = some v :=
  foldl_joinStepF_extends _ sc b hb

end Semper.EMatch.Steps
