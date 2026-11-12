import SemperProofs.EMatch.Flatten.RegroupDefs
import SemperProofs.EMatch.Flatten.Plan

/-!
# `:flatten`: regrouped views in the flattened plan

The plan theorems of `Plan.lean` hold for any enumeration meeting
`Enumerator.Spec`. This file shows that the enumeration with regrouped
views (`Enumerator.regroup`, `RegroupDefs.lean`) meets it, for every fold
direction and any laws:

* `regroup_spec`: every view is a normalization result, and pruning by
  `takeableR` keeps exactly the accepted matches (`prune_regroup`). A
  regrouped leaf holds the class `g` of a group only when it holds a class
  of that group, and every class of the group lies below `g` through an
  `f`-member (`LeafRel`, `Desc`); `takeableR` is closed downwards
  (`takeableR_down`), so a regrouped record a match accepts derives from a
  walk record the pruning keeps;
* `regroup_plan_sound` / `regroup_plan_complete`: the flattened plan with
  regrouped views (`runER`) emits exactly the bindings satisfying every atom
  under `AtomSatG (Enumerator.regroup dir)`: an n-ary atom matches on some
  view of the walk or regrouped view of a stored node of its class, whose
  demand (with the regrouped classes needed) accepts the item classes.
-/

namespace Semper.EMatch.Flatten

open Semper.EMatch
open Binding (Extends)

/-! ## Distinct views of records -/

/-! ## Deduplication through a hash set -/

theorem mem_foldl_dedupH {α : Type} [BEq α] [LawfulBEq α] [Hashable α] :
    ∀ (l : List α) (acc : List α × Std.HashSet α), (∀ y, y ∈ acc.1 ↔ acc.2.contains y = true) →
      (∀ y, y ∈ (l.foldl (fun (acc : List α × Std.HashSet α) x =>
          if acc.2.contains x then acc else (x :: acc.1, acc.2.insert x)) acc).1 ↔
        y ∈ acc.1 ∨ y ∈ l) ∧
      (∀ y, y ∈ (l.foldl (fun (acc : List α × Std.HashSet α) x =>
          if acc.2.contains x then acc else (x :: acc.1, acc.2.insert x)) acc).1 ↔
        (l.foldl (fun (acc : List α × Std.HashSet α) x =>
          if acc.2.contains x then acc else (x :: acc.1, acc.2.insert x)) acc).2.contains y = true)
  | [], acc, h => ⟨fun y => by simp, h⟩
  | x :: l, acc, h => by
      simp only [List.foldl_cons]
      by_cases hx : acc.2.contains x = true
      · rw [if_pos hx]
        obtain ⟨h1, h2⟩ := mem_foldl_dedupH l acc h
        refine ⟨fun y => ?_, h2⟩
        rw [h1 y, List.mem_cons]
        constructor
        · rintro (h | h)
          · exact Or.inl h
          · exact Or.inr (Or.inr h)
        · rintro (h | rfl | h)
          · exact Or.inl h
          · exact Or.inl ((h _).2 hx)
          · exact Or.inr h
      · rw [if_neg hx]
        have h' : ∀ y, y ∈ (x :: acc.1, acc.2.insert x).1 ↔
            (x :: acc.1, acc.2.insert x).2.contains y = true := by
          intro y
          simp only [List.mem_cons, Std.HashSet.contains_insert, Bool.or_eq_true, beq_iff_eq]
          rw [h y]
          exact ⟨fun h => h.imp (fun e => e.symm) id, fun h => h.imp (fun e => e.symm) id⟩
        obtain ⟨h1, h2⟩ := mem_foldl_dedupH l _ h'
        refine ⟨fun y => ?_, h2⟩
        rw [h1 y]
        simp only [List.mem_cons]
        tauto

theorem mem_dedupH {α : Type} [BEq α] [LawfulBEq α] [Hashable α] {l : List α} {y : α} :
    y ∈ dedupH l ↔ y ∈ l := by
  unfold dedupH
  rw [List.mem_reverse, (mem_foldl_dedupH l ([], ∅) (fun y => by simp)).1 y]
  simp

theorem mem_foldl_altsMap :
    ∀ (recs : List RecR) (m : Std.HashMap (List (C × Nat)) (List (List LeafF)))
      (w : List (C × Nat)) (ls : List LeafF),
      ls ∈ (recs.foldl (fun m r => m.insert r.1 (r.alt :: m.getD r.1 [])) m).getD w [] ↔
        ls ∈ m.getD w [] ∨ ∃ r ∈ recs, r.1 = w ∧ r.alt = ls
  | [], m, w, ls => by simp
  | r :: recs, m, w, ls => by
      simp only [List.foldl_cons]
      rw [mem_foldl_altsMap recs _ w ls, Std.HashMap.getD_insert]
      by_cases hw : r.1 = w
      · subst hw
        rw [if_pos (beq_self_eq_true _)]
        constructor
        · rintro (h | ⟨r', hr', h1, h2⟩)
          · rcases List.mem_cons.1 h with h | h
            · exact Or.inr ⟨r, List.mem_cons_self .., rfl, h.symm⟩
            · exact Or.inl h
          · exact Or.inr ⟨r', List.mem_cons_of_mem _ hr', h1, h2⟩
        · rintro (h | ⟨r', hr', h1, h2⟩)
          · exact Or.inl (List.mem_cons_of_mem _ h)
          · rcases List.mem_cons.1 hr' with rfl | hr'
            · exact Or.inl (h2 ▸ List.mem_cons_self ..)
            · exact Or.inr ⟨r', hr', h1, h2⟩
      · have hb : (r.1 == w) = false := beq_eq_false_iff_ne.2 hw
        rw [if_neg (by simp [hb])]
        constructor
        · rintro (h | ⟨r', hr', h1, h2⟩)
          · exact Or.inl h
          · exact Or.inr ⟨r', List.mem_cons_of_mem _ hr', h1, h2⟩
        · rintro (h | ⟨r', hr', h1, h2⟩)
          · exact Or.inl h
          · rcases List.mem_cons.1 hr' with rfl | hr'
            · exact absurd h1 hw
            · exact Or.inr ⟨r', hr', h1, h2⟩

theorem mem_altsMap {recs : List RecR} {w : List (C × Nat)} {ls : List LeafF} :
    ls ∈ (altsMap recs).getD w [] ↔ ∃ r ∈ recs, r.1 = w ∧ r.alt = ls := by
  unfold altsMap
  rw [mem_foldl_altsMap]
  simp

theorem acceptsE_demandOfAlts {κ : FlatKind} {alts : List (List LeafF)} {taken : List C} :
    (demandOfAlts alts).acceptsE κ taken ↔ ∃ ls ∈ alts, ∀ l ∈ ls, l.okE κ taken := by
  unfold demandOfAlts DemandL.acceptsE
  split
  · rename_i h
    simp only [true_or, true_iff]
    exact ⟨[], h, by simp⟩
  · simp

theorem mem_enumerateFromR {recs : List RecR} {w : List (C × Nat)} {d : DemandL}
    (h : (w, d) ∈ enumerateFromR recs) : ∃ r ∈ recs, r.1 = w := by
  unfold enumerateFromR at h
  obtain ⟨w', hw', he⟩ := List.mem_map.1 h
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, -⟩ := he
  obtain ⟨r, hr, rfl⟩ := List.mem_map.1 (mem_dedupH.1 hw')
  exact ⟨r, hr, rfl⟩

/-- A view of `enumerateFromR recs` accepts `taken` exactly when some record
of the view has every leaf and every needed class passing the engine's test. -/
theorem acceptsE_enumerateFromR {κ : FlatKind} {recs : List RecR} {w : List (C × Nat)}
    {taken : List C} :
    (∃ d, (w, d) ∈ enumerateFromR recs ∧ d.acceptsE κ taken) ↔
      ∃ r ∈ recs, r.1 = w ∧ ∀ l ∈ r.alt, l.okE κ taken := by
  unfold enumerateFromR
  constructor
  · rintro ⟨d, hd, hacc⟩
    obtain ⟨w', -, he⟩ := List.mem_map.1 hd
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    obtain ⟨ls, hls, hall⟩ := acceptsE_demandOfAlts.1 hacc
    obtain ⟨r, hr, hw, rfl⟩ := mem_altsMap.1 hls
    exact ⟨r, hr, hw, hall⟩
  · rintro ⟨r, hr, rfl, hall⟩
    refine ⟨_, List.mem_map.2 ⟨r.1, mem_dedupH.2 (List.mem_map.2 ⟨r, hr, rfl⟩), rfl⟩, ?_⟩
    exact acceptsE_demandOfAlts.2 ⟨r.alt, mem_altsMap.2 ⟨r, hr, rfl, rfl⟩, hall⟩

/-! ## Levels -/

section Levels

variable (ctx : Ctx) (dir : Dir) (laws : Laws)

theorem mem_regroupLevels_of_mem :
    ∀ (F : Nat) {recs : List RecR} {r : RecR}, r ∈ recs →
      r ∈ regroupLevels ctx dir laws F recs
  | 0, _, _, h => h
  | _ + 1, _, _, h => List.mem_append_left _ h

/-- A record of the levels of `recs` is one of the levels of a single record. -/
theorem mem_regroupLevels_iff :
    ∀ (F : Nat) (recs : List RecR) (r : RecR),
      r ∈ regroupLevels ctx dir laws F recs ↔
        ∃ r₀ ∈ recs, r ∈ regroupLevels ctx dir laws F [r₀]
  | 0, recs, r => by
      simp only [regroupLevels, List.mem_singleton]
      exact ⟨fun h => ⟨r, h, rfl⟩, fun ⟨r₀, h, he⟩ => he ▸ h⟩
  | F + 1, recs, r => by
      simp only [regroupLevels, List.mem_append, List.mem_singleton]
      rw [mem_regroupLevels_iff F]
      constructor
      · rintro (h | ⟨r₁, h₁, h⟩)
        · exact ⟨r, h, Or.inl rfl⟩
        · obtain ⟨r₀, h₀, h₁'⟩ := List.mem_flatMap.1 (mem_dedupH.1 h₁)
          refine ⟨r₀, h₀, Or.inr ?_⟩
          rw [mem_regroupLevels_iff F]
          exact ⟨r₁, mem_dedupH.2 (by simpa using h₁'), h⟩
      · rintro ⟨r₀, h₀, rfl | h⟩
        · exact Or.inl h₀
        · rw [mem_regroupLevels_iff F] at h
          obtain ⟨r₁, h₁, h⟩ := h
          have h₁' : r₁ ∈ regroupRec ctx dir laws r₀ := by simpa using mem_dedupH.1 h₁
          exact Or.inr ⟨r₁, mem_dedupH.2 (List.mem_flatMap.2 ⟨r₀, h₀, h₁'⟩), h⟩

theorem regroupLevels_mono {F : Nat} {recs recs' : List RecR} (hs : ∀ r ∈ recs, r ∈ recs')
    {r : RecR} (h : r ∈ regroupLevels ctx dir laws F recs) :
    r ∈ regroupLevels ctx dir laws F recs' := by
  obtain ⟨r₀, h₀, h⟩ := (mem_regroupLevels_iff ctx dir laws F recs r).1 h
  exact (mem_regroupLevels_iff ctx dir laws F recs' r).2 ⟨r₀, hs r₀ h₀, h⟩

/-- An invariant of the walk's records preserved by one regrouping holds of
every level. -/
theorem regroupLevels_induction {P : RecR → Prop}
    (hs : ∀ r r', P r → r' ∈ regroupRec ctx dir laws r → P r') :
    ∀ (F : Nat) (recs : List RecR), (∀ r ∈ recs, P r) →
      ∀ r ∈ regroupLevels ctx dir laws F recs, P r
  | 0, _, h0, r, hr => h0 r hr
  | F + 1, recs, h0, r, hr => by
      simp only [regroupLevels, List.mem_append] at hr
      rcases hr with hr | hr
      · exact h0 r hr
      · refine regroupLevels_induction hs F _ ?_ r hr
        intro r₁ h₁
        obtain ⟨r₀, h₀, h₁'⟩ := List.mem_flatMap.1 (mem_dedupH.1 h₁)
        exact hs r₀ r₁ (h0 r₀ h₀) h₁'

end Levels

/-- The records `withinLimit` keeps: those needing at most `limit` classes. -/
theorem mem_withinLimit {limit : Nat} {recs : List RecR} {r : RecR} :
    r ∈ withinLimit limit recs ↔ r ∈ recs ∧ r.2.2.length ≤ limit := by
  simp [withinLimit]

/-- The capped levels are the levels when within the budget. -/
theorem regroupLevelsCapped_eq (ctx : Ctx) (dir : Dir) (laws : Laws) :
    ∀ (F cap : Nat) (recs l : List RecR),
      regroupLevelsCapped ctx dir laws cap F recs = some l →
      l = regroupLevels ctx dir laws F recs
  | 0, _, recs, l, h => by simpa [regroupLevelsCapped, regroupLevels] using h.symm
  | F + 1, cap, recs, l, h => by
      simp only [regroupLevelsCapped] at h
      split at h
      · simp at h
      · obtain ⟨l', h', rfl⟩ := Option.map_eq_some_iff.1 h
        rw [regroupLevelsCapped_eq ctx dir laws F _ _ l' h']
        rfl

/-! ## One regrouping, unfolded -/

theorem mem_groupsOf {ctx : Ctx} {g : C} {grp : List (C × Nat)} (h : (g, grp) ∈ groupsOf ctx) :
    ∃ id m, ctx.IsMember id m g ∧ grp = kids ctx.κ m.children := by
  unfold groupsOf at h
  obtain ⟨p, hp, he⟩ := List.mem_map.1 (List.mem_dedup.1 h)
  obtain ⟨hp, hf⟩ := List.mem_filter.1 hp
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hf
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  exact ⟨p.1, p.2, ⟨hp, hf.1, rfl, hf.2⟩, rfl⟩

theorem mem_groupsOf_of_member {ctx : Ctx} {id : NodeId} {m : Node} {g : C}
    (h : ctx.IsMember id m g) : (g, kids ctx.κ m.children) ∈ groupsOf ctx := by
  obtain ⟨hm, hf, hg, hop⟩ := h
  unfold groupsOf
  refine List.mem_dedup.2 (List.mem_map.2 ⟨(id, m), List.mem_filter.2 ⟨hm, ?_⟩, ?_⟩)
  · simp [hf, hop]
  · simp [hg]

theorem mem_regroupRec {ctx : Ctx} {dir : Dir} {laws : Laws} {r r' : RecR}
    (h : r' ∈ regroupRec ctx dir laws r) :
    ∃ g grp raw, (g, grp) ∈ groupsOf ctx ∧ raw ∈ fitsR ctx.κ dir r.1 g grp ∧
      normalize ctx.κ laws raw = .node r'.1 ∧
      r'.2.1 = r.2.1.map (addG g (grp.map Prod.fst) (r'.1.map Prod.fst)) ∧
      r'.2.2 = needsAfter g (grp.map Prod.fst) (r'.1.map Prod.fst) r.2.2 := by
  unfold regroupRec at h
  obtain ⟨⟨g, grp⟩, hgg, h⟩ := List.mem_flatMap.1 h
  obtain ⟨raw, hraw, h⟩ := List.mem_filterMap.1 h
  revert h
  cases hn : normalize ctx.κ laws raw with
  | node w =>
      intro h
      cases h
      exact ⟨g, grp, raw, hgg, hraw, hn, rfl, rfl⟩
  | _ => simp

theorem regroupRec_of {ctx : Ctx} {dir : Dir} {laws : Laws} {r : RecR} {g : C}
    {grp raw w : List (C × Nat)} (hgg : (g, grp) ∈ groupsOf ctx)
    (hraw : raw ∈ fitsR ctx.κ dir r.1 g grp) (hn : normalize ctx.κ laws raw = .node w) :
    (w, r.2.1.map (addG g (grp.map Prod.fst) (w.map Prod.fst)),
        needsAfter g (grp.map Prod.fst) (w.map Prod.fst) r.2.2) ∈
      regroupRec ctx dir laws r := by
  unfold regroupRec
  refine List.mem_flatMap.2 ⟨(g, grp), hgg, List.mem_filterMap.2 ⟨raw, hraw, ?_⟩⟩
  simp only [hn]

/-! ## Regrouped leaves -/

/-- `b` is a child class of an `f`-member of `a`. -/
def KidOf (ctx : Ctx) (a b : C) : Prop :=
  ∃ id m, ctx.IsMember id m a ∧ b ∈ (kids ctx.κ m.children).map Prod.fst

/-- `b` lies below `a` through `f`-members. -/
def Desc (ctx : Ctx) : C → C → Prop := Relation.ReflTransGen (KidOf ctx)

/-- Whether the laws can drop a class from a normal form: an identity, or, on
a multiset, `:nilpotent` or `:inverse`. -/
def canDrop (κ : FlatKind) (laws : Laws) : Bool :=
  laws.unit.isSome || (κ == .ac && (laws.nilpotent.isSome || laws.inv.isSome))

/-- A regrouped leaf of the walk's leaf `l₀`: same opened class, the same
flag unless the laws can drop a class (a regrouping whose class they drop
flags the leaf, `addG`), and every class it holds lies above a class of
`l₀`. -/
def LeafRel (ctx : Ctx) (laws : Laws) (l₀ l : LeafF) : Prop :=
  l.1.X = l₀.1.X ∧ (l.2 = l₀.2 ∨ canDrop ctx.κ laws = true) ∧
    ∀ c ∈ l.1.g, ∃ c₀ ∈ l₀.1.g, Desc ctx c c₀

/-- A record derived from `r₀`: its leaves are `r₀`'s, each regrouped. -/
def RecRel (ctx : Ctx) (laws : Laws) (r₀ r : RecR) : Prop :=
  ∃ φ : LeafF → LeafF, r.2.1 = r₀.2.1.map φ ∧ ∀ l, LeafRel ctx laws l (φ l)

theorem addG_g {g : C} {grp ws : List C} {l : LeafF} :
    (addG g grp ws l).1.g = l.1.g ∨
      ((addG g grp ws l).1.g = l.1.g ++ [g] ∧ ∃ c ∈ l.1.g, c ∈ grp) := by
  unfold addG
  split
  · rename_i h
    refine Or.inr ⟨by simp [LeafL.g], ?_⟩
    obtain ⟨-, h⟩ := h
    simpa using h
  · exact Or.inl rfl

theorem addG_X (g : C) (grp ws : List C) (l : LeafF) : (addG g grp ws l).1.X = l.1.X := by
  unfold addG; split <;> rfl

/-- The flag is kept, unless the leaf gains `g` and the view does not hold it. -/
theorem addG_flag (g : C) (grp ws : List C) (l : LeafF) :
    (addG g grp ws l).2 = (l.2 || decide (g ∉ ws ∧ g ∉ l.1.g ∧
      l.1.g.any (fun c => decide (c ∈ grp)) = true)) := by
  unfold addG
  by_cases h : g ∉ l.1.g ∧ l.1.g.any (fun c => decide (c ∈ grp)) = true
  · rw [if_pos h]
    by_cases hw : g ∈ ws <;> simp [hw, h.1, h.2]
  · rw [if_neg h]
    have hn : ¬ (g ∉ ws ∧ g ∉ l.1.g ∧ l.1.g.any (fun c => decide (c ∈ grp)) = true) :=
      fun h' => h ⟨h'.2.1, h'.2.2⟩
    simp only [hn, decide_false, Bool.or_false]

/-- The flag is kept when `g` stays in the view. -/
theorem addG_flag_of_mem {g : C} {grp ws : List C} (hg : g ∈ ws) (l : LeafF) :
    (addG g grp ws l).2 = l.2 := by
  rw [addG_flag]; simp [hg]

/-- Every fit holds the group's class. -/
theorem g_mem_fitsR {κ : FlatKind} {dir : Dir} {view : List (C × Nat)} {g : C}
    {grp raw : List (C × Nat)} (h : raw ∈ fitsR κ dir view g grp) : (g, 1) ∈ raw := by
  unfold fitsR at h
  split at h
  · simp at h
  · cases κ with
    | assoc =>
        dsimp only at h
        split at h
        · simp at h
        · obtain ⟨p, -, h⟩ := List.mem_filterMap.1 h
          split at h
          · simp only [Option.some.injEq] at h; subst h; simp
          · simp at h
    | ac | aci =>
        dsimp only at h
        split at h
        · simp at h
        · revert h
          split
          · intro h; rw [List.mem_singleton] at h; subst h; simp
          · simp

theorem normalizeList_of_not_canDrop {κ : FlatKind} {laws : Laws} (h : canDrop κ laws = false)
    (v : List (C × Nat)) : normalizeList κ laws v = canonK κ v := by
  obtain ⟨u, k, inv⟩ := laws
  cases u with
  | some _ => simp [canDrop] at h
  | none =>
      cases κ with
      | assoc => rfl
      | aci => rfl
      | ac =>
          cases k with
          | some _ => simp [canDrop] at h
          | none =>
              cases inv with
              | some _ => simp [canDrop] at h
              | none => rfl

/-- A regrouping whose class the normal form does not hold has laws that drop classes. -/
theorem canDrop_of_gone {κ : FlatKind} {dir : Dir} {laws : Laws} {view : List (C × Nat)} {g : C}
    {grp raw w : List (C × Nat)} (h : raw ∈ fitsR κ dir view g grp)
    (hn : normalize κ laws raw = .node w) (hg : g ∉ w.map Prod.fst) : canDrop κ laws = true := by
  by_contra hc
  rw [Bool.not_eq_true] at hc
  apply hg
  have hw : w = normalizeList κ laws raw := by
    unfold normalize at hn; exact ((classify_node_iff _ _ _).1 hn).1.symm
  rw [hw, normalizeList_of_not_canDrop hc]
  have hm := g_mem_fitsR h
  cases κ with
  | assoc => exact List.mem_map_of_mem (f := Prod.fst) hm
  | ac =>
      show g ∈ (Multiset.entries (ofEntries raw)).map Prod.fst
      unfold Multiset.entries
      rw [List.map_map]
      simp only [Function.comp_def, List.map_id', Finset.mem_sort, Multiset.mem_toFinset]
      refine mem_ofEntries.2 ⟨(g, 1), hm, rfl, Nat.one_pos⟩
  | aci =>
      show g ∈ (((raw.map Prod.fst).toFinset.sort (· ≤ ·)).map (fun c => (c, 1))).map Prod.fst
      rw [List.map_map]
      simp only [Function.comp_def, List.map_id', Finset.mem_sort, List.mem_toFinset]
      exact List.mem_map_of_mem (f := Prod.fst) hm

theorem leafRel_addG {ctx : Ctx} {laws : Laws} {g : C} {grp : List (C × Nat)} {ws : List C}
    (hgg : (g, grp) ∈ groupsOf ctx) (hws : g ∉ ws → canDrop ctx.κ laws = true)
    {l₀ l : LeafF} (h : LeafRel ctx laws l₀ l) :
    LeafRel ctx laws l₀ (addG g (grp.map Prod.fst) ws l) := by
  obtain ⟨hX, hf, hc⟩ := h
  refine ⟨(addG_X _ _ _ _).trans hX, ?_, ?_⟩
  · by_cases hg : g ∈ ws
    · rw [addG_flag_of_mem hg]; exact hf
    · exact Or.inr (hws hg)
  rcases addG_g (g := g) (grp := grp.map Prod.fst) (ws := ws) (l := l) with he | ⟨he, c, hcl, hcg⟩
  · rw [he]; exact hc
  · rw [he]
    intro c' hc'
    rcases List.mem_append.1 hc' with hc' | hc'
    · exact hc c' hc'
    · rw [List.mem_singleton] at hc'
      subst hc'
      obtain ⟨c₀, hc₀, hd⟩ := hc c hcl
      obtain ⟨id, m, hm, rfl⟩ := mem_groupsOf hgg
      exact ⟨c₀, hc₀, Relation.ReflTransGen.head ⟨id, m, hm, hcg⟩ hd⟩

theorem recRel_refl (ctx : Ctx) (laws : Laws) (r : RecR) : RecRel ctx laws r r :=
  ⟨id, by simp, fun l => ⟨rfl, Or.inl rfl, fun c hc => ⟨c, hc, Relation.ReflTransGen.refl⟩⟩⟩

theorem recRel_step {ctx : Ctx} {dir : Dir} {laws : Laws} {r₀ r r' : RecR}
    (h : RecRel ctx laws r₀ r) (h' : r' ∈ regroupRec ctx dir laws r) : RecRel ctx laws r₀ r' := by
  obtain ⟨g, grp, raw, hgg, hraw, hn, hl, -⟩ := mem_regroupRec h'
  obtain ⟨φ, hφ, hrel⟩ := h
  refine ⟨addG g (grp.map Prod.fst) (r'.1.map Prod.fst) ∘ φ, ?_,
    fun l => leafRel_addG hgg (fun hg => canDrop_of_gone hraw hn hg) (hrel l)⟩
  rw [hl, hφ, List.map_map]

theorem recRel_of_mem {ctx : Ctx} {dir : Dir} {laws : Laws} {F : Nat} {r₀ r : RecR}
    (h : r ∈ regroupLevels ctx dir laws F [r₀]) : RecRel ctx laws r₀ r :=
  regroupLevels_induction ctx dir laws (P := RecRel ctx laws r₀)
    (fun _ _ h h' => recRel_step h h') F [r₀]
    (fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact recRel_refl ctx laws _) r h

/-! ## The takeable set is closed downwards -/

/-- A takeable set closed downwards through `f`-members. -/
def DownClosed (ctx : Ctx) (T : C → Bool) : Prop := ∀ a b, KidOf ctx a b → T a = true → T b = true

theorem DownClosed.desc {ctx : Ctx} {T : C → Bool} (hT : DownClosed ctx T) {a b : C}
    (h : Desc ctx a b) (ha : T a = true) : T b = true := by
  induction h with
  | refl => exact ha
  | tail _ hk ih => exact hT _ _ hk ih

theorem subset_belowStep (ctx : Ctx) (S : List C) : S ⊆ belowStep ctx S := by
  intro c hc
  unfold belowStep
  exact List.mem_dedup.2 (List.mem_append_left _ hc)

theorem subset_belowIter (ctx : Ctx) : ∀ (n : Nat) (S : List C), S ⊆ belowIter ctx n S
  | 0, _ => fun _ h => h
  | n + 1, S => fun c hc => subset_belowIter ctx n _ (subset_belowStep ctx S hc)

theorem kidOf_mem_belowStep {ctx : Ctx} {S : List C} {a b : C} (ha : a ∈ S) (h : KidOf ctx a b) :
    b ∈ belowStep ctx S := by
  obtain ⟨id, m, hm, hb⟩ := h
  unfold belowStep
  refine List.mem_dedup.2 (List.mem_append_right _ (List.mem_flatMap.2 ⟨a, ha, ?_⟩))
  exact List.mem_flatMap.2 ⟨(id, m), Ctx.mem_members.2 hm, hb⟩

theorem takeableR_down (ctx : Ctx) (σ : Binding) (items : List Var) :
    DownClosed ctx (takeableR ctx σ items) := by
  intro a b hk ha
  cases h : items.mapM σ.cls with
  | none => simp [takeableR, h]
  | some bound =>
      simp only [takeableR, h] at ha ⊢
      by_cases hcl : belowStep ctx (belowIter ctx ((classesOf ctx.G).card + 1) bound) ⊆
          belowIter ctx ((classesOf ctx.G).card + 1) bound
      · rw [if_pos hcl] at ha ⊢
        simp only [decide_eq_true_eq] at ha ⊢
        exact hcl (kidOf_mem_belowStep ha hk)
      · rw [if_neg hcl]

theorem takenOf_takeableR {ctx : Ctx} {σ σ' : Binding} (hext : Extends σ σ') {items : List Var}
    (hb : ∀ x ∈ items, ∃ c, σ'.cls x = some c) :
    ∀ c ∈ takenOf σ' items, takeableR ctx σ items c = true := by
  intro c hc
  cases h : items.mapM σ.cls with
  | none => simp [takeableR, h]
  | some bound =>
    rw [← takenOf_extends hext items (bound_of_mapM h), takenOf_of_mapM h] at hc
    have hc' := subset_belowIter ctx ((classesOf ctx.G).card + 1) bound hc
    simp only [takeableR, h]
    split <;> simp [hc']

/-! ## Pruning keeps the accepted matches -/

theorem mem_baseRecsR {ctx : Ctx} {dir : Dir} {laws : Laws} {n : Node} {r : RecR}
    (h : r ∈ baseRecsR ctx dir laws n) :
    ∃ v ls, normalize ctx.κ laws v = .node r.1 ∧ r.2.1 = flagLeaves ctx.κ laws v ls ∧
      r.2.2 = [] := by
  unfold baseRecsR at h
  obtain ⟨r', hr', rfl⟩ := List.mem_map.1 h
  unfold rawRecordsLD at hr'
  obtain ⟨raw, -, he⟩ := List.mem_filterMap.1 hr'
  revert he
  cases hn : normalize ctx.κ laws raw.1 with
  | node w =>
      intro he
      simp only [Option.some.injEq] at he
      subst he
      exact ⟨raw.1, raw.2, hn, rfl, rfl⟩
  | _ => simp

/-- Laws that can drop a class keep every leaf of the walk. -/
theorem mayNonInert_of_canDrop {κ : FlatKind} {laws : Laws} {l : LeafL}
    (h : canDrop κ laws = true) : mayNonInert κ laws l = true := by
  unfold canDrop at h
  unfold mayNonInert mayNonInertLeaf
  cases κ with
  | ac => simp_all; tauto
  | _ => simp_all

/-- A regrouped record that a match taking `taken` inside a downward-closed
`T` accepts derives from a walk record the pruning by `T` keeps. -/
theorem keepRec_of_accept {ctx : Ctx} {laws : Laws} {T : C → Bool} (hT : DownClosed ctx T)
    {taken : List C} (htk : ∀ c ∈ taken, T c = true) {v : List (C × Nat)} {ls : List LeafL}
    {r₀ r : RecR} (h₀ : r₀.2.1 = flagLeaves ctx.κ laws v ls) (hrel : RecRel ctx laws r₀ r)
    (hacc : ∀ l ∈ r.2.1, l.okE ctx.κ taken) : keepRec ctx.κ T laws r₀ = true := by
  obtain ⟨φ, hφ, hrl⟩ := hrel
  unfold keepRec
  rw [List.all_eq_true]
  intro l₀ hl₀
  have hok := hacc (φ l₀) (by rw [hφ]; exact List.mem_map_of_mem hl₀)
  obtain ⟨hX, hf, hc⟩ := hrl l₀
  unfold keepLeaf
  simp only [Bool.or_eq_true, Bool.and_eq_true, List.any_eq_true]
  rcases hok with ⟨hm, hXt⟩ | ⟨c, hcg, hct⟩ | hfl
  · rw [hX] at hXt
    exact Or.inl (Or.inr ⟨hm, htk _ hXt⟩)
  · obtain ⟨c₀, hc₀, hd⟩ := hc c hcg
    exact Or.inl (Or.inl ⟨c₀, hc₀, hT.desc hd (htk c hct)⟩)
  · rw [h₀] at hl₀
    obtain ⟨l, -, rfl⟩ := List.mem_map.1 hl₀
    rcases hf with hf | hd
    · rw [hf] at hfl
      exact Or.inr (nonInertB_imp_mayNonInert hfl)
    · exact Or.inr (mayNonInert_of_canDrop hd)

/-- **Pruning is match-preserving with regrouped views**: for `taken` inside a
downward-closed `T`, a view accepts `taken` through the pruned and
regrouped enumeration iff it does through the unpruned one. -/
theorem prune_regroup {T : C → Bool} {ctx : Ctx} {dir : Dir} {laws : Laws} {limit : Nat}
    {n : Node} (hT : DownClosed ctx T) {w : List (C × Nat)} {taken : List C}
    (htk : ∀ c ∈ taken, T c = true) :
    (∃ d, (w, d) ∈ enumerateRD T ctx dir laws limit n ∧ d.acceptsE ctx.κ taken) ↔
      (∃ d, (w, d) ∈ enumerateR ctx dir laws limit n ∧ d.acceptsE ctx.κ taken) := by
  unfold enumerateRD enumerateR regroupAll
  rw [acceptsE_enumerateFromR, acceptsE_enumerateFromR]
  constructor
  · rintro ⟨r, hr, hw, hall⟩
    obtain ⟨hr, hlim⟩ := mem_withinLimit.1 hr
    exact ⟨r, mem_withinLimit.2 ⟨regroupLevels_mono ctx dir laws
      (fun r h => (List.mem_filter.1 h).1) hr, hlim⟩, hw, hall⟩
  · rintro ⟨r, hr, hw, hall⟩
    obtain ⟨hr, hlim⟩ := mem_withinLimit.1 hr
    obtain ⟨r₀, h₀, hr₀⟩ := (mem_regroupLevels_iff ctx dir laws _ _ r).1 hr
    obtain ⟨v, ls, -, hfl, -⟩ := mem_baseRecsR h₀
    have hkeep := keepRec_of_accept hT htk hfl (recRel_of_mem hr₀)
      (fun l hl => hall l (List.mem_append_left _ hl))
    exact ⟨r, mem_withinLimit.2 ⟨(mem_regroupLevels_iff ctx dir laws _ _ r).2
      ⟨r₀, List.mem_filter.2 ⟨h₀, hkeep⟩, hr₀⟩, hlim⟩, hw, hall⟩

/-! ## The specification -/

theorem normal_of_mem_regroupLevels {ctx : Ctx} {dir : Dir} {laws : Laws} {F : Nat}
    {recs : List RecR} (h0 : ∀ r ∈ recs, ∃ v, normalize ctx.κ laws v = .node r.1) :
    ∀ r ∈ regroupLevels ctx dir laws F recs, ∃ v, normalize ctx.κ laws v = .node r.1 :=
  regroupLevels_induction ctx dir laws
    (fun _ _ _ h' => by
      obtain ⟨_, _, raw, -, -, hn, -⟩ := mem_regroupRec h'
      exact ⟨raw, hn⟩) F recs h0

theorem normal_enumerateFromR {ctx : Ctx} {dir : Dir} {laws : Laws} {limit F : Nat}
    {recs : List RecR} (h0 : ∀ r ∈ recs, ∃ v, normalize ctx.κ laws v = .node r.1)
    {w : List (C × Nat)} {d : DemandL}
    (h : (w, d) ∈ enumerateFromR (withinLimit limit (regroupAll ctx dir laws F recs))) :
    ∃ v, normalize ctx.κ laws v = .node w := by
  obtain ⟨r, hr, rfl⟩ := mem_enumerateFromR h
  exact normal_of_mem_regroupLevels h0 r (mem_withinLimit.1 hr).1

theorem normal_baseRecsR {ctx : Ctx} {dir : Dir} {laws : Laws} {n : Node} :
    ∀ r ∈ baseRecsR ctx dir laws n, ∃ v, normalize ctx.κ laws v = .node r.1 := by
  intro r hr
  obtain ⟨v, -, hn, -⟩ := mem_baseRecsR hr
  exact ⟨v, hn⟩

/-- **The enumeration with regrouped views meets the plan specification**,
every fold direction, any laws. -/
theorem regroup_spec (dir : Sym → Dir) : (Enumerator.regroup dir).Spec where
  normal h := normal_enumerateFromR normal_baseRecsR h
  normalP h := normal_enumerateFromR
    (fun r hr => normal_baseRecsR r (List.mem_filter.1 hr).1) h
  to_full hext hb h hacc :=
    (prune_regroup (takeableR_down _ _ _) (takenOf_takeableR hext hb)).1 ⟨_, h, hacc⟩
  to_pruned hext hb h hacc :=
    (prune_regroup (takeableR_down _ _ _) (takenOf_takeableR hext hb)).2 ⟨_, h, hacc⟩

/-! ## The plan theorems with regrouped views -/

/-- **Soundness of the flattened plan with regrouped views.** For any order
of the query's atoms and any fold directions, every binding `runER` emits
from the empty environment satisfies every atom under
`AtomSatG (Enumerator.regroup dir)` and binds exactly the atoms' class
variables. -/
theorem regroup_plan_sound {c : FCtx} {dir : Sym → Dir} {sig : Sym → Kind} {as : List RAtom}
    (r : Nat) (hw : QueryFWF c sig as) {env' : EEnv}
    (h : env' ∈ runER c dir (planF as ∅ r) EEnv.empty) :
    (∀ a ∈ as, AtomSatG (Enumerator.regroup dir) c env'.σ a) ∧
      ClsDom env'.σ (planBound as ∅) :=
  flatten_plan_sound_of_spec (regroup_spec dir) r hw h

/-- **Completeness of the flattened plan with regrouped views.** For any
order of the query's atoms and any fold directions, every binding that
satisfies every atom under `AtomSatG (Enumerator.regroup dir)` (each n-ary
atom matched on a view or regrouped view of a node of its class, accepted
by that view's demand) is emitted by `runER`, up to extension. -/
theorem regroup_plan_complete {c : FCtx} {dir : Sym → Dir} {sig : Sym → Kind}
    {as : List RAtom} (r : Nat) (hw : QueryFWF c sig as) {σ' : Binding}
    (hsat : ∀ a ∈ as, AtomSatG (Enumerator.regroup dir) c σ' a) :
    ∃ env' ∈ runER c dir (planF as ∅ r) EEnv.empty, Extends env'.σ σ' :=
  flatten_plan_complete_of_spec (regroup_spec dir) r hw hsat

end Semper.EMatch.Flatten
