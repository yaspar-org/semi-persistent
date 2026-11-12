import SemperProofs.EMatch.Flatten.RegroupOverlapDefs
import SemperProofs.EMatch.Flatten.RegroupLaws
import SemperProofs.EMatch.Flatten.RegroupBounds

/-!
# `:flatten`: overlap views under idempotence

`RegroupOverlapDefs.lean` adds to the regrouping model the engine's overlap
stage for `:assoc-comm-idem` operators: after the regrouping loop, each view
also yields the views that add the class `g` of an `f`-member over a subset
of its classes and drop some of those members, as many as the pattern's
item count fixes. This file proves the stage sound and characterizes it.

## Soundness

An overlap view denotes the view it comes from in every join semilattice
where the members denote their classes (`overlap_step_sound_aci`,
`overlap_step_sound_aci_laws` under an identity): `g` denotes the join of
the group, which covers the members dropped, and the members kept are
absorbed. Every view of both enumerations with the stage denotes the node
(`regroupO_views_sound_aci_laws`, `regroupSkipO_views_sound_aci_laws`); for
an operator without idempotence the stage is empty and the enumerations are
the ones without it (`enumerateRO_eq_of_not_aci`,
`enumerateRSkipO_eq_of_not_aci`).

## The engine's stage

The stage adds records to the loop's final state and regroups nothing; its
source records are the loop's. `overlapAll_spec` shows that every record it
adds is one overlap step from a reachable record (`ReachO`) and that every
overlap step from a reachable record is covered (`Cov`) by a record of the
result: the skips of the stage (a target with an unconditional record, the
source's first unconditional record alone, the signature deduplication) drop
only covered records, as the loop's do. `regroupSkipO_iff` and
`enumerateRSkipO_iff` conclude that the engine's enumeration with the stage
accepts the same matches as `regroupAllO`, the full enumeration followed by
the stage; `regroupAllSkipOAt_eq` that the stage reading each view's
candidates from the use lists ends with the same records.

## Characterization

`OverlapStepL` is one overlap step declaratively: an `f`-member of class `g`,
a raw overlap fit of its group (`overlapFits`, whose members
`mem_overlapFits` and `overlapDrops_spec` spell out), normalized under the
laws, with the derived leaves and needs. `RegroupChainO` is a chain of
regroupings under the laws followed by at most one overlap step.
`regroupO_views_iff_laws`, `regroupO_match_iff_laws`,
`regroupSkipO_views_iff_laws` and `regroupSkipO_match_iff_laws` are
`regroup_match_iff_laws` and `regroupSkip_match_iff_laws` with
`RegroupChainO` in place of `RegroupChainL`: what the engine finds with the
stage, relative to the classes present. The statements without the stage
are untouched and still hold of the loop alone.

## The counter-model, found

`regroup_idem_overlap_found`: in the graph of `regroup_idem_overlap_sound`
(`RegroupLaws.lean`), the view `{a, c, G}` of `S{a, b, c}` with
`G ∋ S{a, b}` is enumerated with the stage for a pattern of three items,
accepting the item classes `[a, c, G]`; the loop alone never enumerates it
(`regroup_idem_overlap_loop_lost`). The fixture
`flatten_regroup_laws_idem.egg` checks the match in the engine.
-/

namespace Semper.EMatch.Flatten

open Semper.EMatch

/-! ## The overlap family -/

theorem mem_dropSets {l D : List C} {k : Nat} :
    D ∈ dropSets l k ↔ D.Sublist l ∧ D.length = k := by
  simp [dropSets, List.mem_filter, List.mem_sublists]

theorem groupClasses_nodup (grp : List (C × Nat)) : (groupClasses grp).Nodup :=
  (dedupAci_spec grp).1.imp (fun h => Nat.ne_of_lt h)

theorem mem_groupClasses {grp : List (C × Nat)} {c : C} :
    c ∈ groupClasses grp ↔ c ∈ grp.map Prod.fst := by
  rw [← List.mem_toFinset, groupClasses, toFinset_map_fst_dedupAci, List.mem_toFinset]

theorem overlapDrops_eq_none_of_not_aci {κ : FlatKind} (hκ : κ ≠ .aci) (limit : Nat) (view : View)
    (g : C) (grp : List (C × Nat)) : overlapDrops κ limit view g grp = none := by
  have h : (κ != .aci) = true := bne_iff_ne.2 hκ
  simp [overlapDrops, h]

theorem overlapFits_eq_nil_of_not_aci {κ : FlatKind} (hκ : κ ≠ .aci) (limit : Nat) (view : View)
    (g : C) (grp : List (C × Nat)) : overlapFits κ limit view g grp = [] := by
  simp [overlapFits, overlapDrops_eq_none_of_not_aci hκ]

/-- The classes of a group inside a view number at most the view's entries. -/
theorem groupClasses_length_le {grp : List (C × Nat)} {view : View}
    (h : ∀ c ∈ groupClasses grp, c ∈ view.map Prod.fst) :
    (groupClasses grp).length ≤ view.length := by
  have := ((groupClasses_nodup grp).subperm h).length_le
  rwa [List.length_map] at this

theorem overlapDrops_eq_none_of_limit_zero (κ : FlatKind) (view : View) (g : C)
    (grp : List (C × Nat)) : overlapDrops κ 0 view g grp = none := by
  unfold overlapDrops
  split
  · rfl
  dsimp only
  split
  · rfl
  rename_i hcond
  push_neg at hcond
  have hle := groupClasses_length_le hcond.2.2
  generalize (if g ∈ List.map Prod.fst view then 0 else 1) = extra
  simp only [Nat.not_lt_zero, ↓reduceIte, Nat.sub_zero]
  split
  · rfl
  · rename_i hk
    exfalso
    apply hk
    left
    omega

theorem overlapFits_eq_nil_of_limit_zero (κ : FlatKind) (view : View) (g : C)
    (grp : List (C × Nat)) : overlapFits κ 0 view g grp = [] := by
  simp [overlapFits, overlapDrops_eq_none_of_limit_zero]

/-- What a drop count says: a set operator, `g` not a member, at least two
members, all in the view, at least one kept, and a pattern with items. -/
theorem overlapDrops_spec {κ : FlatKind} {limit : Nat} {view : View} {g : C}
    {grp : List (C × Nat)} {k : Nat} (h : overlapDrops κ limit view g grp = some k) :
    κ = .aci ∧ g ∉ groupClasses grp ∧ 2 ≤ (groupClasses grp).length ∧
      (∀ c ∈ groupClasses grp, c ∈ view.map Prod.fst) ∧ k < (groupClasses grp).length ∧
      0 < limit := by
  unfold overlapDrops at h
  split at h
  · simp at h
  rename_i hκ
  dsimp only at h
  split at h
  · simp at h
  rename_i hcond
  push_neg at hcond
  have hle := groupClasses_length_le hcond.2.2
  generalize (if g ∈ List.map Prod.fst view then 0 else 1) = extra at h
  split at h
  · simp at h
  rename_i hbase
  split at h
  · simp at h
  rename_i hk
  simp only [Option.some.injEq] at h
  subst h
  push_neg at hk
  have hκ' : κ = .aci := by
    simpa [bne_iff_ne] using hκ
  refine ⟨hκ', hcond.1, hcond.2.1, hcond.2.2, hk.1, ?_⟩
  omega

theorem mem_overlapFits {κ : FlatKind} {limit : Nat} {view : View} {g : C} {grp : List (C × Nat)}
    {raw : View} :
    raw ∈ overlapFits κ limit view g grp ↔
      ∃ (k : Nat) (D : List C), overlapDrops κ limit view g grp = some k ∧
        D.Sublist (groupClasses grp) ∧ D.length = k ∧
        raw = view.filter (fun e => decide (e.1 ∉ D)) ++ [(g, 1)] := by
  unfold overlapFits
  cases hd : overlapDrops κ limit view g grp with
  | none => simp
  | some k =>
      simp only [List.mem_map, mem_dropSets, Option.some.injEq]
      constructor
      · rintro ⟨D, ⟨hD, hl⟩, rfl⟩
        exact ⟨k, D, rfl, hD, hl, rfl⟩
      · rintro ⟨k', D, hk, hD, hl, he⟩
        cases hk
        exact ⟨D, ⟨hD, hl⟩, he.symm⟩

theorem g_mem_overlapFits {κ : FlatKind} {limit : Nat} {view : View} {g : C}
    {grp raw : List (C × Nat)} (h : raw ∈ overlapFits κ limit view g grp) : (g, 1) ∈ raw := by
  obtain ⟨-, -, -, -, -, rfl⟩ := mem_overlapFits.1 h
  simp

theorem overlapFits_pos {κ : FlatKind} {limit : Nat} {view : View} {g : C}
    {grp raw : List (C × Nat)} (hv : ∀ e ∈ view, 0 < e.2)
    (h : raw ∈ overlapFits κ limit view g grp) : ∀ e ∈ raw, 0 < e.2 := by
  obtain ⟨-, -, -, -, -, rfl⟩ := mem_overlapFits.1 h
  intro e he
  rcases List.mem_append.1 he with he | he
  · exact hv e (List.mem_filter.1 he).1
  · rw [List.mem_singleton] at he; subst he; exact Nat.one_pos

/-- A group with an overlap fit in `w` holds a class of `w`: it is on the use
list of that class, a candidate the engine examines. -/
theorem isCand_of_overlapFits {κ : FlatKind} {limit : Nat} {w : View} {g : C}
    {grp raw : List (C × Nat)} (h : raw ∈ overlapFits κ limit w g grp) : isCand w (g, grp) = true := by
  obtain ⟨k, -, hk, -, -, -⟩ := mem_overlapFits.1 h
  obtain ⟨-, -, h2, hsub, -, -⟩ := overlapDrops_spec hk
  obtain ⟨c, hc⟩ := List.exists_mem_of_ne_nil (groupClasses grp)
    (fun hnil => by rw [hnil] at h2; simp at h2)
  have hcv := hsub c hc
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 (mem_groupClasses.1 hc)
  unfold isCand
  exact List.any_eq_true.2 ⟨e, he, decide_eq_true hcv⟩

theorem overlapFits_nil_of_not_cand {κ : FlatKind} {limit : Nat} {w : View}
    {gg : C × List (C × Nat)} (h : isCand w gg = false) :
    overlapFits κ limit w gg.1 gg.2 = [] := by
  by_contra hne
  obtain ⟨raw, hraw⟩ := List.exists_mem_of_ne_nil _ hne
  have := isCand_of_overlapFits hraw
  rw [h] at this
  cases this

/-! ## Soundness in join semilattices -/

section ACI

variable {M : Type*} [SemilatticeSup M] [OrderBot M]

/-- **One overlap step keeps the denotation, ACI**: `g` denotes the join of
its group, which covers the members dropped; the members kept are absorbed. -/
theorem overlap_step_sound_aci {ctx : Ctx} {den : C → M} (hc : ConsistentACI ctx den)
    {limit : Nat} {id : NodeId} {m : Node} {g : C} (hm : ctx.IsMember id m g)
    {view raw : List (C × Nat)} (hv : ∀ e ∈ view, 0 < e.2)
    (h : raw ∈ overlapFits .aci limit view g (kids .aci m.children)) :
    denACI den raw = denACI den view := by
  obtain ⟨k, D, hk, hD, -, rfl⟩ := mem_overlapFits.1 h
  obtain ⟨-, -, -, hsub, -, -⟩ := overlapDrops_spec hk
  have hg : den g = (groupClasses (kids .aci m.children)).toFinset.sup den := by
    rw [hc id m g hm]
    unfold denACI groupClasses
    rw [toFinset_ofEntries_of_pos (kids_pos _ _), toFinset_map_fst_dedupAci]
  have hpos : ∀ e ∈ view.filter (fun e => decide (e.1 ∉ D)) ++ [(g, 1)], 0 < e.2 :=
    overlapFits_pos hv h
  unfold denACI
  rw [toFinset_ofEntries_of_pos hpos, toFinset_ofEntries_of_pos hv, List.map_append,
    List.toFinset_append, Finset.sup_union]
  simp only [List.map_cons, List.map_nil, List.toFinset_cons, List.toFinset_nil,
    Finset.insert_empty, Finset.sup_singleton]
  rw [hg]
  apply le_antisymm
  · apply sup_le
    · apply Finset.sup_mono
      intro c hc'
      obtain ⟨e, he, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hc')
      exact List.mem_toFinset.2 (List.mem_map_of_mem (List.mem_filter.1 he).1)
    · apply Finset.sup_le
      intro c hc'
      exact Finset.le_sup (List.mem_toFinset.2 (hsub c (List.mem_toFinset.1 hc')))
  · apply Finset.sup_le
    intro c hc'
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hc')
    by_cases hcD : e.1 ∈ D
    · exact le_sup_of_le_right (Finset.le_sup (List.mem_toFinset.2 (hD.subset hcD)))
    · refine le_sup_of_le_left (Finset.le_sup (List.mem_toFinset.2 (List.mem_map_of_mem ?_)))
      exact List.mem_filter.2 ⟨he, decide_eq_true hcD⟩

/-- **One overlap step under the laws keeps the denotation, ACI.** -/
theorem overlap_step_sound_aci_laws {ctx : Ctx} {den : C → M} (hc : ConsistentACI ctx den)
    {laws : Laws} (hl : LawsModelACI laws den) {limit : Nat} {id : NodeId} {m : Node} {g : C}
    (hm : ctx.IsMember id m g) {view raw w' : List (C × Nat)} (hv : ∀ e ∈ view, 0 < e.2)
    (h : raw ∈ overlapFits .aci limit view g (kids .aci m.children))
    (hn : normalize .aci laws raw = .node w') :
    denACI den w' = denACI den view := by
  rw [denACI_normalize hl (overlapFits_pos hv h) hn, overlap_step_sound_aci hc hm hv h]

end ACI

/-! ## Records of the stage -/

/-- A record reachable from the walk's records, or one overlap step from one. -/
def ReachO (ctx : Ctx) (dir : Dir) (laws : Laws) (limit : Nat) (base : List RecR) (r : RecR) :
    Prop :=
  Reach ctx dir laws base r ∨ ∃ r', Reach ctx dir laws base r' ∧ r ∈ overlapRec ctx laws limit r'

theorem mem_overlapRec {ctx : Ctx} {laws : Laws} {limit : Nat} {r r' : RecR} :
    r' ∈ overlapRec ctx laws limit r ↔
      ∃ g grp raw, (g, grp) ∈ groupsOf ctx ∧ raw ∈ overlapFits ctx.κ limit r.1 g grp ∧
        normalize ctx.κ laws raw = .node r'.1 ∧ r' = deriveRec r'.1 g (grp.map Prod.fst) r := by
  unfold overlapRec
  constructor
  · intro h
    obtain ⟨⟨g, grp⟩, hgg, h⟩ := List.mem_flatMap.1 h
    obtain ⟨raw, hraw, h⟩ := List.mem_filterMap.1 h
    revert h
    cases hn : normalize ctx.κ laws raw with
    | node w =>
        intro h
        cases h
        exact ⟨g, grp, raw, hgg, hraw, hn, rfl⟩
    | _ => simp
  · rintro ⟨g, grp, raw, hgg, hraw, hn, he⟩
    refine List.mem_flatMap.2 ⟨(g, grp), hgg, List.mem_filterMap.2 ⟨raw, hraw, ?_⟩⟩
    rw [hn]
    simp only [Option.some.injEq]
    exact he.symm

theorem overlapRec_of {ctx : Ctx} {laws : Laws} {limit : Nat} {r : RecR} {g : C}
    {grp raw w : List (C × Nat)} (hgg : (g, grp) ∈ groupsOf ctx)
    (hraw : raw ∈ overlapFits ctx.κ limit r.1 g grp) (hn : normalize ctx.κ laws raw = .node w) :
    deriveRec w g (grp.map Prod.fst) r ∈ overlapRec ctx laws limit r :=
  mem_overlapRec.2 ⟨g, grp, raw, hgg, hraw, hn, rfl⟩

theorem overlapRec_eq_nil_of_not_aci {ctx : Ctx} (hκ : ctx.κ ≠ .aci) (laws : Laws) (limit : Nat)
    (r : RecR) : overlapRec ctx laws limit r = [] := by
  unfold overlapRec
  simp [overlapFits_eq_nil_of_not_aci hκ]

theorem overlapRec_eq_nil_of_limit_zero (ctx : Ctx) (laws : Laws) (r : RecR) :
    overlapRec ctx laws 0 r = [] := by
  unfold overlapRec
  simp [overlapFits_eq_nil_of_limit_zero]

theorem reachO_of_reach {ctx : Ctx} {dir : Dir} {laws : Laws} {limit : Nat} {base : List RecR}
    {r : RecR} (h : Reach ctx dir laws base r) : ReachO ctx dir laws limit base r :=
  Or.inl h

theorem reach_of_reachO_not_aci {ctx : Ctx} (hκ : ctx.κ ≠ .aci) {dir : Dir} {laws : Laws}
    {limit : Nat} {base : List RecR} {r : RecR} (h : ReachO ctx dir laws limit base r) :
    Reach ctx dir laws base r := by
  rcases h with h | ⟨r', -, h⟩
  · exact h
  · rw [overlapRec_eq_nil_of_not_aci hκ] at h; simp at h

theorem reach_of_reachO_zero {ctx : Ctx} {dir : Dir} {laws : Laws} {base : List RecR} {r : RecR}
    (h : ReachO ctx dir laws 0 base r) : Reach ctx dir laws base r := by
  rcases h with h | ⟨r', -, h⟩
  · exact h
  · rw [overlapRec_eq_nil_of_limit_zero] at h; simp at h

/-- A record of the stage has a good view and needs no class twice. -/
theorem reachO_good {ctx : Ctx} {dir : Dir} {laws : Laws} {limit : Nat} {base : List RecR}
    (hb : BaseGood ctx.κ base) {r : RecR} (h : ReachO ctx dir laws limit base r) :
    ViewGood ctx.κ r.1 ∧ r.2.2.Nodup := by
  rcases h with h | ⟨r', hr', h⟩
  · exact reach_good hb h
  · obtain ⟨g, grp, raw, -, hraw, hn, he⟩ := mem_overlapRec.1 h
    obtain ⟨hv, hnd⟩ := reach_good hb hr'
    refine ⟨viewGood_normalize hn (fun _ => overlapFits_pos hv.1 hraw), ?_⟩
    rw [he]
    exact needsAfter_nodup _ _ _ hnd

theorem reachO_normal {ctx : Ctx} {dir : Dir} {laws : Laws} {limit : Nat} {base : List RecR}
    (h0 : ∀ r ∈ base, ∃ v, normalize ctx.κ laws v = .node r.1) {r : RecR}
    (h : ReachO ctx dir laws limit base r) : ∃ v, normalize ctx.κ laws v = .node r.1 := by
  rcases h with h | ⟨r', -, h⟩
  · exact reach_normal h0 h
  · obtain ⟨-, -, raw, -, -, hn, -⟩ := mem_overlapRec.1 h
    exact ⟨raw, hn⟩

/-- The full enumeration with the stage is exactly the records of `ReachO`. -/
theorem mem_regroupAllO_iff_reachO {ctx : Ctx} {dir : Dir} {laws : Laws} {base : List RecR}
    (hb : BaseGood ctx.κ base) {F : Nat} (hF : ∀ r ∈ base, viewSize r.1 ≤ F) {limit : Nat}
    {r : RecR} :
    r ∈ regroupAllO ctx dir laws limit F base ↔ ReachO ctx dir laws limit base r := by
  unfold regroupAllO overlapStage regroupAll ReachO
  rw [List.mem_append, mem_dedupH, List.mem_flatMap, mem_regroupLevels_iff_reach hb hF]
  constructor
  · rintro (h | ⟨r', hr', h⟩)
    · exact Or.inl h
    · exact Or.inr ⟨r', (mem_regroupLevels_iff_reach hb hF).1 hr', h⟩
  · rintro (h | ⟨r', hr', h⟩)
    · exact Or.inl h
    · exact Or.inr ⟨r', (mem_regroupLevels_iff_reach hb hF).2 hr', h⟩

theorem reachO_of_mem_enumerateRO {ctx : Ctx} {dir : Dir} {laws : Laws} {limit : Nat} {n : Node}
    {w : List (C × Nat)} {d : DemandL} (h : (w, d) ∈ enumerateRO ctx dir laws limit n) :
    ∃ r, ReachO ctx dir laws limit (baseRecsR ctx dir laws n) r ∧ r.1 = w := by
  unfold enumerateRO at h
  obtain ⟨r, hr, rfl⟩ := mem_enumerateFromR h
  exact ⟨r, (mem_regroupAllO_iff_reachO (baseGood_baseRecsR ctx dir laws n)
    (fun _ h => viewSize_le_regroupFuel h)).1 (mem_withinLimit.1 hr).1, rfl⟩

section ACIViews

variable {M : Type*} [SemilatticeSup M] [OrderBot M]

/-- Every record of the stage denotes the node, under the laws. -/
theorem reachO_den_aci {ctx : Ctx} (hκ : ctx.κ = .aci) {den : C → M} (hc : ConsistentACI ctx den)
    {laws : Laws} (hl : LawsModelACI laws den) {limit : Nat} {n : Node} {r : RecR}
    (h : ReachO ctx .both laws limit (baseRecsR ctx .both laws n) r) :
    denACI den r.1 = denACI den (kids .aci n.children) := by
  rcases h with h | ⟨r', hr', h⟩
  · exact reach_den_aci hκ hc hl h
  · obtain ⟨g, grp, raw, hgg, hraw, hn, -⟩ := mem_overlapRec.1 h
    obtain ⟨id, m, hm, rfl⟩ := mem_groupsOf hgg
    have hv := (reach_good (baseGood_baseRecsR ctx .both laws n) hr').1.1
    rw [hκ] at hraw hn
    rw [overlap_step_sound_aci_laws hc hl hm hv hraw hn]
    exact reach_den_aci hκ hc hl hr'

/-- **The views with regrouping and the overlap stage of an ACI operator
denote the node, under its identity.** -/
theorem regroupO_views_sound_aci_laws {ctx : Ctx} (hκ : ctx.κ = .aci) {den : C → M}
    (hc : ConsistentACI ctx den) {laws : Laws} (hl : LawsModelACI laws den) {limit : Nat}
    {n : Node} {w : List (C × Nat)} {d : DemandL}
    (h : (w, d) ∈ enumerateRO ctx .both laws limit n) :
    denACI den w = denACI den (kids .aci n.children) := by
  obtain ⟨r, hr, rfl⟩ := reachO_of_mem_enumerateRO h
  exact reachO_den_aci hκ hc hl hr

end ACIViews

/-- Without idempotence the stage adds nothing to the full enumeration. -/
theorem regroupAllO_eq_of_not_aci {ctx : Ctx} (hκ : ctx.κ ≠ .aci) (dir : Dir) (laws : Laws)
    (limit fuel : Nat) (recs : List RecR) :
    regroupAllO ctx dir laws limit fuel recs = regroupAll ctx dir laws fuel recs := by
  unfold regroupAllO overlapStage
  have : (regroupAll ctx dir laws fuel recs).flatMap (overlapRec ctx laws limit) = [] := by
    rw [List.flatMap_eq_nil_iff]
    intro r _
    exact overlapRec_eq_nil_of_not_aci hκ laws limit r
  have h2 : dedupH ([] : List RecR) = [] := rfl
  rw [this, h2, List.append_nil]

theorem enumerateRO_eq_of_not_aci {ctx : Ctx} (hκ : ctx.κ ≠ .aci) (dir : Dir) (laws : Laws)
    (limit : Nat) (n : Node) : enumerateRO ctx dir laws limit n = enumerateR ctx dir laws limit n := by
  simp only [enumerateRO, enumerateR, regroupAllO_eq_of_not_aci hκ]

theorem enumerateRDO_eq_of_not_aci {ctx : Ctx} (hκ : ctx.κ ≠ .aci) (T : C → Bool) (dir : Dir)
    (laws : Laws) (limit : Nat) (n : Node) :
    enumerateRDO T ctx dir laws limit n = enumerateRD T ctx dir laws limit n := by
  simp only [enumerateRDO, enumerateRD, regroupAllO_eq_of_not_aci hκ]

/-! ## The engine's stage -/

section Stage

variable {ctx : Ctx} {dir : Dir} {laws : Laws} {limit : Nat} {base : List RecR}

/-- The stage's guard is off: a set operator and a pattern with items. -/
theorem stage_on {κ : FlatKind} (h : (κ != .aci || limit == 0) = false) : κ = .aci ∧ 0 < limit := by
  simp only [Bool.or_eq_false_iff, bne_eq_false_iff_eq, beq_eq_false_iff_ne, ne_eq] at h
  exact ⟨h.1, Nat.pos_of_ne_zero h.2⟩

/-- The stage's guard is on: every overlap family is empty. -/
theorem overlapFits_eq_nil_of_guard {κ : FlatKind} (h : (κ != .aci || limit == 0) = true)
    (view : View) (g : C) (grp : List (C × Nat)) : overlapFits κ limit view g grp = [] := by
  simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at h
  rcases h with h | h
  · exact overlapFits_eq_nil_of_not_aci h limit view g grp
  · subst h; exact overlapFits_eq_nil_of_limit_zero κ view g grp

/-- The invariant of the stage: every record is filed under its view and is a
record of `ReachO`, a view with records is an entry, every signature is a
record's. -/
structure OCore (ctx : Ctx) (dir : Dir) (laws : Laws) (limit : Nat) (base : List RecR)
    (st : SkipSt) : Prop where
  sound : ∀ w, ∀ r ∈ st.recs w, r.1 = w ∧ ReachO ctx dir laws limit base r
  in_order : ∀ w, st.recs w ≠ [] → w ∈ st.order
  sigs_rec : ∀ w, ∀ s ∈ st.sigs w, ∃ r ∈ st.recs w, recSig r = s

theorem OCore.of_core {st : SkipSt} (hc : Core ctx dir laws base st) :
    OCore ctx dir laws limit base st :=
  ⟨fun w r hr => ⟨(hc.sound w r hr).1, Or.inl (hc.sound w r hr).2⟩, hc.in_order, hc.sigs_rec⟩

theorem addRec_ocore {st : SkipSt} {t : View} {d : RecR} (hc : OCore ctx dir laws limit base st)
    (ht : t ∈ st.order) (hd : d.1 = t ∧ ReachO ctx dir laws limit base d) :
    OCore ctx dir laws limit base (st.addRec t d) := by
  rcases addRec_cases t st d with ⟨h, -⟩ | h <;> rw [h]
  · exact hc
  · refine ⟨fun w r hr => ?_, fun w hw => ?_, fun w s hs => ?_⟩
    · by_cases hw : w = t
      · subst hw
        simp only [Function.update_self, List.mem_append, List.mem_singleton] at hr
        rcases hr with hr | rfl
        · exact hc.sound _ r hr
        · exact hd
      · simp only [Function.update_of_ne hw] at hr
        exact hc.sound w r hr
    · by_cases hwt : w = t
      · rw [hwt]; exact ht
      · simp only [Function.update_of_ne hwt] at hw
        exact hc.in_order w hw
    · by_cases hw : w = t
      · subst hw
        simp only [Function.update_self, List.mem_append, List.mem_singleton] at hs ⊢
        rcases hs with hs | rfl
        · obtain ⟨r, hr, he⟩ := hc.sigs_rec _ s hs
          exact ⟨r, Or.inl hr, he⟩
        · exact ⟨d, Or.inr rfl, rfl⟩
      · simp only [Function.update_of_ne hw] at hs ⊢
        exact hc.sigs_rec w s hs

/-- After adding `d`, the target has a record of `d`'s signature. -/
theorem addRec_hasO {st : SkipSt} {t : View} {d : RecR} (hc : OCore ctx dir laws limit base st) :
    ∃ c ∈ (st.addRec t d).recs t, RecSig.same (recSig d) (recSig c) = true := by
  rcases addRec_cases t st d with ⟨h, hs⟩ | h
  · rw [h]
    obtain ⟨s, hs, he⟩ := List.any_eq_true.1 hs
    obtain ⟨c, hc', rfl⟩ := hc.sigs_rec t s hs
    exact ⟨c, hc', he⟩
  · rw [h]
    exact ⟨d, by simp, recSig_same_self d⟩

theorem foldl_addRecO {t : View} (ds : List RecR)
    (hds : ∀ d ∈ ds, d.1 = t ∧ ReachO ctx dir laws limit base d) (st : SkipSt)
    (hc : OCore ctx dir laws limit base st) (ht : t ∈ st.order) :
    let st' := ds.foldl (SkipSt.addRec t) st
    OCore ctx dir laws limit base st' ∧ st'.order = st.order ∧ Mono st st' ∧
      ∀ d ∈ ds, ∃ c ∈ st'.recs t, Cov c d := by
  intro st'
  have hI := foldl_induct (SkipSt.addRec t)
    (fun s => OCore ctx dir laws limit base s ∧ s.order = st.order ∧ Mono st s) ds st
    ⟨hc, rfl, Mono.refl _⟩
    (fun s d hd ⟨hcs, ho, hm⟩ => by
      obtain ⟨fo, -, -, fm⟩ := addRec_frame t s d
      exact ⟨addRec_ocore hcs (ho ▸ ht) (hds d hd), fo.trans ho, hm.trans fm⟩)
  obtain ⟨hcore, ho, hm⟩ := hI
  refine ⟨hcore, ho, hm, fun d hd => ?_⟩
  have := foldl_establish (f := SkipSt.addRec t)
    (I := fun s => OCore ctx dir laws limit base s ∧ s.order = st.order)
    (P := fun s => ∃ c ∈ s.recs t, RecSig.same (recSig d) (recSig c) = true) hd
    (fun s x hx ⟨hcs, ho⟩ => ⟨addRec_ocore hcs (ho ▸ ht) (hds x hx),
      (addRec_frame t s x).1.trans ho⟩)
    (fun s x _ _ ⟨c, hc', he⟩ => ⟨c, (addRec_frame t s x).2.2.2.1 t c hc', he⟩)
    (fun s ⟨hcs, _⟩ => addRec_hasO hcs) st ⟨hc, rfl⟩
  obtain ⟨c, hc', he⟩ := this
  refine ⟨c, hc', cov_of_same he ?_⟩
  rw [(hcore.sound t c hc').1, (hds d hd).1]

/-- **One target of the stage.** The derived records `ds` are each covered by
a record of the target afterwards: its unconditional record, a record of the
same signature, or the record itself. -/
theorem addTargetO_spec {st : SkipSt} (hc : OCore ctx dir laws limit base st) {t : View}
    {ds : List RecR} (hds : ∀ d ∈ ds, d.1 = t ∧ ReachO ctx dir laws limit base d) :
    OCore ctx dir laws limit base (st.addTargetO t ds) ∧ Mono st (st.addTargetO t ds) ∧
      ∀ d ∈ ds, ∃ c ∈ (st.addTargetO t ds).recs t, Cov c d := by
  unfold SkipSt.addTargetO
  dsimp only
  set st₁ : SkipSt := if t ∈ st.order then st else { st with order := st.order ++ [t] }
    with hst₁
  have h₁recs : st₁.recs = st.recs := by rw [hst₁]; split <;> rfl
  have h₁sigs : st₁.sigs = st.sigs := by rw [hst₁]; split <;> rfl
  have h₁order : ∀ v, v ∈ st₁.order ↔ v ∈ st.order ∨ v = t := by
    intro v
    rw [hst₁]
    split
    · rename_i h
      constructor
      · exact Or.inl
      · rintro (h' | rfl)
        · exact h'
        · exact h
    · simp
  have ht₁ : t ∈ st₁.order := (h₁order t).2 (Or.inr rfl)
  have hc₁ : OCore ctx dir laws limit base st₁ := by
    obtain ⟨hs, hio, hsr⟩ := hc
    refine ⟨?_, ?_, ?_⟩
    · rw [h₁recs]; exact hs
    · intro v hv; rw [h₁recs] at hv; exact (h₁order v).2 (Or.inl (hio v hv))
    · rw [h₁sigs, h₁recs]; exact hsr
  have hm₁ : Mono st st₁ :=
    ⟨fun v r h => by rw [h₁recs]; exact h, fun v h => (h₁order v).2 (Or.inl h)⟩
  split
  · rename_i hu
    obtain ⟨u, hu, huu⟩ := List.any_eq_true.1 hu
    refine ⟨hc₁, hm₁, fun d hd => ⟨u, hu, cov_uncond huu ?_⟩⟩
    rw [(hc₁.sound t u hu).1, (hds d hd).1]
  · obtain ⟨hc', -, hm', hcov⟩ := foldl_addRecO ds hds st₁ hc₁ ht₁
    exact ⟨hc', hm₁.trans hm', hcov⟩

/-- The records of a source view: filed under it, reachable. -/
def SrcOK (ctx : Ctx) (dir : Dir) (laws : Laws) (base : List RecR) (w : View)
    (srcs : List RecR) : Prop :=
  ∀ r ∈ srcs, r.1 = w ∧ Reach ctx dir laws base r

/-- **One overlap fit.** Every derived record of every source record is
covered by a record of the target afterwards. -/
theorem overlapFitStep_spec {w : View} {srcs : List RecR} (hsrc : SrcOK ctx dir laws base w srcs)
    {gg : C × List (C × Nat)} (hgg : gg ∈ groupsOf ctx) {raw : List (C × Nat)}
    (hraw : raw ∈ overlapFits ctx.κ limit w gg.1 gg.2) {st : SkipSt}
    (hc : OCore ctx dir laws limit base st) :
    OCore ctx dir laws limit base (SkipSt.overlapFitStep ctx laws srcs gg st raw) ∧
      Mono st (SkipSt.overlapFitStep ctx laws srcs gg st raw) ∧
      ∀ t, normalize ctx.κ laws raw = .node t → ∀ a ∈ srcs,
        ∃ c ∈ (SkipSt.overlapFitStep ctx laws srcs gg st raw).recs t,
          Cov c (deriveRec t gg.1 (gg.2.map Prod.fst) a) := by
  unfold SkipSt.overlapFitStep
  split
  · rename_i t hn
    have hsw : ∀ r ∈ srcs, r.1 = w := fun r hr => (hsrc r hr).1
    obtain ⟨hsub, -, hscov⟩ := srcRecs_spec hsw
    have hds : ∀ d ∈ (srcRecs srcs).map (deriveRec t gg.1 (gg.2.map Prod.fst)),
        d.1 = t ∧ ReachO ctx dir laws limit base d := by
      intro d hd
      obtain ⟨a', ha', rfl⟩ := List.mem_map.1 hd
      refine ⟨rfl, Or.inr ⟨a', (hsrc a' (hsub a' ha')).2, ?_⟩⟩
      exact overlapRec_of (g := gg.1) (grp := gg.2) hgg (by rw [hsw a' (hsub a' ha')]; exact hraw) hn
    obtain ⟨hc', hm, hcov⟩ := addTargetO_spec hc hds
    refine ⟨hc', hm, fun t' ht' a ha => ?_⟩
    rw [hn] at ht'
    cases ht'
    obtain ⟨a', ha', hca⟩ := hscov a ha
    obtain ⟨c, hc'', hcd⟩ := hcov _ (List.mem_map_of_mem ha')
    exact ⟨c, hc'', hcd.trans (hca.derive _ _ _)⟩
  · rename_i hn
    refine ⟨hc, Mono.refl _, fun t ht => absurd ht ?_⟩
    intro h; exact hn t h

/-- The overlap steps of the view `w` by the groups `gs` from the records
`srcs` are covered in `st`. -/
def ClosedO (ctx : Ctx) (laws : Laws) (limit : Nat) (gs : List (C × List (C × Nat))) (w : View)
    (srcs : List RecR) (st : SkipSt) : Prop :=
  ∀ gg ∈ gs, ∀ raw ∈ overlapFits ctx.κ limit w gg.1 gg.2, ∀ t,
    normalize ctx.κ laws raw = .node t → ∀ a ∈ srcs,
      ∃ c ∈ st.recs t, Cov c (deriveRec t gg.1 (gg.2.map Prod.fst) a)

theorem ClosedO.mono {gs : List (C × List (C × Nat))} {w : View} {srcs : List RecR} {st st' : SkipSt}
    (h : ClosedO ctx laws limit gs w srcs st) (hm : Mono st st') :
    ClosedO ctx laws limit gs w srcs st' := by
  intro gg hgg raw hraw t ht a ha
  obtain ⟨c, hc, hcov⟩ := h gg hgg raw hraw t ht a ha
  exact ⟨c, hm.1 _ c hc, hcov⟩

/-- **One candidate group**: afterwards every overlap step by it is covered. -/
theorem overlapGroupStep_spec {w : View} {srcs : List RecR} (hsrc : SrcOK ctx dir laws base w srcs)
    {gg : C × List (C × Nat)} (hgg : gg ∈ groupsOf ctx) {st : SkipSt}
    (hc : OCore ctx dir laws limit base st) :
    OCore ctx dir laws limit base (SkipSt.overlapGroupStep ctx laws limit w srcs st gg) ∧
      Mono st (SkipSt.overlapGroupStep ctx laws limit w srcs st gg) ∧
      ClosedO ctx laws limit [gg] w srcs (SkipSt.overlapGroupStep ctx laws limit w srcs st gg) := by
  unfold SkipSt.overlapGroupStep
  let I : SkipSt → Prop := fun s => OCore ctx dir laws limit base s ∧ Mono st s
  have hI : ∀ s raw, raw ∈ overlapFits ctx.κ limit w gg.1 gg.2 → I s →
      I (SkipSt.overlapFitStep ctx laws srcs gg s raw) := by
    intro s raw hraw ⟨hcs, hm⟩
    obtain ⟨h1, h2, -⟩ := overlapFitStep_spec hsrc hgg hraw hcs
    exact ⟨h1, hm.trans h2⟩
  have hall := foldl_induct _ I _ st ⟨hc, Mono.refl _⟩ hI
  refine ⟨hall.1, hall.2, ?_⟩
  intro gg' hgg' raw hraw t ht a ha
  rw [List.mem_singleton] at hgg'
  subst hgg'
  let P : SkipSt → Prop := fun s => ∃ c ∈ s.recs t, Cov c (deriveRec t gg'.1 (gg'.2.map Prod.fst) a)
  refine foldl_establish (I := I) (P := P) hraw hI ?_ ?_ st ⟨hc, Mono.refl _⟩
  · intro s raw' hraw' hIs ⟨c, hc', hcov⟩
    obtain ⟨-, h2, -⟩ := overlapFitStep_spec hsrc hgg hraw' hIs.1
    exact ⟨c, h2.1 _ c hc', hcov⟩
  · intro s hIs
    obtain ⟨-, -, h3⟩ := overlapFitStep_spec hsrc hgg hraw hIs.1
    exact h3 t ht a ha

/-- **One source view**: afterwards every overlap step of it is covered. -/
theorem overlapView_spec {gs : List (C × List (C × Nat))} (hgs : ∀ gg ∈ gs, gg ∈ groupsOf ctx)
    {w : View} {srcs : List RecR} (hsrc : SrcOK ctx dir laws base w srcs) {st : SkipSt}
    (hc : OCore ctx dir laws limit base st) :
    OCore ctx dir laws limit base (SkipSt.overlapView ctx laws limit gs w srcs st) ∧
      Mono st (SkipSt.overlapView ctx laws limit gs w srcs st) ∧
      ClosedO ctx laws limit gs w srcs (SkipSt.overlapView ctx laws limit gs w srcs st) := by
  unfold SkipSt.overlapView
  let I : SkipSt → Prop := fun s => OCore ctx dir laws limit base s ∧ Mono st s
  have hI : ∀ s gg, gg ∈ gs → I s → I (SkipSt.overlapGroupStep ctx laws limit w srcs s gg) := by
    intro s gg hgg ⟨hcs, hm⟩
    obtain ⟨h1, h2, -⟩ := overlapGroupStep_spec hsrc (hgs gg hgg) hcs
    exact ⟨h1, hm.trans h2⟩
  have hall := foldl_induct _ I gs st ⟨hc, Mono.refl _⟩ hI
  refine ⟨hall.1, hall.2, ?_⟩
  intro gg hgg raw hraw t ht a ha
  let P : SkipSt → Prop := fun s => ∃ c ∈ s.recs t, Cov c (deriveRec t gg.1 (gg.2.map Prod.fst) a)
  refine foldl_establish (I := I) (P := P) hgg hI ?_ ?_ st ⟨hc, Mono.refl _⟩
  · intro s gg' hgg' hIs ⟨c, hc', hcov⟩
    obtain ⟨-, h2, -⟩ := overlapGroupStep_spec hsrc (hgs gg' hgg') hIs.1
    exact ⟨c, h2.1 _ c hc', hcov⟩
  · intro s hIs
    obtain ⟨-, -, h3⟩ := overlapGroupStep_spec hsrc (hgs gg hgg) hIs.1
    exact h3 gg (List.mem_singleton_self _) raw hraw t ht a ha

/-- **The stage**: its records are the loop's and overlap records of them,
the loop's records are kept, and every overlap step of every view of the
loop by a candidate group is covered. -/
theorem overlapAll_spec {gs : List (C × List (C × Nat))} (hgs : ∀ gg ∈ gs, gg ∈ groupsOf ctx)
    {st₀ : SkipSt} (hc0 : Core ctx dir laws base st₀) :
    OCore ctx dir laws limit base (SkipSt.overlapAll ctx laws limit gs st₀) ∧
      Mono st₀ (SkipSt.overlapAll ctx laws limit gs st₀) ∧
      ∀ w ∈ st₀.order, ClosedO ctx laws limit gs w (st₀.recs w)
        (SkipSt.overlapAll ctx laws limit gs st₀) := by
  unfold SkipSt.overlapAll
  split
  · rename_i hg
    refine ⟨OCore.of_core hc0, Mono.refl _, fun w _ gg _ raw hraw => ?_⟩
    rw [overlapFits_eq_nil_of_guard hg] at hraw
    simp at hraw
  · let I : SkipSt → Prop := fun s => OCore ctx dir laws limit base s ∧ Mono st₀ s
    have hsrc : ∀ w, SrcOK ctx dir laws base w (st₀.recs w) :=
      fun w r hr => hc0.sound w r hr
    have hI : ∀ s w, w ∈ st₀.order → I s →
        I (SkipSt.overlapView ctx laws limit gs w (st₀.recs w) s) := by
      intro s w _ ⟨hcs, hm⟩
      obtain ⟨h1, h2, -⟩ := overlapView_spec hgs (hsrc w) hcs
      exact ⟨h1, hm.trans h2⟩
    have hall := foldl_induct _ I st₀.order st₀ ⟨OCore.of_core hc0, Mono.refl _⟩ hI
    refine ⟨hall.1, hall.2, fun w hw => ?_⟩
    refine foldl_establish (I := I) (P := ClosedO ctx laws limit gs w (st₀.recs w)) hw hI ?_ ?_
      st₀ ⟨OCore.of_core hc0, Mono.refl _⟩
    · intro s w' hw' hIs hP
      obtain ⟨-, h2, -⟩ := overlapView_spec hgs (hsrc w') hIs.1
      exact hP.mono h2
    · intro s hIs
      exact (overlapView_spec hgs (hsrc w) hIs.1).2.2

/-- `gs` holds every filed `f`-member with an overlap fit in some view. -/
def CandSupO (ctx : Ctx) (limit : Nat) (gs : List (C × List (C × Nat))) : Prop :=
  ∀ gg ∈ groupsOf ctx, ∀ (w : View) (raw : List (C × Nat)),
    raw ∈ overlapFits ctx.κ limit w gg.1 gg.2 → gg ∈ gs

theorem candSupO_of_sup {gs : List (C × List (C × Nat))} (h : ∀ gg ∈ groupsOf ctx, gg ∈ gs) :
    CandSupO ctx limit gs :=
  fun gg hgg _ _ _ => h gg hgg

theorem mem_records_iff {st : SkipSt} {r : RecR} :
    r ∈ st.records ↔ ∃ v ∈ st.order, r ∈ st.recs v := by
  simp [SkipSt.records]

/-- **The engine's regrouping with the stage**: its records are reachable or
one overlap step from a reachable record, and every such record is covered
by one of them. -/
theorem regroupSkipO_spec (hb : BaseGood ctx.κ base) {gs : List (C × List (C × Nat))}
    (hgs : ∀ gg ∈ gs, gg ∈ groupsOf ctx) (hgs' : CandSup ctx dir gs) (hgsO : CandSupO ctx limit gs) :
    (∀ r ∈ regroupSkipO ctx dir laws limit gs base, ReachO ctx dir laws limit base r) ∧
      ∀ b, ReachO ctx dir laws limit base b →
        ∃ c ∈ regroupSkipO ctx dir laws limit gs base, Cov c b := by
  obtain ⟨hi, -⟩ := run_finished hb hgs hgs' (skipFuel ctx dir laws base)
    (SkipSt.init base) (init_inv (ctx := ctx) (dir := dir) (laws := laws) base)
    (by unfold skipFuel; omega)
  set st₀ := SkipSt.run ctx dir laws gs (skipFuel ctx dir laws base) (SkipSt.init base) with hst₀
  obtain ⟨ho, hm, hcl⟩ := overlapAll_spec (limit := limit) hgs hi.core
  set st := SkipSt.overlapAll ctx laws limit gs st₀
  have hloop := regroupSkipG_spec (dir := dir) (laws := laws) hb hgs hgs'
  have hrec0 : ∀ r, r ∈ regroupSkipG ctx dir laws gs base ↔ r ∈ st₀.records := fun _ => Iff.rfl
  refine ⟨fun r hr => ?_, fun b hb' => ?_⟩
  · obtain ⟨v, -, hr⟩ := mem_records_iff.1 hr
    exact (ho.sound v r hr).2
  · suffices h : ∃ c ∈ st.recs b.1, Cov c b by
      obtain ⟨c, hc, hcov⟩ := h
      exact ⟨c, mem_records_iff.2 ⟨b.1, ho.in_order _ (List.ne_nil_of_mem hc), hc⟩, hcov⟩
    rcases hb' with hb' | ⟨a, ha, hab⟩
    · obtain ⟨c, hc, hcov⟩ := hloop.2 b hb'
      obtain ⟨v, -, hc⟩ := mem_records_iff.1 ((hrec0 c).1 hc)
      have hcv : c.1 = v := (hi.core.sound v c hc).1
      have hbv : b.1 = v := hcov.1.symm.trans hcv
      rw [hbv]
      exact ⟨c, hm.1 _ c hc, hcov⟩
    · obtain ⟨g, grp, raw, hgg, hraw, hn, hbe⟩ := mem_overlapRec.1 hab
      obtain ⟨c₀, hc₀, hcov₀⟩ := hloop.2 a ha
      obtain ⟨v, hv, hc₀⟩ := mem_records_iff.1 ((hrec0 c₀).1 hc₀)
      have hcv : c₀.1 = v := (hi.core.sound v c₀ hc₀).1
      have hav : a.1 = v := hcov₀.1.symm.trans hcv
      rw [hav] at hraw
      obtain ⟨c, hc, hcov⟩ := hcl v hv (g, grp) (hgsO (g, grp) hgg v raw hraw) raw hraw b.1 hn
        c₀ hc₀
      refine ⟨c, hc, hcov.trans ?_⟩
      rw [hbe]
      exact hcov₀.derive _ _ _

/-- **The engine's regrouping with the stage accepts the same matches as the
full enumeration with it**, for any laws, kind, fold direction and candidate
order. -/
theorem regroupSkipO_iff (hb : BaseGood ctx.κ base) {gs : List (C × List (C × Nat))}
    (hgs : ∀ gg ∈ gs, gg ∈ groupsOf ctx) (hgs' : CandSup ctx dir gs) (hgsO : CandSupO ctx limit gs)
    {F : Nat} (hF : ∀ r ∈ base, viewSize r.1 ≤ F) {w : List (C × Nat)} {taken : List C} :
    (∃ r ∈ withinLimit limit (regroupSkipO ctx dir laws limit gs base), r.1 = w ∧
        ∀ l ∈ r.alt, l.okE ctx.κ taken) ↔
      ∃ r ∈ withinLimit limit (regroupAllO ctx dir laws limit F base), r.1 = w ∧
        ∀ l ∈ r.alt, l.okE ctx.κ taken := by
  obtain ⟨hs, hc⟩ := regroupSkipO_spec (dir := dir) (laws := laws) hb hgs hgs' hgsO
  constructor
  · rintro ⟨r, hr, hw, hacc⟩
    obtain ⟨hr, hlim⟩ := mem_withinLimit.1 hr
    exact ⟨r, mem_withinLimit.2 ⟨(mem_regroupAllO_iff_reachO hb hF).2 (hs r hr), hlim⟩, hw, hacc⟩
  · rintro ⟨b, hb', rfl, hacc⟩
    obtain ⟨hb', hlim⟩ := mem_withinLimit.1 hb'
    have hreach := (mem_regroupAllO_iff_reachO hb hF).1 hb'
    obtain ⟨c, hc', hcov⟩ := hc b hreach
    exact ⟨c, mem_withinLimit.2 ⟨hc', le_trans (hcov.length (reachO_good hb (hs c hc')).2) hlim⟩,
      hcov.1, hcov.accepts hacc⟩

end Stage

/-- `enumerateRO` and the engine's enumeration with the stage accept the same matches. -/
theorem enumerateRSkipO_iff {ctx : Ctx} {dir : Dir} {laws : Laws} {limit : Nat} {n : Node}
    {w : List (C × Nat)} {taken : List C} :
    (∃ d, (w, d) ∈ enumerateRSkipO ctx dir laws limit n ∧ d.acceptsE ctx.κ taken) ↔
      ∃ d, (w, d) ∈ enumerateRO ctx dir laws limit n ∧ d.acceptsE ctx.κ taken := by
  unfold enumerateRSkipO enumerateRO regroupAllSkipO
  rw [acceptsE_enumerateFromR, acceptsE_enumerateFromR]
  exact regroupSkipO_iff (baseGood_baseRecsR ctx dir laws n) (groupsOfEngine_sub ctx)
    (candSup_of_sup dir (groupsOfEngine_sup ctx)) (candSupO_of_sup (groupsOfEngine_sup ctx))
    (fun _ h => viewSize_le_regroupFuel h)

/-- `enumerateRDO` and the engine's pruned enumeration with the stage accept
the same matches. -/
theorem enumerateRDSkipO_iff {T : C → Bool} {ctx : Ctx} {dir : Dir} {laws : Laws} {limit : Nat}
    {n : Node} {w : List (C × Nat)} {taken : List C} :
    (∃ d, (w, d) ∈ enumerateRDSkipO T ctx dir laws limit n ∧ d.acceptsE ctx.κ taken) ↔
      ∃ d, (w, d) ∈ enumerateRDO T ctx dir laws limit n ∧ d.acceptsE ctx.κ taken := by
  unfold enumerateRDSkipO enumerateRDO regroupAllSkipO
  rw [acceptsE_enumerateFromR, acceptsE_enumerateFromR]
  exact regroupSkipO_iff (baseGood_filter (baseGood_baseRecsR ctx dir laws n) _)
    (groupsOfEngine_sub ctx) (candSup_of_sup dir (groupsOfEngine_sup ctx))
    (candSupO_of_sup (groupsOfEngine_sup ctx))
    (fun _ h => viewSize_le_regroupFuel (List.mem_filter.1 h).1)

/-- A view of the engine's enumeration with the stage is the view of a record
of `ReachO`. -/
theorem reachO_of_mem_enumerateRSkipO {ctx : Ctx} {dir : Dir} {laws : Laws} {limit : Nat}
    {n : Node} {w : List (C × Nat)} {d : DemandL}
    (h : (w, d) ∈ enumerateRSkipO ctx dir laws limit n) :
    ∃ r, ReachO ctx dir laws limit (baseRecsR ctx dir laws n) r ∧ r.1 = w := by
  unfold enumerateRSkipO at h
  obtain ⟨r, hr, rfl⟩ := mem_enumerateFromR h
  exact ⟨r, (regroupSkipO_spec (baseGood_baseRecsR ctx dir laws n) (groupsOfEngine_sub ctx)
    (candSup_of_sup dir (groupsOfEngine_sup ctx)) (candSupO_of_sup (groupsOfEngine_sup ctx))).1
    r (mem_withinLimit.1 hr).1, rfl⟩

section ACISkip

variable {M : Type*} [SemilatticeSup M] [OrderBot M]

/-- **The engine's views of an ACI operator with the stage denote the node,
under its identity.** -/
theorem regroupSkipO_views_sound_aci_laws {ctx : Ctx} (hκ : ctx.κ = .aci) {den : C → M}
    (hc : ConsistentACI ctx den) {laws : Laws} (hl : LawsModelACI laws den) {limit : Nat}
    {n : Node} {w : List (C × Nat)} {d : DemandL}
    (h : (w, d) ∈ enumerateRSkipO ctx .both laws limit n) :
    denACI den w = denACI den (kids .aci n.children) := by
  obtain ⟨r, hr, rfl⟩ := reachO_of_mem_enumerateRSkipO h
  exact reachO_den_aci hκ hc hl hr

end ACISkip

/-- Without idempotence the stage leaves the engine's state unchanged. -/
theorem overlapAll_eq_of_not_aci {ctx : Ctx} (hκ : ctx.κ ≠ .aci) (laws : Laws) (limit : Nat)
    (gs : List (C × List (C × Nat))) (st : SkipSt) : SkipSt.overlapAll ctx laws limit gs st = st := by
  unfold SkipSt.overlapAll
  have : (ctx.κ != .aci || limit == 0) = true := by simp [bne_iff_ne, hκ]
  rw [this]
  rfl

theorem enumerateRSkipO_eq_of_not_aci {ctx : Ctx} (hκ : ctx.κ ≠ .aci) (dir : Dir) (laws : Laws)
    (limit : Nat) (n : Node) :
    enumerateRSkipO ctx dir laws limit n = enumerateRSkip ctx dir laws limit n := by
  unfold enumerateRSkipO enumerateRSkip regroupAllSkipO regroupSkipO regroupAllSkip regroupSkipG
    regroupSkipN
  rw [overlapAll_eq_of_not_aci hκ]

theorem enumerateRDSkipO_eq_of_not_aci {ctx : Ctx} (hκ : ctx.κ ≠ .aci) (T : C → Bool) (dir : Dir)
    (laws : Laws) (limit : Nat) (n : Node) :
    enumerateRDSkipO T ctx dir laws limit n = enumerateRDSkip T ctx dir laws limit n := by
  unfold enumerateRDSkipO enumerateRDSkip regroupAllSkipO regroupSkipO regroupAllSkip regroupSkipG
    regroupSkipN
  rw [overlapAll_eq_of_not_aci hκ]

/-! ## The candidates of each view -/

theorem overlapGroupStep_not_cand {ctx : Ctx} {laws : Laws} {limit : Nat} {w : View}
    {srcs : List RecR} {st : SkipSt} {gg : C × List (C × Nat)} (h : isCand w gg = false) :
    SkipSt.overlapGroupStep ctx laws limit w srcs st gg = st := by
  unfold SkipSt.overlapGroupStep
  rw [overlapFits_nil_of_not_cand h]
  rfl

/-- The stage over the candidates of a view is the stage over every group:
a group holding no class of the view has no overlap fit. -/
theorem overlapView_filter_cand (ctx : Ctx) (laws : Laws) (limit : Nat)
    (gs : List (C × List (C × Nat))) (w : View) (srcs : List RecR) (st : SkipSt) :
    SkipSt.overlapView ctx laws limit (gs.filter (isCand w)) w srcs st =
      SkipSt.overlapView ctx laws limit gs w srcs st := by
  unfold SkipSt.overlapView
  induction gs generalizing st with
  | nil => rfl
  | cons gg gs ih =>
      rw [List.filter_cons]
      by_cases hc : isCand w gg = true
      · simp only [hc, ↓reduceIte, List.foldl_cons]
        exact ih _
      · have hc' : isCand w gg = false := Bool.of_not_eq_true hc
        simp only [hc', Bool.false_eq_true, ↓reduceIte, List.foldl_cons]
        rw [overlapGroupStep_not_cand hc']
        exact ih _

/-- **The engine's candidates give the model's records, with the stage**:
the loop and the stage reading each view's candidates from the use lists of
its classes end with the records of the loop and the stage over every filed
`f`-member. -/
theorem regroupAllSkipOAt_eq (ctx : Ctx) (dir : Dir) (laws : Laws) (limit : Nat)
    (base : List RecR) :
    regroupAllSkipOAt ctx dir laws limit base = regroupAllSkipO ctx dir laws limit base := by
  unfold regroupAllSkipOAt regroupAllSkipO regroupSkipO
  rw [runAt_eq_run ctx dir laws (groupsOfEngineAt ctx) (groupsOfEngine ctx)
    (fun w st => regroupView_filter_cand ctx dir laws (groupsOfEngine ctx) w st)]
  unfold SkipSt.overlapAllAt SkipSt.overlapAll
  split
  · rfl
  · refine congrArg SkipSt.records (List.foldl_ext _ _ _ (fun st w _ => ?_))
    exact overlapView_filter_cand ctx laws limit (groupsOfEngine ctx) w _ st

/-! ## Pruning keeps the accepted matches -/

/-- A raw view holding `(g, 1)` whose normal form does not hold `g` has laws
that drop classes (`canDrop_of_gone` for any raw view). -/
theorem canDrop_of_gone_raw {κ : FlatKind} {laws : Laws} {g : C} {raw w : List (C × Nat)}
    (hm : (g, 1) ∈ raw) (hn : normalize κ laws raw = .node w) (hg : g ∉ w.map Prod.fst) :
    canDrop κ laws = true := by
  by_contra hc
  rw [Bool.not_eq_true] at hc
  apply hg
  have hw : w = normalizeList κ laws raw := by
    unfold normalize at hn; exact ((classify_node_iff _ _ _).1 hn).1.symm
  rw [hw, normalizeList_of_not_canDrop hc]
  cases κ with
  | assoc => exact List.mem_map_of_mem (f := Prod.fst) hm
  | ac =>
      show g ∈ (Multiset.entries (ofEntries raw)).map Prod.fst
      unfold Multiset.entries
      rw [List.map_map]
      simp only [Function.comp_def, List.map_id', Finset.mem_sort, Multiset.mem_toFinset]
      exact mem_ofEntries.2 ⟨(g, 1), hm, rfl, Nat.one_pos⟩
  | aci =>
      show g ∈ (((raw.map Prod.fst).toFinset.sort (· ≤ ·)).map (fun c => (c, 1))).map Prod.fst
      rw [List.map_map]
      simp only [Function.comp_def, List.map_id', Finset.mem_sort, List.mem_toFinset]
      exact List.mem_map_of_mem (f := Prod.fst) hm

/-- An overlap record of a record derived from `r₀` is derived from `r₀`. -/
theorem recRel_overlap {ctx : Ctx} {laws : Laws} {limit : Nat} {r₀ r r' : RecR}
    (h : RecRel ctx laws r₀ r) (h' : r' ∈ overlapRec ctx laws limit r) : RecRel ctx laws r₀ r' := by
  obtain ⟨g, grp, raw, hgg, hraw, hn, he⟩ := mem_overlapRec.1 h'
  obtain ⟨φ, hφ, hrel⟩ := h
  obtain ⟨w', ls', ns'⟩ := r'
  simp only [deriveRec, Prod.mk.injEq] at he
  obtain ⟨-, hls, -⟩ := he
  refine ⟨addG g (grp.map Prod.fst) (w'.map Prod.fst) ∘ φ, ?_,
    fun l => leafRel_addG hgg (fun hg => canDrop_of_gone_raw (g_mem_overlapFits hraw) hn hg) (hrel l)⟩
  show ls' = _
  rw [hls, hφ, List.map_map]

/-- A record of the stage of the walk's records `recs` is one of the stage of
`recs'` when `recs ⊆ recs'`. -/
theorem regroupAllO_mono {ctx : Ctx} {dir : Dir} {laws : Laws} {limit F : Nat}
    {recs recs' : List RecR} (hs : ∀ r ∈ recs, r ∈ recs') {r : RecR}
    (h : r ∈ regroupAllO ctx dir laws limit F recs) : r ∈ regroupAllO ctx dir laws limit F recs' := by
  unfold regroupAllO overlapStage regroupAll at h ⊢
  rw [List.mem_append, mem_dedupH, List.mem_flatMap] at h ⊢
  rcases h with h | ⟨r', hr', h⟩
  · exact Or.inl (regroupLevels_mono ctx dir laws hs h)
  · exact Or.inr ⟨r', regroupLevels_mono ctx dir laws hs hr', h⟩

/-- **Pruning is match-preserving with the stage**: for `taken` inside a
downward-closed `T`, a view accepts `taken` through the pruned enumeration
with the stage iff it does through the unpruned one. -/
theorem prune_regroupO {T : C → Bool} {ctx : Ctx} {dir : Dir} {laws : Laws} {limit : Nat}
    {n : Node} (hT : DownClosed ctx T) {w : List (C × Nat)} {taken : List C}
    (htk : ∀ c ∈ taken, T c = true) :
    (∃ d, (w, d) ∈ enumerateRDO T ctx dir laws limit n ∧ d.acceptsE ctx.κ taken) ↔
      (∃ d, (w, d) ∈ enumerateRO ctx dir laws limit n ∧ d.acceptsE ctx.κ taken) := by
  unfold enumerateRDO enumerateRO
  rw [acceptsE_enumerateFromR, acceptsE_enumerateFromR]
  constructor
  · rintro ⟨r, hr, hw, hall⟩
    obtain ⟨hr, hlim⟩ := mem_withinLimit.1 hr
    exact ⟨r, mem_withinLimit.2 ⟨regroupAllO_mono (fun r h => (List.mem_filter.1 h).1) hr, hlim⟩,
      hw, hall⟩
  · rintro ⟨r, hr, hw, hall⟩
    obtain ⟨hr, hlim⟩ := mem_withinLimit.1 hr
    refine ⟨r, mem_withinLimit.2 ⟨?_, hlim⟩, hw, hall⟩
    unfold regroupAllO overlapStage regroupAll at hr ⊢
    rw [List.mem_append, mem_dedupH, List.mem_flatMap] at hr ⊢
    rcases hr with hr | ⟨r', hr', hro⟩
    · obtain ⟨r₀, h₀, hr₀⟩ := (mem_regroupLevels_iff ctx dir laws _ _ r).1 hr
      obtain ⟨v, ls, -, hfl, -⟩ := mem_baseRecsR h₀
      have hkeep := keepRec_of_accept hT htk hfl (recRel_of_mem hr₀)
        (fun l hl => hall l (List.mem_append_left _ hl))
      exact Or.inl ((mem_regroupLevels_iff ctx dir laws _ _ r).2
        ⟨r₀, List.mem_filter.2 ⟨h₀, hkeep⟩, hr₀⟩)
    · obtain ⟨r₀, h₀, hr₀⟩ := (mem_regroupLevels_iff ctx dir laws _ _ r').1 hr'
      obtain ⟨v, ls, -, hfl, -⟩ := mem_baseRecsR h₀
      have hkeep := keepRec_of_accept hT htk hfl (recRel_overlap (recRel_of_mem hr₀) hro)
        (fun l hl => hall l (List.mem_append_left _ hl))
      exact Or.inr ⟨r', (mem_regroupLevels_iff ctx dir laws _ _ r').2
        ⟨r₀, List.mem_filter.2 ⟨h₀, hkeep⟩, hr₀⟩, hro⟩

/-! ## The specification -/

theorem normal_enumerateRO {ctx : Ctx} {dir : Dir} {laws : Laws} {limit : Nat} {n : Node}
    {w : List (C × Nat)} {d : DemandL} (h : (w, d) ∈ enumerateRO ctx dir laws limit n) :
    ∃ v, normalize ctx.κ laws v = .node w := by
  obtain ⟨r, hr, rfl⟩ := reachO_of_mem_enumerateRO h
  exact reachO_normal normal_baseRecsR hr

theorem normal_enumerateRDO {T : C → Bool} {ctx : Ctx} {dir : Dir} {laws : Laws} {limit : Nat}
    {n : Node} {w : List (C × Nat)} {d : DemandL} (h : (w, d) ∈ enumerateRDO T ctx dir laws limit n) :
    ∃ v, normalize ctx.κ laws v = .node w := by
  unfold enumerateRDO at h
  obtain ⟨r, hr, rfl⟩ := mem_enumerateFromR h
  have hb := baseGood_filter (baseGood_baseRecsR ctx dir laws n) (keepRec ctx.κ T laws)
  exact reachO_normal (fun r hr => normal_baseRecsR r (List.mem_filter.1 hr).1)
    ((mem_regroupAllO_iff_reachO hb (fun _ h => viewSize_le_regroupFuel (List.mem_filter.1 h).1)).1
      (mem_withinLimit.1 hr).1)

/-- **The full enumeration with the stage meets the plan specification.** -/
theorem regroupO_spec (dir : Sym → Dir) : (Enumerator.regroupO dir).Spec where
  normal h := normal_enumerateRO h
  normalP h := normal_enumerateRDO h
  to_full hext hb h hacc :=
    (prune_regroupO (takeableR_down _ _ _) (takenOf_takeableR hext hb)).1 ⟨_, h, hacc⟩
  to_pruned hext hb h hacc :=
    (prune_regroupO (takeableR_down _ _ _) (takenOf_takeableR hext hb)).2 ⟨_, h, hacc⟩

theorem normal_enumerateRSkipO {ctx : Ctx} {dir : Dir} {laws : Laws} {limit : Nat} {n : Node}
    {w : List (C × Nat)} {d : DemandL} (h : (w, d) ∈ enumerateRSkipO ctx dir laws limit n) :
    ∃ v, normalize ctx.κ laws v = .node w := by
  obtain ⟨r, hr, rfl⟩ := reachO_of_mem_enumerateRSkipO h
  exact reachO_normal normal_baseRecsR hr

theorem normal_enumerateRDSkipO {T : C → Bool} {ctx : Ctx} {dir : Dir} {laws : Laws} {limit : Nat}
    {n : Node} {w : List (C × Nat)} {d : DemandL}
    (h : (w, d) ∈ enumerateRDSkipO T ctx dir laws limit n) :
    ∃ v, normalize ctx.κ laws v = .node w := by
  unfold enumerateRDSkipO regroupAllSkipO at h
  obtain ⟨r, hr, rfl⟩ := mem_enumerateFromR h
  have hb := baseGood_filter (baseGood_baseRecsR ctx dir laws n) (keepRec ctx.κ T laws)
  exact reachO_normal (fun r hr => normal_baseRecsR r (List.mem_filter.1 hr).1)
    ((regroupSkipO_spec hb (groupsOfEngine_sub ctx) (candSup_of_sup dir (groupsOfEngine_sup ctx))
      (candSupO_of_sup (groupsOfEngine_sup ctx))).1 r (mem_withinLimit.1 hr).1)

/-- **The engine's enumeration with the stage meets the plan specification.** -/
theorem regroupSkipO_specE (dir : Sym → Dir) : (Enumerator.regroupSkipO dir).Spec where
  normal h := normal_enumerateRSkipO h
  normalP h := normal_enumerateRDSkipO h
  to_full {ctx laws σ σ' items n w d} hext hb h hacc := by
    have h' : (w, d) ∈ enumerateRDSkipO (takeableR ctx σ items) ctx (dir ctx.f) laws
        items.length n := h
    obtain ⟨d₁, hd₁, hacc₁⟩ := enumerateRDSkipO_iff.1 ⟨d, h', hacc⟩
    obtain ⟨d₂, hd₂, hacc₂⟩ :=
      (prune_regroupO (takeableR_down _ _ _) (takenOf_takeableR hext hb)).1 ⟨d₁, hd₁, hacc₁⟩
    show ∃ d', (w, d') ∈ enumerateRSkipO ctx (dir ctx.f) laws items.length n ∧ _
    exact enumerateRSkipO_iff.2 ⟨d₂, hd₂, hacc₂⟩
  to_pruned {ctx laws σ σ' items n w d} hext hb h hacc := by
    have h' : (w, d) ∈ enumerateRSkipO ctx (dir ctx.f) laws items.length n := h
    obtain ⟨d₁, hd₁, hacc₁⟩ := enumerateRSkipO_iff.1 ⟨d, h', hacc⟩
    obtain ⟨d₂, hd₂, hacc₂⟩ :=
      (prune_regroupO (takeableR_down _ _ _) (takenOf_takeableR hext hb)).2 ⟨d₁, hd₁, hacc₁⟩
    show ∃ d', (w, d') ∈ enumerateRDSkipO (takeableR ctx σ items) ctx (dir ctx.f) laws
      items.length n ∧ _
    exact enumerateRDSkipO_iff.2 ⟨d₂, hd₂, hacc₂⟩

/-- **An atom holds under the engine's enumeration with the stage iff under
the full one with it.** -/
theorem atomSat_regroupSkipO_iff {c : FCtx} {dir : Sym → Dir} {σ : Binding} {a : RAtom} :
    AtomSatG (Enumerator.regroupSkipO dir) c σ a ↔ AtomSatG (Enumerator.regroupO dir) c σ a := by
  unfold AtomSatG
  split
  · exact Iff.rfl
  · rename_i κ _
    constructor
    · rintro ⟨id, n, h1, h2, h3, h4, w, d, hd, hm, hacc⟩
      obtain ⟨d', hd', hacc'⟩ := (enumerateRSkipO_iff (ctx := c.ctx a.op κ)).1 ⟨d, hd, hacc⟩
      exact ⟨id, n, h1, h2, h3, h4, w, d', hd', hm, hacc'⟩
    · rintro ⟨id, n, h1, h2, h3, h4, w, d, hd, hm, hacc⟩
      obtain ⟨d', hd', hacc'⟩ := (enumerateRSkipO_iff (ctx := c.ctx a.op κ)).2 ⟨d, hd, hacc⟩
      exact ⟨id, n, h1, h2, h3, h4, w, d', hd', hm, hacc'⟩

/-- **Soundness of the flattened plan with the engine's regrouping and the stage.** -/
theorem regroupSkipO_plan_sound {c : FCtx} {dir : Sym → Dir} {sig : Sym → Kind}
    {as : List RAtom} (r : Nat) (hw : QueryFWF c sig as) {env' : EEnv}
    (h : env' ∈ runERSkipO c dir (planF as ∅ r) EEnv.empty) :
    (∀ a ∈ as, AtomSatG (Enumerator.regroupSkipO dir) c env'.σ a) ∧
      ClsDom env'.σ (planBound as ∅) :=
  flatten_plan_sound_of_spec (regroupSkipO_specE dir) r hw h

/-- **Completeness of the flattened plan with the engine's regrouping and the stage.** -/
theorem regroupSkipO_plan_complete {c : FCtx} {dir : Sym → Dir} {sig : Sym → Kind}
    {as : List RAtom} (r : Nat) (hw : QueryFWF c sig as) {σ' : Binding}
    (hsat : ∀ a ∈ as, AtomSatG (Enumerator.regroupSkipO dir) c σ' a) :
    ∃ env' ∈ runERSkipO c dir (planF as ∅ r) EEnv.empty, Binding.Extends env'.σ σ' :=
  flatten_plan_complete_of_spec (regroupSkipO_specE dir) r hw hsat

/-! ## Characterization -/

/-- **One overlap step under the laws, declaratively**: an `f`-member of
class `g`, a raw overlap fit of its group in the record's view
(`overlapFits`: the view less a sublist of the group's classes, as many as
the item count fixes, with `g` appended), normalized under the laws to the
node `w'`; the leaves gain `g` where they hold a class of the group and the
needed classes are those of a regrouping by the group (`deriveRec`). -/
inductive OverlapStepL (ctx : Ctx) (laws : Laws) (limit : Nat) : RecR → RecR → Prop
  | mk {r : RecR} {id : NodeId} {m : Node} {g : C} {raw w' : List (C × Nat)} :
      ctx.IsMember id m g → raw ∈ overlapFits ctx.κ limit r.1 g (kids ctx.κ m.children) →
      normalize ctx.κ laws raw = .node w' →
      OverlapStepL ctx laws limit r (deriveRec w' g ((kids ctx.κ m.children).map Prod.fst) r)

/-- One overlap step is exactly one overlap record of the model. -/
theorem overlapStepL_iff {ctx : Ctx} {laws : Laws} {limit : Nat} {r r' : RecR} :
    OverlapStepL ctx laws limit r r' ↔ r' ∈ overlapRec ctx laws limit r := by
  constructor
  · rintro ⟨hm, hraw, hn⟩
    exact overlapRec_of (mem_groupsOf_of_member hm) hraw hn
  · intro h
    obtain ⟨g, grp, raw, hgg, hraw, hn, he⟩ := mem_overlapRec.1 h
    obtain ⟨id, m, hm, rfl⟩ := mem_groupsOf hgg
    rw [he]
    exact OverlapStepL.mk hm hraw hn

/-- A chain of regroupings under the laws, then at most one overlap step. -/
def RegroupChainO (ctx : Ctx) (dir : Dir) (laws : Laws) (limit : Nat) (r₀ r : RecR) : Prop :=
  RegroupChainL ctx dir laws r₀ r ∨
    ∃ r₁, RegroupChainL ctx dir laws r₀ r₁ ∧ OverlapStepL ctx laws limit r₁ r

/-- **The views with regrouping and the stage are exactly the views of the
chains with at most one overlap step** (`regroup_views_iff_laws` with the
stage). -/
theorem regroupO_views_iff_laws {ctx : Ctx} {dir : Dir} {laws : Laws} {limit : Nat} {n : Node}
    {w : List (C × Nat)} {taken : List C} :
    (∃ d, (w, d) ∈ enumerateRO ctx dir laws limit n ∧ d.acceptsE ctx.κ taken) ↔
      ∃ r₀ ∈ baseRecsR ctx dir laws n, ∃ r, RegroupChainO ctx dir laws limit r₀ r ∧ r.1 = w ∧
        r.2.2.length ≤ limit ∧ ∀ l ∈ r.alt, l.okE ctx.κ taken := by
  unfold enumerateRO
  rw [acceptsE_enumerateFromR]
  have hb := baseGood_baseRecsR ctx dir laws n
  have hF : ∀ r ∈ baseRecsR ctx dir laws n,
      viewSize r.1 ≤ regroupFuel (baseRecsR ctx dir laws n) :=
    fun _ h => viewSize_le_regroupFuel h
  constructor
  · rintro ⟨r, hr, hw, hacc⟩
    obtain ⟨hr, hlim⟩ := mem_withinLimit.1 hr
    rcases (mem_regroupAllO_iff_reachO hb hF).1 hr with ⟨r₀, h₀, hch⟩ | ⟨r₁, ⟨r₀, h₀, hch⟩, ho⟩
    · exact ⟨r₀, h₀, r, Or.inl ((regroupChainL_iff (viewOK_baseL h₀)).2 hch), hw, hlim, hacc⟩
    · exact ⟨r₀, h₀, r, Or.inr ⟨r₁, (regroupChainL_iff (viewOK_baseL h₀)).2 hch,
        overlapStepL_iff.2 ho⟩, hw, hlim, hacc⟩
  · rintro ⟨r₀, h₀, r, hch, hw, hlim, hacc⟩
    refine ⟨r, mem_withinLimit.2 ⟨(mem_regroupAllO_iff_reachO hb hF).2 ?_, hlim⟩, hw, hacc⟩
    rcases hch with hch | ⟨r₁, hch, ho⟩
    · exact Or.inl ⟨r₀, h₀, (regroupChainL_iff (viewOK_baseL h₀)).1 hch⟩
    · exact Or.inr ⟨r₁, ⟨r₀, h₀, (regroupChainL_iff (viewOK_baseL h₀)).1 hch⟩,
        overlapStepL_iff.1 ho⟩

/-- **The matches with regrouping and the stage, characterized**
(`regroup_match_iff_laws` with the stage): an n-ary atom holds under
`AtomSatG (Enumerator.regroupO dir)` iff some chain of regroupings under the
laws, followed by at most one overlap step, takes a walk record of a stored
node of the atom's class to a record on whose view the binding matches the
shallow pattern, the record needing at most as many classes as the atom has
items, with the item classes satisfying its leaves and taking the classes
it needs. -/
theorem regroupO_match_iff_laws {c : FCtx} {dir : Sym → Dir} {σ : Binding} {a : RAtom}
    {κ : FlatKind} (hκ : a.shape.flatKind = some κ) :
    AtomSatG (Enumerator.regroupO dir) c σ a ↔
      ∃ id n, σ.node a.node = some id ∧ (id, n) ∈ c.G.nodes ∧
        σ.cls a.node = some (c.G.find id) ∧ n.op = a.op ∧
        ∃ r₀ ∈ baseRecsR (c.ctx a.op κ) (dir a.op) (c.laws a.op) n, ∃ r,
          RegroupChainO (c.ctx a.op κ) (dir a.op) (c.laws a.op) a.elems.length r₀ r ∧
          r.2.2.length ≤ a.elems.length ∧
          MatchN c.G a.shallow ⟨a.op, ofView κ r.1⟩ σ ∧
          ∀ l ∈ r.alt, l.okE κ (takenOf σ a.elems) := by
  unfold AtomSatG
  rw [hκ]
  constructor
  · rintro ⟨id, n, hnode, hmem, hcls, hop, w, d, hd, hm, hacc⟩
    obtain ⟨r₀, h₀, r, hch, rfl, hlim, hacc'⟩ :=
      (regroupO_views_iff_laws (ctx := c.ctx a.op κ) (taken := takenOf σ a.elems)).1 ⟨d, hd, hacc⟩
    exact ⟨id, n, hnode, hmem, hcls, hop, r₀, h₀, r, hch, hlim, hm, hacc'⟩
  · rintro ⟨id, n, hnode, hmem, hcls, hop, r₀, h₀, r, hch, hlim, hm, hacc⟩
    obtain ⟨d, hd, hacc'⟩ :=
      (regroupO_views_iff_laws (ctx := c.ctx a.op κ) (taken := takenOf σ a.elems)).2
        ⟨r₀, h₀, r, hch, rfl, hlim, hacc⟩
    exact ⟨id, n, hnode, hmem, hcls, hop, r.1, d, hd, hm, hacc'⟩

/-- **The engine's views with the stage are exactly the views of the chains
with at most one overlap step** (`regroupSkip_views_iff_laws` with the
stage). -/
theorem regroupSkipO_views_iff_laws {ctx : Ctx} {dir : Dir} {laws : Laws} {limit : Nat}
    {n : Node} {w : List (C × Nat)} {taken : List C} :
    (∃ d, (w, d) ∈ enumerateRSkipO ctx dir laws limit n ∧ d.acceptsE ctx.κ taken) ↔
      ∃ r₀ ∈ baseRecsR ctx dir laws n, ∃ r, RegroupChainO ctx dir laws limit r₀ r ∧ r.1 = w ∧
        r.2.2.length ≤ limit ∧ ∀ l ∈ r.alt, l.okE ctx.κ taken :=
  enumerateRSkipO_iff.trans regroupO_views_iff_laws

/-- **The matches of the engine's views with the stage, characterized**
(`regroupSkip_match_iff_laws` with the stage): what the engine finds for an
idempotent operator, relative to the classes present. -/
theorem regroupSkipO_match_iff_laws {c : FCtx} {dir : Sym → Dir} {σ : Binding} {a : RAtom}
    {κ : FlatKind} (hκ : a.shape.flatKind = some κ) :
    AtomSatG (Enumerator.regroupSkipO dir) c σ a ↔
      ∃ id n, σ.node a.node = some id ∧ (id, n) ∈ c.G.nodes ∧
        σ.cls a.node = some (c.G.find id) ∧ n.op = a.op ∧
        ∃ r₀ ∈ baseRecsR (c.ctx a.op κ) (dir a.op) (c.laws a.op) n, ∃ r,
          RegroupChainO (c.ctx a.op κ) (dir a.op) (c.laws a.op) a.elems.length r₀ r ∧
          r.2.2.length ≤ a.elems.length ∧
          MatchN c.G a.shallow ⟨a.op, ofView κ r.1⟩ σ ∧
          ∀ l ∈ r.alt, l.okE κ (takenOf σ a.elems) :=
  atomSat_regroupSkipO_iff.trans (regroupO_match_iff_laws hκ)

/-- **Completeness of the flattened plan with the engine's regrouping and the
stage, chains under the laws** (`regroupSkip_plan_complete_laws` with the
stage). -/
theorem regroupSkipO_plan_complete_laws {c : FCtx} {dir : Sym → Dir} {sig : Sym → Kind}
    {as : List RAtom} (r : Nat) (hw : QueryFWF c sig as) {σ' : Binding}
    (hsat : ∀ a ∈ as, match a.shape.flatKind with
      | none => AtomSat c.G σ' a
      | some κ =>
          ∃ id n, σ'.node a.node = some id ∧ (id, n) ∈ c.G.nodes ∧
            σ'.cls a.node = some (c.G.find id) ∧ n.op = a.op ∧
            ∃ r₀ ∈ baseRecsR (c.ctx a.op κ) (dir a.op) (c.laws a.op) n, ∃ r,
              RegroupChainO (c.ctx a.op κ) (dir a.op) (c.laws a.op) a.elems.length r₀ r ∧
              r.2.2.length ≤ a.elems.length ∧
              MatchN c.G a.shallow ⟨a.op, ofView κ r.1⟩ σ' ∧
              ∀ l ∈ r.alt, l.okE κ (takenOf σ' a.elems)) :
    ∃ env' ∈ runERSkipO c dir (planF as ∅ r) EEnv.empty, Binding.Extends env'.σ σ' := by
  refine regroupSkipO_plan_complete r hw (fun a ha => ?_)
  have h := hsat a ha
  revert h
  cases hκ : a.shape.flatKind with
  | none =>
      intro h
      unfold AtomSatG; rw [hκ]; exact h
  | some κ =>
      intro h
      exact (regroupSkipO_match_iff_laws hκ).2 h

/-- Without idempotence the chains with the stage are the chains. -/
theorem regroupChainO_iff_of_not_aci {ctx : Ctx} (hκ : ctx.κ ≠ .aci) {dir : Dir} {laws : Laws}
    {limit : Nat} {r₀ r : RecR} :
    RegroupChainO ctx dir laws limit r₀ r ↔ RegroupChainL ctx dir laws r₀ r := by
  constructor
  · rintro (h | ⟨r₁, -, ho⟩)
    · exact h
    · have := overlapStepL_iff.1 ho
      rw [overlapRec_eq_nil_of_not_aci hκ] at this
      simp at this
  · exact Or.inl

/-! ## The counter-model, found -/

/-- A sorted list of distinct classes is the sort of its finset. -/
theorem sort_eq_of_sorted {l : List C} (hnd : l.Nodup) (hs : l.Pairwise (· ≤ ·)) :
    l.toFinset.sort (· ≤ ·) = l :=
  (List.toFinset_sort (· ≤ ·) hnd).2 hs

theorem exAci_kids : kids .aci (.set {1, 2, 3}) = [(1, 1), (2, 1), (3, 1)] := by
  show (({1, 2, 3} : Finset C).sort (· ≤ ·)).map (fun c => (c, 1)) = _
  rw [show ({1, 2, 3} : Finset C) = [1, 2, 3].toFinset by decide,
    sort_eq_of_sorted (by decide) (by decide)]
  rfl

theorem exAci_kids_group : kids .aci (.set {1, 2}) = [(1, 1), (2, 1)] := by
  show (({1, 2} : Finset C).sort (· ≤ ·)).map (fun c => (c, 1)) = _
  rw [show ({1, 2} : Finset C) = [1, 2].toFinset by decide,
    sort_eq_of_sorted (by decide) (by decide)]
  rfl

/-- The walk record of `S{a, b, c}` with every child kept. -/
theorem exAci_base :
    ([(1, 1), (2, 1), (3, 1)], [], []) ∈ baseRecsR exAciCtx .both Laws.free exAciRoot := by
  refine kept_mem_baseRecsR ?_
  show normalize .aci Laws.free (scale 1 (kids .aci (.set {1, 2, 3}))) = _
  rw [exAci_kids]
  show classify none (dedupAci (scale 1 [(1, 1), (2, 1), (3, 1)])) = _
  unfold dedupAci
  rw [map_fst_scale, show ([(1, 1), (2, 1), (3, 1)] : List (C × Nat)).map Prod.fst = [1, 2, 3]
    from rfl, sort_eq_of_sorted (by decide) (by decide)]
  rfl

/-- **The idempotent group kept beside its class is found.** In the graph of
`regroup_idem_overlap_sound` (`G ∋ S{a, b}`, the root `S{a, b, c}`), the
engine's enumeration with the overlap stage for a pattern of three items
has the view `{a, c, G}` accepting the item classes `[a, c, G]`: the walk
record `{a, b, c}` takes one overlap step by `G`, dropping `b` and keeping
`a`, to a record needing `G` alone. So `(S x y z)` binds `x = a, y = c,
z = G` (`flatten_regroup_laws_idem.egg`), a match the loop alone never
forms (`regroup_idem_overlap_loop_lost`) and that is sound in every join
semilattice (`regroup_idem_overlap_sound`). -/
theorem regroup_idem_overlap_found :
    ∃ d, ([(1, 1), (3, 1), (4, 1)], d) ∈ enumerateRSkipO exAciCtx .both Laws.free 3 exAciRoot ∧
      d.acceptsE .aci [1, 3, 4] := by
  have hmem : exAciCtx.IsMember 10 ⟨8, .set {1, 2}⟩ 4 := by
    simp [Ctx.IsMember, exAciCtx, exAciG]
  have hgc : groupClasses (kids exAciCtx.κ (Node.children ⟨8, .set {1, 2}⟩)) = [1, 2] := by
    show groupClasses (kids .aci (.set {1, 2})) = _
    rw [exAci_kids_group]
    unfold groupClasses dedupAci
    rw [show ([(1, 1), (2, 1)] : List (C × Nat)).map Prod.fst = [1, 2] from rfl,
      sort_eq_of_sorted (by decide) (by decide)]
    rfl
  have hraw : [(1, 1), (3, 1), (4, 1)] ∈ overlapFits exAciCtx.κ 3 [(1, 1), (2, 1), (3, 1)] 4
      (kids exAciCtx.κ (Node.children ⟨8, .set {1, 2}⟩)) := by
    refine mem_overlapFits.2 ⟨1, [2], ?_, ?_, rfl, rfl⟩
    · unfold overlapDrops
      rw [hgc]
      decide
    · rw [hgc]
      decide
  have hn : normalize exAciCtx.κ Laws.free [(1, 1), (3, 1), (4, 1)] =
      .node [(1, 1), (3, 1), (4, 1)] := by
    show classify none (dedupAci _) = _
    unfold dedupAci
    rw [show ([(1, 1), (3, 1), (4, 1)] : List (C × Nat)).map Prod.fst = [1, 3, 4] from rfl,
      sort_eq_of_sorted (by decide) (by decide)]
    rfl
  have hstep : OverlapStepL exAciCtx Laws.free 3 ([(1, 1), (2, 1), (3, 1)], [], [])
      ([(1, 1), (3, 1), (4, 1)], [], [4]) := by
    have h := OverlapStepL.mk (ctx := exAciCtx) (laws := Laws.free) (limit := 3)
      (r := ([(1, 1), (2, 1), (3, 1)], [], [])) hmem hraw hn
    have hd : deriveRec [(1, 1), (3, 1), (4, 1)] 4
        ((kids exAciCtx.κ (Node.children ⟨8, .set {1, 2}⟩)).map Prod.fst)
        ([(1, 1), (2, 1), (3, 1)], [], []) = ([(1, 1), (3, 1), (4, 1)], [], [4]) := by
      show deriveRec _ _ ((kids .aci (.set {1, 2})).map Prod.fst) _ = _
      rw [exAci_kids_group]
      rfl
    rw [hd] at h
    exact h
  refine (regroupSkipO_views_iff_laws (ctx := exAciCtx) (dir := .both) (laws := Laws.free)
    (limit := 3) (n := exAciRoot) (taken := [1, 3, 4])).2
    ⟨_, exAci_base, _, Or.inr ⟨_, Relation.ReflTransGen.refl, hstep⟩, rfl, by decide, ?_⟩
  intro l hl
  simp only [RecR.alt, List.nil_append, List.map_cons, List.map_nil, List.mem_singleton] at hl
  subst hl
  exact (needLeaf_okE _ _ _).2 (by decide)

end Semper.EMatch.Flatten
