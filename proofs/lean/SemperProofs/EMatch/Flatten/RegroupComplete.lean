import SemperProofs.EMatch.Flatten.RegroupSound

/-!
# `:flatten`: completeness of regrouped views, AC

A match modulo associativity and commutativity may bind a variable to a
class that spells a group of the view's entries through an `f`-member:
`(f x y)` against `f{a, b, c}` with `x` the class `G ∋ f{a, b}`. This file
proves that the enumeration with regrouped views finds every such match,
for a laws-free AC operator:

* `fitsR_ac_complete`: a sub-multiset of at least two entries, not the whole
  view, spelled by a member of `g` not over `g` itself, fits;
* `regroup_chain_ac`: disjoint groups `gs` (their sum within the view, none
  the whole view, so groups covering the view together are included) are
  regrouped one after the other, at most one regrouped class per
  group, each regrouped leaf holding `g` whenever it holds a class of `g`'s
  group;
* `regroup_view_complete_ac`: the view `w₀ - Σ groups + Σ {g}` is in the
  enumeration, with a demand accepting every `taken` that holds each `g`
  and satisfies each leaf of `w₀`'s opening tree through the classes of the
  groups;
* `regroup_match_complete_ac`: hence an AC atom whose variables bind those
  classes satisfies `AtomSatG (Enumerator.regroup dir)`, and
  `regroup_plan_complete` emits the binding.

The groups are the engine's: a group spelled by a member over its own class
(`g ∋ f{g, c}`) and a group that is the whole view are excluded (`hself`,
`hne`), as `fits` excludes them; the number of groups is at most the number
of items (`hlim`, `Demand::needs`). Groups are disjoint here, each over
entries of the walk's view; nested groups (a group holding the class of an
earlier one) and every other kind are covered by the chain theorems of
`RegroupChain.lean`.
-/

namespace Semper.EMatch.Flatten

open Semper.EMatch
open Binding (Extends)

/-! ## One group fits -/

theorem find?_class {view : List (C × Nat)} (hnd : (view.map Prod.fst).Nodup) {c : C}
    (hc : c ∈ ofEntries view) :
    ∃ x, view.find? (fun e => decide (e.1 = c)) = some (c, x) ∧ (c, x) ∈ view ∧
      (ofEntries view).count c = x := by
  obtain ⟨e, he, hec, -⟩ := mem_ofEntries.1 hc
  have hs : (view.find? (fun e => decide (e.1 = c))).isSome := by
    rw [List.find?_isSome]; exact ⟨e, he, by simpa using hec⟩
  obtain ⟨e', he'⟩ := Option.isSome_iff_exists.1 hs
  have hc' : e'.1 = c := by simpa using List.find?_some he'
  obtain ⟨c', x⟩ := e'
  simp only at hc'
  subst hc'
  have hm := List.mem_of_find?_eq_some he'
  exact ⟨x, he', hm, count_ofEntries_of_nodup hnd hm⟩

theorem subEntries_some :
    ∀ (norm view : List (C × Nat)), (view.map Prod.fst).Nodup → (∀ e ∈ norm, 0 < e.2) →
      ofEntries norm ≤ ofEntries view → ∃ v, subEntries view norm = some v
  | [], view, _, _, _ => ⟨_, rfl⟩
  | (c, k) :: rest, view, hnd, hpos, hle => by
      have hk := hpos (c, k) (List.mem_cons_self ..)
      rw [ofEntries_cons] at hle
      have hc : c ∈ ofEntries view :=
        Multiset.mem_of_le hle (Multiset.mem_add.2 (Or.inl (Multiset.mem_replicate.2
          ⟨Nat.pos_iff_ne_zero.1 hk, rfl⟩)))
      obtain ⟨x, hf, hm, hcount⟩ := find?_class hnd hc
      have hkx : k ≤ x := by
        rw [← hcount]
        have := Multiset.count_le_of_le c hle
        rw [Multiset.count_add, Multiset.count_replicate_self] at this
        omega
      have hnd' : ((view.map (fun e => if e.1 = c then (c, x - k) else e)).map Prod.fst).Nodup := by
        rw [List.map_map]
        convert hnd using 2
        funext e
        simp only [Function.comp_apply]
        split <;> simp_all
      have hsub := count_ofEntries_map_sub hnd hm hkx
      have hle' : ofEntries rest ≤ ofEntries (view.map (fun e => if e.1 = c then (c, x - k) else e)) := by
        have h3 : Multiset.replicate k c + ofEntries rest ≤
            Multiset.replicate k c + ofEntries (view.map (fun e => if e.1 = c then (c, x - k) else e)) := by
          have e : ofEntries view = Multiset.replicate k c +
              ofEntries (view.map (fun e => if e.1 = c then (c, x - k) else e)) := by
            rw [← hsub, add_comm]
          rw [← e]; simpa using hle
        exact (add_le_add_iff_left _).1 h3
      obtain ⟨v, hv⟩ := subEntries_some rest _ hnd'
        (fun e he => hpos e (List.mem_cons_of_mem _ he)) hle'
      refine ⟨v, ?_⟩
      simp only [subEntries, hf, hkx, ↓reduceIte]
      exact hv

theorem entries_head_of_card {m : Multiset C} (h : 2 ≤ Multiset.card m) :
    (decide (2 ≤ (Multiset.entries m).length) ||
      ((Multiset.entries m).head?.map (fun e => decide (1 < e.2))).getD false) = true := by
  by_cases h2 : 2 ≤ m.toFinset.card
  · simp [Multiset.entries, h2]
  · have hpos : 0 < m.toFinset.card := by
      rw [Finset.card_pos, Multiset.toFinset_nonempty]
      intro h0; subst h0; simp at h
    have h1 : m.toFinset.card = 1 := by omega
    obtain ⟨c, hc⟩ := Finset.card_eq_one.1 h1
    have hmc : m = Multiset.replicate (Multiset.card m) c := by
      apply Multiset.eq_replicate_card.2
      intro b hb
      have : b ∈ m.toFinset := Multiset.mem_toFinset.2 hb
      rw [hc] at this
      simpa using this
    have hcount : m.count c = Multiset.card m := by
      conv_lhs => rw [hmc]
      simp
    simp only [Multiset.entries, hc, Finset.sort_singleton, List.map_cons, List.map_nil,
      List.length_singleton, List.head?_cons, Option.map_some, Option.getD_some, hcount]
    simp
    omega

/-- **A group fits, AC.** -/
theorem fitsR_ac_complete {dir : Dir} {view : List (C × Nat)} {g : C} {grp : List (C × Nat)}
    (hnd : (view.map Prod.fst).Nodup) (hg : g ∉ grp.map Prod.fst)
    (hle : ofEntries grp ≤ ofEntries view) (hne : ofEntries grp ≠ ofEntries view)
    (h2 : 2 ≤ Multiset.card (ofEntries grp)) :
    ∃ v, v ++ [(g, 1)] ∈ fitsR .ac dir view g grp ∧ ofEntries v + ofEntries grp = ofEntries view := by
  have hc : ofEntries (coalesce grp) = ofEntries grp := ofEntries_coalesce grp
  obtain ⟨v, hv⟩ := subEntries_some (coalesce grp) view hnd (coalesce_canonical grp).2
    (by rw [hc]; exact hle)
  refine ⟨v, ?_, by rw [← hc]; exact subEntries_spec _ _ _ hnd hv⟩
  have hany : grp.any (fun e => decide (e.1 = g)) = false := by
    simp only [List.any_eq_false, decide_eq_true_eq]
    intro e he heg
    exact hg (heg ▸ List.mem_map_of_mem he)
  have htwo : (decide (2 ≤ (coalesce grp).length) ||
      ((coalesce grp).head?.map (fun e => decide (1 < e.2))).getD false) = true :=
    entries_head_of_card h2
  have hneq : (coalesce grp == view) = false := by
    rw [beq_eq_false_iff_ne]
    intro he
    apply hne
    rw [← hc, he]
  unfold fitsR
  simp only [hany, groupNorm, Bool.false_eq_true, ↓reduceIte]
  simp only [hneq, hv, Bool.or_false]
  have ht : (!(decide (2 ≤ (coalesce grp).length) ||
      ((coalesce grp).head?.map (fun e => decide (1 < e.2))).getD false)) = false := by
    rw [htwo]; rfl
  simp
  intro hd
  rcases Bool.or_eq_true_iff.1 htwo with h | h
  · exact Bool.noConfusion (h.symm.trans hd)
  · exact h

/-! ## Normalization of a regrouped view, laws-free -/

theorem normalize_free_ac_node {raw : List (C × Nat)} (h : 2 ≤ Multiset.card (ofEntries raw)) :
    normalize .ac Laws.free raw = .node (coalesce raw) := by
  unfold normalize
  have hnl : normalizeList .ac Laws.free raw = coalesce raw := rfl
  rw [classify_node_iff, hnl]
  refine ⟨rfl, ?_, ?_⟩
  · intro h0
    have := ofEntries_coalesce raw
    rw [h0] at this
    rw [← this] at h
    simp [ofEntries] at h
  · intro c h0
    have := ofEntries_coalesce raw
    rw [h0] at this
    rw [← this] at h
    simp [ofEntries] at h

/-! ## A chain of groups -/

/-- The multiset of a list of groups. -/
def groupSum (gs : List (C × List (C × Nat))) : Multiset C := (gs.map (fun p => ofEntries p.2)).sum

/-- The regrouped classes, each once per group. -/
def groupCls (gs : List (C × List (C × Nat))) : Multiset C := ((gs.map (fun p => p.1) : List C) : Multiset C)

theorem needsAfter_length (g : C) (grp ns : List C) :
    (needsAfter g grp ns).length ≤ ns.length + 1 := by
  dsimp only [needsAfter]
  split
  · exact (List.length_filter_le _ _).trans (Nat.le_succ _)
  · simp only [List.length_append, List.length_singleton]
    exact Nat.succ_le_succ (List.length_filter_le _ _)

theorem mem_needsAfter {g : C} {grp ns : List C} {c : C} (h : c ∈ needsAfter g grp ns) :
    c ∈ ns ∨ c = g := by
  dsimp only [needsAfter] at h
  split at h
  · exact Or.inl (List.mem_filter.1 h).1
  · rcases List.mem_append.1 h with h | h
    · exact Or.inl (List.mem_filter.1 h).1
    · exact Or.inr (List.mem_singleton.1 h)

theorem g_mem_addG {g : C} {grp : List C} {l : LeafF} (h : ∃ c ∈ l.1.g, c ∈ grp) :
    g ∈ (addG g grp l).1.g := by
  unfold addG
  split
  · simp [LeafL.g]
  · rename_i hn
    by_contra hg
    exact hn ⟨hg, by simpa using h⟩

theorem g_subset_addG (g : C) (grp : List C) (l : LeafF) : l.1.g ⊆ (addG g grp l).1.g := by
  rcases addG_g (g := g) (grp := grp) (l := l) with he | ⟨he, -⟩
  · rw [he]
  · rw [he]; exact List.subset_append_left _ _

theorem mem_regroupLevels_succ {ctx : Ctx} {dir : Dir} {laws : Laws} {limit F : Nat}
    {r₀ r₁ r : RecR} (h₁ : r₁ ∈ regroupRec ctx dir laws limit r₀)
    (h : r ∈ regroupLevels ctx dir laws limit F [r₁]) :
    r ∈ regroupLevels ctx dir laws limit (F + 1) [r₀] := by
  simp only [regroupLevels, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  refine List.mem_append_right _ ((mem_regroupLevels_iff ctx dir laws limit F _ r).2 ⟨r₁, ?_, h⟩)
  exact mem_dedupH.2 h₁

theorem regroupLevels_fuel_succ (ctx : Ctx) (dir : Dir) (laws : Laws) (limit : Nat) :
    ∀ (F : Nat) (recs : List RecR) (r : RecR), r ∈ regroupLevels ctx dir laws limit F recs →
      r ∈ regroupLevels ctx dir laws limit (F + 1) recs
  | 0, _, _, h => List.mem_append_left _ h
  | F + 1, recs, r, h => by
      have h' : r ∈ recs ++ regroupLevels ctx dir laws limit F
          (dedupH (recs.flatMap (regroupRec ctx dir laws limit))) := h
      show r ∈ recs ++ regroupLevels ctx dir laws limit (F + 1)
        (dedupH (recs.flatMap (regroupRec ctx dir laws limit)))
      rcases List.mem_append.1 h' with h | h
      · exact List.mem_append_left _ h
      · exact List.mem_append_right _ (regroupLevels_fuel_succ ctx dir laws limit F _ r h)

theorem regroupLevels_fuel_mono (ctx : Ctx) (dir : Dir) (laws : Laws) (limit : Nat)
    {F F' : Nat} (hF : F ≤ F') {recs : List RecR} {r : RecR}
    (h : r ∈ regroupLevels ctx dir laws limit F recs) :
    r ∈ regroupLevels ctx dir laws limit F' recs := by
  induction hF with
  | refl => exact h
  | step _ ih => exact regroupLevels_fuel_succ ctx dir laws limit _ _ _ ih

/-- **A chain of groups, AC, laws-free.** From a record whose view is
canonical, the disjoint groups `gs` (each a member's children, not over its
own class, of at least two entries, their sum within the view, none the
whole view) are regrouped one after the other within `gs.length` levels: the view becomes
`w₀ - Σ groups + Σ {g}`, the needed classes are among the `g`, and every
leaf keeps its classes and holds `g` whenever it holds a class of `g`'s
group. -/
theorem regroup_chain_ac {ctx : Ctx} (hκ : ctx.κ = .ac) {dir : Dir} {limit : Nat} :
    ∀ (gs : List (C × List (C × Nat))) (r₀ : RecR),
      (∀ p ∈ gs, p ∈ groupsOf ctx) → (∀ p ∈ gs, p.1 ∉ p.2.map Prod.fst) →
      (∀ p ∈ gs, 2 ≤ Multiset.card (ofEntries p.2)) →
      groupSum gs ≤ ofEntries r₀.1 → (∀ p ∈ gs, ofEntries p.2 ≠ ofEntries r₀.1) →
      Multiset.entries (ofEntries r₀.1) = r₀.1 →
      r₀.2.2.length + gs.length ≤ limit →
      ∃ r ∈ regroupLevels ctx dir Laws.free limit gs.length [r₀],
        ofEntries r.1 = ofEntries r₀.1 - groupSum gs + groupCls gs ∧
        (∀ c ∈ r.2.2, c ∈ r₀.2.2 ∨ c ∈ gs.map Prod.fst) ∧
        ∃ φ : LeafF → LeafF, r.2.1 = r₀.2.1.map φ ∧ ∀ l, l.1.X = (φ l).1.X ∧
          l.2 = (φ l).2 ∧ l.1.g ⊆ (φ l).1.g ∧
          ∀ p ∈ gs, (∃ c ∈ l.1.g, c ∈ p.2.map Prod.fst) → p.1 ∈ (φ l).1.g
  | [], r₀, _, _, _, _, _, _, _ => by
      refine ⟨r₀, by simp [regroupLevels], by simp [groupSum, groupCls], fun c hc => Or.inl hc,
        id, by simp, fun l => ⟨rfl, rfl, fun _ h => h, by simp⟩⟩
  | (g, grp) :: gs, r₀, hgs, hself, h2, hsum0, hnes, hcan, hlim => by
      have hgg := hgs (g, grp) (List.mem_cons_self ..)
      have hlt : ofEntries grp + groupSum gs ≤ ofEntries r₀.1 := by
        simpa only [groupSum, List.map_cons, List.sum_cons] using hsum0
      have hle : ofEntries grp ≤ ofEntries r₀.1 :=
        le_trans (Multiset.le_add_right _ _) hlt
      have hne : ofEntries grp ≠ ofEntries r₀.1 := hnes (g, grp) (List.mem_cons_self ..)
      have hnd : (r₀.1.map Prod.fst).Nodup := by
        have := (coalesce_canonical r₀.1).nodup
        unfold coalesce at this
        rwa [hcan] at this
      obtain ⟨v, hfit, hsum⟩ := fitsR_ac_complete (dir := dir) hnd
        (hself (g, grp) (List.mem_cons_self ..)) hle hne (h2 (g, grp) (List.mem_cons_self ..))
      rw [← hκ] at hfit
      have hv0 : ofEntries v ≠ 0 := by
        intro h0; rw [h0, zero_add] at hsum; exact hne hsum
      have hcard : 2 ≤ Multiset.card (ofEntries (v ++ [(g, 1)])) := by
        rw [ofEntries_append]
        simp only [Multiset.card_add]
        have : 1 ≤ Multiset.card (ofEntries v) := Multiset.card_pos.2 hv0
        have h1 : Multiset.card (ofEntries [(g, 1)]) = 1 := by simp [ofEntries]
        omega
      have hn : normalize ctx.κ Laws.free (v ++ [(g, 1)]) = .node (coalesce (v ++ [(g, 1)])) := by
        rw [hκ]; exact normalize_free_ac_node hcard
      set r₁ : RecR := (coalesce (v ++ [(g, 1)]), r₀.2.1.map (addG g (grp.map Prod.fst)),
        needsAfter g (grp.map Prod.fst) r₀.2.2) with hr₁
      have hlen₁ : (needsAfter g (grp.map Prod.fst) r₀.2.2).length ≤ limit := by
        have := needsAfter_length g (grp.map Prod.fst) r₀.2.2
        simp only [List.length_cons] at hlim
        omega
      have hstep : r₁ ∈ regroupRec ctx dir Laws.free limit r₀ := regroupRec_of hgg hfit hn hlen₁
      have hS : groupSum gs ≤ ofEntries r₀.1 - ofEntries grp := le_tsub_of_add_le_left hlt
      have hofr₁ : ofEntries r₁.1 = ofEntries r₀.1 - ofEntries grp + {g} := by
        simp only [hr₁, ofEntries_coalesce, ofEntries_append]
        rw [eq_tsub_of_add_eq hsum]
        all_goals simp [ofEntries]
      have hlt₁ : groupSum gs < ofEntries r₁.1 := by
        rw [hofr₁, add_comm, Multiset.singleton_add]
        exact lt_of_le_of_lt hS (Multiset.lt_cons_self _ g)
      have hne₁ : ∀ p ∈ gs, ofEntries p.2 ≠ ofEntries r₁.1 := by
        intro p hp he
        have h1 : ofEntries p.2 ≤ groupSum gs :=
          List.le_sum_of_mem (List.mem_map_of_mem (f := fun p => ofEntries p.2) hp)
        rw [he] at h1
        exact absurd (lt_of_le_of_lt h1 hlt₁) (lt_irrefl _)
      have hcan₁ : Multiset.entries (ofEntries r₁.1) = r₁.1 := by
        simp only [hr₁, ofEntries_coalesce]; rfl
      obtain ⟨r, hr, hof, hneeds, φ, hφ, hrel⟩ := regroup_chain_ac hκ gs r₁
        (fun p hp => hgs p (List.mem_cons_of_mem _ hp))
        (fun p hp => hself p (List.mem_cons_of_mem _ hp))
        (fun p hp => h2 p (List.mem_cons_of_mem _ hp)) hlt₁.le hne₁ hcan₁ (by
          have := needsAfter_length g (grp.map Prod.fst) r₀.2.2
          simp only [List.length_cons] at hlim
          show (needsAfter g (grp.map Prod.fst) r₀.2.2).length + gs.length ≤ limit
          omega)
      refine ⟨r, mem_regroupLevels_succ hstep hr, ?_, ?_, φ ∘ addG g (grp.map Prod.fst), ?_, ?_⟩
      · rw [hof, hofr₁]
        have e1 : groupSum ((g, grp) :: gs) = ofEntries grp + groupSum gs := by
          simp [groupSum]
        have e2 : groupCls ((g, grp) :: gs) = {g} + groupCls gs := by
          simp [groupCls, Multiset.singleton_add]
        rw [e1, e2, ← tsub_add_eq_add_tsub hS, tsub_add_eq_tsub_tsub, add_assoc]
      · intro c hc
        rcases hneeds c hc with hc | hc
        · rcases mem_needsAfter hc with hc | rfl
          · exact Or.inl hc
          · exact Or.inr (List.mem_cons_self ..)
        · exact Or.inr (List.mem_cons_of_mem _ hc)
      · rw [hφ, hr₁, List.map_map]
      · intro l
        obtain ⟨hX, hf, hsub, hp⟩ := hrel (addG g (grp.map Prod.fst) l)
        refine ⟨(addG_X _ _ _).symm.trans hX, (addG_flag _ _ _).symm.trans hf,
          fun x hx => hsub (g_subset_addG g _ l hx), ?_⟩
        intro p hp' hc
        rcases List.mem_cons.1 hp' with rfl | hp'
        · exact hsub (g_mem_addG hc)
        · obtain ⟨c, hc, hcp⟩ := hc
          exact hp p hp' ⟨c, g_subset_addG g _ l hc, hcp⟩

/-! ## The regrouped view is enumerated, and its demand accepts -/

theorem viewSize_eq_card : ∀ w : List (C × Nat), viewSize w = Multiset.card (ofEntries w)
  | [] => rfl
  | e :: w => by
      rw [ofEntries_cons, Multiset.card_add, Multiset.card_replicate, ← viewSize_eq_card w]
      simp [viewSize]

theorem le_foldl_max : ∀ (l : List Nat) (acc : Nat), acc ≤ l.foldl max acc ∧ ∀ x ∈ l, x ≤ l.foldl max acc
  | [], acc => ⟨le_refl _, by simp⟩
  | y :: l, acc => by
      obtain ⟨h1, h2⟩ := le_foldl_max l (max acc y)
      refine ⟨le_trans (le_max_left _ _) h1, ?_⟩
      intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact le_trans (le_max_right _ _) h1
      · exact h2 x hx

theorem viewSize_le_regroupFuel {recs : List RecR} {r : RecR} (h : r ∈ recs) :
    viewSize r.1 ≤ regroupFuel recs :=
  (le_foldl_max _ 0).2 _ (List.mem_map.2 ⟨r, h, rfl⟩)

theorem card_groupSum {gs : List (C × List (C × Nat))}
    (h2 : ∀ p ∈ gs, 2 ≤ Multiset.card (ofEntries p.2)) : gs.length ≤ Multiset.card (groupSum gs) := by
  induction gs with
  | nil => simp
  | cons p gs ih =>
      have := h2 p (List.mem_cons_self ..)
      have := ih (fun q hq => h2 q (List.mem_cons_of_mem _ hq))
      simp only [groupSum, List.map_cons, List.sum_cons, Multiset.card_add, List.length_cons] at *
      omega

/-- **Completeness of regrouped views, AC, laws-free.** Let `w₀` be a view of
the walk at node `n` and `gs` groups of its entries, each the children of an
`f`-member of its class `g` (not over `g` itself, at least two entries),
their sum within `w₀`, none all of `w₀`, at most `limit` of them. Then the view
`w₀ - Σ groups + Σ {g}` is enumerated, and its demand accepts every `taken`
holding each `g` and satisfying each leaf of `w₀`'s opening tree, where a
leaf class of a group counts as satisfied. -/
theorem regroup_view_complete_ac {ctx : Ctx} (hκ : ctx.κ = .ac) {dir : Dir} {limit : Nat}
    {n : Node} {r₀ : RecR} (h₀ : r₀ ∈ baseRecsR ctx dir Laws.free n)
    {gs : List (C × List (C × Nat))} (hgs : ∀ p ∈ gs, p ∈ groupsOf ctx)
    (hself : ∀ p ∈ gs, p.1 ∉ p.2.map Prod.fst)
    (h2 : ∀ p ∈ gs, 2 ≤ Multiset.card (ofEntries p.2)) (hle : groupSum gs ≤ ofEntries r₀.1)
    (hne : ∀ p ∈ gs, ofEntries p.2 ≠ ofEntries r₀.1)
    (hlim : gs.length ≤ limit) {taken : List C} (hneed : ∀ p ∈ gs, p.1 ∈ taken)
    (hleaf : ∀ l ∈ r₀.2.1, (mergeOnClose .ac = true ∧ l.1.X ∈ taken) ∨
      (∃ c ∈ l.1.g, c ∈ taken ∨ ∃ p ∈ gs, c ∈ p.2.map Prod.fst) ∨ l.2 = true) :
    ∃ w d, (w, d) ∈ enumerateR ctx dir Laws.free limit n ∧
      ofEntries w = ofEntries r₀.1 - groupSum gs + groupCls gs ∧ d.acceptsE .ac taken := by
  obtain ⟨v, -, hn, -, hneeds⟩ := mem_baseRecsR h₀
  rw [hκ] at hn
  have hcan := entries_ofEntries_of_canonical (normalize_ac_canonical hn)
  obtain ⟨r, hr, hof, hrn, φ, hφ, hrel⟩ := regroup_chain_ac (dir := dir) (limit := limit) hκ gs r₀
    hgs hself h2 hle hne hcan (by rw [hneeds]; simpa using hlim)
  have hfuel : gs.length ≤ regroupFuel (baseRecsR ctx dir Laws.free n) := by
    have h1 := card_groupSum h2
    have h3 := Multiset.card_le_card hle
    have h4 := viewSize_le_regroupFuel h₀
    rw [viewSize_eq_card] at h4
    omega
  have hmem : r ∈ regroupAll ctx dir Laws.free limit (regroupFuel (baseRecsR ctx dir Laws.free n))
      (baseRecsR ctx dir Laws.free n) :=
    (mem_regroupLevels_iff ctx dir Laws.free limit _ _ r).2
      ⟨r₀, h₀, regroupLevels_fuel_mono ctx dir Laws.free limit hfuel hr⟩
  have hok : ∀ l ∈ r.alt, l.okE .ac taken := by
    intro l hl
    rcases List.mem_append.1 hl with hl | hl
    · rw [hφ] at hl
      obtain ⟨l₀, hl₀, rfl⟩ := List.mem_map.1 hl
      obtain ⟨hX, hf, hsub, hp⟩ := hrel l₀
      rcases hleaf l₀ hl₀ with ⟨hm, hXt⟩ | ⟨c, hc, hct | ⟨p, hp', hcp⟩⟩ | hfl
      · exact Or.inl ⟨hm, hX ▸ hXt⟩
      · exact Or.inr (Or.inl ⟨c, hsub hc, hct⟩)
      · exact Or.inr (Or.inl ⟨p.1, hp p hp' ⟨c, hc, hcp⟩, hneed p hp'⟩)
      · exact Or.inr (Or.inr (hf ▸ hfl))
    · obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hl
      rw [needLeaf_okE]
      rcases hrn c hc with hc | hc
      · rw [hneeds] at hc; simp at hc
      · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hc
        exact hneed p hp
  obtain ⟨d, hd, hacc⟩ := (acceptsE_enumerateFromR (κ := .ac)).2 ⟨r, hmem, rfl, hok⟩
  exact ⟨r.1, d, hd, hof, hacc⟩

/-- **An AC atom matching through regrouped classes satisfies the regrouped
semantics** (laws-free operator). The atom's node `n` has a view `w₀` of
the walk; the binding matches the atom's shallow pattern on the multiset
`w₀ - Σ groups + Σ {g}`, its item classes hold each `g` and satisfy the
leaves of `w₀`'s opening tree through the groups. Then the atom holds under
`AtomSatG (Enumerator.regroup dir)`, so `regroup_plan_complete` emits the
binding. -/
theorem regroup_match_complete_ac {c : FCtx} {dir : Sym → Dir} {σ : Binding} {nv : Var}
    {f : Sym} {es : List (Var × Mult)} {rest : Option Var} {id : NodeId} {n : Node}
    (hnode : σ.node nv = some id) (hmem : (id, n) ∈ c.G.nodes)
    (hcls : σ.cls nv = some (c.G.find id)) (hop : n.op = f) (hlaws : c.laws f = Laws.free)
    {r₀ : RecR} (h₀ : r₀ ∈ baseRecsR (c.ctx f .ac) (dir f) Laws.free n)
    {gs : List (C × List (C × Nat))} (hgs : ∀ p ∈ gs, p ∈ groupsOf (c.ctx f .ac))
    (hself : ∀ p ∈ gs, p.1 ∉ p.2.map Prod.fst)
    (h2 : ∀ p ∈ gs, 2 ≤ Multiset.card (ofEntries p.2)) (hle : groupSum gs ≤ ofEntries r₀.1)
    (hne : ∀ p ∈ gs, ofEntries p.2 ≠ ofEntries r₀.1)
    (hlim : gs.length ≤ es.length) (hneed : ∀ p ∈ gs, p.1 ∈ takenOf σ (es.map Prod.fst))
    (hleaf : ∀ l ∈ r₀.2.1, (mergeOnClose .ac = true ∧ l.1.X ∈ takenOf σ (es.map Prod.fst)) ∨
      (∃ c ∈ l.1.g, c ∈ takenOf σ (es.map Prod.fst) ∨ ∃ p ∈ gs, c ∈ p.2.map Prod.fst) ∨
        l.2 = true)
    (hm : MatchN c.G (RAtom.shallow ⟨nv, f, .ac es rest⟩)
      ⟨f, .mset (ofEntries r₀.1 - groupSum gs + groupCls gs)⟩ σ) :
    AtomSatG (Enumerator.regroup dir) c σ ⟨nv, f, .ac es rest⟩ := by
  obtain ⟨w, d, hd, hof, hacc⟩ := regroup_view_complete_ac (ctx := c.ctx f .ac) rfl
    (limit := es.length) h₀ hgs hself h2 hle hne (by simpa using hlim) hneed hleaf
  unfold AtomSatG
  simp only [Shape.flatKind]
  refine ⟨id, n, hnode, hmem, hcls, hop, w, d, ?_, ?_, hacc⟩
  · show (w, d) ∈ enumerateR (c.ctx f .ac) (dir f) (c.laws f) (es.map Prod.fst).length n
    rw [hlaws, List.length_map]
    exact hd
  · simp only [ofView]
    rw [hof]
    exact hm

end Semper.EMatch.Flatten
