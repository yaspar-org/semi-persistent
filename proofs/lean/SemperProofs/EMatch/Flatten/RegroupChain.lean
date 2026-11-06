import SemperProofs.EMatch.Flatten.RegroupFits

/-!
# `:flatten`: chains of regroupings

A regrouped view may itself be regrouped: the engine (`FlattenScratch::regroup`)
regroups every view it finds, the regrouped ones included, until no group
fits. So a variable may bind a class `G2 ∋ f{G1, c}` where `G1 ∋ f{a, b}`
is a group of the view (nested groups), groups may together cover the whole
view, and for a fold `(a - b) - c` in `[a, b, c, d]` is a group only after
the prefix `[a, b]` is. This file states the matches regrouping reaches as
chains and proves the model finds exactly those, for a laws-free operator of
every kind and fold direction:

* `RegroupsTo κ dir w g grp w'`: one regrouping of the view `w` by the group
  `grp` of class `g`, declaratively: a sub-multiset (AC), a subset (ACI), a
  run on the spine (`:assoc`; a prefix of a left fold, a suffix of a right
  fold: `regroupsTo_left_iff`, `regroupsTo_right_iff`), of at least two
  entries, not the whole view;
* `RegroupStep ctx dir limit r r'`: one regrouping of a record by an
  `f`-member, the leaves gaining `g` (`addG`) and the needed classes losing
  those the group absorbs and gaining `g` (`needsAfter`), at most `limit`
  of them; `RegroupChain` is any finite chain of steps;
* `regroupStep_mem`, `regroupChain_mem_levels`: a declarative step is a
  regrouping of the model and makes the view strictly smaller, so a chain
  lies within the levels the model runs; `regroupStep_of_mem`,
  `regroupChain_of_mem_levels`: conversely;
* `regroup_view_complete`, `regroup_views_iff`: a view of `enumerateR`
  accepts `taken` iff a chain from a walk record reaches it with its leaves
  and needed classes satisfied;
* `regroup_match_complete`, `regroup_match_iff`: at the match level, an
  n-ary atom holds under `AtomSatG (Enumerator.regroup dir)` iff some chain
  reaches a view the atom's shallow pattern matches; `regroup_plan_complete`
  then emits the binding.

The per-item limit (`Demand::needs`) bounds the needed classes at every step
of the chain, as the engine checks it at every step: a chain whose last
record needs few classes but whose intermediate records need more is not
found (`regroup_nested_limit_counter`, `RegroupNested.lean`).
-/

namespace Semper.EMatch.Flatten

open Semper.EMatch

/-! ## Chains of regroupings, declaratively -/

/-- The view one regrouping by the group `grp` of class `g` turns `w` into,
for each kind, read declaratively:

* AC: `grp` is a sub-multiset of at least two entries of `w`, not all of
  `w`; the view becomes `w - grp + {g}`;
* ACI: `grp` is a set of at least two classes of `w`, not all of them; the
  view becomes the set `(w \ grp) ∪ {g}`, which holds at least two classes;
* `:assoc` and the folds: `grp` is a run of at least two entries of `w` at
  some position `p` on the spine of the fold direction (any run, a prefix
  for a left fold, a suffix for a right fold), not all of `w`; the run
  becomes the single entry `g`. -/
def RegroupsTo : FlatKind → Dir → List (C × Nat) → C → List (C × Nat) → List (C × Nat) → Prop
  | .ac, _, w, g, grp, w' =>
      2 ≤ Multiset.card (ofEntries grp) ∧ ofEntries grp ≤ ofEntries w ∧
        ofEntries grp ≠ ofEntries w ∧
        w' = Multiset.entries (ofEntries w - ofEntries grp + {g})
  | .aci, _, w, g, grp, w' =>
      2 ≤ (grp.map Prod.fst).toFinset.card ∧
        (grp.map Prod.fst).toFinset ⊆ (w.map Prod.fst).toFinset ∧
        (grp.map Prod.fst).toFinset ≠ (w.map Prod.fst).toFinset ∧
        2 ≤ (insert g ((w.map Prod.fst).toFinset \ (grp.map Prod.fst).toFinset)).card ∧
        w' = ((insert g ((w.map Prod.fst).toFinset \ (grp.map Prod.fst).toFinset)).sort
          (· ≤ ·)).map (fun c => (c, 1))
  | .assoc, dir, w, g, grp, w' =>
      ∃ p, 2 ≤ grp.length ∧ grp.length < w.length ∧ p + grp.length ≤ w.length ∧
        spineRun dir p grp.length w.length = true ∧
        ((w.drop p).take grp.length).map Prod.fst = grp.map Prod.fst ∧
        w' = w.take p ++ (g, 1) :: w.drop (p + grp.length)

/-- A regrouping of a left fold replaces a prefix. -/
theorem regroupsTo_left_iff {w : List (C × Nat)} {g : C} {grp w' : List (C × Nat)} :
    RegroupsTo .assoc .left w g grp w' ↔
      2 ≤ grp.length ∧ grp.length < w.length ∧
        (w.take grp.length).map Prod.fst = grp.map Prod.fst ∧ w' = (g, 1) :: w.drop grp.length := by
  constructor
  · rintro ⟨p, h2, hlt, -, hsp, hrun, rfl⟩
    simp only [spineRun, beq_iff_eq] at hsp
    subst hsp
    rw [List.drop_zero] at hrun
    exact ⟨h2, hlt, hrun, by simp⟩
  · rintro ⟨h2, hlt, hrun, rfl⟩
    exact ⟨0, h2, hlt, by omega, by simp [spineRun], by simpa using hrun, by simp⟩

/-- A regrouping of a right fold replaces a suffix. -/
theorem regroupsTo_right_iff {w : List (C × Nat)} {g : C} {grp w' : List (C × Nat)} :
    RegroupsTo .assoc .right w g grp w' ↔
      2 ≤ grp.length ∧ grp.length < w.length ∧
        (w.drop (w.length - grp.length)).map Prod.fst = grp.map Prod.fst ∧
        w' = w.take (w.length - grp.length) ++ [(g, 1)] := by
  constructor
  · rintro ⟨p, h2, hlt, hp, hsp, hrun, rfl⟩
    simp only [spineRun, beq_iff_eq] at hsp
    have hp' : p = w.length - grp.length := by omega
    subst hp'
    refine ⟨h2, hlt, ?_, ?_⟩
    · rw [List.take_of_length_le (by simp; omega)] at hrun; exact hrun
    · rw [hsp, List.drop_length]
  · rintro ⟨h2, hlt, hrun, rfl⟩
    refine ⟨w.length - grp.length, h2, hlt, by omega, by simp [spineRun]; omega, ?_, ?_⟩
    · rw [List.take_of_length_le (by simp; omega)]; exact hrun
    · have e : w.length - grp.length + grp.length = w.length := by omega
      rw [e, List.drop_length]

/-- **One regrouping of a record, declaratively.** An `f`-member of class `g`
whose children `grp` do not hold `g` regroups the record's view
(`RegroupsTo`); a leaf holding a class of the group also holds `g`
(`addG`); the classes the record needs taken lose those the group absorbs
and gain `g` (`needsAfter`), and there are at most `limit` of them. -/
inductive RegroupStep (ctx : Ctx) (dir : Dir) (limit : Nat) : RecR → RecR → Prop
  | mk {r : RecR} {id : NodeId} {m : Node} {g : C} {w' : List (C × Nat)} :
      ctx.IsMember id m g → g ∉ (kids ctx.κ m.children).map Prod.fst →
      RegroupsTo ctx.κ dir r.1 g (kids ctx.κ m.children) w' →
      (needsAfter g ((kids ctx.κ m.children).map Prod.fst) r.2.2).length ≤ limit →
      RegroupStep ctx dir limit r
        (w', r.2.1.map (addG g ((kids ctx.κ m.children).map Prod.fst)),
          needsAfter g ((kids ctx.κ m.children).map Prod.fst) r.2.2)

/-- A finite chain of regroupings, each fitting the view the previous ones
left, each within the per-item limit on needed classes. -/
def RegroupChain (ctx : Ctx) (dir : Dir) (limit : Nat) : RecR → RecR → Prop :=
  Relation.ReflTransGen (RegroupStep ctx dir limit)

/-- The views regrouping starts from and keeps: canonical multisets (AC),
canonical sets (ACI), positive counts (`:assoc`). -/
def ViewOK : FlatKind → List (C × Nat) → Prop
  | .ac, w => coalesce w = w
  | .aci, w => dedupAci w = w
  | .assoc, w => ∀ e ∈ w, 0 < e.2

/-! ## The walk's views are canonical -/

theorem kidsOfD_pos (opt : Bool → C → Nat → Finset C → List RawL)
    (hopt : ∀ b X k P, 0 < k → ∀ r ∈ opt b X k P, ∀ e ∈ r.1, 0 < e.2) (dir : Dir) (len : Nat) :
    ∀ (ks : List (C × Nat)) (i k : Nat) (P : Finset C), 0 < k → (∀ e ∈ ks, 0 < e.2) →
      ∀ r ∈ kidsOfD opt dir len ks i k P, ∀ e ∈ r.1, 0 < e.2
  | [], _, _, _, _, _, r, hr => by
      simp only [kidsOfD, List.mem_singleton] at hr; subst hr; simp
  | (X, j) :: rest, i, k, P, hk, hks, r, hr => by
      simp only [kidsOfD] at hr
      obtain ⟨r₁, h₁, hr⟩ := List.mem_flatMap.1 hr
      obtain ⟨r₂, h₂, rfl⟩ := List.mem_map.1 hr
      intro e he
      rcases List.mem_append.1 he with he | he
      · exact hopt _ _ _ _ (Nat.mul_pos hk (hks (X, j) (List.mem_cons_self ..))) r₁ h₁ e he
      · exact kidsOfD_pos opt hopt dir len rest (i + 1) k P hk
          (fun e he => hks e (List.mem_cons_of_mem _ he)) r₂ h₂ e he

theorem rawOptD_pos (ctx : Ctx) (dir : Dir) :
    ∀ (fuel : Nat) (b : Bool) (X : C) (k : Nat) (P : Finset C), 0 < k →
      ∀ r ∈ rawOptD ctx dir fuel b X k P, ∀ e ∈ r.1, 0 < e.2
  | 0, b, X, k, P, hk, r, hr => by
      simp only [rawOptD, List.mem_singleton] at hr; subst hr; simpa using hk
  | fuel + 1, b, X, k, P, hk, r, hr => by
      simp only [rawOptD, List.mem_cons] at hr
      rcases hr with rfl | hr
      · simpa using hk
      · split at hr
        · simp at hr
        · obtain ⟨p, -, hr⟩ := List.mem_flatMap.1 hr
          obtain ⟨r', hr', rfl⟩ := List.mem_map.1 hr
          exact kidsOfD_pos _ (fun b X k P hk => rawOptD_pos ctx dir fuel b X k P hk) dir _ _ 0 k
            _ hk (kids_pos _ _) r' hr'

theorem mem_baseRecsR_raw {ctx : Ctx} {dir : Dir} {laws : Laws} {n : Node} {r : RecR}
    (h : r ∈ baseRecsR ctx dir laws n) :
    ∃ raw ∈ rawNodeD ctx dir (fuelOf ctx.G) n 1 ∅, normalize ctx.κ laws raw.1 = .node r.1 ∧
      r.2.2 = [] := by
  unfold baseRecsR at h
  obtain ⟨r', hr', rfl⟩ := List.mem_map.1 h
  unfold rawRecordsLD at hr'
  obtain ⟨raw, hraw, he⟩ := List.mem_filterMap.1 hr'
  revert he
  cases hn : normalize ctx.κ laws raw.1 with
  | node w =>
      intro he
      simp only [Option.some.injEq] at he
      subst he
      exact ⟨raw, hraw, hn, rfl⟩
  | _ => simp

theorem coalesce_coalesce (v : List (C × Nat)) : coalesce (coalesce v) = coalesce v := by
  unfold coalesce
  rw [ofEntries_entries]

theorem dedupAci_dedupAci (v : List (C × Nat)) : dedupAci (dedupAci v) = dedupAci v := by
  have h := map_fst_dedupAci v
  unfold dedupAci at h ⊢
  rw [h, Finset.sort_toFinset]

/-- The walk's records of a laws-free operator have canonical views. -/
theorem viewOK_base {ctx : Ctx} {dir : Dir} {n : Node} {r : RecR}
    (h : r ∈ baseRecsR ctx dir Laws.free n) : ViewOK ctx.κ r.1 := by
  obtain ⟨raw, hraw, hn, -⟩ := mem_baseRecsR_raw h
  obtain ⟨hw, -, -⟩ := normalize_free_node.1 hn
  cases hκ : ctx.κ <;> rw [hκ] at hw <;> simp only [ViewOK, canonK] at hw ⊢ <;> rw [hw]
  · exact kidsOfD_pos _ (fun b X k P hk => rawOptD_pos ctx dir _ b X k P hk) dir _ _ 0 1 ∅
        Nat.one_pos (kids_pos _ _) raw hraw
  · exact coalesce_coalesce raw.1
  · exact dedupAci_dedupAci raw.1

/-! ## The stored view is a walk record -/

theorem kidsOfD_kept (opt : Bool → C → Nat → Finset C → List RawL)
    (hopt : ∀ b X k P, ([(X, k)], []) ∈ opt b X k P) (dir : Dir) (len : Nat) :
    ∀ (ks : List (C × Nat)) (i k : Nat) (P : Finset C),
      (scale k ks, ([] : List LeafL)) ∈ kidsOfD opt dir len ks i k P
  | [], _, _, _ => by simp [kidsOfD, scale]
  | (X, j) :: rest, i, k, P => by
      simp only [kidsOfD]
      refine List.mem_flatMap.2 ⟨_, hopt _ X (k * j) P, List.mem_map.2
        ⟨_, kidsOfD_kept opt hopt dir len rest (i + 1) k P, ?_⟩⟩
      simp [scale]

theorem rawOptD_kept (ctx : Ctx) (dir : Dir) :
    ∀ (fuel : Nat) (b : Bool) (X : C) (k : Nat) (P : Finset C),
      ([(X, k)], ([] : List LeafL)) ∈ rawOptD ctx dir fuel b X k P
  | 0, _, _, _, _ => by simp [rawOptD]
  | _ + 1, _, _, _, _ => by simp [rawOptD]

/-- The node's stored view, every child kept, normalized, is a walk record
with no leaf and no need. -/
theorem kept_mem_baseRecsR {ctx : Ctx} {dir : Dir} {laws : Laws} {n : Node}
    {w : List (C × Nat)} (h : normalize ctx.κ laws (scale 1 (kids ctx.κ n.children)) = .node w) :
    (w, [], []) ∈ baseRecsR ctx dir laws n := by
  unfold baseRecsR rawRecordsLD
  refine List.mem_map.2 ⟨(w, []), List.mem_filterMap.2 ⟨(scale 1 (kids ctx.κ n.children), []),
    kidsOfD_kept _ (rawOptD_kept ctx dir _) dir _ _ 0 1 ∅, ?_⟩, rfl⟩
  simp only [h]
  rfl

/-! ## One declarative step is one regrouping of the model -/

theorem viewSize_append (a b : List (C × Nat)) : viewSize (a ++ b) = viewSize a + viewSize b := by
  simp [viewSize]

theorem viewSize_ones {w : List (C × Nat)} (h : ∀ e ∈ w, e.2 = 1) : viewSize w = w.length := by
  induction w with
  | nil => rfl
  | cons e w ih =>
      simp only [viewSize, List.map_cons, List.sum_cons, List.length_cons] at ih ⊢
      rw [h e (List.mem_cons_self ..), ih (fun e he => h e (List.mem_cons_of_mem _ he))]
      omega

theorem viewSize_entries (m : Multiset C) : viewSize (Multiset.entries m) = Multiset.card m := by
  rw [viewSize_eq_card, ofEntries_entries]

theorem viewSize_pos_ge {w : List (C × Nat)} (h : ∀ e ∈ w, 0 < e.2) : w.length ≤ viewSize w := by
  induction w with
  | nil => simp
  | cons e w ih =>
      simp only [viewSize, List.map_cons, List.sum_cons, List.length_cons] at ih ⊢
      have := h e (List.mem_cons_self ..)
      have := ih (fun e he => h e (List.mem_cons_of_mem _ he))
      omega

/-- The AC step. -/
theorem regroupStep_ac {ctx : Ctx} (hκ : ctx.κ = .ac) {dir : Dir} {limit : Nat} {r : RecR}
    {g : C} {grp w' : List (C × Nat)} (hgg : (g, grp) ∈ groupsOf ctx)
    (hg : g ∉ grp.map Prod.fst) (hok : ViewOK .ac r.1) (h : RegroupsTo .ac dir r.1 g grp w')
    (hle : (needsAfter g (grp.map Prod.fst) r.2.2).length ≤ limit) :
    (w', r.2.1.map (addG g (grp.map Prod.fst)), needsAfter g (grp.map Prod.fst) r.2.2) ∈
        regroupRec ctx dir Laws.free limit r ∧
      ViewOK .ac w' ∧ viewSize w' < viewSize r.1 := by
  obtain ⟨h2, hsub, hne, rfl⟩ := h
  simp only [ViewOK] at hok
  have hnd : (r.1.map Prod.fst).Nodup := by
    have := (coalesce_canonical r.1).nodup; rwa [hok] at this
  obtain ⟨v, hfit, hsum⟩ := fitsR_ac_complete (dir := dir) hnd hg hsub hne h2
  have hv0 : ofEntries v ≠ 0 := by
    intro h0; rw [h0, zero_add] at hsum; exact hne hsum
  have hcard : 2 ≤ Multiset.card (ofEntries (v ++ [(g, 1)])) := by
    rw [ofEntries_append]
    simp only [Multiset.card_add]
    have : 1 ≤ Multiset.card (ofEntries v) := Multiset.card_pos.2 hv0
    have h1 : Multiset.card (ofEntries [(g, 1)]) = 1 := by simp [ofEntries]
    omega
  have hv : ofEntries v = ofEntries r.1 - ofEntries grp := eq_tsub_of_add_eq hsum
  have hw : coalesce (v ++ [(g, 1)]) = Multiset.entries (ofEntries r.1 - ofEntries grp + {g}) := by
    unfold coalesce
    rw [ofEntries_append, hv]
    congr 2
  have hn : normalize ctx.κ Laws.free (v ++ [(g, 1)]) =
      .node (Multiset.entries (ofEntries r.1 - ofEntries grp + {g})) := by
    rw [hκ, normalize_free_ac_node hcard, hw]
  refine ⟨regroupRec_of hgg (hκ ▸ hfit) hn hle, ?_, ?_⟩
  · simp only [ViewOK]; unfold coalesce; rw [ofEntries_entries]
  · rw [viewSize_entries, viewSize_eq_card, Multiset.card_add, Multiset.card_singleton,
      Multiset.card_sub hsub]
    have := Multiset.card_le_card hsub
    omega

theorem ones_of_dedupAci {w : List (C × Nat)} (h : dedupAci w = w) :
    (w.map Prod.fst).Pairwise (· < ·) ∧ ∀ e ∈ w, e.2 = 1 := by
  rw [← h]; exact dedupAci_spec w

theorem val_toFinset_of_nodup {l : List C} (h : l.Nodup) : l.toFinset.val = (l : Multiset C) := by
  rw [List.toFinset_val, List.dedup_eq_self.2 h]

/-- The regrouped raw view of a canonical set view, deduplicated: the set
`(w \ grp) ∪ {g}`. -/
theorem dedupAci_regrouped {w grp v : List (C × Nat)} {g : C} (hok : dedupAci w = w)
    (hs : subEntries w (dedupAci grp) = some v) :
    dedupAci (v ++ [(g, 1)]) = ((insert g ((w.map Prod.fst).toFinset \
      (grp.map Prod.fst).toFinset)).sort (· ≤ ·)).map (fun c => (c, 1)) := by
  have hcan := ones_of_dedupAci hok
  have hnd : (w.map Prod.fst).Nodup := hcan.1.imp (fun h => Nat.ne_of_lt h)
  have hsum := subEntries_spec _ _ _ hnd hs
  have hvpos := subEntries_pos _ _ _ hs
  have hSval : ofEntries w = (w.map Prod.fst).toFinset.val := by
    rw [ofEntries_of_ones hcan.2, val_toFinset_of_nodup hnd]
  have hGval : ofEntries (dedupAci grp) = (grp.map Prod.fst).toFinset.val := by
    rw [ofEntries_of_ones (dedupAci_ones grp), map_fst_dedupAci, Finset.sort_eq]
  have hvset : (v.map Prod.fst).toFinset =
      (w.map Prod.fst).toFinset \ (grp.map Prod.fst).toFinset := by
    rw [← toFinset_ofEntries_of_pos hvpos, eq_tsub_of_add_eq hsum, hSval, hGval,
      ← Finset.sdiff_val]
    exact Finset.val_toFinset _
  have hraw : (((v ++ [(g, 1)]).map Prod.fst).toFinset) =
      insert g ((w.map Prod.fst).toFinset \ (grp.map Prod.fst).toFinset) := by
    rw [List.map_append, List.toFinset_append, hvset]
    ext c; simp
  unfold dedupAci; rw [hraw]

/-- The ACI step. -/
theorem regroupStep_aci {ctx : Ctx} (hκ : ctx.κ = .aci) {dir : Dir} {limit : Nat} {r : RecR}
    {g : C} {grp w' : List (C × Nat)} (hgg : (g, grp) ∈ groupsOf ctx)
    (hg : g ∉ grp.map Prod.fst) (hok : ViewOK .aci r.1) (h : RegroupsTo .aci dir r.1 g grp w')
    (hle : (needsAfter g (grp.map Prod.fst) r.2.2).length ≤ limit) :
    (w', r.2.1.map (addG g (grp.map Prod.fst)), needsAfter g (grp.map Prod.fst) r.2.2) ∈
        regroupRec ctx dir Laws.free limit r ∧
      ViewOK .aci w' ∧ viewSize w' < viewSize r.1 := by
  obtain ⟨h2, hsub, hne, hF, rfl⟩ := h
  simp only [ViewOK] at hok
  set S := (r.1.map Prod.fst).toFinset with hS
  set G := (grp.map Prod.fst).toFinset with hG
  have hcan := ones_of_dedupAci hok
  have hnd : (r.1.map Prod.fst).Nodup := hcan.1.imp (fun h => Nat.ne_of_lt h)
  obtain ⟨v, hfit, hsum⟩ := fitsR_aci_complete (dir := dir) hcan hg
    (fun c hc => List.mem_toFinset.1 (hsub (List.mem_toFinset.2 hc))) hne h2
  obtain ⟨-, v', hs', he'⟩ := fitsR_aci hfit
  have hvv : v = v' := List.append_cancel_right he'
  subst hvv
  have hd : dedupAci (v ++ [(g, 1)]) =
      ((insert g (S \ G)).sort (· ≤ ·)).map (fun c => (c, 1)) := dedupAci_regrouped hok hs'
  have hlen : ((insert g (S \ G)).sort (· ≤ ·)).length = (insert g (S \ G)).card :=
    Finset.length_sort _
  have hn : normalize ctx.κ Laws.free (v ++ [(g, 1)]) =
      .node (((insert g (S \ G)).sort (· ≤ ·)).map (fun c => (c, 1))) := by
    rw [hκ, normalize_free_node]
    refine ⟨hd.symm, ?_, ?_⟩
    · intro h0
      have := congrArg List.length h0
      simp only [List.length_map, hlen, List.length_nil] at this
      omega
    · intro c h0
      have := congrArg List.length h0
      simp only [List.length_map, hlen, List.length_singleton] at this
      omega
  refine ⟨regroupRec_of hgg (hκ ▸ hfit) hn hle, ?_, ?_⟩
  · simp only [ViewOK]
    rw [← hd, dedupAci_dedupAci]
  · rw [viewSize_ones (fun e he => by
        obtain ⟨_, -, rfl⟩ := List.mem_map.1 he; rfl), List.length_map, hlen,
      viewSize_ones hcan.2]
    have h1 := Finset.card_insert_le g (S \ G)
    have h2' := Finset.card_sdiff_add_card_eq_card hsub
    have h3 : S.card = r.1.length := by
      rw [hS, List.toFinset_card_of_nodup hnd, List.length_map]
    omega

/-- The `:assoc` step, every fold direction. -/
theorem regroupStep_assoc {ctx : Ctx} (hκ : ctx.κ = .assoc) {dir : Dir} {limit : Nat} {r : RecR}
    {g : C} {grp w' : List (C × Nat)} (hgg : (g, grp) ∈ groupsOf ctx)
    (hg : g ∉ grp.map Prod.fst) (hok : ViewOK .assoc r.1) (h : RegroupsTo .assoc dir r.1 g grp w')
    (hle : (needsAfter g (grp.map Prod.fst) r.2.2).length ≤ limit) :
    (w', r.2.1.map (addG g (grp.map Prod.fst)), needsAfter g (grp.map Prod.fst) r.2.2) ∈
        regroupRec ctx dir Laws.free limit r ∧
      ViewOK .assoc w' ∧ viewSize w' < viewSize r.1 := by
  obtain ⟨p, h2, hlt, hp, hsp, hrun, rfl⟩ := h
  simp only [ViewOK] at hok
  have hfit := fitsR_assoc_complete hg h2 hlt hp hsp hrun
  have hn : normalize ctx.κ Laws.free (r.1.take p ++ (g, 1) :: r.1.drop (p + grp.length)) =
      .node (r.1.take p ++ (g, 1) :: r.1.drop (p + grp.length)) := by
    rw [hκ, normalize_free_node]
    refine ⟨rfl, by simp, ?_⟩
    intro c h0
    have := congrArg List.length h0
    simp only [List.length_append, List.length_take, List.length_cons, List.length_drop,
      List.length_nil] at this
    omega
  refine ⟨regroupRec_of hgg (hκ ▸ hfit) hn hle, ?_, ?_⟩
  · simp only [ViewOK]
    intro e he
    rcases List.mem_append.1 he with he | he
    · exact hok e (List.mem_of_mem_take he)
    · rcases List.mem_cons.1 he with rfl | he
      · exact Nat.one_pos
      · exact hok e (List.mem_of_mem_drop he)
  · have hrunpos : ∀ e ∈ (r.1.drop p).take grp.length, 0 < e.2 :=
      fun e he => hok e (List.mem_of_mem_drop (List.mem_of_mem_take he))
    have hrunlen : ((r.1.drop p).take grp.length).length = grp.length := by
      simp only [List.length_take, List.length_drop]; omega
    have h3 := viewSize_pos_ge hrunpos
    have e1 : r.1 = r.1.take p ++ ((r.1.drop p).take grp.length ++ r.1.drop (p + grp.length)) := by
      conv_lhs => rw [← List.take_append_drop p r.1,
        ← List.take_append_drop grp.length (r.1.drop p), List.drop_drop]
    have hr : viewSize r.1 = viewSize (r.1.take p) + (viewSize ((r.1.drop p).take grp.length) +
        viewSize (r.1.drop (p + grp.length))) := by
      have := congrArg viewSize e1
      rw [this, viewSize_append, viewSize_append]
    have hl : viewSize (r.1.take p ++ (g, 1) :: r.1.drop (p + grp.length)) =
        viewSize (r.1.take p) + (1 + viewSize (r.1.drop (p + grp.length))) := by
      rw [viewSize_append]; simp [viewSize]
    rw [hl, hr]
    omega

/-- **One declarative step is one regrouping of the model**, laws-free, every
kind and fold direction: the record is among `regroupRec`'s, its view is
canonical again, and it is strictly smaller. -/
theorem regroupStep_mem {ctx : Ctx} {dir : Dir} {limit : Nat} {r r' : RecR}
    (hok : ViewOK ctx.κ r.1) (h : RegroupStep ctx dir limit r r') :
    r' ∈ regroupRec ctx dir Laws.free limit r ∧ ViewOK ctx.κ r'.1 ∧ viewSize r'.1 < viewSize r.1 := by
  obtain ⟨hm, hg, hto, hle⟩ := h
  have hgg := mem_groupsOf_of_member hm
  generalize kids ctx.κ _ = grp at hgg hg hto hle ⊢
  cases hκ : ctx.κ <;> rw [hκ] at hok hto <;> dsimp only
  · exact regroupStep_assoc hκ hgg hg hok hto hle
  · exact regroupStep_ac hκ hgg hg hok hto hle
  · exact regroupStep_aci hκ hgg hg hok hto hle

/-- A chain of declarative steps from a canonical record lies within as many
levels of the model's regrouping as the record's view has entries. -/
theorem regroupChain_mem_levels {ctx : Ctx} {dir : Dir} {limit : Nat} {r₀ r : RecR}
    (hok : ViewOK ctx.κ r₀.1) (h : RegroupChain ctx dir limit r₀ r) :
    r ∈ regroupLevels ctx dir Laws.free limit (viewSize r₀.1) [r₀] := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact mem_regroupLevels_of_mem ctx dir Laws.free limit _ (List.mem_singleton_self _)
  | head hs _ ih =>
      obtain ⟨h1, hok', hlt⟩ := regroupStep_mem hok hs
      have := mem_regroupLevels_succ h1 (ih hok')
      exact regroupLevels_fuel_mono ctx dir Laws.free limit (by omega) this

/-! ## Completeness -/

/-- **Completeness of regrouped views, chains.** For a laws-free operator of
any kind and fold direction: the view a chain of regroupings reaches from a
walk record is enumerated, and its demand accepts every `taken` that takes
the classes the chain's record still needs and satisfies its leaves. -/
theorem regroup_view_complete {ctx : Ctx} {dir : Dir} {limit : Nat} {n : Node} {r₀ r : RecR}
    (h₀ : r₀ ∈ baseRecsR ctx dir Laws.free n) (hch : RegroupChain ctx dir limit r₀ r)
    {taken : List C} (hacc : ∀ l ∈ r.alt, l.okE ctx.κ taken) :
    ∃ d, (r.1, d) ∈ enumerateR ctx dir Laws.free limit n ∧ d.acceptsE ctx.κ taken := by
  have hlev := regroupChain_mem_levels (viewOK_base h₀) hch
  have hmem : r ∈ regroupAll ctx dir Laws.free limit (regroupFuel (baseRecsR ctx dir Laws.free n))
      (baseRecsR ctx dir Laws.free n) :=
    (mem_regroupLevels_iff ctx dir Laws.free limit _ _ r).2
      ⟨r₀, h₀, regroupLevels_fuel_mono ctx dir Laws.free limit (viewSize_le_regroupFuel h₀) hlev⟩
  exact (acceptsE_enumerateFromR (κ := ctx.κ)).2 ⟨r, hmem, rfl, hacc⟩

/-- **Completeness of regrouped views at the match level, chains.** An n-ary
atom of any kind over a laws-free operator, any fold direction: if a chain
of regroupings, each within the atom's per-item limit, takes a walk record
of the atom's node to a record on whose view the binding matches the atom's
shallow pattern, and the item classes take the classes the record still
needs and satisfy its leaves, the atom holds under
`AtomSatG (Enumerator.regroup dir)`; `regroup_plan_complete` then emits the
binding. -/
theorem regroup_match_complete {c : FCtx} {dir : Sym → Dir} {σ : Binding} {a : RAtom}
    {κ : FlatKind} (hκ : a.shape.flatKind = some κ) {id : NodeId} {n : Node}
    (hnode : σ.node a.node = some id) (hmem : (id, n) ∈ c.G.nodes)
    (hcls : σ.cls a.node = some (c.G.find id)) (hop : n.op = a.op)
    (hlaws : c.laws a.op = Laws.free) {r₀ r : RecR}
    (h₀ : r₀ ∈ baseRecsR (c.ctx a.op κ) (dir a.op) Laws.free n)
    (hch : RegroupChain (c.ctx a.op κ) (dir a.op) a.elems.length r₀ r)
    (hacc : ∀ l ∈ r.alt, l.okE κ (takenOf σ a.elems))
    (hm : MatchN c.G a.shallow ⟨a.op, ofView κ r.1⟩ σ) :
    AtomSatG (Enumerator.regroup dir) c σ a := by
  obtain ⟨d, hd, hd'⟩ := regroup_view_complete (taken := takenOf σ a.elems) h₀ hch hacc
  unfold AtomSatG
  rw [hκ]
  refine ⟨id, n, hnode, hmem, hcls, hop, r.1, d, ?_, hm, hd'⟩
  show (r.1, d) ∈ enumerateR (c.ctx a.op κ) (dir a.op) (c.laws a.op) a.elems.length n
  rw [hlaws]
  exact hd

/-! ## Every regrouping of the model is a declarative step -/

theorem fitsR_not_mem {κ : FlatKind} {dir : Dir} {view : List (C × Nat)} {g : C}
    {grp raw : List (C × Nat)} (h : raw ∈ fitsR κ dir view g grp) : g ∉ grp.map Prod.fst := by
  unfold fitsR at h
  split at h
  · simp at h
  · rename_i hg
    intro hm
    apply hg
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hm
    exact List.any_eq_true.2 ⟨e, he, by simp⟩

/-- The multiset arm of `fits`, unfolded: the group has two entries, is not
the view, and is subtracted from it. -/
theorem fitsR_ms {κ : FlatKind} (hκ : κ ≠ .assoc) {dir : Dir} {view : List (C × Nat)} {g : C}
    {grp raw : List (C × Nat)} (h : raw ∈ fitsR κ dir view g grp) :
    (decide (2 ≤ (groupNorm κ grp).length) ||
        ((groupNorm κ grp).head?.map (fun e => decide (1 < e.2))).getD false) = true ∧
      groupNorm κ grp ≠ view ∧
      ∃ v, subEntries view (groupNorm κ grp) = some v ∧ raw = v ++ [(g, 1)] := by
  unfold fitsR at h
  split at h
  · simp at h
  · cases κ with
    | assoc => exact absurd rfl hκ
    | ac | aci =>
      simp only at h
      split at h
      · simp at h
      · rename_i htwo
        simp only [Bool.not_or, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true',
          beq_iff_eq, not_or, not_and, Bool.not_eq_false] at htwo
        revert h
        cases hs : subEntries view (groupNorm _ grp) with
        | none => simp
        | some v =>
            intro h
            simp only [List.mem_singleton] at h
            refine ⟨?_, htwo.2, v, rfl, h⟩
            cases hA : decide (2 ≤ (groupNorm _ grp).length)
            · simp [htwo.1 hA]
            · simp

theorem le_viewSize {l : List (C × Nat)} {e : C × Nat} (h : e ∈ l) : e.2 ≤ viewSize l := by
  induction l with
  | nil => simp at h
  | cons x l ih =>
      simp only [viewSize, List.map_cons, List.sum_cons] at ih ⊢
      rcases List.mem_cons.1 h with rfl | h
      · omega
      · have := ih h; omega

/-- A canonical AC group that `fits` reads as two entries has at least two
elements. -/
theorem two_card_ac {grp : List (C × Nat)}
    (h : (decide (2 ≤ (coalesce grp).length) ||
        ((coalesce grp).head?.map (fun e => decide (1 < e.2))).getD false) = true) :
    2 ≤ Multiset.card (ofEntries grp) := by
  have hc : Multiset.card (ofEntries grp) = viewSize (coalesce grp) := by
    rw [viewSize_eq_card, ofEntries_coalesce]
  rw [hc]
  rcases Bool.or_eq_true_iff.1 h with h | h
  · have := viewSize_pos_ge (coalesce_canonical grp).2
    simp only [decide_eq_true_eq] at h
    omega
  · cases hh : (coalesce grp).head? with
    | none => rw [hh] at h; simp at h
    | some e =>
        rw [hh] at h
        simp only [Option.map_some, Option.getD_some, decide_eq_true_eq] at h
        have := le_viewSize (List.mem_of_mem_head? hh)
        omega

theorem regroupsTo_of_fitsR {κ : FlatKind} {dir : Dir} {view : List (C × Nat)} {g : C}
    {grp raw w' : List (C × Nat)} (hok : ViewOK κ view) (h : raw ∈ fitsR κ dir view g grp)
    (hn : normalize κ Laws.free raw = .node w') : RegroupsTo κ dir view g grp w' := by
  cases κ with
  | ac =>
      obtain ⟨htwo, hne, v, hs, rfl⟩ := fitsR_ms (by decide) h
      simp only [ViewOK] at hok
      simp only [groupNorm] at htwo hne hs
      have hnd : (view.map Prod.fst).Nodup := by
        have := (coalesce_canonical view).nodup; rwa [hok] at this
      have hsum := subEntries_spec _ _ _ hnd hs
      rw [ofEntries_coalesce] at hsum
      refine ⟨two_card_ac htwo, hsum ▸ Multiset.le_add_left _ _, ?_, ?_⟩
      · intro he
        apply hne
        rw [← hok]
        unfold coalesce
        rw [he]
      · rw [normalize_free_ac hn]
        unfold coalesce
        rw [ofEntries_append, eq_tsub_of_add_eq hsum]
        congr 2
  | aci =>
      obtain ⟨htwo, hne, v, hs, rfl⟩ := fitsR_ms (by decide) h
      simp only [ViewOK] at hok
      simp only [groupNorm] at htwo hne hs
      have hcan := ones_of_dedupAci hok
      have hnd : (view.map Prod.fst).Nodup := hcan.1.imp (fun h => Nat.ne_of_lt h)
      have hsum := subEntries_spec _ _ _ hnd hs
      have hd := dedupAci_regrouped (g := g) hok hs
      obtain ⟨hw, h0, h1⟩ := normalize_free_node.1 hn
      simp only [canonK] at hw
      rw [hd] at hw
      subst hw
      have hlen : (dedupAci grp).length = (grp.map Prod.fst).toFinset.card := by
        simp [dedupAci]
      refine ⟨?_, ?_, ?_, ?_, rfl⟩
      · rw [← hlen]
        rcases Bool.or_eq_true_iff.1 htwo with h | h
        · exact of_decide_eq_true h
        · cases hh : (dedupAci grp).head? with
          | none => rw [hh] at h; simp at h
          | some e =>
              rw [hh] at h
              simp only [Option.map_some, Option.getD_some, decide_eq_true_eq] at h
              rw [dedupAci_ones grp e (List.mem_of_mem_head? hh)] at h
              omega
      · intro c hc
        have hc' : c ∈ ofEntries view := by
          rw [← hsum]
          refine Multiset.mem_add.2 (Or.inr ?_)
          rw [ofEntries_of_ones (dedupAci_ones grp), map_fst_dedupAci]
          simpa using hc
        obtain ⟨e, he, rfl, -⟩ := mem_ofEntries.1 hc'
        exact List.mem_toFinset.2 (List.mem_map_of_mem he)
      · intro he
        apply hne
        rw [← hok]
        unfold dedupAci
        rw [he]
      · by_contra hlt
        rw [Nat.not_le] at hlt
        interval_cases hc : (insert g ((view.map Prod.fst).toFinset \
            (grp.map Prod.fst).toFinset)).card
        · simp at hc
        · obtain ⟨c, hc1⟩ := Finset.card_eq_one.1 hc
          apply h1 c
          rw [hc1]
          simp
  | assoc =>
      have hg := fitsR_not_mem h
      obtain ⟨h2, hlt, p, hsp, hrun, rfl⟩ := fitsR_assoc h
      have hp : p + grp.length ≤ view.length := by
        have := congrArg List.length hrun
        simp only [List.length_map, List.length_take, List.length_drop] at this
        omega
      exact ⟨p, h2, hlt, hp, hsp, hrun, normalize_free_assoc hn⟩

/-- **Every regrouping of the model is a declarative step**, laws-free, from a
canonical view. -/
theorem regroupStep_of_mem {ctx : Ctx} {dir : Dir} {limit : Nat} {r r' : RecR}
    (hok : ViewOK ctx.κ r.1) (h : r' ∈ regroupRec ctx dir Laws.free limit r) :
    RegroupStep ctx dir limit r r' := by
  obtain ⟨g, grp, raw, hgg, hraw, hn, hl, hneeds, hle⟩ := mem_regroupRec h
  obtain ⟨id, m, hm, rfl⟩ := mem_groupsOf hgg
  obtain ⟨w', ls', ns'⟩ := r'
  simp only at hl hneeds hle hn
  subst hl hneeds
  exact RegroupStep.mk hm (fitsR_not_mem hraw) (regroupsTo_of_fitsR hok hraw hn) hle

/-- A record of the model's levels from a canonical record is reached by a
chain of declarative steps. -/
theorem regroupChain_of_mem_levels {ctx : Ctx} {dir : Dir} {limit : Nat} :
    ∀ (F : Nat) {r₀ r : RecR}, ViewOK ctx.κ r₀.1 →
      r ∈ regroupLevels ctx dir Laws.free limit F [r₀] → RegroupChain ctx dir limit r₀ r
  | 0, r₀, r, _, h => by
      simp only [regroupLevels, List.mem_singleton] at h
      subst h; exact Relation.ReflTransGen.refl
  | F + 1, r₀, r, hok, h => by
      simp only [regroupLevels, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        List.mem_append, List.mem_singleton] at h
      rcases h with rfl | h
      · exact Relation.ReflTransGen.refl
      · obtain ⟨r₁, h₁, h⟩ := (mem_regroupLevels_iff ctx dir Laws.free limit F _ r).1 h
        have h₁' := mem_dedupH.1 h₁
        have hs := regroupStep_of_mem hok h₁'
        exact Relation.ReflTransGen.head hs
          (regroupChain_of_mem_levels F (regroupStep_mem hok hs).2.1 h)

/-- **The regrouped views are exactly the chains' views**, laws-free, every
kind and fold direction: a view of `enumerateR` accepts `taken` iff a chain
of regroupings within the limit takes a walk record to a record of that
view whose leaves and needed classes `taken` satisfies. -/
theorem regroup_views_iff {ctx : Ctx} {dir : Dir} {limit : Nat} {n : Node}
    {w : List (C × Nat)} {taken : List C} :
    (∃ d, (w, d) ∈ enumerateR ctx dir Laws.free limit n ∧ d.acceptsE ctx.κ taken) ↔
      ∃ r₀ ∈ baseRecsR ctx dir Laws.free n, ∃ r, RegroupChain ctx dir limit r₀ r ∧ r.1 = w ∧
        ∀ l ∈ r.alt, l.okE ctx.κ taken := by
  constructor
  · intro h
    unfold enumerateR regroupAll at h
    obtain ⟨r, hr, hw, hacc⟩ := (acceptsE_enumerateFromR (κ := ctx.κ)).1 h
    obtain ⟨r₀, h₀, hr⟩ := (mem_regroupLevels_iff ctx dir Laws.free limit _ _ r).1 hr
    exact ⟨r₀, h₀, r, regroupChain_of_mem_levels _ (viewOK_base h₀) hr, hw, hacc⟩
  · rintro ⟨r₀, h₀, r, hch, rfl, hacc⟩
    exact regroup_view_complete h₀ hch hacc

/-- **The matches of regrouped views, characterized.** For an n-ary atom over a
laws-free operator, any kind and fold direction, the atom holds under
`AtomSatG (Enumerator.regroup dir)` iff some chain of regroupings, each
within the atom's per-item limit, takes a walk record of a stored node of
the atom's class to a record on whose view the binding matches the shallow
pattern, with the item classes satisfying the record's leaves and taking the
classes it still needs. -/
theorem regroup_match_iff {c : FCtx} {dir : Sym → Dir} {σ : Binding} {a : RAtom}
    {κ : FlatKind} (hκ : a.shape.flatKind = some κ) (hlaws : c.laws a.op = Laws.free) :
    AtomSatG (Enumerator.regroup dir) c σ a ↔
      ∃ id n, σ.node a.node = some id ∧ (id, n) ∈ c.G.nodes ∧
        σ.cls a.node = some (c.G.find id) ∧ n.op = a.op ∧
        ∃ r₀ ∈ baseRecsR (c.ctx a.op κ) (dir a.op) Laws.free n, ∃ r,
          RegroupChain (c.ctx a.op κ) (dir a.op) a.elems.length r₀ r ∧
          MatchN c.G a.shallow ⟨a.op, ofView κ r.1⟩ σ ∧
          ∀ l ∈ r.alt, l.okE κ (takenOf σ a.elems) := by
  constructor
  · intro h
    unfold AtomSatG at h
    rw [hκ] at h
    obtain ⟨id, n, hnode, hmem, hcls, hop, w, d, hd, hm, hacc⟩ := h
    have hd' : (w, d) ∈ enumerateR (c.ctx a.op κ) (dir a.op) Laws.free a.elems.length n := by
      rw [← hlaws]; exact hd
    obtain ⟨r₀, h₀, r, hch, rfl, hacc'⟩ :=
      (regroup_views_iff (ctx := c.ctx a.op κ) (taken := takenOf σ a.elems)).1 ⟨d, hd', hacc⟩
    exact ⟨id, n, hnode, hmem, hcls, hop, r₀, h₀, r, hch, hm, hacc'⟩
  · rintro ⟨id, n, hnode, hmem, hcls, hop, r₀, h₀, r, hch, hm, hacc⟩
    exact regroup_match_complete hκ hnode hmem hcls hop hlaws h₀ hch hacc hm

end Semper.EMatch.Flatten
