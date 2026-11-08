import SemperProofs.EMatch.Flatten.RegroupSkip
import SemperProofs.EMatch.Flatten.RegroupSound
import SemperProofs.EMatch.Flatten.RegroupNested

/-!
# `:flatten`: regrouped views under the operator's laws

The engine regroups *normal forms*: the walk's views are normalized under the
operator's laws before `FlattenScratch::regroup` reads them, a group replaces
a sub-multiset (AC), a subset (ACI) or a run (`:assoc`) of the normal form by
its class, and the raw result is normalized again under the same laws
(`crate::nary_canon::normalize`: coalescing or deduplication, the identity
drop, the nilpotent clamp, inverse-pair cancellation). Laws need `:comm`
(`sortcheck.rs`), so a sequence operator is laws-free in the engine; the
model still allows an identity there. `:cancellative` changes no view.

## Soundness

`LawsModelAC`, `LawsModelACI`, `LawsModelA`: a denotation of the classes
satisfies the laws (the unit denotes the identity, `k • x = 0` under
`:nilpotent k`, `x + y = 0` when `y` is the inverse class of `x`).
Normalization keeps the denotation in such a model (`denAC_normalizeList`,
`denACI_normalizeList`, `denA_normalizeList`), so one regrouping under laws
keeps it (`regroup_step_sound_ac_laws`, `_aci_laws`, `_assoc_laws`) and every
view of the full enumeration and of the engine's (`enumerateR`,
`enumerateRSkip`) denotes the node (`regroup_views_sound_{ac,aci,assoc}_laws`,
`regroupSkip_views_sound_{ac,aci,assoc}_laws`). A group whose class is the
unit, a group whose class cancels or clamps against the rest, and an
idempotent duplicate are all sound: the normal form of the regrouped raw view
equals the view modulo the laws.

## Completeness

`RegroupsToL κ dir laws w g grp w'`: the laws-free regrouping of
`RegroupChain.lean` (`RegroupsTo`) to a canonical view `w₀`, then the normal
form of `w₀` under the laws is the node `w'`. `RegroupStepL`, `RegroupChainL`
are the record steps and chains. One step is exactly one regrouping of the
model under any laws (`regroupStepL_iff`), so the views and the matches of
both enumerations are exactly the chains' (`regroup_views_iff_laws`,
`regroup_match_iff_laws`, `regroupSkip_views_iff_laws`,
`regroupSkip_match_iff_laws`), generalizing `regroup_match_iff` and
`regroupSkip_match_iff` to any laws; with `Laws.free` a step is the laws-free
one (`regroupStepL_free_iff`). `regroupSkip_match_complete_laws` and
`regroupSkip_plan_complete_laws` restate the final completeness theorems with
chains under the laws; `regroupSkip_plan_sound` and `regroupSkip_plan_complete`
already hold for any laws.

## Classes the normalization drops

Without laws the class `g` of a group stays in the regrouped view; under laws
the normalization may drop it (`g` is the unit, its count clamps to zero, it
cancels against its inverse). A regrouped record therefore needs only the
classes its normal form holds (`needsAfter`), and a leaf that gains a dropped
`g` is flagged non-inert (`addG`): no item can take `g`, and closing the group
again is not inert. Every needed class of a reachable record is a class of its
view (`reach_needs_held`), so a pattern whose items take the whole view
satisfies the needs (`needs_taken_of_all`). The walk keeps every leaf under an
identity (`mayNonInert`), since a later regrouping may flag it, and pruning
stays match-preserving (`prune_regroup`). `regroup_drop_need_unit`,
`regroup_drop_need_nilpotent`, `regroup_drop_need_inverse` and
`regroup_drop_need_leaf` are the four matches of
`flatten_regroup_laws_drop_need.egg`, found by the engine's enumeration.

## What chains miss under laws

The characterization is relative to chains: openings by the walk, then
contractions by regrouping. Relative to the laws, over the classes present,
two kinds of match are beyond any chain:

* **A normal form reached only by inserting** the unit, a cancel pair or `k`
  copies under `:nilpotent k`: `a + c = (a + b) + (c + d)` when
  `zero ∋ add{b, d}` (`regroup_insert_unit_lost`). No chain inserts, and
  insertions are unbounded.
* **An idempotent group kept beside its class**: `S{a, b, c} = S{a, c, G}`
  when `G ∋ S{a, b}`, a canonical set the replacing regrouping never forms
  (`regroup_idem_overlap_lost`); keeping members would multiply the views by
  up to `2^|group|`.

The fixtures `flatten_regroup_laws_insert.egg` and
`flatten_regroup_laws_idem.egg` pin each loss in the engine.
-/

namespace Semper.EMatch.Flatten

open Semper.EMatch

/-! ## Soundness: commutative monoids with the laws -/

section AC

variable {M : Type*} [AddCommMonoid M]

/-- The operator's laws hold in the denotation `den`: the unit denotes zero,
every class is `k`-torsion under `:nilpotent k`, and a class and its inverse
class sum to zero. -/
structure LawsModelAC (laws : Laws) (den : C → M) : Prop where
  unit : ∀ u, laws.unit = some u → den u = 0
  nil : ∀ k, laws.nilpotent = some k → ∀ c, k • den c = 0
  inv : ∀ inv, laws.inv = some inv → ∀ x y, inv x = some y → den x + den y = 0

theorem LawsModelAC.free (den : C → M) : LawsModelAC Laws.free den where
  unit _ h := by simp [Laws.free] at h
  nil _ h := by simp [Laws.free] at h
  inv _ h := by simp [Laws.free] at h

/-- The denotation of an entry list, entry by entry. -/
def denL (den : C → M) (l : List (C × Nat)) : M := (l.map (fun e => e.2 • den e.1)).sum

theorem denAC_eq_denL (den : C → M) : ∀ l : List (C × Nat), denAC den l = denL den l
  | [] => by simp [denAC, denL, ofEntries]
  | e :: l => by
      have ih := denAC_eq_denL den l
      simp only [denAC, denL, ofEntries_cons, Multiset.map_add, Multiset.sum_add,
        Multiset.map_replicate, Multiset.sum_replicate, List.map_cons, List.sum_cons] at ih ⊢
      rw [ih]

theorem denL_filter_zero (den : C → M) :
    ∀ l : List (C × Nat), denL den (l.filter (fun e => e.2 ≠ 0)) = denL den l
  | [] => rfl
  | e :: l => by
      have ih := denL_filter_zero den l
      rw [List.filter_cons]
      split
      · simp only [denL, List.map_cons, List.sum_cons] at ih ⊢; rw [ih]
      · rename_i h
        simp only [ne_eq, decide_eq_true_eq, not_not] at h
        simp only [denL, List.map_cons, List.sum_cons, h, zero_smul, zero_add] at ih ⊢
        exact ih

theorem denL_filter_class (den : C → M) {u : C} (hu : den u = 0) :
    ∀ l : List (C × Nat), denL den (l.filter (fun e => e.1 ≠ u)) = denL den l
  | [] => rfl
  | e :: l => by
      have ih := denL_filter_class den hu l
      rw [List.filter_cons]
      split
      · simp only [denL, List.map_cons, List.sum_cons] at ih ⊢; rw [ih]
      · rename_i h
        simp only [ne_eq, decide_eq_true_eq, not_not] at h
        simp only [denL, List.map_cons, List.sum_cons, h, hu, smul_zero, zero_add] at ih ⊢
        exact ih

/-- A count modulo a torsion order denotes the same. -/
theorem smul_mod_of_torsion {k : Nat} {x : M} (hk : k • x = 0) (n : Nat) :
    (n % k) • x = n • x := by
  conv_rhs => rw [← Nat.mod_add_div n k]
  rw [add_smul, mul_comm, mul_smul, hk, smul_zero, add_zero]

/-- Setting one entry: the rest with that entry zeroed, plus the new entry. -/
theorem denL_set (den : C → M) :
    ∀ (l : List (C × Nat)) (i : Nat) (c c' : C) (a : Nat), i < l.length →
      denL den (l.set i (c, a)) = denL den (l.set i (c', 0)) + a • den c
  | [], _, _, _, _, h => absurd h (by simp)
  | e :: l, 0, c, c', a, _ => by
      simp only [denL, List.set_cons_zero, List.map_cons, List.sum_cons, zero_smul, zero_add]
      rw [add_comm]
  | e :: l, i + 1, c, c', a, h => by
      have ih := denL_set den l i c c' a (by simpa using h)
      simp only [denL, List.set_cons_succ, List.map_cons, List.sum_cons] at ih ⊢
      rw [ih, add_assoc]

theorem denL_eq_set (den : C → M) {l : List (C × Nat)} {i : Nat} {c : C} {a : Nat}
    (h : l[i]? = some (c, a)) :
    denL den l = denL den (l.set i (c, 0)) + a • den c := by
  have hi := (List.getElem?_eq_some_iff.1 h).1
  have hs : l.set i (c, a) = l := by
    have : l[i] = (c, a) := (List.getElem?_eq_some_iff.1 h).2
    rw [← this, List.set_getElem_self]
  conv_lhs => rw [← hs]
  exact denL_set den l i c c a hi

theorem denL_cancelAt {den : C → M} {inv : C → Option C}
    (hinv : ∀ x y, inv x = some y → den x + den y = 0) (l : List (C × Nat)) (i : Nat) :
    denL den (cancelAt inv l i) = denL den l := by
  unfold cancelAt
  rcases hl : l[i]? with _ | ⟨x, xc⟩
  · rfl
  have hi : i < l.length := (List.getElem?_eq_some_iff.1 hl).1
  simp only
  split
  · rfl
  split
  · rfl
  next y hy =>
  split
  · next hyx =>
      subst hyx
      split
      · have h2 : 2 • den y = 0 := by rw [two_smul]; exact hinv y y hy
        rw [denL_eq_set den hl, denL_set den l i y y _ hi, smul_mod_of_torsion h2]
      · rfl
  split
  · rfl
  next j hfind =>
  obtain ⟨hj, hp, -⟩ := List.findIdx?_eq_some_iff_getElem.1 hfind
  simp only [decide_eq_true_eq] at hp
  split
  · rfl
  next y' yc hlj =>
  have hlj' : l[j] = (y', yc) := (List.getElem?_eq_some_iff.1 hlj).2
  have hyy : y' = y := by rw [← hp, hlj']
  subst hyy
  have hji : j ≠ i := by
    rintro rfl
    rw [hl] at hlj
    simp only [Option.some.injEq, Prod.mk.injEq] at hlj
    next hyx => exact hyx hlj.1.symm
  set t := min xc yc
  have hxt : t ≤ xc := min_le_left _ _
  have hyt : t ≤ yc := min_le_right _ _
  have hjl : j < l.length := hj
  -- Both entries zeroed: `Z`.
  have e1 : denL den l = denL den ((l.set i (x, 0)).set j (y', 0)) + yc • den y' + xc • den x := by
    rw [denL_eq_set den hl]
    have : (l.set i (x, 0))[j]? = some (y', yc) := by
      rw [List.getElem?_set_ne (Ne.symm hji)]; exact hlj
    rw [denL_eq_set den this]
  have e2 : denL den ((l.set i (x, xc - t)).set j (y', yc - t)) =
      denL den ((l.set i (x, 0)).set j (y', 0)) + (yc - t) • den y' + (xc - t) • den x := by
    have c1 : ((l.set i (x, xc - t)).set j (y', 0)) = ((l.set j (y', 0)).set i (x, xc - t)) :=
      List.set_comm _ _ (Ne.symm hji)
    have c2 : ((l.set i (x, 0)).set j (y', 0)) = ((l.set j (y', 0)).set i (x, 0)) :=
      List.set_comm _ _ (Ne.symm hji)
    rw [denL_set den _ j y' y' _ (by simpa using hjl), c1, c2,
      denL_set den _ i x x _ (by simpa using hi)]
    abel
  rw [e2, e1]
  have hsum : xc • den x + yc • den y' =
      (xc - t) • den x + (yc - t) • den y' + t • (den x + den y') := by
    conv_lhs => rw [← Nat.sub_add_cancel hxt, ← Nat.sub_add_cancel hyt]
    rw [add_smul, add_smul, smul_add]
    abel
  rw [hinv x y' hy, smul_zero, add_zero] at hsum
  rw [add_assoc, add_assoc, add_comm (yc • den y'), hsum]
  abel

theorem denL_cancel {den : C → M} {inv : C → Option C}
    (hinv : ∀ x y, inv x = some y → den x + den y = 0) (l : List (C × Nat)) :
    denL den (cancel inv l) = denL den l := by
  unfold cancel
  rw [denL_filter_zero]
  generalize l.length = n
  induction n with
  | zero => rfl
  | succ n ih => rw [cancelSteps, denL_cancelAt hinv, ih]

theorem denL_clamp {den : C → M} {laws : Laws} (hl : LawsModelAC laws den)
    (l : List (C × Nat)) : denL den (clamp laws.nilpotent l) = denL den l := by
  unfold clamp
  rcases h : laws.nilpotent with _ | k
  · rfl
  · simp only
    rw [denL_filter_zero]
    unfold denL
    rw [List.map_map]
    congr 1
    refine List.map_congr_left (fun e _ => ?_)
    exact smul_mod_of_torsion (hl.nil k h (e.1)) e.2

theorem denL_dropUnit {den : C → M} {laws : Laws} (hl : LawsModelAC laws den)
    (l : List (C × Nat)) : denL den (dropUnit laws.unit l) = denL den l := by
  unfold dropUnit
  rcases h : laws.unit with _ | u
  · rfl
  · exact denL_filter_class den (hl.unit u h) l

/-- **Normalization under the laws keeps the denotation, AC.** -/
theorem denAC_normalizeList {den : C → M} {laws : Laws} (hl : LawsModelAC laws den)
    (v : List (C × Nat)) : denAC den (normalizeList .ac laws v) = denAC den v := by
  rw [denAC_eq_denL, denAC_eq_denL]
  unfold normalizeList
  simp only
  have h1 : denL den (clamp laws.nilpotent (dropUnit laws.unit (coalesce v))) = denL den v := by
    rw [denL_clamp hl, denL_dropUnit hl, ← denAC_eq_denL, ← denAC_eq_denL, denAC, denAC,
      ofEntries_coalesce]
  rcases h : laws.inv with _ | inv
  · exact h1
  · rw [denL_cancel (hl.inv inv h), h1]

theorem denAC_normalize {den : C → M} {laws : Laws} (hl : LawsModelAC laws den)
    {v w : List (C × Nat)} (h : normalize .ac laws v = .node w) : denAC den w = denAC den v := by
  rw [normalize_node_eq h, denAC_normalizeList hl]

/-- **One regrouping under the laws keeps the denotation, AC**: the regrouped
raw view, normalized under the laws, denotes the view. -/
theorem regroup_step_sound_ac_laws {ctx : Ctx} {den : C → M} (hc : ConsistentAC ctx den)
    {laws : Laws} (hl : LawsModelAC laws den) {dir : Dir} {id : NodeId} {m : Node} {g : C}
    (hm : ctx.IsMember id m g) {view raw w' : List (C × Nat)} (hnd : (view.map Prod.fst).Nodup)
    (h : raw ∈ fitsR .ac dir view g (kids .ac m.children)) (hn : normalize .ac laws raw = .node w') :
    denAC den w' = denAC den view := by
  rw [denAC_normalize hl hn, regroup_step_sound_ac hc hm hnd h]

end AC

/-! ## Soundness: join semilattices with a unit -/

section ACI

variable {M : Type*} [SemilatticeSup M] [OrderBot M]

/-- The identity law in a join semilattice: the unit denotes the bottom. -/
def LawsModelACI (laws : Laws) (den : C → M) : Prop := ∀ u, laws.unit = some u → den u = ⊥

theorem toFinset_ofEntries_filter {l : List (C × Nat)} (hp : ∀ e ∈ l, 0 < e.2) (u : C) :
    (ofEntries (l.filter (fun e => e.1 ≠ u))).toFinset =
      (ofEntries l).toFinset.filter (fun c => c ≠ u) := by
  rw [toFinset_ofEntries_of_pos (fun e he => hp e (List.mem_filter.1 he).1),
    toFinset_ofEntries_of_pos hp]
  ext c
  simp only [List.mem_toFinset, List.mem_map, List.mem_filter, Finset.mem_filter, ne_eq,
    decide_eq_true_eq]
  constructor
  · rintro ⟨e, ⟨he, hu⟩, rfl⟩; exact ⟨⟨e, he, rfl⟩, hu⟩
  · rintro ⟨⟨e, he, rfl⟩, hu⟩; exact ⟨e, ⟨he, hu⟩, rfl⟩

theorem sup_filter_ne {s : Finset C} {den : C → M} {u : C} (hu : den u = ⊥) :
    (s.filter (fun c => c ≠ u)).sup den = s.sup den := by
  conv_rhs => rw [← Finset.filter_union_filter_not_eq (fun c => c ≠ u) s]
  rw [Finset.sup_union]
  have : (s.filter (fun c => ¬ c ≠ u)).sup den = ⊥ := by
    refine Finset.sup_eq_bot_iff _ _ |>.2 (fun c hc => ?_)
    simp only [ne_eq, not_not, Finset.mem_filter] at hc
    rw [hc.2, hu]
  rw [this, sup_bot_eq]

/-- **Normalization under the laws keeps the denotation, ACI.** -/
theorem denACI_normalizeList {den : C → M} {laws : Laws} (hl : LawsModelACI laws den)
    {v : List (C × Nat)} (hp : ∀ e ∈ v, 0 < e.2) :
    denACI den (normalizeList .aci laws v) = denACI den v := by
  unfold normalizeList
  simp only
  unfold denACI dropUnit
  rcases h : laws.unit with _ | u
  · simp only
    rw [toFinset_ofEntries_dedupAci hp]
  · simp only
    rw [toFinset_ofEntries_filter (dedupAci_pos v), toFinset_ofEntries_dedupAci hp,
      sup_filter_ne (hl u h)]

theorem denACI_normalize {den : C → M} {laws : Laws} (hl : LawsModelACI laws den)
    {v w : List (C × Nat)} (hp : ∀ e ∈ v, 0 < e.2) (h : normalize .aci laws v = .node w) :
    denACI den w = denACI den v := by
  rw [normalize_node_eq h, denACI_normalizeList hl hp]

/-- **One regrouping under the laws keeps the denotation, ACI.** -/
theorem regroup_step_sound_aci_laws {ctx : Ctx} {den : C → M} (hc : ConsistentACI ctx den)
    {laws : Laws} (hl : LawsModelACI laws den) {dir : Dir} {id : NodeId} {m : Node} {g : C}
    (hm : ctx.IsMember id m g) {view raw w' : List (C × Nat)} (hnd : (view.map Prod.fst).Nodup)
    (h : raw ∈ fitsR .aci dir view g (kids .aci m.children))
    (hn : normalize .aci laws raw = .node w') :
    denACI den w' = denACI den view := by
  have hrawp : ∀ e ∈ raw, 0 < e.2 := by
    obtain ⟨-, v, hs, rfl⟩ := fitsR_aci h
    intro e he
    rcases List.mem_append.1 he with he | he
    · exact subEntries_pos _ _ _ hs e he
    · rw [List.mem_singleton] at he; subst he; exact Nat.one_pos
  rw [denACI_normalize hl hrawp hn, regroup_step_sound_aci hc hm hnd h]

end ACI

/-! ## Soundness: monoids with a unit -/

section Assoc

variable {M : Type*} [Monoid M]

/-- The identity law in a monoid: the unit denotes one. -/
def LawsModelA (laws : Laws) (den : C → M) : Prop := ∀ u, laws.unit = some u → den u = 1

theorem denA_filter_class {den : C → M} {u : C} (hu : den u = 1) :
    ∀ l : List (C × Nat), denA den (l.filter (fun e => e.1 ≠ u)) = denA den l
  | [] => rfl
  | e :: l => by
      have ih := denA_filter_class hu l
      rw [List.filter_cons]
      split
      · simp only [denA, List.map_cons, List.prod_cons] at ih ⊢; rw [ih]
      · rename_i h
        simp only [ne_eq, decide_eq_true_eq, not_not] at h
        simp only [denA, List.map_cons, List.prod_cons, h, hu, one_mul] at ih ⊢
        exact ih

/-- **Normalization under the laws keeps the denotation, `:assoc`.** -/
theorem denA_normalizeList {den : C → M} {laws : Laws} (hl : LawsModelA laws den)
    (v : List (C × Nat)) : denA den (normalizeList .assoc laws v) = denA den v := by
  unfold normalizeList dropUnit
  simp only
  rcases h : laws.unit with _ | u
  · rfl
  · exact denA_filter_class (hl u h) v

theorem denA_normalize {den : C → M} {laws : Laws} (hl : LawsModelA laws den)
    {v w : List (C × Nat)} (h : normalize .assoc laws v = .node w) : denA den w = denA den v := by
  rw [normalize_node_eq h, denA_normalizeList hl]

/-- **One regrouping under the laws keeps the denotation, `:assoc`.** -/
theorem regroup_step_sound_assoc_laws {ctx : Ctx} {den : C → M} (hc : ConsistentA ctx den)
    {laws : Laws} (hl : LawsModelA laws den) {dir : Dir} {id : NodeId} {m : Node} {g : C}
    (hm : ctx.IsMember id m g) {view raw w' : List (C × Nat)}
    (h : raw ∈ fitsR .assoc dir view g (kids .assoc m.children))
    (hn : normalize .assoc laws raw = .node w') :
    denA den w' = denA den view := by
  rw [denA_normalize hl hn, regroup_step_sound_assoc hc hm h]

end Assoc

/-! ## Every view of both enumerations denotes the node, under the laws -/

/-- A property of the walk's records that one regrouping preserves holds of
every reachable record. -/
theorem reach_induction {ctx : Ctx} {dir : Dir} {laws : Laws} {base : List RecR}
    {P : RecR → Prop} (h0 : ∀ r ∈ base, P r)
    (hs : ∀ r r', P r → r' ∈ regroupRec ctx dir laws r → P r') {r : RecR}
    (h : Reach ctx dir laws base r) : P r := by
  obtain ⟨r₀, h₀, hch⟩ := h
  induction hch with
  | refl => exact h0 _ h₀
  | tail _ hs' ih => exact hs _ _ ih hs'

/-- A view of the full enumeration is the view of a reachable record. -/
theorem reach_of_mem_enumerateR {ctx : Ctx} {dir : Dir} {laws : Laws} {limit : Nat} {n : Node}
    {w : List (C × Nat)} {d : DemandL} (h : (w, d) ∈ enumerateR ctx dir laws limit n) :
    ∃ r, Reach ctx dir laws (baseRecsR ctx dir laws n) r ∧ r.1 = w := by
  unfold enumerateR at h
  obtain ⟨r, hr, rfl⟩ := mem_enumerateFromR h
  exact ⟨r, (mem_regroupAll_iff_reach (baseGood_baseRecsR ctx dir laws n)).1
    (mem_withinLimit.1 hr).1, rfl⟩

/-- A view of the engine's enumeration is the view of a reachable record. -/
theorem reach_of_mem_enumerateRSkip {ctx : Ctx} {dir : Dir} {laws : Laws} {limit : Nat}
    {n : Node} {w : List (C × Nat)} {d : DemandL}
    (h : (w, d) ∈ enumerateRSkip ctx dir laws limit n) :
    ∃ r, Reach ctx dir laws (baseRecsR ctx dir laws n) r ∧ r.1 = w := by
  unfold enumerateRSkip at h
  obtain ⟨r, hr, rfl⟩ := mem_enumerateFromR h
  exact ⟨r, (regroupSkipG_spec (baseGood_baseRecsR ctx dir laws n) (groupsOfEngine_sub ctx)
    (candSup_of_sup dir (groupsOfEngine_sup ctx))).1 r (mem_withinLimit.1 hr).1, rfl⟩

section ACViews

variable {M : Type*} [AddCommMonoid M]

/-- Every record reachable from the walk's records of an AC node denotes the
node, under the laws. -/
theorem reach_den_ac {ctx : Ctx} (hκ : ctx.κ = .ac) {den : C → M} (hc : ConsistentAC ctx den)
    {laws : Laws} (hl : LawsModelAC laws den) {n : Node} {r : RecR}
    (h : Reach ctx .both laws (baseRecsR ctx .both laws n) r) :
    denAC den r.1 = denAC den (kids .ac n.children) := by
  refine (reach_induction (P := fun r => denAC den r.1 = denAC den (kids .ac n.children) ∧
    (r.1.map Prod.fst).Nodup) ?_ ?_ h).1
  · intro r hr
    obtain ⟨v, ls, o, hv, hn⟩ := mem_baseRecsR_both hr
    rw [hκ] at hn
    refine ⟨?_, (normalize_ac_canonical hn).nodup⟩
    have h1 := otl_den_ac hκ hc hv
    rw [hκ, one_smul] at h1
    rw [denAC_normalize hl hn, h1]
  · intro r r' ⟨hr, hnd⟩ h'
    obtain ⟨g, grp, raw, hgg, hraw, hn, -⟩ := mem_regroupRec h'
    obtain ⟨id, m, hm, rfl⟩ := mem_groupsOf hgg
    rw [hκ] at hraw hn
    exact ⟨by rw [regroup_step_sound_ac_laws hc hl hm hnd hraw hn, hr],
      (normalize_ac_canonical hn).nodup⟩

/-- **The views with regrouping of an AC operator denote the node, under its
laws** (`regroup_views_sound_ac` for any laws). -/
theorem regroup_views_sound_ac_laws {ctx : Ctx} (hκ : ctx.κ = .ac) {den : C → M}
    (hc : ConsistentAC ctx den) {laws : Laws} (hl : LawsModelAC laws den) {limit : Nat}
    {n : Node} {w : List (C × Nat)} {d : DemandL}
    (h : (w, d) ∈ enumerateR ctx .both laws limit n) :
    denAC den w = denAC den (kids .ac n.children) := by
  obtain ⟨r, hr, rfl⟩ := reach_of_mem_enumerateR h
  exact reach_den_ac hκ hc hl hr

/-- **The engine's views of an AC operator denote the node, under its laws.** -/
theorem regroupSkip_views_sound_ac_laws {ctx : Ctx} (hκ : ctx.κ = .ac) {den : C → M}
    (hc : ConsistentAC ctx den) {laws : Laws} (hl : LawsModelAC laws den) {limit : Nat}
    {n : Node} {w : List (C × Nat)} {d : DemandL}
    (h : (w, d) ∈ enumerateRSkip ctx .both laws limit n) :
    denAC den w = denAC den (kids .ac n.children) := by
  obtain ⟨r, hr, rfl⟩ := reach_of_mem_enumerateRSkip h
  exact reach_den_ac hκ hc hl hr

end ACViews

section ACIViews

variable {M : Type*} [SemilatticeSup M] [OrderBot M]

theorem reach_den_aci {ctx : Ctx} (hκ : ctx.κ = .aci) {den : C → M} (hc : ConsistentACI ctx den)
    {laws : Laws} (hl : LawsModelACI laws den) {n : Node} {r : RecR}
    (h : Reach ctx .both laws (baseRecsR ctx .both laws n) r) :
    denACI den r.1 = denACI den (kids .aci n.children) := by
  refine (reach_induction (P := fun r => denACI den r.1 = denACI den (kids .aci n.children) ∧
    (r.1.map Prod.fst).Nodup) ?_ ?_ h).1
  · intro r hr
    obtain ⟨v, ls, o, hv, hn⟩ := mem_baseRecsR_both hr
    rw [hκ] at hn
    refine ⟨?_, (normalize_aci_canonical hn).1.imp (fun h => Nat.ne_of_lt h)⟩
    have h1 := otl_den_aci hκ hc hv Nat.one_pos (kids_pos _ _)
    rw [hκ] at h1
    rw [denACI_normalize hl (RawViewL.pos hv) hn, h1]
  · intro r r' ⟨hr, hnd⟩ h'
    obtain ⟨g, grp, raw, hgg, hraw, hn, -⟩ := mem_regroupRec h'
    obtain ⟨id, m, hm, rfl⟩ := mem_groupsOf hgg
    rw [hκ] at hraw hn
    exact ⟨by rw [regroup_step_sound_aci_laws hc hl hm hnd hraw hn, hr],
      (normalize_aci_canonical hn).1.imp (fun h => Nat.ne_of_lt h)⟩

/-- **The views with regrouping of an ACI operator denote the node, under its
identity.** -/
theorem regroup_views_sound_aci_laws {ctx : Ctx} (hκ : ctx.κ = .aci) {den : C → M}
    (hc : ConsistentACI ctx den) {laws : Laws} (hl : LawsModelACI laws den) {limit : Nat}
    {n : Node} {w : List (C × Nat)} {d : DemandL}
    (h : (w, d) ∈ enumerateR ctx .both laws limit n) :
    denACI den w = denACI den (kids .aci n.children) := by
  obtain ⟨r, hr, rfl⟩ := reach_of_mem_enumerateR h
  exact reach_den_aci hκ hc hl hr

theorem regroupSkip_views_sound_aci_laws {ctx : Ctx} (hκ : ctx.κ = .aci) {den : C → M}
    (hc : ConsistentACI ctx den) {laws : Laws} (hl : LawsModelACI laws den) {limit : Nat}
    {n : Node} {w : List (C × Nat)} {d : DemandL}
    (h : (w, d) ∈ enumerateRSkip ctx .both laws limit n) :
    denACI den w = denACI den (kids .aci n.children) := by
  obtain ⟨r, hr, rfl⟩ := reach_of_mem_enumerateRSkip h
  exact reach_den_aci hκ hc hl hr

end ACIViews

section AssocViews

variable {M : Type*} [Monoid M]

theorem reach_den_assoc {ctx : Ctx} (hκ : ctx.κ = .assoc) {den : C → M} (hc : ConsistentA ctx den)
    {laws : Laws} (hl : LawsModelA laws den) {n : Node} {r : RecR}
    (h : Reach ctx .both laws (baseRecsR ctx .both laws n) r) :
    denA den r.1 = denA den (kids .assoc n.children) := by
  refine reach_induction (P := fun r => denA den r.1 = denA den (kids .assoc n.children)) ?_ ?_ h
  · intro r hr
    obtain ⟨v, ls, o, hv, hn⟩ := mem_baseRecsR_both hr
    rw [hκ] at hn
    have h1 := otl_den_assoc hκ hc hv
    rw [hκ] at h1
    rw [denA_normalize hl hn, h1]
  · intro r r' hr h'
    obtain ⟨g, grp, raw, hgg, hraw, hn, -⟩ := mem_regroupRec h'
    obtain ⟨id, m, hm, rfl⟩ := mem_groupsOf hgg
    rw [hκ] at hraw hn
    rw [regroup_step_sound_assoc_laws hc hl hm hraw hn, hr]

/-- **The views with regrouping of an `:assoc` operator denote the node, under
an identity.** -/
theorem regroup_views_sound_assoc_laws {ctx : Ctx} (hκ : ctx.κ = .assoc) {den : C → M}
    (hc : ConsistentA ctx den) {laws : Laws} (hl : LawsModelA laws den) {limit : Nat}
    {n : Node} {w : List (C × Nat)} {d : DemandL}
    (h : (w, d) ∈ enumerateR ctx .both laws limit n) :
    denA den w = denA den (kids .assoc n.children) := by
  obtain ⟨r, hr, rfl⟩ := reach_of_mem_enumerateR h
  exact reach_den_assoc hκ hc hl hr

theorem regroupSkip_views_sound_assoc_laws {ctx : Ctx} (hκ : ctx.κ = .assoc) {den : C → M}
    (hc : ConsistentA ctx den) {laws : Laws} (hl : LawsModelA laws den) {limit : Nat}
    {n : Node} {w : List (C × Nat)} {d : DemandL}
    (h : (w, d) ∈ enumerateRSkip ctx .both laws limit n) :
    denA den w = denA den (kids .assoc n.children) := by
  obtain ⟨r, hr, rfl⟩ := reach_of_mem_enumerateRSkip h
  exact reach_den_assoc hκ hc hl hr

end AssocViews

/-! ## Completeness: chains of regroupings under the laws -/

/-- **One regrouping of a normal form under the laws, declaratively**: the
laws-free regrouping (`RegroupsTo`: a sub-multiset, a subset or a run on the
spine, at least two entries, not the whole view, replaced by `g`) gives the
canonical view `w₀`, and `w₀` normalized under the laws is the node `w'`.
The engine regroups after normalization, the view `w` is a normal form, and
normalizes the regrouped raw view again; a result that is the unit, a single
class or empty is not a view. -/
def RegroupsToL (κ : FlatKind) (dir : Dir) (laws : Laws) (w : List (C × Nat)) (g : C)
    (grp w' : List (C × Nat)) : Prop :=
  ∃ w₀, RegroupsTo κ dir w g grp w₀ ∧ normalize κ laws w₀ = .node w'

/-- One regrouping of a record under the laws, by an `f`-member: the view
regroups (`RegroupsToL`), the leaves gain `g` (`addG`) and the needed classes
lose those the group absorbs and gain `g` (`needsAfter`), as without laws. -/
inductive RegroupStepL (ctx : Ctx) (dir : Dir) (laws : Laws) : RecR → RecR → Prop
  | mk {r : RecR} {id : NodeId} {m : Node} {g : C} {w' : List (C × Nat)} :
      ctx.IsMember id m g → g ∉ (kids ctx.κ m.children).map Prod.fst →
      RegroupsToL ctx.κ dir laws r.1 g (kids ctx.κ m.children) w' →
      RegroupStepL ctx dir laws r
        (w', r.2.1.map (addG g ((kids ctx.κ m.children).map Prod.fst) (w'.map Prod.fst)),
          needsAfter g ((kids ctx.κ m.children).map Prod.fst) (w'.map Prod.fst) r.2.2)

/-- A finite chain of regroupings under the laws. -/
def RegroupChainL (ctx : Ctx) (dir : Dir) (laws : Laws) : RecR → RecR → Prop :=
  Relation.ReflTransGen (RegroupStepL ctx dir laws)

theorem normalizeList_canonK (κ : FlatKind) (laws : Laws) (v : List (C × Nat)) :
    normalizeList κ laws (canonK κ v) = normalizeList κ laws v := by
  cases κ with
  | assoc => rfl
  | ac => unfold normalizeList canonK; rw [coalesce_coalesce]
  | aci => unfold normalizeList canonK; rw [dedupAci_dedupAci]

/-- The laws act on the canonical form: normalizing it is normalizing the raw view. -/
theorem normalize_canonK (κ : FlatKind) (laws : Laws) (v : List (C × Nat)) :
    normalize κ laws (canonK κ v) = normalize κ laws v := by
  unfold normalize
  rw [normalizeList_canonK]

theorem two_le_viewSize {w : List (C × Nat)} (h0 : w ≠ []) (h1 : ∀ c, w ≠ [(c, 1)])
    (hp : ∀ e ∈ w, 0 < e.2) : 2 ≤ viewSize w := by
  match w, h0, h1, hp with
  | [e], _, h1, hp =>
      have he := hp e (List.mem_singleton_self _)
      have hne : e.2 ≠ 1 := fun h => h1 e.1 (by rw [← h])
      simp only [viewSize, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      omega
  | e :: f :: l, _, _, hp =>
      have he := hp e (List.mem_cons_self ..)
      have hf := hp f (List.mem_cons_of_mem _ (List.mem_cons_self ..))
      simp only [viewSize, List.map_cons, List.sum_cons]
      omega

/-- A raw view whose normal form under the laws is a node is a node without
laws: the laws only drop counts. -/
theorem normalize_free_of_node {κ : FlatKind} {laws : Laws} {v w : List (C × Nat)}
    (hp : ∀ e ∈ v, 0 < e.2) (h : normalize κ laws v = .node w) :
    normalize κ Laws.free v = .node (canonK κ v) := by
  have hcl : classify laws.unit (normalizeList κ laws v) = .node w := h
  obtain ⟨hw, h0, h1⟩ := (classify_node_iff _ _ _).1 hcl
  have hwp := (viewGood_normalize h (fun _ => hp)).1
  rw [hw] at h0 h1
  have h2 := two_le_viewSize h0 h1 hwp
  have hle : viewSize w ≤ viewSize (canonK κ v) := by
    rw [← hw, ← normalizeList_canonK]
    refine viewSize_normalizeList_le laws (fun hκ => ?_)
    subst hκ
    exact dedupAci_pos v
  refine normalize_free_node.2 ⟨rfl, fun h => ?_, fun c h => ?_⟩
  · have : viewSize (canonK κ v) = 0 := by rw [h]; rfl
    omega
  · have : viewSize (canonK κ v) = 1 := by rw [h]; rfl
    omega

/-- The canonical views regrouping reads are good views. -/
theorem viewGood_of_viewOK {κ : FlatKind} {w : List (C × Nat)} (h : ViewOK κ w) :
    ViewGood κ w := by
  cases κ with
  | assoc => exact ⟨h, fun h => absurd rfl h⟩
  | ac =>
      have hc : Canonical w := by
        have := coalesce_canonical w; simp only [ViewOK] at h; rwa [h] at this
      exact ⟨hc.2, fun _ => hc.nodup⟩
  | aci =>
      have hc := ones_of_dedupAci h
      exact ⟨fun e he => by rw [hc.2 e he]; exact Nat.one_pos,
        fun _ => hc.1.imp (fun h => Nat.ne_of_lt h)⟩

/-- A normal form under any laws is canonical. -/
theorem viewOK_normalize {κ : FlatKind} {laws : Laws} {v w : List (C × Nat)}
    (h : normalize κ laws v = .node w) (hp : κ = .assoc → ∀ e ∈ v, 0 < e.2) : ViewOK κ w := by
  cases κ with
  | assoc => exact (viewGood_normalize h hp).1
  | ac =>
      simp only [ViewOK]
      unfold coalesce
      exact entries_ofEntries_of_canonical (normalize_ac_canonical h)
  | aci =>
      simp only [ViewOK]
      have hc := normalize_aci_canonical h
      unfold dedupAci
      rw [normalize_aci_sort h, List.map_map]
      refine (List.map_congr_left (fun e he => ?_)).trans (List.map_id w)
      exact Prod.ext rfl (hc.2 e he).symm

/-- The walk's records have canonical views under any laws. -/
theorem viewOK_baseL {ctx : Ctx} {dir : Dir} {laws : Laws} {n : Node} {r : RecR}
    (h : r ∈ baseRecsR ctx dir laws n) : ViewOK ctx.κ r.1 := by
  obtain ⟨raw, hraw, hn, -⟩ := mem_baseRecsR_raw h
  exact viewOK_normalize hn (fun _ => kidsOfD_pos _
    (fun b X k P hk => rawOptD_pos ctx dir _ b X k P hk) dir _ _ 0 1 ∅ Nat.one_pos
    (kids_pos _ _) raw hraw)

/-- A regrouping of a canonical record has a canonical view. -/
theorem viewOK_rstep {ctx : Ctx} {dir : Dir} {laws : Laws} {r r' : RecR}
    (hok : ViewOK ctx.κ r.1) (h : r' ∈ regroupRec ctx dir laws r) : ViewOK ctx.κ r'.1 := by
  obtain ⟨g, grp, raw, -, hraw, hn, -⟩ := mem_regroupRec h
  exact viewOK_normalize hn (fun _ => (fitsR_shrink (viewGood_of_viewOK hok) hraw).2)

/-- A declarative regrouping without laws is a fit of the model whose
laws-free normal form is the regrouped view. -/
theorem fit_of_regroupsTo {κ : FlatKind} {dir : Dir} {view : List (C × Nat)} {g : C}
    {grp w₀ : List (C × Nat)} (hok : ViewOK κ view) (hg : g ∉ grp.map Prod.fst)
    (h : RegroupsTo κ dir view g grp w₀) :
    ∃ raw ∈ fitsR κ dir view g grp, normalize κ Laws.free raw = .node w₀ := by
  cases κ with
  | ac =>
      obtain ⟨h2, hsub, hne, rfl⟩ := h
      simp only [ViewOK] at hok
      have hnd : (view.map Prod.fst).Nodup := by
        have := (coalesce_canonical view).nodup; rwa [hok] at this
      obtain ⟨v, hfit, hsum⟩ := fitsR_ac_complete (dir := dir) hnd hg hsub hne h2
      have hv0 : ofEntries v ≠ 0 := by
        intro h0; rw [h0, zero_add] at hsum; exact hne hsum
      have hcard : 2 ≤ Multiset.card (ofEntries (v ++ [(g, 1)])) := by
        rw [ofEntries_append]
        simp only [Multiset.card_add]
        have : 1 ≤ Multiset.card (ofEntries v) := Multiset.card_pos.2 hv0
        have h1 : Multiset.card (ofEntries [(g, 1)]) = 1 := by simp [ofEntries]
        omega
      have hv : ofEntries v = ofEntries view - ofEntries grp := eq_tsub_of_add_eq hsum
      have hw : coalesce (v ++ [(g, 1)]) =
          Multiset.entries (ofEntries view - ofEntries grp + {g}) := by
        unfold coalesce
        rw [ofEntries_append, hv]
        congr 2
      exact ⟨_, hfit, by rw [normalize_free_ac_node hcard, hw]⟩
  | aci =>
      obtain ⟨h2, hsub, hne, hF, rfl⟩ := h
      simp only [ViewOK] at hok
      have hcan := ones_of_dedupAci hok
      obtain ⟨v, hfit, -⟩ := fitsR_aci_complete (dir := dir) hcan hg
        (fun c hc => List.mem_toFinset.1 (hsub (List.mem_toFinset.2 hc))) hne h2
      obtain ⟨-, v', hs', he'⟩ := fitsR_aci hfit
      have hvv : v = v' := List.append_cancel_right he'
      subst hvv
      have hd := dedupAci_regrouped (g := g) hok hs'
      have hlen : ((insert g ((view.map Prod.fst).toFinset \ (grp.map Prod.fst).toFinset)).sort
          (· ≤ ·)).length = (insert g ((view.map Prod.fst).toFinset \
            (grp.map Prod.fst).toFinset)).card := Finset.length_sort _
      refine ⟨_, hfit, normalize_free_node.2 ⟨hd.symm, fun h0 => ?_, fun c h0 => ?_⟩⟩
      · have := congrArg List.length h0
        simp only [List.length_map, hlen, List.length_nil] at this
        omega
      · have := congrArg List.length h0
        simp only [List.length_map, hlen, List.length_singleton] at this
        omega
  | assoc =>
      obtain ⟨p, h2, hlt, hp, hsp, hrun, rfl⟩ := h
      refine ⟨_, fitsR_assoc_complete hg h2 hlt hp hsp hrun, normalize_free_node.2
        ⟨rfl, by simp, fun c h0 => ?_⟩⟩
      have := congrArg List.length h0
      simp only [List.length_append, List.length_take, List.length_cons, List.length_drop,
        List.length_nil] at this
      omega

/-- **One declarative step under the laws is one regrouping of the model.** -/
theorem regroupStepL_mem {ctx : Ctx} {dir : Dir} {laws : Laws} {r r' : RecR}
    (hok : ViewOK ctx.κ r.1) (h : RegroupStepL ctx dir laws r r') :
    r' ∈ regroupRec ctx dir laws r := by
  obtain ⟨hm, hg, ⟨w₀, hto, hn⟩⟩ := h
  obtain ⟨raw, hraw, hfree⟩ := fit_of_regroupsTo hok hg hto
  have hw₀ : w₀ = canonK ctx.κ raw := (normalize_free_node.1 hfree).1
  have hn' := hn
  rw [hw₀, normalize_canonK] at hn'
  exact regroupRec_of (mem_groupsOf_of_member hm) hraw hn'

/-- **Every regrouping of the model under the laws is a declarative step.** -/
theorem regroupStepL_of_mem {ctx : Ctx} {dir : Dir} {laws : Laws} {r r' : RecR}
    (hok : ViewOK ctx.κ r.1) (h : r' ∈ regroupRec ctx dir laws r) :
    RegroupStepL ctx dir laws r r' := by
  obtain ⟨g, grp, raw, hgg, hraw, hn, hL, hN⟩ := mem_regroupRec h
  have hp := (fitsR_shrink (viewGood_of_viewOK hok) hraw).2
  have hto := regroupsTo_of_fitsR hok hraw (normalize_free_of_node hp hn)
  obtain ⟨id, m, hm, rfl⟩ := mem_groupsOf hgg
  obtain ⟨w', ls', ns'⟩ := r'
  simp only at hL hN hn
  subst hL hN
  refine RegroupStepL.mk hm (fitsR_not_mem hraw) ⟨_, hto, ?_⟩
  rw [normalize_canonK]
  exact hn

/-- **A declarative step under the laws is exactly a regrouping of the model**,
from a canonical record, any laws, kind and fold direction. -/
theorem regroupStepL_iff {ctx : Ctx} {dir : Dir} {laws : Laws} {r r' : RecR}
    (hok : ViewOK ctx.κ r.1) :
    RegroupStepL ctx dir laws r r' ↔ r' ∈ regroupRec ctx dir laws r :=
  ⟨regroupStepL_mem hok, regroupStepL_of_mem hok⟩

/-- Without laws, a step under the laws is the laws-free step of `RegroupChain.lean`. -/
theorem regroupStepL_free_iff {ctx : Ctx} {dir : Dir} {r r' : RecR} (hok : ViewOK ctx.κ r.1) :
    RegroupStepL ctx dir Laws.free r r' ↔ RegroupStep ctx dir r r' :=
  (regroupStepL_iff hok).trans
    ⟨regroupStep_of_mem hok, fun h => (regroupStep_mem hok h).1⟩

/-- Chains under the laws are the reachability of the model's regrouping. -/
theorem regroupChainL_iff {ctx : Ctx} {dir : Dir} {laws : Laws} {r₀ r : RecR}
    (hok : ViewOK ctx.κ r₀.1) :
    RegroupChainL ctx dir laws r₀ r ↔ Relation.ReflTransGen (RStep ctx dir laws) r₀ r := by
  constructor
  · intro h
    induction h using Relation.ReflTransGen.head_induction_on with
    | refl => exact Relation.ReflTransGen.refl
    | head hs _ ih =>
        have h1 := regroupStepL_mem hok hs
        exact Relation.ReflTransGen.head h1 (ih (viewOK_rstep hok h1))
  · intro h
    induction h using Relation.ReflTransGen.head_induction_on with
    | refl => exact Relation.ReflTransGen.refl
    | head hs _ ih =>
        exact Relation.ReflTransGen.head (regroupStepL_of_mem hok hs) (ih (viewOK_rstep hok hs))

/-- **The regrouped views under the laws are exactly the chains' views**
(`regroup_views_iff` for any laws): a view of `enumerateR` accepts `taken`
iff a chain of regroupings under the laws takes a walk record to a record of
that view needing at most `limit` classes, whose leaves and needed classes
`taken` satisfies. -/
theorem regroup_views_iff_laws {ctx : Ctx} {dir : Dir} {laws : Laws} {limit : Nat} {n : Node}
    {w : List (C × Nat)} {taken : List C} :
    (∃ d, (w, d) ∈ enumerateR ctx dir laws limit n ∧ d.acceptsE ctx.κ taken) ↔
      ∃ r₀ ∈ baseRecsR ctx dir laws n, ∃ r, RegroupChainL ctx dir laws r₀ r ∧ r.1 = w ∧
        r.2.2.length ≤ limit ∧ ∀ l ∈ r.alt, l.okE ctx.κ taken := by
  unfold enumerateR
  rw [acceptsE_enumerateFromR]
  constructor
  · rintro ⟨r, hr, hw, hacc⟩
    obtain ⟨hr, hlim⟩ := mem_withinLimit.1 hr
    obtain ⟨r₀, h₀, hch⟩ := (mem_regroupAll_iff_reach (baseGood_baseRecsR ctx dir laws n)).1 hr
    exact ⟨r₀, h₀, r, (regroupChainL_iff (viewOK_baseL h₀)).2 hch, hw, hlim, hacc⟩
  · rintro ⟨r₀, h₀, r, hch, hw, hlim, hacc⟩
    refine ⟨r, mem_withinLimit.2 ⟨?_, hlim⟩, hw, hacc⟩
    exact (mem_regroupAll_iff_reach (baseGood_baseRecsR ctx dir laws n)).2
      ⟨r₀, h₀, (regroupChainL_iff (viewOK_baseL h₀)).1 hch⟩

/-- **The matches of regrouped views under the laws, characterized**
(`regroup_match_iff` for any laws): an n-ary atom of any kind, any fold
direction and any laws of its operator holds under
`AtomSatG (Enumerator.regroup dir)` iff some chain of regroupings under the
laws takes a walk record of a stored node of the atom's class to a record on
whose view the binding matches the shallow pattern, the record needing at
most as many classes as the atom has items, with the item classes
satisfying its leaves and taking the classes it still needs. -/
theorem regroup_match_iff_laws {c : FCtx} {dir : Sym → Dir} {σ : Binding} {a : RAtom}
    {κ : FlatKind} (hκ : a.shape.flatKind = some κ) :
    AtomSatG (Enumerator.regroup dir) c σ a ↔
      ∃ id n, σ.node a.node = some id ∧ (id, n) ∈ c.G.nodes ∧
        σ.cls a.node = some (c.G.find id) ∧ n.op = a.op ∧
        ∃ r₀ ∈ baseRecsR (c.ctx a.op κ) (dir a.op) (c.laws a.op) n, ∃ r,
          RegroupChainL (c.ctx a.op κ) (dir a.op) (c.laws a.op) r₀ r ∧
          r.2.2.length ≤ a.elems.length ∧
          MatchN c.G a.shallow ⟨a.op, ofView κ r.1⟩ σ ∧
          ∀ l ∈ r.alt, l.okE κ (takenOf σ a.elems) := by
  unfold AtomSatG
  rw [hκ]
  constructor
  · rintro ⟨id, n, hnode, hmem, hcls, hop, w, d, hd, hm, hacc⟩
    obtain ⟨r₀, h₀, r, hch, rfl, hlim, hacc'⟩ :=
      (regroup_views_iff_laws (ctx := c.ctx a.op κ) (taken := takenOf σ a.elems)).1 ⟨d, hd, hacc⟩
    exact ⟨id, n, hnode, hmem, hcls, hop, r₀, h₀, r, hch, hlim, hm, hacc'⟩
  · rintro ⟨id, n, hnode, hmem, hcls, hop, r₀, h₀, r, hch, hlim, hm, hacc⟩
    obtain ⟨d, hd, hacc'⟩ :=
      (regroup_views_iff_laws (ctx := c.ctx a.op κ) (taken := takenOf σ a.elems)).2
        ⟨r₀, h₀, r, hch, rfl, hlim, hacc⟩
    exact ⟨id, n, hnode, hmem, hcls, hop, r.1, d, hd, hm, hacc'⟩

/-- **The engine's regrouped views under the laws are exactly the chains'
views** (`regroupSkip_views_iff` for any laws). -/
theorem regroupSkip_views_iff_laws {ctx : Ctx} {dir : Dir} {laws : Laws} {limit : Nat}
    {n : Node} {w : List (C × Nat)} {taken : List C} :
    (∃ d, (w, d) ∈ enumerateRSkip ctx dir laws limit n ∧ d.acceptsE ctx.κ taken) ↔
      ∃ r₀ ∈ baseRecsR ctx dir laws n, ∃ r, RegroupChainL ctx dir laws r₀ r ∧ r.1 = w ∧
        r.2.2.length ≤ limit ∧ ∀ l ∈ r.alt, l.okE ctx.κ taken :=
  enumerateRSkip_iff.trans regroup_views_iff_laws

/-- **The matches of the engine's regrouped views under the laws, characterized**
(`regroupSkip_match_iff` for any laws). -/
theorem regroupSkip_match_iff_laws {c : FCtx} {dir : Sym → Dir} {σ : Binding} {a : RAtom}
    {κ : FlatKind} (hκ : a.shape.flatKind = some κ) :
    AtomSatG (Enumerator.regroupSkip dir) c σ a ↔
      ∃ id n, σ.node a.node = some id ∧ (id, n) ∈ c.G.nodes ∧
        σ.cls a.node = some (c.G.find id) ∧ n.op = a.op ∧
        ∃ r₀ ∈ baseRecsR (c.ctx a.op κ) (dir a.op) (c.laws a.op) n, ∃ r,
          RegroupChainL (c.ctx a.op κ) (dir a.op) (c.laws a.op) r₀ r ∧
          r.2.2.length ≤ a.elems.length ∧
          MatchN c.G a.shallow ⟨a.op, ofView κ r.1⟩ σ ∧
          ∀ l ∈ r.alt, l.okE κ (takenOf σ a.elems) :=
  atomSat_regroupSkip_iff.trans (regroup_match_iff_laws hκ)

/-- **Completeness of the engine's regrouped views at the match level under the
laws** (`regroupSkip_match_complete` for any laws). -/
theorem regroupSkip_match_complete_laws {c : FCtx} {dir : Sym → Dir} {σ : Binding} {a : RAtom}
    {κ : FlatKind} (hκ : a.shape.flatKind = some κ) {id : NodeId} {n : Node}
    (hnode : σ.node a.node = some id) (hmem : (id, n) ∈ c.G.nodes)
    (hcls : σ.cls a.node = some (c.G.find id)) (hop : n.op = a.op) {r₀ r : RecR}
    (h₀ : r₀ ∈ baseRecsR (c.ctx a.op κ) (dir a.op) (c.laws a.op) n)
    (hch : RegroupChainL (c.ctx a.op κ) (dir a.op) (c.laws a.op) r₀ r)
    (hlim : r.2.2.length ≤ a.elems.length)
    (hacc : ∀ l ∈ r.alt, l.okE κ (takenOf σ a.elems))
    (hm : MatchN c.G a.shallow ⟨a.op, ofView κ r.1⟩ σ) :
    AtomSatG (Enumerator.regroupSkip dir) c σ a :=
  (regroupSkip_match_iff_laws hκ).2 ⟨id, n, hnode, hmem, hcls, hop, r₀, h₀, r, hch, hlim, hm, hacc⟩

/-- **Completeness of the flattened plan with the engine's regrouping, chains
under the laws**: a binding that satisfies every non-flattened atom and, for
every flattened atom, has a chain of regroupings under the operator's laws to
a view it matches with the leaves and needed classes satisfied, is emitted by
the engine's plan (`regroupSkip_plan_complete` with
`regroupSkip_match_iff_laws`). -/
theorem regroupSkip_plan_complete_laws {c : FCtx} {dir : Sym → Dir} {sig : Sym → Kind}
    {as : List RAtom} (r : Nat) (hw : QueryFWF c sig as) {σ' : Binding}
    (hsat : ∀ a ∈ as, match a.shape.flatKind with
      | none => AtomSat c.G σ' a
      | some κ =>
          ∃ id n, σ'.node a.node = some id ∧ (id, n) ∈ c.G.nodes ∧
            σ'.cls a.node = some (c.G.find id) ∧ n.op = a.op ∧
            ∃ r₀ ∈ baseRecsR (c.ctx a.op κ) (dir a.op) (c.laws a.op) n, ∃ r,
              RegroupChainL (c.ctx a.op κ) (dir a.op) (c.laws a.op) r₀ r ∧
              r.2.2.length ≤ a.elems.length ∧
              MatchN c.G a.shallow ⟨a.op, ofView κ r.1⟩ σ' ∧
              ∀ l ∈ r.alt, l.okE κ (takenOf σ' a.elems)) :
    ∃ env' ∈ runERSkip c dir (planF as ∅ r) EEnv.empty, Binding.Extends env'.σ σ' := by
  refine regroupSkip_plan_complete r hw (fun a ha => ?_)
  have h := hsat a ha
  revert h
  cases hκ : a.shape.flatKind with
  | none =>
      intro h
      unfold AtomSatG; rw [hκ]; exact h
  | some κ =>
      intro h
      exact (regroupSkip_match_iff_laws hκ).2 h

/-! ## Needed classes the laws drop -/

/-- **Every needed class is a class of its view**, on every record reachable
from the walk's: a regrouped record keeps only the needed classes its normal
form holds (`needsAfter`). So a match whose items take every class of the
view, as a pattern without a rest variable does, takes every needed class. -/
theorem reach_needs_held {ctx : Ctx} {dir : Dir} {laws : Laws} {n : Node} {r : RecR}
    (h : Reach ctx dir laws (baseRecsR ctx dir laws n) r) : ∀ c ∈ r.2.2, c ∈ r.1.map Prod.fst := by
  refine reach_induction (P := fun r => ∀ c ∈ r.2.2, c ∈ r.1.map Prod.fst) ?_ ?_ h
  · intro r hr c hc
    obtain ⟨-, -, -, hn⟩ := mem_baseRecsR_raw hr
    rw [hn] at hc; simp at hc
  · intro r r' _ h' c hc
    obtain ⟨g, grp, raw, hgg, hraw, hn, hL, hN⟩ := mem_regroupRec h'
    rw [hN] at hc
    unfold needsAfter at hc
    exact of_decide_eq_true (List.mem_filter.1 hc).2

/-- A needed class taken by the items whenever they take every class of the view. -/
theorem needs_taken_of_all {κ : FlatKind} {r : RecR} {taken : List C}
    (hheld : ∀ c ∈ r.2.2, c ∈ r.1.map Prod.fst) (hall : ∀ c ∈ r.1.map Prod.fst, c ∈ taken) :
    ∀ c ∈ r.2.2, (needLeaf c).okE κ taken :=
  fun c hc => (needLeaf_okE κ taken c).2 (hall c (hheld c hc))

theorem ofEntries_filter_class (u : C) :
    ∀ l : List (C × Nat), ofEntries (l.filter (fun e => e.1 ≠ u)) = (ofEntries l).filter (· ≠ u)
  | [] => by simp [ofEntries]
  | e :: l => by
      rw [List.filter_cons, ofEntries_cons, Multiset.filter_add, ← ofEntries_filter_class u l]
      split
      · rename_i h
        simp only [ne_eq, decide_eq_true_eq] at h
        rw [ofEntries_cons, Multiset.filter_eq_self.2]
        intro c hc
        rw [Multiset.eq_of_mem_replicate hc]
        exact h
      · rename_i h
        simp only [ne_eq, decide_eq_true_eq, not_not] at h
        rw [Multiset.filter_eq_nil.2, zero_add]
        intro c hc
        rw [Multiset.eq_of_mem_replicate hc, h]
        simp

/-! ### The counter-model: a group whose class is the unit -/

/-- `add` (op 7) AC with the identity `zero` (class 9); classes
`a, b, c, d = 1, …, 4`; `zero ∋ add{a, b}` (node 10); the root `add{a, b, c, d}`
(node 11, class 5). -/
def exUnitG : Graph :=
  ⟨[(10, ⟨7, .mset {1, 2}⟩), (11, ⟨7, .mset {1, 2, 3, 4}⟩)],
    fun id => if id = 10 then 9 else if id = 11 then 5 else id⟩

def exUnitCtx : Ctx := ⟨exUnitG, 7, .ac, fun _ => true⟩

def exUnitLaws : Laws := ⟨some 9, none, none⟩

def exUnitRoot : Node := ⟨7, .mset {1, 2, 3, 4}⟩

theorem exUnit_member {id : NodeId} {m : Node} {X : C} (h : exUnitCtx.IsMember id m X) :
    (m = ⟨7, .mset {1, 2}⟩ ∧ X = 9) ∨ (m = ⟨7, .mset {1, 2, 3, 4}⟩ ∧ X = 5) := by
  obtain ⟨hm, -, hX, -⟩ := h
  simp only [exUnitCtx, exUnitG, List.mem_cons, Prod.mk.injEq, List.mem_nil_iff, or_false] at hm
  rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · left; exact ⟨rfl, by simpa [exUnitCtx, exUnitG] using hX.symm⟩
  · right; exact ⟨rfl, by simpa [exUnitCtx, exUnitG] using hX.symm⟩

theorem ofEntries_normalizeList_exUnit (v : List (C × Nat)) :
    ofEntries (normalizeList .ac exUnitLaws v) = (ofEntries v).filter (· ≠ 9) := by
  show ofEntries ((coalesce v).filter (fun e => e.1 ≠ 9)) = _
  rw [ofEntries_filter_class, ofEntries_coalesce]

/-- An opening tree over classes with no member opens nothing. -/
theorem otl_no_members {ctx : Ctx} {k : Nat} {P : Finset C} {ks v : List (C × Nat)}
    {ls : List LeafL} {o : Nat} (h : OTL ctx k P ks v ls o)
    (hX : ∀ X ∈ ks.map Prod.fst, ∀ id m, ¬ ctx.IsMember id m X) : v = scale k ks := by
  induction h with
  | nil => rfl
  | keep _ ih =>
      rw [ih (fun X hx => hX X (List.mem_cons_of_mem _ hx))]
      rfl
  | opn _ hmem _ _ _ _ =>
      exact absurd hmem (hX _ (List.mem_cons_self ..) _ _)

/-- Every record reachable from the walk's records of the root has the
root's classes, or the view `{c, d}` and needs `zero`. -/
theorem exUnit_base : (Multiset.entries {1, 2, 3, 4}, [], []) ∈
    baseRecsR exUnitCtx .both exUnitLaws exUnitRoot := by
  have hw : normalizeList .ac exUnitLaws (scale 1 (Multiset.entries {1, 2, 3, 4})) =
      Multiset.entries {1, 2, 3, 4} := by
    rw [← entries_ofEntries_of_canonical (normalizeList_ac_canonical exUnitLaws _),
      ofEntries_normalizeList_exUnit, ofEntries_scale_one, ofEntries_entries]
    congr 1
  refine kept_mem_baseRecsR ?_
  show classify exUnitLaws.unit (normalizeList .ac exUnitLaws _) = _
  rw [show kids exUnitCtx.κ exUnitRoot.children = Multiset.entries {1, 2, 3, 4} from rfl, hw,
    classify_node_iff]
  refine ⟨rfl, fun h => ?_, fun c h => ?_⟩
  · have := congrArg (fun l => Multiset.card (ofEntries l)) h
    simp only [ofEntries_entries] at this
    revert this; decide
  · have := congrArg (fun l => Multiset.card (ofEntries l)) h
    simp only [ofEntries_entries] at this
    revert this; simp [ofEntries]

/-! ### The fixture's four matches -/

/-- The multiset arm of normalization after coalescing. -/
def postAC (laws : Laws) (L : List (C × Nat)) : List (C × Nat) :=
  match laws.inv with
  | none => clamp laws.nilpotent (dropUnit laws.unit L)
  | some inv => cancel inv (clamp laws.nilpotent (dropUnit laws.unit L))

theorem normalizeList_ac_post (laws : Laws) (v : List (C × Nat)) :
    normalizeList .ac laws v = postAC laws (coalesce v) := rfl

theorem coalesce_eq_of {v L : List (C × Nat)} (hc : Canonical L) (h : ofEntries v = ofEntries L) :
    coalesce v = L := by
  unfold coalesce; rw [h]; exact entries_ofEntries_of_canonical hc

/-- Normalizing a raw view whose canonical form is the list `L`. -/
theorem normalize_ac_of {laws : Laws} {v L w : List (C × Nat)} (hc : Canonical L)
    (h : ofEntries v = ofEntries L) (hw : classify laws.unit (postAC laws L) = .node w) :
    normalize .ac laws v = .node w := by
  unfold normalize; rw [normalizeList_ac_post, coalesce_eq_of hc h]; exact hw

theorem entries_eq_of {m : Multiset C} {L : List (C × Nat)} (hc : Canonical L)
    (h : ofEntries L = m) : Multiset.entries m = L := by
  rw [← h]; exact entries_ofEntries_of_canonical hc

/-- One AC regrouping under the laws from concrete multisets. -/
theorem regroupStepL_ac_of {ctx : Ctx} (hκ : ctx.κ = .ac) {dir : Dir} {laws : Laws} {r : RecR}
    {id : NodeId} {m : Node} {g : C} {M W : Multiset C} {w' : List (C × Nat)}
    (hm : ctx.IsMember id m g) (hkids : m.children = .mset M) (hW : ofEntries r.1 = W)
    (hg : g ∉ M) (h2 : 2 ≤ Multiset.card M) (hle : M ≤ W) (hne : M ≠ W)
    (hn : normalize .ac laws (Multiset.entries (W - M + {g})) = .node w') :
    RegroupStepL ctx dir laws r (w', r.2.1.map (addG g ((Multiset.entries M).map Prod.fst)
      (w'.map Prod.fst)), needsAfter g ((Multiset.entries M).map Prod.fst) (w'.map Prod.fst)
        r.2.2) := by
  have hk : kids ctx.κ m.children = Multiset.entries M := by rw [hκ, hkids]; rfl
  have h := @RegroupStepL.mk ctx dir laws r id m g w' hm
  rw [hk] at h
  refine h (by rwa [mem_entries_fst]) ⟨Multiset.entries (W - M + {g}), ?_, by rw [hκ]; exact hn⟩
  rw [hκ]
  show 2 ≤ _ ∧ _
  rw [ofEntries_entries, hW]
  exact ⟨h2, hle, hne, rfl⟩

/-- The view `{c, d}` (classes 3 and 4) of the engine's enumeration accepts the
item classes `[c, d]` once a walk record regroups to a record of that view
with no leaf and no need. -/
theorem found_of_step {ctx : Ctx} {laws : Laws} {n : Node} {r₀ : RecR} {w : List (C × Nat)}
    {taken : List C} {ls : List LeafF} {ns : List C} (h₀ : r₀ ∈ baseRecsR ctx .both laws n)
    (hs : RegroupStepL ctx .both laws r₀ (w, ls, ns)) (hlim : ns.length ≤ taken.length)
    (hacc : ∀ l ∈ RecR.alt (w, ls, ns), l.okE ctx.κ taken) :
    ∃ d, (w, d) ∈ enumerateRSkip ctx .both laws taken.length n ∧ d.acceptsE ctx.κ taken :=
  regroupSkip_views_iff_laws.2 ⟨r₀, h₀, _, Relation.ReflTransGen.single hs, rfl, hlim, hacc⟩

/-- **The identity: a regrouping into the unit is found.** With
`zero ∋ add{a, b}`, the view `{a, b, c, d}` regroups to `{zero, c, d}`,
normalized `{c, d}`; the record needs no class (the unit is dropped), so the
engine's enumeration has the view `{c, d}` accepting the item classes
`[c, d]`, and `(add x y)` binds `x = c, y = d`
(`flatten_regroup_laws_drop_need.egg`). The view denotes the node in every
model of the laws where the members denote their classes. -/
theorem regroup_drop_need_unit :
    (∃ d, ([(3, 1), (4, 1)], d) ∈ enumerateRSkip exUnitCtx .both exUnitLaws 2 exUnitRoot ∧
        d.acceptsE .ac [3, 4]) ∧
      ∀ (M : Type) [AddCommMonoid M] (den : C → M), ConsistentAC exUnitCtx den →
        LawsModelAC exUnitLaws den → den 3 + den 4 = den 1 + den 2 + den 3 + den 4 := by
  have hmem : exUnitCtx.IsMember 10 ⟨7, .mset {1, 2}⟩ 9 := by
    simp [Ctx.IsMember, exUnitCtx, exUnitG]
  have hstep : RegroupStepL exUnitCtx .both exUnitLaws (Multiset.entries {1, 2, 3, 4}, [], [])
      ([(3, 1), (4, 1)], [], []) := by
    have h := regroupStepL_ac_of (r := (Multiset.entries {1, 2, 3, 4}, [], []))
      (dir := .both) (w' := [(3, 1), (4, 1)]) rfl hmem rfl (ofEntries_entries _)
      (by decide) (by decide) (by decide) (by decide)
      (normalize_ac_of (laws := exUnitLaws) (L := [(3, 1), (4, 1), (9, 1)]) ⟨by decide, by decide⟩
        (by rw [ofEntries_entries]; decide) (by decide))
    have hns : needsAfter 9 ((Multiset.entries ({1, 2} : Multiset C)).map Prod.fst)
        ([((3 : C), 1), (4, 1)].map Prod.fst) [] = [] := by
      simp [needsAfter, mem_entries_fst, -List.mem_map]
    rw [hns, List.map_nil] at h
    exact h
  refine ⟨found_of_step (taken := [3, 4]) exUnit_base hstep (by decide)
    (fun l hl => by simp [RecR.alt] at hl), ?_⟩
  intro M _ den hc hl
  have hr : Reach exUnitCtx .both exUnitLaws (baseRecsR exUnitCtx .both exUnitLaws exUnitRoot)
      ([(3, 1), (4, 1)], [], []) :=
    ⟨_, exUnit_base, Relation.ReflTransGen.single (regroupStepL_mem
      (viewOK_baseL exUnit_base) hstep)⟩
  have := reach_den_ac rfl hc hl hr
  simp only [denAC, show kids FlatKind.ac exUnitRoot.children =
    Multiset.entries {1, 2, 3, 4} from rfl, ofEntries_entries] at this
  simp only [ofEntries, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Multiset.replicate_one, add_zero] at this
  simpa [add_assoc] using this

/-- The record of the root's stored view, every child kept. -/
theorem kept_base {ctx : Ctx} {laws : Laws} {n : Node} {M : Multiset C} {L : List (C × Nat)}
    (hκ : ctx.κ = .ac) (hkids : n.children = .mset M) (hc : Canonical L) (hL : ofEntries L = M)
    (hw : classify laws.unit (postAC laws L) = .node L) :
    (Multiset.entries M, [], []) ∈ baseRecsR ctx .both laws n := by
  have hk : kids ctx.κ n.children = Multiset.entries M := by rw [hκ, hkids]; rfl
  have he : Multiset.entries M = L := entries_eq_of hc hL
  have := kept_mem_baseRecsR (ctx := ctx) (dir := .both) (laws := laws) (n := n) (w := L) (by
    rw [hk, hκ]
    exact normalize_ac_of hc (by rw [ofEntries_scale_one, ofEntries_entries, hL]) hw)
  rwa [he]

/-- `xor` (op 7) AC, nilpotent of order 2 with the identity `zero` (class 9);
classes `a, b, c, d = 1, …, 4`, `G = 6 ∋ xor{a, b}` (node 10); the root
`xor{a, b, c, d, G}` (node 11, class 5). -/
def exNilG : Graph :=
  ⟨[(10, ⟨7, .mset {1, 2}⟩), (11, ⟨7, .mset {1, 2, 3, 4, 6}⟩)],
    fun id => if id = 10 then 6 else if id = 11 then 5 else id⟩

def exNilCtx : Ctx := ⟨exNilG, 7, .ac, fun _ => true⟩

def exNilLaws : Laws := ⟨some 9, some 2, none⟩

def exNilRoot : Node := ⟨7, .mset {1, 2, 3, 4, 6}⟩

/-- **`:nilpotent 2`: a regrouping whose count clamps to zero is found.**
`{a, b, c, d, G}` regroups to `{G:2, c, d}`, clamped `{c, d}`. -/
theorem regroup_drop_need_nilpotent :
    ∃ d, ([(3, 1), (4, 1)], d) ∈ enumerateRSkip exNilCtx .both exNilLaws 2 exNilRoot ∧
      d.acceptsE .ac [3, 4] := by
  have hb := kept_base (ctx := exNilCtx) (laws := exNilLaws) (n := exNilRoot)
    (L := [(1, 1), (2, 1), (3, 1), (4, 1), (6, 1)]) rfl rfl ⟨by decide, by decide⟩ (by decide)
    (by decide)
  have hmem : exNilCtx.IsMember 10 ⟨7, .mset {1, 2}⟩ 6 := by
    simp [Ctx.IsMember, exNilCtx, exNilG]
  have hstep : RegroupStepL exNilCtx .both exNilLaws (Multiset.entries {1, 2, 3, 4, 6}, [], [])
      ([(3, 1), (4, 1)], [], []) := by
    have h := regroupStepL_ac_of (r := (Multiset.entries {1, 2, 3, 4, 6}, [], []))
      (dir := .both) (w' := [(3, 1), (4, 1)]) rfl hmem rfl (ofEntries_entries _)
      (by decide) (by decide) (by decide) (by decide)
      (normalize_ac_of (laws := exNilLaws) (L := [(3, 1), (4, 1), (6, 2)]) ⟨by decide, by decide⟩
        (by rw [ofEntries_entries]; decide) (by decide))
    have hns : needsAfter 6 ((Multiset.entries ({1, 2} : Multiset C)).map Prod.fst)
        ([((3 : C), 1), (4, 1)].map Prod.fst) [] = [] := by
      simp [needsAfter, mem_entries_fst, -List.mem_map]
    rw [hns, List.map_nil] at h
    exact h
  exact found_of_step (taken := [3, 4]) hb hstep (by decide)
    (fun l hl => by simp [RecR.alt] at hl)

/-- `grp` (op 7) AC with the identity `zero` (class 9) and an inverse: classes
`a, b, c, d = 1, …, 4`, `G = 6 ∋ grp{a, b}` (node 10), `H = 7` the inverse
class of `G`; the root `grp{a, b, c, d, H}` (node 11, class 5). -/
def exInvG : Graph :=
  ⟨[(10, ⟨7, .mset {1, 2}⟩), (11, ⟨7, .mset {1, 2, 3, 4, 7}⟩)],
    fun id => if id = 10 then 6 else if id = 11 then 5 else id⟩

def exInvCtx : Ctx := ⟨exInvG, 7, .ac, fun _ => true⟩

def exInvLaws : Laws :=
  ⟨some 9, none, some (fun x => if x = 6 then some 7 else if x = 7 then some 6 else none)⟩

def exInvRoot : Node := ⟨7, .mset {1, 2, 3, 4, 7}⟩

/-- **`:inverse`: a regrouping whose class cancels is found.**
`{a, b, c, d, H}` regroups to `{G, H, c, d}`, cancelled `{c, d}`. -/
theorem regroup_drop_need_inverse :
    ∃ d, ([(3, 1), (4, 1)], d) ∈ enumerateRSkip exInvCtx .both exInvLaws 2 exInvRoot ∧
      d.acceptsE .ac [3, 4] := by
  have hb := kept_base (ctx := exInvCtx) (laws := exInvLaws) (n := exInvRoot)
    (L := [(1, 1), (2, 1), (3, 1), (4, 1), (7, 1)]) rfl rfl ⟨by decide, by decide⟩ (by decide)
    (by decide)
  have hmem : exInvCtx.IsMember 10 ⟨7, .mset {1, 2}⟩ 6 := by
    simp [Ctx.IsMember, exInvCtx, exInvG]
  have hstep : RegroupStepL exInvCtx .both exInvLaws (Multiset.entries {1, 2, 3, 4, 7}, [], [])
      ([(3, 1), (4, 1)], [], []) := by
    have h := regroupStepL_ac_of (r := (Multiset.entries {1, 2, 3, 4, 7}, [], []))
      (dir := .both) (w' := [(3, 1), (4, 1)]) rfl hmem rfl (ofEntries_entries _)
      (by decide) (by decide) (by decide) (by decide)
      (normalize_ac_of (laws := exInvLaws) (L := [(3, 1), (4, 1), (6, 1), (7, 1)]) ⟨by decide, by decide⟩
        (by rw [ofEntries_entries]; decide) (by decide))
    have hns : needsAfter 6 ((Multiset.entries ({1, 2} : Multiset C)).map Prod.fst)
        ([((3 : C), 1), (4, 1)].map Prod.fst) [] = [] := by
      simp [needsAfter, mem_entries_fst, -List.mem_map]
    rw [hns, List.map_nil] at h
    exact h
  exact found_of_step (taken := [3, 4]) hb hstep (by decide)
    (fun l hl => by simp [RecR.alt] at hl)

/-- `mul` (op 7) AC with the identity `one` (class 9); classes
`a, b, c, d, f = 1, …, 5`, `X = 6 ∋ mul{a, b}` (node 10),
`one ∋ mul{a, b, c}` (node 12); the root `mul{X, c, d, f}` (node 11, class 8). -/
def exLeafG : Graph :=
  ⟨[(10, ⟨7, .mset {1, 2}⟩), (11, ⟨7, .mset {3, 4, 5, 6}⟩), (12, ⟨7, .mset {1, 2, 3}⟩)],
    fun id => if id = 10 then 6 else if id = 11 then 8 else if id = 12 then 9 else id⟩

def exLeafCtx : Ctx := ⟨exLeafG, 7, .ac, fun _ => true⟩

def exLeafRoot : Node := ⟨7, .mset {3, 4, 5, 6}⟩

/-- **A leaf that gains a dropped class is flagged.** The walk opens `X` in
`mul{X, c, d, f}`: the view `{a, b, c, d, f}` with the leaf `(X, [a, b])`. The
group `{a, b, c}` of class `one` regroups it to `{one, d, f}`, normalized
`{d, f}`; the leaf gains `one`, which the view does not hold, so it is flagged
non-inert, and the record needs nothing: the view `{d, f}` accepts the item
classes `[d, f]`, and `(mul x y)` binds `x = d, y = f`
(`flatten_regroup_laws_drop_need.egg`). -/
theorem regroup_drop_need_leaf :
    ∃ d, ([(4, 1), (5, 1)], d) ∈ enumerateRSkip exLeafCtx .both exUnitLaws 2 exLeafRoot ∧
      d.acceptsE .ac [4, 5] := by
  have hk6 : kids exLeafCtx.κ (Children.mset {1, 2}) = [(1, 1), (2, 1)] :=
    entries_eq_of ⟨by decide, by decide⟩ (by decide)
  have hkr : kids exLeafCtx.κ exLeafRoot.children = [(3, 1), (4, 1), (5, 1), (6, 1)] :=
    entries_eq_of ⟨by decide, by decide⟩ (by decide)
  have hm6 : exLeafCtx.IsMember 10 ⟨7, .mset {1, 2}⟩ 6 := by
    simp [Ctx.IsMember, exLeafCtx, exLeafG]
  have hm9 : exLeafCtx.IsMember 12 ⟨7, .mset {1, 2, 3}⟩ 9 := by
    simp [Ctx.IsMember, exLeafCtx, exLeafG]
  have hinner : OTL exLeafCtx (1 * 1) (insert 6 ∅) (kids exLeafCtx.κ (Children.mset {1, 2}))
      [(1, 1 * 1 * 1), (2, 1 * 1 * 1)] [] 0 := by
    rw [hk6]; exact OTL.keep (OTL.keep OTL.nil)
  have hv : RawViewL exLeafCtx exLeafRoot
      [(3, 1 * 1), (4, 1 * 1), (5, 1 * 1), (1, 1 * 1 * 1), (2, 1 * 1 * 1)]
      (leafifyL 6 (1 * 1) [(1, 1 * 1 * 1), (2, 1 * 1 * 1)] [] ++ []) (0 + 0 + 1) := by
    unfold RawViewL ViewNodeL
    rw [hkr]
    exact OTL.keep (OTL.keep (OTL.keep (OTL.opn (by simp) hm6 hinner OTL.nil)))
  set W : List (C × Nat) := [(1, 1), (2, 1), (3, 1), (4, 1), (5, 1)]
  have hn : normalize exLeafCtx.κ exUnitLaws
      [(3, 1 * 1), (4, 1 * 1), (5, 1 * 1), (1, 1 * 1 * 1), (2, 1 * 1 * 1)] = .node W :=
    normalize_ac_of (laws := exUnitLaws) (L := W) ⟨by decide, by decide⟩ (by decide) (by decide)
  set ls := leafifyL 6 (1 * 1) [(1, 1 * 1 * 1), (2, 1 * 1 * 1)] [] ++ []
  have h₀ : (W, flagLeaves exLeafCtx.κ exUnitLaws
      [(3, 1 * 1), (4, 1 * 1), (5, 1 * 1), (1, 1 * 1 * 1), (2, 1 * 1 * 1)] ls, []) ∈
      baseRecsR exLeafCtx .both exUnitLaws exLeafRoot := by
    unfold baseRecsR
    rw [rawRecordsLD_both]
    exact List.mem_map.2 ⟨_, mem_rawRecordsL.2 ⟨_, ls, _, hv, hn, rfl⟩, rfl⟩
  have hW : ofEntries W = {1, 2, 3, 4, 5} := by decide
  have hstep := regroupStepL_ac_of (r := (W, flagLeaves exLeafCtx.κ exUnitLaws
      [(3, 1 * 1), (4, 1 * 1), (5, 1 * 1), (1, 1 * 1 * 1), (2, 1 * 1 * 1)] ls, []))
    (dir := .both) (laws := exUnitLaws) (w' := [(4, 1), (5, 1)]) rfl hm9 rfl hW
    (by decide) (by decide) (by decide) (by decide)
    (normalize_ac_of (laws := exUnitLaws) (L := [(4, 1), (5, 1), (9, 1)]) ⟨by decide, by decide⟩
      (by rw [ofEntries_entries]; decide) (by decide))
  have hns : needsAfter 9 ((Multiset.entries ({1, 2, 3} : Multiset C)).map Prod.fst)
      ([((4 : C), 1), (5, 1)].map Prod.fst) [] = [] := by
    simp [needsAfter, mem_entries_fst, -List.mem_map]
  rw [hns] at hstep
  refine found_of_step (taken := [4, 5]) h₀ hstep (by decide) (fun l hl => ?_)
  -- The only leaf gains `one` and is flagged; nothing is needed.
  simp only [RecR.alt, List.map_nil, List.append_nil, List.mem_map] at hl
  obtain ⟨l₀, hl₀, rfl⟩ := hl
  simp only [flagLeaves, ls, leafifyL, ite_true, List.append_nil, List.map_cons, List.map_nil,
    List.mem_singleton] at hl₀
  subst hl₀
  refine Or.inr (Or.inr ?_)
  have hcond : (9 : C) ∉ (⟨6, 1 * 1, [(1, 1 * 1 * 1), (2, 1 * 1 * 1)]⟩ : LeafL).g ∧
      (⟨6, 1 * 1, [(1, 1 * 1 * 1), (2, 1 * 1 * 1)]⟩ : LeafL).g.any
        (fun c => decide (c ∈ (Multiset.entries ({1, 2, 3} : Multiset C)).map Prod.fst)) = true := by
    refine ⟨by simp [LeafL.g], ?_⟩
    simp only [List.any_eq_true, decide_eq_true_eq, mem_entries_fst]
    exact ⟨1, by simp [LeafL.g], by decide⟩
  unfold addG
  simp only [hcond]
  simp

/-! ### Beyond chains: inserting the unit

A chain only opens (the walk) and contracts (regrouping). Under laws, a term
equal to the node may need an *insertion*: `a + c = a + c + zero` and
`zero ∋ add{b, d}` give `a + c = (a + b) + (c + d)`. No chain inserts the
unit, a cancel pair or `k` copies under `:nilpotent k`, so such a normal form
is never a view, even when every class of it is present. -/

/-- `add` (op 7) AC with the identity `zero` (class 9); classes
`a, b, c, d = 1, …, 4`; `zero ∋ add{b, d}` (node 10), `G = 6 ∋ add{a, b}`
(node 12), `K = 8 ∋ add{c, d}` (node 13); the root `add{a, c}` (node 11,
class 5). -/
def exInsG : Graph :=
  ⟨[(10, ⟨7, .mset {2, 4}⟩), (11, ⟨7, .mset {1, 3}⟩), (12, ⟨7, .mset {1, 2}⟩),
      (13, ⟨7, .mset {3, 4}⟩)],
    fun id => if id = 10 then 9 else if id = 11 then 5 else if id = 12 then 6
      else if id = 13 then 8 else id⟩

def exInsCtx : Ctx := ⟨exInsG, 7, .ac, fun _ => true⟩

def exInsRoot : Node := ⟨7, .mset {1, 3}⟩

theorem exIns_member {id : NodeId} {m : Node} {X : C} (h : exInsCtx.IsMember id m X) :
    (m = ⟨7, .mset {2, 4}⟩ ∧ X = 9) ∨ (m = ⟨7, .mset {1, 3}⟩ ∧ X = 5) ∨
      (m = ⟨7, .mset {1, 2}⟩ ∧ X = 6) ∨ (m = ⟨7, .mset {3, 4}⟩ ∧ X = 8) := by
  obtain ⟨hm, -, hX, -⟩ := h
  simp only [exInsCtx, exInsG, List.mem_cons, Prod.mk.injEq, List.mem_nil_iff, or_false] at hm
  rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inl ⟨rfl, by simpa [exInsCtx, exInsG] using hX.symm⟩
  · exact Or.inr (Or.inl ⟨rfl, by simpa [exInsCtx, exInsG] using hX.symm⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨rfl, by simpa [exInsCtx, exInsG] using hX.symm⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨rfl, by simpa [exInsCtx, exInsG] using hX.symm⟩))

/-- Every record reachable from the walk's records of `add{a, c}` has the view `{a, c}`. -/
theorem exIns_reach {r₀ r : RecR} (h₀ : r₀ ∈ baseRecsR exInsCtx .both exUnitLaws exInsRoot)
    (hch : RegroupChainL exInsCtx .both exUnitLaws r₀ r) : ofEntries r.1 = {1, 3} := by
  induction hch with
  | refl =>
      obtain ⟨v, ls, o, hv, hn⟩ := mem_baseRecsR_both h₀
      have hv' : v = scale 1 (Multiset.entries {1, 3}) := by
        refine otl_no_members hv (fun X hx id m hm => ?_)
        rw [mem_entries_fst] at hx
        rcases exIns_member hm with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;>
          revert hx <;> decide
      rw [normalize_node_eq hn, hv']
      show ofEntries (normalizeList .ac exUnitLaws _) = _
      rw [ofEntries_normalizeList_exUnit, ofEntries_scale_one, ofEntries_entries]
      decide
  | tail _ hs ih =>
      have hk : ∀ m : Multiset C, ofEntries (kids exInsCtx.κ (Children.mset m)) = m :=
        fun m => ofEntries_entries m
      obtain ⟨hm, -, ⟨w₀, hto, -⟩⟩ := hs
      obtain ⟨-, hsub, hne, -⟩ := hto
      rcases exIns_member hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        dsimp only at hsub hne <;> simp only [hk] at hsub hne <;> rw [ih] at hsub hne
      · exact absurd hsub (by decide)
      · exact absurd rfl hne
      · exact absurd hsub (by decide)
      · exact absurd hsub (by decide)

theorem denAC_kids_pair {M : Type*} [AddCommMonoid M] (den : C → M) (x y : C) :
    denAC den (kids .ac (.mset {x, y})) = den x + den y := by
  simp [denAC, kids, ofEntries_entries]

/-- **Counter-model: a normal form reached only by inserting the unit**
(`:identity`). With `zero ∋ add{b, d}`, `G ∋ add{a, b}` and `K ∋ add{c, d}`,
the node `add{a, c}` equals `add{G, K}` in every model of the laws where the
members denote their classes, and `{G, K}` is a normal form over classes
present; but no chain from the walk reaches it (every reachable view is
`{a, c}`), so the engine has no view `{G, K}` and `(add x y)` never binds
`x = G, y = K` (`flatten_regroup_laws_insert.egg`). The same holds for a
cancel pair (`G ∋ grp{a, b}`, `K ∋ grp{c, neg b}`) and for `k` copies under
`:nilpotent k`. -/
theorem regroup_insert_unit_lost :
    (∀ (M : Type) [AddCommMonoid M] (den : C → M), ConsistentAC exInsCtx den →
        LawsModelAC exUnitLaws den → den 6 + den 8 = den 1 + den 3) ∧
      ∀ d, (Multiset.entries {6, 8}, d) ∉
        enumerateRSkip exInsCtx .both exUnitLaws 2 exInsRoot := by
  refine ⟨fun M _ den hc hl => ?_, fun d hd => ?_⟩
  · have h0 := hl.unit 9 rfl
    have h9 := hc 10 ⟨7, .mset {2, 4}⟩ 9 (by simp [Ctx.IsMember, exInsCtx, exInsG])
    have h6 := hc 12 ⟨7, .mset {1, 2}⟩ 6 (by simp [Ctx.IsMember, exInsCtx, exInsG])
    have h8 := hc 13 ⟨7, .mset {3, 4}⟩ 8 (by simp [Ctx.IsMember, exInsCtx, exInsG])
    rw [denAC_kids_pair] at h9 h6 h8
    rw [h6, h8, ← add_zero (den 1 + den 3), ← h0, h9]
    abel
  · obtain ⟨r, ⟨r₀, h₀, hch⟩, hw⟩ := reach_of_mem_enumerateRSkip hd
    have := exIns_reach h₀ ((regroupChainL_iff (viewOK_baseL h₀)).2 hch)
    rw [hw, ofEntries_entries] at this
    revert this; decide

/-! ### Beyond chains: an idempotent group kept beside its class -/

/-- `S` (op 8) ACI; classes `a, b, c = 1, 2, 3`; `G = 4 ∋ S{a, b}` (node 10);
the root `S{a, b, c}` (node 11, class 5). -/
def exAciG : Graph :=
  ⟨[(10, ⟨8, .set {1, 2}⟩), (11, ⟨8, .set {1, 2, 3}⟩)],
    fun id => if id = 10 then 4 else if id = 11 then 5 else id⟩

def exAciCtx : Ctx := ⟨exAciG, 8, .aci, fun _ => true⟩

def exAciRoot : Node := ⟨8, .set {1, 2, 3}⟩

theorem exAci_member {id : NodeId} {m : Node} {X : C} (h : exAciCtx.IsMember id m X) :
    (m = ⟨8, .set {1, 2}⟩ ∧ X = 4) ∨ (m = ⟨8, .set {1, 2, 3}⟩ ∧ X = 5) := by
  obtain ⟨hm, -, hX, -⟩ := h
  simp only [exAciCtx, exAciG, List.mem_cons, Prod.mk.injEq, List.mem_nil_iff, or_false] at hm
  rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · left; exact ⟨rfl, by simpa [exAciCtx, exAciG] using hX.symm⟩
  · right; exact ⟨rfl, by simpa [exAciCtx, exAciG] using hX.symm⟩

theorem toFinset_kids_aci (s : Finset C) :
    ((kids .aci (.set s)).map Prod.fst).toFinset = s := by
  simp only [kids, List.map_map]
  rw [show (Prod.fst ∘ fun c : C => (c, 1)) = id from rfl, List.map_id, Finset.sort_toFinset]

/-- Every record reachable from the walk's records of `S{a, b, c}` has the
classes `{a, b, c}` or `{c, G}`. -/
theorem exAci_reach {r₀ r : RecR} (h₀ : r₀ ∈ baseRecsR exAciCtx .both Laws.free exAciRoot)
    (hch : RegroupChainL exAciCtx .both Laws.free r₀ r) :
    (r.1.map Prod.fst).toFinset = {1, 2, 3} ∨ (r.1.map Prod.fst).toFinset = {3, 4} := by
  induction hch with
  | refl =>
      left
      obtain ⟨v, ls, o, hv, hn⟩ := mem_baseRecsR_both h₀
      have hv' : v = scale 1 (kids .aci (.set {1, 2, 3})) := by
        refine otl_no_members hv (fun X hx id m hm => ?_)
        have hx' : X ∈ ((kids .aci (.set {1, 2, 3})).map Prod.fst).toFinset :=
          List.mem_toFinset.2 hx
        rw [toFinset_kids_aci] at hx'
        rcases exAci_member hm with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> revert hx' <;> decide
      rw [(normalize_free_node.1 hn).1, hv']
      show ((dedupAci _).map Prod.fst).toFinset = _
      rw [toFinset_map_fst_dedupAci]
      have : (scale 1 (kids .aci (.set {1, 2, 3}))).map Prod.fst =
          (kids .aci (.set {1, 2, 3})).map Prod.fst := by simp [scale]
      rw [this, toFinset_kids_aci]
  | tail _ hs ih =>
      obtain ⟨hm, -, ⟨w₀, hto, hn⟩⟩ := hs
      obtain ⟨-, hsub, hne, -, rfl⟩ := hto
      rw [(normalize_free_node.1 hn).1]
      show ((dedupAci _).map Prod.fst).toFinset = _ ∨ ((dedupAci _).map Prod.fst).toFinset = _
      rw [toFinset_map_fst_dedupAci, List.map_map]
      rw [show (Prod.fst ∘ fun c : C => (c, 1)) = id from rfl, List.map_id, Finset.sort_toFinset]
      have hk : ∀ s, ((kids exAciCtx.κ (Children.set s)).map Prod.fst).toFinset = s :=
        toFinset_kids_aci
      rcases exAci_member hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        dsimp only at hsub hne ⊢ <;>
        simp only [hk] at hsub hne ⊢
      · rcases ih with h | h <;> rw [h] at hsub hne ⊢
        · right; decide
        · exact absurd hsub (by decide)
      · rcases ih with h | h <;> rw [h] at hsub hne ⊢
        · exact absurd rfl hne
        · exact absurd hsub (by decide)

/-- **Counter-model: an idempotent group kept beside its class** (ACI). With
`G ∋ S{a, b}`, the node `S{a, b, c}` equals `S{a, c, G}` in every join
semilattice where the members denote their classes (`a ⊔ c ⊔ (a ⊔ b)`), and
`{a, c, G}` is a canonical set over classes present; but regrouping replaces
the group (`{c, G}`) and never keeps one of its members beside `G`, so the
engine has no view `{a, c, G}` and `(S x y z)` never binds `x = a, y = c,
z = G` (`flatten_regroup_laws_idem.egg`). -/
theorem regroup_idem_overlap_lost :
    (∀ (M : Type) [SemilatticeSup M] [OrderBot M] (den : C → M), ConsistentACI exAciCtx den →
        den 1 ⊔ den 3 ⊔ den 4 = den 1 ⊔ den 2 ⊔ den 3) ∧
      ∀ d, ([(1, 1), (3, 1), (4, 1)], d) ∉ enumerateRSkip exAciCtx .both Laws.free 3 exAciRoot := by
  refine ⟨fun M _ _ den hc => ?_, fun d hd => ?_⟩
  · have h4 := hc 10 ⟨8, .set {1, 2}⟩ 4 (by simp [Ctx.IsMember, exAciCtx, exAciG])
    have hd : denACI den (kids .aci (.set {1, 2})) = den 1 ⊔ den 2 := by
      unfold denACI
      rw [toFinset_ofEntries_of_pos (kids_pos _ _), toFinset_kids_aci]
      simp
    rw [hd] at h4
    rw [h4]
    apply le_antisymm <;>
      simp [sup_le_iff, le_sup_left, le_sup_right, le_sup_of_le_left]
  · obtain ⟨r, ⟨r₀, h₀, hch⟩, hw⟩ := reach_of_mem_enumerateRSkip hd
    rcases exAci_reach h₀ ((regroupChainL_iff (viewOK_baseL h₀)).2 hch) with h | h <;>
      rw [hw] at h <;> revert h <;> decide

end Semper.EMatch.Flatten
