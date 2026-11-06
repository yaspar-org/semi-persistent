import SemperProofs.EMatch.Flatten.RegroupSkip
import SemperProofs.EMatch.Flatten.RegroupSound

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

## Not covered here

The characterization is relative to chains: openings by the walk, then
contractions by regrouping. Whether chains reach every match modulo the laws
over the classes present is not addressed in this file.
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
    (groupsOfEngine_sup ctx)).1 r (mem_withinLimit.1 hr).1, rfl⟩

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
        (w', r.2.1.map (addG g ((kids ctx.κ m.children).map Prod.fst)),
          needsAfter g ((kids ctx.κ m.children).map Prod.fst) r.2.2)

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

/-- **One declarative step under the laws is one regrouping of the model.** -/
theorem regroupStepL_mem {ctx : Ctx} {dir : Dir} {laws : Laws} {r r' : RecR}
    (hok : ViewOK ctx.κ r.1) (h : RegroupStepL ctx dir laws r r') :
    r' ∈ regroupRec ctx dir laws r := by
  obtain ⟨hm, hg, ⟨w₀, hto, hn⟩⟩ := h
  have hmem := (regroupStep_mem hok (RegroupStep.mk hm hg hto)).1
  obtain ⟨g', grp', raw', hgg', hraw', hn', hL, hN⟩ := mem_regroupRec hmem
  have hw₀ : w₀ = canonK ctx.κ raw' := (normalize_free_node.1 hn').1
  have hn'' := hn
  rw [hw₀, normalize_canonK] at hn''
  have := regroupRec_of hgg' hraw' hn''
  simp only at hL hN
  rw [← hL, ← hN] at this
  exact this

/-- **Every regrouping of the model under the laws is a declarative step.** -/
theorem regroupStepL_of_mem {ctx : Ctx} {dir : Dir} {laws : Laws} {r r' : RecR}
    (hok : ViewOK ctx.κ r.1) (h : r' ∈ regroupRec ctx dir laws r) :
    RegroupStepL ctx dir laws r r' := by
  obtain ⟨g, grp, raw, hgg, hraw, hn, hL, hN⟩ := mem_regroupRec h
  have hp := (fitsR_shrink (viewGood_of_viewOK hok) hraw).2
  have hfree := normalize_free_of_node hp hn
  have hs := regroupStep_of_mem hok (regroupRec_of hgg hraw hfree)
  generalize hx : (canonK ctx.κ raw, r.2.1.map (addG g (grp.map Prod.fst)),
    needsAfter g (grp.map Prod.fst) r.2.2) = x at hs
  obtain ⟨hm, hg, hto⟩ := hs
  simp only [Prod.mk.injEq] at hx
  obtain ⟨h1, h2, h3⟩ := hx
  obtain ⟨w', ls', ns'⟩ := r'
  simp only at hL hN hn
  subst hL hN
  rw [h2, h3]
  refine RegroupStepL.mk hm hg ⟨_, hto, ?_⟩
  rw [← h1, normalize_canonK]
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

end Semper.EMatch.Flatten
