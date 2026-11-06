import SemperProofs.EMatch.Flatten.Regroup
import SemperProofs.EMatch.Flatten.Fold

/-!
# `:flatten`: regrouped views denote the node's term

A regrouped view replaces a group of entries by the class `g` of an
`f`-member over exactly that group. In the theory `g` equals `f(group)`, so
the regrouped view spells a term equal to the view's. This file proves it
in the denotational form of `Fold.lean`: a denotation of the classes is
*consistent* when every `f`-member of a class denotes the class.

* `regroup_step_sound_ac`, `_aci`, `_assoc`: one regrouping keeps the
  denotation, into a commutative monoid (AC), a join semilattice with a
  bottom (ACI) and a monoid (`:assoc`);
* `regroup_views_sound_ac`, `_aci`, `_assoc`: every view of the enumeration
  with regrouped views (`enumerateR`, laws-free operator) denotes the node:
  the walk's views by induction on the opening tree, the regrouped ones by
  the step lemmas, normalization by `coalesce`, `dedupAci` and the identity;
* `regroup_step_sound_left`, `_right`: on a left fold, regrouping the
  prefix keeps the left fold; on a right fold, the suffix keeps the right
  fold (`lfold_splice`, `rfold_splice`);
* `regroup_off_spine_unsound`: regrouping a run off the spine of a left fold
  (`[a, b, c]` read as `[a, K]` with `K ∋ Sub[b, c]`) changes the left fold,
  the counter-model of `Fold.lean`; the left-fold `fits` does not produce
  that view.
-/

namespace Semper.EMatch.Flatten

open Semper.EMatch

/-! ## Subtracting a group -/

theorem count_ofEntries_map_sub {view : List (C × Nat)} (hnd : (view.map Prod.fst).Nodup)
    {c : C} {x k : Nat} (hc : (c, x) ∈ view) (hk : k ≤ x) :
    ofEntries (view.map (fun e => if e.1 = c then (c, x - k) else e)) +
      Multiset.replicate k c = ofEntries view := by
  set view' := view.map (fun e => if e.1 = c then (c, x - k) else e) with hv'
  have hnd' : (view'.map Prod.fst).Nodup := by
    rw [hv', List.map_map]
    convert hnd using 2
    funext e
    simp only [Function.comp_apply]
    split <;> simp_all
  ext a
  rw [Multiset.count_add, Multiset.count_replicate]
  by_cases hac : a = c
  · subst hac
    have hm : (a, x - k) ∈ view' := List.mem_map.2 ⟨(a, x), hc, by simp⟩
    rw [count_ofEntries_of_nodup hnd' hm, count_ofEntries_of_nodup hnd hc, if_pos rfl]
    simp only
    omega
  · rw [if_neg (Ne.symm hac), Nat.add_zero]
    by_cases ha : a ∈ view.map Prod.fst
    · obtain ⟨e, he, rfl⟩ := List.mem_map.1 ha
      have hm : e ∈ view' := List.mem_map.2 ⟨e, he, by simp [hac]⟩
      rw [count_ofEntries_of_nodup hnd' hm, count_ofEntries_of_nodup hnd he]
    · have ha' : a ∉ view'.map Prod.fst := by
        rw [hv', List.map_map]
        intro h
        obtain ⟨e, he, hea⟩ := List.mem_map.1 h
        simp only [Function.comp_apply] at hea
        split at hea
        · exact hac hea.symm
        · exact ha (List.mem_map.2 ⟨e, he, hea⟩)
      rw [count_ofEntries_eq_zero_of_notMem ha', count_ofEntries_eq_zero_of_notMem ha]

/-- `subEntries` subtracts the group: the rest and the group make the view. -/
theorem subEntries_spec :
    ∀ (norm view : List (C × Nat)) (v : List (C × Nat)), (view.map Prod.fst).Nodup →
      subEntries view norm = some v → ofEntries v + ofEntries norm = ofEntries view
  | [], view, v, _, h => by
      simp only [subEntries, Option.some.injEq] at h
      subst h
      have := ofEntries_filter_nonzero view
      rw [show ofEntries ([] : List (C × Nat)) = 0 from rfl, add_zero]
      convert this using 3
  | (c, k) :: rest, view, v, hnd, h => by
      simp only [subEntries] at h
      revert h
      cases hf : view.find? (fun e => decide (e.1 = c)) with
      | none => simp
      | some e =>
          obtain ⟨c', x⟩ := e
          have hmem := List.mem_of_find?_eq_some hf
          have hcc : c' = c := by simpa using List.find?_some hf
          subst hcc
          simp only
          split
          · rename_i hk
            intro h
            have hnd' : ((view.map (fun e => if e.1 = c' then (c', x - k) else e)).map
                Prod.fst).Nodup := by
              rw [List.map_map]
              convert hnd using 2
              funext e
              simp only [Function.comp_apply]
              split <;> simp_all
            have ih := subEntries_spec rest _ v hnd' h
            rw [ofEntries_cons, ← count_ofEntries_map_sub hnd hmem hk, ← ih]
            simp only
            abel
          · simp

theorem fitsR_ac {dir : Dir} {view : List (C × Nat)} {g : C} {grp raw : List (C × Nat)}
    (h : raw ∈ fitsR .ac dir view g grp) :
    g ∉ grp.map Prod.fst ∧ ∃ v, subEntries view (coalesce grp) = some v ∧ raw = v ++ [(g, 1)] := by
  unfold fitsR at h
  split at h
  · simp at h
  · rename_i hg
    refine ⟨fun hm => hg (by simpa using hm), ?_⟩
    simp only [groupNorm] at h
    revert h
    cases hs : subEntries view (coalesce grp) with
    | none => simp
    | some v =>
        intro h
        refine ⟨v, rfl, ?_⟩
        split_ifs at h <;> simp_all

theorem fitsR_aci {dir : Dir} {view : List (C × Nat)} {g : C} {grp raw : List (C × Nat)}
    (h : raw ∈ fitsR .aci dir view g grp) :
    g ∉ grp.map Prod.fst ∧ ∃ v, subEntries view (dedupAci grp) = some v ∧ raw = v ++ [(g, 1)] := by
  unfold fitsR at h
  split at h
  · simp at h
  · rename_i hg
    refine ⟨fun hm => hg (by simpa using hm), ?_⟩
    simp only [groupNorm] at h
    revert h
    cases hs : subEntries view (dedupAci grp) with
    | none => simp
    | some v =>
        intro h
        refine ⟨v, rfl, ?_⟩
        split_ifs at h <;> simp_all

theorem fitsR_assoc {dir : Dir} {view : List (C × Nat)} {g : C} {grp raw : List (C × Nat)}
    (h : raw ∈ fitsR .assoc dir view g grp) :
    2 ≤ grp.length ∧ grp.length < view.length ∧ ∃ p, spineRun dir p grp.length view.length = true ∧
      ((view.drop p).take grp.length).map Prod.fst = grp.map Prod.fst ∧
      raw = view.take p ++ (g, 1) :: view.drop (p + grp.length) := by
  unfold fitsR at h
  split at h
  · simp at h
  · simp only at h
    split at h
    · simp at h
    · rename_i hk
      refine ⟨by omega, by omega, ?_⟩
      obtain ⟨p, -, h⟩ := List.mem_filterMap.1 h
      split at h
      · rename_i hc
        simp only [Bool.and_eq_true, beq_iff_eq] at hc
        simp only [Option.some.injEq] at h
        exact ⟨p, hc.1, hc.2, h.symm⟩
      · simp at h

theorem normalize_free_ac {raw w : List (C × Nat)} (h : normalize .ac Laws.free raw = .node w) :
    w = coalesce raw := by
  unfold normalize at h
  rw [classify_node_iff] at h
  exact h.1.symm

theorem normalize_free_aci {raw w : List (C × Nat)} (h : normalize .aci Laws.free raw = .node w) :
    w = dedupAci raw := by
  unfold normalize at h
  rw [classify_node_iff] at h
  exact h.1.symm

theorem normalize_free_assoc {raw w : List (C × Nat)}
    (h : normalize .assoc Laws.free raw = .node w) : w = raw := by
  unfold normalize at h
  rw [classify_node_iff] at h
  exact h.1.symm

theorem rawRecordsLD_both (ctx : Ctx) (laws : Laws) (n : Node) :
    rawRecordsLD ctx .both laws n = rawRecordsL ctx laws n := by
  unfold rawRecordsLD rawRecordsL
  rw [rawNodeD_both]
  rfl

/-- A walk record of a laws-free operator with every fold direction `.both`:
an opening tree's raw view, normalized. -/
theorem mem_baseRecsR_both {ctx : Ctx} {laws : Laws} {n : Node} {r : RecR}
    (h : r ∈ baseRecsR ctx .both laws n) :
    ∃ v ls o, RawViewL ctx n v ls o ∧ normalize ctx.κ laws v = .node r.1 := by
  unfold baseRecsR at h
  rw [rawRecordsLD_both] at h
  obtain ⟨r', hr', rfl⟩ := List.mem_map.1 h
  obtain ⟨v, ls, o, hv, hn, -⟩ := mem_rawRecordsL.1 (show (r'.1, r'.2) ∈ _ from hr')
  exact ⟨v, ls, o, hv, hn⟩

/-- Every view of `enumerateR` satisfies an invariant of the walk's records
that one regrouping preserves. -/
theorem enumerateR_induction {ctx : Ctx} {dir : Dir} {laws : Laws} {limit : Nat} {n : Node}
    {P : RecR → Prop} (h0 : ∀ r ∈ baseRecsR ctx dir laws n, P r)
    (hs : ∀ r r', P r → r' ∈ regroupRec ctx dir laws limit r → P r')
    {w : List (C × Nat)} {d : DemandL} (h : (w, d) ∈ enumerateR ctx dir laws limit n) :
    ∃ r, P r ∧ r.1 = w := by
  unfold enumerateR at h
  obtain ⟨r, hr, rfl⟩ := mem_enumerateFromR h
  exact ⟨r, regroupLevels_induction ctx dir laws limit hs _ _ h0 r hr, rfl⟩

/-! ## AC: commutative monoids -/

section AC

variable {M : Type*} [AddCommMonoid M]

/-- The denotation of a view: the sum of its classes with their counts. -/
def denAC (den : C → M) (w : List (C × Nat)) : M := ((ofEntries w).map den).sum

/-- Every `f`-member of a class denotes the class. -/
def ConsistentAC (ctx : Ctx) (den : C → M) : Prop :=
  ∀ id m X, ctx.IsMember id m X → den X = denAC den (kids .ac m.children)

/-- **One regrouping keeps the denotation, AC.** -/
theorem regroup_step_sound_ac {ctx : Ctx} {den : C → M} (hc : ConsistentAC ctx den) {dir : Dir}
    {id : NodeId} {m : Node} {g : C} (hm : ctx.IsMember id m g) {view raw : List (C × Nat)}
    (hnd : (view.map Prod.fst).Nodup) (h : raw ∈ fitsR .ac dir view g (kids .ac m.children)) :
    denAC den raw = denAC den view := by
  obtain ⟨-, v, hs, rfl⟩ := fitsR_ac h
  have hsum := subEntries_spec _ _ _ hnd hs
  rw [ofEntries_coalesce] at hsum
  unfold denAC
  rw [ofEntries_append, ← hsum, Multiset.map_add, Multiset.map_add, Multiset.sum_add,
    Multiset.sum_add]
  congr 1
  rw [show ((ofEntries [(g, 1)]).map den).sum = den g by simp [ofEntries], hc id m g hm]
  rfl

theorem otl_den_ac {ctx : Ctx} (hκ : ctx.κ = .ac) {den : C → M} (hc : ConsistentAC ctx den)
    {k : Nat} {P : Finset C} {ks v : List (C × Nat)} {ls : List LeafL} {o : Nat}
    (h : OTL ctx k P ks v ls o) : denAC den v = k • denAC den ks := by
  induction h with
  | nil => simp [denAC, ofEntries]
  | keep _ ih =>
      simp only [denAC, ofEntries_cons, Multiset.map_add, Multiset.sum_add, Multiset.map_replicate,
        Multiset.sum_replicate] at ih ⊢
      rw [ih, smul_add, mul_smul]
  | @opn k P X j rest id m v₁ v₂ l₁ l₂ o₁ o₂ _ hmem _ _ ih₁ ih₂ =>
      rw [hκ] at ih₁
      simp only [denAC, ofEntries_append, ofEntries_cons, Multiset.map_add, Multiset.sum_add,
        Multiset.map_replicate, Multiset.sum_replicate] at ih₁ ih₂ ⊢
      rw [ih₁, ih₂, ← denAC, ← hc id m X hmem, smul_add, mul_smul]

/-- **The views with regrouping of a laws-free AC operator denote the node.** -/
theorem regroup_views_sound_ac {ctx : Ctx} (hκ : ctx.κ = .ac) {den : C → M}
    (hc : ConsistentAC ctx den) {limit : Nat} {n : Node} {w : List (C × Nat)} {d : DemandL}
    (h : (w, d) ∈ enumerateR ctx .both Laws.free limit n) :
    denAC den w = denAC den (kids .ac n.children) := by
  suffices H : ∃ r : RecR, (denAC den r.1 = denAC den (kids .ac n.children) ∧
      (r.1.map Prod.fst).Nodup) ∧ r.1 = w by
    obtain ⟨r, ⟨hr, -⟩, rfl⟩ := H; exact hr
  refine enumerateR_induction (limit := limit) ?_ ?_ h
  · intro r hr
    obtain ⟨v, ls, o, hv, hn⟩ := mem_baseRecsR_both hr
    rw [hκ] at hn
    refine ⟨?_, (normalize_ac_canonical hn).nodup⟩
    have h1 := otl_den_ac hκ hc hv
    rw [hκ, one_smul] at h1
    rw [normalize_free_ac hn, denAC, ofEntries_coalesce, ← denAC, h1]
  · intro r r' ⟨hr, hnd⟩ h'
    obtain ⟨g, grp, raw, hgg, hraw, hn, -⟩ := mem_regroupRec h'
    obtain ⟨id, m, hm, rfl⟩ := mem_groupsOf hgg
    rw [hκ] at hraw hn
    refine ⟨?_, (normalize_ac_canonical hn).nodup⟩
    rw [normalize_free_ac hn, denAC, ofEntries_coalesce, ← denAC,
      regroup_step_sound_ac hc hm hnd hraw, hr]

end AC

/-! ## ACI: join semilattices -/

section ACI

variable {M : Type*} [SemilatticeSup M] [OrderBot M]

/-- The denotation of a set view: the join of its classes. -/
def denACI (den : C → M) (w : List (C × Nat)) : M := (ofEntries w).toFinset.sup den

def ConsistentACI (ctx : Ctx) (den : C → M) : Prop :=
  ∀ id m X, ctx.IsMember id m X → den X = denACI den (kids .aci m.children)

theorem toFinset_ofEntries_of_pos {l : List (C × Nat)} (hp : ∀ e ∈ l, 0 < e.2) :
    (ofEntries l).toFinset = (l.map Prod.fst).toFinset := by
  ext c
  simp only [Multiset.mem_toFinset, mem_ofEntries, List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨e, he, rfl, -⟩; exact ⟨e, he, rfl⟩
  · rintro ⟨e, he, rfl⟩; exact ⟨e, he, rfl, hp e he⟩

theorem dedupAci_pos (v : List (C × Nat)) : ∀ e ∈ dedupAci v, 0 < e.2 := by
  intro e he
  simp only [dedupAci, List.mem_map] at he
  obtain ⟨_, -, rfl⟩ := he
  exact Nat.one_pos

theorem toFinset_ofEntries_dedupAci {v : List (C × Nat)} (hp : ∀ e ∈ v, 0 < e.2) :
    (ofEntries (dedupAci v)).toFinset = (ofEntries v).toFinset := by
  rw [toFinset_ofEntries_of_pos (dedupAci_pos v), toFinset_ofEntries_of_pos hp,
    toFinset_map_fst_dedupAci]

/-- **One regrouping keeps the denotation, ACI.** -/
theorem regroup_step_sound_aci {ctx : Ctx} {den : C → M} (hc : ConsistentACI ctx den)
    {dir : Dir} {id : NodeId} {m : Node} {g : C} (hm : ctx.IsMember id m g)
    {view raw : List (C × Nat)} (hnd : (view.map Prod.fst).Nodup)
    (h : raw ∈ fitsR .aci dir view g (kids .aci m.children)) :
    denACI den raw = denACI den view := by
  obtain ⟨-, v, hs, rfl⟩ := fitsR_aci h
  have hsum := subEntries_spec _ _ _ hnd hs
  unfold denACI
  rw [ofEntries_append, ← hsum, Multiset.toFinset_add, Multiset.toFinset_add, Finset.sup_union,
    Finset.sup_union, toFinset_ofEntries_dedupAci (kids_pos _ _)]
  congr 1
  rw [show (ofEntries [(g, 1)]).toFinset.sup den = den g by simp [ofEntries], hc id m g hm]
  rfl

theorem otl_den_aci {ctx : Ctx} (hκ : ctx.κ = .aci) {den : C → M} (hc : ConsistentACI ctx den)
    {k : Nat} {P : Finset C} {ks v : List (C × Nat)} {ls : List LeafL} {o : Nat}
    (h : OTL ctx k P ks v ls o) (hk : 0 < k) (hks : ∀ e ∈ ks, 0 < e.2) :
    denACI den v = denACI den ks := by
  induction h with
  | nil => rfl
  | @keep k P X j rest v₂ l₂ o _ ih =>
      have hj := hks (X, j) (List.mem_cons_self ..)
      simp only [denACI, ofEntries_cons, Multiset.toFinset_add, Finset.sup_union] at ih ⊢
      rw [ih hk (fun e he => hks e (List.mem_cons_of_mem _ he))]
      congr 2
      rw [Multiset.toFinset_replicate, Multiset.toFinset_replicate]
      simp [Nat.pos_iff_ne_zero.1 hj, Nat.pos_iff_ne_zero.1 (Nat.mul_pos hk hj)]
  | @opn k P X j rest id m v₁ v₂ l₁ l₂ o₁ o₂ _ hmem _ _ ih₁ ih₂ =>
      have hj := hks (X, j) (List.mem_cons_self ..)
      have h1 := ih₁ (Nat.mul_pos hk hj) (kids_pos _ _)
      rw [hκ, ← hc id m X hmem] at h1
      simp only [denACI, ofEntries_append, ofEntries_cons, Multiset.toFinset_add,
        Finset.sup_union] at h1 ih₂ ⊢
      rw [h1, ih₂ hk (fun e he => hks e (List.mem_cons_of_mem _ he)),
        Multiset.toFinset_replicate]
      simp [Nat.pos_iff_ne_zero.1 hj]

theorem subEntries_pos :
    ∀ (norm view : List (C × Nat)) (v : List (C × Nat)), subEntries view norm = some v →
      ∀ e ∈ v, 0 < e.2
  | [], view, v, h => by
      simp only [subEntries, Option.some.injEq] at h
      subst h
      intro e he
      exact Nat.pos_of_ne_zero (by simpa using (List.mem_filter.1 he).2)
  | (c, k) :: rest, view, v, h => by
      simp only [subEntries] at h
      revert h
      cases view.find? (fun e => decide (e.1 = c)) with
      | none => simp
      | some e =>
          simp only
          split
          · exact subEntries_pos rest _ v
          · simp

/-- **The views with regrouping of a laws-free ACI operator denote the node.** -/
theorem regroup_views_sound_aci {ctx : Ctx} (hκ : ctx.κ = .aci) {den : C → M}
    (hc : ConsistentACI ctx den) {limit : Nat} {n : Node} {w : List (C × Nat)} {d : DemandL}
    (h : (w, d) ∈ enumerateR ctx .both Laws.free limit n) :
    denACI den w = denACI den (kids .aci n.children) := by
  suffices H : ∃ r : RecR, (denACI den r.1 = denACI den (kids .aci n.children) ∧
      (r.1.map Prod.fst).Nodup ∧ ∀ e ∈ r.1, 0 < e.2) ∧ r.1 = w by
    obtain ⟨r, ⟨hr, -, -⟩, rfl⟩ := H; exact hr
  refine enumerateR_induction (limit := limit) ?_ ?_ h
  · intro r hr
    obtain ⟨v, ls, o, hv, hn⟩ := mem_baseRecsR_both hr
    rw [hκ] at hn
    have hcan := normalize_aci_canonical hn
    refine ⟨?_, hcan.1.imp (fun h => Nat.ne_of_lt h), fun e he => by rw [hcan.2 e he]; omega⟩
    have h1 := otl_den_aci hκ hc hv Nat.one_pos (kids_pos _ _)
    rw [hκ] at h1
    rw [normalize_free_aci hn, denACI, toFinset_ofEntries_dedupAci (RawViewL.pos hv), ← denACI,
      h1]
  · intro r r' ⟨hr, hnd, hp⟩ h'
    obtain ⟨g, grp, raw, hgg, hraw, hn, -⟩ := mem_regroupRec h'
    obtain ⟨id, m, hm, rfl⟩ := mem_groupsOf hgg
    rw [hκ] at hraw hn
    have hcan := normalize_aci_canonical hn
    refine ⟨?_, hcan.1.imp (fun h => Nat.ne_of_lt h), fun e he => by rw [hcan.2 e he]; omega⟩
    have hrawp : ∀ e ∈ raw, 0 < e.2 := by
      obtain ⟨-, v, hs, rfl⟩ := fitsR_aci hraw
      intro e he
      rcases List.mem_append.1 he with he | he
      · exact subEntries_pos _ _ _ hs e he
      · rw [List.mem_singleton] at he; subst he; exact Nat.one_pos
    rw [normalize_free_aci hn, denACI, toFinset_ofEntries_dedupAci hrawp, ← denACI,
      regroup_step_sound_aci hc hm hnd hraw, hr]

end ACI

/-! ## `:assoc`: monoids -/

section Assoc

variable {M : Type*} [Monoid M]

/-- The denotation of a sequence view: the product of its classes in order. -/
def denA (den : C → M) (w : List (C × Nat)) : M := (w.map (fun e => den e.1)).prod

def ConsistentA (ctx : Ctx) (den : C → M) : Prop :=
  ∀ id m X, ctx.IsMember id m X → den X = denA den (kids .assoc m.children)

theorem denA_congr {den : C → M} {l l' : List (C × Nat)} (h : l.map Prod.fst = l'.map Prod.fst) :
    denA den l = denA den l' := by
  unfold denA
  have e1 : l.map (fun e => den e.1) = (l.map Prod.fst).map den := by rw [List.map_map]; rfl
  have e2 : l'.map (fun e => den e.1) = (l'.map Prod.fst).map den := by rw [List.map_map]; rfl
  rw [e1, e2, h]

/-- **One regrouping keeps the denotation, `:assoc`** (any run). -/
theorem regroup_step_sound_assoc {ctx : Ctx} {den : C → M} (hc : ConsistentA ctx den)
    {dir : Dir} {id : NodeId} {m : Node} {g : C} (hm : ctx.IsMember id m g)
    {view raw : List (C × Nat)} (h : raw ∈ fitsR .assoc dir view g (kids .assoc m.children)) :
    denA den raw = denA den view := by
  obtain ⟨-, -, p, -, hgrp, rfl⟩ := fitsR_assoc h
  have hg : den g = denA den ((view.drop p).take (kids .assoc m.children).length) := by
    rw [hc id m g hm]; exact denA_congr hgrp.symm
  conv_rhs => rw [← List.take_append_drop p view,
    ← List.take_append_drop (kids .assoc m.children).length (view.drop p), List.drop_drop]
  simp only [denA, List.map_append, List.map_cons, List.prod_append, List.prod_cons] at hg ⊢
  rw [hg, Nat.add_comm]

theorem otl_den_assoc {ctx : Ctx} (hκ : ctx.κ = .assoc) {den : C → M} (hc : ConsistentA ctx den)
    {k : Nat} {P : Finset C} {ks v : List (C × Nat)} {ls : List LeafL} {o : Nat}
    (h : OTL ctx k P ks v ls o) : denA den v = denA den ks := by
  induction h with
  | nil => rfl
  | keep _ ih => simp only [denA, List.map_cons, List.prod_cons] at ih ⊢; rw [ih]
  | @opn k P X j rest id m v₁ v₂ l₁ l₂ o₁ o₂ _ hmem _ _ ih₁ ih₂ =>
      rw [hκ, ← hc id m X hmem] at ih₁
      simp only [denA, List.map_append, List.map_cons, List.prod_append, List.prod_cons] at ih₁ ih₂ ⊢
      rw [ih₁, ih₂]

/-- **The views with regrouping of a laws-free `:assoc` operator denote the node.** -/
theorem regroup_views_sound_assoc {ctx : Ctx} (hκ : ctx.κ = .assoc) {den : C → M}
    (hc : ConsistentA ctx den) {limit : Nat} {n : Node} {w : List (C × Nat)} {d : DemandL}
    (h : (w, d) ∈ enumerateR ctx .both Laws.free limit n) :
    denA den w = denA den (kids .assoc n.children) := by
  suffices H : ∃ r : RecR, denA den r.1 = denA den (kids .assoc n.children) ∧ r.1 = w by
    obtain ⟨r, hr, rfl⟩ := H; exact hr
  refine enumerateR_induction (limit := limit) ?_ ?_ h
  · intro r hr
    obtain ⟨v, ls, o, hv, hn⟩ := mem_baseRecsR_both hr
    rw [hκ] at hn
    have h1 := otl_den_assoc hκ hc hv
    rw [hκ] at h1
    rw [normalize_free_assoc hn, h1]
  · intro r r' hr h'
    obtain ⟨g, grp, raw, hgg, hraw, hn, -⟩ := mem_regroupRec h'
    obtain ⟨id, m, hm, rfl⟩ := mem_groupsOf hgg
    rw [hκ] at hraw hn
    rw [normalize_free_assoc hn, regroup_step_sound_assoc hc hm hraw, hr]

end Assoc

/-! ## Folds: only the spine end regroups -/

/-- **Regrouping the prefix of a left fold keeps the left fold.** -/
theorem regroup_step_sound_left {ctx : Ctx} {den : C → BTm} (hc : ConsistentL ctx den)
    {id : NodeId} {m : Node} {g : C} (hm : ctx.IsMember id m g) {view raw : List (C × Nat)}
    (h : raw ∈ fitsR .assoc .left view g (kids .assoc m.children)) :
    lfold ((raw.map Prod.fst).map den) = lfold ((view.map Prod.fst).map den) := by
  obtain ⟨h2, -, p, hsp, hgrp, rfl⟩ := fitsR_assoc h
  simp only [spineRun, beq_iff_eq] at hsp
  subst hsp
  obtain ⟨cs, hch⟩ : ∃ cs, m.children = .seq cs := by
    cases hch : m.children <;> simp_all [kids]
  have hl : lfold (cs.map den) = some (den g) := hc id m g cs hm hch
  have hcs : (kids .assoc m.children).map Prod.fst = cs := by
    rw [hch]; simp [kids, Function.comp_def]
  have hlen : (kids .assoc m.children).length = cs.length := by rw [hch]; simp [kids]
  rw [hlen, hcs, List.drop_zero] at hgrp
  rw [hlen]
  simp only [List.take_zero, Nat.zero_add, List.nil_append]
  have hraw : (((g, 1) :: view.drop cs.length).map Prod.fst).map den =
      den g :: ((view.drop cs.length).map Prod.fst).map den := by simp
  have hl' : lfold (((view.take cs.length).map Prod.fst).map den) = some (den g) := by
    rw [hgrp]; exact hl
  rw [hraw, lfold_splice hl', ← List.map_append, ← List.map_append, List.take_append_drop]

/-- **Regrouping the suffix of a right fold keeps the right fold.** -/
theorem regroup_step_sound_right {ctx : Ctx} {den : C → BTm} (hc : ConsistentR ctx den)
    {id : NodeId} {m : Node} {g : C} (hm : ctx.IsMember id m g) {view raw : List (C × Nat)}
    (h : raw ∈ fitsR .assoc .right view g (kids .assoc m.children)) :
    rfold ((raw.map Prod.fst).map den) = rfold ((view.map Prod.fst).map den) := by
  obtain ⟨h2, -, p, hsp, hgrp, rfl⟩ := fitsR_assoc h
  simp only [spineRun, beq_iff_eq] at hsp
  obtain ⟨cs, hch⟩ : ∃ cs, m.children = .seq cs := by
    cases hch : m.children <;> simp_all [kids]
  have hr : rfold (cs.map den) = some (den g) := hc id m g cs hm hch
  have hcs : (kids .assoc m.children).map Prod.fst = cs := by
    rw [hch]; simp [kids, Function.comp_def]
  have hlen : (kids .assoc m.children).length = cs.length := by rw [hch]; simp [kids]
  rw [hlen, hcs] at hgrp
  rw [hlen] at hsp ⊢
  have hd : (view.drop p).take cs.length = view.drop p := by
    apply List.take_of_length_le
    simp only [List.length_drop]
    omega
  rw [hd] at hgrp
  rw [hsp, List.drop_length]
  have hraw : ((view.take p ++ [(g, 1)]).map Prod.fst).map den =
      ((view.take p).map Prod.fst).map den ++ [den g] := by simp
  have hr' : rfold (((view.drop p).map Prod.fst).map den) = some (den g) := by
    rw [hgrp]; exact hr
  rw [hraw, rfold_splice hr', ← List.map_append, ← List.map_append, List.take_append_drop]

/-- The reproducer of `Fold.lean` read as a regrouping: the view `[a, b, c]`
of `Sub[a, b, c]` and the member `K ∋ Sub[b, c]` (node 10 of `exFold`). -/
def exRegView : List (C × Nat) := [(1, 1), (2, 1), (3, 1)]

/-- **Regrouping a fold off its spine is unsound.** With a denotation
consistent with the left fold, the regrouped view `[a, K]` of `[a, b, c]`
(the run `[b, c]` at offset 1, which the `:assoc` `fits` produces) denotes
`Sub(a, Sub(b, c))`, not the view's `Sub(Sub(a, b), c)`; the left-fold
`fits` does not produce it. -/
theorem regroup_off_spine_unsound :
    ∃ (ctx : Ctx) (den : C → BTm) (id : NodeId) (m : Node) (g : C) (view raw : List (C × Nat)),
      ConsistentL ctx den ∧ ctx.IsMember id m g ∧
        raw ∈ fitsR .assoc .both view g (kids .assoc m.children) ∧
        raw ∉ fitsR .assoc .left view g (kids .assoc m.children) ∧
        lfold ((raw.map Prod.fst).map den) ≠ lfold ((view.map Prod.fst).map den) :=
  ⟨exFold, exFoldDen, 10, ⟨7, .seq [2, 3]⟩, 4, exRegView, [(1, 1), (4, 1)], exFold_consistent,
    ⟨by simp [exFold], rfl, by simp [exFold], rfl⟩, by decide, by decide, by decide⟩

end Semper.EMatch.Flatten
