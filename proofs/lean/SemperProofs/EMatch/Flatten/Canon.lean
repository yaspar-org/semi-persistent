import SemperProofs.EMatch.Flatten.Views
import SemperProofs.EMatch.Proofs.DecomposeAC

/-!
# `:flatten` views: canonical forms

Properties of the canonization pipeline of `Views.lean`: `ofEntries` and
`Multiset.entries` are inverse on canonical lists, the AC and ACI normal
forms are canonical (strictly sorted classes, positive counts), and the
laws-free pipeline is the kind's canonization step alone.

`List.Sorted` is not available in this Mathlib; strict sortedness is stated
as `List.Pairwise (· < ·)`.
-/

namespace Semper.EMatch.Flatten

open Semper.EMatch

/-! ## `ofEntries` and `entries` -/

theorem ofEntries_entries (m : Multiset C) : ofEntries (Multiset.entries m) = m := by
  rw [entries_eq_resOf, ← ofEntries_filter_nonzero, ofEntries_resOf]
  exact Multiset.filter_eq_self.2 (fun a _ => List.not_mem_nil)

theorem ofEntries_coalesce (v : List (C × Nat)) : ofEntries (coalesce v) = ofEntries v :=
  ofEntries_entries _

theorem mem_ofEntries {w : List (C × Nat)} {c : C} :
    c ∈ ofEntries w ↔ ∃ e ∈ w, e.1 = c ∧ 0 < e.2 := by
  induction w with
  | nil => simp [ofEntries]
  | cons e w ih =>
      rw [ofEntries_cons, Multiset.mem_add, ih, Multiset.mem_replicate]
      simp only [List.mem_cons, exists_eq_or_imp]
      constructor
      · rintro (⟨h0, rfl⟩ | h)
        · exact Or.inl ⟨rfl, Nat.pos_of_ne_zero h0⟩
        · exact Or.inr h
      · rintro (⟨rfl, h0⟩ | h)
        · exact Or.inl ⟨Nat.pos_iff_ne_zero.1 h0, rfl⟩
        · exact Or.inr h

theorem count_ofEntries_of_nodup {w : List (C × Nat)} (hw : (w.map Prod.fst).Nodup)
    {e : C × Nat} (he : e ∈ w) : (ofEntries w).count e.1 = e.2 := by
  induction w with
  | nil => simp at he
  | cons e' w ih =>
      rw [List.map_cons, List.nodup_cons] at hw
      rw [ofEntries_cons, Multiset.count_add, Multiset.count_replicate]
      rcases List.mem_cons.1 he with rfl | he
      · have h0 : (ofEntries w).count e.1 = 0 := by
          rw [Multiset.count_eq_zero]
          intro hm
          obtain ⟨e'', he'', h1, _⟩ := mem_ofEntries.1 hm
          exact hw.1 (h1 ▸ List.mem_map_of_mem he'')
        rw [if_pos rfl, h0, Nat.add_zero]
      · have hne : e'.1 ≠ e.1 := fun h => hw.1 (h ▸ List.mem_map_of_mem he)
        rw [if_neg hne, ih hw.2 he, Nat.zero_add]

/-! ## Canonical lists -/

/-- A canonical child list: strictly increasing classes, positive counts. -/
def Canonical (w : List (C × Nat)) : Prop :=
  (w.map Prod.fst).Pairwise (· < ·) ∧ ∀ e ∈ w, 0 < e.2

theorem Canonical.nodup {w : List (C × Nat)} (h : Canonical w) : (w.map Prod.fst).Nodup :=
  h.1.imp (fun h => Nat.ne_of_lt h)

theorem entries_ofEntries_of_canonical {w : List (C × Nat)} (h : Canonical w) :
    Multiset.entries (ofEntries w) = w := by
  obtain ⟨hs, hp⟩ := h
  have hnd : (w.map Prod.fst).Nodup := hs.imp (fun h => Nat.ne_of_lt h)
  have hfin : (ofEntries w).toFinset = (w.map Prod.fst).toFinset := by
    ext c
    simp only [Multiset.mem_toFinset, List.mem_toFinset, mem_ofEntries, List.mem_map]
    constructor
    · rintro ⟨e, he, rfl, _⟩
      exact ⟨e, he, rfl⟩
    · rintro ⟨e, he, rfl⟩
      exact ⟨e, he, rfl, hp e he⟩
  have hsort : (ofEntries w).toFinset.sort (· ≤ ·) = w.map Prod.fst := by
    rw [hfin, List.toFinset_sort _ hnd]
    exact hs.imp (fun h => Nat.le_of_lt h)
  unfold Multiset.entries
  rw [hsort, List.map_map]
  refine (List.map_congr_left (fun e he => ?_)).trans (List.map_id w)
  exact Prod.ext rfl (count_ofEntries_of_nodup hnd he)

/-- Canonicity passes to sublists. -/
theorem Canonical.of_sublist {l l' : List (C × Nat)} (hs : l'.Sublist l) (h : Canonical l) :
    Canonical l' :=
  ⟨h.1.sublist (hs.map Prod.fst), fun e he => h.2 e (hs.subset he)⟩

theorem coalesce_canonical (v : List (C × Nat)) : Canonical (coalesce v) := by
  unfold coalesce Multiset.entries
  constructor
  · rw [List.map_map]
    have h1 : (Prod.fst ∘ fun c : C => (c, (ofEntries v).count c)) = id := rfl
    rw [h1, List.map_id]
    exact List.sortedLT_iff_pairwise.1 (Finset.sortedLT_sort _)
  · intro e he
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 he
    exact Multiset.count_pos.2 (Multiset.mem_toFinset.1 ((Finset.mem_sort _).1 hc))

theorem dropUnit_canonical (u : Option C) {l : List (C × Nat)} (h : Canonical l) :
    Canonical (dropUnit u l) := by
  cases u with
  | none => exact h
  | some u => exact h.of_sublist List.filter_sublist

theorem clamp_canonical (r : Option Nat) {l : List (C × Nat)} (h : Canonical l) :
    Canonical (clamp r l) := by
  cases r with
  | none => exact h
  | some r =>
      constructor
      · have hsub : ((List.map (fun e : C × Nat => (e.1, e.2 % r)) l).filter
            (fun e => e.2 ≠ 0)).map Prod.fst |>.Sublist
            ((List.map (fun e : C × Nat => (e.1, e.2 % r)) l).map Prod.fst) :=
          List.filter_sublist.map Prod.fst
        rw [List.map_map] at hsub
        have h1 : (Prod.fst ∘ fun e : C × Nat => (e.1, e.2 % r)) = Prod.fst := rfl
        rw [h1] at hsub
        exact h.1.sublist hsub
      · intro e he
        have := (List.mem_filter.1 he).2
        simp only [ne_eq, decide_eq_true_eq] at this
        exact Nat.pos_of_ne_zero this

/-! ## Cancellation keeps the classes -/

theorem map_fst_set {l : List (C × Nat)} {j : Nat} {y : C} {k : Nat}
    (h : (l.map Prod.fst)[j]? = some y) :
    (l.set j (y, k)).map Prod.fst = l.map Prod.fst := by
  rw [List.map_set]
  apply List.ext_getElem?
  intro i
  rw [List.getElem?_set]
  split
  · next hij =>
      subst hij
      split
      · exact h.symm
      · next hlt =>
          exact absurd (List.getElem?_eq_some_iff.1 h).1 hlt
  · rfl

theorem cancelAt_map_fst (inv : C → Option C) (l : List (C × Nat)) (i : Nat) :
    (cancelAt inv l i).map Prod.fst = l.map Prod.fst := by
  unfold cancelAt
  rcases hl : l[i]? with _ | ⟨x, xc⟩
  · rfl
  have hxi : (l.map Prod.fst)[i]? = some x := by
    rw [List.getElem?_map, hl]
    rfl
  simp only
  split
  · rfl
  split
  · rfl
  next y _ =>
  split
  · split
    · exact map_fst_set hxi
    · rfl
  split
  · rfl
  next j hfind =>
  have hyj : (l.map Prod.fst)[j]? = some y := by
    obtain ⟨hj, hp, _⟩ := List.findIdx?_eq_some_iff_getElem.1 hfind
    rw [List.getElem?_map, List.getElem?_eq_getElem hj]
    simp only [decide_eq_true_eq] at hp
    exact congrArg some hp
  split
  · rfl
  next y' yc _ =>
  have hyj' : ((l.set i (x, xc - min xc yc)).map Prod.fst)[j]? = some y := by
    rw [map_fst_set hxi]
    exact hyj
  rw [map_fst_set hyj', map_fst_set hxi]

theorem cancelSteps_map_fst (inv : C → Option C) (l : List (C × Nat)) (i : Nat) :
    (cancelSteps inv l i).map Prod.fst = l.map Prod.fst := by
  induction i with
  | zero => rfl
  | succ i ih => rw [cancelSteps, cancelAt_map_fst, ih]

theorem cancel_canonical (inv : C → Option C) {l : List (C × Nat)} (h : Canonical l) :
    Canonical (cancel inv l) := by
  constructor
  · have hsub := (List.filter_sublist (l := cancelSteps inv l l.length)
      (p := fun e => e.2 ≠ 0)).map Prod.fst
    rw [cancelSteps_map_fst] at hsub
    exact h.1.sublist hsub
  · intro e he
    have := (List.mem_filter.1 he).2
    simp only [ne_eq, decide_eq_true_eq] at this
    exact Nat.pos_of_ne_zero this

/-! ## Degenerate arity -/

theorem classify_node_iff (u : Option C) (w w' : List (C × Nat)) :
    classify u w = .node w' ↔ (w = w' ∧ w ≠ [] ∧ ∀ c, w ≠ [(c, 1)]) := by
  rcases w with _ | ⟨⟨c, _ | _ | n⟩, _ | ⟨⟨c', n'⟩, r⟩⟩
  · simp only [classify]
    split <;> simp
  · simp [classify]
  · simp [classify]
  · simp [classify]
  · simp [classify]
  · simp [classify]
  · simp [classify]

/-! ## AC normal forms are canonical -/

theorem normalizeList_ac_canonical (laws : Laws) (v : List (C × Nat)) :
    Canonical (normalizeList .ac laws v) := by
  obtain ⟨u, r, inv⟩ := laws
  cases inv with
  | none =>
      exact clamp_canonical r (dropUnit_canonical u (coalesce_canonical v))
  | some inv =>
      exact cancel_canonical inv (clamp_canonical r (dropUnit_canonical u (coalesce_canonical v)))

theorem normalize_ac_canonical {laws : Laws} {v w : List (C × Nat)}
    (h : normalize .ac laws v = .node w) : Canonical w := by
  unfold normalize at h
  rw [classify_node_iff] at h
  exact h.1 ▸ normalizeList_ac_canonical laws v

theorem normalize_ac_entries {laws : Laws} {v w : List (C × Nat)}
    (h : normalize .ac laws v = .node w) : Multiset.entries (ofEntries w) = w :=
  entries_ofEntries_of_canonical (normalize_ac_canonical h)

/-! ## ACI normal forms are canonical -/

theorem dedupAci_spec (v : List (C × Nat)) :
    ((dedupAci v).map Prod.fst).Pairwise (· < ·) ∧ ∀ e ∈ dedupAci v, e.2 = 1 := by
  unfold dedupAci
  constructor
  · rw [List.map_map]
    have h1 : (Prod.fst ∘ fun c : C => (c, 1)) = id := rfl
    rw [h1, List.map_id]
    exact List.sortedLT_iff_pairwise.1 (Finset.sortedLT_sort _)
  · intro e he
    obtain ⟨c, _, rfl⟩ := List.mem_map.1 he
    rfl

theorem normalize_aci_canonical {laws : Laws} {v w : List (C × Nat)}
    (h : normalize .aci laws v = .node w) :
    (w.map Prod.fst).Pairwise (· < ·) ∧ ∀ e ∈ w, e.2 = 1 := by
  unfold normalize at h
  rw [classify_node_iff] at h
  obtain ⟨rfl, -, -⟩ := h
  obtain ⟨u, r, inv⟩ := laws
  obtain ⟨hs, h1⟩ := dedupAci_spec v
  have hsub : (dropUnit u (dedupAci v)).Sublist (dedupAci v) := by
    cases u with
    | none => exact List.Sublist.refl _
    | some u => exact List.filter_sublist
  exact ⟨hs.sublist (hsub.map Prod.fst), fun e he => h1 e (hsub.subset he)⟩

theorem normalize_aci_sort {laws : Laws} {v w : List (C × Nat)}
    (h : normalize .aci laws v = .node w) :
    (w.map Prod.fst).toFinset.sort (· ≤ ·) = w.map Prod.fst := by
  have hs := (normalize_aci_canonical h).1
  exact (List.toFinset_sort _ (hs.imp (fun h => Nat.ne_of_lt h))).2
    (hs.imp (fun h => Nat.le_of_lt h))

/-! ## The laws-free pipeline -/

/-- The canonization step of each kind. -/
def canonK : FlatKind → List (C × Nat) → List (C × Nat)
  | .assoc, v => v
  | .ac, v => coalesce v
  | .aci, v => dedupAci v

theorem normalizeList_free (κ : FlatKind) (v : List (C × Nat)) :
    normalizeList κ Laws.free v = canonK κ v := by
  cases κ <;> rfl

theorem normalize_free_node {κ : FlatKind} {v w : List (C × Nat)} :
    normalize κ Laws.free v = .node w ↔
      (w = canonK κ v ∧ w ≠ [] ∧ ∀ c, w ≠ [(c, 1)]) := by
  unfold normalize
  rw [normalizeList_free, classify_node_iff]
  constructor
  · rintro ⟨rfl, h1, h2⟩
    exact ⟨rfl, h1, h2⟩
  · rintro ⟨rfl, h1, h2⟩
    exact ⟨rfl, h1, h2⟩

theorem ofEntries_free_ac {v w : List (C × Nat)}
    (h : normalize .ac Laws.free v = .node w) : ofEntries w = ofEntries v := by
  obtain ⟨rfl, -, -⟩ := normalize_free_node.1 h
  exact ofEntries_coalesce v

end Semper.EMatch.Flatten
