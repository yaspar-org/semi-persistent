import SemperProofs.EMatch.Flatten.RegroupComplete

/-!
# `:flatten`: one group fits, ACI, `:assoc` and the folds

The step-level completeness of `fits` for the kinds other than AC
(`fitsR_ac_complete`, `RegroupComplete.lean`):

* `fitsR_aci_complete`: on a canonical set view, a subset of at least two
  classes, not the whole view, spelled by a member of `g` not over `g`,
  fits; the regrouped raw view is the view less the group, then `g`;
* `fitsR_assoc_complete`: a run of at least two entries, not the whole view,
  on the spine of the fold direction, fits at its position;
  `fitsR_left_complete` (a prefix of a left fold) and `fitsR_right_complete`
  (a suffix of a right fold) are its two fold cases.

The chain and match theorems of `RegroupComplete.lean` are proved for AC
only; these lemmas are the per-step part their ACI and `:assoc` analogues
would use.
-/

namespace Semper.EMatch.Flatten

open Semper.EMatch

theorem ofEntries_of_ones : ∀ {l : List (C × Nat)}, (∀ e ∈ l, e.2 = 1) →
    ofEntries l = ((l.map Prod.fst : List C) : Multiset C)
  | [], _ => rfl
  | e :: l, h => by
      rw [ofEntries_cons, ofEntries_of_ones (fun e he => h e (List.mem_cons_of_mem _ he)),
        h e (List.mem_cons_self ..)]
      simp

theorem dedupAci_ones (v : List (C × Nat)) : ∀ e ∈ dedupAci v, e.2 = 1 := by
  intro e he
  simp only [dedupAci, List.mem_map] at he
  obtain ⟨_, -, rfl⟩ := he
  rfl

theorem map_fst_dedupAci (v : List (C × Nat)) :
    (dedupAci v).map Prod.fst = (v.map Prod.fst).toFinset.sort (· ≤ ·) := by
  simp [dedupAci, List.map_map, Function.comp_def]

/-- **A group fits, ACI.** On a canonical set view, a set of at least two of
its classes, not all of them, spelled by a member of `g` not over `g`
itself, fits. -/
theorem fitsR_aci_complete {dir : Dir} {view : List (C × Nat)} {g : C} {grp : List (C × Nat)}
    (hcan : (view.map Prod.fst).Pairwise (· < ·) ∧ ∀ e ∈ view, e.2 = 1)
    (hg : g ∉ grp.map Prod.fst) (hsub : ∀ c ∈ grp.map Prod.fst, c ∈ view.map Prod.fst)
    (hne : (grp.map Prod.fst).toFinset ≠ (view.map Prod.fst).toFinset)
    (h2 : 2 ≤ (grp.map Prod.fst).toFinset.card) :
    ∃ v, v ++ [(g, 1)] ∈ fitsR .aci dir view g grp ∧
      ofEntries v + ofEntries (dedupAci grp) = ofEntries view := by
  have hnd : (view.map Prod.fst).Nodup := hcan.1.imp (fun h => Nat.ne_of_lt h)
  have hle : ofEntries (dedupAci grp) ≤ ofEntries view := by
    rw [ofEntries_of_ones (dedupAci_ones grp), ofEntries_of_ones hcan.2, map_fst_dedupAci]
    rw [Multiset.le_iff_subset (by
      rw [Multiset.coe_nodup]; exact Finset.sort_nodup _ _)]
    intro c hc
    rw [Multiset.mem_coe, Finset.mem_sort, List.mem_toFinset] at hc
    exact Multiset.mem_coe.2 (hsub c hc)
  obtain ⟨v, hv⟩ := subEntries_some (dedupAci grp) view hnd
    (fun e he => by rw [dedupAci_ones grp e he]; exact Nat.one_pos) hle
  refine ⟨v, ?_, subEntries_spec _ _ _ hnd hv⟩
  have hany : grp.any (fun e => decide (e.1 = g)) = false := by
    simp only [List.any_eq_false, decide_eq_true_eq]
    intro e he heg
    exact hg (heg ▸ List.mem_map_of_mem he)
  have hlen : 2 ≤ (dedupAci grp).length := by
    simp only [dedupAci, List.length_map, Finset.length_sort]; exact h2
  have hneq : (dedupAci grp == view) = false := by
    rw [beq_eq_false_iff_ne]
    intro he
    apply hne
    have := congrArg (fun l => (l.map Prod.fst).toFinset) he
    rw [← this, map_fst_dedupAci]
    ext c; simp
  unfold fitsR
  simp only [hany, groupNorm, Bool.false_eq_true, ↓reduceIte]
  simp [hneq, hv, hlen]

/-- **A run fits, `:assoc` and the folds.** A run of at least two entries at
`p`, not the whole view, on the spine of the fold direction (any run for
`:assoc`, a prefix for a left fold, a suffix for a right fold), spelled by a
member of `g` not over `g` itself, fits. -/
theorem fitsR_assoc_complete {dir : Dir} {view : List (C × Nat)} {g : C} {grp : List (C × Nat)}
    {p : Nat} (hg : g ∉ grp.map Prod.fst) (h2 : 2 ≤ grp.length) (hlt : grp.length < view.length)
    (hp : p + grp.length ≤ view.length) (hsp : spineRun dir p grp.length view.length = true)
    (hrun : ((view.drop p).take grp.length).map Prod.fst = grp.map Prod.fst) :
    view.take p ++ (g, 1) :: view.drop (p + grp.length) ∈ fitsR .assoc dir view g grp := by
  have hany : grp.any (fun e => decide (e.1 = g)) = false := by
    simp only [List.any_eq_false, decide_eq_true_eq]
    intro e he heg
    exact hg (heg ▸ List.mem_map_of_mem he)
  have hk : ¬ (grp.length < 2 ∨ view.length ≤ grp.length) := by omega
  unfold fitsR
  simp only [hany, Bool.false_eq_true, ↓reduceIte, hk]
  refine List.mem_filterMap.2 ⟨p, List.mem_range.2 (by omega), ?_⟩
  simp [hsp, hrun]

/-- A prefix of a left fold fits (`fitsR_assoc_complete` at `p = 0`). -/
theorem fitsR_left_complete {view : List (C × Nat)} {g : C} {grp : List (C × Nat)}
    (hg : g ∉ grp.map Prod.fst) (h2 : 2 ≤ grp.length) (hlt : grp.length < view.length)
    (hrun : (view.take grp.length).map Prod.fst = grp.map Prod.fst) :
    (g, 1) :: view.drop grp.length ∈ fitsR .assoc .left view g grp := by
  have := fitsR_assoc_complete (dir := .left) (p := 0) hg h2 hlt (by omega) (by simp [spineRun])
    (by simpa using hrun)
  simpa using this

/-- A suffix of a right fold fits (`fitsR_assoc_complete` at the last run). -/
theorem fitsR_right_complete {view : List (C × Nat)} {g : C} {grp : List (C × Nat)}
    (hg : g ∉ grp.map Prod.fst) (h2 : 2 ≤ grp.length) (hlt : grp.length < view.length)
    (hrun : (view.drop (view.length - grp.length)).map Prod.fst = grp.map Prod.fst) :
    view.take (view.length - grp.length) ++ [(g, 1)] ∈ fitsR .assoc .right view g grp := by
  have h := fitsR_assoc_complete (dir := .right) (p := view.length - grp.length) hg h2 hlt
    (by omega) (by simp [spineRun]; omega) (by
      rw [List.take_of_length_le (by simp; omega)]; exact hrun)
  have e : view.length - grp.length + grp.length = view.length := by omega
  rw [e, List.drop_length] at h
  exact h

end Semper.EMatch.Flatten
