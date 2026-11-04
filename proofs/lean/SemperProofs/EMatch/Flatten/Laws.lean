import SemperProofs.EMatch.Flatten.FixKind

/-!
# `:flatten` views under laws: inert refolds and the demand rule with laws

The completeness proofs of `FixMain.lean` close an unhit leaf (class `X`,
folded with count `k'`) and need the normal form of the refolded raw view to
be "the normal form of the old view with the leaf's entries removed and
`X : k'` inserted". Without laws that is `coalesce`; with `:identity`,
`:nilpotent` and `:inverse` the refold can drop `X` (unit), clamp its count
to zero, or cancel it (or the leaf's classes) against other classes, and the
match is then lost (`spec-flatten.md` §4.3 caveat, status file).

This file:
* reads the AC pipeline of `Views.lean` per class (`cntNF`): the
  cancellation walk `cancel` is the fold `walk` of a per-class step over the
  sorted classes (`cntOf_cancel`), zero-count classes are inert
  (`walk_filter`), and classes whose inverses are absent are *passive*: the
  walk neither touches them nor depends on them (`walk_passive`);
* defines the leaf data with the folded count (`LeafL`, `OTL`, `RawViewL`)
  and the enumerator `enumerateL` producing demands `DemandL` whose leaves
  carry the non-inertness flag `nonInertB` computed at the root;
* defines `LeafInert` (the weakest condition the completeness induction
  uses: `X` not the unit, not clamped to zero, no cancel pair touching `X`
  or a leaf class) and `RefoldInert` (the strong, literal condition: the
  touched classes are not units, not clamped, not cancelled), and proves
  `refold_normalize_inert` (per class) and `refold_normalize_inert_strong`
  (`NF(M') = NF(M) - L + k'·X`, which lifts `refold_ac`);
* defines the demand rule under laws `DemandL.acceptsLaws` and proves
  `accepts_imp_acceptsLaws`.

`LawsMain.lean` proves the completeness theorems.
-/

namespace Semper.EMatch.Flatten

open Semper.EMatch

/-! ## Counts of an entry list -/

/-- The count function of an entry list. -/
def cntOf (l : List (C × Nat)) : C → Nat := fun x => (ofEntries l).count x

theorem cntOf_of_mem {l : List (C × Nat)} (hl : (l.map Prod.fst).Nodup) {e : C × Nat}
    (he : e ∈ l) : cntOf l e.1 = e.2 :=
  count_ofEntries_of_nodup hl he

theorem cntOf_of_notMem {l : List (C × Nat)} {x : C} (hx : x ∉ l.map Prod.fst) :
    cntOf l x = 0 :=
  count_ofEntries_eq_zero (fun _ he h => hx (h ▸ List.mem_map_of_mem he))

theorem cntOf_ne_zero_mem {l : List (C × Nat)} {x : C} (h : cntOf l x ≠ 0) :
    x ∈ l.map Prod.fst := by
  by_contra hx
  exact h (cntOf_of_notMem hx)

/-- Setting the entry at `i` (class unchanged) updates the count. -/
theorem cntOf_set {l : List (C × Nat)} (hl : (l.map Prod.fst).Nodup) {i : Nat} {x : C}
    {xc : Nat} (hi : l[i]? = some (x, xc)) (c : Nat) :
    cntOf (l.set i (x, c)) = Function.update (cntOf l) x c := by
  have hilt : i < l.length := (List.getElem?_eq_some_iff.1 hi).1
  have hnd' : ((l.set i (x, c)).map Prod.fst).Nodup := by
    rw [map_fst_set (by rw [List.getElem?_map, hi]; rfl)]
    exact hl
  funext z
  by_cases hzx : z = x
  · subst hzx
    rw [Function.update_self]
    have hmem : (z, c) ∈ l.set i (z, c) := by
      rw [List.mem_iff_getElem]
      exact ⟨i, by simpa using hilt, List.getElem_set_self _⟩
    exact cntOf_of_mem hnd' hmem
  · rw [Function.update_of_ne hzx]
    by_cases hz : z ∈ l.map Prod.fst
    · obtain ⟨e, he, rfl⟩ := List.mem_map.1 hz
      obtain ⟨j, hj, hej⟩ := List.mem_iff_getElem.1 he
      have hji : i ≠ j := by
        rintro rfl
        have := List.getElem?_eq_getElem hj
        rw [hi] at this
        exact hzx (by rw [← hej]; exact (Prod.mk.inj (Option.some.inj this)).1.symm)
      have he' : e ∈ l.set i (x, c) := by
        rw [List.mem_iff_getElem]
        exact ⟨j, by simpa using hj, by rw [List.getElem_set_ne hji, hej]⟩
      rw [cntOf_of_mem hnd' he', cntOf_of_mem hl he]
    · have hz' : z ∉ (l.set i (x, c)).map Prod.fst := by
        rwa [map_fst_set (by rw [List.getElem?_map, hi]; rfl)]
      rw [cntOf_of_notMem hz', cntOf_of_notMem hz]

/-! ## The cancellation walk per class -/

/-- One step of the cancellation walk at class `x` on a count function
(`cancelAt` read per class). -/
def stepC (inv : C → Option C) (cnt : C → Nat) (x : C) : C → Nat :=
  if cnt x = 0 then cnt
  else
    match inv x with
    | none => cnt
    | some y =>
        if y = x then (if 1 < cnt x then Function.update cnt x (cnt x % 2) else cnt)
        else
          let t := min (cnt x) (cnt y)
          Function.update (Function.update cnt x (cnt x - t)) y (cnt y - t)

/-- The walk over a class list. -/
def walk (inv : C → Option C) (cs : List C) (cnt : C → Nat) : C → Nat :=
  cs.foldl (stepC inv) cnt

theorem walk_nil (inv : C → Option C) (cnt : C → Nat) : walk inv [] cnt = cnt := rfl

theorem walk_cons (inv : C → Option C) (c : C) (cs : List C) (cnt : C → Nat) :
    walk inv (c :: cs) cnt = walk inv cs (stepC inv cnt c) := rfl

theorem walk_append (inv : C → Option C) (cs cs' : List C) (cnt : C → Nat) :
    walk inv (cs ++ cs') cnt = walk inv cs' (walk inv cs cnt) := by
  simp [walk, List.foldl_append]

/-- `stepC` unfolded for `cnt x ≠ 0` and `inv x = some y`. -/
theorem stepC_some {inv : C → Option C} {cnt : C → Nat} {x y : C} (h0 : cnt x ≠ 0)
    (hy : inv x = some y) :
    stepC inv cnt x =
      if y = x then (if 1 < cnt x then Function.update cnt x (cnt x % 2) else cnt)
      else Function.update (Function.update cnt x (cnt x - min (cnt x) (cnt y)))
        y (cnt y - min (cnt x) (cnt y)) := by
  unfold stepC
  simp only [h0, ↓reduceIte, hy]

/-- A step at a class of count zero does nothing. -/
theorem stepC_zero {inv : C → Option C} {cnt : C → Nat} {x : C} (h : cnt x = 0) :
    stepC inv cnt x = cnt := by
  simp [stepC, h]

/-- A step at a class without inverse does nothing. -/
theorem stepC_none {inv : C → Option C} {cnt : C → Nat} {x : C} (h : inv x = none) :
    stepC inv cnt x = cnt := by
  unfold stepC
  simp only [h]
  split <;> rfl

/-- A step at `x` changes only `x` and its inverse. -/
theorem stepC_of_ne {inv : C → Option C} {cnt : C → Nat} {x z : C} (hzx : z ≠ x)
    (hzy : ∀ y, inv x = some y → z ≠ y) : stepC inv cnt x z = cnt z := by
  by_cases h0 : cnt x = 0
  · rw [stepC_zero h0]
  rcases hinv : inv x with _ | y
  · rw [stepC_none hinv]
  rw [stepC_some h0 hinv]
  have hzy' := hzy y hinv
  by_cases hyx : y = x
  · subst hyx
    simp only [↓reduceIte]
    split
    · rw [Function.update_of_ne hzx]
    · rfl
  · simp only [hyx, ↓reduceIte]
    rw [Function.update_of_ne hzy', Function.update_of_ne hzx]

/-- A step at `x` reads only `x` and its inverse. -/
theorem stepC_congr {inv : C → Option C} {cnt cnt' : C → Nat} {x : C}
    (hx : cnt x = cnt' x) (hy : ∀ y, inv x = some y → cnt y = cnt' y) {z : C}
    (hz : cnt z = cnt' z) : stepC inv cnt x z = stepC inv cnt' x z := by
  by_cases h0 : cnt x = 0
  · rw [stepC_zero h0, stepC_zero (hx ▸ h0)]; exact hz
  have h0' : cnt' x ≠ 0 := hx ▸ h0
  rcases hinv : inv x with _ | y
  · rw [stepC_none hinv, stepC_none hinv]; exact hz
  rw [stepC_some h0 hinv, stepC_some h0' hinv]
  have hy' := hy y hinv
  by_cases hyx : y = x
  · subst hyx
    simp only [↓reduceIte]
    rw [← hx]
    split
    · by_cases hzy : z = y
      · subst hzy; simp
      · rw [Function.update_of_ne hzy, Function.update_of_ne hzy]; exact hz
    · exact hz
  · simp only [hyx, ↓reduceIte]
    rw [← hx, ← hy']
    by_cases hzy : z = y
    · subst hzy; simp
    · rw [Function.update_of_ne hzy, Function.update_of_ne hzy]
      by_cases hzx : z = x
      · subst hzx; simp
      · rw [Function.update_of_ne hzx, Function.update_of_ne hzx]; exact hz

/-- Counts never increase along the walk. -/
theorem stepC_le (inv : C → Option C) (cnt : C → Nat) (x z : C) :
    stepC inv cnt x z ≤ cnt z := by
  by_cases h0 : cnt x = 0
  · rw [stepC_zero h0]
  rcases hinv : inv x with _ | y
  · rw [stepC_none hinv]
  rw [stepC_some h0 hinv]
  by_cases hyx : y = x
  · subst hyx
    simp only [↓reduceIte]
    split
    · by_cases hzy : z = y
      · subst hzy; simp only [Function.update_self]; exact Nat.mod_le _ _
      · rw [Function.update_of_ne hzy]
    · exact le_rfl
  · simp only [hyx, ↓reduceIte]
    by_cases hzy : z = y
    · subst hzy; simp only [Function.update_self]; exact Nat.sub_le _ _
    · rw [Function.update_of_ne hzy]
      by_cases hzx : z = x
      · subst hzx; simp only [Function.update_self]; exact Nat.sub_le _ _
      · rw [Function.update_of_ne hzx]

theorem walk_le (inv : C → Option C) (cs : List C) (cnt : C → Nat) (z : C) :
    walk inv cs cnt z ≤ cnt z := by
  induction cs generalizing cnt with
  | nil => exact le_rfl
  | cons c cs ih => exact le_trans (ih _) (stepC_le inv cnt c z)

/-- A step at a class whose inverse is absent (count zero, or no inverse)
does nothing. -/
theorem stepC_inert {inv : C → Option C} {cnt : C → Nat} {x : C}
    (h : ∀ y, inv x = some y → y ≠ x ∧ cnt y = 0) : stepC inv cnt x = cnt := by
  by_cases h0 : cnt x = 0
  · exact stepC_zero h0
  rcases hinv : inv x with _ | y
  · exact stepC_none hinv
  rw [stepC_some h0 hinv]
  obtain ⟨hyx, hy0⟩ := h y hinv
  simp only [hyx, ↓reduceIte, hy0, Nat.min_zero, Nat.sub_zero]
  rw [Function.update_eq_self, ← hy0, Function.update_eq_self]

/-- Zero-count classes can be dropped from the walk. -/
theorem walk_filter (inv : C → Option C) (p : C → Bool) :
    ∀ (cs : List C) (cnt : C → Nat), (∀ c ∈ cs, p c = false → cnt c = 0) →
      walk inv cs cnt = walk inv (cs.filter p) cnt := by
  intro cs
  induction cs with
  | nil => intros; rfl
  | cons c cs ih =>
      intro cnt h
      rw [walk_cons, List.filter_cons]
      split
      · rw [walk_cons]
        apply ih
        intro c' hc' hp
        exact Nat.le_antisymm ((stepC_le _ _ _ _).trans (h c' (List.mem_cons_of_mem _ hc') hp).le)
          (Nat.zero_le _)
      · next hp =>
        rw [stepC_zero (h c (List.mem_cons_self ..) (by simpa using hp))]
        exact ih cnt (fun c' hc' hp => h c' (List.mem_cons_of_mem _ hc') hp)

/-- **Passivity.** Let `S` be a set of classes whose inverses lie outside
`K` and that are nobody's inverse within... precisely: no class of `S` has
an inverse in `K`, and no class outside `S` has an inverse in `S`. Two count
functions supported in `K` and agreeing outside `S` walk (over any list of
classes of `K`) to count functions agreeing outside `S`, and the walk does
not change the counts of `S`. -/
theorem walk_passive (inv : C → Option C) (K : List C) (S : C → Prop)
    (h1 : ∀ x ∈ K, S x → ∀ y, inv x = some y → y ∉ K)
    (h2 : ∀ y ∈ K, ¬ S y → ∀ z, inv y = some z → ¬ S z) :
    ∀ (cs : List C) (cnt cnt' : C → Nat), (∀ c ∈ cs, c ∈ K) →
      (∀ y, cnt y ≠ 0 → y ∈ K) → (∀ y, cnt' y ≠ 0 → y ∈ K) →
      (∀ x, ¬ S x → cnt x = cnt' x) →
      (∀ x, ¬ S x → walk inv cs cnt x = walk inv cs cnt' x) ∧
      (∀ x, S x → walk inv cs cnt x = cnt x ∧ walk inv cs cnt' x = cnt' x) := by
  intro cs
  induction cs with
  | nil =>
      intro cnt cnt' _ _ _ h3
      exact ⟨fun x hx => h3 x hx, fun x _ => ⟨rfl, rfl⟩⟩
  | cons c cs ih =>
      intro cnt cnt' hcs hK hK' h3
      have hcK : c ∈ K := hcs c (List.mem_cons_self ..)
      have hcs' : ∀ c' ∈ cs, c' ∈ K := fun c' hc' => hcs c' (List.mem_cons_of_mem _ hc')
      rw [walk_cons, walk_cons]
      by_cases hSc : S c
      · -- passive step: identity on both
        have hin : ∀ (f : C → Nat), (∀ y, f y ≠ 0 → y ∈ K) → stepC inv f c = f := by
          intro f hf
          apply stepC_inert
          intro y hy
          have hyK : y ∉ K := h1 c hcK hSc y hy
          refine ⟨fun h => hyK (h ▸ hcK), ?_⟩
          by_contra h0
          exact hyK (hf y h0)
        rw [hin cnt hK, hin cnt' hK']
        exact ih cnt cnt' hcs' hK hK' h3
      · -- active step: agrees outside S, untouched on S
        have hK₁ : ∀ y, stepC inv cnt c y ≠ 0 → y ∈ K := fun y hy =>
          hK y (fun h0 => hy (Nat.le_antisymm ((stepC_le _ _ _ _).trans h0.le) (Nat.zero_le _)))
        have hK₁' : ∀ y, stepC inv cnt' c y ≠ 0 → y ∈ K := fun y hy =>
          hK' y (fun h0 => hy (Nat.le_antisymm ((stepC_le _ _ _ _).trans h0.le) (Nat.zero_le _)))
        have hcc : cnt c = cnt' c := h3 c hSc
        have key : (∀ x, ¬ S x → stepC inv cnt c x = stepC inv cnt' c x) ∧
            (∀ x, S x → stepC inv cnt c x = cnt x ∧ stepC inv cnt' c x = cnt' x) := by
          constructor
          · intro x hx
            exact stepC_congr hcc (fun y hy => h3 y (h2 c hcK hSc y hy)) (h3 x hx)
          · intro x hx
            have hxc : x ≠ c := fun h => hSc (h ▸ hx)
            have hxy : ∀ y, inv c = some y → x ≠ y := fun y hy h => h2 c hcK hSc y hy (h ▸ hx)
            exact ⟨stepC_of_ne hxc hxy, stepC_of_ne hxc hxy⟩
        obtain ⟨ih1, ih2⟩ := ih _ _ hcs' hK₁ hK₁' key.1
        refine ⟨ih1, fun x hx => ?_⟩
        obtain ⟨e1, e2⟩ := ih2 x hx
        obtain ⟨f1, f2⟩ := key.2 x hx
        exact ⟨e1.trans f1, e2.trans f2⟩

/-! ## `cancel` is the walk -/

theorem cntOf_cancelAt {inv : C → Option C} {l : List (C × Nat)} (hl : (l.map Prod.fst).Nodup)
    {i : Nat} {x : C} (hi : (l.map Prod.fst)[i]? = some x) :
    cntOf (cancelAt inv l i) = stepC inv (cntOf l) x := by
  have hil : ∃ xc, l[i]? = some (x, xc) := by
    rw [List.getElem?_map] at hi
    rcases h : l[i]? with _ | ⟨x', xc⟩
    · rw [h] at hi; simp at hi
    · rw [h] at hi
      simp only [Option.map_some, Option.some.injEq] at hi
      exact ⟨xc, by rw [hi]⟩
  obtain ⟨xc, hil⟩ := hil
  have hxc : cntOf l x = xc := cntOf_of_mem hl (List.getElem?_eq_some_iff.1 hil |>.2 ▸
    List.getElem_mem _)
  unfold cancelAt stepC
  rw [hil, hxc]
  simp only
  by_cases h0 : xc = 0
  · simp [h0]
  simp only [h0, ↓reduceIte]
  rcases hinv : inv x with _ | y
  · rfl
  simp only
  by_cases hyx : y = x
  · subst hyx
    simp only [↓reduceIte]
    by_cases h1 : 1 < xc
    · simp only [h1, ↓reduceIte]
      exact cntOf_set hl hil _
    · simp [h1]
  · simp only [hyx, ↓reduceIte]
    rcases hfind : l.findIdx? (fun e => e.1 = y) with _ | j
    · -- `y` is absent: its count is zero, the step is the identity
      have hy0 : cntOf l y = 0 := by
        apply cntOf_of_notMem
        intro hy
        obtain ⟨e, he, rfl⟩ := List.mem_map.1 hy
        have := List.findIdx?_eq_none_iff.1 hfind e he
        simp at this
      simp only [hfind, hy0, Nat.min_zero, Nat.sub_zero]
      rw [← hxc, Function.update_eq_self, ← hy0, Function.update_eq_self]
    · obtain ⟨hj, hpj, -⟩ := List.findIdx?_eq_some_iff_getElem.1 hfind
      simp only [decide_eq_true_eq] at hpj
      have hjl : l[j]? = some (y, l[j].2) := by
        rw [List.getElem?_eq_getElem hj]
        congr 1
        exact Prod.ext hpj rfl
      simp only [hfind, hjl]
      have hyc : cntOf l y = l[j].2 := by
        rw [← hpj]
        exact cntOf_of_mem hl (List.getElem_mem hj)
      have hjl' : (l.set i (x, xc - min xc l[j].2))[j]? = some (y, l[j].2) := by
        have hij : i ≠ j := by
          rintro rfl
          have := List.getElem?_eq_getElem hj
          rw [hil] at this
          exact hyx ((Prod.mk.inj (Option.some.inj this)).1.symm ▸ hpj).symm
        rw [List.getElem?_eq_getElem (by simpa using hj), List.getElem_set_ne hij]
        congr 1
        exact Prod.ext hpj rfl
      have hnd' : ((l.set i (x, xc - min xc l[j].2)).map Prod.fst).Nodup := by
        rw [map_fst_set (by rw [List.getElem?_map, hil]; rfl)]; exact hl
      rw [cntOf_set hnd' hjl', cntOf_set hl hil, hyc]

theorem cntOf_cancelSteps {inv : C → Option C} {l : List (C × Nat)}
    (hl : (l.map Prod.fst).Nodup) :
    ∀ i, i ≤ l.length →
      cntOf (cancelSteps inv l i) = walk inv ((l.map Prod.fst).take i) (cntOf l) := by
  intro i
  induction i with
  | zero => intros; rfl
  | succ i ih =>
      intro hi
      rw [cancelSteps, List.take_add_one, walk_append]
      have hnd : ((cancelSteps inv l i).map Prod.fst).Nodup := by
        rw [cancelSteps_map_fst]; exact hl
      have hx : ∃ x, (l.map Prod.fst)[i]? = some x :=
        ⟨_, List.getElem?_eq_getElem (by simpa using hi)⟩
      obtain ⟨x, hx⟩ := hx
      have hx' : ((cancelSteps inv l i).map Prod.fst)[i]? = some x := by
        rw [cancelSteps_map_fst]; exact hx
      rw [cntOf_cancelAt hnd hx', ih (by omega), hx]
      rfl

/-- The cancellation pass, per class, is the walk over the classes. -/
theorem cntOf_cancel (inv : C → Option C) {l : List (C × Nat)} (hl : (l.map Prod.fst).Nodup) :
    cntOf (cancel inv l) = walk inv (l.map Prod.fst) (cntOf l) := by
  unfold cancel
  have : cntOf ((cancelSteps inv l l.length).filter (fun e => e.2 ≠ 0)) =
      cntOf (cancelSteps inv l l.length) := by
    unfold cntOf; rw [ofEntries_filter_nonzero]
  rw [this, cntOf_cancelSteps hl _ le_rfl, List.take_of_length_le (by simp)]

/-! ## Sorted class lists -/

/-- A strictly sorted list is the sort of its finset. -/
theorem sort_toFinset_of_pairwise {l : List C} (hl : l.Pairwise (· < ·)) :
    l.toFinset.sort (· ≤ ·) = l :=
  (List.toFinset_sort _ (hl.imp (fun h => Nat.ne_of_lt h))).2 (hl.imp (fun h => Nat.le_of_lt h))

theorem sort_pairwise (K : Finset C) : (K.sort (· ≤ ·)).Pairwise (· < ·) :=
  List.sortedLT_iff_pairwise.1 (Finset.sortedLT_sort _)

/-- Filtering a sorted finset list is the sorted list of the filtered finset. -/
theorem sort_filter (K : Finset C) (p : C → Bool) :
    (K.sort (· ≤ ·)).filter p = (K.filter (fun c => p c = true)).sort (· ≤ ·) := by
  have hp : ((K.sort (· ≤ ·)).filter p).Pairwise (· < ·) :=
    (sort_pairwise K).sublist List.filter_sublist
  rw [← sort_toFinset_of_pairwise hp]
  congr 1
  ext c
  simp

/-- The walk over the sorted classes of any finset containing the support. -/
def walkF (inv : C → Option C) (K : Finset C) (cnt : C → Nat) : C → Nat :=
  walk inv (K.sort (· ≤ ·)) cnt

theorem walkF_mono (inv : C → Option C) {K K' : Finset C} (hKK' : K ⊆ K') (cnt : C → Nat)
    (hsupp : ∀ y, cnt y ≠ 0 → y ∈ K) : walkF inv K' cnt = walkF inv K cnt := by
  unfold walkF
  rw [walk_filter inv (fun c => decide (c ∈ K)) _ cnt, sort_filter]
  · congr 2
    ext c
    simp only [Finset.mem_filter, decide_eq_true_eq, and_iff_right_iff_imp]
    exact fun h => hKK' h
  · intro c _ hc
    by_contra h0
    simp [hsupp c h0] at hc

/-! ## The AC normal form per class -/

/-- Identity drop and nilpotent clamp on one count. -/
def preNF (laws : Laws) (x : C) (n : Nat) : Nat :=
  let n₁ := if laws.unit = some x then 0 else n
  match laws.nilpotent with
  | none => n₁
  | some r => n₁ % r

/-- The AC normal form of a multiset, per class: the walk of the inverse
cancellation (if any) over the sorted classes of `K` (any finset holding the
support) on the dropped and clamped counts. -/
def cntNF (laws : Laws) (K : Finset C) (M : Multiset C) : C → Nat :=
  match laws.inv with
  | none => fun x => preNF laws x (M.count x)
  | some inv => walkF inv K (fun x => preNF laws x (M.count x))

theorem preNF_le (laws : Laws) (x : C) (n : Nat) : preNF laws x n ≤ n := by
  unfold preNF
  split
  · split <;> simp
  · split
    · exact le_rfl
    · exact Nat.mod_le _ _

theorem preNF_support {laws : Laws} {x : C} {n : Nat} (h : preNF laws x n ≠ 0) : n ≠ 0 :=
  fun h0 => h (Nat.le_antisymm ((preNF_le _ _ _).trans h0.le) (Nat.zero_le _))

theorem cntOf_coalesce (v : List (C × Nat)) (x : C) :
    cntOf (coalesce v) x = (ofEntries v).count x := by
  unfold cntOf coalesce; rw [ofEntries_entries]

theorem cntOf_dropUnit (u : Option C) {l : List (C × Nat)} (hl : (l.map Prod.fst).Nodup)
    (x : C) : cntOf (dropUnit u l) x = if u = some x then 0 else cntOf l x := by
  rcases u with _ | u
  · simp [dropUnit]
  simp only [dropUnit, Option.some.injEq]
  by_cases hux : u = x
  · subst hux
    simp only [↓reduceIte]
    apply cntOf_of_notMem
    intro h
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 h
    simp at he
  · simp only [hux, ↓reduceIte]
    have hnd : ((l.filter (fun e => e.1 ≠ u)).map Prod.fst).Nodup :=
      hl.sublist (List.filter_sublist.map Prod.fst)
    by_cases hx : x ∈ l.map Prod.fst
    · obtain ⟨e, he, rfl⟩ := List.mem_map.1 hx
      have he' : e ∈ l.filter (fun e => e.1 ≠ u) :=
        List.mem_filter.2 ⟨he, by simpa using Ne.symm hux⟩
      rw [cntOf_of_mem hnd he', cntOf_of_mem hl he]
    · rw [cntOf_of_notMem hx, cntOf_of_notMem]
      intro h
      obtain ⟨e, he, rfl⟩ := List.mem_map.1 h
      exact hx (List.mem_map_of_mem (List.mem_filter.1 he).1)

theorem cntOf_clamp (r : Option Nat) {l : List (C × Nat)} (hl : (l.map Prod.fst).Nodup)
    (x : C) : cntOf (clamp r l) x = match r with | none => cntOf l x | some r => cntOf l x % r := by
  rcases r with _ | r
  · rfl
  simp only [clamp]
  have h1 : cntOf ((l.map (fun e => (e.1, e.2 % r))).filter (fun e => e.2 ≠ 0)) x =
      cntOf (l.map (fun e => (e.1, e.2 % r))) x := by
    unfold cntOf; rw [ofEntries_filter_nonzero]
  rw [h1]
  have hnd' : ((l.map (fun e => (e.1, e.2 % r))).map Prod.fst).Nodup := by
    rw [List.map_map]; exact hl
  by_cases hx : x ∈ l.map Prod.fst
  · obtain ⟨e, he, rfl⟩ := List.mem_map.1 hx
    have he' : (e.1, e.2 % r) ∈ l.map (fun e => (e.1, e.2 % r)) := List.mem_map_of_mem he
    rw [cntOf_of_mem hnd' he', cntOf_of_mem hl he]
  · rw [cntOf_of_notMem hx, cntOf_of_notMem]
    · simp
    · rw [List.map_map]; exact hx

/-- The clamped, dropped list of the pipeline, per class. -/
theorem cntOf_pre (laws : Laws) (v : List (C × Nat)) :
    cntOf (clamp laws.nilpotent (dropUnit laws.unit (coalesce v))) =
      fun x => preNF laws x ((ofEntries v).count x) := by
  funext x
  rw [cntOf_clamp _ (dropUnit_canonical laws.unit (coalesce_canonical v)).nodup,
    cntOf_dropUnit _ (coalesce_canonical v).nodup, cntOf_coalesce]
  rfl

/-- The AC pipeline, per class: `cntNF` over any finset holding the classes
of `v`. -/
theorem cntOf_normalizeList_ac (laws : Laws) (v : List (C × Nat)) {K : Finset C}
    (hK : ∀ e ∈ v, 0 < e.2 → e.1 ∈ K) :
    cntOf (normalizeList .ac laws v) = cntNF laws K (ofEntries v) := by
  have hsupp : ∀ y, preNF laws y ((ofEntries v).count y) ≠ 0 → y ∈ K := by
    intro y hy
    have := preNF_support hy
    obtain ⟨e, he, rfl, hpos⟩ := mem_ofEntries.1 (Multiset.count_ne_zero.1 this)
    exact hK e he hpos
  unfold normalizeList cntNF
  simp only
  rcases hinv : laws.inv with _ | inv
  · exact cntOf_pre laws v
  · have hcan := clamp_canonical laws.nilpotent (dropUnit_canonical laws.unit (coalesce_canonical v))
    rw [cntOf_cancel inv hcan.nodup, cntOf_pre laws v]
    have hsub : ((clamp laws.nilpotent (dropUnit laws.unit (coalesce v))).map Prod.fst).toFinset
        ⊆ K := by
      intro c hc
      rw [List.mem_toFinset] at hc
      obtain ⟨e, he, rfl⟩ := List.mem_map.1 hc
      have hpos := hcan.2 e he
      have : cntOf (clamp laws.nilpotent (dropUnit laws.unit (coalesce v))) e.1 ≠ 0 := by
        rw [cntOf_of_mem hcan.nodup he]; omega
      rw [cntOf_pre] at this
      exact hsupp e.1 this
    have hsupp' : ∀ y, preNF laws y ((ofEntries v).count y) ≠ 0 →
        y ∈ ((clamp laws.nilpotent (dropUnit laws.unit (coalesce v))).map Prod.fst).toFinset := by
      intro y hy
      rw [List.mem_toFinset]
      apply cntOf_ne_zero_mem
      rw [cntOf_pre]
      exact hy
    rw [← sort_toFinset_of_pairwise hcan.1]
    change walkF inv _ _ = walkF inv K _
    rw [walkF_mono inv hsub _ hsupp']

/-! ## Leaves with the folded count -/

/-- A leaf: the class it opened, the folded count and the leaf's entries
(the member's children scaled by the folded count). -/
structure LeafL where
  X : C
  k : Nat
  L : List (C × Nat)
  deriving DecidableEq, Repr

/-- The leaf group (the classes of the leaf's entries). -/
def LeafL.g (l : LeafL) : List C := l.L.map Prod.fst

/-- Forgetting the count data. -/
def LeafL.toX (l : LeafL) : LeafX := (l.X, l.g)

/-- A raw view with its leaves. -/
abbrev RawL := List (C × Nat) × List LeafL

/-- `leafifyX` with the folded count and the entries recorded. -/
def leafifyL (X : C) (k : Nat) (v : List (C × Nat)) (ls : List LeafL) : List LeafL :=
  if ls = [] then [⟨X, k, v⟩] else ls

/-- `OTX` with the folded count per leaf. -/
inductive OTL (ctx : Ctx) : Nat → Finset C → List (C × Nat) → List (C × Nat) →
    List LeafL → Nat → Prop
  | nil {k : Nat} {P : Finset C} : OTL ctx k P [] [] [] 0
  | keep {k : Nat} {P : Finset C} {X : C} {j : Nat} {rest v₂ : List (C × Nat)}
      {l₂ : List LeafL} {o : Nat} :
      OTL ctx k P rest v₂ l₂ o → OTL ctx k P ((X, j) :: rest) ((X, k * j) :: v₂) l₂ o
  | opn {k : Nat} {P : Finset C} {X : C} {j : Nat} {rest : List (C × Nat)}
      {id : NodeId} {m : Node} {v₁ v₂ : List (C × Nat)} {l₁ l₂ : List LeafL} {o₁ o₂ : Nat} :
      X ∉ P → ctx.IsMember id m X →
      OTL ctx (k * j) (insert X P) (kids ctx.κ m.children) v₁ l₁ o₁ →
      OTL ctx k P rest v₂ l₂ o₂ →
      OTL ctx k P ((X, j) :: rest) (v₁ ++ v₂) (leafifyL X (k * j) v₁ l₁ ++ l₂) (o₁ + o₂ + 1)

def ViewNodeL (ctx : Ctx) (m : Node) (k : Nat) (P : Finset C) (v : List (C × Nat))
    (ls : List LeafL) (o : Nat) : Prop :=
  OTL ctx k P (kids ctx.κ m.children) v ls o

def ViewOptL (ctx : Ctx) (X : C) (k : Nat) (P : Finset C) (v : List (C × Nat))
    (ls : List LeafL) (o : Nat) : Prop :=
  (v = [(X, k)] ∧ ls = [] ∧ o = 0) ∨
    (X ∉ P ∧ ∃ id m l₁ o₁, ctx.IsMember id m X ∧
      ViewNodeL ctx m k (insert X P) v l₁ o₁ ∧ ls = leafifyL X k v l₁ ∧ o = o₁ + 1)

/-- A raw view of the root `n` with leaves and `o` openings. -/
def RawViewL (ctx : Ctx) (n : Node) (v : List (C × Nat)) (ls : List LeafL) (o : Nat) : Prop :=
  ViewNodeL ctx n 1 ∅ v ls o

theorem leafifyL_ne_nil (X : C) (k : Nat) (v : List (C × Nat)) (ls : List LeafL) :
    leafifyL X k v ls ≠ [] := by
  unfold leafifyL
  split <;> simp_all

theorem leafifyL_map_toX (X : C) (k : Nat) (v : List (C × Nat)) (ls : List LeafL) :
    (leafifyL X k v ls).map LeafL.toX = leafifyX X v (ls.map LeafL.toX) := by
  unfold leafifyL leafifyX
  by_cases h : ls = []
  · subst h; simp [LeafL.toX, LeafL.g]
  · simp [h]

/-- Forgetting the counts gives an `OTX`. -/
theorem OTL.toOTX {ctx : Ctx} {k : Nat} {P : Finset C} {ks v : List (C × Nat)}
    {ls : List LeafL} {o : Nat} (h : OTL ctx k P ks v ls o) :
    OTX ctx k P ks v (ls.map LeafL.toX) o := by
  induction h with
  | nil => exact OTX.nil
  | keep _ ih => exact OTX.keep ih
  | opn hX hmem _ _ ih₁ ih₂ =>
      rw [List.map_append, leafifyL_map_toX]
      exact OTX.opn hX hmem ih₁ ih₂

/-- Every `OTX` is the projection of some `OTL`. -/
theorem OTX.toOTL {ctx : Ctx} {k : Nat} {P : Finset C} {ks v : List (C × Nat)}
    {ls : List LeafX} {o : Nat} (h : OTX ctx k P ks v ls o) :
    ∃ lsl : List LeafL, OTL ctx k P ks v lsl o ∧ lsl.map LeafL.toX = ls := by
  induction h with
  | nil => exact ⟨[], OTL.nil, rfl⟩
  | keep _ ih =>
      obtain ⟨lsl, h, rfl⟩ := ih
      exact ⟨lsl, OTL.keep h, rfl⟩
  | @opn k _ X j _ _ _ v₁ _ _ _ _ _ hX hmem _ _ ih₁ ih₂ =>
      obtain ⟨lsl₁, h₁, rfl⟩ := ih₁
      obtain ⟨lsl₂, h₂, rfl⟩ := ih₂
      exact ⟨leafifyL X (k * j) v₁ lsl₁ ++ lsl₂, OTL.opn hX hmem h₁ h₂,
        by rw [List.map_append, leafifyL_map_toX]⟩

theorem RawViewL.toRawViewX {ctx : Ctx} {n : Node} {v : List (C × Nat)} {ls : List LeafL}
    {o : Nat} (h : RawViewL ctx n v ls o) : RawViewX ctx n v (ls.map LeafL.toX) o :=
  OTL.toOTX h

theorem RawViewX.toRawViewL {ctx : Ctx} {n : Node} {v : List (C × Nat)} {ls : List LeafX}
    {o : Nat} (h : RawViewX ctx n v ls o) :
    ∃ lsl : List LeafL, RawViewL ctx n v lsl o ∧ lsl.map LeafL.toX = ls :=
  OTX.toOTL h

theorem RawViewL.pos {ctx : Ctx} {n : Node} {v : List (C × Nat)} {ls : List LeafL} {o : Nat}
    (h : RawViewL ctx n v ls o) : ∀ e ∈ v, 0 < e.2 :=
  RawViewX.pos h.toRawViewX

theorem OTL.all_kept_aux {ctx : Ctx} {k : Nat} {P : Finset C} {ks v : List (C × Nat)}
    {ls : List LeafL} {o : Nat} (h : OTL ctx k P ks v ls o) (hls : ls = []) :
    v = scale k ks ∧ o = 0 := by
  induction h with
  | nil => exact ⟨rfl, rfl⟩
  | keep _ ih =>
      subst hls
      obtain ⟨h1, h2⟩ := ih rfl
      exact ⟨by simp [scale, h1], h2⟩
  | opn _ _ _ _ _ _ =>
      exact absurd (List.append_eq_nil_iff.mp hls).1 (leafifyL_ne_nil _ _ _ _)

theorem OTL.all_kept {ctx : Ctx} {k : Nat} {P : Finset C} {ks v : List (C × Nat)} {o : Nat}
    (h : OTL ctx k P ks v [] o) : v = scale k ks ∧ o = 0 :=
  OTL.all_kept_aux h rfl

/-- Closing the leaf `l`: its entries are the member's children scaled by
`l.k > 0`, and replacing the opening by `keep` gives a tree with one opening
fewer whose raw view has `(l.X, l.k)` in place of the leaf's entries. -/
theorem OTL.refold {ctx : Ctx} {k : Nat} {P : Finset C} {ks v : List (C × Nat)}
    {ls : List LeafL} {o : Nat} {l : LeafL} (h : OTL ctx k P ks v ls o) (hl : l ∈ ls)
    (hk : 0 < k) (hks : ∀ e ∈ ks, 0 < e.2) :
    ∃ (v₁ v₂ : List (C × Nat)) (id : NodeId) (m : Node) (ls' : List LeafL) (o' : Nat),
      ctx.IsMember id m l.X ∧ l.L = scale l.k (kids ctx.κ m.children) ∧
      v = v₁ ++ l.L ++ v₂ ∧ 0 < l.k ∧
      OTL ctx k P ks (v₁ ++ (l.X, l.k) :: v₂) ls' o' ∧ o = o' + 1 := by
  induction h with
  | nil => simp at hl
  | @keep k P X j rest v₂ l₂ o _ ih =>
      obtain ⟨v₁', v₂', id, m, ls', o', hmem, hL, hv, hk', ht, ho⟩ :=
        ih hl hk (fun e he => hks e (List.mem_cons_of_mem _ he))
      refine ⟨(X, k * j) :: v₁', v₂', id, m, ls', o', hmem, hL, ?_, hk', ?_, ho⟩
      · subst hv; simp
      · exact OTL.keep ht
  | @opn k P X j rest id m v₁ v₂ l₁ l₂ o₁ o₂ hXP hmem h₁ h₂ ih₁ ih₂ =>
      have hkj : 0 < k * j := Nat.mul_pos hk (hks (X, j) (List.mem_cons_self ..))
      rcases List.mem_append.mp hl with hl₁ | hl₂
      · by_cases hl₁' : l₁ = []
        · subst hl₁'
          simp only [leafifyL, ite_true, List.mem_singleton] at hl₁
          subst hl₁
          obtain ⟨hv₁, ho₁⟩ := OTL.all_kept h₁
          subst ho₁
          refine ⟨[], v₂, id, m, l₂, o₂, hmem, hv₁, rfl, hkj, ?_, by omega⟩
          exact OTL.keep h₂
        · simp only [leafifyL, hl₁', ↓reduceIte] at hl₁
          obtain ⟨v₁', v₂', id', m', ls', o', hmem', hL, hv, hk', ht, ho⟩ :=
            ih₁ hl₁ hkj (kids_pos _ _)
          refine ⟨v₁', v₂' ++ v₂, id', m',
            leafifyL X (k * j) (v₁' ++ (l.X, l.k) :: v₂') ls' ++ l₂, o' + o₂ + 1, hmem', hL, ?_,
            hk', ?_, by omega⟩
          · subst hv; simp
          · have := OTL.opn hXP hmem ht h₂
            simpa using this
      · obtain ⟨v₁', v₂', id', m', ls', o', hmem', hL, hv, hk', ht, ho⟩ :=
          ih₂ hl₂ hk (fun e he => hks e (List.mem_cons_of_mem _ he))
        refine ⟨v₁ ++ v₁', v₂', id', m', leafifyL X (k * j) v₁ l₁ ++ ls', o₁ + o' + 1, hmem',
          hL, ?_, hk', ?_, by omega⟩
        · subst hv; simp
        · have := OTL.opn hXP hmem h₁ ht
          simpa using this

theorem RawViewL.refold {ctx : Ctx} {n : Node} {v : List (C × Nat)} {ls : List LeafL}
    {o : Nat} {l : LeafL} (h : RawViewL ctx n v ls o) (hl : l ∈ ls) :
    ∃ (v₁ v₂ : List (C × Nat)) (id : NodeId) (m : Node) (ls' : List LeafL) (o' : Nat),
      ctx.IsMember id m l.X ∧ l.L = scale l.k (kids ctx.κ m.children) ∧
      v = v₁ ++ l.L ++ v₂ ∧ 0 < l.k ∧
      RawViewL ctx n (v₁ ++ (l.X, l.k) :: v₂) ls' o' ∧ o = o' + 1 :=
  OTL.refold h hl Nat.one_pos (kids_pos _ _)

/-! ## Inertness of a refold -/

/-- The classes a refold of `l` touches: the opened class and the leaf's
classes. -/
def LeafL.touched (l : LeafL) : List C := l.X :: l.g

/-- The classes present in the view and in its refold (a superset). -/
def presentL (v : List (C × Nat)) (l : LeafL) : List C := l.X :: v.map Prod.fst

/-- No cancel pair between the touched classes and the present ones, in
either direction. -/
def NoCancel (inv : C → Option C) (P S : List C) : Prop :=
  (∀ x ∈ S, ∀ y, inv x = some y → y ∉ P) ∧ (∀ y ∈ P, ∀ z, inv y = some z → z ∉ S)

/-- The count of `X` after the refold. -/
def refoldCount (v : List (C × Nat)) (l : LeafL) : Nat :=
  (ofEntries v).count l.X - (ofEntries l.L).count l.X + l.k

/-- **Inertness of a leaf's refold, AC** (the weakest condition the
completeness induction needs): `X` is not the unit, its refolded count does
not clamp to zero, and no cancel pair touches `X` or a leaf class. -/
structure InertAC (laws : Laws) (v : List (C × Nat)) (l : LeafL) : Prop where
  unit : laws.unit ≠ some l.X
  clamp : ∀ r, laws.nilpotent = some r → refoldCount v l % r ≠ 0
  cancel : ∀ inv, laws.inv = some inv → NoCancel inv (presentL v l) l.touched

/-- The executable test of `InertAC` (its negation is the flag the
enumerator records). -/
def nonInertAC (laws : Laws) (v : List (C × Nat)) (l : LeafL) : Bool :=
  decide (laws.unit = some l.X) ||
  (match laws.nilpotent with
   | none => false
   | some r => decide (refoldCount v l % r = 0)) ||
  (match laws.inv with
   | none => false
   | some inv =>
       l.touched.any (fun x => match inv x with
         | none => false
         | some y => decide (y ∈ presentL v l)) ||
       (presentL v l).any (fun y => match inv y with
         | none => false
         | some z => decide (z ∈ l.touched)))

theorem nonInertAC_false_iff (laws : Laws) (v : List (C × Nat)) (l : LeafL) :
    nonInertAC laws v l = false ↔ InertAC laws v l := by
  unfold nonInertAC
  constructor
  · intro h
    simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at h
    obtain ⟨⟨hu, hc⟩, hi⟩ := h
    refine ⟨hu, ?_, ?_⟩
    · intro r hr
      rw [hr] at hc
      simpa using hc
    · intro inv hinv
      rw [hinv] at hi
      simp only [Bool.or_eq_false_iff, List.any_eq_false] at hi
      obtain ⟨h1, h2⟩ := hi
      constructor
      · intro x hx y hy
        have := h1 x hx
        rw [hy] at this
        simpa using this
      · intro y hy z hz
        have := h2 y hy
        rw [hz] at this
        simpa using this
  · intro h
    simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not]
    refine ⟨⟨h.unit, ?_⟩, ?_⟩
    · rcases hr : laws.nilpotent with _ | r
      · rfl
      · simpa using h.clamp r hr
    · rcases hinv : laws.inv with _ | inv
      · rfl
      · obtain ⟨h1, h2⟩ := h.cancel inv hinv
        simp only [Bool.or_eq_false_iff, List.any_eq_false]
        constructor
        · intro x hx
          rcases hy : inv x with _ | y
          · simp
          · simpa using h1 x hx y hy
        · intro y hy
          rcases hz : inv y with _ | z
          · simp
          · simpa using h2 y hy z hz

/-- Inertness for sets: `X` is not the unit. -/
def InertACI (laws : Laws) (l : LeafL) : Prop := laws.unit ≠ some l.X

/-- Inertness for sequences: `X` is not the unit, and the leaf's block does
not vanish (some child is not the unit). -/
def InertAssoc (laws : Laws) (l : LeafL) : Prop :=
  laws.unit ≠ some l.X ∧ ∃ c ∈ l.g, laws.unit ≠ some c

/-- The non-inertness flag the enumerator records per leaf, per kind. -/
def nonInertB (κ : FlatKind) (laws : Laws) (v : List (C × Nat)) (l : LeafL) : Bool :=
  match κ with
  | .ac => nonInertAC laws v l
  | .aci => decide (laws.unit = some l.X)
  | .assoc => decide (laws.unit = some l.X) || l.g.all (fun c => decide (laws.unit = some c))

theorem nonInertB_ac_false_iff (laws : Laws) (v : List (C × Nat)) (l : LeafL) :
    nonInertB .ac laws v l = false ↔ InertAC laws v l :=
  nonInertAC_false_iff laws v l

theorem nonInertB_aci_false_iff (laws : Laws) (v : List (C × Nat)) (l : LeafL) :
    nonInertB .aci laws v l = false ↔ InertACI laws l := by
  simp [nonInertB, InertACI]

theorem nonInertB_assoc_false_iff (laws : Laws) (v : List (C × Nat)) (l : LeafL) :
    nonInertB .assoc laws v l = false ↔ InertAssoc laws l := by
  simp [nonInertB, InertAssoc]

/-! ## The demand rule under laws -/

/-- A leaf with its non-inertness flag. -/
abbrev LeafF := LeafL × Bool

/-- The flagged leaves of a raw view. -/
def flagLeaves (κ : FlatKind) (laws : Laws) (v : List (C × Nat)) (ls : List LeafL) :
    List LeafF :=
  ls.map (fun l => (l, nonInertB κ laws v l))

/-- The per-leaf condition under laws: the leaf group holds a taken class,
or the opened class is taken, or closing the leaf is not inert. -/
def LeafF.okL (taken : List C) (l : LeafF) : Prop :=
  l.1.X ∈ taken ∨ (∃ c ∈ l.1.g, c ∈ taken) ∨ l.2 = true

instance (taken : List C) (l : LeafF) : Decidable (l.okL taken) := by
  unfold LeafF.okL; infer_instance

theorem LeafF.okL_of_ok {taken : List C} {l : LeafL} {b : Bool}
    (h : l.toX.ok taken) : LeafF.okL taken (l, b) := by
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)

/-- A demand with flagged leaves. -/
structure DemandL where
  unconditional : Bool
  alts : List (List LeafF)
  deriving DecidableEq

/-- The demand rule under laws. -/
def DemandL.acceptsLaws (d : DemandL) (taken : List C) : Prop :=
  d.unconditional = true ∨ ∃ ls ∈ d.alts, ∀ l ∈ ls, l.okL taken

def DemandL.acceptsLawsB (d : DemandL) (taken : List C) : Bool :=
  d.unconditional || d.alts.any (fun ls => ls.all (fun l => decide (l.okL taken)))

theorem DemandL.acceptsLawsB_iff (d : DemandL) (taken : List C) :
    d.acceptsLawsB taken = true ↔ d.acceptsLaws taken := by
  simp [DemandL.acceptsLawsB, DemandL.acceptsLaws]

/-- The opening trees giving `w`, as flagged leaves. -/
def AltsL (ctx : Ctx) (laws : Laws) (n : Node) (w : List (C × Nat)) : Set (List LeafF) :=
  { fls | ∃ v ls o, RawViewL ctx n v ls o ∧ normalize ctx.κ laws v = .node w ∧
      fls = flagLeaves ctx.κ laws v ls }

def AltsLAccept (A : Set (List LeafF)) (taken : List C) : Prop :=
  [] ∈ A ∨ ∃ ls ∈ A, ∀ l ∈ ls, l.okL taken

/-! ## The enumerator with flagged leaves -/

def kidsOfL (opt : C → Nat → Finset C → List RawL) :
    List (C × Nat) → Nat → Finset C → List RawL
  | [], _, _ => [([], [])]
  | (X, j) :: rest, k, P =>
      (opt X (k * j) P).flatMap (fun r₁ =>
        (kidsOfL opt rest k P).map (fun r₂ => (r₁.1 ++ r₂.1, r₁.2 ++ r₂.2)))

def rawOptL (ctx : Ctx) : Nat → C → Nat → Finset C → List RawL
  | 0, X, k, _ => [([(X, k)], [])]
  | fuel + 1, X, k, P =>
      ([(X, k)], []) ::
        (if X ∈ P then []
         else (ctx.members X).flatMap (fun p =>
           (kidsOfL (rawOptL ctx fuel) (kids ctx.κ p.2.children) k (insert X P)).map
             (fun r => (r.1, leafifyL X k r.1 r.2))))

def rawNodeL (ctx : Ctx) (fuel : Nat) (m : Node) (k : Nat) (P : Finset C) : List RawL :=
  kidsOfL (rawOptL ctx fuel) (kids ctx.κ m.children) k P

/-- A record: the canonical view and the flagged leaves. -/
abbrev RecL := List (C × Nat) × List LeafF

/-- The records of the root: the raw views that normalize to a node, with
the non-inertness flag computed per leaf from the raw view. -/
def rawRecordsL (ctx : Ctx) (laws : Laws) (n : Node) : List RecL :=
  (rawNodeL ctx (fuelOf ctx.G) n 1 ∅).filterMap (fun r =>
    match normalize ctx.κ laws r.1 with
    | .node w => some (w, flagLeaves ctx.κ laws r.1 r.2)
    | _ => none)

def altsOfL (recs : List RecL) (w : List (C × Nat)) : List (List LeafF) :=
  (recs.filter (fun r => r.1 = w)).map Prod.snd

def demandOfL (recs : List RecL) (w : List (C × Nat)) : DemandL :=
  if [] ∈ altsOfL recs w then ⟨true, []⟩ else ⟨false, altsOfL recs w⟩

def enumerateFromL (recs : List RecL) : List (List (C × Nat) × DemandL) :=
  (recs.map Prod.fst).dedup.map (fun w => (w, demandOfL recs w))

/-- `enumerateX` with the folded count per leaf and the non-inertness flag. -/
def enumerateL (ctx : Ctx) (laws : Laws) (n : Node) : List (List (C × Nat) × DemandL) :=
  enumerateFromL (rawRecordsL ctx laws n)

/-! ### Constructor shapes -/

theorem OTL.cons_opt {ctx : Ctx} {k j : Nat} {P : Finset C} {X : C}
    {rest v₁ v₂ : List (C × Nat)} {l₁ l₂ : List LeafL} {o₁ o₂ : Nat}
    (h₁ : ViewOptL ctx X (k * j) P v₁ l₁ o₁) (h₂ : OTL ctx k P rest v₂ l₂ o₂) :
    OTL ctx k P ((X, j) :: rest) (v₁ ++ v₂) (l₁ ++ l₂) (o₁ + o₂) := by
  rcases h₁ with ⟨rfl, rfl, rfl⟩ | ⟨hX, id, m, l, o, hmem, hm, rfl, rfl⟩
  · simpa using OTL.keep h₂
  · rw [show o + 1 + o₂ = o + o₂ + 1 by omega]
    exact OTL.opn hX hmem hm h₂

theorem ViewOptL.keep {ctx : Ctx} {X : C} {k : Nat} {P : Finset C} :
    ViewOptL ctx X k P [(X, k)] [] 0 := Or.inl ⟨rfl, rfl, rfl⟩

theorem ViewOptL.opn {ctx : Ctx} {X : C} {k : Nat} {P : Finset C} {id : NodeId}
    {m : Node} {v : List (C × Nat)} {ls : List LeafL} {o : Nat}
    (hX : X ∉ P) (hmem : ctx.IsMember id m X)
    (h : ViewNodeL ctx m k (insert X P) v ls o) :
    ViewOptL ctx X k P v (leafifyL X k v ls) (o + 1) :=
  Or.inr ⟨hX, id, m, ls, o, hmem, h, rfl, rfl⟩

/-! ### Soundness of the walk -/

theorem kidsOfL_sound_of {ctx : Ctx} (opt : C → Nat → Finset C → List RawL)
    (hopt : ∀ X k P r, r ∈ opt X k P → ∃ o, ViewOptL ctx X k P r.1 r.2 o) :
    ∀ (ks : List (C × Nat)) (k : Nat) (P : Finset C) (r : RawL),
      r ∈ kidsOfL opt ks k P → ∃ o, OTL ctx k P ks r.1 r.2 o := by
  intro ks
  induction ks with
  | nil =>
      intro k P r hr
      simp only [kidsOfL, List.mem_singleton] at hr
      subst hr
      exact ⟨0, OTL.nil⟩
  | cons e rest ih =>
      intro k P r hr
      obtain ⟨X, j⟩ := e
      simp only [kidsOfL, List.mem_flatMap, List.mem_map] at hr
      obtain ⟨r₁, hr₁, r₂, hr₂, rfl⟩ := hr
      obtain ⟨o₁, h₁⟩ := hopt _ _ _ _ hr₁
      obtain ⟨o₂, h₂⟩ := ih _ _ _ hr₂
      exact ⟨_, OTL.cons_opt h₁ h₂⟩

theorem rawOptL_sound (ctx : Ctx) :
    ∀ (fuel : Nat) (X : C) (k : Nat) (P : Finset C) (r : RawL),
      r ∈ rawOptL ctx fuel X k P → ∃ o, ViewOptL ctx X k P r.1 r.2 o := by
  intro fuel
  induction fuel with
  | zero =>
      intro X k P r hr
      simp only [rawOptL, List.mem_singleton] at hr
      subst hr
      exact ⟨0, ViewOptL.keep⟩
  | succ fuel ih =>
      intro X k P r hr
      simp only [rawOptL, List.mem_cons] at hr
      rcases hr with rfl | hr
      · exact ⟨0, ViewOptL.keep⟩
      · split at hr
        · simp at hr
        · next hX =>
          simp only [List.mem_flatMap, List.mem_map] at hr
          obtain ⟨p, hp, r', hr', rfl⟩ := hr
          have hmem := Ctx.mem_members.1 hp
          obtain ⟨o, ho⟩ := kidsOfL_sound_of _ ih _ _ _ _ hr'
          exact ⟨_, ViewOptL.opn hX hmem ho⟩

theorem rawNodeL_sound {ctx : Ctx} {fuel : Nat} {m : Node} {k : Nat} {P : Finset C}
    {r : RawL} (hr : r ∈ rawNodeL ctx fuel m k P) : ∃ o, ViewNodeL ctx m k P r.1 r.2 o :=
  kidsOfL_sound_of _ (rawOptL_sound ctx fuel) _ _ _ _ hr

/-! ### Completeness of the walk -/

theorem kidsOfL_complete_of {ctx : Ctx} (fuel : Nat) (opt : C → Nat → Finset C → List RawL)
    (hopt : ∀ X k P v ls o, ViewOptL ctx X k P v ls o → P ⊆ classesOf ctx.G →
      (classesOf ctx.G).card - P.card ≤ fuel → (v, ls) ∈ opt X k P)
    {ks : List (C × Nat)} {k : Nat} {P : Finset C} {v : List (C × Nat)}
    {ls : List LeafL} {o : Nat} (h : OTL ctx k P ks v ls o)
    (hP : P ⊆ classesOf ctx.G) (hfuel : (classesOf ctx.G).card - P.card ≤ fuel) :
    (v, ls) ∈ kidsOfL opt ks k P := by
  induction h with
  | nil => simp [kidsOfL]
  | keep h₂ ih =>
      simp only [kidsOfL, List.mem_flatMap, List.mem_map]
      exact ⟨_, hopt _ _ _ _ _ _ ViewOptL.keep hP hfuel, _, ih hP hfuel, rfl⟩
  | opn hX hmem hm h₂ ih₁ ih₂ =>
      simp only [kidsOfL, List.mem_flatMap, List.mem_map]
      exact ⟨_, hopt _ _ _ _ _ _ (ViewOptL.opn hX hmem hm) hP hfuel, _, ih₂ hP hfuel, rfl⟩

theorem rawOptL_complete (ctx : Ctx) :
    ∀ (fuel : Nat) (X : C) (k : Nat) (P : Finset C) (v : List (C × Nat))
      (ls : List LeafL) (o : Nat), ViewOptL ctx X k P v ls o → P ⊆ classesOf ctx.G →
      (classesOf ctx.G).card - P.card ≤ fuel → (v, ls) ∈ rawOptL ctx fuel X k P := by
  intro fuel
  induction fuel with
  | zero =>
      intro X k P v ls o h hP hfuel
      rcases h with ⟨rfl, rfl, rfl⟩ | ⟨hX, id, m, l₁, o₁, hmem, hm, rfl, rfl⟩
      · simp [rawOptL]
      · exfalso
        have hXc : X ∈ classesOf ctx.G := IsMember.cls_mem hmem
        have hlt : P.card < (classesOf ctx.G).card :=
          Finset.card_lt_card ⟨hP, fun hsub => hX (hsub hXc)⟩
        omega
  | succ fuel ih =>
      intro X k P v ls o h hP hfuel
      rcases h with ⟨rfl, rfl, rfl⟩ | ⟨hX, id, m, l₁, o₁, hmem, hm, rfl, rfl⟩
      · simp [rawOptL]
      · simp only [rawOptL, List.mem_cons]
        right
        simp only [hX, ↓reduceIte]
        simp only [List.mem_flatMap, List.mem_map]
        refine ⟨(id, m), Ctx.mem_members.2 hmem, (v, l₁), ?_, rfl⟩
        have hXc : X ∈ classesOf ctx.G := IsMember.cls_mem hmem
        have hP' : insert X P ⊆ classesOf ctx.G := Finset.insert_subset hXc hP
        have hcard : (insert X P).card = P.card + 1 := Finset.card_insert_of_notMem hX
        exact kidsOfL_complete_of fuel _ ih hm hP' (by omega)

theorem rawViewL_mem_rawNodeL {ctx : Ctx} {n : Node} {v : List (C × Nat)}
    {ls : List LeafL} {o : Nat} (h : RawViewL ctx n v ls o) :
    (v, ls) ∈ rawNodeL ctx (fuelOf ctx.G) n 1 ∅ :=
  kidsOfL_complete_of (fuelOf ctx.G) _ (rawOptL_complete ctx (fuelOf ctx.G)) h
    (Finset.empty_subset _) (by simp [fuelOf])

/-! ### Records, demands, the distinct views -/

theorem mem_rawRecordsL {ctx : Ctx} {laws : Laws} {n : Node} {w : List (C × Nat)}
    {fls : List LeafF} :
    (w, fls) ∈ rawRecordsL ctx laws n ↔
      ∃ v ls o, RawViewL ctx n v ls o ∧ normalize ctx.κ laws v = .node w ∧
        fls = flagLeaves ctx.κ laws v ls := by
  simp only [rawRecordsL, List.mem_filterMap]
  constructor
  · rintro ⟨⟨v, ls'⟩, hr, hn⟩
    revert hn
    split
    · next w' hw' =>
      intro hn
      simp only [Option.some.injEq, Prod.mk.injEq] at hn
      obtain ⟨rfl, rfl⟩ := hn
      obtain ⟨o, ho⟩ := rawNodeL_sound hr
      exact ⟨v, ls', o, ho, hw', rfl⟩
    · intro hn
      exact absurd hn (by simp)
  · rintro ⟨v, ls, o, hv, hn, rfl⟩
    refine ⟨(v, ls), rawViewL_mem_rawNodeL hv, ?_⟩
    simp only
    rw [hn]

theorem mem_enumerateFromL {recs : List RecL} {w : List (C × Nat)} {d : DemandL} :
    (w, d) ∈ enumerateFromL recs ↔ (∃ ls, (w, ls) ∈ recs) ∧ d = demandOfL recs w := by
  simp only [enumerateFromL, List.mem_map, List.mem_dedup, Prod.mk.injEq]
  constructor
  · rintro ⟨w', hw', rfl, rfl⟩
    obtain ⟨⟨w'', ls⟩, hr, rfl⟩ := hw'
    exact ⟨⟨ls, hr⟩, rfl⟩
  · rintro ⟨⟨ls, hr⟩, rfl⟩
    exact ⟨w, ⟨(w, ls), hr, rfl⟩, rfl, rfl⟩

theorem mem_altsOfL {recs : List RecL} {w : List (C × Nat)} {ls : List LeafF} :
    ls ∈ altsOfL recs w ↔ (w, ls) ∈ recs := by
  simp only [altsOfL, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨w', ls'⟩, ⟨hr, hw⟩, hls⟩
    simp only at hw hls
    subst hw; subst hls
    exact hr
  · intro hr
    exact ⟨(w, ls), ⟨hr, rfl⟩, rfl⟩

theorem demandOfL_unconditional {recs : List RecL} {w : List (C × Nat)} :
    (demandOfL recs w).unconditional = true ↔ (w, []) ∈ recs := by
  by_cases h0 : [] ∈ altsOfL recs w
  · simp only [demandOfL, h0, ↓reduceIte, true_iff]
    exact mem_altsOfL.1 h0
  · simp only [demandOfL, h0, ↓reduceIte, Bool.false_eq_true, false_iff]
    exact fun hr => h0 (mem_altsOfL.2 hr)

theorem demandOfL_alts {recs : List RecL} {w : List (C × Nat)}
    (h : (demandOfL recs w).unconditional = false) (ls : List LeafF) :
    ls ∈ (demandOfL recs w).alts ↔ (w, ls) ∈ recs := by
  by_cases h0 : [] ∈ altsOfL recs w
  · simp [demandOfL, h0] at h
  · simp only [demandOfL, h0, ↓reduceIte]
    exact mem_altsOfL

theorem acceptsLaws_demandOfL {recs : List RecL} {w : List (C × Nat)} {taken : List C} :
    (demandOfL recs w).acceptsLaws taken ↔
      ∃ ls, (w, ls) ∈ recs ∧ ∀ l ∈ ls, l.okL taken := by
  unfold DemandL.acceptsLaws
  by_cases hu : (demandOfL recs w).unconditional = true
  · simp only [hu, true_or, true_iff]
    exact ⟨[], demandOfL_unconditional.1 hu, by simp⟩
  · have hu' : (demandOfL recs w).unconditional = false := by simpa using hu
    simp only [hu', Bool.false_eq_true, false_or]
    constructor
    · rintro ⟨ls, hls, hall⟩
      exact ⟨ls, (demandOfL_alts hu' ls).1 hls, hall⟩
    · rintro ⟨ls, hls, hall⟩
      exact ⟨ls, (demandOfL_alts hu' ls).2 hls, hall⟩

theorem flagLeaves_eq_nil_iff (κ : FlatKind) (laws : Laws) (v : List (C × Nat))
    (ls : List LeafL) : flagLeaves κ laws v ls = [] ↔ ls = [] := by
  simp [flagLeaves]

/-! ### Soundness and completeness of `enumerateL` -/

theorem views_soundL {ctx : Ctx} {laws : Laws} {n : Node} {w : List (C × Nat)}
    {d : DemandL} (h : (w, d) ∈ enumerateL ctx laws n) :
    w ∈ Views ctx laws n ∧
      (d.unconditional = true ↔ [] ∈ AltsL ctx laws n w) ∧
      (d.unconditional = false → ∀ ls, ls ∈ d.alts ↔ ls ∈ AltsL ctx laws n w) := by
  obtain ⟨⟨ls, hr⟩, rfl⟩ := mem_enumerateFromL.1 h
  obtain ⟨v, ls', o, hv, hn, -⟩ := mem_rawRecordsL.1 hr
  refine ⟨⟨v, (ls'.map LeafL.toX).map Prod.snd, hv.toRawViewX.toRawView, hn⟩, ?_, ?_⟩
  · rw [demandOfL_unconditional, mem_rawRecordsL]
    rfl
  · intro hu ls'
    rw [demandOfL_alts hu, mem_rawRecordsL]
    rfl

theorem views_completeL {ctx : Ctx} {laws : Laws} {n : Node} {v w : List (C × Nat)}
    {ls : List LeafL} {o : Nat} (hv : RawViewL ctx n v ls o)
    (hn : normalize ctx.κ laws v = .node w) :
    ∃ d, (w, d) ∈ enumerateL ctx laws n ∧
      (ls = [] → d.unconditional = true) ∧
      (ls ≠ [] → d.unconditional = true ∨ flagLeaves ctx.κ laws v ls ∈ d.alts) := by
  have hr : (w, flagLeaves ctx.κ laws v ls) ∈ rawRecordsL ctx laws n :=
    mem_rawRecordsL.2 ⟨v, ls, o, hv, hn, rfl⟩
  refine ⟨demandOfL (rawRecordsL ctx laws n) w, mem_enumerateFromL.2 ⟨⟨_, hr⟩, rfl⟩, ?_, ?_⟩
  · rintro rfl
    exact demandOfL_unconditional.2 hr
  · intro _
    by_cases hu : (demandOfL (rawRecordsL ctx laws n) w).unconditional = true
    · exact Or.inl hu
    · right
      exact (demandOfL_alts (by simpa using hu) _).2 hr

theorem mem_enumerateL_iff {ctx : Ctx} {laws : Laws} {n : Node} {w : List (C × Nat)} :
    (∃ d, (w, d) ∈ enumerateL ctx laws n) ↔ w ∈ Views ctx laws n := by
  constructor
  · rintro ⟨d, hd⟩
    exact (views_soundL hd).1
  · rintro ⟨v, ls, hv, hn⟩
    obtain ⟨lsx, o, hvx, -⟩ := hv.toRawViewX
    obtain ⟨lsl, hvl, -⟩ := hvx.toRawViewL
    obtain ⟨d, hd, -⟩ := views_completeL hvl hn
    exact ⟨d, hd⟩

theorem enumerateL_demand_unique {ctx : Ctx} {laws : Laws} {n : Node}
    {w : List (C × Nat)} {d d' : DemandL} (h : (w, d) ∈ enumerateL ctx laws n)
    (h' : (w, d') ∈ enumerateL ctx laws n) : d = d' := by
  rw [(mem_enumerateFromL.1 h).2, (mem_enumerateFromL.1 h').2]

/-- The rule under laws, read through the emitted demand. -/
theorem acceptsLaws_iff_altsLAccept {ctx : Ctx} {laws : Laws} {n : Node}
    {w : List (C × Nat)} {d : DemandL} (h : (w, d) ∈ enumerateL ctx laws n)
    (taken : List C) :
    d.acceptsLaws taken ↔ AltsLAccept (AltsL ctx laws n w) taken := by
  obtain ⟨-, rfl⟩ := mem_enumerateFromL.1 h
  rw [acceptsLaws_demandOfL]
  unfold AltsLAccept
  constructor
  · rintro ⟨ls, hr, hall⟩
    obtain ⟨v, ls', o, hv, hn, rfl⟩ := mem_rawRecordsL.1 hr
    exact Or.inr ⟨_, ⟨v, ls', o, hv, hn, rfl⟩, hall⟩
  · rintro (⟨v, ls', o, hv, hn, hnil⟩ | ⟨ls, ⟨v, ls', o, hv, hn, rfl⟩, hall⟩)
    · exact ⟨[], mem_rawRecordsL.2 ⟨v, ls', o, hv, hn, hnil⟩, by simp⟩
    · exact ⟨_, mem_rawRecordsL.2 ⟨v, ls', o, hv, hn, rfl⟩, hall⟩

/-- A tree whose every flagged leaf is `okL` makes its view's demand accept. -/
theorem acceptsLaws_of_tree {ctx : Ctx} {laws : Laws} {n : Node} {v w : List (C × Nat)}
    {ls : List LeafL} {o : Nat} {taken : List C} (hv : RawViewL ctx n v ls o)
    (hn : normalize ctx.κ laws v = .node w)
    (hok : ∀ l ∈ flagLeaves ctx.κ laws v ls, l.okL taken) :
    ∃ d, (w, d) ∈ enumerateL ctx laws n ∧ d.acceptsLaws taken := by
  obtain ⟨d, hd, hu, ha⟩ := views_completeL hv hn
  refine ⟨d, hd, ?_⟩
  by_cases hls : ls = []
  · exact Or.inl (hu hls)
  · rcases ha hls with h | h
    · exact Or.inl h
    · exact Or.inr ⟨_, h, hok⟩

/-! ## The rule under laws accepts whatever the corrected rule accepts -/

theorem altsXAccept_imp_altsLAccept {ctx : Ctx} {laws : Laws} {n : Node} {w : List (C × Nat)}
    {taken : List C} (h : AltsXAccept (AltsX ctx laws n w) taken) :
    AltsLAccept (AltsL ctx laws n w) taken := by
  rcases h with ⟨v, o, hv, hn⟩ | ⟨ls, ⟨v, o, hv, hn⟩, hall⟩
  · obtain ⟨lsl, hvl, hproj⟩ := hv.toRawViewL
    have hnil : lsl = [] := List.map_eq_nil_iff.1 hproj
    subst hnil
    exact Or.inl ⟨v, [], o, hvl, hn, rfl⟩
  · obtain ⟨lsl, hvl, rfl⟩ := hv.toRawViewL
    refine Or.inr ⟨_, ⟨v, lsl, o, hvl, hn, rfl⟩, ?_⟩
    intro l hl
    obtain ⟨l', hl', rfl⟩ := List.mem_map.1 hl
    exact LeafF.okL_of_ok (hall _ (List.mem_map_of_mem hl'))

/-- The rule under laws accepts every match the corrected rule accepted
(hence every match the original rule accepted, `accepts_imp_acceptsFix`). -/
theorem acceptsFix_imp_acceptsLaws {ctx : Ctx} {laws : Laws} {n : Node} {w : List (C × Nat)}
    {dx : DemandX} {dl : DemandL} (hx : (w, dx) ∈ enumerateX ctx laws n)
    (hl : (w, dl) ∈ enumerateL ctx laws n) {taken : List C} (hacc : dx.acceptsFix taken) :
    dl.acceptsLaws taken :=
  (acceptsLaws_iff_altsLAccept hl taken).2
    (altsXAccept_imp_altsLAccept ((acceptsFix_iff_altsXAccept hx taken).1 hacc))

theorem accepts_imp_acceptsLaws {ctx : Ctx} {laws : Laws} {n : Node} {w : List (C × Nat)}
    {d : Demand} {dl : DemandL} (h : (w, d) ∈ enumerate ctx laws n)
    (hl : (w, dl) ∈ enumerateL ctx laws n) {taken : List C} (hacc : d.accepts taken) :
    dl.acceptsLaws taken := by
  rw [enumerateX_proj] at h
  obtain ⟨⟨w', dx⟩, hx, heq⟩ := List.mem_map.1 h
  simp only [Prod.mk.injEq] at heq
  obtain ⟨rfl, rfl⟩ := heq
  exact acceptsFix_imp_acceptsLaws hx hl (DemandX.accepts_proj_imp _ _ hacc)

/-! ## Multiset helpers for the refold -/

theorem count_ofEntries_eq_zero_of_notMem {w : List (C × Nat)} {z : C}
    (hz : z ∉ w.map Prod.fst) : (ofEntries w).count z = 0 :=
  count_ofEntries_eq_zero (fun _ he h => hz (h ▸ List.mem_map_of_mem he))

theorem mem_map_fst_of_count_ne_zero {w : List (C × Nat)} {z : C}
    (h : (ofEntries w).count z ≠ 0) : z ∈ w.map Prod.fst := by
  obtain ⟨e, he, rfl, -⟩ := mem_ofEntries.1 (Multiset.count_ne_zero.1 h)
  exact List.mem_map_of_mem he

/-- The counts of the raw view and of its refold. -/
theorem count_refold (v₁ v₂ L : List (C × Nat)) (X : C) (k : Nat) (z : C) :
    (ofEntries (v₁ ++ (X, k) :: v₂)).count z =
      (ofEntries (v₁ ++ L ++ v₂)).count z - (ofEntries L).count z +
        (if z = X then k else 0) := by
  simp only [ofEntries_append, ofEntries_cons, Multiset.count_add, Multiset.count_replicate]
  by_cases hzX : z = X
  · subst hzX; simp only [↓reduceIte]; omega
  · simp only [hzX, Ne.symm hzX, ↓reduceIte]; omega

theorem count_refold_of_notMem {v₁ v₂ L : List (C × Nat)} {X : C} {k : Nat} {z : C}
    (hz : z ∉ L.map Prod.fst) (hzX : z ≠ X) :
    (ofEntries (v₁ ++ (X, k) :: v₂)).count z = (ofEntries (v₁ ++ L ++ v₂)).count z := by
  rw [count_refold v₁ v₂ L X k z, count_ofEntries_eq_zero_of_notMem hz]
  simp [hzX]

theorem refoldCount_eq {v₁ v₂ : List (C × Nat)} {l : LeafL} :
    refoldCount (v₁ ++ l.L ++ v₂) l = (ofEntries (v₁ ++ (l.X, l.k) :: v₂)).count l.X := by
  unfold refoldCount
  rw [count_refold v₁ v₂ l.L l.X l.k l.X]
  simp

theorem count_leaf_le {v₁ v₂ L : List (C × Nat)} (z : C) :
    (ofEntries L).count z ≤ (ofEntries (v₁ ++ L ++ v₂)).count z := by
  simp only [ofEntries_append, Multiset.count_add]; omega

/-! ## Inert refolds: the AC normal form of the refolded view -/

/-- **Inert refold, AC, per class.** Under `InertAC`, the normal form of the
refolded view agrees with the normal form of the view on every class the
refold does not touch, and on the touched classes both normal forms are the
dropped and clamped raw counts (the walk does not reach them). -/
theorem cntNF_refold_ac (laws : Laws) {v v₁ v₂ : List (C × Nat)} {l : LeafL}
    (hv : v = v₁ ++ l.L ++ v₂) (hin : InertAC laws v l) :
    (∀ z, z ∉ l.touched →
      cntNF laws (insert l.X (v.map Prod.fst).toFinset) (ofEntries (v₁ ++ (l.X, l.k) :: v₂)) z =
        cntNF laws (insert l.X (v.map Prod.fst).toFinset) (ofEntries v) z) ∧
    (∀ z, z ∈ l.touched →
      cntNF laws (insert l.X (v.map Prod.fst).toFinset) (ofEntries (v₁ ++ (l.X, l.k) :: v₂)) z =
        preNF laws z ((ofEntries (v₁ ++ (l.X, l.k) :: v₂)).count z) ∧
      cntNF laws (insert l.X (v.map Prod.fst).toFinset) (ofEntries v) z =
        preNF laws z ((ofEntries v).count z)) := by
  have hagree : ∀ z, z ∉ l.touched →
      (ofEntries (v₁ ++ (l.X, l.k) :: v₂)).count z = (ofEntries v).count z := by
    intro z hz
    simp only [LeafL.touched, List.mem_cons, not_or] at hz
    rw [hv]
    exact count_refold_of_notMem hz.2 hz.1
  have hsuppM : ∀ y, preNF laws y ((ofEntries v).count y) ≠ 0 → y ∈ l.X :: v.map Prod.fst := by
    intro y hy
    exact List.mem_cons_of_mem _ (mem_map_fst_of_count_ne_zero (preNF_support hy))
  have hsuppM' : ∀ y, preNF laws y ((ofEntries (v₁ ++ (l.X, l.k) :: v₂)).count y) ≠ 0 →
      y ∈ l.X :: v.map Prod.fst := by
    intro y hy
    have hmem := mem_map_fst_of_count_ne_zero (preNF_support hy)
    simp only [List.map_append, List.map_cons, List.mem_append, List.mem_cons] at hmem
    rw [hv]
    simp only [List.map_append, List.mem_append, List.mem_cons]
    tauto
  unfold cntNF
  rcases hinv : laws.inv with _ | inv
  · refine ⟨fun z hz => ?_, fun z _ => ⟨?_, ?_⟩⟩
    · show preNF laws z _ = preNF laws z _
      rw [hagree z hz]
    · rfl
    · rfl
  · simp only
    unfold walkF
    have hKmem : ∀ y, y ∈ (insert l.X (v.map Prod.fst).toFinset).sort (· ≤ ·) ↔
        y ∈ l.X :: v.map Prod.fst := by
      intro y; simp [Finset.mem_sort]
    obtain ⟨hc1, hc2⟩ := hin.cancel inv hinv
    have := walk_passive inv ((insert l.X (v.map Prod.fst).toFinset).sort (· ≤ ·))
      (fun z => z ∈ l.touched)
      (fun x hx hS y hy => by rw [hKmem]; exact hc1 x hS y hy)
      (fun y hy hS z hz => hc2 y ((hKmem y).1 hy) z hz)
      ((insert l.X (v.map Prod.fst).toFinset).sort (· ≤ ·))
      (fun x => preNF laws x ((ofEntries v).count x))
      (fun x => preNF laws x ((ofEntries (v₁ ++ (l.X, l.k) :: v₂)).count x))
      (fun c hc => hc)
      (fun y hy => (hKmem y).2 (hsuppM y hy))
      (fun y hy => (hKmem y).2 (hsuppM' y hy))
      (fun x hx => by rw [hagree x hx])
    exact ⟨fun z hz => (this.1 z hz).symm, fun z hz => ⟨(this.2 z hz).2, (this.2 z hz).1⟩⟩

/-- `cntNF` over the classes of the view and `X` is the normal form's count. -/
theorem count_normalizeList_ac (laws : Laws) (v : List (C × Nat)) (X : C) (z : C) :
    (ofEntries (normalizeList .ac laws v)).count z =
      cntNF laws (insert X (v.map Prod.fst).toFinset) (ofEntries v) z := by
  have := cntOf_normalizeList_ac laws v (K := insert X (v.map Prod.fst).toFinset)
    (fun e he _ => by simp only [Finset.mem_insert, List.mem_toFinset]; exact Or.inr (List.mem_map_of_mem he))
  exact congrFun this z

theorem count_normalizeList_ac_refold (laws : Laws) (v₁ v₂ : List (C × Nat)) (l : LeafL)
    (z : C) :
    (ofEntries (normalizeList .ac laws (v₁ ++ (l.X, l.k) :: v₂))).count z =
      cntNF laws (insert l.X ((v₁ ++ l.L ++ v₂).map Prod.fst).toFinset)
        (ofEntries (v₁ ++ (l.X, l.k) :: v₂)) z := by
  have := cntOf_normalizeList_ac laws (v₁ ++ (l.X, l.k) :: v₂)
    (K := insert l.X ((v₁ ++ l.L ++ v₂).map Prod.fst).toFinset) (fun e he _ => by
      simp only [Finset.mem_insert, List.mem_toFinset, List.map_append, List.mem_append]
      simp only [List.mem_append, List.mem_cons] at he
      rcases he with he | rfl | he
      · exact Or.inr (Or.inl (Or.inl (List.mem_map_of_mem he)))
      · exact Or.inl rfl
      · exact Or.inr (Or.inr (List.mem_map_of_mem he)))
  exact congrFun this z

/-- **Inert refold, AC, on normal forms.** Under `InertAC` the normal form of
the refolded raw view has the counts of the old normal form outside the
touched classes, the dropped and clamped refolded count at `X`, and the
dropped and clamped raw counts on the touched classes. -/
theorem refold_ac_inert (laws : Laws) {v₁ v₂ : List (C × Nat)} {l : LeafL}
    (hin : InertAC laws (v₁ ++ l.L ++ v₂) l) :
    (∀ z, z ∉ l.touched →
      (ofEntries (normalizeList .ac laws (v₁ ++ (l.X, l.k) :: v₂))).count z =
        (ofEntries (normalizeList .ac laws (v₁ ++ l.L ++ v₂))).count z) ∧
    (ofEntries (normalizeList .ac laws (v₁ ++ (l.X, l.k) :: v₂))).count l.X =
      preNF laws l.X (refoldCount (v₁ ++ l.L ++ v₂) l) ∧
    (∀ z, z ∈ l.touched →
      (ofEntries (normalizeList .ac laws (v₁ ++ l.L ++ v₂))).count z =
        preNF laws z ((ofEntries (v₁ ++ l.L ++ v₂)).count z) ∧
      (ofEntries (normalizeList .ac laws (v₁ ++ (l.X, l.k) :: v₂))).count z =
        preNF laws z ((ofEntries (v₁ ++ (l.X, l.k) :: v₂)).count z)) := by
  obtain ⟨h1, h2⟩ := cntNF_refold_ac laws rfl hin
  refine ⟨fun z hz => ?_, ?_, fun z hz => ⟨?_, ?_⟩⟩
  · rw [count_normalizeList_ac_refold, count_normalizeList_ac laws _ l.X, h1 z hz]
  · rw [count_normalizeList_ac_refold, (h2 l.X (List.mem_cons_self ..)).1, refoldCount_eq]
  · rw [count_normalizeList_ac laws _ l.X, (h2 z hz).2]
  · rw [count_normalizeList_ac_refold, (h2 z hz).1]

/-- The refolded count of an inert leaf survives normalization. -/
theorem preNF_refoldCount_ne_zero {laws : Laws} {v : List (C × Nat)} {l : LeafL}
    (hin : InertAC laws v l) (hk : 0 < l.k) : preNF laws l.X (refoldCount v l) ≠ 0 := by
  unfold preNF
  simp only [hin.unit, ↓reduceIte]
  rcases hr : laws.nilpotent with _ | r
  · show refoldCount v l ≠ 0
    unfold refoldCount; omega
  · exact hin.clamp r hr

/-! ### The strong form: the laws-free refold lemmas lift -/

/-- **Inertness of a refold, strong form**: `InertAC`, and the touched
classes are neither the unit nor clamped (their raw counts, before and
after, are below the nilpotent order). -/
structure RefoldInert (laws : Laws) (v₁ v₂ : List (C × Nat)) (l : LeafL) : Prop where
  inert : InertAC laws (v₁ ++ l.L ++ v₂) l
  touched : ∀ z ∈ l.touched, laws.unit ≠ some z ∧
    ∀ r, laws.nilpotent = some r →
      (ofEntries (v₁ ++ l.L ++ v₂)).count z < r ∧ (ofEntries (v₁ ++ (l.X, l.k) :: v₂)).count z < r

theorem preNF_id {laws : Laws} {z : C} {n : Nat} (hu : laws.unit ≠ some z)
    (hr : ∀ r, laws.nilpotent = some r → n < r) : preNF laws z n = n := by
  unfold preNF
  simp only [hu, ↓reduceIte]
  rcases h : laws.nilpotent with _ | r
  · rfl
  · exact Nat.mod_eq_of_lt (hr r h)

/-- **`refold_normalize_inert`.** Under `RefoldInert`, the normal form of the
refolded raw view is the normal form of the raw view with the leaf's entries
removed and `X : k'` inserted (and the leaf's entries are in the normal
form). This is the laws-free shape of `refold_ac`. -/
theorem refold_normalize_inert (laws : Laws) {v₁ v₂ : List (C × Nat)} {l : LeafL}
    (h : RefoldInert laws v₁ v₂ l) :
    ofEntries (normalizeList .ac laws (v₁ ++ (l.X, l.k) :: v₂)) =
      ofEntries (normalizeList .ac laws (v₁ ++ l.L ++ v₂)) - ofEntries l.L +
        Multiset.replicate l.k l.X ∧
    ofEntries l.L ≤ ofEntries (normalizeList .ac laws (v₁ ++ l.L ++ v₂)) := by
  obtain ⟨h1, -, h3⟩ := refold_ac_inert laws h.inert
  have hcount : ∀ z, (ofEntries (normalizeList .ac laws (v₁ ++ (l.X, l.k) :: v₂))).count z =
      (ofEntries (normalizeList .ac laws (v₁ ++ l.L ++ v₂))).count z - (ofEntries l.L).count z +
        (if z = l.X then l.k else 0) := by
    intro z
    by_cases hz : z ∈ l.touched
    · obtain ⟨hu, hr⟩ := h.touched z hz
      obtain ⟨e1, e2⟩ := h3 z hz
      rw [e1, e2, preNF_id hu (fun r hr' => (hr r hr').1), preNF_id hu (fun r hr' => (hr r hr').2),
        count_refold v₁ v₂ l.L l.X l.k z]
    · have hzL : z ∉ l.L.map Prod.fst := fun hzL => hz (List.mem_cons_of_mem _ hzL)
      have hzX : z ≠ l.X := fun hzX => hz (hzX ▸ List.mem_cons_self ..)
      rw [h1 z hz, count_ofEntries_eq_zero_of_notMem hzL]
      simp [hzX]
  constructor
  · ext z
    rw [Multiset.count_add, Multiset.count_sub, Multiset.count_replicate, hcount z]
    by_cases hz : z = l.X
    · subst hz; simp
    · simp [hz, Ne.symm hz]
  · rw [Multiset.le_iff_count]
    intro z
    by_cases hz : z ∈ l.touched
    · obtain ⟨hu, hr⟩ := h.touched z hz
      rw [(h3 z hz).1, preNF_id hu (fun r hr' => (hr r hr').1)]
      exact count_leaf_le z
    · have hzL : z ∉ l.L.map Prod.fst := fun hzL => hz (List.mem_cons_of_mem _ hzL)
      rw [count_ofEntries_eq_zero_of_notMem hzL]
      exact Nat.zero_le _

/-- The laws-free `refold_ac` lifted to an inert refold under laws: the
match on the normal form of the view carries over to the normal form of
the refolded view, with the rest refolded exactly as without laws. -/
theorem refold_ac_lift {G : Graph} {laws : Laws} {f : Sym} {elems : List (Pat × Mult)} {r : Var}
    {σ : Binding} {taken : List C} {v₁ v₂ : List (C × Nat)} {l : LeafL}
    (h : RefoldInert laws v₁ v₂ l) (helems : ∀ e ∈ elems, ∃ x, e.1 = Pat.var x)
    (hm : MatchV G (.ac f elems (some r))
      (.mset (ofEntries (normalizeList .ac laws (v₁ ++ l.L ++ v₂)))) σ taken)
    (hleaf : ∀ c ∈ l.g, c ∉ taken) (hX : l.X ∉ taken) :
    MatchV G (.ac f elems (some r))
      (.mset (ofEntries (normalizeList .ac laws (v₁ ++ (l.X, l.k) :: v₂))))
      (σ.setRest r ((ofEntries (normalizeList .ac laws (v₁ ++ (l.X, l.k) :: v₂))).filter
        (fun c => c ∉ taken))) taken ∧
    (ofEntries (normalizeList .ac laws (v₁ ++ (l.X, l.k) :: v₂))).filter (fun c => c ∉ taken) =
      ((ofEntries (normalizeList .ac laws (v₁ ++ l.L ++ v₂))).filter (fun c => c ∉ taken)) -
        ofEntries l.L + Multiset.replicate l.k l.X := by
  obtain ⟨heq, hle⟩ := refold_normalize_inert laws h
  set N := ofEntries (normalizeList .ac laws (v₁ ++ l.L ++ v₂)) with hN
  have hN' : ofEntries (Multiset.entries (N - ofEntries l.L) ++ Multiset.entries (ofEntries l.L) ++ [])
      = N := by
    rw [ofEntries_append, ofEntries_append, ofEntries_entries, ofEntries_entries]
    have h0 : ofEntries ([] : List (C × Nat)) = 0 := rfl
    rw [h0, add_zero]
    exact tsub_add_cancel_of_le hle
  have hN'' : ofEntries (Multiset.entries (N - ofEntries l.L) ++ (l.X, l.k) :: []) =
      ofEntries (normalizeList .ac laws (v₁ ++ (l.X, l.k) :: v₂)) := by
    rw [heq, ofEntries_append, ofEntries_entries, ofEntries_cons]
    have h0 : ofEntries ([] : List (C × Nat)) = 0 := rfl
    rw [h0, add_zero]
  have hleaf' : ∀ e ∈ Multiset.entries (ofEntries l.L), e.1 ∉ taken := by
    intro e he
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 he
    simp only [Finset.mem_sort, Multiset.mem_toFinset] at hc
    obtain ⟨e', he', hce⟩ := exists_mem_ofEntries hc
    exact hce ▸ hleaf e'.1 (List.mem_map_of_mem he')
  rw [← hN'] at hm
  obtain ⟨hm', hrest⟩ := refold_ac (X := l.X) (k' := l.k) helems hm hleaf' hX
  rw [hN''] at hm' hrest
  rw [hN', ofEntries_entries] at hrest
  exact ⟨hm', hrest⟩

/-! ## Normal forms with two classes are nodes -/

theorem normalize_ac_node_of_two (laws : Laws) {v : List (C × Nat)} {a b : C} (hab : a ≠ b)
    (ha : a ∈ ofEntries (normalizeList .ac laws v)) (hb : b ∈ ofEntries (normalizeList .ac laws v)) :
    normalize .ac laws v = .node (normalizeList .ac laws v) := by
  unfold normalize
  rw [classify_node_iff]
  refine ⟨rfl, ?_, ?_⟩
  · intro h
    rw [h] at ha
    simp [ofEntries] at ha
  · intro c h
    rw [h] at ha hb
    have h1 : ofEntries [(c, 1)] = {c} := by simp [ofEntries]
    rw [h1, Multiset.mem_singleton] at ha hb
    exact hab (ha.trans hb.symm)

theorem ofView_ac_normalizeList (laws : Laws) (v : List (C × Nat)) :
    ofView .ac (normalizeList .ac laws v) = .mset (ofEntries (normalizeList .ac laws v)) := rfl

/-! ## Sets and sequences: only the identity law acts -/

/-- The unit entries removed, as a filter. -/
def dropU (laws : Laws) (v : List (C × Nat)) : List (C × Nat) :=
  v.filter (fun e => decide (laws.unit ≠ some e.1))

theorem dropUnit_eq_dropU (laws : Laws) (v : List (C × Nat)) :
    dropUnit laws.unit v = dropU laws v := by
  unfold dropU
  rcases hu : laws.unit with _ | u
  · simp [dropUnit]
  · simp only [dropUnit]
    apply List.filter_congr
    intro e _
    simp [eq_comm]

theorem dropU_append (laws : Laws) (a b : List (C × Nat)) :
    dropU laws (a ++ b) = dropU laws a ++ dropU laws b := by
  simp [dropU, List.filter_append]

theorem dropU_cons_of_ne (laws : Laws) {X : C} (hX : laws.unit ≠ some X) (k : Nat)
    (v : List (C × Nat)) : dropU laws ((X, k) :: v) = (X, k) :: dropU laws v := by
  simp [dropU, hX]

theorem map_fst_dropU (laws : Laws) (v : List (C × Nat)) :
    (dropU laws v).map Prod.fst = (v.map Prod.fst).filter (fun c => decide (laws.unit ≠ some c)) := by
  induction v with
  | nil => rfl
  | cons e v ih =>
      simp only [dropU, List.filter_cons, List.map_cons] at ih ⊢
      split <;> simp_all

theorem normalizeList_aci_eq (laws : Laws) (v : List (C × Nat)) :
    normalizeList .aci laws v = dropU laws (dedupAci v) := by
  show dropUnit laws.unit (dedupAci v) = _
  exact dropUnit_eq_dropU laws _

theorem normalizeList_assoc_eq (laws : Laws) (v : List (C × Nat)) :
    normalizeList .assoc laws v = dropU laws v := by
  show dropUnit laws.unit v = _
  exact dropUnit_eq_dropU laws _

theorem toFinset_map_fst_dedupAci (v : List (C × Nat)) :
    ((dedupAci v).map Prod.fst).toFinset = (v.map Prod.fst).toFinset := by
  ext c
  simp [dedupAci]

theorem toFinset_map_fst_dropU (laws : Laws) (v : List (C × Nat)) :
    ((dropU laws v).map Prod.fst).toFinset =
      (v.map Prod.fst).toFinset.filter (fun c => laws.unit ≠ some c) := by
  ext c
  simp [map_fst_dropU]

/-- The classes of the ACI normal form are the non-unit classes of the view. -/
theorem classes_normalizeList_aci (laws : Laws) (v : List (C × Nat)) :
    ((normalizeList .aci laws v).map Prod.fst).toFinset =
      ((dropU laws v).map Prod.fst).toFinset := by
  rw [normalizeList_aci_eq, toFinset_map_fst_dropU, toFinset_map_fst_dropU,
    toFinset_map_fst_dedupAci]

theorem ofView_aci_normalizeList (laws : Laws) (v : List (C × Nat)) :
    ofView .aci (normalizeList .aci laws v) = .set ((dropU laws v).map Prod.fst).toFinset := by
  simp only [ofView]
  rw [classes_normalizeList_aci]

theorem normalizeList_aci_nodup (laws : Laws) (v : List (C × Nat)) :
    ((normalizeList .aci laws v).map Prod.fst).Nodup := by
  rw [normalizeList_aci_eq]
  exact (dedupAci_spec v).1.imp (fun h => Nat.ne_of_lt h) |>.sublist
    (List.filter_sublist.map Prod.fst)

theorem normalize_aci_node_of_card (laws : Laws) {v : List (C × Nat)}
    (h2 : 2 ≤ ((dropU laws v).map Prod.fst).toFinset.card) :
    normalize .aci laws v = .node (normalizeList .aci laws v) := by
  have hlen : (normalizeList .aci laws v).length = ((dropU laws v).map Prod.fst).toFinset.card := by
    rw [← classes_normalizeList_aci, List.toFinset_card_of_nodup (normalizeList_aci_nodup laws v),
      List.length_map]
  unfold normalize
  rw [classify_node_iff]
  refine ⟨rfl, ?_, ?_⟩
  · intro h; rw [h] at hlen; simp at hlen; omega
  · intro c h; rw [h] at hlen; simp at hlen; omega

theorem ofView_assoc_normalizeList (laws : Laws) (v : List (C × Nat)) :
    ofView .assoc (normalizeList .assoc laws v) = .seq ((dropU laws v).map Prod.fst) := by
  simp only [ofView]
  rw [normalizeList_assoc_eq]

theorem normalize_assoc_node_of_len (laws : Laws) {v : List (C × Nat)}
    (h : 2 ≤ (dropU laws v).length) :
    normalize .assoc laws v = .node (normalizeList .assoc laws v) := by
  unfold normalize
  rw [classify_node_iff, normalizeList_assoc_eq]
  refine ⟨rfl, ?_, ?_⟩
  · intro h'; rw [h'] at h; simp at h
  · intro c h'; rw [h'] at h; simp at h

/-! ## Refolding a rest under laws -/

/-- The AC normal form of a raw multiset. -/
def nfAC (laws : Laws) (M : Multiset C) : Multiset C :=
  ofEntries (normalizeList .ac laws (Multiset.entries M))

theorem nfAC_ofEntries (laws : Laws) (v : List (C × Nat)) :
    nfAC laws (ofEntries v) = ofEntries (normalizeList .ac laws v) := by
  unfold nfAC normalizeList
  simp only
  have : coalesce (Multiset.entries (ofEntries v)) = coalesce v := by
    unfold coalesce; rw [ofEntries_entries]
  rw [this]

/-- The refolded raw multiset. -/
theorem ofEntries_refold (v₁ v₂ L : List (C × Nat)) (X : C) (k : Nat) :
    ofEntries (v₁ ++ L ++ v₂) - ofEntries L + Multiset.replicate k X =
      ofEntries (v₁ ++ (X, k) :: v₂) := by
  ext z
  rw [Multiset.count_add, Multiset.count_sub, Multiset.count_replicate, count_refold v₁ v₂ L X k z]
  by_cases hz : z = X
  · subst hz; simp
  · simp [hz, Ne.symm hz]

/-- One AC refold step on a rest under laws: the rest of the normal form of
a raw multiset `M` becomes the rest of the normal form of `M` with the
children of an `f`-member `m` of `X` (scaled by `k' > 0`) replaced by `k'`
copies of `X`. Without laws this is `RefoldStepAC`; under `RefoldInert` it
is `RefoldStepAC` on the normal form (`refold_normalize_inert`). -/
def RefoldStepACL (ctx : Ctx) (laws : Laws) (taken : List C) (m₀ m₁ : Multiset C) : Prop :=
  ∃ (id : NodeId) (m : Node) (X : C) (k' : Nat) (M : Multiset C), ctx.IsMember id m X ∧ 0 < k' ∧
    ofEntries (scale k' (kids ctx.κ m.children)) ≤ M ∧
    m₀ = (nfAC laws M).filter (fun c => c ∉ taken) ∧
    m₁ = (nfAC laws (M - ofEntries (scale k' (kids ctx.κ m.children)) +
      Multiset.replicate k' X)).filter (fun c => c ∉ taken)

def RefoldsACL (ctx : Ctx) (laws : Laws) (taken : List C) : Multiset C → Multiset C → Prop :=
  Relation.ReflTransGen (RefoldStepACL ctx laws taken)

/-- One Assoc refold step under laws: a contiguous block equal to the
non-unit children of an `f`-member `m` of `X` is replaced by `X`. -/
def RefoldStepAssocL (ctx : Ctx) (laws : Laws) (l₀ l₁ : List C) : Prop :=
  ∃ (id : NodeId) (m : Node) (X : C) (a b : List C), ctx.IsMember id m X ∧
    l₀ = a ++ ((kids ctx.κ m.children).map Prod.fst).filter
      (fun c => decide (laws.unit ≠ some c)) ++ b ∧
    l₁ = a ++ X :: b

def RefoldsAssocL (ctx : Ctx) (laws : Laws) : List C → List C → Prop :=
  Relation.ReflTransGen (RefoldStepAssocL ctx laws)

/-- Without a unit, `RefoldStepAssocL` is `RefoldStepAssoc`. -/
theorem refoldStepAssocL_free (ctx : Ctx) (l₀ l₁ : List C) :
    RefoldStepAssocL ctx Laws.free l₀ l₁ ↔ RefoldStepAssoc ctx l₀ l₁ := by
  unfold RefoldStepAssocL RefoldStepAssoc
  simp [Laws.free]

/-! ## Matches transfer along count-preserving changes -/

/-- An AC match on `N` is a match on any `N'` with the same counts on the
taken classes, with the rest re-read from `N'`. -/
theorem MatchV.ac_transfer {G : Graph} {f : Sym} {elems : List (Pat × Mult)} {r : Var}
    {σ : Binding} {taken : List C} {N N' : Multiset C}
    (helems : ∀ e ∈ elems, ∃ x, e.1 = Pat.var x)
    (hm : MatchV G (.ac f elems (some r)) (.mset N) σ taken)
    (hcnt : ∀ t ∈ taken, N'.count t = N.count t) :
    MatchV G (.ac f elems (some r)) (.mset N')
      (σ.setRest r (N'.filter (fun c => c ∉ taken))) taken := by
  cases hm with
  | ac hnd hlen hmem hmatch hmult hrest =>
    refine MatchV.ac hnd hlen ?_ ?_ ?_ ?_
    · intro c hc
      rw [← Multiset.count_pos, hcnt c hc, Multiset.count_pos]
      exact hmem c hc
    · intro et het
      obtain ⟨x, hx⟩ := helems et.1 (List.of_mem_zip het).1
      have := hmatch et het
      rw [hx] at this ⊢
      have hc := MatchC.var_inv this
      exact MatchC.var hc
    · intro et het
      rw [MultOk_setRest, hcnt et.2 (List.of_mem_zip het).2]
      exact hmult et het
    · simp [MsetRestOk, Binding.setRest]

end Semper.EMatch.Flatten
