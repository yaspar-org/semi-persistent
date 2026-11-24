import SemperProofs.EMatch.Flatten.Views

/-!
# `:flatten` views: the reference enumerator is sound and complete

`views_sound`: every view the enumerator emits is the canonical view of an
opening tree, its demand is unconditional iff some tree opens nothing, and
otherwise its alternatives are exactly the trees' leaf groups.
`views_complete`: every opening tree's canonical view is emitted. The
enumerator is unbounded (counts are `Nat`, no `MAX_*`), so completeness
needs no bound hypothesis; `views_complete_within` restates it under
`WithinBounds` for the engine-level reading (spec §3, §4.4).
`prune_irrelevant`: pruning by `takeable` does not change the accepted
matches (§2.3).
-/

namespace Semper.EMatch.Flatten

open Semper.EMatch

/-! ## The spec's constructor shapes, recovered -/

theorem OT.cons_opt {ctx : Ctx} {k j : Nat} {P : Finset C} {X : C}
    {rest v₁ v₂ : List (C × Nat)} {l₁ l₂ : List (List C)}
    (h₁ : ViewOpt ctx X (k * j) P v₁ l₁) (h₂ : OT ctx k P rest v₂ l₂) :
    OT ctx k P ((X, j) :: rest) (v₁ ++ v₂) (l₁ ++ l₂) := by
  rcases h₁ with ⟨rfl, rfl⟩ | ⟨hX, id, m, l, hmem, hm, rfl⟩
  · exact OT.keep h₂
  · exact OT.opn hX hmem hm h₂

theorem OT.cons_inv {ctx : Ctx} {k j : Nat} {P : Finset C} {X : C}
    {rest v : List (C × Nat)} {ls : List (List C)}
    (h : OT ctx k P ((X, j) :: rest) v ls) :
    ∃ v₁ l₁ v₂ l₂, v = v₁ ++ v₂ ∧ ls = l₁ ++ l₂ ∧
      ViewOpt ctx X (k * j) P v₁ l₁ ∧ OT ctx k P rest v₂ l₂ := by
  cases h with
  | keep h₂ => exact ⟨_, [], _, _, rfl, rfl, Or.inl ⟨rfl, rfl⟩, h₂⟩
  | opn hX hmem hm h₂ =>
      exact ⟨_, _, _, _, rfl, rfl, Or.inr ⟨hX, _, _, _, hmem, hm, rfl⟩, h₂⟩

theorem ViewOpt.keep {ctx : Ctx} {X : C} {k : Nat} {P : Finset C} :
    ViewOpt ctx X k P [(X, k)] [] := Or.inl ⟨rfl, rfl⟩

theorem ViewOpt.opn {ctx : Ctx} {X : C} {k : Nat} {P : Finset C} {id : NodeId}
    {m : Node} {v : List (C × Nat)} {ls : List (List C)}
    (hX : X ∉ P) (hmem : ctx.IsMember id m X)
    (h : ViewNode ctx m k (insert X P) v ls) :
    ViewOpt ctx X k P v (leafify v ls) := Or.inr ⟨hX, id, m, ls, hmem, h, rfl⟩

/-! ## Soundness of the walk -/

theorem kidsOf_sound_of {ctx : Ctx} (opt : C → Nat → Finset C → List Raw)
    (hopt : ∀ X k P r, r ∈ opt X k P → ViewOpt ctx X k P r.1 r.2) :
    ∀ (ks : List (C × Nat)) (k : Nat) (P : Finset C) (r : Raw),
      r ∈ kidsOf opt ks k P → OT ctx k P ks r.1 r.2 := by
  intro ks
  induction ks with
  | nil =>
      intro k P r hr
      simp only [kidsOf, List.mem_singleton] at hr
      subst hr
      exact OT.nil
  | cons e rest ih =>
      intro k P r hr
      obtain ⟨X, j⟩ := e
      simp only [kidsOf, List.mem_flatMap, List.mem_map] at hr
      obtain ⟨r₁, hr₁, r₂, hr₂, rfl⟩ := hr
      exact OT.cons_opt (hopt _ _ _ _ hr₁) (ih _ _ _ hr₂)

theorem rawOpt_sound (ctx : Ctx) :
    ∀ (fuel : Nat) (X : C) (k : Nat) (P : Finset C) (r : Raw),
      r ∈ rawOpt ctx fuel X k P → ViewOpt ctx X k P r.1 r.2 := by
  intro fuel
  induction fuel with
  | zero =>
      intro X k P r hr
      simp only [rawOpt, List.mem_singleton] at hr
      subst hr
      exact ViewOpt.keep
  | succ fuel ih =>
      intro X k P r hr
      simp only [rawOpt, List.mem_cons] at hr
      rcases hr with rfl | hr
      · exact ViewOpt.keep
      · split at hr
        · simp at hr
        · next hX =>
          simp only [List.mem_flatMap, List.mem_map] at hr
          obtain ⟨p, hp, r', hr', rfl⟩ := hr
          have hmem := Ctx.mem_members.1 hp
          exact ViewOpt.opn hX hmem (kidsOf_sound_of _ (ih) _ _ _ _ hr')

theorem rawNode_sound {ctx : Ctx} {fuel : Nat} {m : Node} {k : Nat} {P : Finset C}
    {r : Raw} (hr : r ∈ rawNode ctx fuel m k P) : ViewNode ctx m k P r.1 r.2 :=
  kidsOf_sound_of _ (rawOpt_sound ctx fuel) _ _ _ _ hr

/-! ## Completeness of the walk -/

theorem IsMember.cls_mem {ctx : Ctx} {id : NodeId} {m : Node} {X : C}
    (h : ctx.IsMember id m X) : X ∈ classesOf ctx.G := by
  obtain ⟨hmem, -, hfind, -⟩ := h
  simp only [classesOf, List.mem_toFinset, List.mem_map]
  exact ⟨(id, m), hmem, hfind⟩

theorem kidsOf_complete_of {ctx : Ctx} (fuel : Nat) (opt : C → Nat → Finset C → List Raw)
    (hopt : ∀ X k P v ls, ViewOpt ctx X k P v ls → P ⊆ classesOf ctx.G →
      (classesOf ctx.G).card - P.card ≤ fuel → (v, ls) ∈ opt X k P)
    {ks : List (C × Nat)} {k : Nat} {P : Finset C} {v : List (C × Nat)}
    {ls : List (List C)} (h : OT ctx k P ks v ls)
    (hP : P ⊆ classesOf ctx.G) (hfuel : (classesOf ctx.G).card - P.card ≤ fuel) :
    (v, ls) ∈ kidsOf opt ks k P := by
  induction h with
  | nil => simp [kidsOf]
  | keep h₂ ih =>
      simp only [kidsOf, List.mem_flatMap, List.mem_map]
      exact ⟨_, hopt _ _ _ _ _ ViewOpt.keep hP hfuel, _, ih hP hfuel, rfl⟩
  | opn hX hmem hm h₂ ih₁ ih₂ =>
      simp only [kidsOf, List.mem_flatMap, List.mem_map]
      exact ⟨_, hopt _ _ _ _ _ (ViewOpt.opn hX hmem hm) hP hfuel, _, ih₂ hP hfuel, rfl⟩

theorem rawOpt_complete (ctx : Ctx) :
    ∀ (fuel : Nat) (X : C) (k : Nat) (P : Finset C) (v : List (C × Nat))
      (ls : List (List C)), ViewOpt ctx X k P v ls → P ⊆ classesOf ctx.G →
      (classesOf ctx.G).card - P.card ≤ fuel → (v, ls) ∈ rawOpt ctx fuel X k P := by
  intro fuel
  induction fuel with
  | zero =>
      intro X k P v ls h hP hfuel
      rcases h with ⟨rfl, rfl⟩ | ⟨hX, id, m, l₁, hmem, hm, rfl⟩
      · simp [rawOpt]
      · exfalso
        have hXc : X ∈ classesOf ctx.G := IsMember.cls_mem hmem
        have hlt : P.card < (classesOf ctx.G).card :=
          Finset.card_lt_card ⟨hP, fun hsub => hX (hsub hXc)⟩
        omega
  | succ fuel ih =>
      intro X k P v ls h hP hfuel
      rcases h with ⟨rfl, rfl⟩ | ⟨hX, id, m, l₁, hmem, hm, rfl⟩
      · simp [rawOpt]
      · simp only [rawOpt, List.mem_cons]
        right
        simp only [hX, ↓reduceIte]
        simp only [List.mem_flatMap, List.mem_map]
        refine ⟨(id, m), Ctx.mem_members.2 hmem, (v, l₁), ?_, rfl⟩
        have hXc : X ∈ classesOf ctx.G := IsMember.cls_mem hmem
        have hP' : insert X P ⊆ classesOf ctx.G := Finset.insert_subset hXc hP
        have hcard : (insert X P).card = P.card + 1 := Finset.card_insert_of_notMem hX
        exact kidsOf_complete_of fuel _ (ih) hm hP' (by omega)

theorem rawNode_complete {ctx : Ctx} {m : Node} {k : Nat} {P : Finset C}
    {v : List (C × Nat)} {ls : List (List C)} (h : ViewNode ctx m k P v ls)
    (hP : P ⊆ classesOf ctx.G) {fuel : Nat}
    (hfuel : (classesOf ctx.G).card - P.card ≤ fuel) :
    (v, ls) ∈ rawNode ctx fuel m k P :=
  kidsOf_complete_of fuel _ (rawOpt_complete ctx fuel) h hP hfuel

theorem rawView_mem_rawNode {ctx : Ctx} {n : Node} {v : List (C × Nat)}
    {ls : List (List C)} (h : RawView ctx n v ls) :
    (v, ls) ∈ rawNode ctx (fuelOf ctx.G) n 1 ∅ :=
  rawNode_complete h (Finset.empty_subset _) (by simp [fuelOf])

/-! ## Records, demands, the distinct views -/

theorem mem_rawRecords {ctx : Ctx} {laws : Laws} {n : Node} {w : List (C × Nat)}
    {ls : List (List C)} :
    (w, ls) ∈ rawRecords ctx laws n ↔
      ∃ v, RawView ctx n v ls ∧ normalize ctx.κ laws v = .node w := by
  simp only [rawRecords, List.mem_filterMap]
  constructor
  · rintro ⟨⟨v, ls'⟩, hr, hn⟩
    revert hn
    split
    · next w' hw' =>
      intro hn
      simp only [Option.some.injEq, Prod.mk.injEq] at hn
      obtain ⟨rfl, rfl⟩ := hn
      exact ⟨v, rawNode_sound hr, hw'⟩
    · intro hn
      exact absurd hn (by simp)
  · rintro ⟨v, hv, hn⟩
    refine ⟨(v, ls), rawView_mem_rawNode hv, ?_⟩
    simp only
    rw [hn]

theorem mem_enumerateFrom {recs : List Raw} {w : List (C × Nat)} {d : Demand} :
    (w, d) ∈ enumerateFrom recs ↔ (∃ ls, (w, ls) ∈ recs) ∧ d = demandOf recs w := by
  simp only [enumerateFrom, List.mem_map, List.mem_dedup, Prod.mk.injEq]
  constructor
  · rintro ⟨w', hw', rfl, rfl⟩
    obtain ⟨⟨w'', ls⟩, hr, rfl⟩ := hw'
    exact ⟨⟨ls, hr⟩, rfl⟩
  · rintro ⟨⟨ls, hr⟩, rfl⟩
    exact ⟨w, ⟨(w, ls), hr, rfl⟩, rfl, rfl⟩

theorem mem_altsOf {recs : List Raw} {w : List (C × Nat)} {ls : List (List C)} :
    ls ∈ altsOf recs w ↔ (w, ls) ∈ recs := by
  simp only [altsOf, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨w', ls'⟩, ⟨hr, hw⟩, hls⟩
    simp only at hw hls
    subst hw; subst hls
    exact hr
  · intro hr
    exact ⟨(w, ls), ⟨hr, rfl⟩, rfl⟩

theorem demandOf_unconditional {recs : List Raw} {w : List (C × Nat)} :
    (demandOf recs w).unconditional = true ↔ (w, []) ∈ recs := by
  by_cases h0 : [] ∈ altsOf recs w
  · simp only [demandOf, h0, ↓reduceIte, true_iff]
    exact mem_altsOf.1 h0
  · simp only [demandOf, h0, ↓reduceIte, Bool.false_eq_true, false_iff]
    exact fun hr => h0 (mem_altsOf.2 hr)

theorem demandOf_alts {recs : List Raw} {w : List (C × Nat)}
    (h : (demandOf recs w).unconditional = false) (ls : List (List C)) :
    ls ∈ (demandOf recs w).alts ↔ (w, ls) ∈ recs := by
  by_cases h0 : [] ∈ altsOf recs w
  · simp [demandOf, h0] at h
  · simp only [demandOf, h0, ↓reduceIte]
    exact mem_altsOf

/-- `Demand.accepts` on a record list's demand: some record of the view has
every leaf group hit (the no-opening record vacuously). -/
theorem accepts_demandOf {recs : List Raw} {w : List (C × Nat)} {taken : List C} :
    (demandOf recs w).accepts taken ↔
      ∃ ls, (w, ls) ∈ recs ∧ ∀ g ∈ ls, ∃ c ∈ g, c ∈ taken := by
  unfold Demand.accepts
  by_cases hu : (demandOf recs w).unconditional = true
  · simp only [hu, true_or, true_iff]
    exact ⟨[], demandOf_unconditional.1 hu, by simp⟩
  · have hu' : (demandOf recs w).unconditional = false := by simpa using hu
    simp only [hu', Bool.false_eq_true, false_or]
    constructor
    · rintro ⟨ls, hls, hall⟩
      exact ⟨ls, (demandOf_alts hu' ls).1 hls, hall⟩
    · rintro ⟨ls, hls, hall⟩
      exact ⟨ls, (demandOf_alts hu' ls).2 hls, hall⟩

/-! ## The theorems (spec §4.3 (a), (b)) -/

/-- (a) Every emitted view is an opening tree's canonical view; its demand
is unconditional iff some tree giving it opens nothing; otherwise its
alternatives are exactly the leaf groups of the trees giving it. -/
theorem views_sound {ctx : Ctx} {laws : Laws} {n : Node} {w : List (C × Nat)}
    {d : Demand} (h : (w, d) ∈ enumerate ctx laws n) :
    w ∈ Views ctx laws n ∧
      (d.unconditional = true ↔ [] ∈ Alts ctx laws n w) ∧
      (d.unconditional = false → ∀ ls, ls ∈ d.alts ↔ ls ∈ Alts ctx laws n w) := by
  obtain ⟨⟨ls, hr⟩, rfl⟩ := mem_enumerateFrom.1 h
  obtain ⟨v, hv, hn⟩ := mem_rawRecords.1 hr
  refine ⟨⟨v, ls, hv, hn⟩, ?_, ?_⟩
  · rw [demandOf_unconditional, mem_rawRecords]
    rfl
  · intro hu ls'
    rw [demandOf_alts hu, mem_rawRecords]
    rfl

/-- (b) Every opening tree's canonical view is emitted, and its leaf groups
are recorded in the view's demand. -/
theorem views_complete {ctx : Ctx} {laws : Laws} {n : Node} {v w : List (C × Nat)}
    {ls : List (List C)} (hv : RawView ctx n v ls)
    (hn : normalize ctx.κ laws v = .node w) :
    ∃ d, (w, d) ∈ enumerate ctx laws n ∧
      (ls = [] → d.unconditional = true) ∧
      (ls ≠ [] → d.unconditional = true ∨ ls ∈ d.alts) := by
  have hr : (w, ls) ∈ rawRecords ctx laws n := mem_rawRecords.2 ⟨v, hv, hn⟩
  refine ⟨demandOf (rawRecords ctx laws n) w, mem_enumerateFrom.2 ⟨⟨ls, hr⟩, rfl⟩, ?_, ?_⟩
  · rintro rfl
    exact demandOf_unconditional.2 hr
  · intro _
    by_cases hu : (demandOf (rawRecords ctx laws n) w).unconditional = true
    · exact Or.inl hu
    · right
      exact (demandOf_alts (by simpa using hu) ls).2 hr

/-- (b) under the engine-level hypothesis of §3: the reference enumerator
needs no bound, so `WithinBounds` is not used by the proof. -/
theorem views_complete_within {W : Nat} {ctx : Ctx} {laws : Laws} {n : Node}
    (_ : WithinBounds W ctx n) {v w : List (C × Nat)} {ls : List (List C)}
    (hv : RawView ctx n v ls) (hn : normalize ctx.κ laws v = .node w) :
    ∃ d, (w, d) ∈ enumerate ctx laws n ∧
      (ls = [] → d.unconditional = true) ∧
      (ls ≠ [] → d.unconditional = true ∨ ls ∈ d.alts) :=
  views_complete hv hn

/-- The emitted view set is exactly `Views`. -/
theorem mem_enumerate_iff {ctx : Ctx} {laws : Laws} {n : Node} {w : List (C × Nat)} :
    (∃ d, (w, d) ∈ enumerate ctx laws n) ↔ w ∈ Views ctx laws n := by
  constructor
  · rintro ⟨d, hd⟩
    exact (views_sound hd).1
  · rintro ⟨v, ls, hv, hn⟩
    obtain ⟨d, hd, -⟩ := views_complete hv hn
    exact ⟨d, hd⟩

/-- One demand per emitted view. -/
theorem enumerate_demand_unique {ctx : Ctx} {laws : Laws} {n : Node}
    {w : List (C × Nat)} {d d' : Demand} (h : (w, d) ∈ enumerate ctx laws n)
    (h' : (w, d') ∈ enumerate ctx laws n) : d = d' := by
  rw [(mem_enumerateFrom.1 h).2, (mem_enumerateFrom.1 h').2]

/-- The demand rule, read through the emitted demand: `AltsAccept` on the
opening trees of `w`. -/
theorem accepts_iff_altsAccept {ctx : Ctx} {laws : Laws} {n : Node}
    {w : List (C × Nat)} {d : Demand} (h : (w, d) ∈ enumerate ctx laws n)
    (taken : List C) :
    d.accepts taken ↔ AltsAccept (Alts ctx laws n w) taken := by
  obtain ⟨-, rfl⟩ := mem_enumerateFrom.1 h
  rw [accepts_demandOf]
  unfold AltsAccept
  constructor
  · rintro ⟨ls, hr, hall⟩
    obtain ⟨v, hv, hn⟩ := mem_rawRecords.1 hr
    exact Or.inr ⟨ls, ⟨v, hv, hn⟩, hall⟩
  · rintro (⟨v, hv, hn⟩ | ⟨ls, ⟨v, hv, hn⟩, hall⟩)
    · exact ⟨[], mem_rawRecords.2 ⟨v, hv, hn⟩, by simp⟩
    · exact ⟨ls, mem_rawRecords.2 ⟨v, hv, hn⟩, hall⟩

/-! ## Pruning (spec §2.3, §4.3 `prune_irrelevant`) -/

/-- Pruning the records by `takeable` does not change the accepted matches,
for any `taken` within `takeable`. -/
theorem prune_irrelevant_records (T : C → Bool) (recs : List Raw) (w : List (C × Nat))
    (taken : List C) (hT : ∀ c ∈ taken, T c = true) :
    (demandOf (recs.filter (fun r => leavesMeet T r.2)) w).accepts taken ↔
      (demandOf recs w).accepts taken := by
  rw [accepts_demandOf, accepts_demandOf]
  simp only [List.mem_filter]
  constructor
  · rintro ⟨ls, ⟨hr, -⟩, hall⟩
    exact ⟨ls, hr, hall⟩
  · rintro ⟨ls, hr, hall⟩
    refine ⟨ls, ⟨hr, ?_⟩, hall⟩
    simp only [leavesMeet, List.all_eq_true, List.any_eq_true]
    intro g hg
    obtain ⟨c, hc, hct⟩ := hall g hg
    exact ⟨c, hc, hT c hct⟩

/-- `prune_irrelevant`: a view accepts `taken` through the pruned
enumeration iff it does through the full one. -/
theorem prune_irrelevant (T : C → Bool) (ctx : Ctx) (laws : Laws) (n : Node)
    (w : List (C × Nat)) (taken : List C) (hT : ∀ c ∈ taken, T c = true) :
    (∃ d, (w, d) ∈ enumeratePruned T ctx laws n ∧ d.accepts taken) ↔
      (∃ d, (w, d) ∈ enumerate ctx laws n ∧ d.accepts taken) := by
  have key : ∀ recs : List Raw,
      (∃ d, (w, d) ∈ enumerateFrom recs ∧ d.accepts taken) ↔
        (demandOf recs w).accepts taken := by
    intro recs
    constructor
    · rintro ⟨d, hd, hacc⟩
      obtain ⟨-, rfl⟩ := mem_enumerateFrom.1 hd
      exact hacc
    · intro hacc
      obtain ⟨ls, hr, -⟩ := accepts_demandOf.1 hacc
      exact ⟨_, mem_enumerateFrom.2 ⟨⟨ls, hr⟩, rfl⟩, hacc⟩
  unfold enumeratePruned enumerate
  rw [key, key]
  exact prune_irrelevant_records T _ w taken hT

end Semper.EMatch.Flatten
