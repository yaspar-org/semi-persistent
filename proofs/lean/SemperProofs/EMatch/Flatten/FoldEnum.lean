import SemperProofs.EMatch.Flatten.RegroupChain

/-!
# `:flatten` on folds: the executable spine enumerator is the spine trees

`rawOptD ctx dir` (`FoldPlan.lean`) is the walk of `flatten::enumerate` with
the spine check: a child position opens only when `spine(dir, i, len)` holds,
the first position for `:assoc-left`, the last for `:assoc-right`.
`OTLeft` and `OTRight` (`Fold.lean`) are the spine trees whose views
`otLeft_sound` and `otRight_sound` prove to denote the node's term. This
file closes the gap between them: the raw views the executable enumerator
produces for a fold are exactly the views of the spine trees.

* `kidsOfD_left_sound`, `rawOptD_left_sound`, `rawNodeD_left_sound`: every
  raw view of `rawNodeD ctx .left` is a view of `OTLeft`, with every count
  the inherited multiplicity (a fold is a sequence, so every count is `k`);
  `rawNodeD_left_complete`: every view of `OTLeft` is produced, with enough
  fuel; `rawNodeD_left_iff`, `rawViews_left_iff`: the two directions on the
  root (multiplicity 1, empty path, the fuel of the graph);
* the same for the right fold: `rawOptD_right_sound`,
  `rawNodeD_right_sound`, `rawNodeD_right_complete`, `rawNodeD_right_iff`,
  `rawViews_right_iff`;
* `enumerateLD_left_iff`, `enumerateLD_right_iff`: the distinct views of
  the fold enumerator are the normal forms of the spine trees' views;
* `enumerateLD_left_sound`, `enumerateLD_right_sound`: every view the fold
  enumerator records for a laws-free fold denotes the node's fold
  (`otLeft_sound`, `otRight_sound` carried to the executable mirror);
* `rawNodeD_sub_both`: the views of any direction are among the views of
  `.both`, so every monoid-level theorem over `.both` applies to a fold.

`SeqShaped ctx`: every `f`-member is a sequence node. The engine fixes the
children shape of an operator at declaration, so a fold's members are
sequences; the model's `kids` reads no child from a mismatched shape, which
`OTLeft`/`OTRight` never open.
-/

namespace Semper.EMatch.Flatten

open Semper.EMatch

/-- Every `f`-member is a sequence node (the engine's operator declaration
fixes the shape). -/
def SeqShaped (ctx : Ctx) : Prop :=
  ∀ id m X, ctx.IsMember id m X → ∃ cs, m.children = .seq cs

/-- A class list as a view with every count `k`. -/
def withK (k : Nat) (cs : List C) : List (C × Nat) := cs.map (fun c => (c, k))

theorem withK_append (k : Nat) (a b : List C) : withK k (a ++ b) = withK k a ++ withK k b := by
  simp [withK]

theorem withK_map_fst (k : Nat) (cs : List C) : (withK k cs).map Prod.fst = cs := by
  induction cs <;> simp_all [withK]

theorem kids_seq (cs : List C) : kids .assoc (.seq cs) = withK 1 cs := rfl

theorem scale_withK (k : Nat) (cs : List C) : scale k (withK 1 cs) = withK k cs := by
  simp [scale, withK]

theorem withK_inj {k : Nat} {a b : List C} (h : withK k a = withK k b) : a = b := by
  have := congrArg (List.map Prod.fst) h
  rwa [withK_map_fst, withK_map_fst] at this

/-- The options of one spine position of a left fold: keep, or open through
a member and take a spine view of its children. -/
def OptLeft (ctx : Ctx) (P : Finset C) (X : C) (v : List C) : Prop :=
  v = [X] ∨ (X ∉ P ∧ ∃ id m cs, ctx.IsMember id m X ∧ m.children = .seq cs ∧
    OTLeft ctx (insert X P) cs v)

def OptRight (ctx : Ctx) (P : Finset C) (X : C) (v : List C) : Prop :=
  v = [X] ∨ (X ∉ P ∧ ∃ id m cs, ctx.IsMember id m X ∧ m.children = .seq cs ∧
    OTRight ctx (insert X P) cs v)

theorem OptLeft.cons {ctx : Ctx} {P : Finset C} {X : C} {v rest : List C}
    (h : OptLeft ctx P X v) : OTLeft ctx P (X :: rest) (v ++ rest) := by
  rcases h with rfl | ⟨hX, id, m, cs, hm, hcs, ht⟩
  · exact OTLeft.keep
  · exact OTLeft.opn hX hm hcs ht

theorem OptRight.snoc {ctx : Ctx} {P : Finset C} {X : C} {v rest : List C}
    (h : OptRight ctx P X v) : OTRight ctx P (rest ++ [X]) (rest ++ v) := by
  rcases h with rfl | ⟨hX, id, m, cs, hm, hcs, ht⟩
  · exact OTRight.keep
  · exact OTRight.opn hX hm hcs ht

/-- A kept head before a right-fold view. -/
theorem OTRight.cons {ctx : Ctx} {P : Finset C} {X : C} {rest v : List C}
    (h : OTRight ctx P rest v) : OTRight ctx P (X :: rest) (X :: v) := by
  cases h with
  | keep => exact OTRight.keep
  | @opn _ Y rest' id m cs v' hY hm hcs ht =>
      have := OTRight.opn (rest := X :: rest') hY hm hcs ht
      simpa using this

/-! ## Any direction is within `.both` -/

theorem kidsOfD_mono (opt opt' : Bool → C → Nat → Finset C → List RawL)
    (hopt : ∀ b X k P r, r ∈ opt b X k P → r ∈ opt' true X k P) (dir : Dir) (len : Nat) :
    ∀ (ks : List (C × Nat)) (i k : Nat) (P : Finset C) (r : RawL),
      r ∈ kidsOfD opt dir len ks i k P → r ∈ kidsOfD opt' .both len ks i k P
  | [], _, _, _, r, hr => by simpa [kidsOfD] using hr
  | (X, j) :: rest, i, k, P, r, hr => by
      simp only [kidsOfD, List.mem_flatMap, List.mem_map] at hr ⊢
      obtain ⟨r₁, h₁, r₂, h₂, rfl⟩ := hr
      exact ⟨r₁, hopt _ _ _ _ _ h₁, r₂, kidsOfD_mono opt opt' hopt dir len rest (i + 1) k P r₂ h₂,
        rfl⟩

theorem rawOptD_sub_both (ctx : Ctx) (dir : Dir) :
    ∀ (fuel : Nat) (b : Bool) (X : C) (k : Nat) (P : Finset C) (r : RawL),
      r ∈ rawOptD ctx dir fuel b X k P → r ∈ rawOptD ctx .both fuel true X k P
  | 0, _, _, _, _, r, hr => by simpa [rawOptD] using hr
  | fuel + 1, b, X, k, P, r, hr => by
      simp only [rawOptD, List.mem_cons] at hr ⊢
      rcases hr with rfl | hr
      · exact Or.inl rfl
      · right
        split at hr
        · simp at hr
        · next hb =>
          have hX : X ∉ P := fun h => hb (Or.inr h)
          simp only [hX, Bool.true_eq_false, or_self, ↓reduceIte, List.mem_flatMap,
            List.mem_map] at hr ⊢
          obtain ⟨p, hp, r', hr', rfl⟩ := hr
          exact ⟨p, hp, r', kidsOfD_mono _ _ (rawOptD_sub_both ctx dir fuel) dir _ _ 0 k _ r' hr',
            rfl⟩

/-- **The views of any direction are views of `.both`.** -/
theorem rawNodeD_sub_both {ctx : Ctx} {dir : Dir} {fuel : Nat} {m : Node} {k : Nat}
    {P : Finset C} {r : RawL} (h : r ∈ rawNodeD ctx dir fuel m k P) :
    r ∈ rawNodeD ctx .both fuel m k P :=
  kidsOfD_mono _ _ (rawOptD_sub_both ctx dir fuel) dir _ _ 0 k P r h

theorem baseRecsR_sub_both {ctx : Ctx} {dir : Dir} {laws : Laws} {n : Node} {r : RecR}
    (h : r ∈ baseRecsR ctx dir laws n) : r ∈ baseRecsR ctx .both laws n := by
  unfold baseRecsR rawRecordsLD at h ⊢
  obtain ⟨r', hr', rfl⟩ := List.mem_map.1 h
  obtain ⟨raw, hraw, he⟩ := List.mem_filterMap.1 hr'
  exact List.mem_map.2 ⟨r', List.mem_filterMap.2 ⟨raw, rawNodeD_sub_both hraw, he⟩, rfl⟩

/-! ## A position off the spine is kept -/

theorem rawOptD_false {ctx : Ctx} {dir : Dir} {fuel : Nat} {X : C} {k : Nat} {P : Finset C}
    {r : RawL} (h : r ∈ rawOptD ctx dir fuel false X k P) : r = ([(X, k)], []) := by
  cases fuel with
  | zero => simpa [rawOptD] using h
  | succ fuel => simpa [rawOptD] using h

/-! ## The left fold -/

/-- The product over the positions of a left fold: at position `0` the head
option and the rest kept, elsewhere everything kept. -/
theorem kidsOfD_left_sound {ctx : Ctx} (opt : Bool → C → Nat → Finset C → List RawL)
    (hT : ∀ X k P r, r ∈ opt true X k P → ∃ v, r.1 = withK k v ∧ OptLeft ctx P X v)
    (hF : ∀ X k P r, r ∈ opt false X k P → r.1 = [(X, k)]) (len : Nat) :
    ∀ (cs : List C) (i k : Nat) (P : Finset C) (r : RawL),
      r ∈ kidsOfD opt .left len (withK 1 cs) i k P →
        (i = 0 → ∃ v, r.1 = withK k v ∧ OTLeft ctx P cs v) ∧ (i ≠ 0 → r.1 = withK k cs)
  | [], i, k, P, r, hr => by
      simp only [withK, List.map_nil, kidsOfD, List.mem_singleton] at hr
      subst hr
      exact ⟨fun _ => ⟨[], rfl, OTLeft.nil⟩, fun _ => rfl⟩
  | X :: cs, i, k, P, r, hr => by
      simp only [withK, List.map_cons, kidsOfD, List.mem_flatMap, List.mem_map] at hr
      obtain ⟨r₁, h₁, r₂, h₂, rfl⟩ := hr
      have h₂' := (kidsOfD_left_sound opt hT hF len cs (i + 1) k P r₂ h₂).2 (Nat.succ_ne_zero i)
      rw [Nat.mul_one] at h₁
      constructor
      · rintro rfl
        simp only [spineB, beq_self_eq_true] at h₁
        obtain ⟨v, hv, ho⟩ := hT _ _ _ _ h₁
        exact ⟨v ++ cs, by simp [hv, h₂', withK_append], ho.cons⟩
      · intro hi
        have hb : spineB .left i len = false := by
          simp only [spineB, beq_eq_false_iff_ne, ne_eq]; exact hi
        rw [hb] at h₁
        have := hF _ _ _ _ h₁
        simp [this, h₂', withK]

theorem rawOptD_left_sound {ctx : Ctx} (hκ : ctx.κ = .assoc) (hs : SeqShaped ctx) :
    ∀ (fuel : Nat) (X : C) (k : Nat) (P : Finset C) (r : RawL),
      r ∈ rawOptD ctx .left fuel true X k P → ∃ v, r.1 = withK k v ∧ OptLeft ctx P X v
  | 0, X, k, P, r, hr => by
      simp only [rawOptD, List.mem_singleton] at hr
      subst hr
      exact ⟨[X], rfl, Or.inl rfl⟩
  | fuel + 1, X, k, P, r, hr => by
      simp only [rawOptD, List.mem_cons] at hr
      rcases hr with rfl | hr
      · exact ⟨[X], rfl, Or.inl rfl⟩
      · split at hr
        · simp at hr
        · next hb =>
          have hX : X ∉ P := fun h => hb (Or.inr h)
          simp only [List.mem_flatMap, List.mem_map] at hr
          obtain ⟨p, hp, r', hr', rfl⟩ := hr
          have hmem := Ctx.mem_members.1 hp
          obtain ⟨cs, hcs⟩ := hs _ _ _ hmem
          rw [hκ, hcs, kids_seq] at hr'
          obtain ⟨v, hv, ht⟩ := (kidsOfD_left_sound (ctx := ctx) _
            (fun X k P r h => rawOptD_left_sound hκ hs fuel X k P r h)
            (fun _ _ _ _ h => by rw [rawOptD_false h]) _ cs 0 k _ r' hr').1 rfl
          exact ⟨v, hv, Or.inr ⟨hX, p.1, p.2, cs, hmem, hcs, ht⟩⟩

/-- **Every raw view of the left-fold enumerator is a spine view.** -/
theorem rawNodeD_left_sound {ctx : Ctx} (hκ : ctx.κ = .assoc) (hs : SeqShaped ctx) {n : Node}
    {cs : List C} (hn : n.children = .seq cs) {fuel k : Nat} {P : Finset C} {r : RawL}
    (h : r ∈ rawNodeD ctx .left fuel n k P) : ∃ v, r.1 = withK k v ∧ OTLeft ctx P cs v := by
  unfold rawNodeD at h
  rw [hκ, hn, kids_seq] at h
  exact (kidsOfD_left_sound _ (fun X k P r h => rawOptD_left_sound hκ hs fuel X k P r h)
    (fun _ _ _ _ h => by rw [rawOptD_false h]) _ cs 0 k P r h).1 rfl

/-- **Every spine view of a left fold is a raw view of the enumerator**, with
enough fuel. -/
theorem kidsOfD_left_complete {ctx : Ctx} (hκ : ctx.κ = .assoc) :
    ∀ (fuel : Nat) {P : Finset C} {cs v : List C}, OTLeft ctx P cs v → P ⊆ classesOf ctx.G →
      (classesOf ctx.G).card - P.card ≤ fuel → ∀ (len k : Nat),
        ∃ ls, (withK k v, ls) ∈ kidsOfD (rawOptD ctx .left fuel) .left len (withK 1 cs) 0 k P := by
  intro fuel P cs v h
  induction h generalizing fuel with
  | nil => intro _ _ len k; exact ⟨[], by simp [withK, kidsOfD]⟩
  | @keep P xs =>
      intro _ _ len k
      refine ⟨[], ?_⟩
      have := kidsOfD_kept _ (rawOptD_kept ctx .left fuel) .left len (withK 1 xs) 0 k P
      rwa [scale_withK] at this
  | @opn P X rest id m cs v hX hm hcs _ ih =>
      intro hP hfuel len k
      have hXc : X ∈ classesOf ctx.G := IsMember.cls_mem hm
      have hlt : P.card < (classesOf ctx.G).card :=
        Finset.card_lt_card ⟨hP, fun hsub => hX (hsub hXc)⟩
      obtain ⟨fuel, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      have hP' : insert X P ⊆ classesOf ctx.G := Finset.insert_subset hXc hP
      have hcard : (insert X P).card = P.card + 1 := Finset.card_insert_of_notMem hX
      obtain ⟨ls, hls⟩ := ih fuel hP' (by omega) (kids ctx.κ m.children).length k
      have hrest := kidsOfD_kept _ (rawOptD_kept ctx .left (fuel + 1)) .left len (withK 1 rest) 1 k P
      rw [scale_withK] at hrest
      have hhead : (withK k v, leafifyL X k (withK k v) ls) ∈
          rawOptD ctx .left (fuel + 1) (spineB .left 0 len) X (k * 1) P := by
        have hb : spineB .left 0 len = true := rfl
        rw [hb, Nat.mul_one]
        refine List.mem_cons_of_mem _ ?_
        rw [ite_eq_right_of_eq_false _ _ (eq_false (show ¬(true = false ∨ X ∈ P) by simp [hX]))]
        refine List.mem_flatMap.2 ⟨(id, m), Ctx.mem_members.2 hm, List.mem_map.2 ⟨(withK k v, ls), ?_, rfl⟩⟩
        rw [hκ, hcs, kids_seq] at hls ⊢
        exact hls
      refine ⟨leafifyL X k (withK k v) ls ++ [], ?_⟩
      rw [withK_append]
      show _ ∈ kidsOfD _ .left len ((X, 1) :: withK 1 rest) 0 k P
      simp only [kidsOfD]
      exact List.mem_flatMap.2 ⟨_, hhead, List.mem_map.2 ⟨_, hrest, rfl⟩⟩

theorem rawNodeD_left_complete {ctx : Ctx} (hκ : ctx.κ = .assoc) {n : Node} {cs : List C}
    (hn : n.children = .seq cs) {P : Finset C} {v : List C} (h : OTLeft ctx P cs v)
    (hP : P ⊆ classesOf ctx.G) {fuel : Nat} (hfuel : (classesOf ctx.G).card - P.card ≤ fuel)
    (k : Nat) : ∃ ls, (withK k v, ls) ∈ rawNodeD ctx .left fuel n k P := by
  unfold rawNodeD
  rw [hκ, hn, kids_seq]
  exact kidsOfD_left_complete hκ fuel h hP hfuel _ k

/-- **The executable left-fold enumerator produces exactly the spine views**
(`rawOptD` with `Dir.left` against `OTLeft`), at the root. -/
theorem rawNodeD_left_iff {ctx : Ctx} (hκ : ctx.κ = .assoc) (hs : SeqShaped ctx) {n : Node}
    {cs : List C} (hn : n.children = .seq cs) {w : List (C × Nat)} :
    (∃ ls, (w, ls) ∈ rawNodeD ctx .left (fuelOf ctx.G) n 1 ∅) ↔
      ∃ v, w = withK 1 v ∧ OTLeft ctx ∅ cs v := by
  constructor
  · rintro ⟨ls, h⟩
    obtain ⟨v, hv, ht⟩ := rawNodeD_left_sound hκ hs hn h
    exact ⟨v, hv, ht⟩
  · rintro ⟨v, rfl, ht⟩
    exact rawNodeD_left_complete hκ hn ht (Finset.empty_subset _) (by simp [fuelOf]) 1

theorem rawViews_left_iff {ctx : Ctx} (hκ : ctx.κ = .assoc) (hs : SeqShaped ctx) {n : Node}
    {cs : List C} (hn : n.children = .seq cs) {v : List C} :
    (∃ ls, (withK 1 v, ls) ∈ rawNodeD ctx .left (fuelOf ctx.G) n 1 ∅) ↔ OTLeft ctx ∅ cs v := by
  rw [rawNodeD_left_iff hκ hs hn]
  constructor
  · rintro ⟨v', hv, ht⟩; rw [withK_inj hv]; exact ht
  · intro ht; exact ⟨v, rfl, ht⟩

/-! ## The right fold -/

theorem kidsOfD_right_sound {ctx : Ctx} (opt : Bool → C → Nat → Finset C → List RawL)
    (hT : ∀ X k P r, r ∈ opt true X k P → ∃ v, r.1 = withK k v ∧ OptRight ctx P X v)
    (hF : ∀ X k P r, r ∈ opt false X k P → r.1 = [(X, k)]) (len : Nat) :
    ∀ (cs : List C) (i k : Nat) (P : Finset C) (r : RawL), i + cs.length = len →
      r ∈ kidsOfD opt .right len (withK 1 cs) i k P → ∃ v, r.1 = withK k v ∧ OTRight ctx P cs v
  | [], i, k, P, r, _, hr => by
      simp only [withK, List.map_nil, kidsOfD, List.mem_singleton] at hr
      subst hr
      exact ⟨[], rfl, OTRight.keep⟩
  | X :: cs, i, k, P, r, hlen, hr => by
      simp only [withK, List.map_cons, kidsOfD, List.mem_flatMap, List.mem_map] at hr
      obtain ⟨r₁, h₁, r₂, h₂, rfl⟩ := hr
      rw [Nat.mul_one] at h₁
      cases cs with
      | nil =>
          simp only [List.length_cons, List.length_nil, Nat.zero_add] at hlen
          have hb : spineB .right i len = true := by simp [spineB, hlen]
          rw [hb] at h₁
          obtain ⟨v, hv, ho⟩ := hT _ _ _ _ h₁
          simp only [List.map_nil, kidsOfD, List.mem_singleton] at h₂
          subst h₂
          refine ⟨v, by simp [hv], ?_⟩
          have := ho.snoc (rest := [])
          simpa using this
      | cons Y cs =>
          have hb : spineB .right i len = false := by
            simp only [spineB, beq_eq_false_iff_ne, ne_eq]
            simp only [List.length_cons] at hlen
            omega
          rw [hb] at h₁
          have h₁' := hF _ _ _ _ h₁
          obtain ⟨v, hv, ht⟩ := kidsOfD_right_sound opt hT hF len (Y :: cs) (i + 1) k P r₂
            (by simp only [List.length_cons] at hlen ⊢; omega) h₂
          exact ⟨X :: v, by simp [h₁', hv, withK], ht.cons⟩

theorem rawOptD_right_sound {ctx : Ctx} (hκ : ctx.κ = .assoc) (hs : SeqShaped ctx) :
    ∀ (fuel : Nat) (X : C) (k : Nat) (P : Finset C) (r : RawL),
      r ∈ rawOptD ctx .right fuel true X k P → ∃ v, r.1 = withK k v ∧ OptRight ctx P X v
  | 0, X, k, P, r, hr => by
      simp only [rawOptD, List.mem_singleton] at hr
      subst hr
      exact ⟨[X], rfl, Or.inl rfl⟩
  | fuel + 1, X, k, P, r, hr => by
      simp only [rawOptD, List.mem_cons] at hr
      rcases hr with rfl | hr
      · exact ⟨[X], rfl, Or.inl rfl⟩
      · split at hr
        · simp at hr
        · next hb =>
          have hX : X ∉ P := fun h => hb (Or.inr h)
          simp only [List.mem_flatMap, List.mem_map] at hr
          obtain ⟨p, hp, r', hr', rfl⟩ := hr
          have hmem := Ctx.mem_members.1 hp
          obtain ⟨cs, hcs⟩ := hs _ _ _ hmem
          rw [hκ, hcs, kids_seq] at hr'
          obtain ⟨v, hv, ht⟩ := kidsOfD_right_sound (ctx := ctx) _
            (fun X k P r h => rawOptD_right_sound hκ hs fuel X k P r h)
            (fun _ _ _ _ h => by rw [rawOptD_false h]) _ cs 0 k _ r' (by simp [withK]) hr'
          exact ⟨v, hv, Or.inr ⟨hX, p.1, p.2, cs, hmem, hcs, ht⟩⟩

/-- **Every raw view of the right-fold enumerator is a spine view.** -/
theorem rawNodeD_right_sound {ctx : Ctx} (hκ : ctx.κ = .assoc) (hs : SeqShaped ctx) {n : Node}
    {cs : List C} (hn : n.children = .seq cs) {fuel k : Nat} {P : Finset C} {r : RawL}
    (h : r ∈ rawNodeD ctx .right fuel n k P) : ∃ v, r.1 = withK k v ∧ OTRight ctx P cs v := by
  unfold rawNodeD at h
  rw [hκ, hn, kids_seq] at h
  exact kidsOfD_right_sound _ (fun X k P r h => rawOptD_right_sound hκ hs fuel X k P r h)
    (fun _ _ _ _ h => by rw [rawOptD_false h]) _ cs 0 k P r (by simp [withK]) h

/-- The product over an appended position list. -/
theorem kidsOfD_append (opt : Bool → C → Nat → Finset C → List RawL) (dir : Dir) (len : Nat) :
    ∀ (a b : List (C × Nat)) (i k : Nat) (P : Finset C) (r₁ r₂ : RawL),
      r₁ ∈ kidsOfD opt dir len a i k P → r₂ ∈ kidsOfD opt dir len b (i + a.length) k P →
        (r₁.1 ++ r₂.1, r₁.2 ++ r₂.2) ∈ kidsOfD opt dir len (a ++ b) i k P
  | [], b, i, k, P, r₁, r₂, h₁, h₂ => by
      simp only [kidsOfD, List.mem_singleton] at h₁
      subst h₁
      simpa using h₂
  | (X, j) :: a, b, i, k, P, r₁, r₂, h₁, h₂ => by
      simp only [List.cons_append, kidsOfD, List.mem_flatMap, List.mem_map] at h₁ ⊢
      obtain ⟨s₁, hs₁, s₂, hs₂, rfl⟩ := h₁
      refine ⟨s₁, hs₁, (s₂.1 ++ r₂.1, s₂.2 ++ r₂.2), ?_, by simp⟩
      apply kidsOfD_append opt dir len a b (i + 1) k P s₂ r₂ hs₂
      simpa [Nat.add_assoc, Nat.add_comm 1] using h₂

theorem kidsOfD_right_complete {ctx : Ctx} (hκ : ctx.κ = .assoc) :
    ∀ (fuel : Nat) {P : Finset C} {cs v : List C}, OTRight ctx P cs v → P ⊆ classesOf ctx.G →
      (classesOf ctx.G).card - P.card ≤ fuel → ∀ (k : Nat),
        ∃ ls, (withK k v, ls) ∈
          kidsOfD (rawOptD ctx .right fuel) .right cs.length (withK 1 cs) 0 k P := by
  intro fuel P cs v h
  induction h generalizing fuel with
  | @keep P xs =>
      intro _ _ k
      refine ⟨[], ?_⟩
      have := kidsOfD_kept _ (rawOptD_kept ctx .right fuel) .right xs.length (withK 1 xs) 0 k P
      rwa [scale_withK] at this
  | @opn P X rest id m cs v hX hm hcs _ ih =>
      intro hP hfuel k
      have hXc : X ∈ classesOf ctx.G := IsMember.cls_mem hm
      have hlt : P.card < (classesOf ctx.G).card :=
        Finset.card_lt_card ⟨hP, fun hsub => hX (hsub hXc)⟩
      obtain ⟨fuel, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      have hP' : insert X P ⊆ classesOf ctx.G := Finset.insert_subset hXc hP
      have hcard : (insert X P).card = P.card + 1 := Finset.card_insert_of_notMem hX
      obtain ⟨ls, hls⟩ := ih fuel hP' (by omega) k
      have hrest := kidsOfD_kept _ (rawOptD_kept ctx .right (fuel + 1)) .right
        (rest ++ [X]).length (withK 1 rest) 0 k P
      rw [scale_withK] at hrest
      have hhead : (withK k v, leafifyL X k (withK k v) ls) ∈
          rawOptD ctx .right (fuel + 1) (spineB .right (0 + (withK 1 rest).length) (rest ++ [X]).length)
            X (k * 1) P := by
        have hb : spineB .right (0 + (withK 1 rest).length) (rest ++ [X]).length = true := by
          simp [spineB, withK]
        rw [hb, Nat.mul_one]
        refine List.mem_cons_of_mem _ ?_
        rw [ite_eq_right_of_eq_false _ _ (eq_false (show ¬(true = false ∨ X ∈ P) by simp [hX]))]
        refine List.mem_flatMap.2 ⟨(id, m), Ctx.mem_members.2 hm, List.mem_map.2 ⟨(withK k v, ls), ?_, rfl⟩⟩
        rw [hκ, hcs, kids_seq]
        simpa [withK] using hls
      have hlast : (withK k v, leafifyL X k (withK k v) ls) ∈
          kidsOfD (rawOptD ctx .right (fuel + 1)) .right (rest ++ [X]).length (withK 1 [X])
            (0 + (withK 1 rest).length) k P := by
        show _ ∈ kidsOfD _ .right _ [(X, 1)] _ k P
        simp only [kidsOfD]
        exact List.mem_flatMap.2 ⟨_, hhead, List.mem_map.2 ⟨([], []), List.mem_singleton.2 rfl,
          by simp⟩⟩
      have := kidsOfD_append _ .right _ _ _ 0 k P _ _ hrest hlast
      rw [← withK_append, ← withK_append] at this
      exact ⟨_, this⟩

theorem rawNodeD_right_complete {ctx : Ctx} (hκ : ctx.κ = .assoc) {n : Node} {cs : List C}
    (hn : n.children = .seq cs) {P : Finset C} {v : List C} (h : OTRight ctx P cs v)
    (hP : P ⊆ classesOf ctx.G) {fuel : Nat} (hfuel : (classesOf ctx.G).card - P.card ≤ fuel)
    (k : Nat) : ∃ ls, (withK k v, ls) ∈ rawNodeD ctx .right fuel n k P := by
  unfold rawNodeD
  rw [hκ, hn, kids_seq]
  have := kidsOfD_right_complete hκ fuel h hP hfuel k
  simpa [withK] using this

/-- **The executable right-fold enumerator produces exactly the spine views**
(`rawOptD` with `Dir.right` against `OTRight`), at the root. -/
theorem rawNodeD_right_iff {ctx : Ctx} (hκ : ctx.κ = .assoc) (hs : SeqShaped ctx) {n : Node}
    {cs : List C} (hn : n.children = .seq cs) {w : List (C × Nat)} :
    (∃ ls, (w, ls) ∈ rawNodeD ctx .right (fuelOf ctx.G) n 1 ∅) ↔
      ∃ v, w = withK 1 v ∧ OTRight ctx ∅ cs v := by
  constructor
  · rintro ⟨ls, h⟩
    obtain ⟨v, hv, ht⟩ := rawNodeD_right_sound hκ hs hn h
    exact ⟨v, hv, ht⟩
  · rintro ⟨v, rfl, ht⟩
    exact rawNodeD_right_complete hκ hn ht (Finset.empty_subset _) (by simp [fuelOf]) 1

theorem rawViews_right_iff {ctx : Ctx} (hκ : ctx.κ = .assoc) (hs : SeqShaped ctx) {n : Node}
    {cs : List C} (hn : n.children = .seq cs) {v : List C} :
    (∃ ls, (withK 1 v, ls) ∈ rawNodeD ctx .right (fuelOf ctx.G) n 1 ∅) ↔ OTRight ctx ∅ cs v := by
  rw [rawNodeD_right_iff hκ hs hn]
  constructor
  · rintro ⟨v', hv, ht⟩; rw [withK_inj hv]; exact ht
  · intro ht; exact ⟨v, rfl, ht⟩

/-! ## The distinct views of the fold enumerator -/

theorem map_fst_enumerateFromL (recs : List RecL) :
    (enumerateFromL recs).map Prod.fst = (recs.map Prod.fst).dedup := by
  unfold enumerateFromL
  simp [List.map_map, Function.comp_def]

theorem mem_views_enumerateLD {ctx : Ctx} {dir : Dir} {laws : Laws} {n : Node}
    {w : List (C × Nat)} :
    w ∈ (enumerateLD ctx dir laws n).map Prod.fst ↔
      ∃ raw ∈ rawNodeD ctx dir (fuelOf ctx.G) n 1 ∅, normalize ctx.κ laws raw.1 = .node w := by
  unfold enumerateLD
  rw [map_fst_enumerateFromL, List.mem_dedup, List.mem_map]
  unfold rawRecordsLD
  constructor
  · rintro ⟨r, hr, rfl⟩
    obtain ⟨raw, hraw, he⟩ := List.mem_filterMap.1 hr
    refine ⟨raw, hraw, ?_⟩
    revert he
    cases hn : normalize ctx.κ laws raw.1 with
    | node w' =>
        intro he
        simp only [Option.some.injEq] at he
        subst he
        rfl
    | _ => simp
  · rintro ⟨raw, hraw, hn⟩
    exact ⟨(w, flagLeaves ctx.κ laws raw.1 raw.2), List.mem_filterMap.2 ⟨raw, hraw, by rw [hn]⟩,
      rfl⟩

/-- **The views of the left-fold enumerator are the normal forms of the
spine views.** -/
theorem enumerateLD_left_iff {ctx : Ctx} (hκ : ctx.κ = .assoc) (hs : SeqShaped ctx) {laws : Laws}
    {n : Node} {cs : List C} (hn : n.children = .seq cs) {w : List (C × Nat)} :
    w ∈ (enumerateLD ctx .left laws n).map Prod.fst ↔
      ∃ v, OTLeft ctx ∅ cs v ∧ normalize .assoc laws (withK 1 v) = .node w := by
  rw [mem_views_enumerateLD, hκ]
  constructor
  · rintro ⟨raw, hraw, hnorm⟩
    obtain ⟨v, hv, ht⟩ := rawNodeD_left_sound hκ hs hn hraw
    exact ⟨v, ht, by rw [← hv]; exact hnorm⟩
  · rintro ⟨v, ht, hnorm⟩
    obtain ⟨ls, hls⟩ := rawNodeD_left_complete (fuel := fuelOf ctx.G) hκ hn ht
      (Finset.empty_subset _) (by simp [fuelOf]) 1
    exact ⟨(withK 1 v, ls), hls, hnorm⟩

theorem enumerateLD_right_iff {ctx : Ctx} (hκ : ctx.κ = .assoc) (hs : SeqShaped ctx)
    {laws : Laws} {n : Node} {cs : List C} (hn : n.children = .seq cs) {w : List (C × Nat)} :
    w ∈ (enumerateLD ctx .right laws n).map Prod.fst ↔
      ∃ v, OTRight ctx ∅ cs v ∧ normalize .assoc laws (withK 1 v) = .node w := by
  rw [mem_views_enumerateLD, hκ]
  constructor
  · rintro ⟨raw, hraw, hnorm⟩
    obtain ⟨v, hv, ht⟩ := rawNodeD_right_sound hκ hs hn hraw
    exact ⟨v, ht, by rw [← hv]; exact hnorm⟩
  · rintro ⟨v, ht, hnorm⟩
    obtain ⟨ls, hls⟩ := rawNodeD_right_complete (fuel := fuelOf ctx.G) hκ hn ht
      (Finset.empty_subset _) (by simp [fuelOf]) 1
    exact ⟨(withK 1 v, ls), hls, hnorm⟩

/-- **Every view of the executable left-fold enumerator denotes the node's
left fold** (`otLeft_sound` for `rawOptD`): laws-free, as the engine declares
no law on a fold. -/
theorem enumerateLD_left_sound {ctx : Ctx} (hκ : ctx.κ = .assoc) (hs : SeqShaped ctx)
    {den : C → BTm} (hc : ConsistentL ctx den) {n : Node} {cs : List C}
    (hn : n.children = .seq cs) {w : List (C × Nat)} {d : DemandL}
    (h : (w, d) ∈ enumerateLD ctx .left Laws.free n) :
    lfold ((w.map Prod.fst).map den) = lfold (cs.map den) := by
  have hw : w ∈ (enumerateLD ctx .left Laws.free n).map Prod.fst := List.mem_map.2 ⟨_, h, rfl⟩
  obtain ⟨v, ht, hnorm⟩ := (enumerateLD_left_iff hκ hs hn).1 hw
  rw [normalize_free_assoc hnorm, withK_map_fst]
  exact otLeft_sound hc ht

theorem enumerateLD_right_sound {ctx : Ctx} (hκ : ctx.κ = .assoc) (hs : SeqShaped ctx)
    {den : C → BTm} (hc : ConsistentR ctx den) {n : Node} {cs : List C}
    (hn : n.children = .seq cs) {w : List (C × Nat)} {d : DemandL}
    (h : (w, d) ∈ enumerateLD ctx .right Laws.free n) :
    rfold ((w.map Prod.fst).map den) = rfold (cs.map den) := by
  have hw : w ∈ (enumerateLD ctx .right Laws.free n).map Prod.fst := List.mem_map.2 ⟨_, h, rfl⟩
  obtain ⟨v, ht, hnorm⟩ := (enumerateLD_right_iff hκ hs hn).1 hw
  rw [normalize_free_assoc hnorm, withK_map_fst]
  exact otRight_sound hc ht

end Semper.EMatch.Flatten
