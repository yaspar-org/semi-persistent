import SemperProofs.EMatch.Flatten.LawsMain

/-!
# `:flatten`: the engine's demand rule, flag and pruning, as the code computes them

The engine keeps one `Demand::accepts` (`flatten.rs:271-283`) for every kind:

```
non_inert || (merge_on_close && taken ∋ opened) || elems ∩ taken ≠ ∅
```

with `merge_on_close = (kind == Ac)` (`flatten.rs:354`). The laws development
(`Laws.lean`) proves completeness of `DemandL.acceptsLaws`, whose leaf test
`LeafF.okL` has the opened-class clause for **every** kind; the engine has
it for multisets only. This file

* defines the engine's leaf test `LeafF.okE` and rule `DemandL.acceptsE` and
  proves `acceptsE .ac = acceptsLaws` (`acceptsE_ac_iff`) and
  `acceptsE κ → acceptsLaws` (`acceptsE_imp_acceptsLaws`): on sets and
  sequences the engine accepts fewer matches than `acceptsLaws`;
* models the engine's flag `Leaf::non_inert` as the code computes it, on the
  raw view and the mask of the positions directly under the leaf
  (`nonInertEng`, `flatten.rs:481-545`: residues summed one by one under the
  nilpotent order, the three inverse loops), and proves it equal to the
  model's `nonInertB` on every leaf block (`nonInertEng_eq`);
* models the walk's pruning (`flatten.rs:787-801`): a leaf is kept when a
  direct element is takeable, or (multisets) its opened class is takeable,
  or `may_be_non_inert` (`flatten.rs:552-569`, `mayNonInert`); proves the
  flag implies `mayNonInert` (`nonInertB_imp_mayNonInert`) and hence that
  the pruned enumeration accepts exactly the same matches as the full one
  for every `taken` inside the takeable set (`prune_engine`).
-/

namespace Semper.EMatch.Flatten

open Semper.EMatch

/-! ## The engine's rule -/

/-- `Demand::accepts`, one leaf (`flatten.rs:276-280`), in the order of
`LeafF.okL`: the opened class is taken (multisets only), a direct element
is taken, or the leaf is flagged non-inert. -/
def LeafF.okE (κ : FlatKind) (taken : List C) (l : LeafF) : Prop :=
  (mergeOnClose κ = true ∧ l.1.X ∈ taken) ∨ (∃ c ∈ l.1.g, c ∈ taken) ∨ l.2 = true

instance (κ : FlatKind) (taken : List C) (l : LeafF) : Decidable (l.okE κ taken) := by
  unfold LeafF.okE; infer_instance

/-- `Demand::accepts` (`flatten.rs:273-282`). -/
def DemandL.acceptsE (κ : FlatKind) (d : DemandL) (taken : List C) : Prop :=
  d.unconditional = true ∨ ∃ ls ∈ d.alts, ∀ l ∈ ls, l.okE κ taken

/-- The executable form, in the code's order of the three tests. -/
def DemandL.acceptsEB (κ : FlatKind) (d : DemandL) (taken : List C) : Bool :=
  d.unconditional || d.alts.any (fun ls => ls.all (fun l =>
    l.2 || (mergeOnClose κ && decide (l.1.X ∈ taken)) || l.1.g.any (fun c => decide (c ∈ taken))))

theorem DemandL.acceptsEB_iff (κ : FlatKind) (d : DemandL) (taken : List C) :
    d.acceptsEB κ taken = true ↔ d.acceptsE κ taken := by
  unfold DemandL.acceptsEB DemandL.acceptsE LeafF.okE
  simp only [Bool.or_eq_true, List.any_eq_true, List.all_eq_true, Bool.and_eq_true,
    decide_eq_true_eq]
  constructor
  · rintro (h | ⟨ls, hls, h⟩)
    · exact Or.inl h
    · refine Or.inr ⟨ls, hls, fun l hl => ?_⟩
      rcases h l hl with (h | h) | h
      · exact Or.inr (Or.inr h)
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
  · rintro (h | ⟨ls, hls, h⟩)
    · exact Or.inl h
    · refine Or.inr ⟨ls, hls, fun l hl => ?_⟩
      rcases h l hl with h | h | h
      · exact Or.inl (Or.inr h)
      · exact Or.inr h
      · exact Or.inl (Or.inl h)

theorem LeafF.okE_ac_iff (taken : List C) (l : LeafF) : l.okE .ac taken ↔ l.okL taken := by
  simp [LeafF.okE, LeafF.okL, mergeOnClose]

theorem LeafF.okE_imp_okL {κ : FlatKind} {taken : List C} {l : LeafF} (h : l.okE κ taken) :
    l.okL taken := by
  rcases h with ⟨-, h⟩ | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

/-- On sets and sequences the engine's leaf test is the model's without the
opened-class clause. -/
theorem LeafF.okE_of_ne_ac {κ : FlatKind} (hκ : κ ≠ .ac) (taken : List C) (l : LeafF) :
    l.okE κ taken ↔ (∃ c ∈ l.1.g, c ∈ taken) ∨ l.2 = true := by
  have : mergeOnClose κ = false := by cases κ <;> simp_all [mergeOnClose]
  simp [LeafF.okE, this]

/-- **The engine's rule is the laws rule on multisets.** -/
theorem DemandL.acceptsE_ac_iff (d : DemandL) (taken : List C) :
    d.acceptsE .ac taken ↔ d.acceptsLaws taken := by
  unfold DemandL.acceptsE DemandL.acceptsLaws
  simp only [LeafF.okE_ac_iff]

/-- The engine accepts no match the laws rule rejects (every kind). -/
theorem DemandL.acceptsE_imp_acceptsLaws {κ : FlatKind} {d : DemandL} {taken : List C}
    (h : d.acceptsE κ taken) : d.acceptsLaws taken := by
  rcases h with h | ⟨ls, hls, h⟩
  · exact Or.inl h
  · exact Or.inr ⟨ls, hls, fun l hl => LeafF.okE_imp_okL (h l hl)⟩

/-- A tree whose every flagged leaf passes the engine's test makes its view's
demand accept under the engine's rule. -/
theorem acceptsE_of_tree {ctx : Ctx} {laws : Laws} {n : Node} {v w : List (C × Nat)}
    {ls : List LeafL} {o : Nat} {taken : List C} (hv : RawViewL ctx n v ls o)
    (hn : normalize ctx.κ laws v = .node w)
    (hok : ∀ l ∈ flagLeaves ctx.κ laws v ls, l.okE ctx.κ taken) :
    ∃ d, (w, d) ∈ enumerateL ctx laws n ∧ d.acceptsE ctx.κ taken := by
  obtain ⟨d, hd, hu, ha⟩ := views_completeL hv hn
  refine ⟨d, hd, ?_⟩
  by_cases hls : ls = []
  · exact Or.inl (hu hls)
  · rcases ha hls with h | h
    · exact Or.inl h
    · exact Or.inr ⟨_, h, hok⟩

/-- The engine's rule read through the emitted demand: some tree giving the
view opens nothing, or has every flagged leaf passing the engine's test. -/
def AltsEAccept (κ : FlatKind) (A : Set (List LeafF)) (taken : List C) : Prop :=
  [] ∈ A ∨ ∃ ls ∈ A, ∀ l ∈ ls, l.okE κ taken

theorem acceptsE_demandOfL {κ : FlatKind} {recs : List RecL} {w : List (C × Nat)}
    {taken : List C} :
    (demandOfL recs w).acceptsE κ taken ↔ ∃ ls ∈ altsOfL recs w, ∀ l ∈ ls, l.okE κ taken := by
  unfold demandOfL DemandL.acceptsE
  split
  · rename_i h
    simp only [true_or, true_iff]
    exact ⟨[], h, by simp⟩
  · simp

theorem acceptsE_iff_altsEAccept {ctx : Ctx} {laws : Laws} {n : Node}
    {w : List (C × Nat)} {d : DemandL} (h : (w, d) ∈ enumerateL ctx laws n)
    (taken : List C) :
    d.acceptsE ctx.κ taken ↔ AltsEAccept ctx.κ (AltsL ctx laws n w) taken := by
  obtain ⟨-, rfl⟩ := mem_enumerateFromL.1 h
  rw [acceptsE_demandOfL]
  unfold AltsEAccept
  constructor
  · rintro ⟨ls, hr, hall⟩
    obtain ⟨v, ls', o, hv, hn, rfl⟩ := mem_rawRecordsL.1 (mem_altsOfL.1 hr)
    exact Or.inr ⟨_, ⟨v, ls', o, hv, hn, rfl⟩, hall⟩
  · rintro (⟨v, ls', o, hv, hn, hnil⟩ | ⟨ls, ⟨v, ls', o, hv, hn, rfl⟩, hall⟩)
    · exact ⟨[], mem_altsOfL.2 (mem_rawRecordsL.2 ⟨v, ls', o, hv, hn, hnil⟩), by simp⟩
    · exact ⟨_, mem_altsOfL.2 (mem_rawRecordsL.2 ⟨v, ls', o, hv, hn, rfl⟩), hall⟩

/-! ## The engine's flag, as the code computes it -/

/-- The entries of `v` at the positions the mask `u` marks. -/
def maskIn (v : List (C × Nat)) (u : List Bool) : List (C × Nat) :=
  ((v.zip u).filter (fun p => p.2)).map Prod.fst

/-- The entries of `v` at the positions the mask does not mark. -/
def maskOut (v : List (C × Nat)) (u : List Bool) : List (C × Nat) :=
  ((v.zip u).filter (fun p => !p.2)).map Prod.fst

/-- The nilpotent residue loop (`flatten.rs:507-515`): start from the folded
count's residue, add the residue of every entry of class `X` outside the
leaf, reducing after each addition. -/
def residueLoop (r : Nat) (X : C) (start : Nat) (out : List (C × Nat)) : Nat :=
  out.foldl (fun acc e => if e.1 = X then (acc + e.2 % r) % r else acc) (start % r)

/-- `FlattenScratch::non_inert` (`flatten.rs:481-545`) on the complete raw
view `v`, the mask `u` of the positions directly under the leaf (the code's
`under`), the leaf's opened class `X` and folded count `k`. -/
def nonInertEng (κ : FlatKind) (laws : Laws) (v : List (C × Nat)) (u : List Bool)
    (X : C) (k : Nat) : Bool :=
  let under := maskIn v u
  let touched : C → Bool := fun c => decide (c = X) || under.any (fun e => decide (e.1 = c))
  let present : C → Bool := fun c => decide (c = X) || v.any (fun e => decide (e.1 = c))
  if laws.unit = some X then true
  else match κ with
    | .assoc => under.all (fun e => decide (laws.unit = some e.1))
    | .aci => false
    | .ac =>
        (match laws.nilpotent with
         | some r => decide (residueLoop r X k (maskOut v u) = 0)
         | none => false) ||
        (match laws.inv with
         | some inv =>
             (inv X).any (fun y => present y || touched y) ||
             under.any (fun e => (inv e.1).any present) ||
             v.any (fun e => (inv e.1).any touched)
         | none => false)

/-- The mask of a leaf block: `v₁` unmarked, the block marked, `v₂` unmarked. -/
def blockMask (n₁ nL n₂ : Nat) : List Bool :=
  List.replicate n₁ false ++ List.replicate nL true ++ List.replicate n₂ false

theorem zip_append_eq {α β : Type} (a₁ a₂ : List α) (b₁ b₂ : List β) (h : a₁.length = b₁.length) :
    (a₁ ++ a₂).zip (b₁ ++ b₂) = a₁.zip b₁ ++ a₂.zip b₂ :=
  List.zip_append h

theorem filter_zip_replicate {α : Type} (a : List α) (b : Bool) (p : α × Bool → Bool)
    (hp : ∀ x, p (x, b) = true) : ((a.zip (List.replicate a.length b)).filter p).map Prod.fst = a := by
  induction a with
  | nil => simp
  | cons x xs ih =>
      simp only [List.length_cons, List.replicate_succ, List.zip_cons_cons, List.filter_cons, hp,
        ↓reduceIte, List.map_cons]
      rw [ih]

theorem filter_zip_replicate_nil {α : Type} (a : List α) (b : Bool) (p : α × Bool → Bool)
    (hp : ∀ x, p (x, b) = false) : (a.zip (List.replicate a.length b)).filter p = [] := by
  induction a with
  | nil => simp
  | cons x xs ih =>
      simp only [List.length_cons, List.replicate_succ, List.zip_cons_cons, List.filter_cons, hp]
      simpa using ih

theorem maskIn_block (v₁ L v₂ : List (C × Nat)) :
    maskIn (v₁ ++ L ++ v₂) (blockMask v₁.length L.length v₂.length) = L := by
  unfold maskIn blockMask
  rw [zip_append_eq _ _ _ _ (by simp), zip_append_eq _ _ _ _ (by simp)]
  simp only [List.filter_append, List.map_append]
  rw [filter_zip_replicate_nil v₁ false _ (by simp), filter_zip_replicate L true _ (by simp),
    filter_zip_replicate_nil v₂ false _ (by simp)]
  simp

theorem maskOut_block (v₁ L v₂ : List (C × Nat)) :
    maskOut (v₁ ++ L ++ v₂) (blockMask v₁.length L.length v₂.length) = v₁ ++ v₂ := by
  unfold maskOut blockMask
  rw [zip_append_eq _ _ _ _ (by simp), zip_append_eq _ _ _ _ (by simp)]
  simp only [List.filter_append, List.map_append]
  rw [filter_zip_replicate v₁ false _ (by simp), filter_zip_replicate_nil L true _ (by simp),
    filter_zip_replicate v₂ false _ (by simp)]
  simp

/-- The residue loop computes the residue of the sum. -/
theorem residueLoop_eq (r : Nat) (X : C) :
    ∀ (out : List (C × Nat)) (start : Nat),
      residueLoop r X start out = (start + ((out.filter (fun e => e.1 = X)).map Prod.snd).sum) % r
  | [], start => by simp [residueLoop]
  | e :: out, start => by
      have ih := residueLoop_eq r X out
      unfold residueLoop at ih ⊢
      simp only [List.foldl_cons]
      by_cases he : e.1 = X
      · simp only [he, ↓reduceIte, decide_true, List.filter_cons_of_pos, List.map_cons,
          List.sum_cons]
        have h1 := ih ((start % r + e.2 % r) % r)
        rw [Nat.mod_mod] at h1
        rw [h1, ← Nat.add_mod, Nat.mod_add_mod, Nat.add_assoc]
      · simp only [he, ↓reduceIte, decide_false, Bool.false_eq_true, not_false_eq_true,
          List.filter_cons_of_neg]
        have h1 := ih start
        exact h1

theorem count_ofEntries_eq_sum (l : List (C × Nat)) (X : C) :
    (ofEntries l).count X = ((l.filter (fun e => e.1 = X)).map Prod.snd).sum := by
  induction l with
  | nil => simp [ofEntries]
  | cons e l ih =>
      have : ofEntries (e :: l) = Multiset.replicate e.2 e.1 + ofEntries l := by
        simp [ofEntries]
      rw [this, Multiset.count_add, ih, Multiset.count_replicate]
      by_cases he : e.1 = X
      · simp [he]
      · simp only [he, decide_false, Bool.false_eq_true, not_false_eq_true,
          List.filter_cons_of_neg]
        have : X ≠ e.1 := fun h => he h.symm
        simp [this]

theorem refoldCount_block (v₁ L v₂ : List (C × Nat)) (X : C) (k : Nat) :
    refoldCount (v₁ ++ L ++ v₂) ⟨X, k, L⟩ =
      (((v₁ ++ v₂).filter (fun e => e.1 = X)).map Prod.snd).sum + k := by
  unfold refoldCount
  simp only
  rw [count_ofEntries_eq_sum, count_ofEntries_eq_sum]
  simp only [List.filter_append, List.map_append, List.sum_append]
  omega

theorem any_present_iff (v : List (C × Nat)) (X c : C) :
    (decide (c = X) || v.any (fun e => decide (e.1 = c))) = decide (c ∈ X :: v.map Prod.fst) := by
  by_cases h : c = X
  · simp [h]
  · rw [Bool.eq_iff_iff]
    simp only [h, decide_false, Bool.false_or, List.mem_cons, false_or, List.mem_map,
      List.any_eq_true, decide_eq_true_eq]

theorem optAny_iff (o : Option C) (p : C → Bool) : o.any p = true ↔ ∃ y, o = some y ∧ p y = true := by
  cases o <;> simp

theorem anyMatch_iff (inv : C → Option C) (S : List C) (p : C → Prop) [DecidablePred p] :
    (S.any (fun x => match inv x with
      | none => false
      | some y => decide (p y))) = true ↔ ∃ x ∈ S, ∃ y, inv x = some y ∧ p y := by
  simp only [List.any_eq_true]
  constructor
  · rintro ⟨x, hx, h⟩
    cases hix : inv x with
    | none => simp [hix] at h
    | some y => simp only [hix, decide_eq_true_eq] at h; exact ⟨x, hx, y, hix, h⟩
  · rintro ⟨x, hx, y, hy, h⟩
    exact ⟨x, hx, by simp [hy, h]⟩

/-- The model's inverse clause, as a proposition. -/
theorem anyMatchB_iff (inv : C → Option C) (S : List C) (q : C → Bool) :
    (S.any (fun x => match inv x with
      | none => false
      | some y => q y)) = true ↔ ∃ x ∈ S, ∃ y, inv x = some y ∧ q y = true := by
  simp only [List.any_eq_true]
  constructor
  · rintro ⟨x, hx, h⟩
    cases hix : inv x with
    | none => simp [hix] at h
    | some y => simp only [hix] at h; exact ⟨x, hx, y, hix, h⟩
  · rintro ⟨x, hx, y, hy, h⟩
    exact ⟨x, hx, by simp [hy, h]⟩

theorem invModel_iff (inv : C → Option C) (v : List (C × Nat)) (l : LeafL) :
    ((l.touched.any (fun x => match inv x with
        | none => false
        | some y => decide (y ∈ presentL v l))) ||
      (presentL v l).any (fun y => match inv y with
        | none => false
        | some z => decide (z ∈ l.touched))) = true ↔
      (∃ x ∈ l.touched, ∃ y, inv x = some y ∧ y ∈ presentL v l) ∨
        (∃ y ∈ presentL v l, ∃ z, inv y = some z ∧ z ∈ l.touched) := by
  rw [Bool.or_eq_true, anyMatch_iff, anyMatch_iff]

/-- The engine's inverse loops (`flatten.rs:524-540`), as a proposition. -/
theorem invEng_iff (inv : C → Option C) (v L : List (C × Nat)) (X : C) :
    ((inv X).any (fun y => (decide (y = X) || v.any (fun e => decide (e.1 = y))) ||
        (decide (y = X) || L.any (fun e => decide (e.1 = y)))) ||
      L.any (fun e => (inv e.1).any (fun y => decide (y = X) || v.any (fun e => decide (e.1 = y)))) ||
      v.any (fun e => (inv e.1).any (fun z => decide (z = X) || L.any (fun e => decide (e.1 = z))))) =
        true ↔
      (∃ y, inv X = some y ∧ (y ∈ X :: v.map Prod.fst ∨ y ∈ X :: L.map Prod.fst)) ∨
        (∃ c ∈ L.map Prod.fst, ∃ y, inv c = some y ∧ y ∈ X :: v.map Prod.fst) ∨
        (∃ c ∈ v.map Prod.fst, ∃ z, inv c = some z ∧ z ∈ X :: L.map Prod.fst) := by
  simp only [Bool.or_eq_true, optAny_iff, any_present_iff, decide_eq_true_eq, List.any_eq_true,
    List.mem_map]
  constructor
  · rintro ((⟨y, hy, h⟩ | ⟨e, he, y, hy, h⟩) | ⟨e, he, z, hz, h⟩)
    · exact Or.inl ⟨y, hy, h⟩
    · exact Or.inr (Or.inl ⟨e.1, ⟨e, he, rfl⟩, y, hy, h⟩)
    · exact Or.inr (Or.inr ⟨e.1, ⟨e, he, rfl⟩, z, hz, h⟩)
  · rintro (⟨y, hy, h⟩ | ⟨c, ⟨e, he, rfl⟩, y, hy, h⟩ | ⟨c, ⟨e, he, rfl⟩, z, hz, h⟩)
    · exact Or.inl (Or.inl ⟨y, hy, h⟩)
    · exact Or.inl (Or.inr ⟨e, he, y, hy, h⟩)
    · exact Or.inr ⟨e, he, z, hz, h⟩

/-- The two readings of "some cancel pair between the touched and the
present classes" agree when the leaf's classes are present. -/
theorem inv_equiv (inv : C → Option C) (X : C) (Lc Vc : List C) (_hsub : ∀ c ∈ Lc, c ∈ Vc) :
    ((∃ y, inv X = some y ∧ (y ∈ X :: Vc ∨ y ∈ X :: Lc)) ∨
        (∃ c ∈ Lc, ∃ y, inv c = some y ∧ y ∈ X :: Vc) ∨
        (∃ c ∈ Vc, ∃ z, inv c = some z ∧ z ∈ X :: Lc)) ↔
      ((∃ x ∈ X :: Lc, ∃ y, inv x = some y ∧ y ∈ X :: Vc) ∨
        (∃ y ∈ X :: Vc, ∃ z, inv y = some z ∧ z ∈ X :: Lc)) := by
  constructor
  · rintro (⟨y, hy, h | h⟩ | ⟨c, hc, y, hy, h⟩ | ⟨c, hc, z, hz, h⟩)
    · exact Or.inl ⟨X, List.mem_cons_self .., y, hy, h⟩
    · exact Or.inr ⟨X, List.mem_cons_self .., y, hy, h⟩
    · exact Or.inl ⟨c, List.mem_cons_of_mem _ hc, y, hy, h⟩
    · exact Or.inr ⟨c, List.mem_cons_of_mem _ hc, z, hz, h⟩
  · rintro (⟨x, hx, y, hy, h⟩ | ⟨y, hy, z, hz, h⟩)
    · rcases List.mem_cons.1 hx with rfl | hx
      · exact Or.inl ⟨y, hy, Or.inl h⟩
      · exact Or.inr (Or.inl ⟨x, hx, y, hy, h⟩)
    · rcases List.mem_cons.1 hy with rfl | hy
      · exact Or.inl ⟨z, hz, Or.inr h⟩
      · exact Or.inr (Or.inr ⟨y, hy, z, hz, h⟩)

/-- **The engine's flag is the model's flag** on every leaf block:
`nonInertEng` on the raw view `v₁ ++ L ++ v₂` with the block's mask equals
`nonInertB` on the leaf `⟨X, k, L⟩`. -/
theorem nonInertEng_eq (κ : FlatKind) (laws : Laws) (v₁ L v₂ : List (C × Nat)) (X : C) (k : Nat) :
    nonInertEng κ laws (v₁ ++ L ++ v₂) (blockMask v₁.length L.length v₂.length) X k =
      nonInertB κ laws (v₁ ++ L ++ v₂) ⟨X, k, L⟩ := by
  unfold nonInertEng
  simp only [maskIn_block, maskOut_block]
  by_cases hu : laws.unit = some X
  · cases κ <;> simp [nonInertB, nonInertAC, hu]
  · simp only [hu, ↓reduceIte]
    cases κ with
    | assoc =>
        simp [nonInertB, hu, LeafL.g, List.all_map]
        rfl
    | aci => simp [nonInertB, hu]
    | ac =>
        simp only [nonInertB, nonInertAC, hu, decide_false, Bool.false_or]
        congr 1
        · rcases laws.nilpotent with _ | r
          · rfl
          · simp only
            rw [residueLoop_eq, refoldCount_block, Nat.add_comm k]
        · rcases laws.inv with _ | inv
          · rfl
          · simp only
            rw [Bool.eq_iff_iff, invEng_iff]
            simp only [LeafL.touched, LeafL.g, presentL]
            rw [inv_equiv inv X (L.map Prod.fst) ((v₁ ++ L ++ v₂).map Prod.fst)
              (fun c hc => by simp only [List.map_append, List.mem_append]; exact Or.inl (Or.inr hc))]
            simp only [Bool.or_eq_true, List.any_eq_true]
            constructor
            · rintro (⟨x, hx, y, hy, h⟩ | ⟨y, hy, z, hz, h⟩)
              · left; exact ⟨x, hx, by rw [hy]; exact decide_eq_true h⟩
              · right; exact ⟨y, hy, by rw [hz]; exact decide_eq_true h⟩
            · rintro (⟨x, hx, h⟩ | ⟨y, hy, h⟩)
              · left
                revert h
                cases hix : inv x with
                | none => simp
                | some y => intro h; exact ⟨x, hx, y, hix, of_decide_eq_true h⟩
              · right
                revert h
                cases hiy : inv y with
                | none => simp
                | some z => intro h; exact ⟨y, hy, z, hiy, of_decide_eq_true h⟩

/-! ## The walk's pruning -/

/-- `may_be_non_inert` (`flatten.rs:552-569`): the unit test and the
sequence test read the leaf only; on a multiset under `:nilpotent` or
`:inverse` every leaf may be non-inert. -/
def mayNonInert (κ : FlatKind) (laws : Laws) (l : LeafL) : Bool :=
  decide (laws.unit = some l.X) ||
    match κ with
    | .assoc => l.g.all (fun c => decide (laws.unit = some c))
    | .aci => false
    | .ac => laws.nilpotent.isSome || laws.inv.isSome

/-- The walk keeps a leaf when it closes (`flatten.rs:793-801`): a takeable
direct element (`hits > 0`), a takeable opened class on a multiset, or
`may_be_non_inert`. -/
def keepLeaf (κ : FlatKind) (T : C → Bool) (laws : Laws) (l : LeafL) : Bool :=
  l.g.any T || (mergeOnClose κ && T l.X) || mayNonInert κ laws l

/-- The enumeration as the pruned walk produces it: the records of the trees
whose every leaf the walk keeps. -/
def enumeratePrunedE (T : C → Bool) (ctx : Ctx) (laws : Laws) (n : Node) :
    List (List (C × Nat) × DemandL) :=
  enumerateFromL ((rawRecordsL ctx laws n).filter
    (fun r => r.2.all (fun lf => keepLeaf ctx.κ T laws lf.1)))

/-- The flag implies `may_be_non_inert`: the walk never prunes a leaf the
demand would accept through its flag. -/
theorem nonInertB_imp_mayNonInert {κ : FlatKind} {laws : Laws} {v : List (C × Nat)} {l : LeafL}
    (h : nonInertB κ laws v l = true) : mayNonInert κ laws l = true := by
  cases κ with
  | assoc => simpa [nonInertB, mayNonInert] using h
  | aci => simpa [nonInertB, mayNonInert] using h
  | ac =>
      simp only [nonInertB, nonInertAC, Bool.or_eq_true, decide_eq_true_eq] at h
      simp only [mayNonInert, Bool.or_eq_true, decide_eq_true_eq, Option.isSome_iff_ne_none,
        ne_eq]
      rcases h with (h | h) | h
      · exact Or.inl h
      · right; left
        intro hn; rw [hn] at h; simp at h
      · right; right
        intro hn; rw [hn] at h; simp at h

theorem keepLeaf_of_okE {κ : FlatKind} {T : C → Bool} {laws : Laws} {v : List (C × Nat)}
    {l : LeafL} {taken : List C} (hT : ∀ c ∈ taken, T c = true)
    (h : LeafF.okE κ taken (l, nonInertB κ laws v l)) : keepLeaf κ T laws l = true := by
  unfold keepLeaf
  simp only [Bool.or_eq_true, Bool.and_eq_true, List.any_eq_true]
  rcases h with ⟨hm, hX⟩ | ⟨c, hc, ht⟩ | hf
  · exact Or.inl (Or.inr ⟨hm, hT _ hX⟩)
  · exact Or.inl (Or.inl ⟨c, hc, hT c ht⟩)
  · exact Or.inr (nonInertB_imp_mayNonInert hf)

theorem mem_rawRecordsL_flag {ctx : Ctx} {laws : Laws} {n : Node} {r : RecL}
    (h : r ∈ rawRecordsL ctx laws n) :
    ∃ v ls o, RawViewL ctx n v ls o ∧ normalize ctx.κ laws v = .node r.1 ∧
      r.2 = flagLeaves ctx.κ laws v ls := by
  obtain ⟨v, ls, o, hv, hn, he⟩ := mem_rawRecordsL.1 (show (r.1, r.2) ∈ _ from h)
  exact ⟨v, ls, o, hv, hn, he⟩

/-- **Pruning is match-preserving** (spec §2.3 for the engine's predicate):
for every `taken` inside the takeable set, a view accepts `taken` through
the pruned enumeration iff it does through the full one. -/
theorem prune_engine (T : C → Bool) (ctx : Ctx) (laws : Laws) (n : Node)
    (w : List (C × Nat)) (taken : List C) (hT : ∀ c ∈ taken, T c = true) :
    (∃ d, (w, d) ∈ enumeratePrunedE T ctx laws n ∧ d.acceptsE ctx.κ taken) ↔
      (∃ d, (w, d) ∈ enumerateL ctx laws n ∧ d.acceptsE ctx.κ taken) := by
  have key : ∀ recs : List RecL,
      (∃ d, (w, d) ∈ enumerateFromL recs ∧ d.acceptsE ctx.κ taken) ↔
        (demandOfL recs w).acceptsE ctx.κ taken := by
    intro recs
    constructor
    · rintro ⟨d, hd, hacc⟩
      obtain ⟨-, rfl⟩ := mem_enumerateFromL.1 hd
      exact hacc
    · intro hacc
      obtain ⟨ls, hr, -⟩ := acceptsE_demandOfL.1 hacc
      unfold altsOfL at hr
      obtain ⟨r, hr', -⟩ := List.mem_map.1 hr
      have hw := (List.mem_filter.1 hr').2
      simp only [decide_eq_true_eq] at hw
      exact ⟨_, mem_enumerateFromL.2 ⟨⟨r.2, by rw [← hw]; exact (List.mem_filter.1 hr').1⟩, rfl⟩,
        hacc⟩
  unfold enumeratePrunedE enumerateL
  rw [key, key, acceptsE_demandOfL, acceptsE_demandOfL]
  unfold altsOfL
  simp only [List.mem_map, List.mem_filter]
  constructor
  · rintro ⟨ls, ⟨r, ⟨⟨hr, -⟩, hw⟩, rfl⟩, hall⟩
    exact ⟨r.2, ⟨r, ⟨hr, hw⟩, rfl⟩, hall⟩
  · rintro ⟨ls, ⟨r, ⟨hr, hw⟩, rfl⟩, hall⟩
    refine ⟨r.2, ⟨r, ⟨⟨hr, ?_⟩, hw⟩, rfl⟩, hall⟩
    obtain ⟨v, ls', o, -, -, he⟩ := mem_rawRecordsL_flag hr
    simp only [List.all_eq_true]
    intro lf hlf
    rw [he] at hlf hall
    obtain ⟨l, -, rfl⟩ := List.mem_map.1 hlf
    exact keepLeaf_of_okE hT (hall _ hlf)

end Semper.EMatch.Flatten
