import SemperProofs.EMatch.Flatten.RegroupSkipDefs
import SemperProofs.EMatch.Flatten.RegroupChain

/-!
# `:flatten`: the engine's regrouping skips lose no match

`regroupAllSkip` (`RegroupSkipDefs.lean`) is the engine's regrouping loop,
view by view, largest first, with its three skips. This file proves that,
for any laws, kind and fold direction, it accepts exactly the matches of
`regroupAll` on every view, after the item limit (`regroupSkip_iff`):

* regrouping makes a view strictly smaller under any laws
  (`regroupRec_shrink`), so the full enumeration's records are the records
  reachable from the walk's by regroupings (`mem_regroupLevels_iff_reach`),
  and a view the engine regroups never becomes a target again
  (`addTarget_spec`: the engine asserts it);
* `Cov c b`: the record `c` admits every match `b` admits and needs no more
  classes (`Cov.accepts`, `Cov.length`): each leaf of `c` has a leaf of `b`
  with the same opened class, flag and classes, and `c` needs a subset of
  the classes `b` needs. An unconditional record covers every record of its
  view (`cov_uncond`), equal signatures cover each other (`cov_of_same`),
  and regrouping both records the same way preserves the cover
  (`Cov.derive`);
* the loop's invariant (`SkipInv`): every record is reachable, and every
  regrouped view is *closed*: each regrouping of each of its records is
  covered by a record of the target. A skipped record is covered when it is
  skipped: by the target's unconditional record, by the regrouping of the
  source's unconditional record, or by the target's record of the same
  signature;
* the loop ends with every view regrouped (`run_finished`), so every
  reachable record is covered (`cover_of_reach`), and covered records pass
  the item limit and the demand rule whenever the records they cover do.
-/

namespace Semper.EMatch.Flatten

open Semper.EMatch

/-! ## Regrouping shrinks a view, under any laws -/

/-- The views regrouping reads: positive counts, and distinct classes for a
multiset or a set (normal forms are, `viewGood_normalize`). -/
def ViewGood (κ : FlatKind) (w : List (C × Nat)) : Prop :=
  (∀ e ∈ w, 0 < e.2) ∧ (κ ≠ .assoc → (w.map Prod.fst).Nodup)

theorem viewSize_cons (e : C × Nat) (l : List (C × Nat)) :
    viewSize (e :: l) = e.2 + viewSize l := by
  simp [viewSize]

theorem viewSize_filter_le (p : C × Nat → Bool) :
    ∀ l : List (C × Nat), viewSize (l.filter p) ≤ viewSize l
  | [] => le_refl _
  | e :: l => by
      have := viewSize_filter_le p l
      rw [List.filter_cons]
      split <;> simp only [viewSize_cons] <;> omega

theorem viewSize_set_le :
    ∀ {l : List (C × Nat)} {i : Nat} {a : C × Nat},
      (∀ e, l[i]? = some e → a.2 ≤ e.2) → viewSize (l.set i a) ≤ viewSize l
  | [], _, _, _ => by simp
  | x :: l, 0, a, h => by
      have := h x rfl
      simp only [List.set_cons_zero, viewSize_cons]
      omega
  | x :: l, i + 1, a, h => by
      have := viewSize_set_le (l := l) (i := i) (a := a) (fun e he => h e (by simpa using he))
      simp only [List.set_cons_succ, viewSize_cons]
      omega

theorem viewSize_cancelAt_le (inv : C → Option C) (l : List (C × Nat)) (i : Nat) :
    viewSize (cancelAt inv l i) ≤ viewSize l := by
  unfold cancelAt
  split
  · exact le_refl _
  · rename_i x xc hi
    split
    · exact le_refl _
    · split
      · exact le_refl _
      · rename_i y _
        split
        · split
          · exact viewSize_set_le (fun e he => by
              rw [hi] at he; cases he; exact Nat.mod_le _ _)
          · exact le_refl _
        · split
          · exact le_refl _
          · rename_i j _
            split
            · exact le_refl _
            · rename_i y' yc hj
              by_cases hij : j = i
              · subst hij
                rw [List.set_set]
                refine viewSize_set_le (fun e he => ?_)
                rw [hj] at he; cases he
                exact Nat.sub_le _ _
              · refine le_trans (viewSize_set_le (fun e he => ?_)) (viewSize_set_le (fun e he => ?_))
                · rw [List.getElem?_set_ne (Ne.symm hij), hj] at he; cases he
                  exact Nat.sub_le _ _
                · rw [hi] at he; cases he
                  exact Nat.sub_le _ _

theorem viewSize_cancelSteps_le (inv : C → Option C) (l : List (C × Nat)) :
    ∀ n, viewSize (cancelSteps inv l n) ≤ viewSize l
  | 0 => le_refl _
  | n + 1 => le_trans (viewSize_cancelAt_le inv _ n) (viewSize_cancelSteps_le inv l n)

theorem viewSize_cancel_le (inv : C → Option C) (l : List (C × Nat)) :
    viewSize (cancel inv l) ≤ viewSize l :=
  le_trans (viewSize_filter_le _ _) (viewSize_cancelSteps_le inv l _)

theorem viewSize_mapMod_le (r : Nat) :
    ∀ l : List (C × Nat), viewSize (l.map (fun e => (e.1, e.2 % r))) ≤ viewSize l
  | [] => le_refl _
  | e :: l => by
      have := viewSize_mapMod_le r l
      have := Nat.mod_le e.2 r
      simp only [List.map_cons, viewSize_cons]
      omega

theorem viewSize_clamp_le (r : Option Nat) (l : List (C × Nat)) :
    viewSize (clamp r l) ≤ viewSize l := by
  cases r with
  | none => exact le_refl _
  | some r => exact le_trans (viewSize_filter_le _ _) (viewSize_mapMod_le r l)

theorem viewSize_dropUnit_le (u : Option C) (l : List (C × Nat)) :
    viewSize (dropUnit u l) ≤ viewSize l := by
  cases u with
  | none => exact le_refl _
  | some u => exact viewSize_filter_le _ _

theorem viewSize_coalesce (v : List (C × Nat)) : viewSize (coalesce v) = viewSize v := by
  unfold coalesce
  rw [viewSize_entries, viewSize_eq_card]

theorem viewSize_dedupAci_le {v : List (C × Nat)} (h : ∀ e ∈ v, 0 < e.2) :
    viewSize (dedupAci v) ≤ viewSize v := by
  rw [viewSize_ones (dedupAci_ones v)]
  have hlen : (dedupAci v).length = (v.map Prod.fst).toFinset.card := by simp [dedupAci]
  rw [hlen]
  refine le_trans (List.toFinset_card_le _) ?_
  rw [List.length_map]
  exact viewSize_pos_ge h

theorem viewSize_normalizeList_le {κ : FlatKind} (laws : Laws) {v : List (C × Nat)}
    (h : κ = .aci → ∀ e ∈ v, 0 < e.2) : viewSize (normalizeList κ laws v) ≤ viewSize v := by
  obtain ⟨u, r, inv⟩ := laws
  cases κ with
  | assoc => exact viewSize_dropUnit_le u v
  | aci => exact le_trans (viewSize_dropUnit_le u _) (viewSize_dedupAci_le (h rfl))
  | ac =>
      have h1 : viewSize (clamp r (dropUnit u (coalesce v))) ≤ viewSize v := by
        refine le_trans (viewSize_clamp_le r _) (le_trans (viewSize_dropUnit_le u _) ?_)
        rw [viewSize_coalesce]
      cases inv with
      | none => exact h1
      | some inv => exact le_trans (viewSize_cancel_le inv _) h1

theorem normalize_node_eq {κ : FlatKind} {laws : Laws} {v w : List (C × Nat)}
    (h : normalize κ laws v = .node w) : w = normalizeList κ laws v := by
  unfold normalize at h
  exact ((classify_node_iff _ _ _).1 h).1.symm

theorem dropUnit_sublist (u : Option C) (l : List (C × Nat)) : (dropUnit u l).Sublist l := by
  cases u with
  | none => exact List.Sublist.refl _
  | some u => exact List.filter_sublist

/-- A normal form is a good view (for `:assoc`, of a raw view with positive
counts). -/
theorem viewGood_normalize {κ : FlatKind} {laws : Laws} {v w : List (C × Nat)}
    (h : normalize κ laws v = .node w) (hpos : κ = .assoc → ∀ e ∈ v, 0 < e.2) :
    ViewGood κ w := by
  cases κ with
  | ac =>
      have hc := normalize_ac_canonical h
      exact ⟨hc.2, fun _ => hc.nodup⟩
  | aci =>
      have hc := normalize_aci_canonical h
      exact ⟨fun e he => by rw [hc.2 e he]; exact Nat.one_pos,
        fun _ => hc.1.imp (fun h => Nat.ne_of_lt h)⟩
  | assoc =>
      have hw := normalize_node_eq h
      refine ⟨fun e he => ?_, fun h => absurd rfl h⟩
      rw [hw] at he
      exact hpos rfl e ((dropUnit_sublist _ _).subset he)

/-- A fit of a group is strictly smaller than the view, with positive counts. -/
theorem fitsR_shrink {κ : FlatKind} {dir : Dir} {view : List (C × Nat)} {g : C}
    {grp raw : List (C × Nat)} (hv : ViewGood κ view) (h : raw ∈ fitsR κ dir view g grp) :
    viewSize raw < viewSize view ∧ ∀ e ∈ raw, 0 < e.2 := by
  cases κ with
  | assoc =>
      obtain ⟨h2, -, p, -, hrun, rfl⟩ := fitsR_assoc h
      have hlen := congrArg List.length hrun
      simp only [List.length_map, List.length_take, List.length_drop] at hlen
      have hsplit : view = view.take p ++ ((view.drop p).take grp.length ++
          view.drop (p + grp.length)) := by
        rw [← List.drop_drop, List.take_append_drop, List.take_append_drop]
      have hmid : grp.length ≤ viewSize ((view.drop p).take grp.length) := by
        have := viewSize_pos_ge (w := (view.drop p).take grp.length)
          (fun e he => hv.1 e (List.mem_of_mem_drop (List.mem_of_mem_take he)))
        simp only [List.length_take, List.length_drop] at this
        omega
      constructor
      · conv => rhs; rw [hsplit]
        simp only [viewSize_append, viewSize_cons]
        omega
      · intro e he
        rcases List.mem_append.1 he with he | he
        · exact hv.1 e (List.mem_of_mem_take he)
        · rcases List.mem_cons.1 he with rfl | he
          · exact Nat.one_pos
          · exact hv.1 e (List.mem_of_mem_drop he)
  | ac =>
      obtain ⟨htwo, -, v, hs, rfl⟩ := fitsR_ms (by decide) h
      simp only [groupNorm] at htwo hs
      have hsum := subEntries_spec _ _ _ (hv.2 (by decide)) hs
      have hc := congrArg Multiset.card hsum
      rw [Multiset.card_add, ← viewSize_eq_card, ← viewSize_eq_card, ← viewSize_eq_card,
        viewSize_coalesce] at hc
      have h2 := two_card_ac htwo
      rw [← viewSize_eq_card] at h2
      refine ⟨?_, fun e he => ?_⟩
      · have h1 : viewSize [(g, 1)] = 1 := rfl
        rw [viewSize_append, h1]; omega
      · rcases List.mem_append.1 he with he | he
        · exact subEntries_pos _ _ _ hs e he
        · simp at he; rw [he]; exact Nat.one_pos
  | aci =>
      obtain ⟨htwo, -, v, hs, rfl⟩ := fitsR_ms (by decide) h
      simp only [groupNorm] at htwo hs
      have hsum := subEntries_spec _ _ _ (hv.2 (by decide)) hs
      have hc := congrArg Multiset.card hsum
      rw [Multiset.card_add, ← viewSize_eq_card, ← viewSize_eq_card, ← viewSize_eq_card,
        viewSize_ones (dedupAci_ones grp)] at hc
      have h2 : 2 ≤ (dedupAci grp).length := by
        rcases Bool.or_eq_true_iff.1 htwo with h | h
        · exact of_decide_eq_true h
        · cases hh : (dedupAci grp).head? with
          | none => rw [hh] at h; simp at h
          | some e =>
              rw [hh] at h
              simp only [Option.map_some, Option.getD_some, decide_eq_true_eq] at h
              rw [dedupAci_ones grp e (List.mem_of_mem_head? hh)] at h
              omega
      refine ⟨?_, fun e he => ?_⟩
      · have h1 : viewSize [(g, 1)] = 1 := rfl
        rw [viewSize_append, h1]; omega
      · rcases List.mem_append.1 he with he | he
        · exact subEntries_pos _ _ _ hs e he
        · simp at he; rw [he]; exact Nat.one_pos

/-- **Regrouping shrinks a view, under any laws**: a regrouping of a record
with a good view has a good view, strictly smaller. -/
theorem regroupRec_shrink {ctx : Ctx} {dir : Dir} {laws : Laws} {r r' : RecR}
    (hv : ViewGood ctx.κ r.1) (h : r' ∈ regroupRec ctx dir laws r) :
    ViewGood ctx.κ r'.1 ∧ viewSize r'.1 < viewSize r.1 := by
  obtain ⟨g, grp, raw, -, hraw, hn, -, -⟩ := mem_regroupRec h
  obtain ⟨hlt, hpos⟩ := fitsR_shrink hv hraw
  refine ⟨viewGood_normalize hn (fun _ => hpos), ?_⟩
  rw [normalize_node_eq hn]
  exact lt_of_le_of_lt (viewSize_normalizeList_le laws (fun _ => hpos)) hlt

/-! ## The full enumeration is the reachable records -/

/-- One regrouping. -/
def RStep (ctx : Ctx) (dir : Dir) (laws : Laws) (a b : RecR) : Prop :=
  b ∈ regroupRec ctx dir laws a

/-- The records reachable from `base` by regroupings. -/
def Reach (ctx : Ctx) (dir : Dir) (laws : Laws) (base : List RecR) (r : RecR) : Prop :=
  ∃ r₀ ∈ base, Relation.ReflTransGen (RStep ctx dir laws) r₀ r

/-- The walk's records as regrouping reads them: good views, no class needed
twice. -/
def BaseGood (κ : FlatKind) (base : List RecR) : Prop :=
  ∀ r ∈ base, ViewGood κ r.1 ∧ r.2.2.Nodup

theorem needsAfter_nodup (g : C) (grp ws : List C) {ns : List C} (h : ns.Nodup) :
    (needsAfter g grp ws ns).Nodup := by
  unfold needsAfter
  have hf : (ns.filter (fun c => decide (c ∉ grp))).Nodup := h.filter _
  dsimp only
  refine List.Nodup.filter _ ?_
  split
  · exact hf
  · rename_i hg
    refine List.nodup_append.2 ⟨hf, List.nodup_singleton g, fun a ha b hb => ?_⟩
    rw [List.mem_singleton] at hb
    subst hb
    rintro rfl
    exact hg ha

theorem rstep_good {ctx : Ctx} {dir : Dir} {laws : Laws} {a b : RecR}
    (h : RStep ctx dir laws a b) (ha : ViewGood ctx.κ a.1 ∧ a.2.2.Nodup) :
    ViewGood ctx.κ b.1 ∧ b.2.2.Nodup := by
  refine ⟨(regroupRec_shrink ha.1 h).1, ?_⟩
  obtain ⟨g, grp, -, -, -, -, -, hn⟩ := mem_regroupRec h
  rw [hn]
  exact needsAfter_nodup _ _ _ ha.2

theorem reach_good {ctx : Ctx} {dir : Dir} {laws : Laws} {base : List RecR}
    (hb : BaseGood ctx.κ base) {r : RecR} (h : Reach ctx dir laws base r) :
    ViewGood ctx.κ r.1 ∧ r.2.2.Nodup := by
  obtain ⟨r₀, h₀, hch⟩ := h
  induction hch with
  | refl => exact hb r₀ h₀
  | tail _ hs ih => exact rstep_good hs ih

theorem reach_step {ctx : Ctx} {dir : Dir} {laws : Laws} {base : List RecR} {a b : RecR}
    (ha : Reach ctx dir laws base a) (h : b ∈ regroupRec ctx dir laws a) :
    Reach ctx dir laws base b := by
  obtain ⟨r₀, h₀, hch⟩ := ha
  exact ⟨r₀, h₀, Relation.ReflTransGen.tail hch h⟩

theorem mem_levels_of_chain {ctx : Ctx} {dir : Dir} {laws : Laws} {r₀ r : RecR}
    (hok : ViewGood ctx.κ r₀.1) (h : Relation.ReflTransGen (RStep ctx dir laws) r₀ r) :
    r ∈ regroupLevels ctx dir laws (viewSize r₀.1) [r₀] := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact mem_regroupLevels_of_mem ctx dir laws _ (List.mem_singleton_self _)
  | head hs _ ih =>
      obtain ⟨hok', hlt⟩ := regroupRec_shrink hok hs
      have := mem_regroupLevels_succ hs (ih hok')
      exact regroupLevels_fuel_mono ctx dir laws (by omega) this

theorem chain_of_mem_levels {ctx : Ctx} {dir : Dir} {laws : Laws} :
    ∀ (F : Nat) {r₀ r : RecR}, r ∈ regroupLevels ctx dir laws F [r₀] →
      Relation.ReflTransGen (RStep ctx dir laws) r₀ r
  | 0, r₀, r, h => by
      simp only [regroupLevels, List.mem_singleton] at h
      subst h; exact Relation.ReflTransGen.refl
  | F + 1, r₀, r, h => by
      simp only [regroupLevels, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        List.mem_append, List.mem_singleton] at h
      rcases h with rfl | h
      · exact Relation.ReflTransGen.refl
      · obtain ⟨r₁, h₁, h⟩ := (mem_regroupLevels_iff ctx dir laws F _ r).1 h
        exact Relation.ReflTransGen.head (mem_dedupH.1 h₁) (chain_of_mem_levels F h)

/-- **The full enumeration is the reachable records**, under any laws, with
as many levels as the largest view of the walk's records. -/
theorem mem_regroupLevels_iff_reach {ctx : Ctx} {dir : Dir} {laws : Laws} {base : List RecR}
    (hb : BaseGood ctx.κ base) {F : Nat} (hF : ∀ r ∈ base, viewSize r.1 ≤ F) {r : RecR} :
    r ∈ regroupLevels ctx dir laws F base ↔ Reach ctx dir laws base r := by
  rw [mem_regroupLevels_iff]
  constructor
  · rintro ⟨r₀, h₀, h⟩
    exact ⟨r₀, h₀, chain_of_mem_levels F h⟩
  · rintro ⟨r₀, h₀, h⟩
    exact ⟨r₀, h₀, regroupLevels_fuel_mono ctx dir laws (hF r₀ h₀)
      (mem_levels_of_chain (hb r₀ h₀).1 h)⟩

theorem mem_regroupAll_iff_reach {ctx : Ctx} {dir : Dir} {laws : Laws} {base : List RecR}
    (hb : BaseGood ctx.κ base) {r : RecR} :
    r ∈ regroupAll ctx dir laws (regroupFuel base) base ↔ Reach ctx dir laws base r :=
  mem_regroupLevels_iff_reach hb (fun _ h => viewSize_le_regroupFuel h)

/-! ## Covering records -/

/-- Two leaves with the same opened class, flag and classes. -/
def LeafEq (l l' : LeafF) : Prop :=
  l.1.X = l'.1.X ∧ l.2 = l'.2 ∧ ∀ c, c ∈ l.1.g ↔ c ∈ l'.1.g

/-- `c` covers `b`: same view, each leaf of `c` has an equal leaf in `b`, and
`c` needs only classes `b` needs. -/
def Cov (c b : RecR) : Prop :=
  c.1 = b.1 ∧ (∀ l ∈ c.2.1, ∃ l' ∈ b.2.1, LeafEq l l') ∧ ∀ x ∈ c.2.2, x ∈ b.2.2

theorem Cov.refl (b : RecR) : Cov b b :=
  ⟨rfl, fun l hl => ⟨l, hl, rfl, rfl, fun _ => Iff.rfl⟩, fun _ h => h⟩

theorem Cov.trans {a b c : RecR} (h₁ : Cov a b) (h₂ : Cov b c) : Cov a c := by
  refine ⟨h₁.1.trans h₂.1, fun l hl => ?_, fun x hx => h₂.2.2 x (h₁.2.2 x hx)⟩
  obtain ⟨l', hl', e₁⟩ := h₁.2.1 l hl
  obtain ⟨l'', hl'', e₂⟩ := h₂.2.1 l' hl'
  exact ⟨l'', hl'', e₁.1.trans e₂.1, e₁.2.1.trans e₂.2.1,
    fun x => (e₁.2.2 x).trans (e₂.2.2 x)⟩

theorem LeafEq.okE {κ : FlatKind} {taken : List C} {l l' : LeafF} (h : LeafEq l l')
    (hok : l'.okE κ taken) : l.okE κ taken := by
  obtain ⟨hX, hf, hg⟩ := h
  unfold LeafF.okE at hok ⊢
  rw [hX, hf]
  rcases hok with h | ⟨c, hc, ht⟩ | h
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨c, (hg c).2 hc, ht⟩)
  · exact Or.inr (Or.inr h)

theorem LeafEq.okL {taken : List C} {l l' : LeafF} (h : LeafEq l l')
    (hok : l'.okL taken) : l.okL taken := by
  obtain ⟨hX, hf, hg⟩ := h
  unfold LeafF.okL at hok ⊢
  rw [hX, hf]
  rcases hok with h | ⟨c, hc, ht⟩ | h
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨c, (hg c).2 hc, ht⟩)
  · exact Or.inr (Or.inr h)

/-- A covering record passes the engine's demand rule whenever the covered one
does. -/
theorem Cov.accepts {κ : FlatKind} {taken : List C} {c b : RecR} (h : Cov c b)
    (hb : ∀ l ∈ b.alt, l.okE κ taken) : ∀ l ∈ c.alt, l.okE κ taken := by
  intro l hl
  rcases List.mem_append.1 hl with hl | hl
  · obtain ⟨l', hl', he⟩ := h.2.1 l hl
    exact he.okE (hb l' (List.mem_append_left _ hl'))
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hl
    have := hb (needLeaf x) (List.mem_append_right _ (List.mem_map_of_mem (h.2.2 x hx)))
    exact (needLeaf_okE κ taken x).2 ((needLeaf_okE κ taken x).1 this)

/-- A covering record passes the demand rule under laws whenever the covered
one does. -/
theorem Cov.acceptsL {taken : List C} {c b : RecR} (h : Cov c b)
    (hb : ∀ l ∈ b.alt, l.okL taken) : ∀ l ∈ c.alt, l.okL taken := by
  intro l hl
  rcases List.mem_append.1 hl with hl | hl
  · obtain ⟨l', hl', he⟩ := h.2.1 l hl
    exact he.okL (hb l' (List.mem_append_left _ hl'))
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hl
    exact hb (needLeaf x) (List.mem_append_right _ (List.mem_map_of_mem (h.2.2 x hx)))

/-- A covering record needs no more classes: it passes the item limit whenever
the covered one does. -/
theorem Cov.length {c b : RecR} (h : Cov c b) (hc : c.2.2.Nodup) :
    c.2.2.length ≤ b.2.2.length :=
  (hc.subperm h.2.2).length_le

theorem addG_leafEq {g : C} {grp ws : List C} {l l' : LeafF} (h : LeafEq l l') :
    LeafEq (addG g grp ws l) (addG g grp ws l') := by
  obtain ⟨hX, hf, hg⟩ := h
  have hc : (g ∉ l.1.g ∧ l.1.g.any (fun c => decide (c ∈ grp)) = true) ↔
      (g ∉ l'.1.g ∧ l'.1.g.any (fun c => decide (c ∈ grp)) = true) := by
    simp only [List.any_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨h1, c, hc, hc'⟩; exact ⟨fun h => h1 ((hg g).2 h), c, (hg c).1 hc, hc'⟩
    · rintro ⟨h1, c, hc, hc'⟩; exact ⟨fun h => h1 ((hg g).1 h), c, (hg c).2 hc, hc'⟩
  refine ⟨by rw [addG_X, addG_X, hX], ?_, fun x => ?_⟩
  · rw [addG_flag, addG_flag, hf]
    simp only [List.any_eq_true, decide_eq_true_eq] at hc ⊢
    by_cases hw : g ∈ ws
    · simp [hw]
    · simp only [hw, not_false_eq_true, true_and]
      congr 1
      exact decide_eq_decide.2 hc
  unfold addG
  split_ifs with h1 h2 h2
  · simp only [LeafL.g, List.map_append, List.mem_append]
    exact or_congr (hg x) Iff.rfl
  · exact absurd (hc.1 h1) h2
  · exact absurd (hc.2 h2) h1
  · exact hg x

theorem needsAfter_mono {g : C} {grp ws ns ns' : List C} (h : ∀ x ∈ ns, x ∈ ns') :
    ∀ x ∈ needsAfter g grp ws ns, x ∈ needsAfter g grp ws ns' := by
  have mem0 : ∀ {ms : List C} {x : C},
      x ∈ (let ns := ms.filter (fun c => decide (c ∉ grp)); if g ∈ ns then ns else ns ++ [g]) ↔
      (x ∈ ms ∧ x ∉ grp) ∨ x = g := by
    intro ms x
    dsimp only
    split
    · rename_i hg
      simp only [List.mem_filter, decide_eq_true_eq]
      constructor
      · exact Or.inl
      · rintro (h | rfl)
        · exact h
        · simpa using hg
    · simp [List.mem_filter]
  have mem : ∀ {ms : List C} {x : C}, x ∈ needsAfter g grp ws ms ↔
      ((x ∈ ms ∧ x ∉ grp) ∨ x = g) ∧ x ∈ ws := by
    intro ms x
    unfold needsAfter
    rw [List.mem_filter, mem0, decide_eq_true_eq]
  intro x hx
  obtain ⟨hx, hw⟩ := mem.1 hx
  rcases hx with ⟨h1, h2⟩ | rfl
  · exact mem.2 ⟨Or.inl ⟨h x h1, h2⟩, hw⟩
  · exact mem.2 ⟨Or.inr rfl, hw⟩

/-- Regrouping two records the same way preserves the cover. -/
theorem Cov.derive {c b : RecR} (h : Cov c b) (t : View) (g : C) (grp : List C) :
    Cov (deriveRec t g grp c) (deriveRec t g grp b) := by
  refine ⟨rfl, fun l hl => ?_, needsAfter_mono h.2.2⟩
  obtain ⟨l₀, hl₀, rfl⟩ := List.mem_map.1 hl
  obtain ⟨l', hl', he⟩ := h.2.1 l₀ hl₀
  exact ⟨addG g grp (t.map Prod.fst) l', List.mem_map_of_mem hl', addG_leafEq he⟩

/-- An unconditional record covers every record of its view. -/
theorem cov_uncond {u b : RecR} (hu : u.uncond = true) (hv : u.1 = b.1) : Cov u b := by
  simp only [RecR.uncond, Bool.and_eq_true, List.isEmpty_iff] at hu
  refine ⟨hv, fun l hl => ?_, fun x hx => ?_⟩
  · rw [hu.1] at hl; simp at hl
  · rw [hu.2] at hx; simp at hx

theorem mem_mergeSort_le {l : List C} {x : C} :
    x ∈ l.mergeSort (fun a b => decide (a ≤ b)) ↔ x ∈ l :=
  List.mem_mergeSort

/-- A record with the same signature covers. -/
theorem cov_of_same {c d : RecR} (hs : RecSig.same (recSig d) (recSig c) = true)
    (hv : c.1 = d.1) : Cov c d := by
  simp only [RecSig.same, recSig, Bool.and_eq_true, List.isPerm_iff] at hs
  obtain ⟨hl, hn⟩ := hs
  refine ⟨hv, fun l hl' => ?_, fun x hx => hn.symm.subset hx⟩
  obtain ⟨l', hl'', he⟩ := List.mem_map.1 (hl.symm.subset (List.mem_map_of_mem (f := leafSig) hl'))
  simp only [leafSig, Prod.mk.injEq] at he
  exact ⟨l', hl'', he.1.symm, he.2.1.symm, fun x => by
    rw [← mem_mergeSort_le (l := l.1.g), ← he.2.2, mem_mergeSort_le]⟩

/-- A regrouping, as the loop derives it. -/
theorem regroupRec_derive {ctx : Ctx} {dir : Dir} {laws : Laws} {a b : RecR}
    (h : b ∈ regroupRec ctx dir laws a) :
    ∃ g grp raw, (g, grp) ∈ groupsOf ctx ∧ raw ∈ fitsR ctx.κ dir a.1 g grp ∧
      normalize ctx.κ laws raw = .node b.1 ∧ b = deriveRec b.1 g (grp.map Prod.fst) a := by
  obtain ⟨g, grp, raw, hgg, hraw, hn, hl, hneeds⟩ := mem_regroupRec h
  refine ⟨g, grp, raw, hgg, hraw, hn, ?_⟩
  obtain ⟨w, ls, ns⟩ := b
  simp only at hl hneeds
  subst hl hneeds
  rfl

theorem deriveRec_mem {ctx : Ctx} {dir : Dir} {laws : Laws} {c : RecR} {g : C}
    {grp raw : List (C × Nat)} {t : View} (hgg : (g, grp) ∈ groupsOf ctx)
    (hraw : raw ∈ fitsR ctx.κ dir c.1 g grp) (hn : normalize ctx.κ laws raw = .node t) :
    deriveRec t g (grp.map Prod.fst) c ∈ regroupRec ctx dir laws c :=
  regroupRec_of hgg hraw hn

theorem mem_groupsOfEngine {ctx : Ctx} {gg : C × List (C × Nat)} :
    gg ∈ groupsOfEngine ctx ↔ gg ∈ groupsOf ctx := by
  unfold groupsOfEngine groupsOf
  rw [List.mem_dedup]
  simp only [List.mem_map, List.mem_mergeSort]

/-! ## Folds -/

theorem foldl_induct {α β : Type} (f : β → α → β) (I : β → Prop) :
    ∀ (xs : List α) (b : β), I b → (∀ b x, x ∈ xs → I b → I (f b x)) → I (xs.foldl f b)
  | [], _, hb, _ => hb
  | x :: xs, b, hb, h =>
      foldl_induct f I xs (f b x) (h b x (List.mem_cons_self ..) hb)
        (fun b' y hy hb' => h b' y (List.mem_cons_of_mem _ hy) hb')

/-- A property some step of a fold establishes and every step keeps holds at
the end. -/
theorem foldl_establish {α β : Type} {f : β → α → β} {I P : β → Prop} {x₀ : α} :
    ∀ {xs : List α}, x₀ ∈ xs → (∀ b x, x ∈ xs → I b → I (f b x)) →
      (∀ b x, x ∈ xs → I b → P b → P (f b x)) → (∀ b, I b → P (f b x₀)) →
      ∀ b, I b → P (xs.foldl f b)
  | [], hx, _, _, _, _, _ => by simp at hx
  | y :: ys, hx, hI, hP, h0, b, hb => by
      rw [List.foldl_cons]
      have hI' : ∀ b x, x ∈ ys → I b → I (f b x) :=
        fun b x hx hb => hI b x (List.mem_cons_of_mem _ hx) hb
      have hP' : ∀ b x, x ∈ ys → I b → P b → P (f b x) :=
        fun b x hx hb => hP b x (List.mem_cons_of_mem _ hx) hb
      by_cases hy : x₀ = y
      · subst hy
        have := foldl_induct f (fun b => I b ∧ P b) ys (f b x₀)
          ⟨hI b x₀ (List.mem_cons_self ..) hb, h0 b hb⟩
          (fun b x hx hb => ⟨hI' b x hx hb.1, hP' b x hx hb.1 hb.2⟩)
        exact this.2
      · have hx' : x₀ ∈ ys := by
          rcases List.mem_cons.1 hx with h | h
          · exact absurd h hy
          · exact h
        exact foldl_establish hx' hI' hP' h0 (f b y) (hI b y (List.mem_cons_self ..) hb)

/-! ## The loop's invariant -/

section Loop

variable {ctx : Ctx} {dir : Dir} {laws : Laws} {base : List RecR}

/-- The invariant every step keeps: the records are reachable and filed under
their view, a view with records is an entry, a view not entered is not
regrouped, every signature is a record's, the walk's records are kept. -/
structure Core (ctx : Ctx) (dir : Dir) (laws : Laws) (base : List RecR) (st : SkipSt) :
    Prop where
  sound : ∀ w, ∀ r ∈ st.recs w, r.1 = w ∧ Reach ctx dir laws base r
  in_order : ∀ w, st.recs w ≠ [] → w ∈ st.order
  out_done : ∀ w, w ∉ st.order → st.done w = false
  sigs_rec : ∀ w, ∀ s ∈ st.sigs w, ∃ r ∈ st.recs w, recSig r = s
  base_in : ∀ r ∈ base, r ∈ st.recs r.1

/-- Every entry has a record (between two targets). -/
def Filled (st : SkipSt) : Prop := ∀ w ∈ st.order, st.recs w ≠ []

/-- The records and the entries only grow. -/
def Mono (st st' : SkipSt) : Prop :=
  (∀ w, ∀ r ∈ st.recs w, r ∈ st'.recs w) ∧ ∀ w ∈ st.order, w ∈ st'.order

theorem Mono.refl (st : SkipSt) : Mono st st := ⟨fun _ _ h => h, fun _ h => h⟩

theorem Mono.trans {a b c : SkipSt} (h₁ : Mono a b) (h₂ : Mono b c) : Mono a c :=
  ⟨fun w r h => h₂.1 w r (h₁.1 w r h), fun w h => h₂.2 w (h₁.2 w h)⟩

/-- A regrouped view is closed: every regrouping of each of its records is
covered by a record of the target. -/
def Closed (ctx : Ctx) (dir : Dir) (laws : Laws) (st : SkipSt) (v : View) : Prop :=
  ∀ a ∈ st.recs v, ∀ b ∈ regroupRec ctx dir laws a, ∃ c ∈ st.recs b.1, Cov c b

theorem Closed.mono {st st' : SkipSt} {v : View} (h : Closed ctx dir laws st v)
    (hm : Mono st st') (hv : st'.recs v = st.recs v) : Closed ctx dir laws st' v := by
  intro a ha b hb
  rw [hv] at ha
  obtain ⟨c, hc, hcov⟩ := h a ha b hb
  exact ⟨c, hm.1 _ c hc, hcov⟩

theorem Core.sigs_nil {st : SkipSt} (hc : Core ctx dir laws base st) {w : View}
    (hw : w ∉ st.order) : st.sigs w = [] := by
  cases h : st.sigs w with
  | nil => rfl
  | cons s _ =>
      obtain ⟨r, hr, -⟩ := hc.sigs_rec w s (by rw [h]; exact List.mem_cons_self ..)
      exact absurd (hc.in_order w (List.ne_nil_of_mem hr)) hw

/-! ### Adding one derived record -/

theorem addRec_cases (t : View) (st : SkipSt) (d : RecR) :
    (st.addRec t d = st ∧ (st.sigs t).any (RecSig.same (recSig d)) = true) ∨
      st.addRec t d = { st with
        sigs := Function.update st.sigs t (st.sigs t ++ [recSig d])
        recs := Function.update st.recs t (st.recs t ++ [d]) } := by
  unfold SkipSt.addRec
  split
  · exact Or.inl ⟨rfl, by assumption⟩
  · exact Or.inr rfl

theorem addRec_frame (t : View) (st : SkipSt) (d : RecR) :
    (st.addRec t d).order = st.order ∧ (st.addRec t d).done = st.done ∧
      (∀ w, w ≠ t → (st.addRec t d).recs w = st.recs w) ∧ Mono st (st.addRec t d) := by
  rcases addRec_cases t st d with ⟨h, -⟩ | h <;> rw [h]
  · exact ⟨rfl, rfl, fun _ _ => rfl, Mono.refl _⟩
  · refine ⟨rfl, rfl, fun w hw => Function.update_of_ne hw _ _, fun w r hr => ?_, fun _ h => h⟩
    by_cases hw : w = t
    · subst hw; simp [hr]
    · simp [Function.update_of_ne hw, hr]

theorem addRec_core {st : SkipSt} {t : View} {d : RecR} (hc : Core ctx dir laws base st)
    (ht : t ∈ st.order) (hd : d.1 = t ∧ Reach ctx dir laws base d) :
    Core ctx dir laws base (st.addRec t d) := by
  rcases addRec_cases t st d with ⟨h, -⟩ | h <;> rw [h]
  · exact hc
  · refine ⟨fun w r hr => ?_, fun w hw => ?_, hc.out_done, fun w s hs => ?_,
      fun r hr => ?_⟩
    · by_cases hw : w = t
      · subst hw
        simp only [Function.update_self, List.mem_append, List.mem_singleton] at hr
        rcases hr with hr | rfl
        · exact hc.sound _ r hr
        · exact hd
      · simp only [Function.update_of_ne hw] at hr
        exact hc.sound w r hr
    · by_cases hwt : w = t
      · rw [hwt]; exact ht
      · simp only [Function.update_of_ne hwt] at hw
        exact hc.in_order w hw
    · by_cases hw : w = t
      · subst hw
        simp only [Function.update_self, List.mem_append, List.mem_singleton] at hs ⊢
        rcases hs with hs | rfl
        · obtain ⟨r, hr, he⟩ := hc.sigs_rec _ s hs
          exact ⟨r, Or.inl hr, he⟩
        · exact ⟨d, Or.inr rfl, rfl⟩
      · simp only [Function.update_of_ne hw] at hs ⊢
        exact hc.sigs_rec w s hs
    · by_cases hw : r.1 = t
      · simp only [hw, Function.update_self, List.mem_append]
        exact Or.inl (hw ▸ hc.base_in r hr)
      · simp only [Function.update_of_ne hw]
        exact hc.base_in r hr

theorem recSig_same_self (d : RecR) : RecSig.same (recSig d) (recSig d) = true := by
  simp [RecSig.same, List.isPerm_iff]

/-- After adding `d`, the target has a record of `d`'s signature. -/
theorem addRec_has {st : SkipSt} {t : View} {d : RecR} (hc : Core ctx dir laws base st) :
    ∃ c ∈ (st.addRec t d).recs t, RecSig.same (recSig d) (recSig c) = true := by
  rcases addRec_cases t st d with ⟨h, hs⟩ | h
  · rw [h]
    obtain ⟨s, hs, he⟩ := List.any_eq_true.1 hs
    obtain ⟨c, hc', rfl⟩ := hc.sigs_rec t s hs
    exact ⟨c, hc', he⟩
  · rw [h]
    exact ⟨d, by simp, recSig_same_self d⟩

theorem foldl_addRec {t : View} (ds : List RecR) (hds : ∀ d ∈ ds, d.1 = t ∧ Reach ctx dir laws base d)
    (st : SkipSt) (hc : Core ctx dir laws base st) (ht : t ∈ st.order) :
    let st' := ds.foldl (SkipSt.addRec t) st
    Core ctx dir laws base st' ∧ st'.order = st.order ∧ st'.done = st.done ∧
      (∀ w, w ≠ t → st'.recs w = st.recs w) ∧ Mono st st' ∧
      (∀ d ∈ ds, ∃ c ∈ st'.recs t, Cov c d) ∧ (st.sigs t = [] → ds ≠ [] → st'.recs t ≠ []) := by
  intro st'
  have hI := foldl_induct (SkipSt.addRec t)
    (fun s => Core ctx dir laws base s ∧ s.order = st.order ∧ s.done = st.done ∧
      (∀ w, w ≠ t → s.recs w = st.recs w) ∧ Mono st s) ds st
    ⟨hc, rfl, rfl, fun _ _ => rfl, Mono.refl _⟩
    (fun s d hd ⟨hcs, ho, hdn, hr, hm⟩ => by
      obtain ⟨fo, fd, fr, fm⟩ := addRec_frame t s d
      exact ⟨addRec_core hcs (ho ▸ ht) (hds d hd), fo.trans ho, fd.trans hdn,
        fun w hw => (fr w hw).trans (hr w hw), hm.trans fm⟩)
  obtain ⟨hcore, ho, hdn, hr, hm⟩ := hI
  refine ⟨hcore, ho, hdn, hr, hm, ?_, ?_⟩
  · intro d hd
    have := foldl_establish (f := SkipSt.addRec t)
      (I := fun s => Core ctx dir laws base s ∧ s.order = st.order)
      (P := fun s => ∃ c ∈ s.recs t, RecSig.same (recSig d) (recSig c) = true) hd
      (fun s x hx ⟨hcs, ho⟩ => ⟨addRec_core hcs (ho ▸ ht) (hds x hx),
        (addRec_frame t s x).1.trans ho⟩)
      (fun s x _ _ ⟨c, hc', he⟩ => ⟨c, (addRec_frame t s x).2.2.2.1 t c hc', he⟩)
      (fun s ⟨hcs, _⟩ => addRec_has hcs) st ⟨hc, rfl⟩
    obtain ⟨c, hc', he⟩ := this
    refine ⟨c, hc', cov_of_same he ?_⟩
    rw [(hcore.sound t c hc').1, (hds d hd).1]
  · intro hs hne
    obtain ⟨d, ds', rfl⟩ := List.exists_cons_of_ne_nil hne
    have h1 : (st.addRec t d).recs t ≠ [] := by
      rcases addRec_cases t st d with ⟨-, hany⟩ | h
      · rw [hs] at hany; simp at hany
      · rw [h]; simp
    obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ h1
    have hm' := foldl_induct (SkipSt.addRec t) (fun s => x ∈ s.recs t) ds' (st.addRec t d) hx
      (fun s y _ h => (addRec_frame t s y).2.2.2.1 t x h)
    exact List.ne_nil_of_mem hm'

/-! ### One target -/

/-- The source's records: a subset, nonempty when the source has records, and
covering each of them. -/
theorem srcRecs_spec {rs : List RecR} {w : View} (hw : ∀ r ∈ rs, r.1 = w) :
    (∀ r ∈ srcRecs rs, r ∈ rs) ∧ (rs ≠ [] → srcRecs rs ≠ []) ∧
      ∀ a ∈ rs, ∃ a' ∈ srcRecs rs, Cov a' a := by
  unfold srcRecs
  split
  · rename_i u hu
    have hmem := List.mem_of_find?_eq_some hu
    have hun := List.find?_some hu
    refine ⟨fun r hr => by rw [List.mem_singleton] at hr; rw [hr]; exact hmem,
      fun _ => List.cons_ne_nil _ _, fun a ha => ⟨u, List.mem_singleton_self _, ?_⟩⟩
    exact cov_uncond hun ((hw u hmem).trans (hw a ha).symm)
  · exact ⟨fun _ h => h, id, fun a ha => ⟨a, ha, Cov.refl a⟩⟩

/-- While the view `w` is regrouped: the core invariant, every entry filled,
the regrouped views fixed to `D`, and the entries not regrouped no larger
than `w`. -/
structure ProcInv (ctx : Ctx) (dir : Dir) (laws : Laws) (base : List RecR) (w : View)
    (D : View → Bool) (st : SkipSt) : Prop where
  core : Core ctx dir laws base st
  filled : Filled st
  done_eq : st.done = D
  small : ∀ u ∈ st.order, D u = false → viewSize u ≤ viewSize w

/-- What a step of the regrouping of `w` keeps. -/
def StepOK (D : View → Bool) (st st' : SkipSt) : Prop :=
  Mono st st' ∧ ∀ v, D v = true → st'.recs v = st.recs v

theorem StepOK.refl (D : View → Bool) (st : SkipSt) : StepOK D st st :=
  ⟨Mono.refl _, fun _ _ => rfl⟩

theorem StepOK.trans {D : View → Bool} {a b c : SkipSt} (h₁ : StepOK D a b)
    (h₂ : StepOK D b c) : StepOK D a c :=
  ⟨h₁.1.trans h₂.1, fun v hv => (h₂.2 v hv).trans (h₁.2 v hv)⟩

/-- **One target.** Every regrouped view is at least as large as `w`, the
target is smaller: it is not regrouped (the engine's assertion), so the
derived records `ds` are each covered by a record of the target afterwards:
its unconditional record, or a record of the same signature, or the record
itself. -/
theorem addTarget_spec {w : View} {D : View → Bool} {st : SkipSt}
    (hp : ProcInv ctx dir laws base w D st) (hD : ∀ v, D v = true → viewSize w ≤ viewSize v)
    {t : View} {ds : List RecR} (hds : ∀ d ∈ ds, d.1 = t ∧ Reach ctx dir laws base d)
    (hne : ds ≠ []) (hlt : viewSize t < viewSize w) :
    ProcInv ctx dir laws base w D (st.addTarget t ds) ∧ StepOK D st (st.addTarget t ds) ∧
      ∀ d ∈ ds, ∃ c ∈ (st.addTarget t ds).recs t, Cov c d := by
  have hnd : st.done t = false := by
    rw [hp.done_eq]
    cases h : D t
    · rfl
    · have := hD t h; omega
  have hDt : D t = false := hp.done_eq ▸ hnd
  unfold SkipSt.addTarget
  -- The target entered.
  set st₁ : SkipSt := if t ∈ st.order then st else { st with order := st.order ++ [t] }
    with hst₁
  have h₁recs : st₁.recs = st.recs := by rw [hst₁]; split <;> rfl
  have h₁done : st₁.done = st.done := by rw [hst₁]; split <;> rfl
  have h₁sigs : st₁.sigs = st.sigs := by rw [hst₁]; split <;> rfl
  have h₁order : ∀ v, v ∈ st₁.order ↔ v ∈ st.order ∨ v = t := by
    intro v
    rw [hst₁]
    split
    · rename_i h
      constructor
      · exact Or.inl
      · rintro (h' | rfl)
        · exact h'
        · exact h
    · simp
  have ht₁ : t ∈ st₁.order := (h₁order t).2 (Or.inr rfl)
  have hc₁ : Core ctx dir laws base st₁ := by
    obtain ⟨hs, hio, hod, hsr, hbi⟩ := hp.core
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [h₁recs]; exact hs
    · intro v hv; rw [h₁recs] at hv; exact (h₁order v).2 (Or.inl (hio v hv))
    · intro v hv; rw [h₁done]; exact hod v (fun h => hv ((h₁order v).2 (Or.inl h)))
    · rw [h₁sigs, h₁recs]; exact hsr
    · rw [h₁recs]; exact hbi
  have hm₁ : StepOK D st st₁ :=
    ⟨⟨fun v r h => by rw [h₁recs]; exact h, fun v h => (h₁order v).2 (Or.inl h)⟩,
      fun v _ => by rw [h₁recs]⟩
  dsimp only
  split
  · -- An unconditional record of the target admits every match.
    rename_i hu
    obtain ⟨u, hu, huu⟩ := List.any_eq_true.1 hu
    have htin : t ∈ st.order := hp.core.in_order t (by rw [← h₁recs]; exact List.ne_nil_of_mem hu)
    refine ⟨⟨hc₁, fun v hv => ?_, by rw [h₁done, hp.done_eq], fun v hv hDv => ?_⟩, hm₁,
      fun d hd => ⟨u, hu, cov_uncond huu ?_⟩⟩
    · rw [h₁recs]
      rcases (h₁order v).1 hv with h | rfl
      · exact hp.filled v h
      · exact hp.filled _ htin
    · rcases (h₁order v).1 hv with h | rfl
      · exact hp.small v h hDv
      · exact le_of_lt hlt
    · rw [(hc₁.sound t u hu).1, (hds d hd).1]
  · obtain ⟨hc', ho', hdn', hr', hm', hcov, hfill⟩ := foldl_addRec ds hds st₁ hc₁ ht₁
    refine ⟨⟨hc', fun v hv => ?_, by rw [hdn', h₁done, hp.done_eq], fun v hv hDv => ?_⟩,
      hm₁.trans ⟨hm', fun v hDv => hr' v (fun h => by rw [h, hDt] at hDv; simp at hDv)⟩, hcov⟩
    · rw [ho'] at hv
      by_cases hvt : v = t
      · subst hvt
        by_cases hin : v ∈ st.order
        · exact fun h => hp.filled v hin (by
            have := hm'.1 v; rw [h₁recs] at this
            obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ (hp.filled v hin)
            have := this x hx; rw [h] at this; simp at this)
        · exact hfill (by rw [h₁sigs]; exact hp.core.sigs_nil hin) hne
      · rw [hr' v hvt, h₁recs]
        rcases (h₁order v).1 hv with h | h
        · exact hp.filled v h
        · exact absurd h hvt
    · rw [ho'] at hv
      rcases (h₁order v).1 hv with h | rfl
      · exact hp.small v h hDv
      · exact le_of_lt hlt

/-! ### Regrouping one view -/

theorem fitStep_spec (hb : BaseGood ctx.κ base) {w : View} {D : View → Bool} {st : SkipSt}
    (hp : ProcInv ctx dir laws base w D st) (hD : ∀ v, D v = true → viewSize w ≤ viewSize v)
    (hDw : D w = true) {gg : C × List (C × Nat)} (hgg : gg ∈ groupsOf ctx)
    {raw : List (C × Nat)} (hraw : raw ∈ fitsR ctx.κ dir w gg.1 gg.2) :
    ProcInv ctx dir laws base w D (SkipSt.fitStep ctx laws w gg st raw) ∧
      StepOK D st (SkipSt.fitStep ctx laws w gg st raw) ∧
      ∀ t, normalize ctx.κ laws raw = .node t → ∀ a ∈ st.recs w,
        ∃ c ∈ (SkipSt.fitStep ctx laws w gg st raw).recs t,
          Cov c (deriveRec t gg.1 (gg.2.map Prod.fst) a) := by
  unfold SkipSt.fitStep
  split
  · rename_i t hn
    have hwin : w ∈ st.order := by
      by_contra h
      have := hp.core.out_done w h
      rw [hp.done_eq, hDw] at this
      simp at this
    have hsw : ∀ r ∈ st.recs w, r.1 = w := fun r hr => (hp.core.sound w r hr).1
    obtain ⟨hsub, hsne, hscov⟩ := srcRecs_spec hsw
    have hmem : ∀ a' ∈ srcRecs (st.recs w),
        deriveRec t gg.1 (gg.2.map Prod.fst) a' ∈ regroupRec ctx dir laws a' := by
      intro a' ha'
      exact deriveRec_mem hgg (by rw [hsw a' (hsub a' ha')]; exact hraw) hn
    have hds : ∀ d ∈ (srcRecs (st.recs w)).map (deriveRec t gg.1 (gg.2.map Prod.fst)),
        d.1 = t ∧ Reach ctx dir laws base d := by
      intro d hd
      obtain ⟨a', ha', rfl⟩ := List.mem_map.1 hd
      exact ⟨rfl, reach_step (hp.core.sound w a' (hsub a' ha')).2 (hmem a' ha')⟩
    obtain ⟨a₀, ha₀⟩ := List.exists_mem_of_ne_nil _ (hsne (hp.filled w hwin))
    have hlt : viewSize t < viewSize w := by
      have hr := (hp.core.sound w a₀ (hsub a₀ ha₀))
      have := (regroupRec_shrink (reach_good hb hr.2).1 (hmem a₀ ha₀)).2
      rw [hr.1] at this
      exact this
    obtain ⟨hp', hok, hcov⟩ := addTarget_spec hp hD hds
      (by simp only [ne_eq, List.map_eq_nil_iff]; exact hsne (hp.filled w hwin)) hlt
    refine ⟨hp', hok, fun t' ht' a ha => ?_⟩
    rw [hn] at ht'
    cases ht'
    obtain ⟨a', ha', hca⟩ := hscov a ha
    obtain ⟨c, hc, hcd⟩ := hcov _ (List.mem_map_of_mem ha')
    exact ⟨c, hc, hcd.trans (hca.derive _ _ _)⟩
  · rename_i hn
    refine ⟨hp, StepOK.refl _ _, fun t ht => absurd ht ?_⟩
    intro h; exact hn t h

theorem regroupView_spec (hb : BaseGood ctx.κ base) {gs : List (C × List (C × Nat))}
    (hgs : ∀ gg ∈ gs, gg ∈ groupsOf ctx) (hgs' : CandSup ctx dir gs)
    {w : View} {D : View → Bool} {st₀ : SkipSt}
    (hp : ProcInv ctx dir laws base w D st₀) (hD : ∀ v, D v = true → viewSize w ≤ viewSize v)
    (hDw : D w = true) :
    ProcInv ctx dir laws base w D (SkipSt.regroupView ctx dir laws gs w st₀) ∧
      StepOK D st₀ (SkipSt.regroupView ctx dir laws gs w st₀) ∧
      Closed ctx dir laws (SkipSt.regroupView ctx dir laws gs w st₀) w := by
  let I : SkipSt → Prop := fun st => ProcInv ctx dir laws base w D st ∧ StepOK D st₀ st
  have hfit : ∀ gg ∈ gs, ∀ st raw, raw ∈ fitsR ctx.κ dir w gg.1 gg.2 → I st →
      I (SkipSt.fitStep ctx laws w gg st raw) := by
    intro gg hgg st raw hraw ⟨hp', hok⟩
    obtain ⟨h1, h2, -⟩ := fitStep_spec hb hp' hD hDw (hgs gg hgg) hraw
    exact ⟨h1, hok.trans h2⟩
  have hgrp : ∀ st gg, gg ∈ gs → I st → I (SkipSt.groupStep ctx dir laws w st gg) :=
    fun st gg hgg hI => foldl_induct _ I _ st hI (fun st raw hraw h => hfit gg hgg st raw hraw h)
  have hall := foldl_induct _ I gs st₀ ⟨hp, StepOK.refl _ _⟩ hgrp
  refine ⟨hall.1, hall.2, ?_⟩
  unfold SkipSt.regroupView
  intro a ha b hb'
  have hrw : ∀ st, I st → st.recs w = st₀.recs w := fun st hI => hI.2.2 w hDw
  rw [hrw _ hall] at ha
  obtain ⟨g, grp, raw, hgg, hraw, hn, hbe⟩ := regroupRec_derive hb'
  have haw : a.1 = w := (hp.core.sound w a ha).1
  rw [haw] at hraw
  let P : SkipSt → Prop := fun st => ∃ c ∈ st.recs b.1, Cov c b
  have hPm : ∀ st st', StepOK D st st' → P st → P st' :=
    fun st st' hok ⟨c, hc, hcov⟩ => ⟨c, hok.1.1 _ c hc, hcov⟩
  refine foldl_establish (I := I) (P := P) (hgs' w _ hgg _ hraw) hgrp ?_ ?_ st₀ ⟨hp, StepOK.refl _ _⟩
  · intro st gg hgg' hI hP
    have := foldl_induct (SkipSt.fitStep ctx laws w gg)
      (fun st' => I st' ∧ StepOK D st st') _ st ⟨hI, StepOK.refl _ _⟩
      (fun st' raw hraw ⟨hI', hok'⟩ => by
        obtain ⟨h1, h2, -⟩ := fitStep_spec hb hI'.1 hD hDw (hgs gg hgg') hraw
        exact ⟨⟨h1, hI'.2.trans h2⟩, hok'.trans h2⟩)
    exact hPm _ _ this.2 hP
  · intro st hI
    refine foldl_establish (I := I) (P := P) hraw (fun st raw hraw h => hfit _ (hgs' w _ hgg _ hraw) st raw hraw h)
      ?_ ?_ st hI
    · intro st' raw' hraw' hI' hP'
      obtain ⟨-, h2, -⟩ := fitStep_spec hb hI'.1 hD hDw hgg hraw'
      exact hPm _ _ h2 hP'
    · intro st' hI'
      obtain ⟨-, -, h3⟩ := fitStep_spec hb hI'.1 hD hDw hgg hraw
      obtain ⟨c, hc, hcov⟩ := h3 b.1 hn a (by rw [hrw _ hI']; exact ha)
      refine ⟨c, hc, ?_⟩
      rw [hbe]
      exact hcov

/-! ### The order of the views -/

/-- What the scan for the next view has found so far: nothing when every view
seen was regrouped, otherwise a view not regrouped at least as large as
every view seen not regrouped. -/
def NextOK (st : SkipSt) (seen : List View) (best : Option View) : Prop :=
  (best = none → ∀ u ∈ seen, st.done u = true) ∧
    ∀ b, best = some b → b ∈ seen ∧ st.done b = false ∧
      ∀ u ∈ seen, st.done u = false → viewSize u ≤ viewSize b

theorem nextOK_foldl (st : SkipSt) :
    ∀ (l seen : List View) (best : Option View), NextOK st seen best →
      NextOK st (seen ++ l) (l.foldl st.pickStep best)
  | [], seen, best, h => by simpa using h
  | x :: l, seen, best, h => by
      rw [List.foldl_cons, List.append_cons]
      refine nextOK_foldl st l (seen ++ [x]) _ ?_
      obtain ⟨hn, hs⟩ := h
      unfold SkipSt.pickStep
      by_cases hx : st.done x = true
      · simp only [hx, ↓reduceIte]
        refine ⟨fun h u hu => ?_, fun b hb => ?_⟩
        · rcases List.mem_append.1 hu with hu | hu
          · exact hn h u hu
          · rw [List.mem_singleton] at hu; rw [hu]; exact hx
        · obtain ⟨h1, h2, h3⟩ := hs b hb
          refine ⟨List.mem_append_left _ h1, h2, fun u hu hd => ?_⟩
          rcases List.mem_append.1 hu with hu | hu
          · exact h3 u hu hd
          · rw [List.mem_singleton] at hu; rw [hu] at hd; rw [hd] at hx; simp at hx
      · have hx' : st.done x = false := by simpa using hx
        simp only [hx', Bool.false_eq_true, ↓reduceIte]
        cases best with
        | none =>
            refine ⟨fun h => by simp at h, fun b hb => ?_⟩
            simp only [Option.some.injEq] at hb
            subst hb
            refine ⟨by simp, hx', fun u hu hd => ?_⟩
            rcases List.mem_append.1 hu with hu | hu
            · have := hn rfl u hu; rw [hd] at this; simp at this
            · rw [List.mem_singleton] at hu; rw [hu]
        | some b₀ =>
            obtain ⟨h1, h2, h3⟩ := hs b₀ rfl
            simp only
            split
            · rename_i hlt
              refine ⟨fun h => by simp at h, fun b hb => ?_⟩
              simp only [Option.some.injEq] at hb
              subst hb
              refine ⟨List.mem_append_left _ h1, h2, fun u hu hd => ?_⟩
              rcases List.mem_append.1 hu with hu | hu
              · exact h3 u hu hd
              · rw [List.mem_singleton] at hu; rw [hu]; exact le_of_lt hlt
            · rename_i hlt
              refine ⟨fun h => by simp at h, fun b hb => ?_⟩
              simp only [Option.some.injEq] at hb
              subst hb
              refine ⟨by simp, hx', fun u hu hd => ?_⟩
              rcases List.mem_append.1 hu with hu | hu
              · exact le_trans (h3 u hu hd) (by omega)
              · rw [List.mem_singleton] at hu; rw [hu]

/-- **The next view** is an entry not regrouped, at least as large as every
entry not regrouped; there is none when every entry is regrouped. -/
theorem next_spec (st : SkipSt) : NextOK st st.order st.next := by
  have := nextOK_foldl st st.order [] none ⟨fun _ _ h => by simp at h, fun _ h => by simp at h⟩
  unfold SkipSt.next
  simpa using this

/-! ### The loop -/

/-- The invariant of the loop: the core, every entry filled, every view
regrouped at least as large as every entry not regrouped, and every view
regrouped closed. -/
structure SkipInv (ctx : Ctx) (dir : Dir) (laws : Laws) (base : List RecR) (st : SkipSt) :
    Prop where
  core : Core ctx dir laws base st
  filled : Filled st
  sizes : ∀ v u, st.done v = true → u ∈ st.order → st.done u = false → viewSize u ≤ viewSize v
  closed : ∀ v, st.done v = true → Closed ctx dir laws st v

/-- The views regrouped. -/
def doneSet (st : SkipSt) : Finset View := (st.order.filter (fun v => st.done v)).toFinset

theorem mark_procInv {st : SkipSt} {w : View} (hi : SkipInv ctx dir laws base st)
    (hn : st.next = some w) :
    ProcInv ctx dir laws base w (st.mark w).done (st.mark w) ∧
      (∀ v, (st.mark w).done v = true → viewSize w ≤ viewSize v) ∧ (st.mark w).done w = true := by
  obtain ⟨hw, hwd, hmax⟩ := (next_spec st).2 w hn
  have hD : ∀ v, (st.mark w).done v = true ↔ v = w ∨ st.done v = true := by
    intro v
    by_cases hv : v = w
    · subst hv; simp [SkipSt.mark]
    · simp [SkipSt.mark, hv]
  obtain ⟨hs, hio, hod, hsr, hbi⟩ := hi.core
  refine ⟨⟨⟨hs, hio, fun v hv => ?_, hsr, hbi⟩, hi.filled, rfl, fun u hu hDu => ?_⟩,
    fun v hv => ?_, (hD w).2 (Or.inl rfl)⟩
  · have hvw : v ≠ w := fun h => hv (h ▸ hw)
    simp only [SkipSt.mark, Function.update_of_ne hvw]
    exact hod v hv
  · have hu' : st.done u = false := by
      cases h : st.done u
      · rfl
      · have := (hD u).2 (Or.inr h); rw [hDu] at this; simp at this
    exact hmax u hu hu'
  · rcases (hD v).1 hv with rfl | hv
    · exact le_refl _
    · exact hi.sizes v w hv hw hwd

/-- **One iteration** keeps the invariant and regroups one more view. -/
theorem step_spec (hb : BaseGood ctx.κ base) {gs : List (C × List (C × Nat))}
    (hgs : ∀ gg ∈ gs, gg ∈ groupsOf ctx) (hgs' : CandSup ctx dir gs)
    {st : SkipSt} {w : View} (hi : SkipInv ctx dir laws base st) (hn : st.next = some w) :
    SkipInv ctx dir laws base (SkipSt.regroupView ctx dir laws gs w (st.mark w)) ∧
      doneSet (SkipSt.regroupView ctx dir laws gs w (st.mark w)) = insert w (doneSet st) ∧
      w ∉ doneSet st := by
  obtain ⟨hw, hwd, -⟩ := (next_spec st).2 w hn
  obtain ⟨hp, hD, hDw⟩ := mark_procInv hi hn
  obtain ⟨hp', hok, hcl⟩ := regroupView_spec hb hgs hgs' hp hD hDw
  set st₁ := SkipSt.regroupView ctx dir laws gs w (st.mark w)
  have hdone : st₁.done = (st.mark w).done := hp'.done_eq
  have hDiff : ∀ v, (st.mark w).done v = true ↔ v = w ∨ st.done v = true := by
    intro v
    by_cases hv : v = w
    · subst hv; simp [SkipSt.mark]
    · simp [SkipSt.mark, hv]
  refine ⟨⟨hp'.core, hp'.filled, fun v u hv hu hud => ?_, fun v hv => ?_⟩, ?_, ?_⟩
  · rw [hdone] at hv hud
    exact le_trans (hp'.small u hu hud) (hD v hv)
  · rw [hdone] at hv
    rcases (hDiff v).1 hv with rfl | hv'
    · exact hcl
    · have hcl0 : Closed ctx dir laws (st.mark w) v := hi.closed v hv'
      exact hcl0.mono hok.1 (hok.2 v hv)
  · ext v
    simp only [doneSet, List.mem_toFinset, List.mem_filter, Finset.mem_insert, hdone]
    constructor
    · rintro ⟨-, hv⟩
      rcases (hDiff v).1 hv with h | h
      · exact Or.inl h
      · refine Or.inr ⟨?_, h⟩
        by_contra hno
        have := hi.core.out_done v hno; rw [h] at this; simp at this
    · rintro (rfl | ⟨hv, hd⟩)
      · exact ⟨hok.1.2 _ hw, (hDiff _).2 (Or.inl rfl)⟩
      · exact ⟨hok.1.2 _ hv, (hDiff v).2 (Or.inr hd)⟩
  · simp [doneSet, hwd]

/-- The views regrouped are views of the full enumeration. -/
theorem doneSet_subset (hb : BaseGood ctx.κ base) {st : SkipSt}
    (hi : SkipInv ctx dir laws base st) :
    doneSet st ⊆ ((regroupAll ctx dir laws (regroupFuel base) base).map Prod.fst).toFinset := by
  intro v hv
  simp only [doneSet, List.mem_toFinset, List.mem_filter] at hv
  obtain ⟨r, hr⟩ := List.exists_mem_of_ne_nil _ (hi.filled v hv.1)
  obtain ⟨rfl, hreach⟩ := hi.core.sound v r hr
  exact List.mem_toFinset.2 (List.mem_map_of_mem ((mem_regroupAll_iff_reach hb).2 hreach))

/-- **The loop ends with every view regrouped**, within the fuel. -/
theorem run_finished (hb : BaseGood ctx.κ base) {gs : List (C × List (C × Nat))}
    (hgs : ∀ gg ∈ gs, gg ∈ groupsOf ctx) (hgs' : CandSup ctx dir gs) :
    ∀ (n : Nat) (st : SkipSt), SkipInv ctx dir laws base st →
      (regroupAll ctx dir laws (regroupFuel base) base).length + 1 ≤ (doneSet st).card + n →
      SkipInv ctx dir laws base (SkipSt.run ctx dir laws gs n st) ∧
        (SkipSt.run ctx dir laws gs n st).next = none
  | 0, st, hi, hle => by
      have h1 := Finset.card_le_card (doneSet_subset hb hi)
      have h2 := List.toFinset_card_le ((regroupAll ctx dir laws (regroupFuel base) base).map
        Prod.fst)
      rw [List.length_map] at h2
      omega
  | n + 1, st, hi, hle => by
      unfold SkipSt.run
      split
      · rename_i hn
        exact ⟨hi, hn⟩
      · rename_i w hn
        obtain ⟨hi', hds, hw⟩ := step_spec hb hgs hgs' hi hn
        refine run_finished hb hgs hgs' n _ hi' ?_
        rw [hds, Finset.card_insert_of_notMem hw]
        omega

/-! ### The walk's records -/

theorem enter_mono {st : SkipSt} {r : RecR} {v : View} {x : RecR} (h : x ∈ st.recs v) :
    x ∈ (st.enter r).recs v := by
  by_cases hv : v = r.1
  · subst hv; simp [SkipSt.enter, h]
  · simp [SkipSt.enter, Function.update_of_ne hv, h]

theorem foldl_enter_mem :
    ∀ (xs : List RecR) (st : SkipSt) (r : RecR), (r ∈ xs ∨ r ∈ st.recs r.1) →
      r ∈ (xs.foldl SkipSt.enter st).recs r.1
  | [], _, _, h => by simpa using h
  | x :: xs, st, r, h => by
      rw [List.foldl_cons]
      refine foldl_enter_mem xs _ r ?_
      rcases h with h | h
      · rcases List.mem_cons.1 h with rfl | h
        · exact Or.inr (by simp [SkipSt.enter])
        · exact Or.inl h
      · exact Or.inr (enter_mono h)

theorem init_inv (base : List RecR) : SkipInv ctx dir laws base (SkipSt.init base) := by
  have hI := foldl_induct SkipSt.enter
    (fun st => (∀ w, ∀ r ∈ st.recs w, r.1 = w ∧ r ∈ base) ∧
      (∀ w, w ∈ st.order ↔ st.recs w ≠ []) ∧ (∀ w, st.done w = false) ∧
      ∀ w, st.sigs w = []) base SkipSt.empty
    ⟨fun _ _ h => by simp [SkipSt.empty] at h, fun _ => by simp [SkipSt.empty],
      fun _ => rfl, fun _ => rfl⟩
    (fun st x hx ⟨hs, ho, hd, hsg⟩ => by
      refine ⟨fun w r hr => ?_, fun w => ?_, hd, hsg⟩
      · by_cases hw : w = x.1
        · subst hw
          simp only [SkipSt.enter, Function.update_self, List.mem_append,
            List.mem_singleton] at hr
          rcases hr with hr | rfl
          · exact hs _ r hr
          · exact ⟨rfl, hx⟩
        · simp only [SkipSt.enter, Function.update_of_ne hw] at hr
          exact hs w r hr
      · by_cases hw : w = x.1
        · subst hw
          simp only [SkipSt.enter, Function.update_self, ne_eq, List.append_eq_nil_iff,
            List.cons_ne_self, and_false, not_false_eq_true, iff_true]
          split
          · assumption
          · simp
        · simp only [SkipSt.enter, Function.update_of_ne hw]
          rw [← ho w]
          split
          · rfl
          · simp [hw])
  obtain ⟨hs, ho, hd, hsg⟩ := hI
  unfold SkipSt.init
  refine ⟨⟨fun w r hr => ⟨(hs w r hr).1, r, (hs w r hr).2, Relation.ReflTransGen.refl⟩,
    fun w h => (ho w).2 h, fun w _ => hd w, fun w s h => by rw [hsg w] at h; simp at h,
    fun r hr => foldl_enter_mem base SkipSt.empty r (Or.inl hr)⟩,
    fun w h => (ho w).1 h, fun v _ h => by rw [hd v] at h; simp at h,
    fun v h => by rw [hd v] at h; simp at h⟩

/-! ### The records the loop ends with -/

/-- **The engine's regrouping**: its records are reachable, and every
reachable record is covered by one of them. -/
theorem regroupSkipG_spec (hb : BaseGood ctx.κ base) {gs : List (C × List (C × Nat))}
    (hgs : ∀ gg ∈ gs, gg ∈ groupsOf ctx) (hgs' : CandSup ctx dir gs) :
    (∀ r ∈ regroupSkipG ctx dir laws gs base, Reach ctx dir laws base r) ∧
      ∀ b, Reach ctx dir laws base b → ∃ c ∈ regroupSkipG ctx dir laws gs base, Cov c b := by
  obtain ⟨hi, hnext⟩ := run_finished hb hgs hgs' (skipFuel ctx dir laws base)
    (SkipSt.init base) (init_inv (ctx := ctx) (dir := dir) (laws := laws) base)
    (by unfold skipFuel; omega)
  set st := SkipSt.run ctx dir laws gs (skipFuel ctx dir laws base) (SkipSt.init base)
  have hall : ∀ v ∈ st.order, st.done v = true := (next_spec st).1 hnext
  have hrec : ∀ r, r ∈ regroupSkipG ctx dir laws gs base ↔ ∃ v ∈ st.order, r ∈ st.recs v := by
    intro r
    show r ∈ st.records ↔ _
    simp [SkipSt.records]
  refine ⟨fun r hr => ?_, fun b hb' => ?_⟩
  · obtain ⟨v, -, hr⟩ := (hrec r).1 hr
    exact (hi.core.sound v r hr).2
  · suffices h : ∃ c ∈ st.recs b.1, Cov c b by
      obtain ⟨c, hc, hcov⟩ := h
      exact ⟨c, (hrec c).2 ⟨b.1, hi.core.in_order _ (List.ne_nil_of_mem hc), hc⟩, hcov⟩
    obtain ⟨r₀, h₀, hch⟩ := hb'
    induction hch with
    | refl => exact ⟨r₀, hi.core.base_in r₀ h₀, Cov.refl _⟩
    | @tail a b' _ hs ih =>
        obtain ⟨c, hc, hcov⟩ := ih
        obtain ⟨g, grp, raw, hgg, hraw, hn, hbe⟩ := regroupRec_derive hs
        have hc1 : c.1 = a.1 := hcov.1
        have hc' : deriveRec b'.1 g (grp.map Prod.fst) c ∈ regroupRec ctx dir laws c :=
          deriveRec_mem hgg (by rw [hc1]; exact hraw) hn
        have hca : a.1 ∈ st.order := hi.core.in_order _ (List.ne_nil_of_mem hc)
        obtain ⟨c', hc'', hcov'⟩ := hi.closed a.1 (hall _ hca) c hc _ hc'
        refine ⟨c', hc'', hcov'.trans ?_⟩
        rw [hbe]
        exact hcov.derive _ _ _

end Loop

/-! ## The match sets are equal -/

/-- **The engine's regrouping accepts the same matches as the full one**, for
any laws, kind, fold direction and candidate order: a view has a record
within the item limit passing the engine's demand rule in one iff it has one
in the other. The full side is the covered record; the engine's side covers
it, needs no more classes and passes the rule whenever it does. -/
theorem regroupSkipG_iff {ctx : Ctx} {dir : Dir} {laws : Laws} {base : List RecR}
    (hb : BaseGood ctx.κ base) {gs : List (C × List (C × Nat))}
    (hgs : ∀ gg ∈ gs, gg ∈ groupsOf ctx) (hgs' : CandSup ctx dir gs)
    {F : Nat} (hF : ∀ r ∈ base, viewSize r.1 ≤ F) {limit : Nat} {w : List (C × Nat)}
    {taken : List C} :
    (∃ r ∈ withinLimit limit (regroupSkipG ctx dir laws gs base), r.1 = w ∧
        ∀ l ∈ r.alt, l.okE ctx.κ taken) ↔
      ∃ r ∈ withinLimit limit (regroupLevels ctx dir laws F base), r.1 = w ∧
        ∀ l ∈ r.alt, l.okE ctx.κ taken := by
  obtain ⟨hs, hc⟩ := regroupSkipG_spec (dir := dir) (laws := laws) hb hgs hgs'
  constructor
  · rintro ⟨r, hr, hw, hacc⟩
    obtain ⟨hr, hlim⟩ := mem_withinLimit.1 hr
    exact ⟨r, mem_withinLimit.2 ⟨(mem_regroupLevels_iff_reach hb hF).2 (hs r hr), hlim⟩, hw, hacc⟩
  · rintro ⟨b, hb', rfl, hacc⟩
    obtain ⟨hb', hlim⟩ := mem_withinLimit.1 hb'
    have hreach := (mem_regroupLevels_iff_reach hb hF).1 hb'
    obtain ⟨c, hc', hcov⟩ := hc b hreach
    exact ⟨c, mem_withinLimit.2 ⟨hc', le_trans (hcov.length (reach_good hb (hs c hc')).2) hlim⟩,
      hcov.1, hcov.accepts hacc⟩

/-- The same under the demand rule with laws (`acceptsLaws`, leaf test
`okL`). -/
theorem regroupSkipG_iffL {ctx : Ctx} {dir : Dir} {laws : Laws} {base : List RecR}
    (hb : BaseGood ctx.κ base) {gs : List (C × List (C × Nat))}
    (hgs : ∀ gg ∈ gs, gg ∈ groupsOf ctx) (hgs' : CandSup ctx dir gs)
    {F : Nat} (hF : ∀ r ∈ base, viewSize r.1 ≤ F) {limit : Nat} {w : List (C × Nat)}
    {taken : List C} :
    (∃ r ∈ withinLimit limit (regroupSkipG ctx dir laws gs base), r.1 = w ∧
        ∀ l ∈ r.alt, l.okL taken) ↔
      ∃ r ∈ withinLimit limit (regroupLevels ctx dir laws F base), r.1 = w ∧
        ∀ l ∈ r.alt, l.okL taken := by
  obtain ⟨hs, hc⟩ := regroupSkipG_spec (dir := dir) (laws := laws) hb hgs hgs'
  constructor
  · rintro ⟨r, hr, hw, hacc⟩
    obtain ⟨hr, hlim⟩ := mem_withinLimit.1 hr
    exact ⟨r, mem_withinLimit.2 ⟨(mem_regroupLevels_iff_reach hb hF).2 (hs r hr), hlim⟩, hw, hacc⟩
  · rintro ⟨b, hb', rfl, hacc⟩
    obtain ⟨hb', hlim⟩ := mem_withinLimit.1 hb'
    have hreach := (mem_regroupLevels_iff_reach hb hF).1 hb'
    obtain ⟨c, hc', hcov⟩ := hc b hreach
    exact ⟨c, mem_withinLimit.2 ⟨hc', le_trans (hcov.length (reach_good hb (hs c hc')).2) hlim⟩,
      hcov.1, hcov.acceptsL hacc⟩

theorem groupsOfEngine_sub (ctx : Ctx) : ∀ gg ∈ groupsOfEngine ctx, gg ∈ groupsOf ctx :=
  fun _ h => mem_groupsOfEngine.1 h

theorem groupsOfEngine_sup (ctx : Ctx) : ∀ gg ∈ groupsOf ctx, gg ∈ groupsOfEngine ctx :=
  fun _ h => mem_groupsOfEngine.2 h

/-- The walk's records are good, under any laws. -/
theorem baseGood_baseRecsR (ctx : Ctx) (dir : Dir) (laws : Laws) (n : Node) :
    BaseGood ctx.κ (baseRecsR ctx dir laws n) := by
  intro r hr
  obtain ⟨raw, hraw, hn, hneeds⟩ := mem_baseRecsR_raw hr
  refine ⟨viewGood_normalize hn (fun _ => ?_), by rw [hneeds]; exact List.nodup_nil⟩
  exact kidsOfD_pos _ (fun b X k P hk => rawOptD_pos ctx dir _ b X k P hk) dir _ _ 0 1 ∅
    Nat.one_pos (kids_pos _ _) raw hraw

theorem baseGood_filter {κ : FlatKind} {base : List RecR} (hb : BaseGood κ base)
    (p : RecR → Bool) : BaseGood κ (base.filter p) :=
  fun r hr => hb r (List.mem_filter.1 hr).1

/-- `enumerateR` and the engine's enumeration accept the same matches. -/
theorem enumerateRSkip_iff {ctx : Ctx} {dir : Dir} {laws : Laws} {limit : Nat} {n : Node}
    {w : List (C × Nat)} {taken : List C} :
    (∃ d, (w, d) ∈ enumerateRSkip ctx dir laws limit n ∧ d.acceptsE ctx.κ taken) ↔
      ∃ d, (w, d) ∈ enumerateR ctx dir laws limit n ∧ d.acceptsE ctx.κ taken := by
  unfold enumerateRSkip enumerateR regroupAllSkip regroupAll
  rw [acceptsE_enumerateFromR, acceptsE_enumerateFromR]
  exact regroupSkipG_iff (baseGood_baseRecsR ctx dir laws n) (groupsOfEngine_sub ctx)
    (candSup_of_sup dir (groupsOfEngine_sup ctx)) (fun _ h => viewSize_le_regroupFuel h)

/-- `enumerateRD` and the engine's pruned enumeration accept the same matches. -/
theorem enumerateRDSkip_iff {T : C → Bool} {ctx : Ctx} {dir : Dir} {laws : Laws} {limit : Nat}
    {n : Node} {w : List (C × Nat)} {taken : List C} :
    (∃ d, (w, d) ∈ enumerateRDSkip T ctx dir laws limit n ∧ d.acceptsE ctx.κ taken) ↔
      ∃ d, (w, d) ∈ enumerateRD T ctx dir laws limit n ∧ d.acceptsE ctx.κ taken := by
  unfold enumerateRDSkip enumerateRD regroupAllSkip regroupAll
  rw [acceptsE_enumerateFromR, acceptsE_enumerateFromR]
  exact regroupSkipG_iff (baseGood_filter (baseGood_baseRecsR ctx dir laws n) _)
    (groupsOfEngine_sub ctx) (candSup_of_sup dir (groupsOfEngine_sup ctx))
    (fun _ h => viewSize_le_regroupFuel (List.mem_filter.1 h).1)

theorem reach_normal {ctx : Ctx} {dir : Dir} {laws : Laws} {base : List RecR}
    (h0 : ∀ r ∈ base, ∃ v, normalize ctx.κ laws v = .node r.1) {r : RecR}
    (h : Reach ctx dir laws base r) : ∃ v, normalize ctx.κ laws v = .node r.1 := by
  obtain ⟨r₀, h₀, hch⟩ := h
  cases hch with
  | refl => exact h0 _ h₀
  | tail _ hs =>
      obtain ⟨_, _, raw, -, -, hn, -⟩ := mem_regroupRec hs
      exact ⟨raw, hn⟩

theorem normal_enumerateFromRSkip {ctx : Ctx} {dir : Dir} {laws : Laws} {limit : Nat}
    {base : List RecR} (hb : BaseGood ctx.κ base)
    (h0 : ∀ r ∈ base, ∃ v, normalize ctx.κ laws v = .node r.1)
    {w : List (C × Nat)} {d : DemandL}
    (h : (w, d) ∈ enumerateFromR (withinLimit limit (regroupAllSkip ctx dir laws base))) :
    ∃ v, normalize ctx.κ laws v = .node w := by
  obtain ⟨r, hr, rfl⟩ := mem_enumerateFromR h
  exact reach_normal h0 ((regroupSkipG_spec hb (groupsOfEngine_sub ctx)
    (candSup_of_sup dir (groupsOfEngine_sup ctx))).1 r (mem_withinLimit.1 hr).1)

/-- **The engine's enumeration meets the plan specification**, every fold
direction, any laws. -/
theorem regroupSkip_spec (dir : Sym → Dir) : (Enumerator.regroupSkip dir).Spec where
  normal {ctx laws items n w d} h := by
    unfold Enumerator.regroupSkip enumerateRSkip at h
    exact normal_enumerateFromRSkip (baseGood_baseRecsR ctx (dir ctx.f) laws n)
      normal_baseRecsR h
  normalP {ctx laws σ items n w d} h := by
    unfold Enumerator.regroupSkip enumerateRDSkip at h
    exact normal_enumerateFromRSkip (baseGood_filter (baseGood_baseRecsR ctx (dir ctx.f) laws n) _)
      (fun r hr => normal_baseRecsR r (List.mem_filter.1 hr).1) h
  to_full {ctx laws σ σ' items n w d} hext hb h hacc := by
    have h' : (w, d) ∈ enumerateRDSkip (takeableR ctx σ items) ctx (dir ctx.f) laws
        items.length n := h
    obtain ⟨d₁, hd₁, hacc₁⟩ := enumerateRDSkip_iff.1 ⟨d, h', hacc⟩
    obtain ⟨d₂, hd₂, hacc₂⟩ :=
      (prune_regroup (takeableR_down _ _ _) (takenOf_takeableR hext hb)).1 ⟨d₁, hd₁, hacc₁⟩
    show ∃ d', (w, d') ∈ enumerateRSkip ctx (dir ctx.f) laws items.length n ∧ _
    exact enumerateRSkip_iff.2 ⟨d₂, hd₂, hacc₂⟩
  to_pruned {ctx laws σ σ' items n w d} hext hb h hacc := by
    have h' : (w, d) ∈ enumerateRSkip ctx (dir ctx.f) laws items.length n := h
    obtain ⟨d₁, hd₁, hacc₁⟩ := enumerateRSkip_iff.1 ⟨d, h', hacc⟩
    obtain ⟨d₂, hd₂, hacc₂⟩ :=
      (prune_regroup (takeableR_down _ _ _) (takenOf_takeableR hext hb)).2 ⟨d₁, hd₁, hacc₁⟩
    show ∃ d', (w, d') ∈ enumerateRDSkip (takeableR ctx σ items) ctx (dir ctx.f) laws
      items.length n ∧ _
    exact enumerateRDSkip_iff.2 ⟨d₂, hd₂, hacc₂⟩

/-- **An atom holds under the engine's enumeration iff under the full one.** -/
theorem atomSat_regroupSkip_iff {c : FCtx} {dir : Sym → Dir} {σ : Binding} {a : RAtom} :
    AtomSatG (Enumerator.regroupSkip dir) c σ a ↔ AtomSatG (Enumerator.regroup dir) c σ a := by
  unfold AtomSatG
  split
  · exact Iff.rfl
  · rename_i κ _
    constructor
    · rintro ⟨id, n, h1, h2, h3, h4, w, d, hd, hm, hacc⟩
      obtain ⟨d', hd', hacc'⟩ := (enumerateRSkip_iff (ctx := c.ctx a.op κ)).1 ⟨d, hd, hacc⟩
      exact ⟨id, n, h1, h2, h3, h4, w, d', hd', hm, hacc'⟩
    · rintro ⟨id, n, h1, h2, h3, h4, w, d, hd, hm, hacc⟩
      obtain ⟨d', hd', hacc'⟩ := (enumerateRSkip_iff (ctx := c.ctx a.op κ)).2 ⟨d, hd, hacc⟩
      exact ⟨id, n, h1, h2, h3, h4, w, d', hd', hm, hacc'⟩

/-! ## The final theorems with the engine's enumeration -/

/-- **Soundness of the flattened plan with the engine's regrouping.** -/
theorem regroupSkip_plan_sound {c : FCtx} {dir : Sym → Dir} {sig : Sym → Kind}
    {as : List RAtom} (r : Nat) (hw : QueryFWF c sig as) {env' : EEnv}
    (h : env' ∈ runERSkip c dir (planF as ∅ r) EEnv.empty) :
    (∀ a ∈ as, AtomSatG (Enumerator.regroupSkip dir) c env'.σ a) ∧
      ClsDom env'.σ (planBound as ∅) :=
  flatten_plan_sound_of_spec (regroupSkip_spec dir) r hw h

/-- **Completeness of the flattened plan with the engine's regrouping.** -/
theorem regroupSkip_plan_complete {c : FCtx} {dir : Sym → Dir} {sig : Sym → Kind}
    {as : List RAtom} (r : Nat) (hw : QueryFWF c sig as) {σ' : Binding}
    (hsat : ∀ a ∈ as, AtomSatG (Enumerator.regroupSkip dir) c σ' a) :
    ∃ env' ∈ runERSkip c dir (planF as ∅ r) EEnv.empty, Binding.Extends env'.σ σ' :=
  flatten_plan_complete_of_spec (regroupSkip_spec dir) r hw hsat

/-- **Completeness of the flattened plan with the engine's regrouping, against
the full enumeration**: every binding satisfying every atom under the full
enumeration (`regroup_match_iff`: some chain of regroupings) is emitted. -/
theorem regroupSkip_plan_complete_full {c : FCtx} {dir : Sym → Dir} {sig : Sym → Kind}
    {as : List RAtom} (r : Nat) (hw : QueryFWF c sig as) {σ' : Binding}
    (hsat : ∀ a ∈ as, AtomSatG (Enumerator.regroup dir) c σ' a) :
    ∃ env' ∈ runERSkip c dir (planF as ∅ r) EEnv.empty, Binding.Extends env'.σ σ' :=
  regroupSkip_plan_complete r hw (fun a ha => atomSat_regroupSkip_iff.2 (hsat a ha))

/-- **The engine's regrouped views are exactly the chains' views**, laws-free,
every kind and fold direction (`regroup_views_iff`). -/
theorem regroupSkip_views_iff {ctx : Ctx} {dir : Dir} {limit : Nat} {n : Node}
    {w : List (C × Nat)} {taken : List C} :
    (∃ d, (w, d) ∈ enumerateRSkip ctx dir Laws.free limit n ∧ d.acceptsE ctx.κ taken) ↔
      ∃ r₀ ∈ baseRecsR ctx dir Laws.free n, ∃ r, RegroupChain ctx dir r₀ r ∧ r.1 = w ∧
        r.2.2.length ≤ limit ∧ ∀ l ∈ r.alt, l.okE ctx.κ taken :=
  enumerateRSkip_iff.trans regroup_views_iff

/-- **The matches of the engine's regrouped views, characterized**
(`regroup_match_iff` for `Enumerator.regroupSkip`): an n-ary atom over a
laws-free operator holds iff some chain of regroupings takes a walk record
of a stored node of the atom's class to a record on whose view the binding
matches the shallow pattern, needing at most as many classes as the atom
has items, its leaves and needed classes satisfied by the item classes. -/
theorem regroupSkip_match_iff {c : FCtx} {dir : Sym → Dir} {σ : Binding} {a : RAtom}
    {κ : FlatKind} (hκ : a.shape.flatKind = some κ) (hlaws : c.laws a.op = Laws.free) :
    AtomSatG (Enumerator.regroupSkip dir) c σ a ↔
      ∃ id n, σ.node a.node = some id ∧ (id, n) ∈ c.G.nodes ∧
        σ.cls a.node = some (c.G.find id) ∧ n.op = a.op ∧
        ∃ r₀ ∈ baseRecsR (c.ctx a.op κ) (dir a.op) Laws.free n, ∃ r,
          RegroupChain (c.ctx a.op κ) (dir a.op) r₀ r ∧ r.2.2.length ≤ a.elems.length ∧
          MatchN c.G a.shallow ⟨a.op, ofView κ r.1⟩ σ ∧
          ∀ l ∈ r.alt, l.okE κ (takenOf σ a.elems) :=
  atomSat_regroupSkip_iff.trans (regroup_match_iff hκ hlaws)

/-- **Completeness of the engine's regrouped views at the match level, chains**
(`regroup_match_complete` for `Enumerator.regroupSkip`). -/
theorem regroupSkip_match_complete {c : FCtx} {dir : Sym → Dir} {σ : Binding} {a : RAtom}
    {κ : FlatKind} (hκ : a.shape.flatKind = some κ) {id : NodeId} {n : Node}
    (hnode : σ.node a.node = some id) (hmem : (id, n) ∈ c.G.nodes)
    (hcls : σ.cls a.node = some (c.G.find id)) (hop : n.op = a.op)
    (hlaws : c.laws a.op = Laws.free) {r₀ r : RecR}
    (h₀ : r₀ ∈ baseRecsR (c.ctx a.op κ) (dir a.op) Laws.free n)
    (hch : RegroupChain (c.ctx a.op κ) (dir a.op) r₀ r) (hlim : r.2.2.length ≤ a.elems.length)
    (hacc : ∀ l ∈ r.alt, l.okE κ (takenOf σ a.elems))
    (hm : MatchN c.G a.shallow ⟨a.op, ofView κ r.1⟩ σ) :
    AtomSatG (Enumerator.regroupSkip dir) c σ a :=
  atomSat_regroupSkip_iff.2 (regroup_match_complete hκ hnode hmem hcls hop hlaws h₀ hch hlim hacc hm)

end Semper.EMatch.Flatten
