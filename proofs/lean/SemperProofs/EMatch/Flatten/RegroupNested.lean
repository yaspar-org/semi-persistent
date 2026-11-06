import SemperProofs.EMatch.Flatten.RegroupChain

/-!
# `:flatten`: nested groups and the per-item limit

Two instances of the chain theorems of `RegroupChain.lean`:

* `regroup_nested_limit_counter`: a counter-model for the statement in
  which the per-item limit bounds only the classes still needed after the
  chain. `G3 ∋ F{G1, G2}` with `G1 ∋ F{a, b}` and `G2 ∋ F{c, d}`: the chain
  to `{h, k, G3}` ends needing `G3` alone but passes through
  `{h, k, G1, G2}`, which needs two classes, so with a limit of one the
  enumeration has no view holding `G3`. The engine checks the limit at every
  step too (`flatten_regroup_nested_limit.egg`);
* `regroup_fold_nested`: the nested prefixes of a left fold
  (`(a - b) - c` in `((a - b) - c) - d`) are reached, within one needed
  class at each step.
-/

namespace Semper.EMatch.Flatten

open Semper.EMatch

theorem mem_entries_fst {m : Multiset C} {c : C} :
    c ∈ (Multiset.entries m).map Prod.fst ↔ c ∈ m := by
  have hcan : Canonical (Multiset.entries m) := by
    have := coalesce_canonical (Multiset.entries m)
    unfold coalesce at this
    rwa [ofEntries_entries] at this
  conv_rhs => rw [← ofEntries_entries m]
  rw [mem_ofEntries]
  constructor
  · intro h
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 h
    exact ⟨e, he, rfl, hcan.2 e he⟩
  · rintro ⟨e, he, rfl, -⟩
    exact List.mem_map_of_mem he

theorem mem_needsAfter_iff {g : C} {grp ns : List C} {c : C} :
    c ∈ needsAfter g grp ns ↔ c = g ∨ (c ∈ ns ∧ c ∉ grp) := by
  dsimp only [needsAfter]
  split
  · rename_i hg
    simp only [List.mem_filter, decide_eq_true_eq]
    constructor
    · intro h; exact Or.inr h
    · rintro (rfl | h)
      · simpa using hg
      · exact h
  · simp only [List.mem_append, List.mem_filter, decide_eq_true_eq, List.mem_singleton]
    tauto


/-- A declarative AC step from concrete multisets. -/
theorem regroupStep_ac_of {ctx : Ctx} (hκ : ctx.κ = .ac) {dir : Dir} {limit : Nat} {r : RecR}
    {id : NodeId} {m : Node} {g : C} {M W : Multiset C} (hm : ctx.IsMember id m g)
    (hkids : m.children = .mset M) (hW : ofEntries r.1 = W) (hg : g ∉ M)
    (h2 : 2 ≤ Multiset.card M) (hle : M ≤ W) (hne : M ≠ W) {ns : List C}
    (hns : needsAfter g ((Multiset.entries M).map Prod.fst) r.2.2 = ns) (hlim : ns.length ≤ limit) :
    RegroupStep ctx dir limit r
      (Multiset.entries (W - M + {g}), r.2.1.map (addG g ((Multiset.entries M).map Prod.fst)), ns) := by
  have hk : kids ctx.κ m.children = Multiset.entries M := by rw [hκ, hkids]; rfl
  have h := @RegroupStep.mk ctx dir limit r id m g (Multiset.entries (W - M + {g})) hm
  rw [hk, hκ, hns] at h
  refine h (by rwa [mem_entries_fst]) ?_ hlim
  show 2 ≤ _ ∧ _
  rw [ofEntries_entries, hW]
  exact ⟨h2, hle, hne, rfl⟩

/-! ## A nested group, AC -/

/-- `F` (op 7) AC, classes `a, b, c, d, h, k = 1, …, 6`; `G1 = 11 ∋ F{a, b}`,
`G2 = 13 ∋ F{c, d}`, `G3 = 15 ∋ F{G1, G2}`; the root `F{a, b, c, d, h, k}`
(node 16, class 17). The class `G3` spells `F{a, b, c, d}` only through the
nested groups `G1` and `G2` (`flatten_regroup_nested_limit.egg`). -/
def exNestG : Graph :=
  ⟨[(10, ⟨7, .mset {1, 2}⟩), (12, ⟨7, .mset {3, 4}⟩), (14, ⟨7, .mset {11, 13}⟩),
    (16, ⟨7, .mset {1, 2, 3, 4, 5, 6}⟩)],
    fun id => if id = 10 then 11 else if id = 12 then 13 else if id = 14 then 15
      else if id = 16 then 17 else id⟩

def exNestCtx : Ctx := ⟨exNestG, 7, .ac, fun _ => true⟩

def exNestRoot : Node := ⟨7, .mset {1, 2, 3, 4, 5, 6}⟩

theorem exNest_member {id : NodeId} {m : Node} {g : C} (h : exNestCtx.IsMember id m g) :
    (g = 11 ∧ m.children = .mset {1, 2}) ∨ (g = 13 ∧ m.children = .mset {3, 4}) ∨
      (g = 15 ∧ m.children = .mset {11, 13}) ∨ (g = 17 ∧ m.children = .mset {1, 2, 3, 4, 5, 6}) := by
  obtain ⟨hm, -, hg, -⟩ := h
  simp only [exNestCtx, exNestG, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hm hg
  rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp_all

theorem otl_none_open {ctx : Ctx} {k : Nat} {P : Finset C} {ks v : List (C × Nat)}
    {ls : List LeafL} {o : Nat} (h : OTL ctx k P ks v ls o)
    (hno : ∀ e ∈ ks, ∀ id m, ¬ ctx.IsMember id m e.1) : v = scale k ks := by
  induction h with
  | nil => rfl
  | keep _ ih =>
      rw [ih (fun e he => hno e (List.mem_cons_of_mem _ he))]
      rfl
  | opn _ hmem _ _ _ _ =>
      exact absurd hmem (hno _ (List.mem_cons_self ..) _ _)

theorem ofEntries_scale_one (ks : List (C × Nat)) : ofEntries (scale 1 ks) = ofEntries ks := by
  simp [scale]

/-- The walk at the root opens nothing: its classes have no member. -/
theorem exNest_base {r : RecR} (h : r ∈ baseRecsR exNestCtx .both Laws.free exNestRoot) :
    r.2.2 = [] ∧ ofEntries r.1 = {1, 2, 3, 4, 5, 6} := by
  obtain ⟨v, -, hn, -, hneeds⟩ := mem_baseRecsR h
  obtain ⟨v', ls, o, hv, hn'⟩ := mem_baseRecsR_both h
  refine ⟨hneeds, ?_⟩
  have hk : kids exNestCtx.κ exNestRoot.children = Multiset.entries {1, 2, 3, 4, 5, 6} := rfl
  have hv' := otl_none_open hv (by
    intro e he id m hm
    rw [hk] at he
    have he1 := mem_entries_fst.1 (List.mem_map_of_mem (f := Prod.fst) he)
    rcases exNest_member hm with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ <;> rw [h1] at he1 <;>
      simp at he1)
  rw [ofEntries_free_ac hn', hv', ofEntries_scale_one, hk, ofEntries_entries]

/-- The invariant of the chains within one needed class: every class of the
view is a root class, or `G1` or `G2` and needed; at most six elements. -/
def ExNestInv (r : RecR) : Prop :=
  r.2.2.length ≤ 1 ∧ Multiset.card (ofEntries r.1) ≤ 6 ∧
    ∀ c ∈ ofEntries r.1, c ∈ ({1, 2, 3, 4, 5, 6} : Multiset C) ∨ ((c = 11 ∨ c = 13) ∧ c ∈ r.2.2)

theorem two_le_length {l : List C} {a b : C} (ha : a ∈ l) (hb : b ∈ l) (hab : a ≠ b) :
    2 ≤ l.length := by
  rcases l with _ | ⟨x, _ | ⟨y, l⟩⟩
  · simp at ha
  · simp only [List.mem_singleton] at ha hb; exact absurd (ha.trans hb.symm) hab
  · simp

theorem exNestInv_step {r r' : RecR} (hi : ExNestInv r)
    (h : RegroupStep exNestCtx .both 1 r r') : ExNestInv r' := by
  obtain ⟨hn, hcard, hcls⟩ := hi
  obtain ⟨hm, hg, hto, hle⟩ := h
  obtain ⟨h2, hsub, hne, rfl⟩ := hto
  simp only [ExNestInv, ofEntries_entries]
  refine ⟨hle, ?_, ?_⟩
  · rw [Multiset.card_add, Multiset.card_singleton, Multiset.card_sub hsub]
    have := Multiset.card_le_card hsub
    omega
  have hcases := exNest_member hm
  rcases hcases with ⟨rfl, hch⟩ | ⟨rfl, hch⟩ | ⟨rfl, hch⟩ | ⟨rfl, hch⟩ <;>
    simp only [exNestCtx, hch, kids, ofEntries_entries] at h2 hsub hne hle ⊢
  · -- `G1`: a class kept is still classified, `G1` is needed
    intro c hc
    rcases Multiset.mem_add.1 hc with hc | hc
    · rcases hcls c (Multiset.mem_of_le (Multiset.sub_le_self _ _) hc) with h | ⟨h1, h2⟩
      · exact Or.inl h
      · refine Or.inr ⟨h1, mem_needsAfter_iff.2 (Or.inr ⟨h2, ?_⟩)⟩
        rw [mem_entries_fst]; rcases h1 with rfl | rfl <;> decide
    · rw [Multiset.mem_singleton] at hc
      exact Or.inr ⟨Or.inl hc, mem_needsAfter_iff.2 (Or.inl hc)⟩
  · intro c hc
    rcases Multiset.mem_add.1 hc with hc | hc
    · rcases hcls c (Multiset.mem_of_le (Multiset.sub_le_self _ _) hc) with h | ⟨h1, h2⟩
      · exact Or.inl h
      · refine Or.inr ⟨h1, mem_needsAfter_iff.2 (Or.inr ⟨h2, ?_⟩)⟩
        rw [mem_entries_fst]; rcases h1 with rfl | rfl <;> decide
    · rw [Multiset.mem_singleton] at hc
      exact Or.inr ⟨Or.inr hc, mem_needsAfter_iff.2 (Or.inl hc)⟩
  · -- `G3` needs `G1` and `G2` both in the view, so both needed: two classes
    exfalso
    have h11 := hcls 11 (Multiset.mem_of_le hsub (by simp))
    have h13 := hcls 13 (Multiset.mem_of_le hsub (by simp))
    rcases h11 with h11 | ⟨-, h11⟩
    · simp at h11
    rcases h13 with h13 | ⟨-, h13⟩
    · simp at h13
    have := two_le_length h11 h13 (by decide)
    omega
  · -- the root's own group is the whole view
    exfalso
    apply hne
    refine Multiset.eq_of_le_of_card_le hsub ?_
    have : Multiset.card ({1, 2, 3, 4, 5, 6} : Multiset C) = 6 := rfl
    omega

theorem exNestInv_chain {r₀ r : RecR} (h : RegroupChain exNestCtx .both 1 r₀ r)
    (h₀ : ExNestInv r₀) : ExNestInv r := by
  induction h with
  | refl => exact h₀
  | tail _ hs ih => exact exNestInv_step ih hs

/-- **Counter-model: the per-item limit applies at every step of a chain.**
In `exNestG`, a chain of three regroupings takes the root's view
`{a, b, c, d, h, k}` to `{h, k, G3}` needing only `G3`, but its second view
`{h, k, G1, G2}` needs `G1` and `G2`. So the chain is within a limit of two,
and the enumeration with a limit of one (an atom with one item and a rest,
`(F x ..r)`) has no view holding `G3` at all: a match binding `x` to `G3`,
though its final record needs one class, is not found. The engine behaves
the same (`flatten_regroup_nested_limit.egg`). The chain statement
(`regroup_match_complete`) therefore bounds the needed classes at every
step, not only those still needed after the chain. -/
theorem regroup_nested_limit_counter :
    (∃ r₀ ∈ baseRecsR exNestCtx .both Laws.free exNestRoot, ∃ r,
      RegroupChain exNestCtx .both 2 r₀ r ∧ r.2.2 = [15] ∧ ofEntries r.1 = {5, 6, 15}) ∧
    ∀ w d, (w, d) ∈ enumerateR exNestCtx .both Laws.free 1 exNestRoot → 15 ∉ ofEntries w := by
  constructor
  · have hn : normalize exNestCtx.κ Laws.free (scale 1 (kids exNestCtx.κ exNestRoot.children)) =
        .node (Multiset.entries {1, 2, 3, 4, 5, 6}) := by
      have hk : kids exNestCtx.κ exNestRoot.children = Multiset.entries {1, 2, 3, 4, 5, 6} := rfl
      show normalize .ac Laws.free _ = _
      rw [normalize_free_ac_node (by rw [ofEntries_scale_one, hk, ofEntries_entries]; decide)]
      unfold coalesce
      rw [ofEntries_scale_one, hk, ofEntries_entries]
    have hmem : exNestCtx.IsMember 10 ⟨7, .mset {1, 2}⟩ 11 ∧
        exNestCtx.IsMember 12 ⟨7, .mset {3, 4}⟩ 13 ∧
        exNestCtx.IsMember 14 ⟨7, .mset {11, 13}⟩ 15 := by
      simp [Ctx.IsMember, exNestCtx, exNestG]
    refine ⟨_, kept_mem_baseRecsR hn, _, Relation.ReflTransGen.head
      (regroupStep_ac_of rfl hmem.1 rfl (ofEntries_entries _) (by decide) (by decide) (by decide)
        (by decide) (ns := [11]) (by simp [needsAfter]) (by decide)) <|
      Relation.ReflTransGen.head
      (regroupStep_ac_of rfl hmem.2.1 rfl (ofEntries_entries _) (by decide) (by decide) (by decide)
        (by decide) (ns := [11, 13]) (by simp [needsAfter, mem_entries_fst]) (by decide)) <|
      Relation.ReflTransGen.head
      (regroupStep_ac_of rfl hmem.2.2 rfl (ofEntries_entries _) (by decide) (by decide) (by decide)
        (by decide) (ns := [15]) (by simp [needsAfter, mem_entries_fst]) (by decide))
      Relation.ReflTransGen.refl, rfl, ?_⟩
    rw [ofEntries_entries]
    decide
  · intro w d h
    obtain ⟨r, hr, rfl⟩ := mem_enumerateFromR h
    obtain ⟨r₀, h₀, hr⟩ := (mem_regroupLevels_iff _ _ _ _ _ _ r).1 hr
    have hch := regroupChain_of_mem_levels _ (viewOK_base h₀) hr
    obtain ⟨hn0, ho0⟩ := exNest_base h₀
    obtain ⟨-, -, hcls⟩ := exNestInv_chain hch ⟨by rw [hn0]; simp, by rw [ho0]; rfl, by
      intro c hc; rw [ho0] at hc; exact Or.inl hc⟩
    intro h15
    rcases hcls 15 h15 with h | ⟨h, -⟩
    · simp at h
    · rcases h with h | h <;> exact absurd h (by decide)

/-! ## Nested prefixes of a left fold -/

/-- `Sub` (op 8) a left fold, classes `a, b, c, d = 1, …, 4`;
`G1 = 11 ∋ Sub[a, b]`, `G2 = 13 ∋ Sub[G1, c]`; the root `Sub[a, b, c, d]`
(node 14, class 15). -/
def exFoldNG : Graph :=
  ⟨[(10, ⟨8, .seq [1, 2]⟩), (12, ⟨8, .seq [11, 3]⟩), (14, ⟨8, .seq [1, 2, 3, 4]⟩)],
    fun id => if id = 10 then 11 else if id = 12 then 13 else if id = 14 then 15 else id⟩

def exFoldNCtx : Ctx := ⟨exFoldNG, 8, .assoc, fun _ => true⟩

def exFoldNRoot : Node := ⟨8, .seq [1, 2, 3, 4]⟩

/-- **Nested prefixes of a left fold are reached.** `(a - b) - c` in
`((a - b) - c) - d` is the class `G2 ∋ Sub[G1, c]`, a group of the view only
after `G1 ∋ Sub[a, b]` regroups the prefix `[a, b]`: the chain
`[a, b, c, d] → [G1, c, d] → [G2, d]` needs one class at each step, so even
an atom with one item (`(Sub x ..r)`) binds `x` to `G2`. -/
theorem regroup_fold_nested :
    ∃ d, ([(13, 1), (4, 1)], d) ∈ enumerateR exFoldNCtx .left Laws.free 1 exFoldNRoot ∧
      d.acceptsE .assoc [13] := by
  have hn : normalize exFoldNCtx.κ Laws.free (scale 1 (kids exFoldNCtx.κ exFoldNRoot.children)) =
      .node [(1, 1), (2, 1), (3, 1), (4, 1)] := by decide
  have hmem : exFoldNCtx.IsMember 10 ⟨8, .seq [1, 2]⟩ 11 ∧
      exFoldNCtx.IsMember 12 ⟨8, .seq [11, 3]⟩ 13 := by
    simp [Ctx.IsMember, exFoldNCtx, exFoldNG]
  exact regroup_view_complete (kept_mem_baseRecsR hn)
    (Relation.ReflTransGen.head (RegroupStep.mk (w' := [(11, 1), (3, 1), (4, 1)]) hmem.1
        (by decide) ⟨0, by decide⟩ (by decide)) <|
      Relation.ReflTransGen.head (RegroupStep.mk (w' := [(13, 1), (4, 1)]) hmem.2
        (by decide) ⟨0, by decide⟩ (by decide)) Relation.ReflTransGen.refl)
    (by decide)

end Semper.EMatch.Flatten
