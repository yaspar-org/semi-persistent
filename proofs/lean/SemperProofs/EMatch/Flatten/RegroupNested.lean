import SemperProofs.EMatch.Flatten.RegroupChain

/-!
# `:flatten`: nested groups and the per-item limit

Two instances of the chain theorems of `RegroupChain.lean`:

* `regroup_nested_matches`: the per-item limit bounds only the classes the
  last record of a chain needs. `G3 ∋ F{G1, G2}` with `G1 ∋ F{a, b}` and
  `G2 ∋ F{c, d}`: the chain to `{h, k, G3}` ends needing `G3` alone but
  passes through `{h, k, G1, G2}`, which needs two classes; with a limit of
  one (an atom with one item and a rest, `(F x ..r)`) the view holding `G3`
  is enumerated and accepts `x = G3` (`flatten_regroup_nested_needs.egg`);
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

/-- A declarative AC step from concrete multisets. -/
theorem regroupStep_ac_of {ctx : Ctx} (hκ : ctx.κ = .ac) {dir : Dir} {r : RecR}
    {id : NodeId} {m : Node} {g : C} {M W : Multiset C} (hm : ctx.IsMember id m g)
    (hkids : m.children = .mset M) (hW : ofEntries r.1 = W) (hg : g ∉ M)
    (h2 : 2 ≤ Multiset.card M) (hle : M ≤ W) (hne : M ≠ W) {ns : List C}
    (hns : needsAfter g ((Multiset.entries M).map Prod.fst)
      ((Multiset.entries (W - M + {g})).map Prod.fst) r.2.2 = ns) :
    RegroupStep ctx dir r
      (Multiset.entries (W - M + {g}), r.2.1.map (addG g ((Multiset.entries M).map Prod.fst)
        ((Multiset.entries (W - M + {g})).map Prod.fst)), ns) := by
  have hk : kids ctx.κ m.children = Multiset.entries M := by rw [hκ, hkids]; rfl
  have h := @RegroupStep.mk ctx dir r id m g (Multiset.entries (W - M + {g})) hm
  rw [hk, hκ, hns] at h
  refine h (by rwa [mem_entries_fst]) ?_
  show 2 ≤ _ ∧ _
  rw [ofEntries_entries, hW]
  exact ⟨h2, hle, hne, rfl⟩

/-! ## A nested group, AC -/

/-- `F` (op 7) AC, classes `a, b, c, d, h, k = 1, …, 6`; `G1 = 11 ∋ F{a, b}`,
`G2 = 13 ∋ F{c, d}`, `G3 = 15 ∋ F{G1, G2}`; the root `F{a, b, c, d, h, k}`
(node 16, class 17). The class `G3` spells `F{a, b, c, d}` only through the
nested groups `G1` and `G2` (`flatten_regroup_nested_needs.egg`). -/
def exNestG : Graph :=
  ⟨[(10, ⟨7, .mset {1, 2}⟩), (12, ⟨7, .mset {3, 4}⟩), (14, ⟨7, .mset {11, 13}⟩),
    (16, ⟨7, .mset {1, 2, 3, 4, 5, 6}⟩)],
    fun id => if id = 10 then 11 else if id = 12 then 13 else if id = 14 then 15
      else if id = 16 then 17 else id⟩

def exNestCtx : Ctx := ⟨exNestG, 7, .ac, fun _ => true⟩

def exNestRoot : Node := ⟨7, .mset {1, 2, 3, 4, 5, 6}⟩

theorem ofEntries_scale_one (ks : List (C × Nat)) : ofEntries (scale 1 ks) = ofEntries ks := by
  simp [scale]

/-- **Nested groups match within the per-item limit of the last record.** In
`exNestG`, a chain of three regroupings takes the root's view
`{a, b, c, d, h, k}` to `{h, k, G3}` needing only `G3`; its second view
`{h, k, G1, G2}` needs `G1` and `G2`, past a limit of one. The enumeration
with a limit of one (an atom with one item and a rest, `(F x ..r)`) has the
view `{h, k, G3}`, and its demand accepts `x = G3`: the limit bounds the
classes the last record needs, not those of the records in between. The
engine finds the same match (`flatten_regroup_nested_needs.egg`). -/
theorem regroup_nested_matches :
    ∃ w d, (w, d) ∈ enumerateR exNestCtx .both Laws.free 1 exNestRoot ∧
      ofEntries w = {5, 6, 15} ∧ d.acceptsE .ac [15] := by
  have hn : normalize exNestCtx.κ Laws.free (scale 1 (kids exNestCtx.κ exNestRoot.children)) =
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
  obtain ⟨r, hch, hneeds, hleaves, hw⟩ : ∃ r, RegroupChain exNestCtx .both
      (Multiset.entries {1, 2, 3, 4, 5, 6}, [], []) r ∧ r.2.2 = [15] ∧ r.2.1 = [] ∧
      ofEntries r.1 = {5, 6, 15} := by
    refine ⟨_, Relation.ReflTransGen.head
      (regroupStep_ac_of rfl hmem.1 rfl (ofEntries_entries _) (by decide) (by decide) (by decide)
        (by decide) (ns := [11]) (by simp [needsAfter, mem_entries_fst, -List.mem_map])) <|
      Relation.ReflTransGen.head
      (regroupStep_ac_of rfl hmem.2.1 rfl (ofEntries_entries _) (by decide) (by decide) (by decide)
        (by decide) (ns := [11, 13]) (by simp [needsAfter, mem_entries_fst, -List.mem_map])) <|
      Relation.ReflTransGen.head
      (regroupStep_ac_of rfl hmem.2.2 rfl (ofEntries_entries _) (by decide) (by decide) (by decide)
        (by decide) (ns := [15]) (by simp [needsAfter, mem_entries_fst, -List.mem_map]))
      Relation.ReflTransGen.refl, rfl, rfl, ?_⟩
    rw [ofEntries_entries]
    decide
  obtain ⟨d, hd, hacc⟩ := regroup_view_complete (limit := 1) (taken := [15])
    (kept_mem_baseRecsR hn) hch (by rw [hneeds]; decide)
    (by rw [RecR.alt, hneeds, hleaves]; simp [needLeaf_okE])
  exact ⟨r.1, d, hd, hw, hacc⟩

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
        (by decide) ⟨0, by decide⟩) <|
      Relation.ReflTransGen.head (RegroupStep.mk (w' := [(13, 1), (4, 1)]) hmem.2
        (by decide) ⟨0, by decide⟩) Relation.ReflTransGen.refl)
    (by decide) (by decide)

end Semper.EMatch.Flatten
