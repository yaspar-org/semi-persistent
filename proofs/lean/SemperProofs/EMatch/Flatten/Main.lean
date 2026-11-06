import SemperProofs.EMatch.Flatten.Views
import SemperProofs.EMatch.Flatten.Canon
import SemperProofs.EMatch.Flatten.Enum
import SemperProofs.EMatch.Flatten.Interp
import SemperProofs.EMatch.Flatten.Refold

/-!
# `:flatten` views: final theorems

Re-exports, under the names of `spec-flatten.md` §4.3, the theorems proved
in `Flatten/{Enum,Interp,Refold}.lean`:

* `views_sound`, `views_complete`, `views_complete_within` (§4.3 a, b);
* `prune_irrelevant` (§2.3);
* `flatten_match_sound_ac/aci/assoc`, `flatten_match_complete_ac/aci/assoc`
  (§4.3 c): the plan fragment "flatten, then decompose on the view
  register" emits exactly the `MatchFlat` bindings;
* `demand_refold_ac` (spec lemma 9, restricted: laws-free operator, item
  patterns are variables, a rest variable is present, and the closed class
  is not itself taken; see the counterexample in `Refold.lean`), with
  `demand_refold_aci` and the two `refold_assoc_*` lemmas for the other
  kinds.
-/

namespace Semper.EMatch.Flatten

open Semper.EMatch

/-! ## (c) the interpreter fragment -/

alias flatten_match_sound_ac := flatten_ac_sound
alias flatten_match_complete_ac := flatten_ac_complete
alias flatten_match_sound_aci := flatten_aci_sound
alias flatten_match_complete_aci := flatten_aci_complete
alias flatten_match_sound_assoc := flatten_assoc_sound
alias flatten_match_complete_assoc := flatten_assoc_complete

/-! ## Lemma 9: demand refolding (restricted) -/

/-- Lemma 9 for a laws-free AC operator. A raw view `v` of `n` with a leaf
group `g` that no item takes, matched by an AC atom whose item patterns are
variables and which has a rest variable: the leaf is an opening of some
`f`-member `m` of a class `X`, and closing it gives a raw view of `n`
(`v₁ ++ (X, k') :: v₂`) on which the same item bindings match, with the
rest being the old rest with the leaf's elements replaced by `X^k'`,
**provided the closed class `X` is not itself taken**. Without that
proviso the statement is false (`Refold.lean`, `refold_ac` docstring).
The refolded raw view may normalize to a non-node (a single class), in
which case it is not a view of `n` (spec §5 Q3). -/
theorem demand_refold_ac {ctx : Ctx} {n : Node} {v w : List (C × Nat)}
    {ls : List (List C)} {g : List C} {f : Sym} {elems : List (Pat × Mult)} {r : Var}
    {σ : Binding} {taken : List C}
    (hv : RawView ctx n v ls) (hg : g ∈ ls)
    (hn : normalize .ac Laws.free v = .node w)
    (helems : ∀ e ∈ elems, ∃ x, e.1 = Pat.var x)
    (hm : MatchV ctx.G (.ac f elems (some r)) (ofView .ac w) σ taken)
    (hmiss : ∀ c ∈ g, c ∉ taken) :
    ∃ (v₁ v₂ : List (C × Nat)) (X : C) (k' : Nat) (id : NodeId) (m : Node)
      (ls' : List (List C)),
      ctx.IsMember id m X ∧ g = (kids ctx.κ m.children).map Prod.fst ∧
      v = v₁ ++ scale k' (kids ctx.κ m.children) ++ v₂ ∧
      RawView ctx n (v₁ ++ (X, k') :: v₂) ls' ∧
      (X ∉ taken →
        MatchV ctx.G (.ac f elems (some r)) (.mset (ofEntries (v₁ ++ (X, k') :: v₂)))
          (σ.setRest r ((ofEntries (v₁ ++ (X, k') :: v₂)).filter (fun c => c ∉ taken)))
          taken ∧
        (ofEntries (v₁ ++ (X, k') :: v₂)).filter (fun c => c ∉ taken) =
          ((ofEntries v).filter (fun c => c ∉ taken)) -
            ofEntries (scale k' (kids ctx.κ m.children)) + Multiset.replicate k' X) := by
  obtain ⟨v₁, v₂, X, k', id, m, ls', hmem, hgeq, hveq, hot⟩ := OT.refold hv hg
  refine ⟨v₁, v₂, X, k', id, m, ls', hmem, hgeq, hveq, hot, fun hX => ?_⟩
  have hm' : MatchV ctx.G (.ac f elems (some r))
      (.mset (ofEntries (v₁ ++ scale k' (kids ctx.κ m.children) ++ v₂))) σ taken := by
    have : ofView .ac w = .mset (ofEntries v) := by
      simp [ofView, ofEntries_free_ac hn]
    rw [this, hveq] at hm
    exact hm
  have hleaf : ∀ e ∈ scale k' (kids ctx.κ m.children), e.1 ∉ taken := by
    intro e he
    apply hmiss
    rw [hgeq, ← map_fst_scale k']
    exact List.mem_map_of_mem he
  obtain ⟨h₁, h₂⟩ := refold_ac helems hm' hleaf hX
  refine ⟨h₁, ?_⟩
  rw [h₂, hveq]

/-- Lemma 9 for a laws-free ACI operator: no proviso on the closed class. -/
theorem demand_refold_aci {ctx : Ctx} {n : Node} {v w : List (C × Nat)}
    {ls : List (List C)} {g : List C} {f : Sym} {elems : List Pat} {r : Var}
    {σ : Binding} {taken : List C}
    (hv : RawView ctx n v ls) (hg : g ∈ ls)
    (hn : normalize .aci Laws.free v = .node w)
    (helems : ∀ p ∈ elems, ∃ x, p = Pat.var x)
    (hm : MatchV ctx.G (.aci f elems (some r)) (ofView .aci w) σ taken)
    (hmiss : ∀ c ∈ g, c ∉ taken) :
    ∃ (v₁ v₂ : List (C × Nat)) (X : C) (k' : Nat) (id : NodeId) (m : Node)
      (ls' : List (List C)),
      ctx.IsMember id m X ∧ g = (kids ctx.κ m.children).map Prod.fst ∧
      v = v₁ ++ scale k' (kids ctx.κ m.children) ++ v₂ ∧
      RawView ctx n (v₁ ++ (X, k') :: v₂) ls' ∧
      MatchV ctx.G (.aci f elems (some r))
        (.set ((v₁ ++ (X, k') :: v₂).map Prod.fst).toFinset)
        (σ.setSetRest r ((((v₁ ++ (X, k') :: v₂).map Prod.fst).toFinset).filter
          (fun c => c ∉ taken))) taken := by
  obtain ⟨v₁, v₂, X, k', id, m, ls', hmem, hgeq, hveq, hot⟩ := OT.refold hv hg
  refine ⟨v₁, v₂, X, k', id, m, ls', hmem, hgeq, hveq, hot, ?_⟩
  have hw : w = dedupAci v := (normalize_free_node.1 hn).1
  have hm' : MatchV ctx.G (.aci f elems (some r))
      (.set ((v₁ ++ scale k' (kids ctx.κ m.children) ++ v₂).map Prod.fst).toFinset)
      σ taken := by
    have : ofView .aci w = .set (v.map Prod.fst).toFinset := by
      simp [ofView, hw, dedupAci, Function.comp_def, Finset.sort_toFinset]
    rw [this, hveq] at hm
    exact hm
  have hleaf : ∀ e ∈ scale k' (kids ctx.κ m.children), e.1 ∉ taken := by
    intro e he
    apply hmiss
    rw [hgeq, ← map_fst_scale k']
    exact List.mem_map_of_mem he
  exact refold_aci helems hm' hleaf

end Semper.EMatch.Flatten
