import SemperProofs.EMatch.Flatten.Views
import SemperProofs.EMatch.Proofs.DecomposeAC

/-!
# `:flatten` views: refolding a leaf

Two groups of facts about opening trees and flattened matches.

* Tree facts: a tree with no leaf group opens nothing (`OT.all_kept`), and
  a leaf instance of a tree can be closed again, giving a tree of the same
  positions whose raw view replaces the leaf's children by the leaf's class
  (`OT.refold`).
* The laws-free demand refold (spec lemma 9, restricted to item patterns
  that are variables): a match on a raw view whose leaf group is not hit by
  the taken classes is still a match on the refolded view, with the rest
  updated (`refold_ac`, `refold_aci`, `refold_assoc_pre`,
  `refold_assoc_suf`).
-/

namespace Semper.EMatch.Flatten

open Semper.EMatch

/-! ## Tree facts -/

theorem leafify_ne_nil (v : List (C × Nat)) (ls : List (List C)) : leafify v ls ≠ [] := by
  unfold leafify
  split <;> simp_all

theorem map_fst_scale (k : Nat) (ks : List (C × Nat)) :
    (scale k ks).map Prod.fst = ks.map Prod.fst := by
  simp [scale]

theorem OT.all_kept_aux {ctx : Ctx} {k : Nat} {P : Finset C} {ks v : List (C × Nat)}
    {ls : List (List C)} (h : OT ctx k P ks v ls) (hls : ls = []) : v = scale k ks := by
  induction h with
  | nil => rfl
  | keep _ ih =>
      subst hls
      simp [scale, ih rfl]
  | opn _ _ _ _ _ _ =>
      exact absurd (List.append_eq_nil_iff.mp hls).1 (leafify_ne_nil _ _)

/-- A tree with no leaf group opens nothing: every position is kept. -/
theorem OT.all_kept {ctx : Ctx} {k : Nat} {P : Finset C} {ks v : List (C × Nat)}
    (h : OT ctx k P ks v []) : v = scale k ks :=
  OT.all_kept_aux h rfl

/-- Closing the leaf instance whose group is `g`: it is an `opn` node whose
subtree has no leaf group, so it kept all of `m`'s children scaled by some
`k'`; replacing it by `keep` gives a tree over the same positions. -/
theorem OT.refold {ctx : Ctx} {k : Nat} {P : Finset C} {ks v : List (C × Nat)}
    {ls : List (List C)} {g : List C} (h : OT ctx k P ks v ls) (hg : g ∈ ls) :
    ∃ (v₁ v₂ : List (C × Nat)) (X : C) (k' : Nat) (id : NodeId) (m : Node)
      (ls' : List (List C)),
      ctx.IsMember id m X ∧ g = (kids ctx.κ m.children).map Prod.fst ∧
      v = v₁ ++ scale k' (kids ctx.κ m.children) ++ v₂ ∧
      OT ctx k P ks (v₁ ++ (X, k') :: v₂) ls' := by
  induction h with
  | nil => simp at hg
  | @keep k P X j rest v₂ l₂ _ ih =>
      obtain ⟨v₁', v₂', X', k'', id, m, ls', hmem, hgeq, hv, ht⟩ := ih hg
      refine ⟨(X, k * j) :: v₁', v₂', X', k'', id, m, ls', hmem, hgeq, ?_, ?_⟩
      · subst hv; simp
      · exact OT.keep ht
  | @opn k P X j rest id m v₁ v₂ l₁ l₂ hXP hmem h₁ h₂ ih₁ ih₂ =>
      rcases List.mem_append.mp hg with hg₁ | hg₂
      · by_cases hl₁ : l₁ = []
        · subst hl₁
          simp only [leafify, ite_true, List.mem_singleton] at hg₁
          subst hg₁
          have hv₁ := OT.all_kept h₁
          refine ⟨[], v₂, X, k * j, id, m, l₂, hmem, ?_, ?_, ?_⟩
          · rw [hv₁, map_fst_scale]
          · rw [hv₁]; rfl
          · exact OT.keep h₂
        · simp only [leafify, hl₁, ↓reduceIte] at hg₁
          obtain ⟨v₁', v₂', X', k'', id', m', ls', hmem', hgeq, hv, ht⟩ := ih₁ hg₁
          refine ⟨v₁', v₂' ++ v₂, X', k'', id', m',
            leafify (v₁' ++ (X', k'') :: v₂') ls' ++ l₂, hmem', hgeq, ?_, ?_⟩
          · subst hv; simp
          · have := OT.opn hXP hmem ht h₂
            simpa using this
      · obtain ⟨v₁', v₂', X', k'', id', m', ls', hmem', hgeq, hv, ht⟩ := ih₂ hg₂
        refine ⟨v₁ ++ v₁', v₂', X', k'', id', m', leafify v₁ l₁ ++ ls', hmem', hgeq, ?_, ?_⟩
        · subst hv; simp
        · have := OT.opn hXP hmem h₁ ht
          simpa using this

/-! ## Multiset helpers -/

theorem ofEntries_append (l₁ l₂ : List (C × Nat)) :
    ofEntries (l₁ ++ l₂) = ofEntries l₁ + ofEntries l₂ := by
  simp [ofEntries]

theorem exists_mem_ofEntries {c : C} {l : List (C × Nat)} (h : c ∈ ofEntries l) :
    ∃ e ∈ l, e.1 = c := by
  induction l with
  | nil => simp [ofEntries] at h
  | cons e l ih =>
      rw [ofEntries_cons, Multiset.mem_add] at h
      rcases h with h | h
      · exact ⟨e, List.mem_cons_self .., (Multiset.mem_replicate.mp h).2.symm⟩
      · obtain ⟨e', he', hc⟩ := ih h
        exact ⟨e', List.mem_cons_of_mem _ he', hc⟩

theorem count_ofEntries_eq_zero {c : C} {l : List (C × Nat)} (h : ∀ e ∈ l, e.1 ≠ c) :
    (ofEntries l).count c = 0 := by
  rw [Multiset.count_eq_zero]
  intro hc
  obtain ⟨e, he, hec⟩ := exists_mem_ofEntries hc
  exact h e he hec

/-! ## Binding helpers -/

theorem MatchC.var_inv {G : Graph} {x : Var} {c : C} {σ : Binding}
    (h : MatchC G (.var x) c σ) : σ.cls x = some c := by
  cases h with
  | var h => exact h
  | app _ _ hh _ => simp [Pat.head] at hh

theorem MultOk_setRest {σ : Binding} {r : Var} {m : Multiset C} {μ : Mult} {n : Nat} :
    MultOk (σ.setRest r m) μ n ↔ MultOk σ μ n := by
  cases μ <;> exact Iff.rfl

theorem SeqRestOk_setSeqRest {σ : Binding} {rp : Var} {l : List C} {suf : Option Var}
    {w : List C} (hne : ∀ rs, suf = some rs → rs ≠ rp) (h : SeqRestOk σ suf w) :
    SeqRestOk (σ.setSeqRest rp l) suf w := by
  cases suf with
  | none => exact h
  | some rs =>
      show Function.update σ.seqRest rp (some l) rs = some w
      rw [Function.update_of_ne (hne rs rfl)]
      exact h

/-! ## The laws-free demand refold, per kind -/

/-- AC. The hypothesis `hX : X ∉ taken` is necessary: with
`n = Plus{Y, Z}`, `Z ∋ Plus{Y, d}`, `Y ∋ Plus{X, c}`, the tree opening both
`Y` and `Z` with the `Y` under `Z` kept gives the raw view `{X, c, Y, d}`;
the pattern `(Plus y d' ..rest)` with `y = Y`, `d' = d` has `taken = [Y, d]`
and the leaf `[X, c]` is not hit, but refolding the `Y`-leaf gives
`{Y : 2, d}`, where the exact-1 item `y` cannot take `Y`. -/
theorem refold_ac {G : Graph} {f : Sym} {elems : List (Pat × Mult)} {r : Var} {σ : Binding}
    {taken : List C} {v₁ v₂ leaf : List (C × Nat)} {X : C} {k' : Nat}
    (helems : ∀ e ∈ elems, ∃ x, e.1 = Pat.var x)
    (hm : MatchV G (.ac f elems (some r)) (.mset (ofEntries (v₁ ++ leaf ++ v₂))) σ taken)
    (hleaf : ∀ e ∈ leaf, e.1 ∉ taken) (hX : X ∉ taken) :
    MatchV G (.ac f elems (some r)) (.mset (ofEntries (v₁ ++ (X, k') :: v₂)))
      (σ.setRest r ((ofEntries (v₁ ++ (X, k') :: v₂)).filter (fun c => c ∉ taken))) taken ∧
    (ofEntries (v₁ ++ (X, k') :: v₂)).filter (fun c => c ∉ taken) =
      ((ofEntries (v₁ ++ leaf ++ v₂)).filter (fun c => c ∉ taken)) - ofEntries leaf +
        Multiset.replicate k' X := by
  have hcount : ∀ c ∈ taken,
      (ofEntries (v₁ ++ (X, k') :: v₂)).count c = (ofEntries (v₁ ++ leaf ++ v₂)).count c := by
    intro c hc
    have hcX : X ≠ c := fun h => hX (h ▸ hc)
    have hl : (ofEntries leaf).count c = 0 :=
      count_ofEntries_eq_zero (fun e he h => hleaf e he (h ▸ hc))
    simp only [ofEntries_append, ofEntries_cons, Multiset.count_add, Multiset.count_replicate,
      hcX, ↓reduceIte, hl]
    omega
  cases hm with
  | ac hnd hlen hmem hmatch hmult hrest =>
    refine ⟨MatchV.ac hnd hlen ?_ ?_ ?_ ?_, ?_⟩
    · intro c hc
      rw [← Multiset.count_pos, hcount c hc, Multiset.count_pos]
      exact hmem c hc
    · intro et het
      obtain ⟨x, hx⟩ := helems et.1 (List.of_mem_zip het).1
      have := hmatch et het
      rw [hx] at this ⊢
      have hc := MatchC.var_inv this
      exact MatchC.var hc
    · intro et het
      rw [MultOk_setRest, hcount et.2 (List.of_mem_zip het).2]
      exact hmult et het
    · simp [MsetRestOk, Binding.setRest]
    · have hl : (ofEntries leaf).filter (fun c => c ∉ taken) = ofEntries leaf := by
        rw [Multiset.filter_eq_self]
        intro c hc
        obtain ⟨e, he, hec⟩ := exists_mem_ofEntries hc
        rw [← hec]
        exact hleaf e he
      have hXr : (Multiset.replicate k' X).filter (fun c => c ∉ taken) =
          Multiset.replicate k' X := by
        rw [Multiset.filter_eq_self]
        intro c hc
        rw [(Multiset.mem_replicate.mp hc).2]
        exact hX
      have key : ∀ (a b l : Multiset C), a + l + b - l = a + b := fun a b l => by
        rw [add_right_comm, add_tsub_cancel_right]
      simp only [ofEntries_append, ofEntries_cons, Multiset.filter_add, hl, hXr]
      rw [key]
      abel

/-- ACI. Here `X ∈ taken` is allowed: `X` is in the new set, and a taken
class other than `X` is in `v₁ ++ v₂` (it is not a leaf class), hence in the
new set. -/
theorem refold_aci {G : Graph} {f : Sym} {elems : List Pat} {r : Var} {σ : Binding}
    {taken : List C} {v₁ v₂ leaf : List (C × Nat)} {X : C} {k' : Nat}
    (helems : ∀ p ∈ elems, ∃ x, p = Pat.var x)
    (hm : MatchV G (.aci f elems (some r)) (.set ((v₁ ++ leaf ++ v₂).map Prod.fst).toFinset)
      σ taken)
    (hleaf : ∀ e ∈ leaf, e.1 ∉ taken) :
    MatchV G (.aci f elems (some r)) (.set ((v₁ ++ (X, k') :: v₂).map Prod.fst).toFinset)
      (σ.setSetRest r ((((v₁ ++ (X, k') :: v₂).map Prod.fst).toFinset).filter
        (fun c => c ∉ taken))) taken := by
  cases hm with
  | aci hnd hlen hmem hmatch hrest =>
    refine MatchV.aci hnd hlen ?_ ?_ ?_
    · intro c hc
      have h := hmem c hc
      simp only [List.map_append, List.mem_toFinset, List.mem_append, List.map_cons,
        List.mem_cons] at h ⊢
      rcases h with (h | h) | h
      · exact Or.inl h
      · exfalso
        obtain ⟨e, he, rfl⟩ := List.mem_map.mp h
        exact hleaf e he hc
      · exact Or.inr (Or.inr h)
    · intro et het
      obtain ⟨x, hx⟩ := helems et.1 (List.of_mem_zip het).1
      have := hmatch et het
      rw [hx] at this ⊢
      have hc := MatchC.var_inv this
      exact MatchC.var hc
    · simp [SetRestOk, Binding.setSetRest]

/-- The ACI rest after the refold, when `X` is not taken: the old rest minus
the leaf classes that occur nowhere else, plus `X`. -/
theorem refold_aci_rest {v₁ v₂ leaf : List (C × Nat)} {X : C} {k' : Nat} {taken : List C}
    (hleaf : ∀ e ∈ leaf, e.1 ∉ taken) (hX : X ∉ taken) :
    (((v₁ ++ (X, k') :: v₂).map Prod.fst).toFinset).filter (fun c => c ∉ taken) =
      insert X (((((v₁ ++ leaf ++ v₂).map Prod.fst).toFinset).filter (fun c => c ∉ taken)) \
        ((leaf.map Prod.fst).filter (fun c => c ∉ (v₁ ++ v₂).map Prod.fst)).toFinset) := by
  ext c
  have hl : c ∈ leaf.map Prod.fst → c ∉ taken := by
    intro h
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp h
    exact hleaf e he
  by_cases hcX : c = X
  · subst hcX
    simp [hX]
  · simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_sdiff, List.mem_toFinset,
      List.map_append, List.map_cons, List.mem_append, List.mem_cons, List.mem_filter,
      decide_eq_true_eq, hcX, false_or]
    tauto

/-- Inversion of the assoc clause. -/
theorem MatchV.assoc_inv {G : Graph} {f : Sym} {pre suf : Option Var} {args : List Pat}
    {s : List C} {σ : Binding} {taken : List C}
    (hm : MatchV G (.assoc f pre args suf) (.seq s) σ taken) :
    ∃ u w, s = u ++ taken ++ w ∧ args.length = taken.length ∧ SeqRestOk σ pre u ∧
      SeqRestOk σ suf w ∧ ∀ pc ∈ args.zip taken, MatchC G pc.1 pc.2 σ := by
  cases hm with
  | assoc hlen hpre hsuf hargs => exact ⟨_, _, rfl, hlen, hpre, hsuf, hargs⟩

/-- Assoc, leaf block in the prefix: the prefix rest `rp` is bound to
`a ++ leaf ++ b`; the refolded sequence has prefix `a ++ X :: b`. The
suffix rest, if any, is a different variable. -/
theorem refold_assoc_pre {G : Graph} {f : Sym} {rp : Var} {suf : Option Var} {args : List Pat}
    {σ : Binding} {s a leaf b w mid : List C} {X : C}
    (helems : ∀ p ∈ args, ∃ x, p = Pat.var x)
    (hne : ∀ rs, suf = some rs → rs ≠ rp)
    (hm : MatchV G (.assoc f (some rp) args suf) (.seq s) σ mid)
    (hpre : σ.seqRest rp = some (a ++ leaf ++ b))
    (hsuf : SeqRestOk σ suf w) :
    s = (a ++ leaf ++ b) ++ mid ++ w ∧
    MatchV G (.assoc f (some rp) args suf) (.seq ((a ++ X :: b) ++ mid ++ w))
      (σ.setSeqRest rp (a ++ X :: b)) mid := by
  obtain ⟨u, w', hs, hlen, hu, hw, hargs⟩ := MatchV.assoc_inv hm
  have hu' : u = a ++ leaf ++ b := by
    simp only [SeqRestOk] at hu
    rw [hu] at hpre
    exact Option.some.inj hpre
  have hw' : w' = w := by
    cases suf with
    | none =>
        simp only [SeqRestOk] at hw hsuf
        rw [hw, hsuf]
    | some rs =>
        simp only [SeqRestOk] at hw hsuf
        rw [hw] at hsuf
        exact Option.some.inj hsuf
  subst hu' hw'
  refine ⟨hs, MatchV.assoc hlen ?_ (SeqRestOk_setSeqRest hne hsuf) ?_⟩
  · simp [SeqRestOk, Binding.setSeqRest]
  · intro pc hpc
    obtain ⟨x, hx⟩ := helems pc.1 (List.of_mem_zip hpc).1
    have := hargs pc hpc
    rw [hx] at this ⊢
    have hc := MatchC.var_inv this
    exact MatchC.var hc

/-- Assoc, leaf block in the suffix: symmetric to `refold_assoc_pre`. -/
theorem refold_assoc_suf {G : Graph} {f : Sym} {pre : Option Var} {rs : Var} {args : List Pat}
    {σ : Binding} {s u a leaf b mid : List C} {X : C}
    (helems : ∀ p ∈ args, ∃ x, p = Pat.var x)
    (hne : ∀ rp, pre = some rp → rp ≠ rs)
    (hm : MatchV G (.assoc f pre args (some rs)) (.seq s) σ mid)
    (hpre : SeqRestOk σ pre u)
    (hsuf : σ.seqRest rs = some (a ++ leaf ++ b)) :
    s = u ++ mid ++ (a ++ leaf ++ b) ∧
    MatchV G (.assoc f pre args (some rs)) (.seq (u ++ mid ++ (a ++ X :: b)))
      (σ.setSeqRest rs (a ++ X :: b)) mid := by
  obtain ⟨u', w, hs, hlen, hu, hw, hargs⟩ := MatchV.assoc_inv hm
  have hw' : w = a ++ leaf ++ b := by
    simp only [SeqRestOk] at hw
    rw [hw] at hsuf
    exact Option.some.inj hsuf
  have hu' : u' = u := by
    cases pre with
    | none =>
        simp only [SeqRestOk] at hu hpre
        rw [hu, hpre]
    | some rp =>
        simp only [SeqRestOk] at hu hpre
        rw [hu] at hpre
        exact Option.some.inj hpre
  subst hw' hu'
  refine ⟨hs, MatchV.assoc hlen (SeqRestOk_setSeqRest hne hpre) ?_ ?_⟩
  · simp [SeqRestOk, Binding.setSeqRest]
  · intro pc hpc
    obtain ⟨x, hx⟩ := helems pc.1 (List.of_mem_zip hpc).1
    have := hargs pc hpc
    rw [hx] at this ⊢
    have hc := MatchC.var_inv this
    exact MatchC.var hc

end Semper.EMatch.Flatten
