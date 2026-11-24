import SemperProofs.EMatch.Env.Lemmas

/-!
# `DecomposeAC`: the executor's `decompose_ac_elem` refines `decomposeAC`

Restore and membership for `execAC` (`Exec.lean`), for a residual with
canonical and distinct classes (H2), given the continuation specification.
-/

namespace Semper.EMatch.Env

open Semper.EMatch

/-! ## Helpers -/

/-- `set_mult` for the annotation keeps the environment bounded when the
multiplicity variable, if any, is in `B`. -/
theorem EnvOk.setMultOf {e : Env} {B : List Var} (h : EnvOk e B) {μ : Mult}
    (hμ : ∀ k lo hi, μ = .var k lo hi → k ∈ B) (m : Nat) : EnvOk (setMultOf e μ m) B := by
  cases μ with
  | exact n => exact h
  | var k lo hi => exact h.setMult (hμ k lo hi rfl) m

/-- No entry of class `c`: a `find?` whose test needs class `c` fails. -/
theorem find?_class_eq_none {c : C} {res : List (C × Nat)} (f : C × Nat → Bool)
    (h : c ∉ res.map (·.1)) (hf : ∀ p, p.1 ≠ c → f p = false) :
    res.find? f = none := by
  rw [List.find?_eq_none]
  intro p hp
  have : p.1 ≠ c := fun h' => h (List.mem_map.mpr ⟨p, hp, h'⟩)
  simp [hf p this]

/-- On a residual with distinct classes, searching the class `c` under a
test `P` that rejects `0` is searching the live entry of class `c` and
testing it. -/
theorem find?_nodup_class (c : C) (res : List (C × Nat)) (P : Nat → Bool)
    (hnd : (res.map (·.1)).Nodup) (h0 : P 0 = false) :
    res.find? (fun p => p.1 = c ∧ P p.2) =
      match res.find? (fun p => p.1 = c ∧ p.2 ≠ 0) with
      | some p => if P p.2 then some p else none
      | none => none := by
  induction res with
  | nil => rfl
  | cons q res ih =>
      simp only [List.map_cons, List.nodup_cons] at hnd
      by_cases hq : q.1 = c
      · have hn : c ∉ res.map (·.1) := hq ▸ hnd.1
        have hn1 : res.find? (fun p => p.1 = c ∧ P p.2) = none :=
          find?_class_eq_none _ hn (fun p hp => by simp [hp])
        have hn2 : res.find? (fun p => p.1 = c ∧ p.2 ≠ 0) = none :=
          find?_class_eq_none _ hn (fun p hp => by simp [hp])
        by_cases hP : P q.2 = true
        · have hz : q.2 ≠ 0 := by
            intro hz; rw [hz, h0] at hP; exact Bool.false_ne_true hP
          rw [List.find?_cons_of_pos (by simp [hq, hP]),
            List.find?_cons_of_pos (by simp [hq, hz])]
          simp [hP]
        · rw [List.find?_cons_of_neg (by simp [hP]), hn1]
          by_cases hz : q.2 = 0
          · rw [List.find?_cons_of_neg (by simp [hz]), hn2]
          · rw [List.find?_cons_of_pos (by simp [hq, hz])]
            simp [hP]
      · rw [List.find?_cons_of_neg (by simp [hq]), List.find?_cons_of_neg (by simp [hq])]
        exact ih hnd.2

/-- Membership in a `flatMap` continued by `F`, entry by entry. -/
theorem mem_flatMap_iff_of_entries {α β γ : Type} (as : List α) (f : α → List β)
    (g : α → List γ) (F : β → List γ) (σ : γ)
    (h : ∀ a ∈ as, σ ∈ g a ↔ ∃ σ' ∈ f a, σ ∈ F σ') :
    σ ∈ as.flatMap g ↔ ∃ σ' ∈ as.flatMap f, σ ∈ F σ' := by
  simp only [List.mem_flatMap]
  constructor
  · rintro ⟨a, ha, hσ⟩
    obtain ⟨σ', hσ', hF⟩ := (h a ha).1 hσ
    exact ⟨σ', ⟨a, ha, hσ'⟩, hF⟩
  · rintro ⟨σ', ⟨a, ha, hσ'⟩, hF⟩
    exact ⟨a, ha, (h a ha).2 ⟨σ', hσ', hF⟩⟩


/-- `decompose_ac_elem` restores the environment and emits the members of
the reference `decomposeAC` continued by `F`. Hypotheses: `e` is bounded
by the continuation's set `Bf`, which contains the variables the step
binds; the rest span is empty on entry; element variables are class
variables and no annotation is `exact 0`; the residual's classes are
canonical and distinct. -/
theorem execAC_spec (G : Graph) (κ : Var → Bool) {k : Cont} {Bf : List Var}
    {F : Binding → List Binding} (hk : ContSpec G κ k Bf F)
    (elems : List (Var × Mult)) (rest : Option Var) (res : List (C × Nat)) (e : Env)
    (he : EnvOk e Bf)
    (hrest : ∀ r ∈ rest, e.msetSpan r = none)
    (helems : ∀ p ∈ elems, κ p.1 = false ∧ p.2 ≠ .exact 0)
    (hBf : ∀ y ∈ acBinds elems rest, y ∈ Bf)
    (hres : ∀ p ∈ res, G.find p.1 = p.1)
    (hnd : (res.map (·.1)).Nodup) :
    (execAC G k elems rest res e).2 = e ∧
      ∀ σ, σ ∈ (execAC G k elems rest res e).1 ↔
        ∃ σ' ∈ decomposeAC elems rest res (abs G κ e), σ ∈ F σ' := by
  induction elems generalizing res e with
  | nil =>
      cases rest with
      | none =>
          simp only [execAC, decomposeAC]
          rw [all_zero_iff_filter_nil]
          split_ifs with h
          · refine ⟨hk.restore e he, fun σ => ?_⟩
            rw [hk.mem e he]
            simp
          · simp
      | some r =>
          have hr : r ∈ Bf := hBf r mem_acBinds_rest
          have he' := he.pushMset hr (res.filter (fun p => p.2 ≠ 0))
          simp only [execAC, decomposeAC]
          refine ⟨?_, fun σ => ?_⟩
          · rw [hk.restore _ he', Env.popMset_pushMset _ _ _ (hrest r rfl)]
          · rw [hk.mem _ he', abs_pushMset G κ e r _ he.spans]
            simp
  | cons p es ih =>
      obtain ⟨x, μ⟩ := p
      have hp : (x, μ) ∈ (x, μ) :: es := List.mem_cons_self ..
      obtain ⟨hκx, hμ0⟩ := helems _ hp
      have hxB : x ∈ Bf := hBf x (mem_acBinds_fst hp)
      have hμB : ∀ k lo hi, μ = .var k lo hi → k ∈ Bf := by
        intro k lo hi h; subst h; exact hBf k (mem_acBinds_mult hp)
      have helems' : ∀ q ∈ es, κ q.1 = false ∧ q.2 ≠ .exact 0 :=
        fun q hq => helems q (List.mem_cons_of_mem _ hq)
      have hBf' : ∀ y ∈ acBinds es rest, y ∈ Bf :=
        fun y hy => hBf y (acBinds_cons_subset y hy)
      have hres' : ∀ c, ∀ q ∈ zeroEntry c res, G.find q.1 = q.1 := by
        intro c q hq
        obtain ⟨p, hp, hpq⟩ := mem_zeroEntry_fst hq
        rw [← hpq]; exact hres p hp
      have hnd' : ∀ c, ((zeroEntry c res).map (·.1)).Nodup := by
        intro c; rw [zeroEntry_fst]; exact hnd
      cases hx : e.nodes x with
      | some g =>
          simp only [execAC, decomposeAC, abs_cls, hx, Option.map_some]
          have hf := find?_nodup_class (G.find g) res (fun n => multMatchesE μ n (boundMult e μ))
            hnd (multMatchesE_zero μ hμ0 _)
          beta_reduce at hf
          rw [hf]
          cases hfr : res.find? (fun p => p.1 = G.find g ∧ p.2 ≠ 0) with
          | none => simp
          | some q =>
              have hq := List.find?_some hfr
              simp only [decide_eq_true_eq] at hq
              dsimp only
              rw [multMatches_abs G κ e μ q.2 hq.2]
              by_cases hm : multMatchesE μ q.2 (boundMult e μ) = true
              · simp only [hm, ite_true]
                have he' : EnvOk (setMultOf e μ q.2) Bf := he.setMultOf hμB q.2
                have hrest' : ∀ r ∈ rest, (setMultOf e μ q.2).msetSpan r = none := by
                  intro r hr; rw [setMultOf_msetSpan]; exact hrest r hr
                obtain ⟨ih1, ih2⟩ := ih (zeroEntry (G.find g) res) (setMultOf e μ q.2) he' hrest'
                  helems' hBf' (hres' _) (hnd' _)
                refine ⟨?_, ih2⟩
                rw [ih1]
                exact resetMult_setMultOf e μ q.2 hm
              · simp [hm]
      | none =>
          simp only [execAC, decomposeAC, abs_cls, hx, Option.map_none]
          have hbody : ∀ p ∈ res, multMatchesE μ p.2 (boundMult e μ) = true →
              (execAC G k es rest (zeroEntry p.1 res) (setMultOf (e.set x p.1) μ p.2)).2 =
                  setMultOf (e.set x p.1) μ p.2 ∧
              ∀ σ, σ ∈ (execAC G k es rest (zeroEntry p.1 res)
                    (setMultOf (e.set x p.1) μ p.2)).1 ↔
                ∃ σ' ∈ decomposeAC es rest (zeroEntry p.1 res)
                    ((abs G κ (setMultOf e μ p.2)).setCls x p.1), σ ∈ F σ' := by
            intro p hp hm
            have he' : EnvOk (setMultOf (e.set x p.1) μ p.2) Bf :=
              (he.set hxB p.1).setMultOf hμB p.2
            have hrest' : ∀ r ∈ rest, (setMultOf (e.set x p.1) μ p.2).msetSpan r = none := by
              intro r hr; rw [setMultOf_msetSpan, Env.set_msetSpan]; exact hrest r hr
            obtain ⟨ih1, ih2⟩ := ih (zeroEntry p.1 res) _ he' hrest' helems' hBf' (hres' _) (hnd' _)
            refine ⟨ih1, fun σ => ?_⟩
            rw [ih2 σ, abs_setMultOf_set G κ e x p.1 μ p.2 hκx (hres p hp)]
          rw [loop_restore]
          · refine ⟨rfl, fun σ => mem_flatMap_iff_of_entries res _ _ F σ ?_⟩
            intro p hp
            by_cases hz : p.2 = 0
            · simp [hz, multMatchesE_zero μ hμ0]
            · rw [multMatches_abs G κ e μ p.2 hz]
              by_cases hm : multMatchesE μ p.2 (boundMult e μ) = true
              · simp only [hm, hz, ite_true, ite_false]
                exact (hbody p hp hm).2 σ
              · simp [hm, hz]
          · intro p hp
            by_cases hm : multMatchesE μ p.2 (boundMult e μ) = true
            · rw [ite_eq_left hm, (hbody p hp hm).1, setMultOf_set,
                Env.clear_set _ _ _ (by rw [setMultOf_nodes]; exact hx), wasUnbound_set]
              exact resetMult_setMultOf e μ p.2 hm
            · rw [ite_eq_right hm]

end Semper.EMatch.Env
