import SemperProofs.EMatch.Env.Lemmas

/-!
# `DecomposeACI`: the executor's `decompose_aci_elem` refines `decomposeACI`
-/

namespace Semper.EMatch.Env

open Semper.EMatch

/-- `decompose_aci_elem` restores the environment and emits the members of
the reference `decomposeACI` continued by `F`. -/
theorem execACI_spec (G : Graph) (κ : Var → Bool) {k : Cont} {Bf : List Var}
    {F : Binding → List Binding} (hk : ContSpec G κ k Bf F)
    (elems : List Var) (rest : Option Var) (res : List C) (e : Env)
    (he : EnvOk e Bf)
    (hrest : ∀ r ∈ rest, e.setSpan r = none)
    (helems : ∀ x ∈ elems, κ x = false)
    (hBf : ∀ y ∈ elems ++ rest.toList, y ∈ Bf)
    (hres : ∀ c ∈ res, G.find c = c) :
    (execACI G k elems rest res e).2 = e ∧
      ∀ σ, σ ∈ (execACI G k elems rest res e).1 ↔
        ∃ σ' ∈ decomposeACI elems rest res (abs G κ e), σ ∈ F σ' := by
  induction elems generalizing res e with
  | nil =>
      cases rest with
      | none =>
          simp only [execACI, decomposeACI]
          by_cases h : res.isEmpty
          · simp only [h, ite_true]
            refine ⟨hk.restore e he, fun σ => ?_⟩
            rw [hk.mem e he]
            simp
          · simp [h]
      | some r =>
          have hr : r ∈ Bf := hBf r (by simp)
          have hrs : e.setSpan r = none := hrest r rfl
          have hok := he.pushSet hr res
          simp only [execACI, decomposeACI]
          refine ⟨?_, fun σ => ?_⟩
          · rw [hk.restore _ hok, Env.popSet_pushSet e r res hrs]
          · rw [hk.mem _ hok, abs_pushSet G κ e r res he.spans]
            simp
  | cons x es ih =>
      have hx : κ x = false := helems x (List.mem_cons_self ..)
      have hxB : x ∈ Bf := hBf x (by simp)
      have helems' : ∀ y ∈ es, κ y = false := fun y hy => helems y (List.mem_cons_of_mem x hy)
      have hBf' : ∀ y ∈ es ++ rest.toList, y ∈ Bf := fun y hy =>
        hBf y (by simp only [List.mem_append, List.mem_cons] at hy ⊢; tauto)
      cases hg : e.nodes x with
      | some g =>
          simp only [execACI, decomposeACI, abs_cls, hg, Option.map_some]
          by_cases hm : G.find g ∈ res
          · simp only [hm, ite_true]
            exact ih (res.erase (G.find g)) e he hrest helems' hBf'
              (fun c hc => hres c (List.mem_of_mem_erase hc))
          · simp [hm]
      | none =>
          simp only [execACI, decomposeACI, abs_cls, hg, Option.map_none]
          have ih' : ∀ c ∈ res,
              (execACI G k es rest (res.erase c) (e.set x c)).2 = e.set x c ∧
              ∀ σ, σ ∈ (execACI G k es rest (res.erase c) (e.set x c)).1 ↔
                ∃ σ' ∈ decomposeACI es rest (res.erase c) ((abs G κ e).setCls x c), σ ∈ F σ' := by
            intro c hc
            have h := ih (res.erase c) (e.set x c) (he.set hxB c)
              (fun r hr => by rw [Env.set_setSpan]; exact hrest r hr) helems' hBf'
              (fun d hd => hres d (List.mem_of_mem_erase hd))
            rw [abs_set_cls G κ e x c hx (hres c hc)] at h
            exact h
          have hiter : ∀ c ∈ res,
              ((fun c e => ((execACI G k es rest (res.erase c) (e.set x c)).1,
                (execACI G k es rest (res.erase c) (e.set x c)).2.clear x)) c e).2 = e := by
            intro c hc
            simp only [(ih' c hc).1]
            exact Env.clear_set e x c hg
          rw [loop_restore _ res e hiter]
          refine ⟨rfl, fun σ => ?_⟩
          simp only [List.mem_flatMap]
          constructor
          · rintro ⟨c, hc, hσ⟩
            rw [(ih' c hc).2 σ] at hσ
            obtain ⟨σ', hσ', hσσ⟩ := hσ
            exact ⟨σ', ⟨c, hc, hσ'⟩, hσσ⟩
          · rintro ⟨σ', hσ', hσσ⟩
            obtain ⟨c, hc, hσ'⟩ := hσ'
            exact ⟨c, hc, ((ih' c hc).2 σ).mpr ⟨σ', hσ', hσσ⟩⟩

end Semper.EMatch.Env
