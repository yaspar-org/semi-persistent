import SemperProofs.EMatch.Env.Lemmas

/-!
# `DecomposeComm`: the pair decomposition refines `decomposeComm`

As sets of bindings only: with the first element bound and `a = b`, the
reference `decomposeComm` lists the binding twice (`bindElems` succeeds
in both orders) while the engine's bound path takes the first entry once
(`ematch.rs:2385-2390`). See `Dup.lean`.
-/

namespace Semper.EMatch.Env

open Semper.EMatch

theorem execPairSnd_spec (G : Graph) (κ : Var → Bool) {k : Cont} {Bf : List Var}
    {F : Binding → List Binding} (hk : ContSpec G κ k Bf F)
    (y : Var) (c : C) (e : Env)
    (he : EnvOk e Bf) (hy : κ y = false) (hyB : y ∈ Bf) (hc : G.find c = c) :
    (execPairSnd G k y c e).2 = e ∧
      ∀ σ, σ ∈ (execPairSnd G k y c e).1 ↔
        ∃ σ' ∈ (bindElems [y] [c] (abs G κ e)).toList, σ ∈ F σ' := by
  cases hn : e.nodes y with
  | some g =>
    simp only [execPairSnd, hn, bindElems, abs_cls, Option.map_some]
    by_cases hg : G.find g = c
    · simp only [hg, ite_true, hk.restore e he, true_and]
      intro σ
      simp only [hk.mem e he, Option.toList_some, List.mem_singleton, exists_eq_left]
    · simp only [hg, ite_false, true_and]
      intro σ
      simp only [List.not_mem_nil, Option.toList_none, false_and, exists_false]
  | none =>
    simp only [execPairSnd, hn, bindElems, abs_cls, Option.map_none]
    have he' : EnvOk (e.set y c) Bf := he.set hyB c
    refine ⟨?_, ?_⟩
    · simp only [hk.restore _ he', Env.clear_set e y c hn]
    · intro σ
      simp only [hk.mem _ he', abs_set_cls G κ e y c hy hc, Option.toList_some,
        List.mem_singleton, exists_eq_left]

theorem execPair_spec (G : Graph) (κ : Var → Bool) {k : Cont} {Bf : List Var}
    {F : Binding → List Binding} (hk : ContSpec G κ k Bf F)
    (x y : Var) (a b : C) (e : Env)
    (he : EnvOk e Bf) (hx : κ x = false) (hy : κ y = false) (hxB : x ∈ Bf) (hyB : y ∈ Bf)
    (ha : G.find a = a) (hb : G.find b = b) :
    (execPair G k x y a b e).2 = e ∧
      ∀ σ, σ ∈ (execPair G k x y a b e).1 ↔
        ∃ σ' ∈ decomposeComm x y a b (abs G κ e), σ ∈ F σ' := by
  cases hn : e.nodes x with
  | some g =>
    simp only [execPair, hn, decomposeComm, bindElems, abs_cls, Option.map_some]
    by_cases hga : G.find g = a
    · simp only [hga, ite_true]
      obtain ⟨h1, h2⟩ := execPairSnd_spec G κ hk y b e he hy hyB hb
      simp only [bindElems, abs_cls] at h2
      refine ⟨h1, fun σ => ?_⟩
      rw [h2 σ]
      by_cases hab : a = b
      · subst hab
        simp only [ite_true, List.mem_append, or_self]
      · simp only [hab, ite_false, Option.toList_none, List.append_nil]
    · simp only [hga, ite_false, Option.toList_none, List.nil_append]
      by_cases hgb : G.find g = b
      · simp only [hgb, ite_true]
        have h := execPairSnd_spec G κ hk y a e he hy hyB ha
        simpa only [bindElems, abs_cls] using h
      · simp only [hgb, ite_false, Option.toList_none, true_and]
        intro σ
        simp only [List.not_mem_nil, false_and, exists_false]
  | none =>
    simp only [execPair, hn, decomposeComm, bindElems, abs_cls, Option.map_none]
    have hea : EnvOk (e.set x a) Bf := he.set hxB a
    have heb : EnvOk (e.set x b) Bf := he.set hxB b
    obtain ⟨h1, h2⟩ := execPairSnd_spec G κ hk y b (e.set x a) hea hy hyB hb
    rw [h1, Env.clear_set e x a hn]
    obtain ⟨h3, h4⟩ := execPairSnd_spec G κ hk y a (e.set x b) heb hy hyB ha
    rw [h3, Env.clear_set e x b hn]
    refine ⟨rfl, fun σ => ?_⟩
    rw [abs_set_cls G κ e x a hx ha] at h2
    rw [abs_set_cls G κ e x b hx hb] at h4
    simp only [bindElems, Binding.setCls] at h2 h4
    simp only [Binding.setCls]
    simp only [List.mem_append, h2 σ, h4 σ]
    constructor
    · rintro (⟨σ', hσ', hσ⟩ | ⟨σ', hσ', hσ⟩)
      · exact ⟨σ', Or.inl hσ', hσ⟩
      · exact ⟨σ', Or.inr hσ', hσ⟩
    · rintro ⟨σ', hσ' | hσ', hσ⟩
      · exact Or.inl ⟨σ', hσ', hσ⟩
      · exact Or.inr ⟨σ', hσ', hσ⟩

end Semper.EMatch.Env
