import SemperProofs.EMatch.Env.Lemmas

/-!
# `ExpandA`: the executor's `run_expand_a` refines `expandA`
-/

namespace Semper.EMatch.Env

open Semper.EMatch

/-! ## `bind_fixed_and_continue` -/

/-- `bind_fixed_and_continue` clears exactly the variables it bound and
emits the members of `bindElems` on the abstraction continued by `F`. -/
theorem bindFixed_spec (G : Graph) (κ : Var → Bool) {k : Cont} {Bf : List Var}
    {F : Binding → List Binding} (hk : ContSpec G κ k Bf F)
    (xs : List Var) (cs : List C) (bound : List Var) (e : Env)
    (he : EnvOk e Bf)
    (hxs : ∀ x ∈ xs, κ x = false ∧ x ∈ Bf)
    (hcs : ∀ c ∈ cs, G.find c = c) :
    (bindFixed G k xs cs bound e).2 = unbind bound e ∧
      ∀ σ, σ ∈ (bindFixed G k xs cs bound e).1 ↔
        ∃ σ' ∈ (bindElems xs (cs.take xs.length) (abs G κ e)).toList, σ ∈ F σ' := by
  induction xs generalizing cs bound e with
  | nil =>
      simp only [bindFixed, List.length_nil, List.take_zero, bindElems, Option.toList_some,
        List.mem_singleton, exists_eq_left]
      exact ⟨by rw [hk.restore e he], fun σ => hk.mem e he σ⟩
  | cons x xs ih =>
      have hx := hxs x (List.mem_cons_self ..)
      have hxs' : ∀ y ∈ xs, κ y = false ∧ y ∈ Bf := fun y hy => hxs y (List.mem_cons_of_mem x hy)
      cases cs with
      | nil =>
          have hnone : bindElems (x :: xs) (List.take (x :: xs).length []) (abs G κ e) = none := rfl
          rw [hnone]
          exact ⟨rfl, fun σ => by simp [bindFixed]⟩
      | cons c cs =>
          have hc := hcs c (List.mem_cons_self ..)
          have hcs' : ∀ d ∈ cs, G.find d = d := fun d hd => hcs d (List.mem_cons_of_mem c hd)
          simp only [List.length_cons, List.take_succ_cons, bindElems, abs_cls]
          cases hg : e.nodes x with
          | some g =>
              simp only [bindFixed, hg, Option.map_some]
              by_cases hfind : G.find g = c
              · simp only [hfind, hc, ite_true]
                exact ih cs bound e he hxs' hcs'
              · rw [hc]
                simp [hfind]
          | none =>
              simp only [bindFixed, hg, Option.map_none]
              have h := ih cs (x :: bound) (e.set x c) (he.set hx.2 c) hxs' hcs'
              rw [unbind_cons, Env.clear_set e x c hg, abs_set_cls G κ e x c hx.1 hc] at h
              exact h

/-! ## Optional rest pushes -/

/-- Push an optional sequence rest (`none` is a no-op). -/
def pushE (r : Option Var) (u : List C) (e : Env) : Env :=
  match r with
  | none => e
  | some r => e.pushSeq r u

/-- Pop an optional sequence rest (`none` is a no-op). -/
def popE (r : Option Var) (e : Env) : Env :=
  match r with
  | none => e
  | some r => e.popSeq r

@[simp] theorem pushE_none (u : List C) (e : Env) : pushE none u e = e := rfl
@[simp] theorem pushE_some (r : Var) (u : List C) (e : Env) :
    pushE (some r) u e = e.pushSeq r u := rfl
@[simp] theorem popE_none (e : Env) : popE none e = e := rfl
@[simp] theorem popE_some (r : Var) (e : Env) : popE (some r) e = e.popSeq r := rfl

theorem pushE_seqSpan_ne (r : Option Var) (u : List C) (e : Env) (s : Var)
    (h : ∀ a ∈ r, a ≠ s) : (pushE r u e).seqSpan s = e.seqSpan s := by
  cases r with
  | none => rfl
  | some a =>
      simp only [pushE_some, Env.pushSeq_seqSpan]
      rw [Function.update_of_ne (h a rfl).symm]

theorem popE_pushE (r : Option Var) (u : List C) (e : Env) (h : ∀ a ∈ r, e.seqSpan a = none) :
    popE r (pushE r u e) = e := by
  cases r with
  | none => rfl
  | some a => exact Env.popSeq_pushSeq e a u (h a rfl)

theorem EnvOk.pushE {e : Env} {Bf : List Var} (he : EnvOk e Bf) (r : Option Var)
    (hr : ∀ a ∈ r, a ∈ Bf) (u : List C) : EnvOk (pushE r u e) Bf := by
  cases r with
  | none => exact he
  | some a => exact he.pushSeq (hr a rfl) u

theorem abs_pushE (G : Graph) (κ : Var → Bool) (r : Option Var) (u : List C) (e : Env)
    (hok : SpansOk e) : abs G κ (pushE r u e) = bindSeq r u (abs G κ e) := by
  cases r with
  | none => rfl
  | some a => exact abs_pushSeq G κ e a u hok

theorem bindElems_bindSeq (xs : List Var) (cs : List C) (σ : Binding) (r : Option Var)
    (u : List C) :
    bindElems xs cs (bindSeq r u σ) = (bindElems xs cs σ).map (bindSeq r u) := by
  cases r with
  | none =>
      show bindElems xs cs σ = (bindElems xs cs σ).map (bindSeq none u)
      cases bindElems xs cs σ <;> rfl
  | some a => exact bindElems_setSeqRest xs cs σ a u

/-- One split of `run_expand_a`: push the rests for the offset `j`, bind
the fixed children, pop the rests. -/
theorem bindFixed_split (G : Graph) (κ : Var → Bool) {k : Cont} {Bf : List Var}
    {F : Binding → List Binding} (hk : ContSpec G κ k Bf F)
    (pre : Option Var) (elems : List Var) (suf : Option Var) (cs : List C) (e : Env) (j : Nat)
    (he : EnvOk e Bf)
    (hpre : ∀ r ∈ pre, e.seqSpan r = none)
    (hsuf : ∀ r ∈ suf, e.seqSpan r = none)
    (hdist : ∀ r ∈ pre, suf ≠ some r)
    (helems : ∀ x ∈ elems, κ x = false)
    (hBf : ∀ y ∈ pre.toList ++ elems ++ suf.toList, y ∈ Bf)
    (hcs : ∀ c ∈ cs, G.find c = c) :
    popE pre (popE suf (bindFixed G k elems (cs.drop j) []
        (pushE suf (cs.drop (j + elems.length)) (pushE pre (cs.take j) e))).2) = e ∧
      ∀ σ, σ ∈ (bindFixed G k elems (cs.drop j) []
          (pushE suf (cs.drop (j + elems.length)) (pushE pre (cs.take j) e))).1 ↔
        ∃ σ₁, bindElems elems ((cs.drop j).take elems.length) (abs G κ e) = some σ₁ ∧
          σ ∈ F (bindSeq suf (cs.drop (j + elems.length)) (bindSeq pre (cs.take j) σ₁)) := by
  have hpreB : ∀ a ∈ pre, a ∈ Bf := fun a ha =>
    hBf a (by simp only [List.mem_append, Option.mem_toList]; exact Or.inl (Or.inl ha))
  have hsufB : ∀ a ∈ suf, a ∈ Bf := fun a ha =>
    hBf a (by simp only [List.mem_append, Option.mem_toList]; exact Or.inr ha)
  have helemsB : ∀ x ∈ elems, x ∈ Bf := fun x hx =>
    hBf x (by simp only [List.mem_append]; exact Or.inl (Or.inr hx))
  have hsuf' : ∀ a ∈ suf, (pushE pre (cs.take j) e).seqSpan a = none := by
    intro a ha
    rw [pushE_seqSpan_ne pre _ e a (fun b hb hba => hdist b hb (by rw [hba]; exact ha))]
    exact hsuf a ha
  have he₁ : EnvOk (pushE pre (cs.take j) e) Bf := he.pushE pre hpreB _
  have he₂ : EnvOk (pushE suf (cs.drop (j + elems.length)) (pushE pre (cs.take j) e)) Bf :=
    he₁.pushE suf hsufB _
  obtain ⟨hr, hm⟩ := bindFixed_spec G κ hk elems (cs.drop j) [] _ he₂
    (fun x hx => ⟨helems x hx, helemsB x hx⟩) (fun c hc => hcs c (List.mem_of_mem_drop hc))
  refine ⟨?_, fun σ => ?_⟩
  · rw [hr, unbind_nil, popE_pushE suf _ _ hsuf', popE_pushE pre _ e hpre]
  · rw [hm σ, abs_pushE G κ suf _ _ he₁.spans, abs_pushE G κ pre _ e he.spans,
      bindElems_bindSeq, bindElems_bindSeq]
    cases bindElems elems ((cs.drop j).take elems.length) (abs G κ e) with
    | none => simp
    | some σ₁ => simp

/-! ## The reference `expandA` -/

/-- Membership in `expandA`: an offset `j` with the fixed children in range,
forced to `0` without a prefix rest and to the end without a suffix rest. -/
theorem mem_expandA (pre : Option Var) (elems : List Var) (suf : Option Var) (cs : List C)
    (σ σ' : Binding) :
    σ' ∈ expandA pre elems suf cs σ ↔
      ∃ j, j + elems.length ≤ cs.length ∧ (pre = none → j = 0) ∧
        (suf = none → j + elems.length = cs.length) ∧
        ∃ σ₁, bindElems elems ((cs.drop j).take elems.length) σ = some σ₁ ∧
          σ' = bindSeq suf (cs.drop (j + elems.length)) (bindSeq pre (cs.take j) σ₁) := by
  simp only [expandA, List.mem_flatMap, List.mem_range, List.length_take, List.length_drop,
    ne_eq, List.take_eq_nil_iff, List.drop_eq_nil_iff, List.drop_drop, Option.isNone_iff_eq_none]
  constructor
  · rintro ⟨j, hj, hmem⟩
    by_cases h1 : ¬ min elems.length (cs.length - j) = elems.length
    · rw [ite_eq_left h1] at hmem
      exact absurd hmem (by simp)
    rw [ite_eq_right h1] at hmem
    by_cases h2 : pre = none ∧ ¬ (j = 0 ∨ cs = [])
    · rw [ite_eq_left h2] at hmem
      exact absurd hmem (by simp)
    rw [ite_eq_right h2] at hmem
    by_cases h3 : suf = none ∧ ¬ cs.length ≤ j + elems.length
    · rw [ite_eq_left h3] at hmem
      exact absurd hmem (by simp)
    rw [ite_eq_right h3] at hmem
    cases hb : bindElems elems (List.take elems.length (List.drop j cs)) σ with
    | none => simp [hb] at hmem
    | some σ₁ =>
        simp only [hb, List.mem_singleton] at hmem
        refine ⟨j, (by omega), fun hp => ?_, fun hs => ?_, σ₁, hb, hmem⟩
        · have : j = 0 ∨ cs = [] := by
            by_contra hc
            exact h2 ⟨hp, hc⟩
          rcases this with h | h
          · exact h
          · subst h
            simp at hj
            omega
        · have : cs.length ≤ j + elems.length := by
            by_contra hc
            exact h3 ⟨hs, hc⟩
          omega
  · rintro ⟨j, hj, hp, hs, σ₁, hb, rfl⟩
    refine ⟨j, (by omega), ?_⟩
    rw [ite_eq_right (show ¬ ¬ min elems.length (cs.length - j) = elems.length by omega),
      ite_eq_right (show ¬ (pre = none ∧ ¬ (j = 0 ∨ cs = [])) from
        fun ⟨hp', hu⟩ => hu (Or.inl (hp hp'))),
      ite_eq_right (show ¬ (suf = none ∧ ¬ cs.length ≤ j + elems.length) from
        fun ⟨hs', hv⟩ => hv (le_of_eq (hs hs').symm)),
      hb]
    exact List.mem_singleton.mpr rfl

/-- `run_expand_a` with `bind_fixed_and_continue` restores the environment
and emits the members of the reference `expandA` continued by `F`.
Hypotheses: the rest spans are empty on entry and distinct; the fixed
child variables are class variables; the children are canonical. -/
theorem execExpandA_spec (G : Graph) (κ : Var → Bool) {k : Cont} {Bf : List Var}
    {F : Binding → List Binding} (hk : ContSpec G κ k Bf F)
    (pre : Option Var) (elems : List Var) (suf : Option Var) (cs : List C) (e : Env)
    (he : EnvOk e Bf)
    (hpre : ∀ r ∈ pre, e.seqSpan r = none)
    (hsuf : ∀ r ∈ suf, e.seqSpan r = none)
    (hdist : ∀ r ∈ pre, suf ≠ some r)
    (helems : ∀ x ∈ elems, κ x = false)
    (hBf : ∀ y ∈ pre.toList ++ elems ++ suf.toList, y ∈ Bf)
    (hcs : ∀ c ∈ cs, G.find c = c) :
    (execExpandA G k pre elems suf cs e).2 = e ∧
      ∀ σ, σ ∈ (execExpandA G k pre elems suf cs e).1 ↔
        ∃ σ' ∈ expandA pre elems suf cs (abs G κ e), σ ∈ F σ' := by
  -- the failing shapes: nothing is emitted and the reference is empty
  have hfail : ∀ (P : Prop), (∀ σ' ∈ expandA pre elems suf cs (abs G κ e), P) → ¬ P →
      ∀ σ, σ ∈ ([] : List Binding) ↔ ∃ σ' ∈ expandA pre elems suf cs (abs G κ e), σ ∈ F σ' := by
    intro P hP hnP σ
    constructor
    · intro h
      exact absurd h (by simp)
    · rintro ⟨σ', hσ', -⟩
      exact absurd (hP σ' hσ') hnP
  cases pre with
  | none =>
      cases suf with
      | none =>
          simp only [execExpandA]
          by_cases hlen : cs.length = elems.length
          · rw [ite_eq_left hlen]
            have h := bindFixed_split G κ hk none elems none cs e 0 he hpre hsuf hdist helems
              hBf hcs
            simp only [pushE_none, popE_none, List.drop_zero, Nat.zero_add] at h
            refine ⟨h.1, fun σ => ?_⟩
            rw [h.2 σ]
            constructor
            · rintro ⟨σ₁, hb, hσ⟩
              exact ⟨σ₁, (mem_expandA _ _ _ _ _ _).mpr
                ⟨0, (by omega), (fun _ => rfl), (fun _ => by omega), σ₁, hb, rfl⟩, hσ⟩
            · rintro ⟨σ', hσ', hσ⟩
              rw [mem_expandA] at hσ'
              obtain ⟨j, hj, hj0, -, σ₁, hb, heq⟩ := hσ'
              have := hj0 rfl
              subst this
              rw [heq] at hσ
              exact ⟨σ₁, hb, hσ⟩
          · rw [ite_eq_right hlen]
            refine ⟨rfl, hfail (cs.length = elems.length) ?_ hlen⟩
            intro σ' hσ'
            rw [mem_expandA] at hσ'
            obtain ⟨j, hj, hj0, hjn, -⟩ := hσ'
            have := hj0 rfl
            have := hjn rfl
            omega
      | some s =>
          simp only [execExpandA]
          by_cases hlt : cs.length < elems.length
          · rw [ite_eq_left hlt]
            refine ⟨rfl, hfail (elems.length ≤ cs.length) ?_ (by omega)⟩
            intro σ' hσ'
            rw [mem_expandA] at hσ'
            obtain ⟨j, hj, -⟩ := hσ'
            omega
          · rw [ite_eq_right hlt]
            have h := bindFixed_split G κ hk none elems (some s) cs e 0 he hpre hsuf hdist helems
              hBf hcs
            simp only [pushE_none, pushE_some, popE_none, popE_some, List.drop_zero,
              Nat.zero_add] at h
            refine ⟨h.1, fun σ => ?_⟩
            rw [h.2 σ]
            constructor
            · rintro ⟨σ₁, hb, hσ⟩
              refine ⟨bindSeq (some s) (cs.drop elems.length) (bindSeq none (cs.take 0) σ₁),
                (mem_expandA _ _ _ _ _ _).mpr
                  ⟨0, (by omega), (fun _ => rfl), (fun h => by cases h), σ₁, hb, ?_⟩, hσ⟩
              rw [Nat.zero_add]
            · rintro ⟨σ', hσ', hσ⟩
              rw [mem_expandA] at hσ'
              obtain ⟨j, hj, hj0, -, σ₁, hb, heq⟩ := hσ'
              have := hj0 rfl
              subst this
              rw [heq, Nat.zero_add] at hσ
              exact ⟨σ₁, hb, hσ⟩
  | some p =>
      cases suf with
      | none =>
          simp only [execExpandA]
          by_cases hlt : cs.length < elems.length
          · rw [ite_eq_left hlt]
            refine ⟨rfl, hfail (elems.length ≤ cs.length) ?_ (by omega)⟩
            intro σ' hσ'
            rw [mem_expandA] at hσ'
            obtain ⟨j, hj, -⟩ := hσ'
            omega
          · rw [ite_eq_right hlt]
            have h := bindFixed_split G κ hk (some p) elems none cs e (cs.length - elems.length)
              he hpre hsuf hdist helems hBf hcs
            have hsplit : cs.length - elems.length + elems.length = cs.length := by omega
            simp only [pushE_none, pushE_some, popE_none, popE_some, hsplit] at h
            refine ⟨h.1, fun σ => ?_⟩
            rw [h.2 σ]
            constructor
            · rintro ⟨σ₁, hb, hσ⟩
              exact ⟨_, (mem_expandA _ _ _ _ _ _).mpr
                ⟨cs.length - elems.length, (by omega), (fun h => by cases h), (fun _ => hsplit),
                  σ₁, hb, rfl⟩, hσ⟩
            · rintro ⟨σ', hσ', hσ⟩
              rw [mem_expandA] at hσ'
              obtain ⟨j, hj, -, hjn, σ₁, hb, heq⟩ := hσ'
              have hj' : j = cs.length - elems.length := by
                have := hjn rfl
                omega
              subst hj'
              rw [heq] at hσ
              exact ⟨σ₁, hb, hσ⟩
      | some s =>
          simp only [execExpandA]
          by_cases hlt : cs.length < elems.length
          · rw [ite_eq_left hlt]
            refine ⟨rfl, hfail (elems.length ≤ cs.length) ?_ (by omega)⟩
            intro σ' hσ'
            rw [mem_expandA] at hσ'
            obtain ⟨j, hj, -⟩ := hσ'
            omega
          · rw [ite_eq_right hlt]
            have h := fun off =>
              bindFixed_split G κ hk (some p) elems (some s) cs e off he hpre hsuf hdist helems
                hBf hcs
            have hloop := loop_restore
              (fun off e =>
                ((bindFixed G k elems (cs.drop off) []
                  ((e.pushSeq p (cs.take off)).pushSeq s (cs.drop (off + elems.length)))).1,
                 ((bindFixed G k elems (cs.drop off) []
                  ((e.pushSeq p (cs.take off)).pushSeq s
                    (cs.drop (off + elems.length)))).2.popSeq s).popSeq p))
              (List.range (cs.length - elems.length + 1)) e (fun off _ => (h off).1)
            rw [hloop]
            refine ⟨rfl, fun σ => ?_⟩
            simp only [List.mem_flatMap, List.mem_range]
            constructor
            · rintro ⟨off, hoff, hσ⟩
              obtain ⟨σ₁, hb, hσ⟩ := ((h off).2 σ).mp hσ
              exact ⟨_, (mem_expandA _ _ _ _ _ _).mpr
                ⟨off, (by omega), (fun h => by cases h), (fun h => by cases h), σ₁, hb, rfl⟩, hσ⟩
            · rintro ⟨σ', hσ', hσ⟩
              rw [mem_expandA] at hσ'
              obtain ⟨j, hj, -, -, σ₁, hb, heq⟩ := hσ'
              rw [heq] at hσ
              exact ⟨j, (by omega), ((h j).2 σ).mpr ⟨σ₁, hb, hσ⟩⟩

end Semper.EMatch.Env
