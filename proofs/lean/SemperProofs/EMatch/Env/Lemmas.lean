import SemperProofs.EMatch.Env.Exec

/-!
# Shared lemmas for the refinement

The continuation specification `ContSpec`, the loop lemmas, the
multiplicity correspondence (`mult_matches` with the `ZERO` encoding
versus the reference `multMatches`), and small facts about `abs`,
`EnvOk`, `acBinds` and residuals.
-/

namespace Semper.EMatch.Env

open Semper.EMatch

/-! ## The continuation specification -/

/-- What the rest of the plan guarantees on every well-formed environment
bounded by `B'`: it restores the environment and its emitted list has the
members of `F` on the abstraction. -/
structure ContSpec (G : Graph) (κ : Var → Bool) (k : Cont) (B' : List Var)
    (F : Binding → List Binding) : Prop where
  restore : ∀ e, EnvOk e B' → (k e).2 = e
  mem : ∀ e, EnvOk e B' → ∀ σ, σ ∈ (k e).1 ↔ σ ∈ F (abs G κ e)

/-! ## `EnvOk` under the writes -/

namespace EnvOk

theorem mono {e : Env} {B B' : List Var} (h : EnvOk e B) (hB : ∀ x ∈ B, x ∈ B') : EnvOk e B' :=
  ⟨h.bounded.mono hB, h.spans⟩
theorem cons {e : Env} {B : List Var} (h : EnvOk e B) (x : Var) : EnvOk e (x :: B) :=
  ⟨h.bounded.cons x, h.spans⟩
theorem append_left {e : Env} {B : List Var} (h : EnvOk e B) (B' : List Var) :
    EnvOk e (B' ++ B) :=
  ⟨h.bounded.append_left B', h.spans⟩
theorem set {e : Env} {B : List Var} (h : EnvOk e B) {x : Var} (hx : x ∈ B) (g : NodeId) :
    EnvOk (e.set x g) B :=
  ⟨h.bounded.set hx g, h.spans.set x g⟩
theorem setOpt {e : Env} {B : List Var} (h : EnvOk e B) {x : Var} (hx : x ∈ B)
    (v : Option NodeId) : EnvOk (e.setOpt x v) B :=
  ⟨h.bounded.setOpt hx v, h.spans.setOpt x v⟩
theorem clear {e : Env} {B : List Var} (h : EnvOk e B) (x : Var) : EnvOk (e.clear x) B :=
  ⟨h.bounded.clear x, h.spans.clear x⟩
theorem setMult {e : Env} {B : List Var} (h : EnvOk e B) {k : Var} (hk : k ∈ B) (m : Nat) :
    EnvOk (e.setMult k m) B :=
  ⟨h.bounded.setMult hk m, h.spans.setMult k m⟩
theorem pushSeq {e : Env} {B : List Var} (h : EnvOk e B) {r : Var} (hr : r ∈ B) (d : List C) :
    EnvOk (e.pushSeq r d) B :=
  ⟨h.bounded.pushSeq hr d, h.spans.pushSeq r d⟩
theorem pushSet {e : Env} {B : List Var} (h : EnvOk e B) {r : Var} (hr : r ∈ B) (d : List C) :
    EnvOk (e.pushSet r d) B :=
  ⟨h.bounded.pushSet hr d, h.spans.pushSet r d⟩
theorem pushMset {e : Env} {B : List Var} (h : EnvOk e B) {r : Var} (hr : r ∈ B)
    (d : List (C × Nat)) : EnvOk (e.pushMset r d) B :=
  ⟨h.bounded.pushMset hr d, h.spans.pushMset r d⟩

theorem nodes_none {e : Env} {B : List Var} (h : EnvOk e B) {x : Var} (hx : x ∉ B) :
    e.nodes x = none := h.bounded.nodes x hx
theorem seqSpan_none {e : Env} {B : List Var} (h : EnvOk e B) {r : Var} (hr : r ∉ B) :
    e.seqSpan r = none := h.bounded.seq r hr
theorem setSpan_none {e : Env} {B : List Var} (h : EnvOk e B) {r : Var} (hr : r ∉ B) :
    e.setSpan r = none := h.bounded.fin r hr
theorem msetSpan_none {e : Env} {B : List Var} (h : EnvOk e B) {r : Var} (hr : r ∉ B) :
    e.msetSpan r = none := h.bounded.mset r hr

end EnvOk

/-! ## Loops -/

theorem loop_restore {α : Type} (f : α → Env → List Binding × Env) (as : List α) (e : Env)
    (h : ∀ a ∈ as, (f a e).2 = e) :
    loop f as e = (as.flatMap (fun a => (f a e).1), e) := by
  induction as with
  | nil => rfl
  | cons a as ih =>
      have ha := h a (List.mem_cons_self ..)
      rw [loop_cons, ha, ih (fun b hb => h b (List.mem_cons_of_mem a hb))]
      simp

theorem mem_loop_of_restore {α : Type} (f : α → Env → List Binding × Env) (as : List α)
    (e : Env) (h : ∀ a ∈ as, (f a e).2 = e) (σ : Binding) :
    σ ∈ (loop f as e).1 ↔ ∃ a ∈ as, σ ∈ (f a e).1 := by
  rw [loop_restore f as e h]; simp

/-- The join loop (`leapfrog_join`): the target slot is overwritten per
key and only restored after the loop, so the environment threaded through
the loop differs from the entry one at `t` only. -/
theorem loop_set (k : Cont) (t : Var) (ids : List NodeId) (env : Env)
    (hk : ∀ id ∈ ids, (k (env.set t id)).2 = env.set t id) :
    ∀ e', e'.setOpt t (env.nodes t) = env →
      (loop (fun id e => k (e.set t id)) ids e').1 =
          ids.flatMap (fun id => (k (env.set t id)).1) ∧
        ((loop (fun id e => k (e.set t id)) ids e').2).setOpt t (env.nodes t) = env := by
  induction ids with
  | nil => intro e' he; simp [he]
  | cons id ids ih =>
      intro e' he
      have hset : e'.set t id = env.set t id := Env.set_of_setOpt_eq he id
      have hk' := hk id (List.mem_cons_self ..)
      have hrest : (env.set t id).setOpt t (env.nodes t) = env := Env.setOpt_set env t id
      obtain ⟨ih1, ih2⟩ := ih (fun i hi => hk i (List.mem_cons_of_mem id hi)) (env.set t id) hrest
      simp only [loop_cons, hset, hk']
      exact ⟨by rw [ih1, List.flatMap_cons], ih2⟩

/-! ## Multiplicities -/

@[simp] theorem setMultOf_nodes (e : Env) (μ : Mult) (m : Nat) : (setMultOf e μ m).nodes = e.nodes := by
  cases μ <;> rfl
@[simp] theorem setMultOf_seqPool (e : Env) (μ : Mult) (m : Nat) :
    (setMultOf e μ m).seqPool = e.seqPool := by cases μ <;> rfl
@[simp] theorem setMultOf_seqSpan (e : Env) (μ : Mult) (m : Nat) :
    (setMultOf e μ m).seqSpan = e.seqSpan := by cases μ <;> rfl
@[simp] theorem setMultOf_setPool (e : Env) (μ : Mult) (m : Nat) :
    (setMultOf e μ m).setPool = e.setPool := by cases μ <;> rfl
@[simp] theorem setMultOf_setSpan (e : Env) (μ : Mult) (m : Nat) :
    (setMultOf e μ m).setSpan = e.setSpan := by cases μ <;> rfl
@[simp] theorem setMultOf_msetPool (e : Env) (μ : Mult) (m : Nat) :
    (setMultOf e μ m).msetPool = e.msetPool := by cases μ <;> rfl
@[simp] theorem setMultOf_msetSpan (e : Env) (μ : Mult) (m : Nat) :
    (setMultOf e μ m).msetSpan = e.msetSpan := by cases μ <;> rfl
@[simp] theorem nodeOf_setMultOf (e : Env) (G : Graph) (v : Var) (μ : Mult) (m : Nat) :
    (setMultOf e μ m).nodeOf G v = e.nodeOf G v := by cases μ <;> rfl

@[simp] theorem resetMult_nodes (e : Env) (μ : Mult) (wu : Bool) : (resetMult e μ wu).nodes = e.nodes := by
  cases μ with
  | var k lo hi => cases wu <;> rfl
  | exact n => rfl

theorem setMultOf_set (e : Env) (x : Var) (g : NodeId) (μ : Mult) (m : Nat) :
    setMultOf (e.set x g) μ m = (setMultOf e μ m).set x g := by
  cases μ <;> rfl

theorem wasUnbound_set (e : Env) (x : Var) (g : NodeId) (μ : Mult) :
    wasUnbound (e.set x g) μ = wasUnbound e μ := by
  cases μ <;> rfl

theorem boundMult_set (e : Env) (x : Var) (g : NodeId) (μ : Mult) :
    boundMult (e.set x g) μ = boundMult e μ := by
  cases μ <;> rfl

theorem resetMult_clear (e : Env) (x : Var) (μ : Mult) (wu : Bool) :
    resetMult (e.clear x) μ wu = (resetMult e μ wu).clear x := by
  cases μ with
  | var k lo hi => cases wu <;> rfl
  | exact n => rfl

/-- The `was_unbound` discipline restores the multiplicity slot
(`ematch.rs:2408-2439`): a slot that was zero is zeroed again, a slot that
was bound was re-written with its own value (`mult_matches` forced it). -/
theorem resetMult_setMultOf (e : Env) (μ : Mult) (m : Nat)
    (h : multMatchesE μ m (boundMult e μ) = true) :
    resetMult (setMultOf e μ m) μ (wasUnbound e μ) = e := by
  cases μ with
  | exact n => rfl
  | var k lo hi =>
      have h' := h
      simp only [multMatchesE, boundMult, Bool.and_eq_true, Bool.or_eq_true] at h'
      simp only [resetMult, setMultOf, wasUnbound]
      by_cases hz : e.mults k = 0
      · simp [hz, Env.setMult_zero_setMult]
      · have : m = e.mults k := by
          rcases h'.1.2 with h'' | h''
          · exact absurd (of_decide_eq_true h'') hz
          · exact of_decide_eq_true h''
        subst this
        simp [hz, Env.setMult_self]

theorem multMatchesE_zero (μ : Mult) (hμ : μ ≠ .exact 0) (b : Nat) :
    multMatchesE μ 0 b = false := by
  cases μ with
  | exact n =>
      simp only [multMatchesE, decide_eq_false_iff_not]
      intro h; exact hμ (by rw [h])
  | var k lo hi => simp [multMatchesE]

/-- `mult_matches` with the `ZERO` encoding is the reference `multMatches`
on the abstraction, and the binding it produces is the abstraction of the
`set_mult` write. -/
theorem multMatches_abs (G : Graph) (κ : Var → Bool) (e : Env) (μ : Mult) (m : Nat)
    (hm : m ≠ 0) :
    multMatches (abs G κ e) μ m =
      if multMatchesE μ m (boundMult e μ) then some (abs G κ (setMultOf e μ m)) else none := by
  cases μ with
  | exact n =>
      simp only [multMatches, multMatchesE, setMultOf]
      by_cases h : m = n <;> simp [h]
  | var k lo hi =>
      simp only [multMatches, multMatchesE, boundMult, setMultOf, abs_mult]
      by_cases hz : e.mults k = 0
      · simp only [hz, ite_true, decide_true, Bool.true_or, Bool.and_true]
        by_cases hi : inInterval lo hi m
        · simp [hi, hm, abs_setMult G κ e k m hm]
        · simp [hi]
      · simp only [hz, ite_false, decide_false, Bool.false_or]
        by_cases hi : inInterval lo hi m
        · by_cases he : e.mults k = m
          · have : m = e.mults k := he.symm
            subst this
            simp [hi, hm, Env.setMult_self]
          · have : ¬ m = e.mults k := fun h => he h.symm
            simp [hi, he, this]
        · simp [hi]

/-- Reference `multMatches` only changes `mult`; stated for `abs` through
`setMultOf`. -/
theorem abs_setMultOf_set (G : Graph) (κ : Var → Bool) (e : Env) (x : Var) (c : C) (μ : Mult)
    (m : Nat) (hx : κ x = false) (hc : G.find c = c) :
    abs G κ (setMultOf (e.set x c) μ m) = (abs G κ (setMultOf e μ m)).setCls x c := by
  rw [setMultOf_set, abs_set_cls G κ _ x c hx hc]

/-! ## Residuals -/

theorem zeroEntry_fst (c : C) (res : List (C × Nat)) :
    (zeroEntry c res).map (·.1) = res.map (·.1) := by
  induction res with
  | nil => rfl
  | cons p ps ih =>
      simp only [zeroEntry, List.map_cons, List.map_map] at ih ⊢
      by_cases h : p.1 = c
      · simp [h, ih]
      · simp [h, ih]

theorem mem_zeroEntry_fst {c : C} {res : List (C × Nat)} {q : C × Nat}
    (hq : q ∈ zeroEntry c res) : ∃ p ∈ res, p.1 = q.1 := by
  simp only [zeroEntry, List.mem_map] at hq
  obtain ⟨p, hp, hpq⟩ := hq
  refine ⟨p, hp, ?_⟩
  by_cases h : p.1 = c
  · simp [h] at hpq; rw [← hpq, h]
  · simp [h] at hpq; rw [hpq]

theorem entries_fst_nodup (m : Multiset C) : ((Multiset.entries m).map (·.1)).Nodup := by
  have : (Multiset.entries m).map (·.1) = m.toFinset.sort (· ≤ ·) := by
    simp only [Multiset.entries, List.map_map]
    exact List.map_id'' (fun _ => rfl) _
  rw [this]
  exact Finset.sort_nodup m.toFinset (· ≤ ·)

theorem mem_entries_fst {m : Multiset C} {p : C × Nat} (hp : p ∈ Multiset.entries m) : p.1 ∈ m := by
  simp only [Multiset.entries, List.mem_map] at hp
  obtain ⟨c, hc, rfl⟩ := hp
  exact Multiset.mem_toFinset.mp ((Finset.mem_sort (· ≤ ·)).mp hc)

theorem canonRes_entries (G : Graph) (m : Multiset C) (h : ∀ c ∈ m, G.find c = c) :
    canonRes G (Multiset.entries m) = Multiset.entries m := by
  unfold canonRes
  conv_rhs => rw [← List.map_id (Multiset.entries m)]
  apply List.map_congr_left
  intro p hp
  have := h p.1 (mem_entries_fst hp)
  ext <;> simp [this]

theorem map_find_sort (G : Graph) (s : Finset C) (h : ∀ c ∈ s, G.find c = c) :
    (s.sort (· ≤ ·)).map G.find = s.sort (· ≤ ·) := by
  conv_rhs => rw [← List.map_id (s.sort (· ≤ ·))]
  apply List.map_congr_left
  intro c hc
  exact h c ((Finset.mem_sort (· ≤ ·)).mp hc)

theorem all_zero_iff_filter_nil (res : List (C × Nat)) :
    res.all (fun p => p.2 = 0) = (res.filter (fun p => p.2 ≠ 0)).isEmpty := by
  induction res with
  | nil => rfl
  | cons p ps ih =>
      by_cases h : p.2 = 0
      · simp [h, ih]
      · simp [h]

/-! ## `acBinds` membership -/

theorem mem_acBinds_fst {elems : List (Var × Mult)} {rest : Option Var} {p : Var × Mult}
    (hp : p ∈ elems) : p.1 ∈ acBinds elems rest := by
  simp only [acBinds, List.mem_append, List.mem_map]
  exact Or.inl (Or.inl ⟨p, hp, rfl⟩)

theorem mem_acBinds_mult {elems : List (Var × Mult)} {rest : Option Var} {x k : Var}
    {lo : Nat} {hi : Option Nat} (hp : (x, .var k lo hi) ∈ elems) : k ∈ acBinds elems rest := by
  simp only [acBinds, List.mem_append, List.mem_filterMap]
  exact Or.inl (Or.inr ⟨(x, .var k lo hi), hp, rfl⟩)

theorem mem_acBinds_rest {elems : List (Var × Mult)} {r : Var} :
    r ∈ acBinds elems (some r) := by
  simp [acBinds]

theorem acBinds_cons_subset {p : Var × Mult} {elems : List (Var × Mult)} {rest : Option Var} :
    ∀ y ∈ acBinds elems rest, y ∈ acBinds (p :: elems) rest := by
  intro y hy
  simp only [acBinds, List.mem_append, List.mem_map, List.mem_filterMap] at hy ⊢
  rcases hy with (⟨q, hq, rfl⟩ | ⟨q, hq, hq'⟩) | h
  · exact Or.inl (Or.inl ⟨q, List.mem_cons_of_mem p hq, rfl⟩)
  · exact Or.inl (Or.inr ⟨q, List.mem_cons_of_mem p hq, hq'⟩)
  · exact Or.inr h

/-! ## `bindElems` and the rest writes commute -/

theorem bindElems_setSeqRest (xs : List Var) (cs : List C) (σ : Binding) (r : Var) (u : List C) :
    bindElems xs cs (σ.setSeqRest r u) = (bindElems xs cs σ).map (fun σ' => σ'.setSeqRest r u) := by
  induction xs generalizing cs σ with
  | nil => cases cs <;> rfl
  | cons x xs ih =>
      cases cs with
      | nil => rfl
      | cons c cs =>
          simp only [bindElems, Binding.setSeqRest]
          cases σ.cls x with
          | some c' =>
              simp only
              by_cases h : c' = c
              · simp only [h, ite_true]; exact ih cs σ
              · simp [h]
          | none =>
              simp only
              have := ih cs (σ.setCls x c)
              simp only [Binding.setSeqRest, Binding.setCls] at this
              exact this

theorem bindSeq_setSeqRest_comm (r : Option Var) (v : List C) (σ : Binding) (r' : Var) (u : List C)
    (h : ∀ a ∈ r, a ≠ r') :
    bindSeq r v (σ.setSeqRest r' u) = (bindSeq r v σ).setSeqRest r' u := by
  cases r with
  | none => rfl
  | some a =>
      simp only [bindSeq, Binding.setSeqRest]
      have hne := h a rfl
      congr 1
      exact Function.update_comm hne.symm (some u) (some v) σ.seqRest

/-! ## `nodeOf` and `childAt` -/

theorem nodeOf_some_find {G : Graph} (hG : G.ChildrenCanon) {e : Env} {v : Var} {n : Node}
    (h : e.nodeOf G v = some n) {pos : Nat} {c : C} (hc : n.children.childAt pos = some c) :
    G.find c = c :=
  Children.Canon.childAt (nodeOf_canon hG h) hc

end Semper.EMatch.Env
