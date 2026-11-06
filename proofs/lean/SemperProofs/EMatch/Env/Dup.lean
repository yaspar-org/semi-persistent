import SemperProofs.EMatch.Env.Lemmas

/-!
# Duplicates (spec C): the commutative pair, and AC without duplicates

`MatchSet::push` appends (`ematch.rs:852-915`): the engine's output is a
multiset. Spec C.1: a commutative pattern `(Eq x y)` on a node `Eq(a, a)`
yields `{x ↦ a, y ↦ a}` twice, in the engine and in the reference
(`decomposeComm` lists both orders). `comm_pair_duplicate_run` and
`comm_pair_duplicate_exec` exhibit it on a one-node graph.

A finding beyond the spec: when the pair's *first* element is already
bound (non-linear pattern, e.g. `f(x, Eq(x, y))`) and `a = b`, the
reference emits the binding twice (`bindElems` succeeds in both orders)
while the engine's bound path takes the first entry of that class once
(`ematch.rs:2385-2390`): `comm_bound_first_run` has two elements,
`comm_bound_first_exec` one. This is why `refine` is stated as set
membership and not as list or multiset equality.

Spec C.2: on a multiset node with distinct classes (H2) the AC
decomposition emits no duplicate: `decomposeAC_nodup`.
-/

namespace Semper.EMatch.Env

open Semper.EMatch

/-! ## The commutative pair -/

/-- One node `Eq(1, 1)` (operator `0`), `find` the identity. -/
def pairGraph : Graph := ⟨[(0, ⟨0, .spair 1 1⟩)], fun c => c⟩

/-- `(Eq x y)` with `x = 1`, `y = 2`, node variable `0`. -/
def pairPlan : Plan := [.join 0 [.byOp 0], .decomposeComm 0 1 2]

/-- Node variables: `0`, the plan's join target. -/
def pairκ : Var → Bool := fun v => decide (v = 0)

theorem pairPlan_wf : WF (fun _ => false) [] pairPlan :=
  WF.join (by simp [Lookup.reads]) (WF.decomposeComm (List.mem_cons_self ..) (by simp) WF.nil)

/-- `pairκ` is the kinds the plan ends with. -/
theorem pairκ_eq : planKinds pairPlan = pairκ := by
  funext v; by_cases h : v = 0 <;> simp [pairPlan, joinKinds, pairκ, h, Function.update]

theorem pairGraph_canon : pairGraph.ChildrenCanon := by
  intro p hp
  simp [pairGraph] at hp
  subst hp
  exact ⟨rfl, rfl⟩

theorem pairGraph_idem : pairGraph.FindIdem := fun _ => rfl

@[simp] theorem pairGraph_find (c : C) : pairGraph.find c = c := rfl

/-- The reference lists the binding `{x ↦ 1, y ↦ 1}` twice. -/
theorem comm_pair_duplicate_run :
    ∃ σ, run pairGraph pairPlan Binding.empty = [σ, σ] ∧
      σ.cls 1 = some 1 ∧ σ.cls 2 = some 1 := by
  refine ⟨_, rfl, ?_, ?_⟩ <;> rfl

/-- The engine emits the same environment twice: once with `x` at entry
`0` and `y` at entry `1`, once the other way round. -/
theorem comm_pair_duplicate_exec :
    ∃ σ, (exec pairGraph pairκ pairPlan Env.empty).1 = [σ, σ] ∧
      σ.cls 1 = some 1 ∧ σ.cls 2 = some 1 := by
  have h1 : (Env.empty.set 0 0).nodes 1 = none := by simp [Env.empty]
  have h2 : ((Env.empty.set 0 0).set 1 1).nodes 2 = none := by simp [Env.empty]
  have hn : (Env.empty.set 0 0).nodeOf pairGraph 0 = some ⟨0, .spair 1 1⟩ := by
    simp [Env.nodeOf, Env.empty, pairGraph, Graph.lookupNode]
  have hc : candidates pairGraph (abs pairGraph pairκ Env.empty) [.byOp 0] = [0] := by
    simp [candidates, Lookup.bucket, Graph.byOp, pairGraph]
  refine ⟨abs pairGraph pairκ ((Env.empty.set 0 0).set 1 1 |>.set 2 1), ?_, ?_, ?_⟩
  · simp only [pairPlan, exec_cons, exec_nil, execStep, hc, loop_cons, loop_nil, hn, execPair,
      execPairSnd, h1, pairGraph_find, h2, Env.clear_set _ _ _ h2, Env.clear_set _ _ _ h1,
      List.append_nil, List.cons_append, List.nil_append]
  · simp [Env.empty]
  · simp [Env.empty]

/-! ## The first element bound: reference two, engine one -/

/-- `f(x, Eq(x, y))`-like plan: `x = 1` is bound by `ExtractChild` before the
pair is decomposed (here the pair node is its own "parent": the plan only
needs `x` bound to class `1`). -/
def pairPlanBound : Plan := [.join 0 [.byOp 0], .extractChild 0 0 1, .decomposeComm 0 1 2]

theorem pairPlanBound_wf : WF (fun _ => false) [] pairPlanBound := by
  refine WF.join (by simp [Lookup.reads]) ?_
  refine WF.extractChild (List.mem_cons_self ..) (by simp) (by simp) ?_
  exact WF.decomposeComm (List.mem_cons_of_mem _ (List.mem_cons_self ..)) (by simp) WF.nil

theorem pairκ_eq_bound : planKinds pairPlanBound = pairκ := by
  funext v; by_cases h : v = 0 <;> simp [pairPlanBound, joinKinds, pairκ, h, Function.update]

/-- The reference interpreter emits the binding twice. -/
theorem comm_bound_first_run : (run pairGraph pairPlanBound Binding.empty).length = 2 := rfl

/-- The engine emits it once. -/
theorem comm_bound_first_exec : (exec pairGraph pairκ pairPlanBound Env.empty).1.length = 1 := by
  have h1 : (Env.empty.set 0 0).nodes 1 = none := by simp [Env.empty]
  have h2 : ((Env.empty.set 0 0).set 1 1).nodes 2 = none := by simp [Env.empty]
  have hn : (Env.empty.set 0 0).nodeOf pairGraph 0 = some ⟨0, .spair 1 1⟩ := by
    simp [Env.nodeOf, Env.empty, pairGraph, Graph.lookupNode]
  have hn' : ((Env.empty.set 0 0).set 1 1).nodeOf pairGraph 0 = some ⟨0, .spair 1 1⟩ := by
    simp [Env.nodeOf, Env.empty, pairGraph, Graph.lookupNode]
  have h1' : ((Env.empty.set 0 0).set 1 1).nodes 1 = some 1 := by simp
  have hc : candidates pairGraph (abs pairGraph pairκ Env.empty) [.byOp 0] = [0] := by
    simp [candidates, Lookup.bucket, Graph.byOp, pairGraph]
  simp only [pairPlanBound, exec_cons, exec_nil, execStep, hc, loop_cons, loop_nil, hn, hn',
    Children.childAt, h1, h1', execPair, execPairSnd, h2, pairGraph_find, ite_true,
    Env.clear_set _ _ _ h2, Env.clear_set _ _ _ h1, List.append_nil, List.length_singleton]

/-! ## AC decompositions do not duplicate (H2) -/

theorem multMatches_cls {σ σ₁ : Binding} {μ : Mult} {m : Nat} (h : multMatches σ μ m = some σ₁) :
    σ₁.cls = σ.cls := by
  cases μ with
  | exact n =>
      simp only [multMatches] at h
      split at h
      · cases h; rfl
      · cases h
  | var k lo hi =>
      simp only [multMatches] at h
      split at h
      · split at h
        · split at h
          · cases h; rfl
          · cases h
        · cases h; rfl
      · cases h

theorem decomposeAC_cls_mono (es : List (Var × Mult)) (rest : Option Var) :
    ∀ (res : List (C × Nat)) (σ σ' : Binding), σ' ∈ decomposeAC es rest res σ →
      ∀ y c, σ.cls y = some c → σ'.cls y = some c := by
  induction es with
  | nil =>
      intro res σ σ' h y c hy
      cases rest with
      | none =>
          simp only [decomposeAC] at h
          split at h
          · rw [List.mem_singleton] at h; subst h; exact hy
          · simp at h
      | some r =>
          simp only [decomposeAC, List.mem_singleton] at h
          subst h; simpa [Binding.setRest] using hy
  | cons p es ih =>
      intro res σ σ' h y c hy
      obtain ⟨x, μ⟩ := p
      unfold decomposeAC at h
      cases hx : σ.cls x with
      | some cx =>
          rw [hx] at h; dsimp only at h
          cases hf : res.find? (fun e => e.1 = cx ∧ e.2 ≠ 0) with
          | none => rw [hf] at h; simp at h
          | some e =>
              rw [hf] at h; dsimp only at h
              cases hm : multMatches σ μ e.2 with
              | none => rw [hm] at h; simp at h
              | some σ₁ =>
                  rw [hm] at h; dsimp only at h
                  exact ih _ σ₁ σ' h y c (by rw [multMatches_cls hm]; exact hy)
      | none =>
          rw [hx] at h; dsimp only at h; rw [List.mem_flatMap] at h
          obtain ⟨e, _, he⟩ := h
          split at he
          · simp at he
          · cases hm : multMatches σ μ e.2 with
            | none => rw [hm] at he; simp at he
            | some σ₁ =>
                rw [hm] at he; dsimp only at he
                refine ih _ _ σ' he y c ?_
                have hyx : y ≠ x := fun h' => by subst h'; rw [hx] at hy; cases hy
                simp [Binding.setCls, Function.update_of_ne hyx, multMatches_cls hm, hy]

/-- Spec C.2: on a residual with distinct classes, `decomposeAC` emits no
binding twice: two choices differing at some element bind that element's
variable to different classes. -/
theorem decomposeAC_nodup (es : List (Var × Mult)) (rest : Option Var) :
    ∀ (res : List (C × Nat)) (σ : Binding), (res.map (·.1)).Nodup →
      (decomposeAC es rest res σ).Nodup := by
  induction es with
  | nil =>
      intro res σ _
      cases rest with
      | none => simp only [decomposeAC]; split <;> simp
      | some r => simp [decomposeAC]
  | cons p es ih =>
      intro res σ hnd
      obtain ⟨x, μ⟩ := p
      unfold decomposeAC
      cases hx : σ.cls x with
      | some cx =>
          dsimp only
          cases hf : res.find? (fun e => e.1 = cx ∧ e.2 ≠ 0) with
          | none => simp
          | some e =>
              dsimp only
              cases hm : multMatches σ μ e.2 with
              | none => simp
              | some σ₁ => dsimp only; exact ih _ σ₁ (by rw [zeroEntry_fst]; exact hnd)
      | none =>
          dsimp only
          rw [List.nodup_flatMap]
          refine ⟨fun e _ => ?_, ?_⟩
          · split
            · simp
            · cases hm : multMatches σ μ e.2 with
              | none => simp
              | some σ₁ => exact ih _ _ (by rw [zeroEntry_fst]; exact hnd)
          · have hpw : res.Pairwise (fun a b => a.1 ≠ b.1) := by
              rw [List.Nodup, List.pairwise_map] at hnd
              exact hnd
            refine hpw.imp ?_
            intro a b hab
            simp only [Function.onFun]
            rw [List.disjoint_left]
            intro σ' ha hb
            have key : ∀ (e : C × Nat), ∀ σ'' ∈ (if e.2 = 0 then []
                else match multMatches σ μ e.2 with
                  | some σ₁ => decomposeAC es rest (zeroEntry e.1 res) (σ₁.setCls x e.1)
                  | none => []), σ''.cls x = some e.1 := by
              intro e σ'' h
              split at h
              · simp at h
              · cases hm : multMatches σ μ e.2 with
                | none => rw [hm] at h; simp at h
                | some σ₁ =>
                    rw [hm] at h; dsimp only at h
                    exact decomposeAC_cls_mono es rest _ _ σ'' h x e.1 (by simp [Binding.setCls])
            have h1 := key a σ' ha
            have h2 := key b σ' hb
            rw [h1] at h2
            exact hab (Option.some.inj h2)

end Semper.EMatch.Env
