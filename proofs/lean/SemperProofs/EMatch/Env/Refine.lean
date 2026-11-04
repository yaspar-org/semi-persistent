import SemperProofs.EMatch.Env.StepAC
import SemperProofs.EMatch.Env.StepACI
import SemperProofs.EMatch.Env.StepA
import SemperProofs.EMatch.Env.StepComm

/-!
# `(Restore)` and the refinement of the reference interpreter

`exec_spec`: for a well-formed plan and an entry environment bounded by
the plan's bound set, the executor returns the entry environment (spec
B.2, `(Restore)`) and emits, as a set, `run G plan (abs G κ e)` (spec
B.4). The two are proved together: the restore of the continuation is
what makes each loop iteration start from the same environment.

Graph hypotheses: `G.ChildrenCanon` (H2: stored children are `find`
fixed points, so the raw child the engine stores is the class the
reference binds) and `G.FindIdem` (`find` is a representative function,
H1; used by `CopyBinding`, which stores `canon(nodes[other])`).
-/

namespace Semper.EMatch.Env

open Semper.EMatch

theorem ContSpec.of_ih {G : Graph} {κ : Var → Bool} {ss : Plan} {B' : List Var}
    (ih : ∀ e, EnvOk e B' → (exec G κ ss e).2 = e ∧
      ∀ σ, σ ∈ (exec G κ ss e).1 ↔ σ ∈ run G ss (abs G κ e)) :
    ContSpec G κ (exec G κ ss) B' (run G ss) :=
  ⟨fun e he => (ih e he).1, fun e he => (ih e he).2⟩

theorem mem_run_cons' {G : Graph} {s : Step} {ss : Plan} {σ σ' : Binding} :
    σ' ∈ run G (s :: ss) σ ↔ ∃ σm ∈ runStep G s σ, σ' ∈ run G ss σm := by
  simp [run]

/-- The combined restore-and-refine statement. -/
theorem exec_spec (G : Graph) (κ : Var → Bool) (hG : G.ChildrenCanon) (hidem : G.FindIdem)
    {B : List Var} {plan : Plan} (hwf : WF κ B plan) :
    ∀ e, EnvOk e B → (exec G κ plan e).2 = e ∧
      ∀ σ, σ ∈ (exec G κ plan e).1 ↔ σ ∈ run G plan (abs G κ e) := by
  induction hwf with
  | nil => intro e _; simp [run]
  | @join B t ls ss ht hr _ ih =>
      intro e he
      have hk := ContSpec.of_ih ih
      have hres : ∀ id ∈ candidates G (abs G κ e) ls,
          (exec G κ ss (e.set t id)).2 = e.set t id :=
        fun id _ => hk.restore _ ((he.cons t).set (List.mem_cons_self ..) id)
      obtain ⟨h1, h2⟩ := loop_set (exec G κ ss) t (candidates G (abs G κ e) ls) e hres e
        (Env.setOpt_self e t)
      simp only [exec_cons, execStep]
      refine ⟨h2, fun σ => ?_⟩
      rw [h1, List.mem_flatMap, mem_run_cons']
      simp only [runStep, List.mem_map]
      constructor
      · rintro ⟨id, hid, hσ⟩
        refine ⟨joinBind G (abs G κ e) t id, ⟨id, hid, rfl⟩, ?_⟩
        rw [← abs_set_node G κ e t id ht]
        exact (hk.mem _ ((he.cons t).set (List.mem_cons_self ..) id) σ).mp hσ
      · rintro ⟨_, ⟨id, hid, rfl⟩, hσ⟩
        refine ⟨id, hid, ?_⟩
        rw [hk.mem _ ((he.cons t).set (List.mem_cons_self ..) id) σ, abs_set_node G κ e t id ht]
        exact hσ
  | @extractChild B v out pos ss hv hκv hout hκout _ ih =>
      intro e he
      have hk := ContSpec.of_ih ih
      simp only [exec_cons, execStep, run, runStep, abs_nodeOf G κ e v hκv]
      cases hn : e.nodeOf G v with
      | none => simp
      | some n =>
          simp only [hn]
          cases hc : n.children.childAt pos with
          | none => simp [hc]
          | some c =>
              simp only [hc]
              have hfc : G.find c = c := nodeOf_some_find hG hn hc
              have hout' : e.nodes out = none := he.nodes_none hout
              have he' : EnvOk (e.set out c) (out :: B) :=
                (he.cons out).set (List.mem_cons_self ..) c
              simp only [abs_cls, hout', Option.map_none]
              refine ⟨?_, fun σ => ?_⟩
              · simp only [hk.restore _ he', Env.clear_set e out c hout']
              · simp only [hk.mem _ he' σ, abs_set_cls G κ e out c hκout hfc,
                  List.flatMap_cons, List.flatMap_nil, List.append_nil]
  | @checkChildEq B v x pos ss hv hκv hx hκx _ ih =>
      intro e he
      have hk := ContSpec.of_ih ih
      simp only [exec_cons, execStep, run, runStep, abs_nodeOf G κ e v hκv, abs_cls]
      cases hn : e.nodeOf G v with
      | none => simp
      | some n =>
          cases hg : e.nodes x with
          | none => simp [hg]
          | some g =>
              simp only [hg, Option.map_some]
              cases hc : n.children.childAt pos with
              | none => simp [hc]
              | some c =>
                  have hfc : G.find c = c := nodeOf_some_find hG hn hc
                  simp only [hc, Option.some.injEq, hfc]
                  by_cases hceq : c = G.find g
                  · simp only [hceq, ite_true, hk.restore _ he, true_and, hk.mem _ he]
                    simp
                  · simp [hceq]
  | @checkEq B x y ss hx hκx hy hκy _ ih =>
      intro e he
      have hk := ContSpec.of_ih ih
      simp only [exec_cons, execStep, run, runStep, abs_cls]
      cases ha : e.nodes x with
      | none => simp [ha]
      | some a =>
          cases hb : e.nodes y with
          | none => simp [hb]
          | some b =>
              simp only [hb, Option.map_some]
              by_cases hab : G.find a = G.find b
              · simp only [hab, ite_true, hk.restore _ he, true_and, hk.mem _ he]
                simp
              · simp [hab]
  | @copyBinding B t o ss ho ht hκt _ ih =>
      intro e he
      have hk := ContSpec.of_ih ih
      simp only [exec_cons, execStep, run, runStep, abs_cls]
      cases hg : e.nodes o with
      | none => simp [hg]
      | some g =>
          simp only [hg]
          have ht' : e.nodes t = none := he.nodes_none ht
          have he' : EnvOk (e.set t (G.find g)) (t :: B) :=
            (he.cons t).set (List.mem_cons_self ..) (G.find g)
          simp only [Option.map_some, ht', Option.map_none]
          refine ⟨?_, fun σ => ?_⟩
          · simp only [hk.restore _ he', Env.clear_set e t (G.find g) ht']
          · simp only [hk.mem _ he' σ, abs_set_cls G κ e t (G.find g) hκt (hidem g),
              List.flatMap_cons, List.flatMap_nil, List.append_nil]
  | @decomposeAC B v elems rest ss hv hκv helems hrest _ ih =>
      intro e he
      have hk := ContSpec.of_ih ih
      simp only [exec_cons, execStep, run, runStep, abs_nodeOf G κ e v hκv]
      cases hn : e.nodeOf G v with
      | none => simp [hn]
      | some n =>
          obtain ⟨op, ch⟩ := n
          have hcan := nodeOf_canon hG hn
          cases ch with
          | mset m =>
              simp only
              have hm : ∀ c ∈ m, G.find c = c := hcan
              rw [canonRes_entries G m hm]
              have he' : EnvOk e (acBinds elems rest ++ B) := he.append_left _
              obtain ⟨h1, h2⟩ := execAC_spec G κ hk elems rest (Multiset.entries m) e he'
                (fun r hr => he.msetSpan_none (hrest r hr)) helems
                (fun y hy => List.mem_append_left _ hy)
                (fun p hp => hm p.1 (mem_entries_fst hp)) (entries_fst_nodup m)
              refine ⟨h1, fun σ => ?_⟩
              rw [h2 σ, List.mem_flatMap]
          | tuple cs => simp
          | spair a b => simp
          | seq cs => simp
          | set s => simp
  | @decomposeACI B v elems rest ss hv hκv helems hrest _ ih =>
      intro e he
      have hk := ContSpec.of_ih ih
      simp only [exec_cons, execStep, run, runStep, abs_nodeOf G κ e v hκv]
      cases hn : e.nodeOf G v with
      | none => simp [hn]
      | some n =>
          obtain ⟨op, ch⟩ := n
          have hcan := nodeOf_canon hG hn
          cases ch with
          | set s =>
              simp only
              have hs : ∀ c ∈ s, G.find c = c := hcan
              rw [map_find_sort G s hs]
              have he' : EnvOk e (elems ++ rest.toList ++ B) := he.append_left _
              obtain ⟨h1, h2⟩ := execACI_spec G κ hk elems rest (s.sort (· ≤ ·)) e he'
                (fun r hr => he.setSpan_none (hrest r hr)) helems
                (fun y hy => List.mem_append_left _ hy)
                (fun c hc => hs c ((Finset.mem_sort (· ≤ ·)).mp hc))
              refine ⟨h1, fun σ => ?_⟩
              rw [h2 σ, List.mem_flatMap]
          | tuple cs => simp
          | spair a b => simp
          | seq cs => simp
          | mset m => simp
  | @expandA B v pre suf elems ss hv hκv helems hpre hsuf hdist _ ih =>
      intro e he
      have hk := ContSpec.of_ih ih
      simp only [exec_cons, execStep, run, runStep, abs_nodeOf G κ e v hκv]
      cases hn : e.nodeOf G v with
      | none => simp [hn]
      | some n =>
          obtain ⟨op, ch⟩ := n
          have hcan := nodeOf_canon hG hn
          cases ch with
          | seq cs =>
              simp only
              have hcs : ∀ c ∈ cs, G.find c = c := hcan
              have he' : EnvOk e (pre.toList ++ elems ++ suf.toList ++ B) := he.append_left _
              obtain ⟨h1, h2⟩ := execExpandA_spec G κ hk pre elems suf cs e he'
                (fun r hr => he.seqSpan_none (hpre r hr))
                (fun r hr => he.seqSpan_none (hsuf r hr)) hdist helems
                (fun y hy => List.mem_append_left _ hy) hcs
              refine ⟨h1, fun σ => ?_⟩
              rw [h2 σ, List.mem_flatMap]
          | tuple cs => simp
          | spair a b => simp
          | mset m => simp
          | set s => simp
  | @decomposeComm B v x y ss hv hκv hκx hκy _ ih =>
      intro e he
      have hk := ContSpec.of_ih ih
      simp only [exec_cons, execStep, run, runStep, abs_nodeOf G κ e v hκv]
      cases hn : e.nodeOf G v with
      | none => simp [hn]
      | some n =>
          obtain ⟨op, ch⟩ := n
          have hcan := nodeOf_canon hG hn
          cases ch with
          | spair a b =>
              simp only
              have hab : G.find a = a ∧ G.find b = b := hcan
              rw [hab.1, hab.2]
              have he' : EnvOk e (x :: y :: B) := (he.cons y).cons x
              obtain ⟨h1, h2⟩ := execPair_spec G κ hk x y a b e he' hκx hκy
                (List.mem_cons_self ..) (List.mem_cons_of_mem x (List.mem_cons_self ..))
                hab.1 hab.2
              refine ⟨h1, fun σ => ?_⟩
              rw [h2 σ, List.mem_flatMap]
          | tuple cs => simp
          | seq cs => simp
          | mset m => simp
          | set s => simp

/-- **(Restore)**, spec B.2: on return from `run_step` the environment
equals its value on entry, on `nodes`, `mults` and the three pools and
spans. Hypotheses: the plan is `WF` and the entry environment binds only
the plan's bound set `B`. The fields outside the model (`lit_vals`, the
`mults` written by `Collect`'s `fill`) are the spec's stated exceptions
and are not covered. -/
theorem restore (G : Graph) (κ : Var → Bool) (hG : G.ChildrenCanon) (hidem : G.FindIdem)
    {B : List Var} {plan : Plan} (hwf : WF κ B plan) (e : Env) (he : EnvOk e B) :
    (exec G κ plan e).2 = e :=
  (exec_spec G κ hG hidem hwf e he).1

/-- **Refinement**, spec B.4: the environments the engine emits from `e`
are, as a set, the bindings the reference interpreter emits from
`abs G κ e`. -/
theorem refine (G : Graph) (κ : Var → Bool) (hG : G.ChildrenCanon) (hidem : G.FindIdem)
    {B : List Var} {plan : Plan} (hwf : WF κ B plan) (e : Env) (he : EnvOk e B) (σ : Binding) :
    σ ∈ (exec G κ plan e).1 ↔ σ ∈ run G plan (abs G κ e) :=
  (exec_spec G κ hG hidem hwf e he).2 σ

/-- The refinement from the empty environment: `abs` of `Match::new` is
`Binding.empty`. -/
theorem abs_empty (G : Graph) (κ : Var → Bool) : abs G κ Env.empty = Binding.empty := by
  refine Binding.ext' ?_ ?_ ?_ ?_ ?_ ?_ <;> funext x <;> simp [Env.empty, Binding.empty, Env.slice]

theorem refine_empty (G : Graph) (κ : Var → Bool) (hG : G.ChildrenCanon) (hidem : G.FindIdem)
    {plan : Plan} (hwf : WF κ [] plan) (σ : Binding) :
    σ ∈ (exec G κ plan Env.empty).1 ↔ σ ∈ run G plan Binding.empty := by
  rw [refine G κ hG hidem hwf Env.empty EnvOk.empty σ, abs_empty]

end Semper.EMatch.Env
