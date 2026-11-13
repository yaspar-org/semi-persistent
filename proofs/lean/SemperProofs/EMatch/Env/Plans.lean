import SemperProofs.EMatch.Env.Main
import SemperProofs.EMatch.Engine.Plan
import SemperProofs.EMatch.Engine.WF

/-!
# The scheduler's plans are well formed for the executor

`planOK_envWF`: every plan the scheduler emits (`PlanOK`, the grammar
`Sched`) is `WF` for the executor from `Match::new`, under the resolver's
variable discipline (`EnvAtomsWF`): a class variable is no multiplicity or
rest variable, rest variables are linear, an atom's prefix and suffix rests
are distinct, no annotation is `exact 0`. Nested patterns are covered: a
nested child variable is bound as a class by its parent (`ExtractChild`,
a decomposition) and refined to a node by the nested atom's join, or bound
as a node by the nested atom first and read as a class by the parent.

`exec_matches` composes `env_refine_empty` with `plan_matches`: the
executor with undo emits, as a set, exactly the bindings satisfying every
atom.

`nested_plan_*` work the pattern `(f (g x) y)` both ways round.
-/

namespace Semper.EMatch.Env

open Semper.EMatch

/-- The AC elements of an atom. -/
def acElems (a : RAtom) : List (Var × Mult) :=
  match a.shape with
  | .ac es _ => es
  | _ => []

/-- The resolver's variable discipline, as the executor needs it: a class
variable of any atom (an atom's `binds`, an `Eq` operand) is no
multiplicity or rest variable, a multiplicity variable is no rest variable,
rest variables are linear across atoms, an atom's prefix and suffix rests
are distinct, and no AC annotation is `exact 0` (`resolve.rs:1999`). -/
structure EnvAtomsWF (atoms : List QAtom) : Prop where
  clsNotMult : ∀ q ∈ atoms, ∀ a, QAtom.scan a ∈ atoms → ∀ x ∈ q.binds, x ∉ a.multVars
  clsNotRest : ∀ q ∈ atoms, ∀ a, QAtom.scan a ∈ atoms → ∀ x ∈ q.binds, x ∉ a.restVars
  multNotRest : ∀ a b, QAtom.scan a ∈ atoms → QAtom.scan b ∈ atoms →
    ∀ k ∈ a.multVars, k ∉ b.restVars
  restLinear : ∀ (i j : Nat) (a b : RAtom), atoms[i]? = some (.scan a) →
    atoms[j]? = some (.scan b) → i ≠ j → ∀ r ∈ a.restVars, r ∉ b.restVars
  seqNodup : ∀ a, QAtom.scan a ∈ atoms → a.seqRestVars.Nodup
  noZero : ∀ a, QAtom.scan a ∈ atoms → ∀ p ∈ acElems a, p.2 ≠ .exact 0

/-! ## What a lowering binds -/

theorem childSteps_bound (n : Var) : ∀ (cs : List Var) (i : Nat) (B' : Finset Var) (L : List Var),
    ∀ x ∈ boundAfter L (childSteps n cs i B'), x ∈ L ∨ x ∈ cs := by
  intro cs
  induction cs with
  | nil => intro i B' L x hx; exact Or.inl hx
  | cons c cs ih =>
      intro i B' L x hx
      simp only [childSteps] at hx
      split at hx
      · rcases ih (i + 1) B' L x hx with h | h
        · exact Or.inl h
        · exact Or.inr (List.mem_cons_of_mem c h)
      · rcases ih (i + 1) (insert c B') (c :: L) x hx with h | h
        · rcases List.mem_cons.1 h with rfl | h
          · exact Or.inr (List.mem_cons_self ..)
          · exact Or.inl h
        · exact Or.inr (List.mem_cons_of_mem c h)

/-- A lowering binds the atom's class, multiplicity and rest variables. -/
theorem lower_bound (a : RAtom) (B : Finset Var) (L : List Var) :
    ∀ x ∈ boundAfter L (lower a B),
      x ∈ L ∨ x ∈ a.binds ∨ x ∈ a.multVars ∨ x ∈ a.restVars := by
  obtain ⟨n, f, sh⟩ := a
  intro x hx
  have hn : n ∈ RAtom.binds ⟨n, f, sh⟩ := Finset.mem_insert_self _ _
  have hel : ∀ y ∈ RAtom.elems ⟨n, f, sh⟩, y ∈ RAtom.binds ⟨n, f, sh⟩ :=
    fun y hy => Finset.mem_insert_of_mem (List.mem_toFinset.2 hy)
  cases sh with
  | plain cs =>
      simp only [lower, lowerBody, boundAfter, stepBound] at hx
      rcases childSteps_bound n cs 0 _ (n :: L) x hx with h | h
      · rcases List.mem_cons.1 h with rfl | h
        · exact Or.inr (Or.inl hn)
        · exact Or.inl h
      · exact Or.inr (Or.inl (hel x h))
  | comm y z =>
      simp only [lower, lowerBody, boundAfter, stepBound, List.mem_cons] at hx
      rcases hx with rfl | rfl | rfl | h
      · exact Or.inr (Or.inl (hel _ (by simp [RAtom.elems])))
      · exact Or.inr (Or.inl (hel _ (by simp [RAtom.elems])))
      · exact Or.inr (Or.inl hn)
      · exact Or.inl h
  | assoc pre fx suf =>
      simp only [lower, lowerBody, boundAfter, stepBound, List.mem_append, List.mem_cons,
        Option.mem_toList] at hx
      rcases hx with ((h | h) | h) | rfl | h
      · exact Or.inr (Or.inr (Or.inr (by simp [RAtom.restVars, RAtom.seqRestVars, h])))
      · exact Or.inr (Or.inl (hel x (by simpa [RAtom.elems] using h)))
      · exact Or.inr (Or.inr (Or.inr (by simp [RAtom.restVars, RAtom.seqRestVars, h])))
      · exact Or.inr (Or.inl hn)
      · exact Or.inl h
  | ac es rest =>
      simp only [lower, lowerBody, boundAfter, stepBound, acBinds, List.mem_append,
        List.mem_cons, Option.mem_toList, List.mem_map, List.mem_filterMap] at hx
      rcases hx with ((⟨p, hp, rfl⟩ | ⟨p, hp, hk⟩) | h) | rfl | h
      · exact Or.inr (Or.inl (hel _ (by simp only [RAtom.elems, List.mem_map]; exact ⟨p, hp, rfl⟩)))
      · obtain ⟨y, μ⟩ := p
        cases μ with
        | exact m => simp at hk
        | var k lo hi =>
            simp only [Option.some.injEq] at hk
            subst hk
            refine Or.inr (Or.inr (Or.inl ?_))
            simp only [RAtom.multVars, multVars, List.mem_flatMap]
            exact ⟨(y, .var k lo hi), hp, by simp [Mult.vars]⟩
      · exact Or.inr (Or.inr (Or.inr (by simp [RAtom.restVars, RAtom.msetRestVars, h])))
      · exact Or.inr (Or.inl hn)
      · exact Or.inl h
  | aci es rest =>
      simp only [lower, lowerBody, boundAfter, stepBound, List.mem_append, List.mem_cons,
        Option.mem_toList] at hx
      rcases hx with (h | h) | rfl | h
      · exact Or.inr (Or.inl (hel x (by simpa [RAtom.elems] using h)))
      · exact Or.inr (Or.inr (Or.inr (by simp [RAtom.restVars, RAtom.setRestVars, h])))
      · exact Or.inr (Or.inl hn)
      · exact Or.inl h

/-! ## One lowering is well formed -/

theorem childSteps_envWF (O : Var → Prop) (n : Var) {κ : Var → Bool} (hκn : κ n = true) :
    ∀ (cs : List Var) (i : Nat) (B' : Finset Var) (L : List Var) (ss : Plan),
      n ∈ L → (∀ x ∈ B', x ∈ L) → (∀ x ∈ L, x ∈ B' ∨ O x) → (∀ c ∈ cs, ¬ O c) →
      WF κ (boundAfter L (childSteps n cs i B')) ss → WF κ L (childSteps n cs i B' ++ ss) := by
  intro cs
  induction cs with
  | nil => intro i B' L ss _ _ _ _ h; exact h
  | cons c cs ih =>
      intro i B' L ss hn hBL hLB hO h
      have hO' : ∀ d ∈ cs, ¬ O d := fun d hd => hO d (List.mem_cons_of_mem c hd)
      by_cases hc : c ∈ B'
      · simp only [childSteps, hc, ite_true, boundAfter, stepBound, List.cons_append] at h ⊢
        exact WF.checkChildEq hn hκn (hBL c hc) (ih (i + 1) B' L ss hn hBL hLB hO' h)
      · simp only [childSteps, hc, ite_false, boundAfter, stepBound, List.cons_append] at h ⊢
        have hcL : c ∉ L := by
          intro hcL
          rcases hLB c hcL with h' | h'
          · exact hc h'
          · exact hO c (List.mem_cons_self ..) h'
        refine WF.extractChild hn hκn hcL (ih (i + 1) (insert c B') (c :: L) ss
          (List.mem_cons_of_mem c hn) ?_ ?_ hO' h)
        · intro x hx
          rcases Finset.mem_insert.1 hx with rfl | hx
          · exact List.mem_cons_self ..
          · exact List.mem_cons_of_mem _ (hBL x hx)
        · intro x hx
          rcases List.mem_cons.1 hx with rfl | hx
          · exact Or.inl (Finset.mem_insert_self _ _)
          · rcases hLB x hx with h' | h'
            · exact Or.inl (Finset.mem_insert_of_mem h')
            · exact Or.inr h'

/-- The lowering of one atom is well formed, its join making the atom's
node variable a node variable, whatever the kinds before it. `O` holds of
the multiplicity and rest variables already bound. -/
theorem lower_envWF (O : Var → Prop) (a : RAtom) (B : Finset Var) (L : List Var)
    (hBL : ∀ x ∈ B, x ∈ L) (hLB : ∀ x ∈ L, x ∈ B ∨ O x)
    (hbinds : ∀ x ∈ a.binds, ¬ O x)
    (hrest : ∀ r ∈ a.restVars, r ∉ B ∧ ¬ O r ∧ r ∉ a.binds)
    (hseq : a.seqRestVars.Nodup) (hzero : ∀ p ∈ acElems a, p.2 ≠ .exact 0)
    (κ : Var → Bool) (ss : Plan)
    (hss : WF (Function.update κ a.node true) (boundAfter L (lower a B)) ss) :
    WF κ L (lower a B ++ ss) := by
  obtain ⟨n, f, sh⟩ := a
  have hreads : ∀ l ∈ joinLookups ⟨n, f, sh⟩ B, ∀ x ∈ l.reads, x ∈ L :=
    fun l hl x hx => hBL x (joinLookups_reads ⟨n, f, sh⟩ B l hl x hx)
  have hκn : Function.update κ n true n = true := by simp
  have hnL : n ∈ n :: L := List.mem_cons_self ..
  have hfresh : ∀ r ∈ RAtom.restVars ⟨n, f, sh⟩, r ∉ n :: L := by
    intro r hr hrL
    obtain ⟨hrB, hrO, hrb⟩ := hrest r hr
    rcases List.mem_cons.1 hrL with rfl | hrL
    · exact hrb (Finset.mem_insert_self _ _)
    · rcases hLB r hrL with h | h
      · exact hrB h
      · exact hrO h
  simp only [lower, List.cons_append]
  refine WF.join hreads ?_
  cases sh with
  | plain cs =>
      simp only [lowerBody]
      refine childSteps_envWF O n hκn cs 0 (insert n B) (n :: L) ss hnL ?_ ?_ ?_ hss
      · intro x hx
        rcases Finset.mem_insert.1 hx with rfl | hx
        · exact hnL
        · exact List.mem_cons_of_mem _ (hBL x hx)
      · intro x hx
        rcases List.mem_cons.1 hx with rfl | hx
        · exact Or.inl (Finset.mem_insert_self _ _)
        · rcases hLB x hx with h | h
          · exact Or.inl (Finset.mem_insert_of_mem h)
          · exact Or.inr h
      · intro c hc
        exact hbinds c (Finset.mem_insert_of_mem (List.mem_toFinset.2 hc))
  | comm y z =>
      exact WF.decomposeComm hnL hκn hss
  | assoc pre fx suf =>
      refine WF.expandA hnL hκn ?_ ?_ ?_ hss
      · intro r hr; exact hfresh r (by simp only [RAtom.restVars, RAtom.seqRestVars, RAtom.msetRestVars, RAtom.setRestVars, List.mem_append, Option.mem_toList, List.not_mem_nil, or_false]; tauto)
      · intro r hr; exact hfresh r (by simp only [RAtom.restVars, RAtom.seqRestVars, RAtom.msetRestVars, RAtom.setRestVars, List.mem_append, Option.mem_toList, List.not_mem_nil, or_false]; tauto)
      · intro r hr hsr
        subst hr; subst hsr
        simp [RAtom.seqRestVars] at hseq
  | ac es rest =>
      refine WF.decomposeAC hnL hκn (fun p hp => hzero p hp) ?_ hss
      intro r hr; exact hfresh r (by simp only [RAtom.restVars, RAtom.seqRestVars, RAtom.msetRestVars, RAtom.setRestVars, List.mem_append, Option.mem_toList, List.not_mem_nil, or_false]; tauto)
  | aci es rest =>
      refine WF.decomposeACI hnL hκn ?_ hss
      intro r hr; exact hfresh r (by simp only [RAtom.restVars, RAtom.seqRestVars, RAtom.msetRestVars, RAtom.setRestVars, List.mem_append, Option.mem_toList, List.not_mem_nil, or_false]; tauto)

/-! ## Every scheduled plan is well formed -/

/-- The multiplicity and rest variables of the atoms used so far. -/
def UsedOther (atoms : List QAtom) (used : Finset Nat) (x : Var) : Prop :=
  ∃ (i : Nat) (a : RAtom), atoms[i]? = some (.scan a) ∧ i ∈ used ∧
    (x ∈ a.multVars ∨ x ∈ a.restVars)

theorem sched_envWF {atoms : List QAtom} (hA : EnvAtomsWF atoms) {used : Finset Nat}
    {Bs : Finset Var} {plan : Plan} (h : Sched atoms used Bs plan) :
    ∀ (κ : Var → Bool) (L : List Var), (∀ x ∈ Bs, x ∈ L) →
      (∀ x ∈ L, x ∈ Bs ∨ UsedOther atoms used x) →
      (∀ x ∈ Bs, ∃ q ∈ atoms, x ∈ q.binds) → WF κ L plan := by
  induction h with
  | done _ _ => intro κ L _ _ _; exact WF.nil
  | @eager used B i q rest hi hnot hfree _ ih =>
      intro κ L hBL hLB hcls
      have hq : q ∈ atoms := List.mem_of_getElem? hi
      have hmono : ∀ x, UsedOther atoms used x → UsedOther atoms (insert i used) x := by
        rintro x ⟨j, a, hj, hju, hx⟩; exact ⟨j, a, hj, Finset.mem_insert_of_mem hju, hx⟩
      have hcls' : ∀ x ∈ B ∪ q.binds, ∃ q ∈ atoms, x ∈ q.binds := by
        intro x hx
        rcases Finset.mem_union.1 hx with hx | hx
        · exact hcls x hx
        · exact ⟨q, hq, hx⟩
      -- a class variable of `q` outside `B` is not bound
      have hnotL : ∀ x ∈ q.binds, x ∉ B → x ∉ L := by
        intro x hxq hxB hxL
        rcases hLB x hxL with h | ⟨j, a, hj, -, hx | hx⟩
        · exact hxB h
        · exact hA.clsNotMult q hq a (List.mem_of_getElem? hj) x hxq hx
        · exact hA.clsNotRest q hq a (List.mem_of_getElem? hj) x hxq hx
      cases q with
      | scan a => exact absurd hfree (by simp [QAtom.eagerFree])
      | eq x y =>
          have hxq : x ∈ (QAtom.eq x y).binds := by simp [QAtom.binds]
          have hyq : y ∈ (QAtom.eq x y).binds := by simp [QAtom.binds]
          simp only [QAtom.eagerLower]
          by_cases hx : x ∈ B
          · by_cases hy : y ∈ B
            · simp only [hx, hy, ite_true, List.singleton_append]
              refine WF.checkEq (hBL x hx) (hBL y hy) (ih κ L ?_ ?_ hcls')
              · intro z hz
                rcases Finset.mem_union.1 hz with hz | hz
                · exact hBL z hz
                · simp only [QAtom.binds, Finset.mem_insert, Finset.mem_singleton] at hz
                  rcases hz with rfl | rfl
                  · exact hBL _ hx
                  · exact hBL _ hy
              · intro z hz
                rcases hLB z hz with h | h
                · exact Or.inl (Finset.mem_union_left _ h)
                · exact Or.inr (hmono z h)
            · simp only [hx, hy, ite_true, ite_false, List.singleton_append]
              refine WF.copyBinding (hBL x hx) (hnotL y hyq hy) (ih κ (y :: L) ?_ ?_ hcls')
              · intro z hz
                rcases Finset.mem_union.1 hz with hz | hz
                · exact List.mem_cons_of_mem _ (hBL z hz)
                · simp only [QAtom.binds, Finset.mem_insert, Finset.mem_singleton] at hz
                  rcases hz with rfl | rfl
                  · exact List.mem_cons_of_mem _ (hBL _ hx)
                  · exact List.mem_cons_self ..
              · intro z hz
                rcases List.mem_cons.1 hz with rfl | hz
                · exact Or.inl (Finset.mem_union_right _ hyq)
                · rcases hLB z hz with h | h
                  · exact Or.inl (Finset.mem_union_left _ h)
                  · exact Or.inr (hmono z h)
          · have hy : y ∈ B := by
              simp only [QAtom.eagerFree] at hfree
              exact hfree.resolve_left hx
            simp only [hx, ite_false, List.singleton_append]
            refine WF.copyBinding (hBL y hy) (hnotL x hxq hx) (ih κ (x :: L) ?_ ?_ hcls')
            · intro z hz
              rcases Finset.mem_union.1 hz with hz | hz
              · exact List.mem_cons_of_mem _ (hBL z hz)
              · simp only [QAtom.binds, Finset.mem_insert, Finset.mem_singleton] at hz
                rcases hz with rfl | rfl
                · exact List.mem_cons_self ..
                · exact List.mem_cons_of_mem _ (hBL _ hy)
            · intro z hz
              rcases List.mem_cons.1 hz with rfl | hz
              · exact Or.inl (Finset.mem_union_right _ hxq)
              · rcases hLB z hz with h | h
                · exact Or.inl (Finset.mem_union_left _ h)
                · exact Or.inr (hmono z h)
  | @pick used B i a rest hi hnot _ ih =>
      intro κ L hBL hLB hcls
      have ha : QAtom.scan a ∈ atoms := List.mem_of_getElem? hi
      refine lower_envWF (UsedOther atoms used) a B L hBL hLB ?_ ?_
        (hA.seqNodup a ha) (hA.noZero a ha) κ rest ?_
      · rintro x hx ⟨j, b, hj, -, hxb | hxb⟩
        · exact hA.clsNotMult (.scan a) ha b (List.mem_of_getElem? hj) x hx hxb
        · exact hA.clsNotRest (.scan a) ha b (List.mem_of_getElem? hj) x hx hxb
      · intro r hr
        refine ⟨?_, ?_, fun hrb => hA.clsNotRest (.scan a) ha a ha r hrb hr⟩
        · intro hrB
          obtain ⟨q, hq, hrq⟩ := hcls r hrB
          exact hA.clsNotRest q hq a ha r hrq hr
        · rintro ⟨j, b, hj, hju, hrb | hrb⟩
          · exact hA.multNotRest b a (List.mem_of_getElem? hj) ha r hrb hr
          · have hij : j ≠ i := fun h => hnot (h ▸ hju)
            exact hA.restLinear j i b a hj hi hij r hrb hr
      · refine ih _ _ (lower_wf a B L hBL).2 ?_ ?_
        · intro x hx
          rcases lower_bound a B L x hx with h | h | h | h
          · rcases hLB x h with h' | ⟨j, b, hj, hju, hxb⟩
            · exact Or.inl (Finset.mem_union_left _ h')
            · exact Or.inr ⟨j, b, hj, Finset.mem_insert_of_mem hju, hxb⟩
          · exact Or.inl (Finset.mem_union_right _ h)
          · exact Or.inr ⟨i, a, hi, Finset.mem_insert_self _ _, Or.inl h⟩
          · exact Or.inr ⟨i, a, hi, Finset.mem_insert_self _ _, Or.inr h⟩
        · intro x hx
          rcases Finset.mem_union.1 hx with hx | hx
          · exact hcls x hx
          · exact ⟨.scan a, ha, hx⟩

/-- **The scheduler's plans are well formed for the executor.** Every
`PlanOK` plan of an atom list with the resolver's variable discipline is
`WF` from `Match::new`, nested patterns included. -/
theorem planOK_envWF {atoms : List QAtom} {plan : Plan} (hA : EnvAtomsWF atoms)
    (h : PlanOK atoms plan) : WF (fun _ => false) [] plan :=
  sched_envWF hA h (fun _ => false) [] (fun x hx => by simp at hx) (fun x hx => by simp at hx)
    (fun x hx => by simp at hx)

/-- **The executor with undo emits exactly the matches.** For a `PlanOK`
plan, the environments the engine's recursive executor emits from
`Match::new`, read with the plan's join targets as node variables, are,
as a set, the bindings satisfying every atom (`plan_matches`). -/
theorem exec_matches {G : Graph} {sig : Sym → Kind} {atoms : List QAtom} {plan : Plan}
    (hG : G.ChildrenCanon) (hidem : G.FindIdem) (hwf : AtomsWF G sig atoms)
    (hA : EnvAtomsWF atoms) (h : PlanOK atoms plan) (σ : Binding) :
    σ ∈ (exec G (planKinds plan) plan Env.empty).1 ↔ Matches G atoms σ := by
  rw [env_refine_empty G hG hidem (planOK_envWF hA h) σ, plan_matches hwf h σ]

/-! ## The nested pattern `(f (g x) y)`, both ways round -/

/-- `(f (g x) y)`: `f = 0` and `g = 1` plain, `x = 0`, `y = 1`. -/
def nestedPat : Pat := .plain 0 [.plain 1 [.var 0], .var 1]

/-- The parent atom `f(n₃, y)` at the root node variable `2`. -/
def nestedParent : RAtom := ⟨2, 0, .plain [3, 1]⟩

/-- The nested atom `g(x)` at the node variable `3`, the parent's child. -/
def nestedChild : RAtom := ⟨3, 1, .plain [0]⟩

/-- The scanning atoms of `(f (g x) y)` at the root node variable `2`. -/
def nestedAtoms : List QAtom := (atoms nestedPat 2).map QAtom.scan

theorem nestedAtoms_eq : nestedAtoms = [.scan nestedChild, .scan nestedParent] := by
  simp [nestedAtoms, nestedPat, nestedChild, nestedParent, atoms, atomsAt, atomsChildren,
    atomsChild, Pat.freshAbove, Pat.vars]

/-- The parent lowered first: `ExtractChild` binds `3` as a class, the
nested atom's re-join `join 3 [byRepr 3, byOp g]` refines it to a node of
that class and reads its own target. -/
def nestedPlanParent : Plan := lower nestedParent ∅ ++ (lower nestedChild {2, 3, 1} ++ [])

theorem nestedPlanParent_eq : nestedPlanParent =
    [.join 2 [.byOp 0], .extractChild 2 0 3, .extractChild 2 1 1,
     .join 3 [.byRepr 3, .byOp 1], .extractChild 3 0 0] := by
  decide

/-- The nested atom lowered first: the join binds `3` as a node, and the
parent's `byChildPos` lookup and `CheckChildEq` read it as a class. -/
def nestedPlanChild : Plan := lower nestedChild ∅ ++ (lower nestedParent {3, 0} ++ [])

theorem nestedPlanChild_eq : nestedPlanChild =
    [.join 3 [.byOp 1], .extractChild 3 0 0,
     .join 2 [.byOp 0, .byChildPos 0 3], .checkChildEq 2 0 3, .extractChild 2 1 1] := by
  decide

theorem nested_envAtomsWF : EnvAtomsWF nestedAtoms := by
  rw [nestedAtoms_eq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro q _ a ha; simp at ha; rcases ha with rfl | rfl <;> simp [RAtom.multVars, nestedChild, nestedParent]
  · intro q _ a ha; simp at ha; rcases ha with rfl | rfl <;>
      simp [RAtom.restVars, RAtom.seqRestVars, RAtom.msetRestVars, RAtom.setRestVars,
        nestedChild, nestedParent]
  · intro a b ha _; simp at ha; rcases ha with rfl | rfl <;> simp [RAtom.multVars, nestedChild, nestedParent]
  · intro i j a b hi _ _ r hr
    have : a = nestedChild ∨ a = nestedParent := by
      match i, hi with
      | 0, hi => simp at hi; exact Or.inl hi.symm
      | 1, hi => simp at hi; exact Or.inr hi.symm
    rcases this with rfl | rfl <;>
      simp [RAtom.restVars, RAtom.seqRestVars, RAtom.msetRestVars, RAtom.setRestVars,
        nestedChild, nestedParent] at hr
  · intro a ha; simp at ha; rcases ha with rfl | rfl <;> simp [RAtom.seqRestVars, nestedChild, nestedParent]
  · intro a ha; simp at ha; rcases ha with rfl | rfl <;> simp [acElems, nestedChild, nestedParent]

/-- Both atoms are used at the end of a plan. -/
theorem nested_done {used : Finset Nat} {B : Finset Var} (h0 : 0 ∈ used) (h1 : 1 ∈ used) :
    Sched nestedAtoms used B [] := by
  refine Sched.done ?_ ?_
  · intro i a hi
    rw [nestedAtoms_eq] at hi
    match i, hi with
    | 0, _ => exact h0
    | 1, _ => exact h1
  · intro i q hi hu
    rw [nestedAtoms_eq] at hi
    match i, hi with
    | 0, _ => exact absurd h0 hu
    | 1, _ => exact absurd h1 hu

theorem nestedPlanParent_ok : PlanOK nestedAtoms nestedPlanParent := by
  have h1 : nestedAtoms[1]? = some (.scan nestedParent) := by rw [nestedAtoms_eq]; rfl
  have h0 : nestedAtoms[0]? = some (.scan nestedChild) := by rw [nestedAtoms_eq]; rfl
  have hB : (∅ : Finset Var) ∪ nestedParent.binds = {2, 3, 1} := by decide
  refine Sched.pick h1 (by simp) ?_
  rw [hB]
  have hB' : ({2, 3, 1} : Finset Var) ∪ nestedChild.binds = {2, 3, 1, 0} := by decide
  refine Sched.pick h0 (by simp) ?_
  rw [hB']
  exact nested_done (by simp) (by simp)

theorem nestedPlanChild_ok : PlanOK nestedAtoms nestedPlanChild := by
  have h1 : nestedAtoms[1]? = some (.scan nestedParent) := by rw [nestedAtoms_eq]; rfl
  have h0 : nestedAtoms[0]? = some (.scan nestedChild) := by rw [nestedAtoms_eq]; rfl
  have hB : (∅ : Finset Var) ∪ nestedChild.binds = {3, 0} := by decide
  refine Sched.pick h0 (by simp) ?_
  rw [hB]
  have hB' : ({3, 0} : Finset Var) ∪ nestedParent.binds = {3, 0, 2, 1} := by decide
  refine Sched.pick h1 (by simp) ?_
  rw [hB']
  exact nested_done (by simp) (by simp)

/-- **The scheduler's plans for a nested pattern are well formed**, both
ways round. The former `κ` partition rejected both: `3` is a class
variable of the parent and the node variable of the nested atom. -/
theorem nested_plans_wf :
    WF (fun _ => false) [] nestedPlanParent ∧ WF (fun _ => false) [] nestedPlanChild :=
  ⟨planOK_envWF nested_envAtomsWF nestedPlanParent_ok,
    planOK_envWF nested_envAtomsWF nestedPlanChild_ok⟩

/-- **The executor is exact on the nested pattern**, both ways round: on
every rebuilt graph whose atoms are well formed, the environments the
engine emits from `Match::new` are the matches of `(f (g x) y)`. -/
theorem nested_exec_matches {G : Graph} {sig : Sym → Kind} (hG : G.ChildrenCanon)
    (hidem : G.FindIdem) (hwf : AtomsWF G sig nestedAtoms) (σ : Binding) :
    (σ ∈ (exec G (planKinds nestedPlanParent) nestedPlanParent Env.empty).1 ↔
        Matches G nestedAtoms σ) ∧
      (σ ∈ (exec G (planKinds nestedPlanChild) nestedPlanChild Env.empty).1 ↔
        Matches G nestedAtoms σ) :=
  ⟨exec_matches hG hidem hwf nested_envAtomsWF nestedPlanParent_ok σ,
    exec_matches hG hidem hwf nested_envAtomsWF nestedPlanChild_ok σ⟩

end Semper.EMatch.Env
