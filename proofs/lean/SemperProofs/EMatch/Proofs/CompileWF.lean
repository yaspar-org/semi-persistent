import SemperProofs.EMatch.Lemmas

/-!
# Lemma 10: the compiler's output is a well-formed plan

Proves `compile_wf'`, the statement of the `compile_wf` stub in
`Lemmas.lean`. The invariant is continuation-passing: `WFCont B s` says
that `s` prefixed to any continuation that is well-formed under every
superset of `B` gives a plan well-formed under `B`. This avoids computing
the bound set a sub-plan leaves behind: a binding step only grows the set,
so the continuation is checked under every superset.

The hypothesis `hf` of `compile_wf` (fresh above the pattern variables) is
not needed: `PlanWF` only checks membership, and every variable a step reads
is the node variable or class variable that an earlier step of the same
sub-plan bound. The one place a variable could be read unbound, a variable
pattern under a class variable (`checkEq z x`), is never generated:
`compileNested` compiles a variable to the empty plan.
-/

namespace Semper.EMatch

/-- `s` is well-formed under `B` for every continuation well-formed under
every superset of `B`. -/
def WFCont (B : List Var) (s : Plan) : Prop :=
  ∀ ss : Plan, (∀ B', B ⊆ B' → PlanWF B' ss) → PlanWF B (s ++ ss)

namespace WFCont

theorem nil (B : List Var) : WFCont B [] := by
  intro ss h
  simpa using h B (List.Subset.refl _)

theorem toPlanWF {B : List Var} {s : Plan} (h : WFCont B s) : PlanWF B s := by
  simpa using h [] (fun _ _ => PlanWF.nil)

theorem append {B : List Var} {s₁ s₂ : Plan} (h₁ : WFCont B s₁)
    (h₂ : ∀ B', B ⊆ B' → WFCont B' s₂) : WFCont B (s₁ ++ s₂) := by
  intro ss hss
  rw [List.append_assoc]
  apply h₁
  intro B' hB
  exact h₂ B' hB ss (fun B'' hB' => hss B'' (List.Subset.trans hB hB'))

theorem join {B : List Var} {t : Var} {ls : List Lookup} {s : Plan}
    (hr : ∀ l ∈ ls, ∀ x ∈ l.reads, x ∈ B) (h : WFCont (t :: B) s) :
    WFCont B (.join t ls :: s) := by
  intro ss hss
  exact PlanWF.join hr
    (h ss (fun B' hB => hss B' (List.Subset.trans (List.subset_cons_self t B) hB)))

theorem extractChild {B : List Var} {v out : Var} {pos : Nat} {s : Plan}
    (hv : v ∈ B) (h : WFCont (out :: B) s) :
    WFCont B (.extractChild v pos out :: s) := by
  intro ss hss
  exact PlanWF.extractChild hv
    (h ss (fun B' hB => hss B' (List.Subset.trans (List.subset_cons_self out B) hB)))

theorem decomposeAC {B : List Var} {v : Var} {elems : List (Var × Mult)}
    {rest : Option Var} {s : Plan} (hv : v ∈ B)
    (h : WFCont (acBinds elems rest ++ B) s) :
    WFCont B (.decomposeAC v elems rest :: s) := by
  intro ss hss
  exact PlanWF.decomposeAC hv
    (h ss (fun B' hB => hss B' (List.Subset.trans (List.subset_append_right _ _) hB)))

theorem decomposeACI {B : List Var} {v : Var} {elems : List Var}
    {rest : Option Var} {s : Plan} (hv : v ∈ B)
    (h : WFCont (elems ++ rest.toList ++ B) s) :
    WFCont B (.decomposeACI v elems rest :: s) := by
  intro ss hss
  exact PlanWF.decomposeACI hv
    (h ss (fun B' hB => hss B' (List.Subset.trans (List.subset_append_right _ _) hB)))

theorem expandA {B : List Var} {v : Var} {pre suf : Option Var}
    {elems : List Var} {s : Plan} (hv : v ∈ B)
    (h : WFCont (pre.toList ++ elems ++ suf.toList ++ B) s) :
    WFCont B (.expandA v pre elems suf :: s) := by
  intro ss hss
  exact PlanWF.expandA hv
    (h ss (fun B' hB => hss B' (List.Subset.trans (List.subset_append_right _ _) hB)))

theorem decomposeComm {B : List Var} {v x y : Var} {s : Plan} (hv : v ∈ B)
    (h : WFCont (x :: y :: B) s) :
    WFCont B (.decomposeComm v x y :: s) := by
  intro ss hss
  refine PlanWF.decomposeComm hv (h ss (fun B' hB => hss B' ?_))
  exact List.Subset.trans (List.Subset.trans (List.subset_cons_self y B) (List.subset_cons_self x _)) hB

/-- The join step of an application reads only the class variable `cv`. -/
theorem joinStep {B : List Var} {nv : Var} {f : Sym} {cv : Option Var}
    {s : Plan} (hcv : ∀ z ∈ cv, z ∈ B) (h : WFCont (nv :: B) s) :
    WFCont B (Semper.EMatch.joinStep nv f cv :: s) := by
  cases cv with
  | none =>
      apply join _ h
      simp [Lookup.reads]
  | some z =>
      apply join _ h
      simp [Lookup.reads]
      exact hcv z rfl

end WFCont

mutual
theorem compileAt_wf (P : Pat) (cv : Option Var) (fresh : Nat) (B : List Var)
    (hcv : ∀ z ∈ cv, z ∈ B) (hvar : ∀ x, P = .var x → ∀ z ∈ cv, x ∈ B) :
    WFCont B (compileAt P cv fresh).1 := by
  match P with
  | .var x =>
      cases cv with
      | none => simp only [compileAt]; exact WFCont.nil B
      | some z =>
          simp only [compileAt]
          intro ss hss
          exact PlanWF.checkEq (hcv z rfl) (hvar x rfl z rfl)
            (hss B (List.Subset.refl _))
  | .plain f args =>
      rcases hs : compilePlainArgs args fresh 0 (fresh + 1) with ⟨s, fr⟩
      simp only [compileAt, hs]
      apply WFCont.joinStep hcv
      have := compilePlainArgs_wf args fresh 0 (fresh + 1) (fresh :: B)
        (List.mem_cons_self ..)
      rw [hs] at this
      exact this
  | .comm f p q =>
      rcases h1 : elemVar p (fresh + 1) with ⟨vp, fr₁⟩
      rcases h2 : elemVar q fr₁ with ⟨vq, fr₂⟩
      rcases h3 : compileNested p vp fr₂ with ⟨sp, fr₃⟩
      rcases h4 : compileNested q vq fr₃ with ⟨sq, fr₄⟩
      simp only [compileAt, h1, h2, h3, h4]
      apply WFCont.joinStep hcv
      apply WFCont.decomposeComm (List.mem_cons_self ..)
      apply WFCont.append
      · have := compileNested_wf p vp fr₂ (vp :: vq :: fresh :: B)
          (List.mem_cons_self ..)
        rw [h3] at this
        exact this
      · intro B' hB
        have := compileNested_wf q vq fr₃ B'
          (hB (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
        rw [h4] at this
        exact this
  | .assoc f pre args suf =>
      rcases h1 : elemVars args (fresh + 1) with ⟨vs, fr₁⟩
      rcases h2 : compileNestedList args vs fr₁ with ⟨s, fr₂⟩
      simp only [compileAt, h1, h2]
      apply WFCont.joinStep hcv
      apply WFCont.expandA (List.mem_cons_self ..)
      have := compileNestedList_wf args vs fr₁
        (pre.toList ++ vs ++ suf.toList ++ fresh :: B) (by intro v hv; simp [hv])
      rw [h2] at this
      exact this
  | .ac f elems rest =>
      rcases h1 : elemVarsAC elems (fresh + 1) with ⟨vs, fr₁⟩
      rcases h2 : compileNestedAC elems (vs.map (·.1)) fr₁ with ⟨s, fr₂⟩
      simp only [compileAt, h1, h2]
      apply WFCont.joinStep hcv
      apply WFCont.decomposeAC (List.mem_cons_self ..)
      have := compileNestedAC_wf elems (vs.map (·.1)) fr₁
        (acBinds vs rest ++ fresh :: B) (by intro v hv; simp [acBinds, hv])
      rw [h2] at this
      exact this
  | .aci f elems rest =>
      rcases h1 : elemVars elems (fresh + 1) with ⟨vs, fr₁⟩
      rcases h2 : compileNestedList elems vs fr₁ with ⟨s, fr₂⟩
      simp only [compileAt, h1, h2]
      apply WFCont.joinStep hcv
      apply WFCont.decomposeACI (List.mem_cons_self ..)
      have := compileNestedList_wf elems vs fr₁
        (vs ++ rest.toList ++ fresh :: B) (by intro v hv; simp [hv])
      rw [h2] at this
      exact this
termination_by (sizeOf P, 0)
decreasing_by all_goals (simp_wf; omega)

theorem compilePlainArgs_wf (args : List Pat) (nv : Var) (i : Nat) (fresh : Nat)
    (B : List Var) (hnv : nv ∈ B) :
    WFCont B (compilePlainArgs args nv i fresh).1 := by
  cases args with
  | nil => simp only [compilePlainArgs]; exact WFCont.nil B
  | cons p ps =>
      rcases h1 : elemVar p fresh with ⟨v, fr₁⟩
      rcases h2 : compileNested p v fr₁ with ⟨sp, fr₂⟩
      rcases h3 : compilePlainArgs ps nv (i + 1) fr₂ with ⟨s, fr₃⟩
      simp only [compilePlainArgs, h1, h2, h3]
      apply WFCont.extractChild hnv
      apply WFCont.append
      · have := compileNested_wf p v fr₁ (v :: B) (List.mem_cons_self ..)
        rw [h2] at this
        exact this
      · intro B' hB
        have := compilePlainArgs_wf ps nv (i + 1) fr₂ B'
          (hB (List.mem_cons_of_mem _ hnv))
        rw [h3] at this
        exact this
termination_by (sizeOf args, 0)
decreasing_by all_goals (simp_wf; omega)

theorem compileNested_wf (p : Pat) (v : Var) (fresh : Nat) (B : List Var)
    (hv : v ∈ B) : WFCont B (compileNested p v fresh).1 := by
  cases p with
  | var x => simp only [compileNested]; exact WFCont.nil B
  | plain f args =>
      simp only [compileNested]
      exact compileAt_wf (.plain f args) (some v) fresh B
        (by intro z hz; cases hz; exact hv) (by intro x h; cases h)
  | comm f p q =>
      simp only [compileNested]
      exact compileAt_wf (.comm f p q) (some v) fresh B
        (by intro z hz; cases hz; exact hv) (by intro x h; cases h)
  | assoc f pre args suf =>
      simp only [compileNested]
      exact compileAt_wf (.assoc f pre args suf) (some v) fresh B
        (by intro z hz; cases hz; exact hv) (by intro x h; cases h)
  | ac f elems rest =>
      simp only [compileNested]
      exact compileAt_wf (.ac f elems rest) (some v) fresh B
        (by intro z hz; cases hz; exact hv) (by intro x h; cases h)
  | aci f elems rest =>
      simp only [compileNested]
      exact compileAt_wf (.aci f elems rest) (some v) fresh B
        (by intro z hz; cases hz; exact hv) (by intro x h; cases h)
termination_by (sizeOf p, 1)
decreasing_by all_goals (simp_wf; omega)

theorem compileNestedList_wf (ps : List Pat) (vs : List Var) (fresh : Nat)
    (B : List Var) (h : ∀ v ∈ vs, v ∈ B) :
    WFCont B (compileNestedList ps vs fresh).1 := by
  cases ps with
  | nil => simp only [compileNestedList]; exact WFCont.nil B
  | cons p ps =>
      cases vs with
      | nil => simp only [compileNestedList]; exact WFCont.nil B
      | cons v vs =>
          rcases h1 : compileNested p v fresh with ⟨sp, fr₁⟩
          rcases h2 : compileNestedList ps vs fr₁ with ⟨s, fr₂⟩
          simp only [compileNestedList, h1, h2]
          apply WFCont.append
          · have := compileNested_wf p v fresh B (h v (List.mem_cons_self ..))
            rw [h1] at this
            exact this
          · intro B' hB
            have := compileNestedList_wf ps vs fr₁ B'
              (fun w hw => hB (h w (List.mem_cons_of_mem _ hw)))
            rw [h2] at this
            exact this
termination_by (sizeOf ps, 0)
decreasing_by all_goals (simp_wf; omega)

theorem compileNestedAC_wf (es : List (Pat × Mult)) (vs : List Var) (fresh : Nat)
    (B : List Var) (h : ∀ v ∈ vs, v ∈ B) :
    WFCont B (compileNestedAC es vs fresh).1 := by
  cases es with
  | nil => simp only [compileNestedAC]; exact WFCont.nil B
  | cons e es =>
      obtain ⟨p, μ⟩ := e
      cases vs with
      | nil => simp only [compileNestedAC]; exact WFCont.nil B
      | cons v vs =>
          rcases h1 : compileNested p v fresh with ⟨sp, fr₁⟩
          rcases h2 : compileNestedAC es vs fr₁ with ⟨s, fr₂⟩
          simp only [compileNestedAC, h1, h2]
          apply WFCont.append
          · have := compileNested_wf p v fresh B (h v (List.mem_cons_self ..))
            rw [h1] at this
            exact this
          · intro B' hB
            have := compileNestedAC_wf es vs fr₁ B'
              (fun w hw => hB (h w (List.mem_cons_of_mem _ hw)))
            rw [h2] at this
            exact this
termination_by (sizeOf es, 0)
decreasing_by all_goals (simp_wf; omega)
end

/-- Lemma 10 (`plan_wf`), the statement of `compile_wf`: the compiler binds
every variable before it is read. -/
theorem compile_wf' (P : Pat) (fresh : Nat) (_hf : ∀ x ∈ P.vars, x < fresh) :
    PlanWF [] (compile P fresh) := by
  have := compileAt_wf P none fresh [] (by intro z hz; cases hz)
    (by intro x _ z hz; cases hz)
  exact this.toPlanWF

end Semper.EMatch
