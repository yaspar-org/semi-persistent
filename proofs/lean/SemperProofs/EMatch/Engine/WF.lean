import SemperProofs.EMatch.Engine.Sched

/-!
# Well-formedness of scheduled plans (spec-scheduler §3.1, `PlanOK → PlanWF`)

Every lookup variable, parent variable and check operand of a `Sched` plan
is in the bound list when its step runs: the lowering only adds lookups on
bound variables, the join binds the node variable before the body reads it,
and the decompositions bind their element variables.
-/

namespace Semper.EMatch

/-- The bound list after one step, as `PlanWF` extends it. -/
def stepBound : Step → List Var → List Var
  | .join t _, L => t :: L
  | .extractChild _ _ out, L => out :: L
  | .checkChildEq _ _ _, L => L
  | .checkEq _ _, L => L
  | .copyBinding t _, L => t :: L
  | .decomposeAC _ elems rest, L => acBinds elems rest ++ L
  | .decomposeACI _ elems rest, L => elems ++ rest.toList ++ L
  | .expandA _ pre elems suf, L => pre.toList ++ elems ++ suf.toList ++ L
  | .decomposeComm _ x y, L => x :: y :: L

/-- The bound list after a plan. -/
def boundAfter : List Var → Plan → List Var
  | L, [] => L
  | L, s :: ss => boundAfter (stepBound s L) ss

theorem planWF_cons_iff {L : List Var} {s : Step} {ss : Plan} :
    PlanWF L (s :: ss) ↔ (∃ (_ : PlanWF L [s]), True) ∧ PlanWF (stepBound s L) ss := by
  constructor
  · intro h
    cases h with
    | join h₁ h₂ => exact ⟨⟨PlanWF.join h₁ PlanWF.nil, trivial⟩, h₂⟩
    | extractChild h₁ h₂ => exact ⟨⟨PlanWF.extractChild h₁ PlanWF.nil, trivial⟩, h₂⟩
    | checkChildEq h₁ h₂ h₃ => exact ⟨⟨PlanWF.checkChildEq h₁ h₂ PlanWF.nil, trivial⟩, h₃⟩
    | checkEq h₁ h₂ h₃ => exact ⟨⟨PlanWF.checkEq h₁ h₂ PlanWF.nil, trivial⟩, h₃⟩
    | copyBinding h₁ h₂ => exact ⟨⟨PlanWF.copyBinding h₁ PlanWF.nil, trivial⟩, h₂⟩
    | decomposeAC h₁ h₂ => exact ⟨⟨PlanWF.decomposeAC h₁ PlanWF.nil, trivial⟩, h₂⟩
    | decomposeACI h₁ h₂ => exact ⟨⟨PlanWF.decomposeACI h₁ PlanWF.nil, trivial⟩, h₂⟩
    | expandA h₁ h₂ => exact ⟨⟨PlanWF.expandA h₁ PlanWF.nil, trivial⟩, h₂⟩
    | decomposeComm h₁ h₂ => exact ⟨⟨PlanWF.decomposeComm h₁ PlanWF.nil, trivial⟩, h₂⟩
  · rintro ⟨⟨h₁, -⟩, h₂⟩
    cases h₁ with
    | join h _ => exact PlanWF.join h h₂
    | extractChild h _ => exact PlanWF.extractChild h h₂
    | checkChildEq h h' _ => exact PlanWF.checkChildEq h h' h₂
    | checkEq h h' _ => exact PlanWF.checkEq h h' h₂
    | copyBinding h _ => exact PlanWF.copyBinding h h₂
    | decomposeAC h _ => exact PlanWF.decomposeAC h h₂
    | decomposeACI h _ => exact PlanWF.decomposeACI h h₂
    | expandA h _ => exact PlanWF.expandA h h₂
    | decomposeComm h _ => exact PlanWF.decomposeComm h h₂

theorem planWF_append {L : List Var} : ∀ {p₁ p₂ : Plan},
    PlanWF L (p₁ ++ p₂) ↔ PlanWF L p₁ ∧ PlanWF (boundAfter L p₁) p₂ := by
  intro p₁
  induction p₁ generalizing L with
  | nil => intro p₂; simp [boundAfter, PlanWF.nil]
  | cons s ss ih =>
      intro p₂
      rw [List.cons_append, planWF_cons_iff, ih, planWF_cons_iff (ss := ss)]
      simp only [boundAfter]
      tauto

theorem PlanWF.mono {L L' : List Var} (hL : ∀ x ∈ L, x ∈ L') : ∀ {p : Plan}, PlanWF L p → PlanWF L' p := by
  intro p h
  induction h generalizing L' with
  | nil => exact PlanWF.nil
  | join h₁ _ ih =>
      exact PlanWF.join (fun l hl x hx => hL x (h₁ l hl x hx))
        (ih (fun x hx => by simp only [List.mem_cons] at hx ⊢; rcases hx with rfl | hx; exact Or.inl rfl; exact Or.inr (hL x hx)))
  | extractChild h₁ _ ih =>
      exact PlanWF.extractChild (hL _ h₁)
        (ih (fun x hx => by simp only [List.mem_cons] at hx ⊢; rcases hx with rfl | hx; exact Or.inl rfl; exact Or.inr (hL x hx)))
  | checkChildEq h₁ h₂ _ ih => exact PlanWF.checkChildEq (hL _ h₁) (hL _ h₂) (ih hL)
  | checkEq h₁ h₂ _ ih => exact PlanWF.checkEq (hL _ h₁) (hL _ h₂) (ih hL)
  | copyBinding h₁ _ ih =>
      exact PlanWF.copyBinding (hL _ h₁)
        (ih (fun x hx => by simp only [List.mem_cons] at hx ⊢; rcases hx with rfl | hx; exact Or.inl rfl; exact Or.inr (hL x hx)))
  | decomposeAC h₁ _ ih =>
      exact PlanWF.decomposeAC (hL _ h₁)
        (ih (fun x hx => by simp only [List.mem_append] at hx ⊢; rcases hx with hx | hx; exact Or.inl hx; exact Or.inr (hL x hx)))
  | decomposeACI h₁ _ ih =>
      exact PlanWF.decomposeACI (hL _ h₁)
        (ih (fun x hx => by simp only [List.mem_append] at hx ⊢; rcases hx with hx | hx; exact Or.inl hx; exact Or.inr (hL x hx)))
  | expandA h₁ _ ih =>
      exact PlanWF.expandA (hL _ h₁)
        (ih (fun x hx => by simp only [List.mem_append] at hx ⊢; rcases hx with hx | hx; exact Or.inl hx; exact Or.inr (hL x hx)))
  | decomposeComm h₁ _ ih =>
      exact PlanWF.decomposeComm (hL _ h₁)
        (ih (fun x hx => by simp only [List.mem_cons] at hx ⊢; rcases hx with rfl | rfl | hx; exact Or.inl rfl; exact Or.inr (Or.inl rfl); exact Or.inr (Or.inr (hL x hx))))

/-- The bound list only grows. -/
theorem subset_boundAfter : ∀ (p : Plan) (L : List Var), ∀ x ∈ L, x ∈ boundAfter L p := by
  intro p
  induction p with
  | nil => intro L x hx; simpa [boundAfter] using hx
  | cons s ss ih =>
      intro L x hx
      simp only [boundAfter]
      apply ih
      cases s <;> simp [stepBound, hx]

/-- The child loop is well-formed when the node is bound and `B'` is bound,
and it binds every child. -/
theorem childSteps_wf (n : Var) : ∀ (cs : List Var) (i : Nat) (B' : Finset Var) (L : List Var),
    n ∈ L → (∀ x ∈ B', x ∈ L) →
    PlanWF L (childSteps n cs i B') ∧ ∀ c ∈ cs, c ∈ boundAfter L (childSteps n cs i B') := by
  intro cs
  induction cs with
  | nil => intro i B' L _ _; exact ⟨PlanWF.nil, by simp⟩
  | cons c cs ih =>
      intro i B' L hn hB
      simp only [childSteps]
      split
      · rename_i hc
        obtain ⟨h₁, h₂⟩ := ih (i + 1) B' L hn hB
        refine ⟨PlanWF.checkChildEq hn (hB c hc) h₁, ?_⟩
        intro x hx
        rw [List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact subset_boundAfter _ _ _ (hB x hc)
        · simpa [boundAfter, stepBound] using h₂ x hx
      · obtain ⟨h₁, h₂⟩ := ih (i + 1) (insert c B') (c :: L) (List.mem_cons_of_mem _ hn)
          (by intro x hx; rw [Finset.mem_insert] at hx; rcases hx with rfl | hx; simp; exact List.mem_cons_of_mem _ (hB x hx))
        refine ⟨PlanWF.extractChild hn h₁, ?_⟩
        intro x hx
        rw [List.mem_cons] at hx
        rcases hx with rfl | hx
        · simp only [boundAfter, stepBound]
          exact subset_boundAfter _ _ _ (List.mem_cons_self ..)
        · simpa [boundAfter, stepBound] using h₂ x hx

theorem joinLookups_reads (a : RAtom) (B : Finset Var) :
    ∀ l ∈ joinLookups a B, ∀ x ∈ l.reads, x ∈ B := by
  intro l hl x hx
  unfold joinLookups at hl
  split at hl
  · rename_i hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl
    · simp only [Lookup.reads, List.mem_singleton] at hx; subst hx; exact hn
    · simp [Lookup.reads] at hx
  · simp only [List.mem_cons] at hl
    rcases hl with rfl | hl
    · simp [Lookup.reads] at hx
    · unfold extraLookups at hl
      split at hl
      · obtain ⟨j, c, -, hc, rfl⟩ := mem_childLookups hl
        simp only [Lookup.reads, List.mem_singleton] at hx; subst hx; exact hc
      · simp at hl
      · obtain ⟨e, -, he, rfl⟩ := mem_containsLookups hl
        simp only [Lookup.reads, List.mem_singleton] at hx; subst hx; exact he

/-- The lowering of an atom under a bound set contained in `L` is
well-formed and binds the atom's variables. -/
theorem lower_wf (a : RAtom) (B : Finset Var) (L : List Var) (hB : ∀ x ∈ B, x ∈ L) :
    PlanWF L (lower a B) ∧ ∀ x ∈ B ∪ a.binds, x ∈ boundAfter L (lower a B) := by
  obtain ⟨n, f, sh⟩ := a
  have hreads : ∀ l ∈ joinLookups ⟨n, f, sh⟩ B, ∀ x ∈ l.reads, x ∈ L :=
    fun l hl x hx => hB x (joinLookups_reads ⟨n, f, sh⟩ B l hl x hx)
  have hB' : ∀ x ∈ insert n B, x ∈ n :: L := by
    intro x hx; rw [Finset.mem_insert] at hx
    rcases hx with rfl | hx
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (hB x hx)
  cases sh with
  | plain cs =>
      obtain ⟨h₁, h₂⟩ := childSteps_wf n cs 0 (insert n B) (n :: L) (List.mem_cons_self ..) hB'
      refine ⟨PlanWF.join hreads h₁, ?_⟩
      intro x hx
      simp only [lower, lowerBody, boundAfter, stepBound]
      rw [Finset.mem_union, RAtom.binds] at hx
      simp only [RAtom.elems, Finset.mem_insert, List.mem_toFinset] at hx
      rcases hx with hx | hx | hx
      · exact subset_boundAfter _ _ _ (List.mem_cons_of_mem _ (hB x hx))
      · subst hx; exact subset_boundAfter _ _ _ (List.mem_cons_self ..)
      · exact h₂ x hx
  | comm y z =>
      refine ⟨PlanWF.join hreads (PlanWF.decomposeComm (List.mem_cons_self ..) PlanWF.nil), ?_⟩
      intro x hx
      simp only [lower, lowerBody, boundAfter, stepBound]
      rw [Finset.mem_union, RAtom.binds] at hx
      simp only [RAtom.elems, Finset.mem_insert, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hx
      simp only [List.mem_cons]
      rcases hx with hx | hx | hx | hx <;> simp [hx, hB]
  | assoc pre fx suf =>
      refine ⟨PlanWF.join hreads (PlanWF.expandA (List.mem_cons_self ..) PlanWF.nil), ?_⟩
      intro x hx
      simp only [lower, lowerBody, boundAfter, stepBound]
      rw [Finset.mem_union, RAtom.binds] at hx
      simp only [RAtom.elems, Finset.mem_insert, List.mem_toFinset] at hx
      simp only [List.mem_append, List.mem_cons]
      rcases hx with hx | hx | hx <;> simp [hx, hB]
  | ac es rest =>
      refine ⟨PlanWF.join hreads (PlanWF.decomposeAC (List.mem_cons_self ..) PlanWF.nil), ?_⟩
      intro x hx
      simp only [lower, lowerBody, boundAfter, stepBound]
      rw [Finset.mem_union, RAtom.binds] at hx
      simp only [RAtom.elems, Finset.mem_insert, List.mem_toFinset] at hx
      simp only [acBinds, List.mem_append, List.mem_cons]
      rcases hx with hx | hx | hx <;> simp [hx, hB]
  | aci es rest =>
      refine ⟨PlanWF.join hreads (PlanWF.decomposeACI (List.mem_cons_self ..) PlanWF.nil), ?_⟩
      intro x hx
      simp only [lower, lowerBody, boundAfter, stepBound]
      rw [Finset.mem_union, RAtom.binds] at hx
      simp only [RAtom.elems, Finset.mem_insert, List.mem_toFinset] at hx
      simp only [List.mem_append, List.mem_cons]
      rcases hx with hx | hx | hx <;> simp [hx, hB]

theorem eager_wf (q : QAtom) (B : Finset Var) (L : List Var) (hB : ∀ x ∈ B, x ∈ L)
    (hf : q.eagerFree B) :
    PlanWF L (q.eagerLower B) ∧ ∀ x ∈ B ∪ q.binds, x ∈ boundAfter L (q.eagerLower B) := by
  cases q with
  | scan a => simp [QAtom.eagerFree] at hf
  | eq y z =>
      simp only [QAtom.eagerLower]
      have hbinds : ∀ x, x ∈ B ∪ QAtom.binds (.eq y z) ↔ x ∈ B ∨ x = y ∨ x = z := by
        intro x; simp [QAtom.binds]; tauto
      split
      · rename_i hy
        split
        · rename_i hz
          refine ⟨PlanWF.checkEq (hB y hy) (hB z hz) PlanWF.nil, ?_⟩
          intro x hx
          rw [hbinds] at hx
          simp only [boundAfter, stepBound]
          rcases hx with hx | rfl | rfl
          · exact hB x hx
          · exact hB _ hy
          · exact hB _ hz
        · refine ⟨PlanWF.copyBinding (hB y hy) PlanWF.nil, ?_⟩
          intro x hx
          rw [hbinds] at hx
          simp only [boundAfter, stepBound, List.mem_cons]
          rcases hx with hx | rfl | rfl
          · exact Or.inr (hB x hx)
          · exact Or.inr (hB _ hy)
          · exact Or.inl rfl
      · rename_i hy
        have hz : z ∈ B := by
          simp only [QAtom.eagerFree] at hf
          rcases hf with h | h
          · exact absurd h hy
          · exact h
        refine ⟨PlanWF.copyBinding (hB z hz) PlanWF.nil, ?_⟩
        intro x hx
        rw [hbinds] at hx
        simp only [boundAfter, stepBound, List.mem_cons]
        rcases hx with hx | rfl | rfl
        · exact Or.inr (hB x hx)
        · exact Or.inl rfl
        · exact Or.inr (hB _ hz)

/-- Spec §3.1: every scheduled plan is well-formed from any bound list
containing the bound set. -/
theorem sched_wf {atoms : List QAtom} : ∀ {used : Finset Nat} {B : Finset Var} {plan : Plan},
    Sched atoms used B plan → ∀ L : List Var, (∀ x ∈ B, x ∈ L) → PlanWF L plan := by
  intro used B plan h
  induction h with
  | done _ _ => intro L _; exact PlanWF.nil
  | @eager used B i q rest _ _ hf _ ih =>
      intro L hB
      rw [planWF_append]
      obtain ⟨h₁, h₂⟩ := eager_wf q B L hB hf
      exact ⟨h₁, ih _ h₂⟩
  | @pick used B i a rest _ _ _ ih =>
      intro L hB
      rw [planWF_append]
      obtain ⟨h₁, h₂⟩ := lower_wf a B L hB
      exact ⟨h₁, ih _ h₂⟩

/-- `PlanOK → PlanWF`. -/
theorem planOK_wf {atoms : List QAtom} {plan : Plan} (h : PlanOK atoms plan) : PlanWF [] plan :=
  sched_wf h [] (by simp)

/-- Seeded plans are well-formed from the seed list. -/
theorem planOKFrom_wf {atoms : List QAtom} {pre : Finset Var} {plan : Plan}
    (h : PlanOKFrom atoms pre plan) : PlanWF pre.toList plan :=
  sched_wf h pre.toList (by simp)

end Semper.EMatch
