import SemperProofs.EMatch.Lemmas
import SemperProofs.EMatch.Proofs.JoinCommA
import SemperProofs.EMatch.Proofs.DecomposeAC
import SemperProofs.EMatch.Proofs.CompileWF

/-!
# Lemmas 11 and 12: soundness and completeness of the interpreter

Proves `interp_sound'` and `interp_complete'` for the left-to-right
compiler of `Ref.lean`, from the component lemmas:
`join_complete'`, `decompose_ac_sound'`, `decompose_ac_complete'`,
`decompose_aci_sound'`, `decompose_aci_complete'`, `expand_a_sound'`,
`expand_a_complete'`, `decompose_comm_sound'`, `decompose_comm_complete'`.

Both stubs in `Lemmas.lean` are false as stated; see the docstrings of
`interp_sound'` and `interp_complete'` for the counterexamples and the
corrected hypotheses (a kind signature the graph and the pattern conform
to, distinct rest variables, and the binding comparison restricted to the
variables below `fresh`).

Structure: one invariant lemma (`struct`) over the compiler's plans gives
`Extends` and the frame of every run; soundness and completeness are then
proved by strong induction on the size of the pattern, with inner
inductions on argument lists.
-/

namespace Semper.EMatch

open Binding

/-- `vomega` after unfolding the `Nat` abbreviations (`Var`, `C`, `NodeId`,
`Sym`): `vomega` does not recognize `<` and `≤` elaborated at those types. -/
macro "vomega" : tactic =>
  `(tactic| ((try dsimp only [Var, C, NodeId, Sym] at *) <;> omega))

/-! ## Running plans -/

@[simp] theorem run_nil (G : Graph) (σ : Binding) : run G [] σ = [σ] := rfl

@[simp] theorem run_cons (G : Graph) (s : Step) (ss : Plan) (σ : Binding) :
    run G (s :: ss) σ = (runStep G s σ).flatMap (run G ss) := rfl

theorem run_append (G : Graph) (a b : Plan) (σ : Binding) :
    run G (a ++ b) σ = (run G a σ).flatMap (run G b) := by
  induction a generalizing σ with
  | nil => simp
  | cons s ss ih =>
      simp only [List.cons_append, run_cons, List.flatMap_assoc]
      congr 1
      funext σ₁
      exact ih σ₁

theorem mem_run_append {G : Graph} {a b : Plan} {σ σ' : Binding} :
    σ' ∈ run G (a ++ b) σ ↔ ∃ σm ∈ run G a σ, σ' ∈ run G b σm := by
  rw [run_append, List.mem_flatMap]

theorem mem_run_cons {G : Graph} {s : Step} {ss : Plan} {σ σ' : Binding} :
    σ' ∈ run G (s :: ss) σ ↔ ∃ σm ∈ runStep G s σ, σ' ∈ run G ss σm := by
  rw [run_cons, List.mem_flatMap]

/-! ## Node lookup -/

theorem find?_key_of_mem {l : List (NodeId × Node)} (hk : (l.map (·.1)).Nodup)
    {id : NodeId} {n : Node} (h : (id, n) ∈ l) :
    l.find? (fun p => p.1 = id) = some (id, n) := by
  induction l with
  | nil => simp at h
  | cons p l ih =>
      rw [List.map_cons, List.nodup_cons] at hk
      obtain ⟨hnot, hk'⟩ := hk
      rw [List.mem_cons] at h
      by_cases hp : p.1 = id
      · rcases h with rfl | h
        · simp [List.find?_cons]
        · exact absurd (List.mem_map.2 ⟨(id, n), h, hp.symm⟩) hnot
      · rcases h with rfl | h
        · exact absurd rfl hp
        · simp only [List.find?_cons, hp, decide_false]
          exact ih hk' h

theorem lookupNode_of_mem {G : Graph} (hk : G.KeysNodup) {id : NodeId} {n : Node}
    (h : (id, n) ∈ G.nodes) : G.lookupNode id = some n := by
  unfold Graph.lookupNode
  rw [find?_key_of_mem hk h]
  rfl

theorem mem_of_lookupNode {G : Graph} {id : NodeId} {n : Node}
    (h : G.lookupNode id = some n) : (id, n) ∈ G.nodes := by
  unfold Graph.lookupNode at h
  rw [Option.map_eq_some_iff] at h
  obtain ⟨⟨i, m⟩, hp, hm⟩ := h
  have hmem := List.mem_of_find?_eq_some hp
  have hid := List.find?_some hp
  simp only [decide_eq_true_eq] at hid hm
  subst hid; subst hm
  exact hmem

theorem nodeOf_of_node {G : Graph} (hk : G.KeysNodup) {σ : Binding} {v : Var}
    {id : NodeId} {n : Node} (hv : σ.node v = some id) (h : (id, n) ∈ G.nodes) :
    σ.nodeOf G v = some n := by
  simp [Binding.nodeOf, hv, lookupNode_of_mem hk h]

theorem nodeOf_some {G : Graph} {σ : Binding} {v : Var} {n : Node}
    (h : σ.nodeOf G v = some n) : ∃ id, σ.node v = some id ∧ (id, n) ∈ G.nodes := by
  simp only [Binding.nodeOf, Option.bind_eq_some_iff] at h
  obtain ⟨id, hid, hl⟩ := h
  exact ⟨id, hid, mem_of_lookupNode hl⟩

/-! ## Monotonicity of matching under `Extends` -/

theorem SeqRestOk.mono {σ σ' : Binding} {r : Option Var} {u : List C}
    (h : SeqRestOk σ r u) (he : Extends σ σ') : SeqRestOk σ' r u := by
  cases r with
  | none => exact h
  | some r => exact he.2.2.2.2.1 r u h

theorem MsetRestOk.mono {σ σ' : Binding} {r : Option Var} {m : Multiset C}
    {taken : List C} (h : MsetRestOk σ r m taken) (he : Extends σ σ') :
    MsetRestOk σ' r m taken := by
  cases r with
  | none => exact h
  | some r => exact he.2.2.2.1 r _ h

theorem SetRestOk.mono {σ σ' : Binding} {r : Option Var} {s : Finset C}
    {taken : List C} (h : SetRestOk σ r s taken) (he : Extends σ σ') :
    SetRestOk σ' r s taken := by
  cases r with
  | none => exact h
  | some r => exact he.2.2.2.2.2 r _ h

mutual
theorem MatchC.mono {G : Graph} {P : Pat} {c : C} {σ σ' : Binding}
    (h : MatchC G P c σ) (he : Extends σ σ') : MatchC G P c σ' :=
  match h with
  | .var hx => .var (he.1 _ _ hx)
  | .app hmem hf hh hn => .app hmem hf hh (MatchN.mono hn he)
theorem MatchN.mono {G : Graph} {P : Pat} {n : Node} {σ σ' : Binding}
    (h : MatchN G P n σ) (he : Extends σ σ') : MatchN G P n σ' :=
  match h with
  | .plain hl hall => .plain hl (fun pc hpc => MatchC.mono (hall pc hpc) he)
  | .comm₁ hp hq => .comm₁ (MatchC.mono hp he) (MatchC.mono hq he)
  | .comm₂ hp hq => .comm₂ (MatchC.mono hp he) (MatchC.mono hq he)
  | .assoc hl hpre hsuf hall =>
      .assoc hl (hpre.mono he) (hsuf.mono he) (fun pc hpc => MatchC.mono (hall pc hpc) he)
  | .ac hnd hl hmem hall hmult hrest =>
      .ac hnd hl hmem (fun et het => MatchC.mono (hall et het) he)
        (fun et het => (hmult et het).mono he) (hrest.mono he)
  | .aci hnd hl hmem hall hrest =>
      .aci hnd hl hmem (fun et het => MatchC.mono (hall et het) he) (hrest.mono he)
end

/-! ## Binding frames -/

theorem extends_setNode_of_none {σ : Binding} {t : Var} {id : NodeId}
    (h : σ.node t = none) : Extends σ (σ.setNode t id) := by
  refine ⟨fun _ _ h => h, ?_, fun _ _ h => h, fun _ _ h => h, fun _ _ h => h,
    fun _ _ h => h⟩
  intro v i hv
  have hne : v ≠ t := by
    rintro rfl
    rw [h] at hv
    cases hv
  simp [Binding.setNode, Function.update_of_ne hne, hv]

@[simp] theorem setNode_node_of_ne (σ : Binding) (t : Var) (id : NodeId) (v : Var)
    (h : v ≠ t) : (σ.setNode t id).node v = σ.node v := by
  simp [Binding.setNode, Function.update_of_ne h]

@[simp] theorem setNode_node_self (σ : Binding) (t : Var) (id : NodeId) :
    (σ.setNode t id).node t = some id := by
  simp [Binding.setNode]

@[simp] theorem joinBind_node_self (G : Graph) (σ : Binding) (t : Var) (id : NodeId) :
    (joinBind G σ t id).node t = some id := by
  simp [joinBind, Binding.setNode, Binding.setCls]

@[simp] theorem joinBind_node_of_ne (G : Graph) (σ : Binding) (t : Var) (id : NodeId) (v : Var)
    (h : v ≠ t) : (joinBind G σ t id).node v = σ.node v := by
  simp [joinBind, Binding.setNode, Binding.setCls, Function.update_of_ne h]

@[simp] theorem joinBind_cls_self (G : Graph) (σ : Binding) (t : Var) (id : NodeId) :
    (joinBind G σ t id).cls t = some (G.find id) := by
  simp [joinBind, Binding.setNode, Binding.setCls]

@[simp] theorem joinBind_cls_of_ne (G : Graph) (σ : Binding) (t : Var) (id : NodeId) (w : Var)
    (h : w ≠ t) : (joinBind G σ t id).cls w = σ.cls w := by
  simp [joinBind, Binding.setNode, Binding.setCls, Function.update_of_ne h]

@[simp] theorem joinBind_mult (G : Graph) (σ : Binding) (t : Var) (id : NodeId) :
    (joinBind G σ t id).mult = σ.mult := rfl
@[simp] theorem joinBind_rest (G : Graph) (σ : Binding) (t : Var) (id : NodeId) :
    (joinBind G σ t id).rest = σ.rest := rfl
@[simp] theorem joinBind_seqRest (G : Graph) (σ : Binding) (t : Var) (id : NodeId) :
    (joinBind G σ t id).seqRest = σ.seqRest := rfl
@[simp] theorem joinBind_finRest (G : Graph) (σ : Binding) (t : Var) (id : NodeId) :
    (joinBind G σ t id).finRest = σ.finRest := rfl

theorem extends_joinBind_of_none {G : Graph} {σ : Binding} {t : Var} {id : NodeId}
    (h : σ.node t = none) (hc : σ.cls t = none) : Extends σ (joinBind G σ t id) := by
  refine ⟨?_, ?_, fun _ _ h => h, fun _ _ h => h, fun _ _ h => h, fun _ _ h => h⟩
  · intro w c hw
    have hne : w ≠ t := by
      rintro rfl
      rw [hc] at hw
      cases hw
    rw [joinBind_cls_of_ne _ _ _ _ _ hne]
    exact hw
  · intro v i hv
    have hne : v ≠ t := by
      rintro rfl
      rw [h] at hv
      cases hv
    rw [joinBind_node_of_ne _ _ _ _ _ hne]
    exact hv

@[simp] theorem setCls_cls_of_ne (σ : Binding) (x : Var) (c : C) (w : Var)
    (h : w ≠ x) : (σ.setCls x c).cls w = σ.cls w := by
  simp [Binding.setCls, Function.update_of_ne h]

@[simp] theorem setCls_cls_self (σ : Binding) (x : Var) (c : C) :
    (σ.setCls x c).cls x = some c := by
  simp [Binding.setCls]

/-- What a binding function leaves unchanged: `node` everywhere, `cls`
outside `cs`, `mult` outside `ks`, `rest` outside `rs`, `seqRest` outside
`ss`, `finRest` outside `fs`. -/
structure Frame (cs ks rs ss fs : List Var) (σ σ' : Binding) : Prop where
  node : σ'.node = σ.node
  cls : ∀ w, w ∉ cs → σ'.cls w = σ.cls w
  mult : ∀ k, k ∉ ks → σ'.mult k = σ.mult k
  rest : ∀ r, r ∉ rs → σ'.rest r = σ.rest r
  seqRest : ∀ r, r ∉ ss → σ'.seqRest r = σ.seqRest r
  finRest : ∀ r, r ∉ fs → σ'.finRest r = σ.finRest r

namespace Frame

theorem refl (cs ks rs ss fs : List Var) (σ : Binding) : Frame cs ks rs ss fs σ σ :=
  ⟨rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩

theorem trans {cs ks rs ss fs cs' ks' rs' ss' fs' : List Var} {σ σ' σ'' : Binding}
    (h₁ : Frame cs ks rs ss fs σ σ') (h₂ : Frame cs' ks' rs' ss' fs' σ' σ'') :
    Frame (cs ++ cs') (ks ++ ks') (rs ++ rs') (ss ++ ss') (fs ++ fs') σ σ'' where
  node := h₂.node.trans h₁.node
  cls w hw := by
    rw [List.mem_append, not_or] at hw
    rw [h₂.cls w hw.2, h₁.cls w hw.1]
  mult k hk := by
    rw [List.mem_append, not_or] at hk
    rw [h₂.mult k hk.2, h₁.mult k hk.1]
  rest r hr := by
    rw [List.mem_append, not_or] at hr
    rw [h₂.rest r hr.2, h₁.rest r hr.1]
  seqRest r hr := by
    rw [List.mem_append, not_or] at hr
    rw [h₂.seqRest r hr.2, h₁.seqRest r hr.1]
  finRest r hr := by
    rw [List.mem_append, not_or] at hr
    rw [h₂.finRest r hr.2, h₁.finRest r hr.1]

theorem mono {cs ks rs ss fs cs' ks' rs' ss' fs' : List Var} {σ σ' : Binding}
    (h : Frame cs ks rs ss fs σ σ') (hc : cs ⊆ cs') (hk : ks ⊆ ks') (hr : rs ⊆ rs')
    (hs : ss ⊆ ss') (hf : fs ⊆ fs') : Frame cs' ks' rs' ss' fs' σ σ' where
  node := h.node
  cls w hw := h.cls w (fun h' => hw (hc h'))
  mult k hk' := h.mult k (fun h' => hk' (hk h'))
  rest r hr' := h.rest r (fun h' => hr' (hr h'))
  seqRest r hr' := h.seqRest r (fun h' => hr' (hs h'))
  finRest r hr' := h.finRest r (fun h' => hr' (hf h'))

end Frame

theorem frame_setCls (σ : Binding) (x : Var) (c : C) :
    Frame [x] [] [] [] [] σ (σ.setCls x c) where
  node := rfl
  cls w hw := by simp at hw; simp [Binding.setCls, Function.update_of_ne hw]
  mult _ _ := rfl
  rest _ _ := rfl
  seqRest _ _ := rfl
  finRest _ _ := rfl

theorem frame_setMult (σ : Binding) (k : Var) (m : Nat) :
    Frame [] [k] [] [] [] σ (σ.setMult k m) where
  node := rfl
  cls _ _ := rfl
  mult k' hk := by simp at hk; simp [Binding.setMult, Function.update_of_ne hk]
  rest _ _ := rfl
  seqRest _ _ := rfl
  finRest _ _ := rfl

theorem frame_setRest (σ : Binding) (r : Var) (m : Multiset C) :
    Frame [] [] [r] [] [] σ (σ.setRest r m) where
  node := rfl
  cls _ _ := rfl
  mult _ _ := rfl
  rest r' hr := by simp at hr; simp [Binding.setRest, Function.update_of_ne hr]
  seqRest _ _ := rfl
  finRest _ _ := rfl

theorem frame_setSeqRest (σ : Binding) (r : Var) (u : List C) :
    Frame [] [] [] [r] [] σ (σ.setSeqRest r u) where
  node := rfl
  cls _ _ := rfl
  mult _ _ := rfl
  rest _ _ := rfl
  seqRest r' hr := by simp at hr; simp [Binding.setSeqRest, Function.update_of_ne hr]
  finRest _ _ := rfl

theorem frame_setSetRest (σ : Binding) (r : Var) (s : Finset C) :
    Frame [] [] [] [] [r] σ (σ.setSetRest r s) where
  node := rfl
  cls _ _ := rfl
  mult _ _ := rfl
  rest _ _ := rfl
  seqRest _ _ := rfl
  finRest r' hr := by simp at hr; simp [Binding.setSetRest, Function.update_of_ne hr]

/-- The multiplicity variable of an annotation. -/
def Mult.vars : Mult → List Var
  | .exact _ => []
  | .var k _ _ => [k]

theorem frame_multMatches {σ σ' : Binding} {μ : Mult} {m : Nat}
    (h : multMatches σ μ m = some σ') : Frame [] μ.vars [] [] [] σ σ' := by
  cases μ with
  | exact k =>
      simp only [multMatches] at h
      split at h
      · cases h; exact Frame.refl _ _ _ _ _ _
      · cases h
  | var k lo hi =>
      simp only [multMatches] at h
      split at h
      · split at h
        · split at h
          · cases h; exact Frame.refl _ _ _ _ _ _
          · cases h
        · cases h; exact frame_setMult _ _ _
      · cases h

/-- Multiplicity variables of AC elements. -/
def multVars (es : List (Var × Mult)) : List Var := es.flatMap (fun e => e.2.vars)

theorem frame_decomposeAC : ∀ (es : List (Var × Mult)) (rest : Option Var)
    (res : List (C × Nat)) (σ σ' : Binding), σ' ∈ decomposeAC es rest res σ →
    Frame (es.map (·.1)) (multVars es) rest.toList [] [] σ σ' := by
  intro es
  induction es with
  | nil =>
      intro rest res σ σ' h
      cases rest with
      | none =>
          simp [decomposeAC] at h
          obtain ⟨-, rfl⟩ := h
          exact Frame.refl _ _ _ _ _ _
      | some r =>
          simp [decomposeAC] at h
          subst h
          exact (frame_setRest _ _ _).mono (by simp) (by simp) (by simp) (by simp) (by simp)
  | cons e es ih =>
      intro rest res σ σ' h
      obtain ⟨x, μ⟩ := e
      simp only [decomposeAC] at h
      split at h
      · rename_i c hc
        split at h
        · rename_i e he
          split at h
          · rename_i σ₁ hσ₁
            have h₁ := frame_multMatches hσ₁
            have h₂ := ih rest _ σ₁ σ' h
            have := h₁.trans h₂
            refine this.mono ?_ ?_ ?_ ?_ ?_ <;> simp [multVars, List.flatMap_cons]
          · simp at h
        · simp at h
      · rw [List.mem_flatMap] at h
        obtain ⟨e, _, he⟩ := h
        split at he
        · simp at he
        · split at he
          · rename_i σ₁ hσ₁
            have h₁ := frame_multMatches hσ₁
            have h₂ := (frame_setCls σ₁ x e.1)
            have h₃ := ih rest _ _ σ' he
            have := (h₁.trans h₂).trans h₃
            refine this.mono ?_ ?_ ?_ ?_ ?_ <;> simp [multVars, List.flatMap_cons]
          · simp at he

theorem frame_decomposeACI : ∀ (es : List Var) (rest : Option Var)
    (res : List C) (σ σ' : Binding), σ' ∈ decomposeACI es rest res σ →
    Frame es [] [] [] rest.toList σ σ' := by
  intro es
  induction es with
  | nil =>
      intro rest res σ σ' h
      cases rest with
      | none =>
          simp [decomposeACI] at h
          obtain ⟨-, rfl⟩ := h
          exact Frame.refl _ _ _ _ _ _
      | some r =>
          simp [decomposeACI] at h
          subst h
          exact (frame_setSetRest _ _ _).mono (by simp) (by simp) (by simp) (by simp) (by simp)
  | cons x es ih =>
      intro rest res σ σ' h
      simp only [decomposeACI] at h
      split at h
      · split at h
        · have := ih rest _ σ σ' h
          exact this.mono (by simp) (by simp) (by simp) (by simp) (by simp)
        · simp at h
      · rw [List.mem_flatMap] at h
        obtain ⟨c, _, hc⟩ := h
        have h₁ := frame_setCls σ x c
        have h₂ := ih rest _ _ σ' hc
        exact (h₁.trans h₂).mono (by simp) (by simp) (by simp) (by simp) (by simp)

theorem frame_bindElems : ∀ (xs : List Var) (cs : List C) (σ σ' : Binding),
    bindElems xs cs σ = some σ' → Frame xs [] [] [] [] σ σ' := by
  intro xs
  induction xs with
  | nil =>
      intro cs σ σ' h
      cases cs with
      | nil => simp [bindElems] at h; subst h; exact Frame.refl _ _ _ _ _ _
      | cons c cs => simp [bindElems] at h
  | cons x xs ih =>
      intro cs σ σ' h
      cases cs with
      | nil => simp [bindElems] at h
      | cons c cs =>
          simp only [bindElems] at h
          split at h
          · split at h
            · exact (ih cs σ σ' h).mono (by simp) (by simp) (by simp) (by simp) (by simp)
            · cases h
          · have h₁ := frame_setCls σ x c
            have h₂ := ih cs _ σ' h
            exact (h₁.trans h₂).mono (by simp) (by simp) (by simp) (by simp) (by simp)

theorem frame_bindSeq (r : Option Var) (u : List C) (σ : Binding) :
    Frame [] [] [] r.toList [] σ (bindSeq r u σ) := by
  cases r with
  | none => exact Frame.refl _ _ _ _ _ _
  | some r => exact (frame_setSeqRest σ r u).mono (by simp) (by simp) (by simp) (by simp) (by simp)

theorem frame_expandA {pre suf : Option Var} {elems : List Var} {cs : List C}
    {σ σ' : Binding} (h : σ' ∈ expandA pre elems suf cs σ) :
    Frame elems [] [] (pre.toList ++ suf.toList) [] σ σ' := by
  unfold expandA at h
  rw [List.mem_flatMap] at h
  obtain ⟨k, -, hk⟩ := h
  simp only at hk
  split_ifs at hk
  all_goals try (simp only [List.not_mem_nil] at hk)
  split at hk
  · simp at hk
  · rename_i σ₁ hσ₁
    simp at hk; subst hk
    have h₁ := frame_bindElems _ _ _ _ hσ₁
    have h₂ := frame_bindSeq pre (cs.take k) σ₁
    have h₃ := frame_bindSeq suf (cs.drop (k + elems.length)) (bindSeq pre (cs.take k) σ₁)
    refine ((h₁.trans h₂).trans h₃).mono ?_ ?_ ?_ ?_ ?_ <;> simp

theorem frame_decomposeComm {x y : Var} {a b : C} {σ σ' : Binding}
    (h : σ' ∈ decomposeComm x y a b σ) : Frame [x, y] [] [] [] [] σ σ' := by
  unfold decomposeComm at h
  rw [List.mem_append, Option.mem_toList, Option.mem_toList] at h
  rcases h with h | h
  · exact frame_bindElems _ _ _ _ h
  · exact frame_bindElems _ _ _ _ h

/-! ## Rest variables of a pattern -/

mutual
/-- Rest variables: the AC and ACI rests and the A prefix and suffix. -/
def Pat.restVars : Pat → List Var
  | .var _ => []
  | .plain _ args => Pat.restVarsList args
  | .comm _ p q => p.restVars ++ q.restVars
  | .assoc _ pre args suf => pre.toList ++ suf.toList ++ Pat.restVarsList args
  | .ac _ elems rest => rest.toList ++ Pat.restVarsElems elems
  | .aci _ elems rest => rest.toList ++ Pat.restVarsList elems
def Pat.restVarsList : List Pat → List Var
  | [] => []
  | p :: ps => p.restVars ++ Pat.restVarsList ps
def Pat.restVarsElems : List (Pat × Mult) → List Var
  | [] => []
  | (p, _) :: es => p.restVars ++ Pat.restVarsElems es
end

@[simp] theorem varsList_nil : Pat.varsList [] = [] := rfl
@[simp] theorem varsList_cons (p : Pat) (ps : List Pat) :
    Pat.varsList (p :: ps) = p.vars ++ Pat.varsList ps := rfl
@[simp] theorem varsElems_nil : Pat.varsElems [] = [] := rfl
theorem varsElems_cons (p : Pat) (μ : Mult) (es : List (Pat × Mult)) :
    Pat.varsElems ((p, μ) :: es) = p.vars ++ μ.vars ++ Pat.varsElems es := by
  cases μ <;> simp [Pat.varsElems, Mult.vars]
@[simp] theorem restVarsList_nil : Pat.restVarsList [] = [] := rfl
@[simp] theorem restVarsList_cons (p : Pat) (ps : List Pat) :
    Pat.restVarsList (p :: ps) = p.restVars ++ Pat.restVarsList ps := rfl
@[simp] theorem restVarsElems_nil : Pat.restVarsElems [] = [] := rfl
@[simp] theorem restVarsElems_cons (p : Pat) (μ : Mult) (es : List (Pat × Mult)) :
    Pat.restVarsElems ((p, μ) :: es) = p.restVars ++ Pat.restVarsElems es := rfl

@[simp] theorem vars_var (x : Var) : Pat.vars (.var x) = [x] := rfl
@[simp] theorem vars_plain (f : Sym) (args : List Pat) :
    Pat.vars (.plain f args) = Pat.varsList args := rfl
@[simp] theorem vars_comm (f : Sym) (p q : Pat) : Pat.vars (.comm f p q) = p.vars ++ q.vars := rfl
@[simp] theorem vars_assoc (f : Sym) (pre : Option Var) (args : List Pat) (suf : Option Var) :
    Pat.vars (.assoc f pre args suf) = pre.toList ++ Pat.varsList args ++ suf.toList := rfl
@[simp] theorem vars_ac (f : Sym) (elems : List (Pat × Mult)) (rest : Option Var) :
    Pat.vars (.ac f elems rest) = Pat.varsElems elems ++ rest.toList := rfl
@[simp] theorem vars_aci (f : Sym) (elems : List Pat) (rest : Option Var) :
    Pat.vars (.aci f elems rest) = Pat.varsList elems ++ rest.toList := rfl

@[simp] theorem restVars_var (x : Var) : Pat.restVars (.var x) = [] := rfl
@[simp] theorem restVars_plain (f : Sym) (args : List Pat) :
    Pat.restVars (.plain f args) = Pat.restVarsList args := rfl
@[simp] theorem restVars_comm (f : Sym) (p q : Pat) :
    Pat.restVars (.comm f p q) = p.restVars ++ q.restVars := rfl
@[simp] theorem restVars_assoc (f : Sym) (pre : Option Var) (args : List Pat) (suf : Option Var) :
    Pat.restVars (.assoc f pre args suf) = pre.toList ++ suf.toList ++ Pat.restVarsList args := rfl
@[simp] theorem restVars_ac (f : Sym) (elems : List (Pat × Mult)) (rest : Option Var) :
    Pat.restVars (.ac f elems rest) = rest.toList ++ Pat.restVarsElems elems := rfl
@[simp] theorem restVars_aci (f : Sym) (elems : List Pat) (rest : Option Var) :
    Pat.restVars (.aci f elems rest) = rest.toList ++ Pat.restVarsList elems := rfl

theorem mem_varsList_of_mem {p : Pat} {ps : List Pat} (hp : p ∈ ps) {x : Var}
    (hx : x ∈ p.vars) : x ∈ Pat.varsList ps := by
  induction ps with
  | nil => simp at hp
  | cons q qs ih =>
      rw [List.mem_cons] at hp
      rcases hp with rfl | hp
      · simp [hx]
      · simp [ih hp]

theorem mem_varsElems_of_mem {e : Pat × Mult} {es : List (Pat × Mult)} (he : e ∈ es) {x : Var}
    (hx : x ∈ e.1.vars) : x ∈ Pat.varsElems es := by
  induction es with
  | nil => simp at he
  | cons e' es ih =>
      rw [List.mem_cons] at he
      obtain ⟨p, μ⟩ := e'
      rcases he with rfl | he
      · simp [varsElems_cons, hx]
      · simp [varsElems_cons, ih he]

theorem mem_varsElems_of_mult {e : Pat × Mult} {es : List (Pat × Mult)} (he : e ∈ es) {k : Var}
    (hk : k ∈ e.2.vars) : k ∈ Pat.varsElems es := by
  induction es with
  | nil => simp at he
  | cons e' es ih =>
      rw [List.mem_cons] at he
      obtain ⟨p, μ⟩ := e'
      rcases he with rfl | he
      · simp [varsElems_cons, hk]
      · simp [varsElems_cons, ih he]

/-! ## The compiler, unfolded -/

theorem compileAt_var (x : Var) (cv : Option Var) (fresh : Nat) :
    compileAt (.var x) cv fresh =
      ((match cv with | some z => [.checkEq z x] | none => [] : Plan), fresh) := by
  cases cv <;> simp [compileAt]

theorem compileAt_plain (f : Sym) (args : List Pat) (cv : Option Var) (fresh : Nat)
    {s : Plan} {fr : Nat} (h : compilePlainArgs args fresh 0 (fresh + 1) = (s, fr)) :
    compileAt (.plain f args) cv fresh = (joinStep fresh f cv :: s, fr) := by
  rw [compileAt]; simp [h]

theorem compileAt_comm (f : Sym) (p q : Pat) (cv : Option Var) (fresh : Nat)
    {vp fr₁ vq fr₂ fr₃ fr₄ : Nat} {sp sq : Plan}
    (h₁ : elemVar p (fresh + 1) = (vp, fr₁)) (h₂ : elemVar q fr₁ = (vq, fr₂))
    (h₃ : compileNested p vp fr₂ = (sp, fr₃)) (h₄ : compileNested q vq fr₃ = (sq, fr₄)) :
    compileAt (.comm f p q) cv fresh =
      (joinStep fresh f cv :: .decomposeComm fresh vp vq :: sp ++ sq, fr₄) := by
  rw [compileAt]; simp [h₁, h₂, h₃, h₄]

theorem compileAt_assoc (f : Sym) (pre : Option Var) (args : List Pat) (suf : Option Var)
    (cv : Option Var) (fresh : Nat) {vs : List Var} {fr₁ fr₂ : Nat} {s : Plan}
    (h₁ : elemVars args (fresh + 1) = (vs, fr₁))
    (h₂ : compileNestedList args vs fr₁ = (s, fr₂)) :
    compileAt (.assoc f pre args suf) cv fresh =
      (joinStep fresh f cv :: .expandA fresh pre vs suf :: s, fr₂) := by
  rw [compileAt]; simp [h₁, h₂]

theorem compileAt_ac (f : Sym) (elems : List (Pat × Mult)) (rest : Option Var)
    (cv : Option Var) (fresh : Nat) {vs : List (Var × Mult)} {fr₁ fr₂ : Nat} {s : Plan}
    (h₁ : elemVarsAC elems (fresh + 1) = (vs, fr₁))
    (h₂ : compileNestedAC elems (vs.map (·.1)) fr₁ = (s, fr₂)) :
    compileAt (.ac f elems rest) cv fresh =
      (joinStep fresh f cv :: .decomposeAC fresh vs rest :: s, fr₂) := by
  rw [compileAt]; simp [h₁, h₂]

theorem compileAt_aci (f : Sym) (elems : List Pat) (rest : Option Var)
    (cv : Option Var) (fresh : Nat) {vs : List Var} {fr₁ fr₂ : Nat} {s : Plan}
    (h₁ : elemVars elems (fresh + 1) = (vs, fr₁))
    (h₂ : compileNestedList elems vs fr₁ = (s, fr₂)) :
    compileAt (.aci f elems rest) cv fresh =
      (joinStep fresh f cv :: .decomposeACI fresh vs rest :: s, fr₂) := by
  rw [compileAt]; simp [h₁, h₂]

theorem compilePlainArgs_nil (nv : Var) (i fresh : Nat) :
    compilePlainArgs [] nv i fresh = ([], fresh) := by
  rw [compilePlainArgs]

theorem compilePlainArgs_cons (p : Pat) (ps : List Pat) (nv : Var) (i fresh : Nat)
    {v fr₁ fr₂ fr₃ : Nat} {sp s : Plan}
    (h₁ : elemVar p fresh = (v, fr₁)) (h₂ : compileNested p v fr₁ = (sp, fr₂))
    (h₃ : compilePlainArgs ps nv (i + 1) fr₂ = (s, fr₃)) :
    compilePlainArgs (p :: ps) nv i fresh = (.extractChild nv i v :: sp ++ s, fr₃) := by
  rw [compilePlainArgs]; simp [h₁, h₂, h₃]

theorem compileNested_var (x : Var) (v : Var) (fresh : Nat) :
    compileNested (.var x) v fresh = ([], fresh) := by
  rw [compileNested]

theorem compileNested_app (p : Pat) (hp : p.head.isSome = true) (v : Var) (fresh : Nat) :
    compileNested p v fresh = compileAt p (some v) fresh := by
  cases p with
  | var x => simp [Pat.head] at hp
  | plain f args => rw [compileNested]
  | comm f p q => rw [compileNested]
  | assoc f pre args suf => rw [compileNested]
  | ac f elems rest => rw [compileNested]
  | aci f elems rest => rw [compileNested]

theorem compileNestedList_cons (p : Pat) (ps : List Pat) (v : Var) (vs : List Var) (fresh : Nat)
    {fr₁ fr₂ : Nat} {sp s : Plan}
    (h₁ : compileNested p v fresh = (sp, fr₁)) (h₂ : compileNestedList ps vs fr₁ = (s, fr₂)) :
    compileNestedList (p :: ps) (v :: vs) fresh = (sp ++ s, fr₂) := by
  rw [compileNestedList]; simp [h₁, h₂]

theorem compileNestedList_nil_left (vs : List Var) (fresh : Nat) :
    compileNestedList [] vs fresh = ([], fresh) := by
  cases vs <;> simp [compileNestedList]

theorem compileNestedList_nil_right (ps : List Pat) (fresh : Nat) :
    compileNestedList ps [] fresh = ([], fresh) := by
  cases ps <;> simp [compileNestedList]

theorem compileNestedAC_cons (p : Pat) (μ : Mult) (es : List (Pat × Mult)) (v : Var)
    (vs : List Var) (fresh : Nat) {fr₁ fr₂ : Nat} {sp s : Plan}
    (h₁ : compileNested p v fresh = (sp, fr₁)) (h₂ : compileNestedAC es vs fr₁ = (s, fr₂)) :
    compileNestedAC ((p, μ) :: es) (v :: vs) fresh = (sp ++ s, fr₂) := by
  rw [compileNestedAC]; simp [h₁, h₂]

theorem compileNestedAC_nil_left (vs : List Var) (fresh : Nat) :
    compileNestedAC [] vs fresh = ([], fresh) := by
  cases vs <;> simp [compileNestedAC]

theorem compileNestedAC_nil_right (es : List (Pat × Mult)) (fresh : Nat) :
    compileNestedAC es [] fresh = ([], fresh) := by
  cases es with
  | nil => simp [compileNestedAC]
  | cons e es => obtain ⟨p, μ⟩ := e; simp [compileNestedAC]

/-! ## Allocation of element variables -/

/-- The class variable `v` of an element pattern `p`, allocated between `lo`
and `hi`: the variable itself for a variable pattern, a fresh one in
`[lo, hi)` for an application. -/
def ElemRel (lo hi : Nat) (p : Pat) (v : Var) : Prop :=
  (∃ x, p = .var x ∧ v = x) ∨ (p.head.isSome = true ∧ lo ≤ v ∧ v < hi)

theorem ElemRel.mono {lo hi lo' hi' : Nat} {p : Pat} {v : Var} (h : ElemRel lo hi p v)
    (h₁ : lo' ≤ lo) (h₂ : hi ≤ hi') : ElemRel lo' hi' p v := by
  rcases h with h | ⟨hh, hlo, hhi⟩
  · exact Or.inl h
  · exact Or.inr ⟨hh, le_trans h₁ hlo, lt_of_lt_of_le hhi h₂⟩

theorem elemVar_spec (p : Pat) (fresh : Nat) {v fr : Nat} (h : elemVar p fresh = (v, fr)) :
    (∃ x, p = .var x ∧ v = x ∧ fr = fresh) ∨
      (p.head.isSome = true ∧ v = fresh ∧ fr = fresh + 1) := by
  cases p with
  | var x => simp [elemVar] at h; exact Or.inl ⟨x, rfl, h.1.symm, h.2.symm⟩
  | plain f args => simp [elemVar] at h; exact Or.inr ⟨rfl, h.1.symm, h.2.symm⟩
  | comm f p q => simp [elemVar] at h; exact Or.inr ⟨rfl, h.1.symm, h.2.symm⟩
  | assoc f pre args suf => simp [elemVar] at h; exact Or.inr ⟨rfl, h.1.symm, h.2.symm⟩
  | ac f elems rest => simp [elemVar] at h; exact Or.inr ⟨rfl, h.1.symm, h.2.symm⟩
  | aci f elems rest => simp [elemVar] at h; exact Or.inr ⟨rfl, h.1.symm, h.2.symm⟩

theorem elemVar_rel (p : Pat) (fresh : Nat) {v fr : Nat} (h : elemVar p fresh = (v, fr)) :
    fresh ≤ fr ∧ ElemRel fresh fr p v := by
  rcases elemVar_spec p fresh h with ⟨x, rfl, rfl, rfl⟩ | ⟨hh, rfl, rfl⟩
  · exact ⟨le_refl _, Or.inl ⟨_, rfl, rfl⟩⟩
  · exact ⟨by vomega, Or.inr ⟨hh, le_refl _, by vomega⟩⟩

theorem elemVars_spec : ∀ (ps : List Pat) (fresh : Nat) {vs : List Var} {fr : Nat},
    elemVars ps fresh = (vs, fr) → fresh ≤ fr ∧ List.Forall₂ (ElemRel fresh fr) ps vs := by
  intro ps
  induction ps with
  | nil =>
      intro fresh vs fr h
      simp [elemVars] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨le_refl _, List.Forall₂.nil⟩
  | cons p ps ih =>
      intro fresh vs fr h
      simp only [elemVars] at h
      rcases h₁ : elemVar p fresh with ⟨v, fr₁⟩
      rcases h₂ : elemVars ps fr₁ with ⟨vs', fr₂⟩
      rw [h₁, h₂] at h
      simp at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨hle₁, hrel₁⟩ := elemVar_rel p fresh h₁
      obtain ⟨hle₂, hrel₂⟩ := ih fr₁ h₂
      refine ⟨by vomega, List.Forall₂.cons (hrel₁.mono (le_refl _) hle₂) ?_⟩
      exact List.Forall₂.imp (fun _ _ h => h.mono hle₁ (le_refl _)) hrel₂

theorem elemVarsAC_spec : ∀ (es : List (Pat × Mult)) (fresh : Nat) {vs : List (Var × Mult)}
    {fr : Nat}, elemVarsAC es fresh = (vs, fr) →
    fresh ≤ fr ∧ List.Forall₂ (fun e v => e.2 = v.2 ∧ ElemRel fresh fr e.1 v.1) es vs := by
  intro es
  induction es with
  | nil =>
      intro fresh vs fr h
      simp [elemVarsAC] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨le_refl _, List.Forall₂.nil⟩
  | cons e es ih =>
      intro fresh vs fr h
      obtain ⟨p, μ⟩ := e
      simp only [elemVarsAC] at h
      rcases h₁ : elemVar p fresh with ⟨v, fr₁⟩
      rcases h₂ : elemVarsAC es fr₁ with ⟨vs', fr₂⟩
      rw [h₁, h₂] at h
      simp at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨hle₁, hrel₁⟩ := elemVar_rel p fresh h₁
      obtain ⟨hle₂, hrel₂⟩ := ih fr₁ h₂
      refine ⟨by vomega, List.Forall₂.cons ⟨rfl, hrel₁.mono (le_refl _) hle₂⟩ ?_⟩
      exact List.Forall₂.imp (fun _ _ h => ⟨h.1, h.2.mono hle₁ (le_refl _)⟩) hrel₂

/-! ## The frame of a compiled plan -/

/-- Node variables at or above `k` are unbound. -/
def NodeFree (k : Nat) (σ : Binding) : Prop :=
  ∀ v, k ≤ v → σ.node v = none ∧ σ.cls v = none

/-- The rest variables in `R` are unbound in all three rest maps. -/
def RestFree (R : List Var) (σ : Binding) : Prop :=
  ∀ r ∈ R, σ.rest r = none ∧ σ.seqRest r = none ∧ σ.finRest r = none

theorem NodeFree.mono {k k' : Nat} {σ : Binding} (h : NodeFree k σ) (hk : k ≤ k') :
    NodeFree k' σ := fun v hv => h v (le_trans hk hv)

theorem RestFree.mono {R R' : List Var} {σ : Binding} (h : RestFree R σ) (hR : R' ⊆ R) :
    RestFree R' σ := fun r hr => h r (hR hr)

theorem forall₂_exists_left {α β : Type} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ b ∈ l₂, ∃ a ∈ l₁, R a b := by
  intro l₁ l₂ h
  induction h with
  | nil => intro b hb; simp at hb
  | cons hab hs ih =>
      intro b hb
      rw [List.mem_cons] at hb
      rcases hb with rfl | hb
      · exact ⟨_, List.mem_cons_self .., hab⟩
      · obtain ⟨a, ha, h'⟩ := ih b hb
        exact ⟨a, List.mem_cons_of_mem _ ha, h'⟩

theorem ElemRel.mem_or_range {lo hi : Nat} {p : Pat} {v : Var} (h : ElemRel lo hi p v) :
    v ∈ p.vars ∨ (lo ≤ v ∧ v < hi) := by
  rcases h with ⟨x, rfl, rfl⟩ | ⟨-, hlo, hhi⟩
  · exact Or.inl (by simp)
  · exact Or.inr ⟨hlo, hhi⟩

theorem RestFree.joinBind {R : List Var} {σ : Binding} (h : RestFree R σ) (G : Graph) (t : Var)
    (id : NodeId) : RestFree R (joinBind G σ t id) := h

theorem NodeFree.joinBind {k : Nat} {σ : Binding} (h : NodeFree k σ) (G : Graph) (t : Var)
    (ht : t < k) (id : NodeId) : NodeFree k (joinBind G σ t id) := by
  intro w hw
  have hne : w ≠ t := by vomega
  rw [joinBind_node_of_ne _ _ _ _ _ hne, joinBind_cls_of_ne _ _ _ _ _ hne]
  exact h w hw

/-- `NodeFree` across a step frame: the node map is untouched and the
class variables written are all below the new bound. -/
theorem NodeFree.ofFrame {cs ks rs ss fs : List Var} {σ σ' : Binding} {k k' : Nat}
    (hfr : Frame cs ks rs ss fs σ σ') (hnf : NodeFree k σ) (hk : k ≤ k')
    (hcs : ∀ w ∈ cs, w < k') : NodeFree k' σ' := by
  intro w hw
  rw [hfr.node, hfr.cls w (fun h => by have := hcs w h; vomega)]
  exact hnf w (by vomega)

theorem ElemRel.lt_of_lt {lo hi : Nat} {p : Pat} {v : Var} (h : ElemRel lo hi p v)
    (hlt : ∀ x ∈ p.vars, x < lo) (hle : lo ≤ hi) : v < hi := by
  rcases h.mem_or_range with h | h
  · have := hlt v h; vomega
  · exact h.2

theorem forall₂_elemRel_lt {lo hi : Nat} {ps : List Pat} {vs : List Var}
    (hrel : List.Forall₂ (ElemRel lo hi) ps vs) (hlt : ∀ x ∈ Pat.varsList ps, x < lo)
    (hle : lo ≤ hi) : ∀ v ∈ vs, v < hi := by
  intro v hv
  obtain ⟨p, hp, hpv⟩ := forall₂_exists_left hrel v hv
  exact hpv.lt_of_lt (fun x hx => hlt x (mem_varsList_of_mem hp hx)) hle

theorem forall₂_elemRel_lt_ac {lo hi : Nat} {es : List (Pat × Mult)} {vs : List (Var × Mult)}
    (hrel : List.Forall₂ (fun e v => e.2 = v.2 ∧ ElemRel lo hi e.1 v.1) es vs)
    (hlt : ∀ x ∈ Pat.varsElems es, x < lo) (hle : lo ≤ hi) : ∀ v ∈ vs.map (·.1), v < hi := by
  intro v hv
  rw [List.mem_map] at hv
  obtain ⟨v', hv', rfl⟩ := hv
  obtain ⟨e, he, -, hpv⟩ := forall₂_exists_left hrel v' hv'
  exact hpv.lt_of_lt (fun x hx => hlt x (mem_varsElems_of_mem he hx)) hle

/-- A run of a compiled plan for a pattern with variables `V` and rest
variables `R`, allocating fresh variables in `[fresh, fr)`: it extends the
binding, binds node variables only in `[fresh, fr)`, class variables only in
`V` or `[fresh, fr)`, multiplicity variables only in `V`, and rest variables
only in `R`. -/
structure PlanFrame (V R : List Var) (fresh fr : Nat) (σ σ' : Binding) : Prop where
  ext : Extends σ σ'
  node : ∀ v, (v < fresh ∨ fr ≤ v) → σ'.node v = σ.node v
  cls : ∀ w, w ∉ V → (w < fresh ∨ fr ≤ w) → σ'.cls w = σ.cls w
  mult : ∀ k, k ∉ V → σ'.mult k = σ.mult k
  rest : ∀ r, r ∉ R → σ'.rest r = σ.rest r
  seqRest : ∀ r, r ∉ R → σ'.seqRest r = σ.seqRest r
  finRest : ∀ r, r ∉ R → σ'.finRest r = σ.finRest r

namespace PlanFrame

theorem refl (V R : List Var) (fresh fr : Nat) (σ : Binding) : PlanFrame V R fresh fr σ σ :=
  ⟨Extends.refl σ, fun _ _ => rfl, fun _ _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl,
    fun _ _ => rfl, fun _ _ => rfl⟩

theorem trans {V₁ R₁ V₂ R₂ : List Var} {f₁ f₂ f₃ : Nat} {σ σ' σ'' : Binding}
    (h₁ : PlanFrame V₁ R₁ f₁ f₂ σ σ') (h₂ : PlanFrame V₂ R₂ f₂ f₃ σ' σ'')
    (hle₁ : f₁ ≤ f₂) (hle₂ : f₂ ≤ f₃) :
    PlanFrame (V₁ ++ V₂) (R₁ ++ R₂) f₁ f₃ σ σ'' where
  ext := h₁.ext.trans h₂.ext
  node v hv := by
    rcases hv with hv | hv
    · rw [h₂.node v (Or.inl (by vomega)), h₁.node v (Or.inl hv)]
    · rw [h₂.node v (Or.inr hv), h₁.node v (Or.inr (by vomega))]
  cls w hw hr := by
    rw [List.mem_append, not_or] at hw
    rcases hr with hr | hr
    · rw [h₂.cls w hw.2 (Or.inl (by vomega)), h₁.cls w hw.1 (Or.inl hr)]
    · rw [h₂.cls w hw.2 (Or.inr hr), h₁.cls w hw.1 (Or.inr (by vomega))]
  mult k hk := by
    rw [List.mem_append, not_or] at hk
    rw [h₂.mult k hk.2, h₁.mult k hk.1]
  rest r hr := by
    rw [List.mem_append, not_or] at hr
    rw [h₂.rest r hr.2, h₁.rest r hr.1]
  seqRest r hr := by
    rw [List.mem_append, not_or] at hr
    rw [h₂.seqRest r hr.2, h₁.seqRest r hr.1]
  finRest r hr := by
    rw [List.mem_append, not_or] at hr
    rw [h₂.finRest r hr.2, h₁.finRest r hr.1]

theorem mono {V R V' R' : List Var} {fresh fr fresh' fr' : Nat} {σ σ' : Binding}
    (h : PlanFrame V R fresh fr σ σ') (hV : V ⊆ V') (hR : R ⊆ R')
    (h₁ : fresh' ≤ fresh) (h₂ : fr ≤ fr') : PlanFrame V' R' fresh' fr' σ σ' where
  ext := h.ext
  node v hv := h.node v (by rcases hv with hv | hv; exact Or.inl (by vomega); exact Or.inr (by vomega))
  cls w hw hr := h.cls w (fun h' => hw (hV h'))
    (by rcases hr with hr | hr; exact Or.inl (by vomega); exact Or.inr (by vomega))
  mult k hk := h.mult k (fun h' => hk (hV h'))
  rest r hr := h.rest r (fun h' => hr (hR h'))
  seqRest r hr := h.seqRest r (fun h' => hr (hR h'))
  finRest r hr := h.finRest r (fun h' => hr (hR h'))

/-- A step with a `Frame` and `Extends` is a plan frame when its bound
variables lie in the pattern's variables or the fresh range. -/
theorem ofFrame {cs ks rs ss fs V R : List Var} {fresh fr : Nat} {σ σ' : Binding}
    (hf : Frame cs ks rs ss fs σ σ') (he : Extends σ σ')
    (hc : ∀ w ∈ cs, w ∈ V ∨ (fresh ≤ w ∧ w < fr)) (hk : ks ⊆ V) (hr : rs ⊆ R)
    (hs : ss ⊆ R) (hfs : fs ⊆ R) : PlanFrame V R fresh fr σ σ' where
  ext := he
  node v _ := by rw [hf.node]
  cls w hw hrng := by
    apply hf.cls
    intro hmem
    rcases hc w hmem with h | h
    · exact hw h
    · rcases hrng with hrng | hrng <;> vomega
  mult k hk' := hf.mult k (fun h => hk' (hk h))
  rest r hr' := hf.rest r (fun h => hr' (hr h))
  seqRest r hr' := hf.seqRest r (fun h => hr' (hs h))
  finRest r hr' := hf.finRest r (fun h => hr' (hfs h))

theorem join {G : Graph} {V R : List Var} {fresh fr : Nat} {σ : Binding} {t : Var} {id : NodeId}
    (h : σ.node t = none ∧ σ.cls t = none) (h₁ : fresh ≤ t) (h₂ : t < fr) :
    PlanFrame V R fresh fr σ (joinBind G σ t id) where
  ext := extends_joinBind_of_none h.1 h.2
  node v hv := by
    have : v ≠ t := by rcases hv with hv | hv <;> vomega
    simp [this]
  cls w _ hw := by
    have : w ≠ t := by rcases hw with hw | hw <;> vomega
    simp [this]
  mult _ _ := rfl
  rest _ _ := rfl
  seqRest _ _ := rfl
  finRest _ _ := rfl

end PlanFrame

theorem runStep_join_mem {G : Graph} {t : Var} {ls : List Lookup} {σ σ' : Binding} :
    σ' ∈ runStep G (.join t ls) σ ↔ ∃ id ∈ candidates G σ ls, joinBind G σ t id = σ' := by
  simp [runStep]

/-- The lookups of a `joinStep` hold exactly for the nodes with head `f`
in the class of `cv` when `cv` is bound. -/
theorem joinStep_pred (G : Graph) (σ : Binding) (f : Sym) (cv : Option Var) (id : NodeId) :
    (∀ l ∈ (match cv with | some z => [Lookup.byRepr z, .byOp f] | none => [.byOp f] : List Lookup),
      l.pred G σ id) ↔
    (∃ n, (id, n) ∈ G.nodes ∧ n.op = f) ∧ ∀ z, cv = some z → σ.cls z = some (G.find id) := by
  cases cv with
  | none =>
      constructor
      · intro hall
        have h₂ := hall (.byOp f) (by simp)
        exact ⟨h₂, fun z hz => by cases hz⟩
      · rintro ⟨⟨n, hn, hop⟩, -⟩ l hl
        simp only [List.mem_singleton] at hl
        subst hl
        exact ⟨n, hn, hop⟩
  | some z =>
      constructor
      · intro hall
        have h₁ := hall (.byRepr z) (by simp)
        have h₂ := hall (.byOp f) (by simp)
        exact ⟨h₂, fun z' hz => by cases hz; exact h₁.2⟩
      · rintro ⟨⟨n, hn, hop⟩, hz⟩ l hl
        simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
        rcases hl with rfl | rfl
        · exact ⟨⟨n, hn⟩, hz z rfl⟩
        · exact ⟨n, hn, hop⟩

theorem mem_joinStep {G : Graph} {nv : Var} {f : Sym} {cv : Option Var} {σ σ' : Binding} :
    σ' ∈ runStep G (joinStep nv f cv) σ ↔
      ∃ id n, (id, n) ∈ G.nodes ∧ n.op = f ∧ (∀ z, cv = some z → σ.cls z = some (G.find id)) ∧
        joinBind G σ nv id = σ' := by
  unfold joinStep
  rw [runStep_join_mem]
  constructor
  · rintro ⟨id, hid, rfl⟩
    rw [join_complete'] at hid
    obtain ⟨-, hall⟩ := hid
    obtain ⟨⟨n, hmem, hop⟩, hz⟩ := (joinStep_pred G σ f cv id).1 hall
    exact ⟨id, n, hmem, hop, hz, rfl⟩
  · rintro ⟨id, n, hmem, hop, hz, rfl⟩
    refine ⟨id, ?_, rfl⟩
    rw [join_complete']
    exact ⟨⟨n, hmem⟩, (joinStep_pred G σ f cv id).2 ⟨⟨n, hmem, hop⟩, hz⟩⟩

theorem runStep_extractChild_mem {G : Graph} {v out : Var} {pos : Nat} {σ σ' : Binding}
    (h : σ' ∈ runStep G (.extractChild v pos out) σ) :
    ∃ n c, σ.nodeOf G v = some n ∧ n.children.childAt pos = some c ∧
      σ'.cls out = some c ∧ Extends σ σ' ∧ Frame [out] [] [] [] [] σ σ' := by
  simp only [runStep] at h
  cases hn : σ.nodeOf G v with
  | none => simp [hn] at h
  | some n =>
    simp only [hn] at h
    cases hc : n.children.childAt pos with
    | none => simp [hc] at h
    | some c =>
      simp only [hc] at h
      cases hco : σ.cls out with
      | none =>
          simp only [hco, List.mem_singleton] at h
          subst h
          exact ⟨n, c, by first | rfl | exact hn, by first | rfl | exact hc, by simp,
            extends_setCls_of_none hco, frame_setCls _ _ _⟩
      | some c' =>
          simp only [hco] at h
          by_cases hcc : c' = c
          · subst hcc
            simp at h
            subst h
            exact ⟨n, c', by first | rfl | exact hn, by first | rfl | exact hc, hco,
              Extends.refl _, Frame.refl _ _ _ _ _ _⟩
          · simp [hcc] at h

/-- Complete direction of `extractChild`: a node at `v` with child `c` at
`pos` and `out` unbound or bound to `c` yields a binding below any `σ*`
that binds `out` to `c`. -/
theorem runStep_extractChild_complete {G : Graph} {v out : Var} {pos : Nat} {σ : Binding}
    {n : Node} {c : C} (hn : σ.nodeOf G v = some n) (hc : n.children.childAt pos = some c)
    (hout : σ.cls out = none ∨ σ.cls out = some c) :
    ∃ σ' ∈ runStep G (.extractChild v pos out) σ, σ'.cls out = some c ∧
      (σ' = σ ∨ σ' = σ.setCls out c) := by
  rcases hout with hout | hout
  · exact ⟨σ.setCls out c, by simp [runStep, hn, hc, hout], by simp, Or.inr rfl⟩
  · exact ⟨σ, by simp [runStep, hn, hc, hout], hout, Or.inl rfl⟩

/-- The main invariant on a compiled sub-plan. -/
def StructAt (G : Graph) (P : Pat) : Prop :=
  ∀ (cv : Option Var) (fresh : Nat) (σ σ' : Binding),
    (∀ x ∈ P.vars, x < fresh) → NodeFree fresh σ → RestFree P.restVars σ → P.restVars.Nodup →
    σ' ∈ run G (compileAt P cv fresh).1 σ →
    PlanFrame P.vars P.restVars fresh (compileAt P cv fresh).2 σ σ' ∧
      NodeFree (compileAt P cv fresh).2 σ' ∧ fresh ≤ (compileAt P cv fresh).2

theorem structNested {G : Graph} {p : Pat} (hp : StructAt G p) (v : Var) (fresh : Nat)
    (σ σ' : Binding) (hlt : ∀ x ∈ p.vars, x < fresh) (hnf : NodeFree fresh σ) (hrf : RestFree p.restVars σ)
    (hnd : p.restVars.Nodup) (h : σ' ∈ run G (compileNested p v fresh).1 σ) :
    PlanFrame p.vars p.restVars fresh (compileNested p v fresh).2 σ σ' ∧
      NodeFree (compileNested p v fresh).2 σ' ∧ fresh ≤ (compileNested p v fresh).2 := by
  cases hh : p.head.isSome
  · cases p with
    | var x =>
        rw [compileNested_var] at h ⊢
        simp at h; subst h
        exact ⟨PlanFrame.refl _ _ _ _ _, hnf, le_refl _⟩
    | plain f args => simp [Pat.head] at hh
    | comm f p q => simp [Pat.head] at hh
    | assoc f pre args suf => simp [Pat.head] at hh
    | ac f elems rest => simp [Pat.head] at hh
    | aci f elems rest => simp [Pat.head] at hh
  · rw [compileNested_app p hh] at h ⊢
    exact hp (some v) fresh σ σ' hlt hnf hrf hnd h

theorem structNestedList {G : Graph} : ∀ (ps : List Pat), (∀ p ∈ ps, StructAt G p) →
    ∀ (vs : List Var) (fresh : Nat) (σ σ' : Binding),
    (∀ x ∈ Pat.varsList ps, x < fresh) →
    NodeFree fresh σ → RestFree (Pat.restVarsList ps) σ → (Pat.restVarsList ps).Nodup →
    σ' ∈ run G (compileNestedList ps vs fresh).1 σ →
    PlanFrame (Pat.varsList ps) (Pat.restVarsList ps) fresh (compileNestedList ps vs fresh).2 σ σ' ∧
      NodeFree (compileNestedList ps vs fresh).2 σ' ∧ fresh ≤ (compileNestedList ps vs fresh).2 := by
  intro ps
  induction ps with
  | nil =>
      intro _ vs fresh σ σ' _ hnf _ _ h
      rw [compileNestedList_nil_left] at h ⊢
      simp at h; subst h
      exact ⟨PlanFrame.refl _ _ _ _ _, hnf, le_refl _⟩
  | cons p ps ih =>
      intro hall vs fresh σ σ' hlt hnf hrf hnd h
      cases vs with
      | nil =>
          rw [compileNestedList_nil_right] at h ⊢
          simp at h; subst h
          exact ⟨PlanFrame.refl _ _ _ _ _, hnf, le_refl _⟩
      | cons v vs =>
          rcases h₁ : compileNested p v fresh with ⟨sp, fr₁⟩
          rcases h₂ : compileNestedList ps vs fr₁ with ⟨s, fr₂⟩
          rw [compileNestedList_cons p ps v vs fresh h₁ h₂] at h ⊢
          simp only at h ⊢
          rw [mem_run_append] at h
          obtain ⟨σ₁, hσ₁, hσ'⟩ := h
          rw [restVarsList_cons] at hrf hnd
          have hnd' := List.nodup_append.1 hnd
          obtain ⟨hf₁, hnf₁, hle₁⟩ := structNested (hall p (List.mem_cons_self ..)) v fresh σ σ₁
            (fun x hx => hlt x (by simp [hx])) hnf
            (hrf.mono (List.subset_append_left _ _)) hnd'.1 (by rw [h₁]; exact hσ₁)
          rw [h₁] at hf₁ hnf₁ hle₁
          simp only at hf₁ hnf₁ hle₁
          have hrf₂ : RestFree (Pat.restVarsList ps) σ₁ := by
            intro r hr
            have hnot : r ∉ p.restVars := fun hr' => hnd'.2.2 r hr' r hr rfl
            rw [hf₁.rest r hnot, hf₁.seqRest r hnot, hf₁.finRest r hnot]
            exact hrf r (List.mem_append_right _ hr)
          obtain ⟨hf₂, hnf₂, hle₂⟩ := ih (fun q hq => hall q (List.mem_cons_of_mem _ hq)) vs fr₁ σ₁ σ'
            (fun x hx => by have := hlt x (by simp [varsElems_cons, hx]); vomega) hnf₁ hrf₂ hnd'.2.1
            (by rw [h₂]; exact hσ')
          rw [h₂] at hf₂ hnf₂ hle₂
          simp only at hf₂ hnf₂ hle₂
          exact ⟨by simpa using hf₁.trans hf₂ hle₁ hle₂, hnf₂, by vomega⟩

theorem structNestedAC {G : Graph} : ∀ (es : List (Pat × Mult)), (∀ e ∈ es, StructAt G e.1) →
    ∀ (vs : List Var) (fresh : Nat) (σ σ' : Binding),
    (∀ x ∈ Pat.varsElems es, x < fresh) →
    NodeFree fresh σ → RestFree (Pat.restVarsElems es) σ → (Pat.restVarsElems es).Nodup →
    σ' ∈ run G (compileNestedAC es vs fresh).1 σ →
    PlanFrame (Pat.varsElems es) (Pat.restVarsElems es) fresh (compileNestedAC es vs fresh).2 σ σ' ∧
      NodeFree (compileNestedAC es vs fresh).2 σ' ∧ fresh ≤ (compileNestedAC es vs fresh).2 := by
  intro es
  induction es with
  | nil =>
      intro _ vs fresh σ σ' _ hnf _ _ h
      rw [compileNestedAC_nil_left] at h ⊢
      simp at h; subst h
      exact ⟨PlanFrame.refl _ _ _ _ _, hnf, le_refl _⟩
  | cons e es ih =>
      intro hall vs fresh σ σ' hlt hnf hrf hnd h
      obtain ⟨p, μ⟩ := e
      cases vs with
      | nil =>
          rw [compileNestedAC_nil_right] at h ⊢
          simp at h; subst h
          exact ⟨PlanFrame.refl _ _ _ _ _, hnf, le_refl _⟩
      | cons v vs =>
          rcases h₁ : compileNested p v fresh with ⟨sp, fr₁⟩
          rcases h₂ : compileNestedAC es vs fr₁ with ⟨s, fr₂⟩
          rw [compileNestedAC_cons p μ es v vs fresh h₁ h₂] at h ⊢
          simp only at h ⊢
          rw [mem_run_append] at h
          obtain ⟨σ₁, hσ₁, hσ'⟩ := h
          rw [restVarsElems_cons] at hrf hnd
          have hnd' := List.nodup_append.1 hnd
          obtain ⟨hf₁, hnf₁, hle₁⟩ := structNested (hall (p, μ) (List.mem_cons_self ..)) v fresh σ σ₁
            (fun x hx => hlt x (by simp [varsElems_cons, hx])) hnf
            (hrf.mono (List.subset_append_left _ _)) hnd'.1 (by rw [h₁]; exact hσ₁)
          rw [h₁] at hf₁ hnf₁ hle₁
          simp only at hf₁ hnf₁ hle₁
          have hrf₂ : RestFree (Pat.restVarsElems es) σ₁ := by
            intro r hr
            have hnot : r ∉ p.restVars := fun hr' => hnd'.2.2 r hr' r hr rfl
            rw [hf₁.rest r hnot, hf₁.seqRest r hnot, hf₁.finRest r hnot]
            exact hrf r (List.mem_append_right _ hr)
          obtain ⟨hf₂, hnf₂, hle₂⟩ := ih (fun q hq => hall q (List.mem_cons_of_mem _ hq)) vs fr₁ σ₁ σ'
            (fun x hx => by have := hlt x (by simp [varsElems_cons, hx]); vomega) hnf₁ hrf₂ hnd'.2.1
            (by rw [h₂]; exact hσ')
          rw [h₂] at hf₂ hnf₂ hle₂
          simp only at hf₂ hnf₂ hle₂
          refine ⟨?_, hnf₂, by vomega⟩
          have := hf₁.trans hf₂ hle₁ hle₂
          rw [varsElems_cons, restVarsElems_cons]
          exact this.mono (by intro x hx; simp only [List.mem_append] at hx ⊢; tauto)
            (List.Subset.refl _) (le_refl _) (le_refl _)

theorem structArgs {G : Graph} : ∀ (args : List Pat), (∀ p ∈ args, StructAt G p) →
    ∀ (nv : Var) (i fresh : Nat) (σ σ' : Binding),
    (∀ x ∈ Pat.varsList args, x < fresh) →
    NodeFree fresh σ → RestFree (Pat.restVarsList args) σ → (Pat.restVarsList args).Nodup →
    σ' ∈ run G (compilePlainArgs args nv i fresh).1 σ →
    PlanFrame (Pat.varsList args) (Pat.restVarsList args) fresh
        (compilePlainArgs args nv i fresh).2 σ σ' ∧
      NodeFree (compilePlainArgs args nv i fresh).2 σ' ∧
      fresh ≤ (compilePlainArgs args nv i fresh).2 := by
  intro args
  induction args with
  | nil =>
      intro _ nv i fresh σ σ' _ hnf _ _ h
      rw [compilePlainArgs_nil] at h ⊢
      simp at h; subst h
      exact ⟨PlanFrame.refl _ _ _ _ _, hnf, le_refl _⟩
  | cons p ps ih =>
      intro hall nv i fresh σ σ' hlt hnf hrf hnd h
      rcases h₁ : elemVar p fresh with ⟨v, fr₁⟩
      rcases h₂ : compileNested p v fr₁ with ⟨sp, fr₂⟩
      rcases h₃ : compilePlainArgs ps nv (i + 1) fr₂ with ⟨s, fr₃⟩
      rw [compilePlainArgs_cons p ps nv i fresh h₁ h₂ h₃] at h ⊢
      simp only at h ⊢
      rw [List.cons_append, mem_run_cons] at h
      obtain ⟨σ₀, hσ₀, h⟩ := h
      rw [mem_run_append] at h
      obtain ⟨σ₁, hσ₁, hσ'⟩ := h
      obtain ⟨n, c, -, -, -, hext₀, hfr₀⟩ := runStep_extractChild_mem hσ₀
      obtain ⟨hle₁, hrel⟩ := elemVar_rel p fresh h₁
      rw [restVarsList_cons] at hrf hnd
      have hnd' := List.nodup_append.1 hnd
      have hnf₀ : NodeFree fr₁ σ₀ :=
        NodeFree.ofFrame hfr₀ hnf hle₁ (by
          intro w hw; simp only [List.mem_singleton] at hw; subst hw
          exact hrel.lt_of_lt (fun x hx => hlt x (by simp [hx])) hle₁)
      have hrf₀ : RestFree (p.restVars ++ Pat.restVarsList ps) σ₀ := by
        intro r hr
        rw [hfr₀.rest r (by simp), hfr₀.seqRest r (by simp), hfr₀.finRest r (by simp)]
        exact hrf r hr
      obtain ⟨hf₁, hnf₁, hle₂⟩ := structNested (hall p (List.mem_cons_self ..)) v fr₁ σ₀ σ₁
        (fun x hx => by have := hlt x (by simp [hx]); vomega) hnf₀
        (hrf₀.mono (List.subset_append_left _ _)) hnd'.1 (by rw [h₂]; exact hσ₁)
      rw [h₂] at hf₁ hnf₁ hle₂
      simp only at hf₁ hnf₁ hle₂
      have hrf₂ : RestFree (Pat.restVarsList ps) σ₁ := by
        intro r hr
        have hnot : r ∉ p.restVars := fun hr' => hnd'.2.2 r hr' r hr rfl
        rw [hf₁.rest r hnot, hf₁.seqRest r hnot, hf₁.finRest r hnot]
        exact hrf₀ r (List.mem_append_right _ hr)
      obtain ⟨hf₂, hnf₂, hle₃⟩ := ih (fun q hq => hall q (List.mem_cons_of_mem _ hq)) nv (i + 1) fr₂
        σ₁ σ' (fun x hx => by have := hlt x (by simp [hx]); vomega) hnf₁ hrf₂ hnd'.2.1
        (by rw [h₃]; exact hσ')
      rw [h₃] at hf₂ hnf₂ hle₃
      simp only at hf₂ hnf₂ hle₃
      refine ⟨?_, hnf₂, by vomega⟩
      have hf₀ : PlanFrame p.vars [] fresh fr₁ σ σ₀ := by
        refine PlanFrame.ofFrame hfr₀ hext₀ ?_ (by simp) (by simp) (by simp) (by simp)
        intro w hw
        simp at hw; subst hw
        rcases hrel with ⟨x, rfl, rfl⟩ | ⟨-, hlo, hhi⟩
        · exact Or.inl (by simp)
        · exact Or.inr ⟨hlo, hhi⟩
      have := (hf₀.trans hf₁ hle₁ hle₂).trans hf₂ (by vomega) hle₃
      rw [varsList_cons, restVarsList_cons]
      exact this.mono (by intro x hx; simp only [List.mem_append] at hx ⊢; tauto)
        (by intro x hx; simp only [List.mem_append] at hx ⊢; tauto) (le_refl _) (le_refl _)

/-! ## Size facts for the strong induction -/

theorem sizeOf_lt_plain {p : Pat} {args : List Pat} (hp : p ∈ args) (f : Sym) :
    sizeOf p < sizeOf (Pat.plain f args) := by
  have := List.sizeOf_lt_of_mem hp
  simp only [Pat.plain.sizeOf_spec]
  vomega

theorem sizeOf_lt_comm_left (f : Sym) (p q : Pat) : sizeOf p < sizeOf (Pat.comm f p q) := by
  simp only [Pat.comm.sizeOf_spec]; vomega

theorem sizeOf_lt_comm_right (f : Sym) (p q : Pat) : sizeOf q < sizeOf (Pat.comm f p q) := by
  simp only [Pat.comm.sizeOf_spec]; vomega

theorem sizeOf_lt_assoc {p : Pat} {args : List Pat} (hp : p ∈ args) (f : Sym)
    (pre suf : Option Var) : sizeOf p < sizeOf (Pat.assoc f pre args suf) := by
  have := List.sizeOf_lt_of_mem hp
  simp only [Pat.assoc.sizeOf_spec]
  vomega

theorem sizeOf_lt_ac {e : Pat × Mult} {elems : List (Pat × Mult)} (he : e ∈ elems) (f : Sym)
    (rest : Option Var) : sizeOf e.1 < sizeOf (Pat.ac f elems rest) := by
  have := List.sizeOf_lt_of_mem he
  obtain ⟨p, μ⟩ := e
  simp only [Pat.ac.sizeOf_spec, Prod.mk.sizeOf_spec] at this ⊢
  vomega

theorem sizeOf_lt_aci {p : Pat} {elems : List Pat} (hp : p ∈ elems) (f : Sym)
    (rest : Option Var) : sizeOf p < sizeOf (Pat.aci f elems rest) := by
  have := List.sizeOf_lt_of_mem hp
  simp only [Pat.aci.sizeOf_spec]
  vomega

/-! ## Decomposition steps, unpacked -/

theorem runStep_checkEq_mem {G : Graph} {x y : Var} {σ σ' : Binding}
    (h : σ' ∈ runStep G (.checkEq x y) σ) : σ' = σ := by
  simp only [runStep] at h
  split at h
  · split at h
    · simpa using h
    · simp at h
  · simp at h

theorem runStep_decomposeComm_mem {G : Graph} {v x y : Var} {σ σ' : Binding}
    (h : σ' ∈ runStep G (.decomposeComm v x y) σ) :
    ∃ f a b, σ.nodeOf G v = some ⟨f, .spair a b⟩ ∧ σ' ∈ decomposeComm x y a b σ := by
  simp only [runStep] at h
  cases hn : σ.nodeOf G v with
  | none => simp [hn] at h
  | some n =>
      obtain ⟨f, ch⟩ := n
      cases ch with
      | spair a b =>
          simp only [hn] at h
          exact ⟨f, a, b, by first | rfl | exact hn, h⟩
      | tuple cs => simp [hn] at h
      | seq cs => simp [hn] at h
      | mset m => simp [hn] at h
      | set s => simp [hn] at h

theorem runStep_expandA_mem {G : Graph} {v : Var} {pre suf : Option Var} {elems : List Var}
    {σ σ' : Binding} (h : σ' ∈ runStep G (.expandA v pre elems suf) σ) :
    ∃ f cs, σ.nodeOf G v = some ⟨f, .seq cs⟩ ∧ σ' ∈ expandA pre elems suf cs σ := by
  simp only [runStep] at h
  cases hn : σ.nodeOf G v with
  | none => simp [hn] at h
  | some n =>
      obtain ⟨f, ch⟩ := n
      cases ch with
      | seq cs =>
          simp only [hn] at h
          exact ⟨f, cs, by first | rfl | exact hn, h⟩
      | tuple cs => simp [hn] at h
      | spair a b => simp [hn] at h
      | mset m => simp [hn] at h
      | set s => simp [hn] at h

theorem runStep_decomposeAC_mem {G : Graph} {v : Var} {elems : List (Var × Mult)}
    {rest : Option Var} {σ σ' : Binding} (h : σ' ∈ runStep G (.decomposeAC v elems rest) σ) :
    ∃ f m, σ.nodeOf G v = some ⟨f, .mset m⟩ ∧
      σ' ∈ decomposeAC elems rest (Multiset.entries m) σ := by
  simp only [runStep] at h
  cases hn : σ.nodeOf G v with
  | none => simp [hn] at h
  | some n =>
      obtain ⟨f, ch⟩ := n
      cases ch with
      | mset m =>
          simp only [hn] at h
          exact ⟨f, m, by first | rfl | exact hn, h⟩
      | tuple cs => simp [hn] at h
      | spair a b => simp [hn] at h
      | seq cs => simp [hn] at h
      | set s => simp [hn] at h

theorem runStep_decomposeACI_mem {G : Graph} {v : Var} {elems : List Var}
    {rest : Option Var} {σ σ' : Binding} (h : σ' ∈ runStep G (.decomposeACI v elems rest) σ) :
    ∃ f s, σ.nodeOf G v = some ⟨f, .set s⟩ ∧
      σ' ∈ decomposeACI elems rest (s.sort (· ≤ ·)) σ := by
  simp only [runStep] at h
  cases hn : σ.nodeOf G v with
  | none => simp [hn] at h
  | some n =>
      obtain ⟨f, ch⟩ := n
      cases ch with
      | set s =>
          simp only [hn] at h
          exact ⟨f, s, by first | rfl | exact hn, h⟩
      | tuple cs => simp [hn] at h
      | spair a b => simp [hn] at h
      | seq cs => simp [hn] at h
      | mset m => simp [hn] at h

theorem mem_multVars {es : List (Var × Mult)} {k : Var} :
    k ∈ multVars es ↔ ∃ v ∈ es, k ∈ v.2.vars := by
  simp [multVars, List.mem_flatMap]

/-! ## The invariant, by strong induction on the pattern -/

theorem structAt_of_sub {G : Graph} (P : Pat)
    (ih : ∀ p, sizeOf p < sizeOf P → StructAt G p) : StructAt G P := by
  intro cv fresh σ σ' hlt hnf hrf hnd h
  cases P with
  | var x =>
      rw [compileAt_var] at h ⊢
      simp only at h ⊢
      cases cv with
      | none =>
          simp at h; subst h
          exact ⟨PlanFrame.refl _ _ _ _ _, hnf, le_refl _⟩
      | some z =>
          simp only at h
          rw [mem_run_cons] at h
          obtain ⟨σ₁, hσ₁, hσ'⟩ := h
          simp at hσ'; subst hσ'
          have := runStep_checkEq_mem hσ₁; subst this
          exact ⟨PlanFrame.refl _ _ _ _ _, hnf, le_refl _⟩
  | plain f args =>
      rcases h₁ : compilePlainArgs args fresh 0 (fresh + 1) with ⟨s, fr⟩
      rw [compileAt_plain f args cv fresh h₁] at h ⊢
      simp only at h ⊢
      rw [mem_run_cons] at h
      obtain ⟨σ₁, hσ₁, hσ'⟩ := h
      obtain ⟨id, n, hmem, hop, hz, rfl⟩ := mem_joinStep.1 hσ₁
      have hnf₁ : NodeFree (fresh + 1) (joinBind G σ fresh id) :=
        (hnf.mono (by vomega)).joinBind G fresh (by vomega) id
      obtain ⟨hf, hnf', hle⟩ := structArgs args (fun p hp => ih p (sizeOf_lt_plain hp f)) fresh 0
        (fresh + 1) _ σ' (fun x hx => by have := hlt x (by simp [hx]); vomega) hnf₁ (hrf.joinBind G fresh id) hnd (by rw [h₁]; exact hσ')
      rw [h₁] at hf hnf' hle
      simp only at hf hnf' hle
      refine ⟨?_, hnf', by vomega⟩
      have hj : PlanFrame (Pat.varsList args) (Pat.restVarsList args) fresh (fresh + 1) σ
          (joinBind G σ fresh id) :=
        PlanFrame.join (hnf fresh (le_refl _)) (le_refl _) (by vomega)
      have := hj.trans hf (by vomega) hle
      exact this.mono (by simp) (by simp) (le_refl _) (le_refl _)
  | comm f p q =>
      rcases h₁ : elemVar p (fresh + 1) with ⟨vp, fr₁⟩
      rcases h₂ : elemVar q fr₁ with ⟨vq, fr₂⟩
      rcases h₃ : compileNested p vp fr₂ with ⟨sp, fr₃⟩
      rcases h₄ : compileNested q vq fr₃ with ⟨sq, fr₄⟩
      rw [compileAt_comm f p q cv fresh h₁ h₂ h₃ h₄] at h ⊢
      simp only at h ⊢
      rw [List.cons_append, List.cons_append, mem_run_cons] at h
      obtain ⟨σ₁, hσ₁, h⟩ := h
      rw [mem_run_cons] at h
      obtain ⟨σ₂, hσ₂, h⟩ := h
      rw [mem_run_append] at h
      obtain ⟨σ₃, hσ₃, hσ'⟩ := h
      obtain ⟨id, n, hmem, hop, hz, rfl⟩ := mem_joinStep.1 hσ₁
      obtain ⟨g, a, b, hn, hd⟩ := runStep_decomposeComm_mem hσ₂
      obtain ⟨hext₂, -⟩ := decompose_comm_sound' vp vq a b _ σ₂ hd
      have hfr₂ := frame_decomposeComm hd
      obtain ⟨hle₁, hrel₁⟩ := elemVar_rel p (fresh + 1) h₁
      obtain ⟨hle₂, hrel₂⟩ := elemVar_rel q fr₁ h₂
      rw [restVars_comm] at hrf hnd
      have hnd' := List.nodup_append.1 hnd
      have hnf₁ : NodeFree (fresh + 1) (joinBind G σ fresh id) :=
        (hnf.mono (by vomega)).joinBind G fresh (by vomega) id
      have hnf₂ : NodeFree fr₂ σ₂ :=
        NodeFree.ofFrame hfr₂ hnf₁ (by vomega) (by
          intro w hw
          simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hw
          rcases hw with rfl | rfl
          · have := hrel₁.lt_of_lt (fun x hx => by have := hlt x (by simp [hx]); vomega) hle₁; vomega
          · exact hrel₂.lt_of_lt (fun x hx => by have := hlt x (by simp [hx]); vomega) hle₂)
      have hrf₂ : RestFree (p.restVars ++ q.restVars) σ₂ := by
        intro r hr
        rw [hfr₂.rest r (by simp), hfr₂.seqRest r (by simp), hfr₂.finRest r (by simp)]
        exact hrf r hr
      obtain ⟨hf₃, hnf₃, hle₃⟩ := structNested (ih p (sizeOf_lt_comm_left f p q)) vp fr₂ σ₂ σ₃
        (fun x hx => by have := hlt x (by simp [hx]); vomega) hnf₂
        (hrf₂.mono (List.subset_append_left _ _)) hnd'.1 (by rw [h₃]; exact hσ₃)
      rw [h₃] at hf₃ hnf₃ hle₃
      simp only at hf₃ hnf₃ hle₃
      have hrf₃ : RestFree q.restVars σ₃ := by
        intro r hr
        have hnot : r ∉ p.restVars := fun hr' => hnd'.2.2 r hr' r hr rfl
        rw [hf₃.rest r hnot, hf₃.seqRest r hnot, hf₃.finRest r hnot]
        exact hrf₂ r (List.mem_append_right _ hr)
      obtain ⟨hf₄, hnf₄, hle₄⟩ := structNested (ih q (sizeOf_lt_comm_right f p q)) vq fr₃ σ₃ σ'
        (fun x hx => by have := hlt x (by simp [hx]); vomega) hnf₃
        hrf₃ hnd'.2.1 (by rw [h₄]; exact hσ')
      rw [h₄] at hf₄ hnf₄ hle₄
      simp only at hf₄ hnf₄ hle₄
      refine ⟨?_, hnf₄, by vomega⟩
      have hj : PlanFrame (p.vars ++ q.vars) (p.restVars ++ q.restVars) fresh (fresh + 1) σ
          (joinBind G σ fresh id) :=
        PlanFrame.join (hnf fresh (le_refl _)) (le_refl _) (by vomega)
      have hd' : PlanFrame (p.vars ++ q.vars) (p.restVars ++ q.restVars) (fresh + 1) fr₂
          (joinBind G σ fresh id) σ₂ := by
        refine PlanFrame.ofFrame hfr₂ hext₂ ?_ (by simp) (by simp) (by simp) (by simp)
        intro w hw
        simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl
        · rcases hrel₁.mem_or_range with h | h
          · exact Or.inl (List.mem_append_left _ h)
          · exact Or.inr ⟨h.1, by vomega⟩
        · rcases hrel₂.mem_or_range with h | h
          · exact Or.inl (List.mem_append_right _ h)
          · exact Or.inr ⟨by vomega, h.2⟩
      have := ((hj.trans hd' (by vomega) (by vomega)).trans hf₃ (by vomega) hle₃).trans hf₄
        (by vomega) hle₄
      rw [vars_comm, restVars_comm]
      exact this.mono (by intro x hx; simp only [List.mem_append] at hx ⊢; tauto)
        (by intro x hx; simp only [List.mem_append] at hx ⊢; tauto) (le_refl _) (le_refl _)
  | assoc f pre args suf =>
      rcases h₁ : elemVars args (fresh + 1) with ⟨vs, fr₁⟩
      rcases h₂ : compileNestedList args vs fr₁ with ⟨s, fr₂⟩
      rw [compileAt_assoc f pre args suf cv fresh h₁ h₂] at h ⊢
      simp only at h ⊢
      rw [mem_run_cons] at h
      obtain ⟨σ₁, hσ₁, h⟩ := h
      rw [mem_run_cons] at h
      obtain ⟨σ₂, hσ₂, hσ'⟩ := h
      obtain ⟨id, n, hmem, hop, hz, rfl⟩ := mem_joinStep.1 hσ₁
      obtain ⟨g, cs, hn, hd⟩ := runStep_expandA_mem hσ₂
      rw [restVars_assoc] at hrf hnd
      have hpre₀ : ∀ r, pre = some r → (joinBind G σ fresh id).seqRest r = none := by
        intro r hr; subst hr; exact (hrf r (by simp)).2.1
      have hsuf₀ : ∀ r, suf = some r → (joinBind G σ fresh id).seqRest r = none := by
        intro r hr; subst hr; exact (hrf r (by simp)).2.1
      have hdist : ∀ r, pre = some r → suf ≠ some r := by
        intro r hr hs; subst hr; subst hs
        simp at hnd
      obtain ⟨hext₂, -⟩ := expand_a_sound' pre suf vs cs _ σ₂ hpre₀ hsuf₀ hdist hd
      have hfr₂ := frame_expandA hd
      obtain ⟨hle₁, hrel⟩ := elemVars_spec args (fresh + 1) h₁
      have hnf₁ : NodeFree (fresh + 1) (joinBind G σ fresh id) :=
        (hnf.mono (by vomega)).joinBind G fresh (by vomega) id
      have hnf₂ : NodeFree fr₁ σ₂ :=
        NodeFree.ofFrame hfr₂ hnf₁ hle₁
          (forall₂_elemRel_lt hrel (fun x hx => by have := hlt x (by simp [hx]); vomega) hle₁)
      have hnd' := List.nodup_append.1 hnd
      have hrf₂ : RestFree (Pat.restVarsList args) σ₂ := by
        intro r hr
        have hnot : r ∉ pre.toList ++ suf.toList := fun hr' => hnd'.2.2 r hr' r hr rfl
        rw [hfr₂.rest r (by simp), hfr₂.seqRest r hnot, hfr₂.finRest r (by simp)]
        exact hrf r (List.mem_append_right _ hr)
      obtain ⟨hf₃, hnf₃, hle₃⟩ := structNestedList args
        (fun p hp => ih p (sizeOf_lt_assoc hp f pre suf)) vs fr₁ σ₂ σ'
        (fun x hx => by have := hlt x (by simp [hx]); vomega) hnf₂ hrf₂ hnd'.2.1
        (by rw [h₂]; exact hσ')
      rw [h₂] at hf₃ hnf₃ hle₃
      simp only at hf₃ hnf₃ hle₃
      refine ⟨?_, hnf₃, by vomega⟩
      have hj : PlanFrame (pre.toList ++ Pat.varsList args ++ suf.toList)
          (pre.toList ++ suf.toList ++ Pat.restVarsList args) fresh (fresh + 1) σ
          (joinBind G σ fresh id) :=
        PlanFrame.join (hnf fresh (le_refl _)) (le_refl _) (by vomega)
      have hd' : PlanFrame (pre.toList ++ Pat.varsList args ++ suf.toList)
          (pre.toList ++ suf.toList ++ Pat.restVarsList args) (fresh + 1) fr₁
          (joinBind G σ fresh id) σ₂ := by
        refine PlanFrame.ofFrame hfr₂ hext₂ ?_ (by simp) (by simp)
          (List.subset_append_left _ _) (by simp)
        intro w hw
        obtain ⟨p, hp, hpw⟩ := forall₂_exists_left hrel w hw
        rcases hpw.mem_or_range with h | h
        · exact Or.inl (by simp [mem_varsList_of_mem hp h])
        · exact Or.inr h
      have := (hj.trans hd' (by vomega) hle₁).trans hf₃ (by vomega) hle₃
      rw [vars_assoc, restVars_assoc]
      exact this.mono (by intro x hx; simp only [List.mem_append] at hx ⊢; tauto)
        (by intro x hx; simp only [List.mem_append] at hx ⊢; tauto) (le_refl _) (le_refl _)
  | ac f elems rest =>
      rcases h₁ : elemVarsAC elems (fresh + 1) with ⟨vs, fr₁⟩
      rcases h₂ : compileNestedAC elems (vs.map (·.1)) fr₁ with ⟨s, fr₂⟩
      rw [compileAt_ac f elems rest cv fresh h₁ h₂] at h ⊢
      simp only at h ⊢
      rw [mem_run_cons] at h
      obtain ⟨σ₁, hσ₁, h⟩ := h
      rw [mem_run_cons] at h
      obtain ⟨σ₂, hσ₂, hσ'⟩ := h
      obtain ⟨id, n, hmem, hop, hz, rfl⟩ := mem_joinStep.1 hσ₁
      obtain ⟨g, m, hn, hd⟩ := runStep_decomposeAC_mem hσ₂
      rw [restVars_ac] at hrf hnd
      have hfresh : ∀ r ∈ rest, (joinBind G σ fresh id).rest r = none := by
        intro r hr; exact (hrf r (List.mem_append_left _ (Option.mem_toList.2 hr))).1
      obtain ⟨hext₂, -⟩ := decompose_ac_sound' vs rest m _ σ₂ hfresh hd
      have hfr₂ := frame_decomposeAC vs rest _ _ _ hd
      obtain ⟨hle₁, hrel⟩ := elemVarsAC_spec elems (fresh + 1) h₁
      have hnf₁ : NodeFree (fresh + 1) (joinBind G σ fresh id) :=
        (hnf.mono (by vomega)).joinBind G fresh (by vomega) id
      have hnf₂ : NodeFree fr₁ σ₂ :=
        NodeFree.ofFrame hfr₂ hnf₁ hle₁
          (forall₂_elemRel_lt_ac hrel (fun x hx => by have := hlt x (by simp [varsElems_cons, hx]); vomega) hle₁)
      have hnd' := List.nodup_append.1 hnd
      have hrf₂ : RestFree (Pat.restVarsElems elems) σ₂ := by
        intro r hr
        have hnot : r ∉ rest.toList := fun hr' => hnd'.2.2 r hr' r hr rfl
        rw [hfr₂.rest r hnot, hfr₂.seqRest r (by simp), hfr₂.finRest r (by simp)]
        exact hrf r (List.mem_append_right _ hr)
      obtain ⟨hf₃, hnf₃, hle₃⟩ := structNestedAC elems
        (fun e he => ih e.1 (sizeOf_lt_ac he f rest)) (vs.map (·.1)) fr₁ σ₂ σ'
        (fun x hx => by have := hlt x (by simp [hx]); vomega) hnf₂ hrf₂ hnd'.2.1
        (by rw [h₂]; exact hσ')
      rw [h₂] at hf₃ hnf₃ hle₃
      simp only at hf₃ hnf₃ hle₃
      refine ⟨?_, hnf₃, by vomega⟩
      have hj : PlanFrame (Pat.varsElems elems ++ rest.toList)
          (rest.toList ++ Pat.restVarsElems elems) fresh (fresh + 1) σ (joinBind G σ fresh id) :=
        PlanFrame.join (hnf fresh (le_refl _)) (le_refl _) (by vomega)
      have hd' : PlanFrame (Pat.varsElems elems ++ rest.toList)
          (rest.toList ++ Pat.restVarsElems elems) (fresh + 1) fr₁ (joinBind G σ fresh id) σ₂ := by
        refine PlanFrame.ofFrame hfr₂ hext₂ ?_ ?_ (List.subset_append_left _ _) (by simp) (by simp)
        · intro w hw
          rw [List.mem_map] at hw
          obtain ⟨v, hv, rfl⟩ := hw
          obtain ⟨e, he, -, hrel'⟩ := forall₂_exists_left hrel v hv
          rcases hrel'.mem_or_range with h | h
          · exact Or.inl (List.mem_append_left _ (mem_varsElems_of_mem he h))
          · exact Or.inr h
        · intro k hk
          rw [mem_multVars] at hk
          obtain ⟨v, hv, hkv⟩ := hk
          obtain ⟨e, he, heq, -⟩ := forall₂_exists_left hrel v hv
          rw [← heq] at hkv
          exact List.mem_append_left _ (mem_varsElems_of_mult he hkv)
      have := (hj.trans hd' (by vomega) hle₁).trans hf₃ (by vomega) hle₃
      rw [vars_ac, restVars_ac]
      exact this.mono (by intro x hx; simp only [List.mem_append] at hx ⊢; tauto)
        (by intro x hx; simp only [List.mem_append] at hx ⊢; tauto) (le_refl _) (le_refl _)
  | aci f elems rest =>
      rcases h₁ : elemVars elems (fresh + 1) with ⟨vs, fr₁⟩
      rcases h₂ : compileNestedList elems vs fr₁ with ⟨s, fr₂⟩
      rw [compileAt_aci f elems rest cv fresh h₁ h₂] at h ⊢
      simp only at h ⊢
      rw [mem_run_cons] at h
      obtain ⟨σ₁, hσ₁, h⟩ := h
      rw [mem_run_cons] at h
      obtain ⟨σ₂, hσ₂, hσ'⟩ := h
      obtain ⟨id, n, hmem, hop, hz, rfl⟩ := mem_joinStep.1 hσ₁
      obtain ⟨g, st, hn, hd⟩ := runStep_decomposeACI_mem hσ₂
      rw [restVars_aci] at hrf hnd
      have hfresh : ∀ r ∈ rest, (joinBind G σ fresh id).finRest r = none := by
        intro r hr; exact (hrf r (List.mem_append_left _ (Option.mem_toList.2 hr))).2.2
      obtain ⟨hext₂, -⟩ := decompose_aci_sound' vs rest st _ σ₂ hfresh hd
      have hfr₂ := frame_decomposeACI vs rest _ _ _ hd
      obtain ⟨hle₁, hrel⟩ := elemVars_spec elems (fresh + 1) h₁
      have hnf₁ : NodeFree (fresh + 1) (joinBind G σ fresh id) :=
        (hnf.mono (by vomega)).joinBind G fresh (by vomega) id
      have hnf₂ : NodeFree fr₁ σ₂ :=
        NodeFree.ofFrame hfr₂ hnf₁ hle₁
          (forall₂_elemRel_lt hrel (fun x hx => by have := hlt x (by simp [hx]); vomega) hle₁)
      have hnd' := List.nodup_append.1 hnd
      have hrf₂ : RestFree (Pat.restVarsList elems) σ₂ := by
        intro r hr
        have hnot : r ∉ rest.toList := fun hr' => hnd'.2.2 r hr' r hr rfl
        rw [hfr₂.rest r (by simp), hfr₂.seqRest r (by simp), hfr₂.finRest r hnot]
        exact hrf r (List.mem_append_right _ hr)
      obtain ⟨hf₃, hnf₃, hle₃⟩ := structNestedList elems
        (fun p hp => ih p (sizeOf_lt_aci hp f rest)) vs fr₁ σ₂ σ'
        (fun x hx => by have := hlt x (by simp [hx]); vomega) hnf₂ hrf₂ hnd'.2.1
        (by rw [h₂]; exact hσ')
      rw [h₂] at hf₃ hnf₃ hle₃
      simp only at hf₃ hnf₃ hle₃
      refine ⟨?_, hnf₃, by vomega⟩
      have hj : PlanFrame (Pat.varsList elems ++ rest.toList)
          (rest.toList ++ Pat.restVarsList elems) fresh (fresh + 1) σ (joinBind G σ fresh id) :=
        PlanFrame.join (hnf fresh (le_refl _)) (le_refl _) (by vomega)
      have hd' : PlanFrame (Pat.varsList elems ++ rest.toList)
          (rest.toList ++ Pat.restVarsList elems) (fresh + 1) fr₁ (joinBind G σ fresh id) σ₂ := by
        refine PlanFrame.ofFrame hfr₂ hext₂ ?_ (by simp) (by simp) (by simp)
          (List.subset_append_left _ _)
        intro w hw
        obtain ⟨p, hp, hpw⟩ := forall₂_exists_left hrel w hw
        rcases hpw.mem_or_range with h | h
        · exact Or.inl (List.mem_append_left _ (mem_varsList_of_mem hp h))
        · exact Or.inr h
      have := (hj.trans hd' (by vomega) hle₁).trans hf₃ (by vomega) hle₃
      rw [vars_aci, restVars_aci]
      exact this.mono (by intro x hx; simp only [List.mem_append] at hx ⊢; tauto)
        (by intro x hx; simp only [List.mem_append] at hx ⊢; tauto) (le_refl _) (le_refl _)

theorem structAt_all {G : Graph} : ∀ (n : Nat) (P : Pat), sizeOf P = n → StructAt G P := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
      intro P hP
      exact structAt_of_sub P (fun p hp => ih _ (hP ▸ hp) p rfl)

theorem structAt {G : Graph} (P : Pat) : StructAt G P := structAt_all _ P rfl

/-! ## Kinds: the signature the graph and the pattern conform to -/

/-- The kind of an operator: plain of a fixed arity, C, A, AC or ACI. -/
inductive Kind where
  | plain (k : Nat)
  | comm
  | assoc
  | ac
  | aci
  deriving DecidableEq

/-- The kind of a node's children. -/
def Children.kind : Children → Kind
  | .tuple cs => .plain cs.length
  | .spair _ _ => .comm
  | .seq _ => .assoc
  | .mset _ => .ac
  | .set _ => .aci

/-- Every node of the graph has the children shape of its operator's kind. -/
def Graph.Conforms (sig : Sym → Kind) (G : Graph) : Prop :=
  ∀ p ∈ G.nodes, p.2.children.kind = sig p.2.op

/-- Every application in the pattern uses the constructor of its head's
kind, with the declared arity for plain operators. -/
inductive PatWK (sig : Sym → Kind) : Pat → Prop
  | var (x : Var) : PatWK sig (.var x)
  | plain {f : Sym} {args : List Pat} :
      sig f = .plain args.length → (∀ p ∈ args, PatWK sig p) → PatWK sig (.plain f args)
  | comm {f : Sym} {p q : Pat} :
      sig f = .comm → PatWK sig p → PatWK sig q → PatWK sig (.comm f p q)
  | assoc {f : Sym} {pre suf : Option Var} {args : List Pat} :
      sig f = .assoc → (∀ p ∈ args, PatWK sig p) → PatWK sig (.assoc f pre args suf)
  | ac {f : Sym} {elems : List (Pat × Mult)} {rest : Option Var} :
      sig f = .ac → (∀ e ∈ elems, PatWK sig e.1) → PatWK sig (.ac f elems rest)
  | aci {f : Sym} {elems : List Pat} {rest : Option Var} :
      sig f = .aci → (∀ p ∈ elems, PatWK sig p) → PatWK sig (.aci f elems rest)

theorem Children.kind_plain {ch : Children} {k : Nat} (h : ch.kind = .plain k) :
    ∃ cs, ch = .tuple cs ∧ cs.length = k := by
  cases ch with
  | tuple cs => exact ⟨cs, rfl, by simpa [Children.kind] using h⟩
  | spair a b => simp [Children.kind] at h
  | seq cs => simp [Children.kind] at h
  | mset m => simp [Children.kind] at h
  | set s => simp [Children.kind] at h

/-! ## Zip transfer along `Forall₂` -/

theorem zip_transfer {α α' β : Type} {R : α → α' → Prop} :
    ∀ {l₁ : List α} {l₁' : List α'}, List.Forall₂ R l₁ l₁' → ∀ (l₂ : List β),
    ∀ et ∈ l₁.zip l₂, ∃ et' ∈ l₁'.zip l₂, R et.1 et'.1 ∧ et.2 = et'.2 := by
  intro l₁ l₁' h
  induction h with
  | nil => intro l₂ et het; simp at het
  | cons hab hs ih =>
      intro l₂ et het
      cases l₂ with
      | nil => simp at het
      | cons b l₂ =>
          rw [List.zip_cons_cons, List.mem_cons] at het
          rcases het with rfl | het
          · exact ⟨(_, b), by simp, hab, rfl⟩
          · obtain ⟨et', h₁, h₂, h₃⟩ := ih l₂ et het
            exact ⟨et', List.mem_cons_of_mem _ h₁, h₂, h₃⟩

theorem forall₂_cls_of_zip {vs : List Var} {cs : List C} {σ : Binding}
    (hlen : vs.length = cs.length) (h : ∀ ec ∈ vs.zip cs, σ.cls ec.1 = some ec.2) :
    List.Forall₂ (fun v c => σ.cls v = some c) vs cs :=
  List.forall₂_iff_zip.2 ⟨hlen, fun hab => h _ hab⟩

theorem forall₂_cls_of_zip_fst {vs : List (Var × Mult)} {cs : List C} {σ : Binding}
    (hlen : vs.length = cs.length) (h : ∀ et ∈ vs.zip cs, σ.cls et.1.1 = some et.2) :
    List.Forall₂ (fun v c => σ.cls v = some c) (vs.map (·.1)) cs := by
  rw [List.forall₂_map_left_iff]
  exact List.forall₂_iff_zip.2 ⟨hlen, fun hab => h _ hab⟩

theorem ElemRel.var_eq {lo hi : Nat} {p : Pat} {v : Var} (h : ElemRel lo hi p v) :
    ∀ x, p = .var x → v = x := by
  intro x hx
  rcases h with ⟨x', rfl, rfl⟩ | ⟨hh, -, -⟩
  · cases hx; rfl
  · subst hx; simp [Pat.head] at hh

/-! ## Soundness -/

/-- Soundness of a compiled application pattern. -/
def SoundAt (G : Graph) (sig : Sym → Kind) (P : Pat) : Prop :=
  ∀ (cv : Option Var) (fresh : Nat) (σ σ' : Binding),
    G.KeysNodup → G.Conforms sig → PatWK sig P → P.head.isSome = true →
    (∀ x ∈ P.vars, x < fresh) → NodeFree fresh σ → RestFree P.restVars σ → P.restVars.Nodup →
    σ' ∈ run G (compileAt P cv fresh).1 σ →
    ∃ id n, σ'.node fresh = some id ∧ (id, n) ∈ G.nodes ∧ P.head = some n.op ∧
      (∀ z, cv = some z → σ'.cls z = some (G.find id)) ∧ MatchN G P n σ'

theorem soundNested {G : Graph} {sig : Sym → Kind} {p : Pat} (hp : SoundAt G sig p)
    (v : Var) (fresh : Nat) (σ σ' : Binding) (c : C)
    (hk : G.KeysNodup) (hconf : G.Conforms sig) (hwk : PatWK sig p)
    (hlt : ∀ x ∈ p.vars, x < fresh)
    (hnf : NodeFree fresh σ) (hrf : RestFree p.restVars σ) (hnd : p.restVars.Nodup)
    (hv : σ.cls v = some c) (hvar : ∀ x, p = .var x → v = x)
    (h : σ' ∈ run G (compileNested p v fresh).1 σ) : MatchC G p c σ' := by
  cases hh : p.head.isSome
  · cases p with
    | var x =>
        rw [compileNested_var] at h
        simp at h; subst h
        rw [hvar x rfl] at hv
        exact MatchC.var hv
    | plain f args => simp [Pat.head] at hh
    | comm f p q => simp [Pat.head] at hh
    | assoc f pre args suf => simp [Pat.head] at hh
    | ac f elems rest => simp [Pat.head] at hh
    | aci f elems rest => simp [Pat.head] at hh
  · rw [compileNested_app p hh] at h
    obtain ⟨id, n, -, hmem, hhead, hz, hm⟩ := hp (some v) fresh σ σ' hk hconf hwk hh hlt hnf hrf hnd h
    have hext := (structAt p (some v) fresh σ σ' hlt hnf hrf hnd h).1.ext
    have h₁ := hz v rfl
    have h₂ := hext.1 v c hv
    rw [h₁] at h₂
    have hfind : G.find id = c := Option.some.inj h₂
    exact MatchC.app hmem hfind hhead hm

theorem soundNestedList {G : Graph} {sig : Sym → Kind} : ∀ (ps : List Pat),
    (∀ p ∈ ps, SoundAt G sig p) →
    ∀ (vs : List Var) (cs : List C) (fresh : Nat) (σ σ' : Binding),
    G.KeysNodup → G.Conforms sig → (∀ p ∈ ps, PatWK sig p) →
    (∀ x ∈ Pat.varsList ps, x < fresh) →
    NodeFree fresh σ → RestFree (Pat.restVarsList ps) σ → (Pat.restVarsList ps).Nodup →
    List.Forall₂ (fun p v => ∀ x, p = .var x → v = x) ps vs →
    List.Forall₂ (fun v c => σ.cls v = some c) vs cs →
    σ' ∈ run G (compileNestedList ps vs fresh).1 σ →
    List.Forall₂ (fun p c => MatchC G p c σ') ps cs := by
  intro ps
  induction ps with
  | nil =>
      intro _ vs cs fresh σ σ' _ _ _ _ _ _ _ hvs hcs _
      rw [List.forall₂_nil_left_iff] at hvs; subst hvs
      rw [List.forall₂_nil_left_iff] at hcs; subst hcs
      exact List.Forall₂.nil
  | cons p ps ih =>
      intro hall vs cs fresh σ σ' hk hconf hwk hlt hnf hrf hnd hvs hcs h
      rw [List.forall₂_cons_left_iff] at hvs
      obtain ⟨v, vs, hpv, hvs, rfl⟩ := hvs
      rw [List.forall₂_cons_left_iff] at hcs
      obtain ⟨c, cs, hvc, hcs, rfl⟩ := hcs
      rcases h₁ : compileNested p v fresh with ⟨sp, fr₁⟩
      rcases h₂ : compileNestedList ps vs fr₁ with ⟨s, fr₂⟩
      rw [compileNestedList_cons p ps v vs fresh h₁ h₂] at h
      simp only at h
      rw [mem_run_append] at h
      obtain ⟨σ₁, hσ₁, hσ'⟩ := h
      rw [restVarsList_cons] at hrf hnd
      have hnd' := List.nodup_append.1 hnd
      have hp := hall p (List.mem_cons_self ..)
      have hm₁ := soundNested hp v fresh σ σ₁ c hk hconf (hwk p (List.mem_cons_self ..))
        (fun x hx => hlt x (by simp [hx])) hnf
        (hrf.mono (List.subset_append_left _ _)) hnd'.1 hvc hpv (by rw [h₁]; exact hσ₁)
      obtain ⟨hf₁, hnf₁, hle₁⟩ := structNested (structAt p) v fresh σ σ₁
        (fun x hx => hlt x (by simp [hx])) hnf
        (hrf.mono (List.subset_append_left _ _)) hnd'.1 (by rw [h₁]; exact hσ₁)
      rw [h₁] at hf₁ hnf₁ hle₁
      simp only at hf₁ hnf₁ hle₁
      have hrf₂ : RestFree (Pat.restVarsList ps) σ₁ := by
        intro r hr
        have hnot : r ∉ p.restVars := fun hr' => hnd'.2.2 r hr' r hr rfl
        rw [hf₁.rest r hnot, hf₁.seqRest r hnot, hf₁.finRest r hnot]
        exact hrf r (List.mem_append_right _ hr)
      have hcs₁ : List.Forall₂ (fun v c => σ₁.cls v = some c) vs cs :=
        hcs.imp (fun v c hvc => hf₁.ext.1 v c hvc)
      have hrest := ih (fun q hq => hall q (List.mem_cons_of_mem _ hq)) vs cs fr₁ σ₁ σ' hk hconf
        (fun q hq => hwk q (List.mem_cons_of_mem _ hq))
        (fun x hx => by have := hlt x (by simp [hx]); vomega) hnf₁ hrf₂ hnd'.2.1 hvs hcs₁
        (by rw [h₂]; exact hσ')
      obtain ⟨hf₂, -, -⟩ := structNestedList ps (fun q _ => structAt q) vs fr₁ σ₁ σ'
        (fun x hx => by have := hlt x (by simp [hx]); vomega) hnf₁ hrf₂
        hnd'.2.1 (by rw [h₂]; exact hσ')
      rw [h₂] at hf₂
      simp only at hf₂
      exact List.Forall₂.cons (hm₁.mono hf₂.ext) hrest

theorem soundNestedAC {G : Graph} {sig : Sym → Kind} : ∀ (es : List (Pat × Mult)),
    (∀ e ∈ es, SoundAt G sig e.1) →
    ∀ (vs : List Var) (cs : List C) (fresh : Nat) (σ σ' : Binding),
    G.KeysNodup → G.Conforms sig → (∀ e ∈ es, PatWK sig e.1) →
    (∀ x ∈ Pat.varsElems es, x < fresh) →
    NodeFree fresh σ → RestFree (Pat.restVarsElems es) σ → (Pat.restVarsElems es).Nodup →
    List.Forall₂ (fun e v => ∀ x, e.1 = .var x → v = x) es vs →
    List.Forall₂ (fun v c => σ.cls v = some c) vs cs →
    σ' ∈ run G (compileNestedAC es vs fresh).1 σ →
    List.Forall₂ (fun e c => MatchC G e.1 c σ') es cs := by
  intro es
  induction es with
  | nil =>
      intro _ vs cs fresh σ σ' _ _ _ _ _ _ _ hvs hcs _
      rw [List.forall₂_nil_left_iff] at hvs; subst hvs
      rw [List.forall₂_nil_left_iff] at hcs; subst hcs
      exact List.Forall₂.nil
  | cons e es ih =>
      intro hall vs cs fresh σ σ' hk hconf hwk hlt hnf hrf hnd hvs hcs h
      obtain ⟨p, μ⟩ := e
      rw [List.forall₂_cons_left_iff] at hvs
      obtain ⟨v, vs, hpv, hvs, rfl⟩ := hvs
      rw [List.forall₂_cons_left_iff] at hcs
      obtain ⟨c, cs, hvc, hcs, rfl⟩ := hcs
      rcases h₁ : compileNested p v fresh with ⟨sp, fr₁⟩
      rcases h₂ : compileNestedAC es vs fr₁ with ⟨s, fr₂⟩
      rw [compileNestedAC_cons p μ es v vs fresh h₁ h₂] at h
      simp only at h
      rw [mem_run_append] at h
      obtain ⟨σ₁, hσ₁, hσ'⟩ := h
      rw [restVarsElems_cons] at hrf hnd
      have hnd' := List.nodup_append.1 hnd
      have hp := hall (p, μ) (List.mem_cons_self ..)
      have hm₁ := soundNested hp v fresh σ σ₁ c hk hconf (hwk (p, μ) (List.mem_cons_self ..))
        (fun x hx => hlt x (by simp [varsElems_cons, hx])) hnf
        (hrf.mono (List.subset_append_left _ _)) hnd'.1 hvc hpv (by rw [h₁]; exact hσ₁)
      obtain ⟨hf₁, hnf₁, hle₁⟩ := structNested (structAt p) v fresh σ σ₁
        (fun x hx => hlt x (by simp [varsElems_cons, hx])) hnf
        (hrf.mono (List.subset_append_left _ _)) hnd'.1 (by rw [h₁]; exact hσ₁)
      rw [h₁] at hf₁ hnf₁ hle₁
      simp only at hf₁ hnf₁ hle₁
      have hrf₂ : RestFree (Pat.restVarsElems es) σ₁ := by
        intro r hr
        have hnot : r ∉ p.restVars := fun hr' => hnd'.2.2 r hr' r hr rfl
        rw [hf₁.rest r hnot, hf₁.seqRest r hnot, hf₁.finRest r hnot]
        exact hrf r (List.mem_append_right _ hr)
      have hcs₁ : List.Forall₂ (fun v c => σ₁.cls v = some c) vs cs :=
        hcs.imp (fun v c hvc => hf₁.ext.1 v c hvc)
      have hrest := ih (fun q hq => hall q (List.mem_cons_of_mem _ hq)) vs cs fr₁ σ₁ σ' hk hconf
        (fun q hq => hwk q (List.mem_cons_of_mem _ hq))
        (fun x hx => by have := hlt x (by simp [varsElems_cons, hx]); vomega) hnf₁ hrf₂ hnd'.2.1 hvs hcs₁
        (by rw [h₂]; exact hσ')
      obtain ⟨hf₂, -, -⟩ := structNestedAC es (fun q _ => structAt q.1) vs fr₁ σ₁ σ'
        (fun x hx => by have := hlt x (by simp [varsElems_cons, hx]); vomega) hnf₁ hrf₂
        hnd'.2.1 (by rw [h₂]; exact hσ')
      rw [h₂] at hf₂
      simp only at hf₂
      exact List.Forall₂.cons (hm₁.mono hf₂.ext) hrest

theorem soundArgs {G : Graph} {sig : Sym → Kind} : ∀ (args : List Pat),
    (∀ p ∈ args, SoundAt G sig p) →
    ∀ (nv : Var) (i fresh : Nat) (σ σ' : Binding) (id : NodeId) (n : Node) (cs : List C),
    G.KeysNodup → G.Conforms sig → (∀ p ∈ args, PatWK sig p) →
    (∀ x ∈ Pat.varsList args, x < fresh) →
    NodeFree fresh σ → RestFree (Pat.restVarsList args) σ → (Pat.restVarsList args).Nodup →
    σ.node nv = some id → (id, n) ∈ G.nodes → n.children = .tuple cs →
    i + args.length = cs.length →
    σ' ∈ run G (compilePlainArgs args nv i fresh).1 σ →
    List.Forall₂ (fun p c => MatchC G p c σ') args (cs.drop i) := by
  intro args
  induction args with
  | nil =>
      intro _ nv i fresh σ σ' id n cs _ _ _ _ _ _ _ _ _ _ hlen _
      simp at hlen
      rw [List.drop_eq_nil_of_le (by omega)]
      exact List.Forall₂.nil
  | cons p ps ih =>
      intro hall nv i fresh σ σ' id n cs hk hconf hwk hlt hnf hrf hnd hnv hmem hch hlen h
      rcases h₁ : elemVar p fresh with ⟨v, fr₁⟩
      rcases h₂ : compileNested p v fr₁ with ⟨sp, fr₂⟩
      rcases h₃ : compilePlainArgs ps nv (i + 1) fr₂ with ⟨s, fr₃⟩
      rw [compilePlainArgs_cons p ps nv i fresh h₁ h₂ h₃] at h
      simp only at h
      rw [List.cons_append, mem_run_cons] at h
      obtain ⟨σ₀, hσ₀, h⟩ := h
      rw [mem_run_append] at h
      obtain ⟨σ₁, hσ₁, hσ'⟩ := h
      obtain ⟨n', c, hn', hc, hcls₀, hext₀, hfr₀⟩ := runStep_extractChild_mem hσ₀
      have hn : σ.nodeOf G nv = some n := nodeOf_of_node hk hnv hmem
      rw [hn] at hn'
      obtain rfl := Option.some.inj hn'
      rw [hch] at hc
      simp only [Children.childAt] at hc
      have hi : i < cs.length := by simp at hlen; omega
      rw [List.getElem?_eq_getElem hi] at hc
      obtain rfl := Option.some.inj hc
      obtain ⟨hle₁, hrel⟩ := elemVar_rel p fresh h₁
      rw [restVarsList_cons] at hrf hnd
      have hnd' := List.nodup_append.1 hnd
      have hnf₀ : NodeFree fr₁ σ₀ :=
        NodeFree.ofFrame hfr₀ hnf hle₁ (by
          intro w hw; simp only [List.mem_singleton] at hw; subst hw
          exact hrel.lt_of_lt (fun x hx => hlt x (by simp [hx])) hle₁)
      have hrf₀ : RestFree (p.restVars ++ Pat.restVarsList ps) σ₀ := by
        intro r hr
        rw [hfr₀.rest r (by simp), hfr₀.seqRest r (by simp), hfr₀.finRest r (by simp)]
        exact hrf r hr
      have hm₁ := soundNested (hall p (List.mem_cons_self ..)) v fr₁ σ₀ σ₁ _ hk hconf
        (hwk p (List.mem_cons_self ..)) (fun x hx => by have := hlt x (by simp [hx]); vomega) hnf₀
        (hrf₀.mono (List.subset_append_left _ _)) hnd'.1 hcls₀
        hrel.var_eq (by rw [h₂]; exact hσ₁)
      obtain ⟨hf₁, hnf₁, hle₂⟩ := structNested (structAt p) v fr₁ σ₀ σ₁
        (fun x hx => by have := hlt x (by simp [hx]); vomega) hnf₀
        (hrf₀.mono (List.subset_append_left _ _)) hnd'.1 (by rw [h₂]; exact hσ₁)
      rw [h₂] at hf₁ hnf₁ hle₂
      simp only at hf₁ hnf₁ hle₂
      have hrf₂ : RestFree (Pat.restVarsList ps) σ₁ := by
        intro r hr
        have hnot : r ∉ p.restVars := fun hr' => hnd'.2.2 r hr' r hr rfl
        rw [hf₁.rest r hnot, hf₁.seqRest r hnot, hf₁.finRest r hnot]
        exact hrf₀ r (List.mem_append_right _ hr)
      have hnv₁ : σ₁.node nv = some id := hf₁.ext.2.1 nv id (by rw [hfr₀.node]; exact hnv)
      have hrest := ih (fun q hq => hall q (List.mem_cons_of_mem _ hq)) nv (i + 1) fr₂ σ₁ σ' id n cs
        hk hconf (fun q hq => hwk q (List.mem_cons_of_mem _ hq))
        (fun x hx => by have := hlt x (by simp [hx]); vomega) hnf₁ hrf₂ hnd'.2.1 hnv₁ hmem hch
        (by simp at hlen ⊢; omega) (by rw [h₃]; exact hσ')
      obtain ⟨hf₂, -, -⟩ := structArgs ps (fun q _ => structAt q) nv (i + 1) fr₂ σ₁ σ'
        (fun x hx => by have := hlt x (by simp [hx]); vomega) hnf₁ hrf₂
        hnd'.2.1 (by rw [h₃]; exact hσ')
      rw [h₃] at hf₂
      simp only at hf₂
      rw [List.drop_eq_getElem_cons hi]
      exact List.Forall₂.cons (hm₁.mono hf₂.ext) hrest

theorem soundAt_of_sub {G : Graph} {sig : Sym → Kind} (P : Pat)
    (ih : ∀ p, sizeOf p < sizeOf P → SoundAt G sig p) : SoundAt G sig P := by
  intro cv fresh σ σ' hk hconf hwk hh hlt hnf hrf hnd h
  have hst := structAt P cv fresh σ σ' hlt hnf hrf hnd h
  cases P with
  | var x => simp [Pat.head] at hh
  | plain f args =>
      rcases h₁ : compilePlainArgs args fresh 0 (fresh + 1) with ⟨s, fr⟩
      rw [compileAt_plain f args cv fresh h₁] at h hst
      simp only at h hst
      rw [mem_run_cons] at h
      obtain ⟨σ₁, hσ₁, hσ'⟩ := h
      obtain ⟨id, n, hmem, hop, hz, rfl⟩ := mem_joinStep.1 hσ₁
      cases hwk with
      | plain hsig hwk' =>
      have hkind := hconf (id, n) hmem
      simp only at hkind
      rw [hop, hsig] at hkind
      obtain ⟨cs, hch, hlen⟩ := Children.kind_plain hkind
      have hnf₁ : NodeFree (fresh + 1) (joinBind G σ fresh id) :=
        (hnf.mono (by vomega)).joinBind G fresh (by vomega) id
      have hall := soundArgs args (fun p hp => ih p (sizeOf_lt_plain hp f)) fresh 0 (fresh + 1)
        _ σ' id n cs hk hconf hwk' (fun x hx => by have := hlt x (by simp [hx]); vomega) hnf₁ (hrf.joinBind G fresh id) hnd (joinBind_node_self _ _ _ _) hmem hch
        (by omega) (by rw [h₁]; exact hσ')
      simp only [List.drop_zero] at hall
      obtain ⟨hf, -, -⟩ := structArgs args (fun q _ => structAt q) fresh 0 (fresh + 1) _ σ'
        (fun x hx => by have := hlt x (by simp [hx]); vomega) hnf₁
        (hrf.joinBind G fresh id) hnd (by rw [h₁]; exact hσ')
      rw [h₁] at hf
      simp only at hf
      refine ⟨id, n, hf.ext.2.1 fresh id (joinBind_node_self _ _ _ _), hmem, by simp [Pat.head, hop],
        fun z hz' => hst.1.ext.1 z _ (hz z hz'), ?_⟩
      obtain ⟨f', ch⟩ := n
      simp only at hop hch
      subst hop; subst hch
      exact MatchN.plain hlen.symm (fun pc hpc => (List.forall₂_iff_zip.1 hall).2 hpc)
  | comm f p q =>
      rcases h₁ : elemVar p (fresh + 1) with ⟨vp, fr₁⟩
      rcases h₂ : elemVar q fr₁ with ⟨vq, fr₂⟩
      rcases h₃ : compileNested p vp fr₂ with ⟨sp, fr₃⟩
      rcases h₄ : compileNested q vq fr₃ with ⟨sq, fr₄⟩
      rw [compileAt_comm f p q cv fresh h₁ h₂ h₃ h₄] at h hst
      simp only at h hst
      rw [List.cons_append, List.cons_append, mem_run_cons] at h
      obtain ⟨σ₁, hσ₁, h⟩ := h
      rw [mem_run_cons] at h
      obtain ⟨σ₂, hσ₂, h⟩ := h
      rw [mem_run_append] at h
      obtain ⟨σ₃, hσ₃, hσ'⟩ := h
      obtain ⟨id, n, hmem, hop, hz, rfl⟩ := mem_joinStep.1 hσ₁
      obtain ⟨g, a, b, hn, hd⟩ := runStep_decomposeComm_mem hσ₂
      rw [nodeOf_of_node hk (joinBind_node_self _ _ _ _) hmem] at hn
      obtain rfl := Option.some.inj hn
      simp only at hop
      obtain rfl := hop.symm
      obtain ⟨hext₂, hab⟩ := decompose_comm_sound' vp vq a b _ σ₂ hd
      have hfr₂ := frame_decomposeComm hd
      obtain ⟨hle₁, hrel₁⟩ := elemVar_rel p (fresh + 1) h₁
      obtain ⟨hle₂, hrel₂⟩ := elemVar_rel q fr₁ h₂
      cases hwk with
      | comm _ hwp hwq =>
      rw [restVars_comm] at hrf hnd
      have hnd' := List.nodup_append.1 hnd
      have hnf₁ : NodeFree (fresh + 1) (joinBind G σ fresh id) :=
        (hnf.mono (by vomega)).joinBind G fresh (by vomega) id
      have hnf₂ : NodeFree fr₂ σ₂ :=
        NodeFree.ofFrame hfr₂ hnf₁ (by vomega) (by
          intro w hw
          simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hw
          rcases hw with rfl | rfl
          · have := hrel₁.lt_of_lt (fun x hx => by have := hlt x (by simp [hx]); vomega) hle₁; vomega
          · exact hrel₂.lt_of_lt (fun x hx => by have := hlt x (by simp [hx]); vomega) hle₂)
      have hrf₂ : RestFree (p.restVars ++ q.restVars) σ₂ := by
        intro r hr
        rw [hfr₂.rest r (by simp), hfr₂.seqRest r (by simp), hfr₂.finRest r (by simp)]
        exact hrf r hr
      obtain ⟨hf₃, hnf₃, hle₃⟩ := structNested (structAt p) vp fr₂ σ₂ σ₃
        (fun x hx => by have := hlt x (by simp [hx]); vomega) hnf₂
        (hrf₂.mono (List.subset_append_left _ _)) hnd'.1 (by rw [h₃]; exact hσ₃)
      rw [h₃] at hf₃ hnf₃ hle₃
      simp only at hf₃ hnf₃ hle₃
      have hrf₃ : RestFree q.restVars σ₃ := by
        intro r hr
        have hnot : r ∉ p.restVars := fun hr' => hnd'.2.2 r hr' r hr rfl
        rw [hf₃.rest r hnot, hf₃.seqRest r hnot, hf₃.finRest r hnot]
        exact hrf₂ r (List.mem_append_right _ hr)
      obtain ⟨hf₄, -, -⟩ := structNested (structAt q) vq fr₃ σ₃ σ'
        (fun x hx => by have := hlt x (by simp [hx]); vomega) hnf₃ hrf₃ hnd'.2.1
        (by rw [h₄]; exact hσ')
      rw [h₄] at hf₄
      simp only at hf₄
      refine ⟨id, ⟨f, .spair a b⟩, hf₄.ext.2.1 fresh id (hf₃.ext.2.1 fresh id
        (by rw [hfr₂.node]; exact joinBind_node_self _ _ _ _)), hmem,
        by simp [Pat.head], fun z hz' => hst.1.ext.1 z _ (hz z hz'), ?_⟩
      rcases hab with ⟨hpa, hqb⟩ | ⟨hpb, hqa⟩
      · have hmp := soundNested (ih p (sizeOf_lt_comm_left f p q)) vp fr₂ σ₂ σ₃ a hk hconf hwp
          (fun x hx => by have := hlt x (by simp [hx]); vomega) hnf₂
          (hrf₂.mono (List.subset_append_left _ _)) hnd'.1 hpa hrel₁.var_eq (by rw [h₃]; exact hσ₃)
        have hmq := soundNested (ih q (sizeOf_lt_comm_right f p q)) vq fr₃ σ₃ σ' b hk hconf hwq
          (fun x hx => by have := hlt x (by simp [hx]); vomega) hnf₃
          hrf₃ hnd'.2.1 (hf₃.ext.1 vq b hqb) hrel₂.var_eq (by rw [h₄]; exact hσ')
        exact MatchN.comm₁ (hmp.mono hf₄.ext) hmq
      · have hmp := soundNested (ih p (sizeOf_lt_comm_left f p q)) vp fr₂ σ₂ σ₃ b hk hconf hwp
          (fun x hx => by have := hlt x (by simp [hx]); vomega) hnf₂
          (hrf₂.mono (List.subset_append_left _ _)) hnd'.1 hpb hrel₁.var_eq (by rw [h₃]; exact hσ₃)
        have hmq := soundNested (ih q (sizeOf_lt_comm_right f p q)) vq fr₃ σ₃ σ' a hk hconf hwq
          (fun x hx => by have := hlt x (by simp [hx]); vomega) hnf₃
          hrf₃ hnd'.2.1 (hf₃.ext.1 vq a hqa) hrel₂.var_eq (by rw [h₄]; exact hσ')
        exact MatchN.comm₂ (hmp.mono hf₄.ext) hmq
  | assoc f pre args suf =>
      rcases h₁ : elemVars args (fresh + 1) with ⟨vs, fr₁⟩
      rcases h₂ : compileNestedList args vs fr₁ with ⟨s, fr₂⟩
      rw [compileAt_assoc f pre args suf cv fresh h₁ h₂] at h hst
      simp only at h hst
      rw [mem_run_cons] at h
      obtain ⟨σ₁, hσ₁, h⟩ := h
      rw [mem_run_cons] at h
      obtain ⟨σ₂, hσ₂, hσ'⟩ := h
      obtain ⟨id, n, hmem, hop, hz, rfl⟩ := mem_joinStep.1 hσ₁
      obtain ⟨g, cs, hn, hd⟩ := runStep_expandA_mem hσ₂
      rw [nodeOf_of_node hk (joinBind_node_self _ _ _ _) hmem] at hn
      obtain rfl := Option.some.inj hn
      simp only at hop
      obtain rfl := hop.symm
      cases hwk with
      | assoc _ hwk' =>
      rw [restVars_assoc] at hrf hnd
      have hpre₀ : ∀ r, pre = some r → (joinBind G σ fresh id).seqRest r = none := by
        intro r hr; subst hr; exact (hrf r (by simp)).2.1
      have hsuf₀ : ∀ r, suf = some r → (joinBind G σ fresh id).seqRest r = none := by
        intro r hr; subst hr; exact (hrf r (by simp)).2.1
      have hdist : ∀ r, pre = some r → suf ≠ some r := by
        intro r hr hs; subst hr; subst hs
        simp at hnd
      obtain ⟨hext₂, u, mid, w, hcs, hlen, hpre, hsuf, hcls⟩ :=
        expand_a_sound' pre suf vs cs _ σ₂ hpre₀ hsuf₀ hdist hd
      have hfr₂ := frame_expandA hd
      obtain ⟨hle₁, hrel⟩ := elemVars_spec args (fresh + 1) h₁
      have hnf₁ : NodeFree (fresh + 1) (joinBind G σ fresh id) :=
        (hnf.mono (by vomega)).joinBind G fresh (by vomega) id
      have hnf₂ : NodeFree fr₁ σ₂ :=
        NodeFree.ofFrame hfr₂ hnf₁ hle₁
          (forall₂_elemRel_lt hrel (fun x hx => by have := hlt x (by simp [hx]); vomega) hle₁)
      have hnd' := List.nodup_append.1 hnd
      have hrf₂ : RestFree (Pat.restVarsList args) σ₂ := by
        intro r hr
        have hnot : r ∉ pre.toList ++ suf.toList := fun hr' => hnd'.2.2 r hr' r hr rfl
        rw [hfr₂.rest r (by simp), hfr₂.seqRest r hnot, hfr₂.finRest r (by simp)]
        exact hrf r (List.mem_append_right _ hr)
      have hvs : List.Forall₂ (fun p v => ∀ x, p = .var x → v = x) args vs :=
        hrel.imp (fun _ _ h => h.var_eq)
      have hmid : List.Forall₂ (fun v c => σ₂.cls v = some c) vs mid :=
        forall₂_cls_of_zip hlen.symm hcls
      have hall := soundNestedList args (fun p hp => ih p (sizeOf_lt_assoc hp f pre suf)) vs mid fr₁
        σ₂ σ' hk hconf hwk' (fun x hx => by have := hlt x (by simp [hx]); vomega) hnf₂ hrf₂ hnd'.2.1 hvs hmid (by rw [h₂]; exact hσ')
      obtain ⟨hf₃, -, -⟩ := structNestedList args (fun q _ => structAt q) vs fr₁ σ₂ σ' (fun x hx => by have := hlt x (by simp [hx]); vomega) hnf₂ hrf₂
        hnd'.2.1 (by rw [h₂]; exact hσ')
      rw [h₂] at hf₃
      simp only at hf₃
      refine ⟨id, ⟨f, .seq cs⟩, hf₃.ext.2.1 fresh id
        (by rw [hfr₂.node]; exact joinBind_node_self _ _ _ _), hmem,
        by simp [Pat.head], fun z hz' => hst.1.ext.1 z _ (hz z hz'), ?_⟩
      subst hcs
      exact MatchN.assoc hall.length_eq (hpre.mono hf₃.ext) (hsuf.mono hf₃.ext)
        (fun pc hpc => (List.forall₂_iff_zip.1 hall).2 hpc)
  | ac f elems rest =>
      rcases h₁ : elemVarsAC elems (fresh + 1) with ⟨vs, fr₁⟩
      rcases h₂ : compileNestedAC elems (vs.map (·.1)) fr₁ with ⟨s, fr₂⟩
      rw [compileAt_ac f elems rest cv fresh h₁ h₂] at h hst
      simp only at h hst
      rw [mem_run_cons] at h
      obtain ⟨σ₁, hσ₁, h⟩ := h
      rw [mem_run_cons] at h
      obtain ⟨σ₂, hσ₂, hσ'⟩ := h
      obtain ⟨id, n, hmem, hop, hz, rfl⟩ := mem_joinStep.1 hσ₁
      obtain ⟨g, m, hn, hd⟩ := runStep_decomposeAC_mem hσ₂
      rw [nodeOf_of_node hk (joinBind_node_self _ _ _ _) hmem] at hn
      obtain rfl := Option.some.inj hn
      simp only at hop
      obtain rfl := hop.symm
      cases hwk with
      | ac _ hwk' =>
      rw [restVars_ac] at hrf hnd
      have hfresh : ∀ r ∈ rest, (joinBind G σ fresh id).rest r = none := by
        intro r hr; exact (hrf r (List.mem_append_left _ (Option.mem_toList.2 hr))).1
      obtain ⟨hext₂, taken, hnd_t, hlen_t, hmem_t, hcls, hmult, hrest⟩ :=
        decompose_ac_sound' vs rest m _ σ₂ hfresh hd
      have hfr₂ := frame_decomposeAC vs rest _ _ _ hd
      obtain ⟨hle₁, hrel⟩ := elemVarsAC_spec elems (fresh + 1) h₁
      have hnf₁ : NodeFree (fresh + 1) (joinBind G σ fresh id) :=
        (hnf.mono (by vomega)).joinBind G fresh (by vomega) id
      have hnf₂ : NodeFree fr₁ σ₂ :=
        NodeFree.ofFrame hfr₂ hnf₁ hle₁
          (forall₂_elemRel_lt_ac hrel (fun x hx => by have := hlt x (by simp [varsElems_cons, hx]); vomega) hle₁)
      have hnd' := List.nodup_append.1 hnd
      have hrf₂ : RestFree (Pat.restVarsElems elems) σ₂ := by
        intro r hr
        have hnot : r ∉ rest.toList := fun hr' => hnd'.2.2 r hr' r hr rfl
        rw [hfr₂.rest r hnot, hfr₂.seqRest r (by simp), hfr₂.finRest r (by simp)]
        exact hrf r (List.mem_append_right _ hr)
      have hvs : List.Forall₂ (fun e v => ∀ x, e.1 = .var x → v = x) elems (vs.map (·.1)) := by
        rw [List.forall₂_map_right_iff]
        exact hrel.imp (fun _ _ h => h.2.var_eq)
      have htk : List.Forall₂ (fun v c => σ₂.cls v = some c) (vs.map (·.1)) taken :=
        forall₂_cls_of_zip_fst hlen_t hcls
      have hall := soundNestedAC elems (fun e he => ih e.1 (sizeOf_lt_ac he f rest)) (vs.map (·.1))
        taken fr₁ σ₂ σ' hk hconf hwk' (fun x hx => by have := hlt x (by simp [hx]); vomega) hnf₂ hrf₂ hnd'.2.1 hvs htk (by rw [h₂]; exact hσ')
      obtain ⟨hf₃, -, -⟩ := structNestedAC elems (fun q _ => structAt q.1) (vs.map (·.1)) fr₁ σ₂ σ'
        (fun x hx => by have := hlt x (by simp [hx]); vomega) hnf₂ hrf₂ hnd'.2.1 (by rw [h₂]; exact hσ')
      rw [h₂] at hf₃
      simp only at hf₃
      refine ⟨id, ⟨f, .mset m⟩, hf₃.ext.2.1 fresh id
        (by rw [hfr₂.node]; exact joinBind_node_self _ _ _ _), hmem,
        by simp [Pat.head], fun z hz' => hst.1.ext.1 z _ (hz z hz'), ?_⟩
      refine MatchN.ac hnd_t hall.length_eq hmem_t (fun et het => (List.forall₂_iff_zip.1 hall).2 het)
        ?_ (hrest.mono hf₃.ext)
      intro et het
      obtain ⟨et', het', ⟨hμ, -⟩, h2⟩ := zip_transfer hrel taken et het
      rw [hμ, h2]
      exact (hmult et' het').mono hf₃.ext
  | aci f elems rest =>
      rcases h₁ : elemVars elems (fresh + 1) with ⟨vs, fr₁⟩
      rcases h₂ : compileNestedList elems vs fr₁ with ⟨s, fr₂⟩
      rw [compileAt_aci f elems rest cv fresh h₁ h₂] at h hst
      simp only at h hst
      rw [mem_run_cons] at h
      obtain ⟨σ₁, hσ₁, h⟩ := h
      rw [mem_run_cons] at h
      obtain ⟨σ₂, hσ₂, hσ'⟩ := h
      obtain ⟨id, n, hmem, hop, hz, rfl⟩ := mem_joinStep.1 hσ₁
      obtain ⟨g, st, hn, hd⟩ := runStep_decomposeACI_mem hσ₂
      rw [nodeOf_of_node hk (joinBind_node_self _ _ _ _) hmem] at hn
      obtain rfl := Option.some.inj hn
      simp only at hop
      obtain rfl := hop.symm
      cases hwk with
      | aci _ hwk' =>
      rw [restVars_aci] at hrf hnd
      have hfresh : ∀ r ∈ rest, (joinBind G σ fresh id).finRest r = none := by
        intro r hr; exact (hrf r (List.mem_append_left _ (Option.mem_toList.2 hr))).2.2
      obtain ⟨hext₂, taken, hnd_t, hlen_t, hmem_t, hcls, hrest⟩ :=
        decompose_aci_sound' vs rest st _ σ₂ hfresh hd
      have hfr₂ := frame_decomposeACI vs rest _ _ _ hd
      obtain ⟨hle₁, hrel⟩ := elemVars_spec elems (fresh + 1) h₁
      have hnf₁ : NodeFree (fresh + 1) (joinBind G σ fresh id) :=
        (hnf.mono (by vomega)).joinBind G fresh (by vomega) id
      have hnf₂ : NodeFree fr₁ σ₂ :=
        NodeFree.ofFrame hfr₂ hnf₁ hle₁
          (forall₂_elemRel_lt hrel (fun x hx => by have := hlt x (by simp [hx]); vomega) hle₁)
      have hnd' := List.nodup_append.1 hnd
      have hrf₂ : RestFree (Pat.restVarsList elems) σ₂ := by
        intro r hr
        have hnot : r ∉ rest.toList := fun hr' => hnd'.2.2 r hr' r hr rfl
        rw [hfr₂.rest r (by simp), hfr₂.seqRest r (by simp), hfr₂.finRest r hnot]
        exact hrf r (List.mem_append_right _ hr)
      have hvs : List.Forall₂ (fun p v => ∀ x, p = .var x → v = x) elems vs :=
        hrel.imp (fun _ _ h => h.var_eq)
      have htk : List.Forall₂ (fun v c => σ₂.cls v = some c) vs taken :=
        forall₂_cls_of_zip hlen_t hcls
      have hall := soundNestedList elems (fun p hp => ih p (sizeOf_lt_aci hp f rest)) vs taken fr₁
        σ₂ σ' hk hconf hwk' (fun x hx => by have := hlt x (by simp [hx]); vomega) hnf₂ hrf₂ hnd'.2.1 hvs htk (by rw [h₂]; exact hσ')
      obtain ⟨hf₃, -, -⟩ := structNestedList elems (fun q _ => structAt q) vs fr₁ σ₂ σ' (fun x hx => by have := hlt x (by simp [hx]); vomega) hnf₂ hrf₂
        hnd'.2.1 (by rw [h₂]; exact hσ')
      rw [h₂] at hf₃
      simp only at hf₃
      refine ⟨id, ⟨f, .set st⟩, hf₃.ext.2.1 fresh id
        (by rw [hfr₂.node]; exact joinBind_node_self _ _ _ _), hmem,
        by simp [Pat.head], fun z hz' => hst.1.ext.1 z _ (hz z hz'), ?_⟩
      exact MatchN.aci hnd_t hall.length_eq hmem_t (fun et het => (List.forall₂_iff_zip.1 hall).2 het)
        (hrest.mono hf₃.ext)

theorem soundAt_all {G : Graph} {sig : Sym → Kind} :
    ∀ (n : Nat) (P : Pat), sizeOf P = n → SoundAt G sig P := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
      intro P hP
      exact soundAt_of_sub P (fun p hp => ih _ (hP ▸ hp) p rfl)

theorem soundAt {G : Graph} {sig : Sym → Kind} (P : Pat) : SoundAt G sig P :=
  soundAt_all _ P rfl

/-- Lemma 11 (`interp_sound`), corrected. The statement in `Lemmas.lean` is
false: with `G.nodes = [(0, ⟨f, .mset ∅⟩)]`, `P = .plain f []` and
`fresh = 1`, the plan is one join on `by_op f`, which accepts node `0`, but
`MatchN G (.plain f []) ⟨f, .mset ∅⟩ σ` has no derivation (the `plain`
constructor needs a `tuple`). The engine never meets this case because
`by_op` is per operator with a fixed shape; the model states that as a
kind signature `sig` the graph (`hconf`) and the pattern (`hwk`) conform
to. The second added hypothesis, `hnd`, asks the rest variables of `P` to
be distinct: the interpreter overwrites a rest variable bound twice, so a
pattern with the same rest variable in two sub-patterns can emit a binding
whose first rest is not checked (the stubs `decompose_ac_sound`,
`decompose_aci_sound` and `expand_a_sound` are false for the same reason;
the primed forms carry the "rest unbound" hypothesis). -/
theorem interp_sound' (G : Graph) (sig : Sym → Kind) (P : Pat) (fresh : Nat) (σ : Binding)
    (hkeys : G.KeysNodup) (hconf : G.Conforms sig) (hwk : PatWK sig P)
    (hP : P.head.isSome = true) (hf : ∀ x ∈ P.vars, x < fresh) (hnd : P.restVars.Nodup)
    (h : σ ∈ run G (compile P fresh) Binding.empty) :
    ∃ id n, σ.node fresh = some id ∧ (id, n) ∈ G.nodes ∧ MatchN G P n σ := by
  obtain ⟨id, n, hid, hmem, -, -, hm⟩ := soundAt (sig := sig) P none fresh Binding.empty σ hkeys
    hconf hwk hP hf (fun _ _ => ⟨rfl, rfl⟩) (fun _ _ => ⟨rfl, rfl, rfl⟩) hnd h
  exact ⟨id, n, hid, hmem, hm⟩

/-! ## Completeness -/

/-- The run binding `σr` against the witness `σ`: below `b` (the pattern
variables) every entry of `σr` agrees with `σ`; from `fresh` upward the
class and node variables of `σr` are unbound. -/
structure CInv (b fresh : Nat) (σr σ : Binding) : Prop where
  cls : ∀ x c, x < b → σr.cls x = some c → σ.cls x = some c
  mult : ∀ k m, k < b → σr.mult k = some m → σ.mult k = some m
  rest : ∀ r m, r < b → σr.rest r = some m → σ.rest r = some m
  seqRest : ∀ r u, r < b → σr.seqRest r = some u → σ.seqRest r = some u
  finRest : ∀ r s, r < b → σr.finRest r = some s → σ.finRest r = some s
  clsFree : ∀ v, fresh ≤ v → σr.cls v = none
  nodeFree : ∀ v, fresh ≤ v → σr.node v = none

theorem CInv.mono {b fresh fresh' : Nat} {σr σ : Binding} (h : CInv b fresh σr σ)
    (hle : fresh ≤ fresh') : CInv b fresh' σr σ where
  cls := h.cls
  mult := h.mult
  rest := h.rest
  seqRest := h.seqRest
  finRest := h.finRest
  clsFree v hv := h.clsFree v (by vomega)
  nodeFree v hv := h.nodeFree v (by vomega)

theorem CInv.joinBind {b fresh : Nat} {σr σ : Binding} (h : CInv b fresh σr σ) (G : Graph)
    (hb : b ≤ fresh) (id : NodeId) : CInv b (fresh + 1) (joinBind G σr fresh id) σ where
  cls x c hx hc := by
    rw [joinBind_cls_of_ne _ _ _ _ _ (by vomega)] at hc
    exact h.cls x c hx hc
  mult := h.mult
  rest := h.rest
  seqRest := h.seqRest
  finRest := h.finRest
  clsFree v hv := by
    rw [joinBind_cls_of_ne _ _ _ _ _ (by vomega)]
    exact h.clsFree v (by vomega)
  nodeFree v hv := by
    rw [joinBind_node_of_ne _ _ _ _ _ (by vomega)]
    exact h.nodeFree v (by vomega)

/-- The run binding is `NodeFree` (node and class) from `fresh` upward. -/
theorem CInv.free {b fresh : Nat} {σr σ : Binding} (h : CInv b fresh σr σ) : NodeFree fresh σr :=
  fun v hv => ⟨h.nodeFree v hv, h.clsFree v hv⟩

theorem CInv.empty (b fresh : Nat) (σ : Binding) : CInv b fresh Binding.empty σ where
  cls _ _ _ h := by cases h
  mult _ _ _ h := by cases h
  rest _ _ _ h := by cases h
  seqRest _ _ _ h := by cases h
  finRest _ _ _ h := by cases h
  clsFree _ _ := rfl
  nodeFree _ _ := rfl

/-- The binding handed to the component completeness lemmas: `σ1` with the
pattern variables (below `b`) taken from the witness `σ` and the fresh
element variables taken from `pairs`. -/
def star (b : Nat) (σ1 σ : Binding) (pairs : List (Var × C)) : Binding where
  cls x := if x < b then (match σ.cls x with | some c => some c | none => σ1.cls x)
    else match pairs.find? (fun p => p.1 = x) with | some p => some p.2 | none => σ1.cls x
  node := σ1.node
  mult k := if k < b then (match σ.mult k with | some m => some m | none => σ1.mult k)
    else σ1.mult k
  rest r := if r < b then (match σ.rest r with | some m => some m | none => σ1.rest r)
    else σ1.rest r
  seqRest r := if r < b then (match σ.seqRest r with | some u => some u | none => σ1.seqRest r)
    else σ1.seqRest r
  finRest r := if r < b then (match σ.finRest r with | some s => some s | none => σ1.finRest r)
    else σ1.finRest r

theorem star_cls_lt {b : Nat} {σ1 σ : Binding} {pairs : List (Var × C)} {x : Var} {c : C}
    (hx : x < b) (h : σ.cls x = some c) : (star b σ1 σ pairs).cls x = some c := by
  simp [star, hx, h]

theorem star_mult_lt {b : Nat} {σ1 σ : Binding} {pairs : List (Var × C)} {k : Var} {m : Nat}
    (hk : k < b) (h : σ.mult k = some m) : (star b σ1 σ pairs).mult k = some m := by
  simp [star, hk, h]

theorem star_rest_lt {b : Nat} {σ1 σ : Binding} {pairs : List (Var × C)} {r : Var}
    {m : Multiset C} (hr : r < b) (h : σ.rest r = some m) :
    (star b σ1 σ pairs).rest r = some m := by
  simp [star, hr, h]

theorem star_seqRest_lt {b : Nat} {σ1 σ : Binding} {pairs : List (Var × C)} {r : Var}
    {u : List C} (hr : r < b) (h : σ.seqRest r = some u) :
    (star b σ1 σ pairs).seqRest r = some u := by
  simp [star, hr, h]

theorem star_finRest_lt {b : Nat} {σ1 σ : Binding} {pairs : List (Var × C)} {r : Var}
    {s : Finset C} (hr : r < b) (h : σ.finRest r = some s) :
    (star b σ1 σ pairs).finRest r = some s := by
  simp [star, hr, h]

/-- `find?` on a key list whose entries for `x` all carry `c`. -/
theorem find?_key {pairs : List (Var × C)} {x : Var} {c : C} (hmem : (x, c) ∈ pairs)
    (huniq : ∀ p ∈ pairs, p.1 = x → p.2 = c) :
    ∃ p, pairs.find? (fun p => p.1 = x) = some p ∧ p.2 = c := by
  have hsome : (pairs.find? (fun p => p.1 = x)).isSome := by
    rw [List.find?_isSome]
    exact ⟨(x, c), hmem, by simp⟩
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.1 hsome
  refine ⟨p, hp, huniq p (List.mem_of_find?_eq_some hp) ?_⟩
  have := List.find?_some hp
  simpa using this

theorem star_cls_ge {b : Nat} {σ1 σ : Binding} {pairs : List (Var × C)} {x : Var} {c : C}
    (hx : ¬ x < b) (hmem : (x, c) ∈ pairs) (huniq : ∀ p ∈ pairs, p.1 = x → p.2 = c) :
    (star b σ1 σ pairs).cls x = some c := by
  obtain ⟨p, hp, hpc⟩ := find?_key hmem huniq
  simp [star, hx, hp, hpc]

/-- `Extends σ1 (star b σ1 σ pairs)` when `σ1` agrees with `σ` below `b`
and every key of `pairs` is a pattern variable or a fresh one. -/
theorem extends_star {b fresh : Nat} {σ1 σ : Binding} {pairs : List (Var × C)}
    (hinv : CInv b fresh σ1 σ) (hkeys : ∀ p ∈ pairs, p.1 < b ∨ fresh ≤ p.1) :
    Extends σ1 (star b σ1 σ pairs) := by
  refine ⟨?_, fun _ _ h => h, ?_, ?_, ?_, ?_⟩
  · intro x c hx
    by_cases hxb : x < b
    · exact star_cls_lt hxb (hinv.cls x c hxb hx)
    · simp only [star, hxb, ite_false]
      cases hfind : pairs.find? (fun p => p.1 = x) with
      | none => exact hx
      | some p =>
          have hp := List.find?_some hfind
          simp only [decide_eq_true_eq] at hp
          rcases hkeys p (List.mem_of_find?_eq_some hfind) with h | h
          · vomega
          · rw [hinv.clsFree x (by rw [← hp]; exact h)] at hx
            cases hx
  · intro k m hk
    by_cases hkb : k < b
    · exact star_mult_lt hkb (hinv.mult k m hkb hk)
    · simp [star, hkb, hk]
  · intro r m hr
    by_cases hrb : r < b
    · exact star_rest_lt hrb (hinv.rest r m hrb hr)
    · simp [star, hrb, hr]
  · intro r u hr
    by_cases hrb : r < b
    · exact star_seqRest_lt hrb (hinv.seqRest r u hrb hr)
    · simp [star, hrb, hr]
  · intro r s hr
    by_cases hrb : r < b
    · exact star_finRest_lt hrb (hinv.finRest r s hrb hr)
    · simp [star, hrb, hr]

/-- A binding below `star b σ1 σ pairs` with the node map of `σ1` satisfies
the invariant at any `fr ≥ fresh` above the keys of `pairs`. -/
theorem cinv_of_extends_star {b fresh fr : Nat} {σ1 σ σ'' : Binding} {pairs : List (Var × C)}
    (hinv : CInv b fresh σ1 σ) (hb : b ≤ fresh) (hle : fresh ≤ fr)
    (hkeys : ∀ p ∈ pairs, p.1 < b ∨ p.1 < fr)
    (hext : Extends σ'' (star b σ1 σ pairs)) (hnode : σ''.node = σ1.node) :
    CInv b fr σ'' σ where
  cls x c hx h := by
    have h' := hext.1 x c h
    simp only [star, hx, ite_true] at h'
    cases hσ : σ.cls x with
    | some c' => simp only [hσ] at h'; exact h'
    | none => simp only [hσ] at h'; exact absurd (hinv.cls x c hx h') (by rw [hσ]; simp)
  mult k m hk h := by
    have h' := hext.2.2.1 k m h
    simp only [star, hk, ite_true] at h'
    cases hσ : σ.mult k with
    | some m' => simp only [hσ] at h'; exact h'
    | none => simp only [hσ] at h'; exact absurd (hinv.mult k m hk h') (by rw [hσ]; simp)
  rest r m hr h := by
    have h' := hext.2.2.2.1 r m h
    simp only [star, hr, ite_true] at h'
    cases hσ : σ.rest r with
    | some m' => simp only [hσ] at h'; exact h'
    | none => simp only [hσ] at h'; exact absurd (hinv.rest r m hr h') (by rw [hσ]; simp)
  seqRest r u hr h := by
    have h' := hext.2.2.2.2.1 r u h
    simp only [star, hr, ite_true] at h'
    cases hσ : σ.seqRest r with
    | some u' => simp only [hσ] at h'; exact h'
    | none => simp only [hσ] at h'; exact absurd (hinv.seqRest r u hr h') (by rw [hσ]; simp)
  finRest r s hr h := by
    have h' := hext.2.2.2.2.2 r s h
    simp only [star, hr, ite_true] at h'
    cases hσ : σ.finRest r with
    | some s' => simp only [hσ] at h'; exact h'
    | none => simp only [hσ] at h'; exact absurd (hinv.finRest r s hr h') (by rw [hσ]; simp)
  clsFree v hv := by
    cases hc : σ''.cls v with
    | none => rfl
    | some c =>
        exfalso
        have h' := hext.1 v c hc
        have hvb : ¬ v < b := by vomega
        simp only [star, hvb, ite_false] at h'
        cases hfind : pairs.find? (fun p => p.1 = v) with
        | none =>
            rw [hfind] at h'
            simp only at h'
            rw [hinv.clsFree v (by vomega)] at h'
            cases h'
        | some p =>
            have hp := List.find?_some hfind
            simp only [decide_eq_true_eq] at hp
            rcases hkeys p (List.mem_of_find?_eq_some hfind) with h | h <;> vomega
  nodeFree v hv := by rw [hnode]; exact hinv.nodeFree v (by vomega)

/-! ### Distinctness of fresh element variables -/

theorem elemVars_distinct : ∀ (ps : List Pat) (fresh : Nat) {vs : List Var} {fr : Nat},
    elemVars ps fresh = (vs, fr) → (∀ x ∈ Pat.varsList ps, x < fresh) →
    List.Pairwise (fun v w => fresh ≤ v → fresh ≤ w → v < w) vs := by
  intro ps
  induction ps with
  | nil =>
      intro fresh vs fr h _
      simp [elemVars] at h
      obtain ⟨rfl, -⟩ := h
      exact List.Pairwise.nil
  | cons p ps ih =>
      intro fresh vs fr h hlt
      simp only [elemVars] at h
      rcases h₁ : elemVar p fresh with ⟨v, fr₁⟩
      rcases h₂ : elemVars ps fr₁ with ⟨vs', fr₂⟩
      rw [h₁, h₂] at h
      simp at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨hle₁, hrel₁⟩ := elemVar_rel p fresh h₁
      obtain ⟨hle₂, hrel₂⟩ := elemVars_spec ps fr₁ h₂
      rw [varsList_cons] at hlt
      have hlt' : ∀ x ∈ Pat.varsList ps, x < fr₁ := fun x hx => by
        have := hlt x (List.mem_append_right _ hx); vomega
      have htail := ih fr₁ h₂ hlt'
      -- a variable of `vs'` at or above `fresh` is an application variable, hence at or above `fr₁`
      have hup : ∀ w ∈ vs', fresh ≤ w → fr₁ ≤ w := by
        intro w hw hfw
        obtain ⟨q, hq, hqw⟩ := forall₂_exists_left hrel₂ w hw
        rcases hqw with ⟨x, rfl, rfl⟩ | ⟨-, hlo, -⟩
        · have := hlt w (List.mem_append_right _ (mem_varsList_of_mem hq (by simp)))
          vomega
        · exact hlo
      refine List.Pairwise.cons ?_ (htail.imp_of_mem ?_)
      · intro w hw hfv hfw
        have hfr := hup w hw hfw
        rcases hrel₁ with ⟨x, rfl, rfl⟩ | ⟨-, -, hhi⟩
        · have := hlt v (List.mem_append_left _ (by simp)); vomega
        · vomega
      · intro v' w' hv' hw' hr hfv hfw
        exact hr (hup v' hv' hfv) (hup w' hw' hfw)

theorem elemVarsAC_distinct : ∀ (es : List (Pat × Mult)) (fresh : Nat) {vs : List (Var × Mult)}
    {fr : Nat}, elemVarsAC es fresh = (vs, fr) → (∀ x ∈ Pat.varsElems es, x < fresh) →
    List.Pairwise (fun v w => fresh ≤ v → fresh ≤ w → v < w) (vs.map (·.1)) := by
  intro es
  induction es with
  | nil =>
      intro fresh vs fr h _
      simp [elemVarsAC] at h
      obtain ⟨rfl, -⟩ := h
      exact List.Pairwise.nil
  | cons e es ih =>
      intro fresh vs fr h hlt
      obtain ⟨p, μ⟩ := e
      simp only [elemVarsAC] at h
      rcases h₁ : elemVar p fresh with ⟨v, fr₁⟩
      rcases h₂ : elemVarsAC es fr₁ with ⟨vs', fr₂⟩
      rw [h₁, h₂] at h
      simp at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨hle₁, hrel₁⟩ := elemVar_rel p fresh h₁
      obtain ⟨hle₂, hrel₂⟩ := elemVarsAC_spec es fr₁ h₂
      rw [varsElems_cons] at hlt
      have hlt' : ∀ x ∈ Pat.varsElems es, x < fr₁ := fun x hx => by
        have := hlt x (List.mem_append_right _ hx); vomega
      have htail := ih fr₁ h₂ hlt'
      have hup : ∀ w ∈ vs'.map (·.1), fresh ≤ w → fr₁ ≤ w := by
        intro w hw hfw
        rw [List.mem_map] at hw
        obtain ⟨v', hv', rfl⟩ := hw
        obtain ⟨q, hq, -, hqw⟩ := forall₂_exists_left hrel₂ v' hv'
        rcases hqw with ⟨x, hqx, hvx⟩ | ⟨-, hlo, -⟩
        · rw [hvx] at hfw ⊢
          have := hlt x (List.mem_append_right _ (mem_varsElems_of_mem hq (by rw [hqx]; simp)))
          vomega
        · exact hlo
      rw [List.map_cons]
      refine List.Pairwise.cons ?_ (htail.imp_of_mem ?_)
      · intro w hw hfv hfw
        have hfr := hup w hw hfw
        rcases hrel₁ with ⟨x, rfl, rfl⟩ | ⟨-, -, hhi⟩
        · have := hlt v (List.mem_append_left _ (List.mem_append_left _ (by simp))); vomega
        · vomega
      · intro v' w' hv' hw' hr hfv hfw
        exact hr (hup v' hv' hfv) (hup w' hw' hfw)

/-- Two pairs of a zip with the same key at or above `lo` carry the same
value, when the keys above `lo` are pairwise distinct. -/
theorem zip_key_unique : ∀ {keys : List Var} {vals : List C} {lo : Nat},
    List.Pairwise (fun v w => lo ≤ v → lo ≤ w → v < w) keys →
    ∀ {x : Var} {c c' : C}, lo ≤ x → (x, c) ∈ keys.zip vals → (x, c') ∈ keys.zip vals → c = c' := by
  intro keys
  induction keys with
  | nil => intro vals lo _ x c c' _ h; simp at h
  | cons k ks ih =>
      intro vals lo hp x c c' hx h₁ h₂
      cases vals with
      | nil => simp at h₁
      | cons v vs =>
          rw [List.pairwise_cons] at hp
          rw [List.zip_cons_cons, List.mem_cons] at h₁ h₂
          rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
          · rw [Prod.mk.injEq] at h₁ h₂; rw [h₁.2, h₂.2]
          · rw [Prod.mk.injEq] at h₁
            obtain ⟨rfl, rfl⟩ := h₁
            have := hp.1 x (List.of_mem_zip h₂).1 hx hx
            vomega
          · rw [Prod.mk.injEq] at h₂
            obtain ⟨rfl, rfl⟩ := h₂
            have := hp.1 x (List.of_mem_zip h₁).1 hx hx
            vomega
          · exact ih hp.2 hx h₁ h₂

theorem forall₂_cls_unique {f : Var → Option C} : ∀ {ks : List Var} {l₁ l₂ : List C},
    List.Forall₂ (fun v c => f v = some c) ks l₁ →
    List.Forall₂ (fun v c => f v = some c) ks l₂ → l₁ = l₂ := by
  intro ks
  induction ks with
  | nil =>
      intro l₁ l₂ h₁ h₂
      rw [List.forall₂_nil_left_iff] at h₁ h₂
      rw [h₁, h₂]
  | cons k ks ih =>
      intro l₁ l₂ h₁ h₂
      rw [List.forall₂_cons_left_iff] at h₁ h₂
      obtain ⟨c₁, l₁, hc₁, h₁, rfl⟩ := h₁
      obtain ⟨c₂, l₂, hc₂, h₂, rfl⟩ := h₂
      rw [hc₁] at hc₂
      rw [Option.some.inj hc₂, ih h₁ h₂]

/-- A var-element key below `b` is bound in `σ` to its child (from the
match), and the remaining keys lie in a fresh range. -/
theorem star_cls_keys {b fresh fr : Nat} {σ1 σ : Binding} {keys : List Var} {cs : List C}
    (_hb : b ≤ fresh)
    (hrange : ∀ v ∈ keys, v < b ∨ (fresh ≤ v ∧ v < fr))
    (hvar : ∀ v c, (v, c) ∈ keys.zip cs → v < b → σ.cls v = some c)
    (hdist : List.Pairwise (fun v w => fresh ≤ v → fresh ≤ w → v < w) keys) :
    ∀ vc ∈ keys.zip cs, (star b σ1 σ (keys.zip cs)).cls vc.1 = some vc.2 := by
  intro vc hvc
  obtain ⟨v, c⟩ := vc
  by_cases hvb : v < b
  · exact star_cls_lt hvb (hvar v c hvc hvb)
  · have hv : fresh ≤ v := by
      rcases hrange v (List.of_mem_zip hvc).1 with h | h
      · vomega
      · exact h.1
    refine star_cls_ge hvb hvc ?_
    intro p hp hpv
    obtain ⟨v', c'⟩ := p
    simp only at hpv
    subst hpv
    exact zip_key_unique hdist hv hp hvc

/-! ### The completeness statements -/

def CompleteAt (G : Graph) (P : Pat) : Prop :=
  ∀ (cv : Option Var) (fresh b : Nat) (σr σ : Binding) (id : NodeId) (n : Node),
    G.KeysNodup → P.head.isSome = true → (∀ x ∈ P.vars, x < b) → b ≤ fresh →
    RestFree P.restVars σr → P.restVars.Nodup → CInv b fresh σr σ →
    (id, n) ∈ G.nodes → MatchN G P n σ →
    (∀ z, cv = some z → σr.cls z = some (G.find id)) →
    ∃ σ' ∈ run G (compileAt P cv fresh).1 σr,
      σ'.node fresh = some id ∧ CInv b (compileAt P cv fresh).2 σ' σ

theorem completeNested {G : Graph} {p : Pat} (hp : CompleteAt G p) (v : Var) (fresh b : Nat)
    (σr σ : Binding) (c : C)
    (hk : G.KeysNodup) (hlt : ∀ x ∈ p.vars, x < b) (hb : b ≤ fresh)
    (hrf : RestFree p.restVars σr) (hnd : p.restVars.Nodup) (hinv : CInv b fresh σr σ)
    (hm : MatchC G p c σ) (hv : σr.cls v = some c) :
    ∃ σ' ∈ run G (compileNested p v fresh).1 σr, CInv b (compileNested p v fresh).2 σ' σ := by
  cases hh : p.head.isSome
  · cases p with
    | var x =>
        rw [compileNested_var]
        exact ⟨σr, by simp, hinv⟩
    | plain f args => simp [Pat.head] at hh
    | comm f p q => simp [Pat.head] at hh
    | assoc f pre args suf => simp [Pat.head] at hh
    | ac f elems rest => simp [Pat.head] at hh
    | aci f elems rest => simp [Pat.head] at hh
  · rw [compileNested_app p hh]
    cases hm with
    | var hx => simp [Pat.head] at hh
    | app hmem hfind hhead hmn =>
        obtain ⟨σ', hσ', -, hinv'⟩ := hp (some v) fresh b σr σ _ _ hk hh hlt hb hrf hnd hinv hmem hmn
          (fun z hz => by cases hz; rw [hfind]; exact hv)
        exact ⟨σ', hσ', hinv'⟩

theorem completeNestedList {G : Graph} : ∀ (ps : List Pat), (∀ p ∈ ps, CompleteAt G p) →
    ∀ (vs : List Var) (cs : List C) (fresh b : Nat) (σr σ : Binding),
    G.KeysNodup → (∀ x ∈ Pat.varsList ps, x < b) → b ≤ fresh →
    RestFree (Pat.restVarsList ps) σr → (Pat.restVarsList ps).Nodup → CInv b fresh σr σ →
    List.Forall₂ (fun p c => MatchC G p c σ) ps cs →
    List.Forall₂ (fun v c => σr.cls v = some c) vs cs →
    ∃ σ' ∈ run G (compileNestedList ps vs fresh).1 σr,
      CInv b (compileNestedList ps vs fresh).2 σ' σ := by
  intro ps
  induction ps with
  | nil =>
      intro _ vs cs fresh b σr σ _ _ _ _ _ hinv _ _
      rw [compileNestedList_nil_left]
      exact ⟨σr, by simp, hinv⟩
  | cons p ps ih =>
      intro hall vs cs fresh b σr σ hk hlt hb hrf hnd hinv hm hcs
      rw [List.forall₂_cons_left_iff] at hm
      obtain ⟨c, cs, hpc, hm, rfl⟩ := hm
      cases vs with
      | nil => rw [List.forall₂_nil_left_iff] at hcs; cases hcs
      | cons v vs =>
      rw [List.forall₂_cons_left_iff] at hcs
      obtain ⟨c', cs', hvc, hcs, hcc⟩ := hcs
      rw [List.cons.injEq] at hcc
      obtain ⟨rfl, rfl⟩ := hcc
      rcases h₁ : compileNested p v fresh with ⟨sp, fr₁⟩
      rcases h₂ : compileNestedList ps vs fr₁ with ⟨s, fr₂⟩
      rw [compileNestedList_cons p ps v vs fresh h₁ h₂]
      simp only
      rw [varsList_cons] at hlt
      rw [restVarsList_cons] at hrf hnd
      have hnd' := List.nodup_append.1 hnd
      obtain ⟨σ₁, hσ₁, hinv₁⟩ := completeNested (hall p (List.mem_cons_self ..)) v fresh b σr σ c hk
        (fun x hx => hlt x (List.mem_append_left _ hx)) hb (hrf.mono (List.subset_append_left _ _))
        hnd'.1 hinv hpc hvc
      rw [h₁] at hσ₁ hinv₁
      simp only at hσ₁ hinv₁
      obtain ⟨hf₁, -, hle₁⟩ := structNested (structAt p) v fresh σr σ₁
        (fun x hx => by have := hlt x (by simp [hx]); vomega) hinv.free
        (hrf.mono (List.subset_append_left _ _)) hnd'.1 (by rw [h₁]; exact hσ₁)
      rw [h₁] at hf₁ hle₁
      simp only at hf₁ hle₁
      have hrf₂ : RestFree (Pat.restVarsList ps) σ₁ := by
        intro r hr
        have hnot : r ∉ p.restVars := fun hr' => hnd'.2.2 r hr' r hr rfl
        rw [hf₁.rest r hnot, hf₁.seqRest r hnot, hf₁.finRest r hnot]
        exact hrf r (List.mem_append_right _ hr)
      obtain ⟨σ', hσ', hinv'⟩ := ih (fun q hq => hall q (List.mem_cons_of_mem _ hq)) vs cs fr₁ b σ₁ σ
        hk (fun x hx => hlt x (List.mem_append_right _ hx)) (by vomega) hrf₂ hnd'.2.1 hinv₁ hm
        (hcs.imp (fun v c h => hf₁.ext.1 v c h))
      rw [h₂] at hσ' hinv'
      simp only at hσ' hinv'
      exact ⟨σ', mem_run_append.2 ⟨σ₁, hσ₁, hσ'⟩, hinv'⟩

theorem completeNestedAC {G : Graph} : ∀ (es : List (Pat × Mult)),
    (∀ e ∈ es, CompleteAt G e.1) →
    ∀ (vs : List Var) (cs : List C) (fresh b : Nat) (σr σ : Binding),
    G.KeysNodup → (∀ x ∈ Pat.varsElems es, x < b) → b ≤ fresh →
    RestFree (Pat.restVarsElems es) σr → (Pat.restVarsElems es).Nodup → CInv b fresh σr σ →
    List.Forall₂ (fun e c => MatchC G e.1 c σ) es cs →
    List.Forall₂ (fun v c => σr.cls v = some c) vs cs →
    ∃ σ' ∈ run G (compileNestedAC es vs fresh).1 σr,
      CInv b (compileNestedAC es vs fresh).2 σ' σ := by
  intro es
  induction es with
  | nil =>
      intro _ vs cs fresh b σr σ _ _ _ _ _ hinv _ _
      rw [compileNestedAC_nil_left]
      exact ⟨σr, by simp, hinv⟩
  | cons e es ih =>
      intro hall vs cs fresh b σr σ hk hlt hb hrf hnd hinv hm hcs
      obtain ⟨p, μ⟩ := e
      rw [List.forall₂_cons_left_iff] at hm
      obtain ⟨c, cs, hpc, hm, rfl⟩ := hm
      cases vs with
      | nil => rw [List.forall₂_nil_left_iff] at hcs; cases hcs
      | cons v vs =>
      rw [List.forall₂_cons_left_iff] at hcs
      obtain ⟨c', cs', hvc, hcs, hcc⟩ := hcs
      rw [List.cons.injEq] at hcc
      obtain ⟨rfl, rfl⟩ := hcc
      rcases h₁ : compileNested p v fresh with ⟨sp, fr₁⟩
      rcases h₂ : compileNestedAC es vs fr₁ with ⟨s, fr₂⟩
      rw [compileNestedAC_cons p μ es v vs fresh h₁ h₂]
      simp only
      rw [varsElems_cons] at hlt
      rw [restVarsElems_cons] at hrf hnd
      have hnd' := List.nodup_append.1 hnd
      obtain ⟨σ₁, hσ₁, hinv₁⟩ := completeNested (hall (p, μ) (List.mem_cons_self ..)) v fresh b σr σ
        c hk (fun x hx => hlt x (List.mem_append_left _ (List.mem_append_left _ hx))) hb
        (hrf.mono (List.subset_append_left _ _)) hnd'.1 hinv hpc hvc
      rw [h₁] at hσ₁ hinv₁
      simp only at hσ₁ hinv₁
      obtain ⟨hf₁, -, hle₁⟩ := structNested (structAt p) v fresh σr σ₁
        (fun x hx => by have := hlt x (by simp [hx]); vomega) hinv.free
        (hrf.mono (List.subset_append_left _ _)) hnd'.1 (by rw [h₁]; exact hσ₁)
      rw [h₁] at hf₁ hle₁
      simp only at hf₁ hle₁
      have hrf₂ : RestFree (Pat.restVarsElems es) σ₁ := by
        intro r hr
        have hnot : r ∉ p.restVars := fun hr' => hnd'.2.2 r hr' r hr rfl
        rw [hf₁.rest r hnot, hf₁.seqRest r hnot, hf₁.finRest r hnot]
        exact hrf r (List.mem_append_right _ hr)
      obtain ⟨σ', hσ', hinv'⟩ := ih (fun q hq => hall q (List.mem_cons_of_mem _ hq)) vs cs fr₁ b σ₁ σ
        hk (fun x hx => hlt x (List.mem_append_right _ hx)) (by vomega) hrf₂ hnd'.2.1 hinv₁ hm
        (hcs.imp (fun v c h => hf₁.ext.1 v c h))
      rw [h₂] at hσ' hinv'
      simp only at hσ' hinv'
      exact ⟨σ', mem_run_append.2 ⟨σ₁, hσ₁, hσ'⟩, hinv'⟩

theorem completeArgs {G : Graph} : ∀ (args : List Pat), (∀ p ∈ args, CompleteAt G p) →
    ∀ (nv : Var) (i fresh b : Nat) (σr σ : Binding) (id : NodeId) (n : Node) (cs : List C),
    G.KeysNodup → (∀ x ∈ Pat.varsList args, x < b) → b ≤ fresh →
    RestFree (Pat.restVarsList args) σr → (Pat.restVarsList args).Nodup → CInv b fresh σr σ →
    σr.node nv = some id → (id, n) ∈ G.nodes → n.children = .tuple cs →
    i + args.length = cs.length →
    List.Forall₂ (fun p c => MatchC G p c σ) args (cs.drop i) →
    ∃ σ' ∈ run G (compilePlainArgs args nv i fresh).1 σr,
      CInv b (compilePlainArgs args nv i fresh).2 σ' σ := by
  intro args
  induction args with
  | nil =>
      intro _ nv i fresh b σr σ id n cs _ _ _ _ _ hinv _ _ _ _ _
      rw [compilePlainArgs_nil]
      exact ⟨σr, by simp, hinv⟩
  | cons p ps ih =>
      intro hall nv i fresh b σr σ id n cs hk hlt hb hrf hnd hinv hnv hmem hch hlen hm
      have hi : i < cs.length := by simp at hlen; vomega
      rw [List.drop_eq_getElem_cons hi, List.forall₂_cons_left_iff] at hm
      obtain ⟨c, cs', hpc, hm, hcc⟩ := hm
      rw [List.cons.injEq] at hcc
      obtain ⟨rfl, rfl⟩ := hcc
      rcases h₁ : elemVar p fresh with ⟨v, fr₁⟩
      rcases h₂ : compileNested p v fr₁ with ⟨sp, fr₂⟩
      rcases h₃ : compilePlainArgs ps nv (i + 1) fr₂ with ⟨s, fr₃⟩
      rw [compilePlainArgs_cons p ps nv i fresh h₁ h₂ h₃]
      simp only
      rw [varsList_cons] at hlt
      rw [restVarsList_cons] at hrf hnd
      have hnd' := List.nodup_append.1 hnd
      -- the extract step
      have hn : σr.nodeOf G nv = some n := nodeOf_of_node hk hnv hmem
      have hc : n.children.childAt i = some cs[i] := by
        rw [hch]; simp [Children.childAt, List.getElem?_eq_getElem hi]
      have hspec := elemVar_spec p fresh h₁
      have hout : σr.cls v = none ∨ σr.cls v = some cs[i] := by
        rcases hspec with ⟨x, hpx, hvx, -⟩ | ⟨-, hvf, -⟩
        · subst hvx
          subst hpx
          cases hσ : σr.cls v with
          | none => exact Or.inl rfl
          | some c' =>
              right
              have hx : v < b := hlt v (List.mem_append_left _ (by simp))
              have h₁' := hinv.cls v c' hx hσ
              cases hpc with
              | var hx' => rw [hx'] at h₁'; exact congrArg some (Option.some.inj h₁').symm
              | app _ _ hh _ => simp [Pat.head] at hh
        · rw [hvf]; exact Or.inl (hinv.clsFree fresh (le_refl _))
      obtain ⟨σ₀, hσ₀, hcls₀, hσ₀eq⟩ := runStep_extractChild_complete hn hc hout
      obtain ⟨hle₁, hrel₁⟩ := elemVar_rel p fresh h₁
      have hinv₀ : CInv b fr₁ σ₀ σ := by
        rcases hσ₀eq with rfl | rfl
        · exact hinv.mono hle₁
        · rcases hspec with ⟨x, hpx, hvx, hfr⟩ | ⟨-, hvf, hfr⟩
          · subst hvx
            subst hpx
            subst hfr
            refine ⟨?_, hinv.mult, hinv.rest, hinv.seqRest, hinv.finRest, ?_, hinv.nodeFree⟩
            · intro y c' hy hc'
              by_cases hyx : y = v
              · subst hyx
                rw [setCls_cls_self] at hc'
                cases hpc with
                | var hx' => rw [← Option.some.inj hc']; exact hx'
                | app _ _ hh _ => simp [Pat.head] at hh
              · rw [setCls_cls_of_ne _ _ _ _ hyx] at hc'
                exact hinv.cls y c' hy hc'
            · intro w hw
              have hwx : w ≠ v := by
                have := hlt v (List.mem_append_left _ (by simp)); vomega
              rw [setCls_cls_of_ne _ _ _ _ hwx]
              exact hinv.clsFree w hw
          · subst hvf
            subst hfr
            refine ⟨?_, hinv.mult, hinv.rest, hinv.seqRest, hinv.finRest, ?_,
              fun w hw => hinv.nodeFree w (by vomega)⟩
            · intro y c' hy hc'
              have hyf : y ≠ v := by vomega
              rw [setCls_cls_of_ne _ _ _ _ hyf] at hc'
              exact hinv.cls y c' hy hc'
            · intro w hw
              have hwf : w ≠ v := by vomega
              rw [setCls_cls_of_ne _ _ _ _ hwf]
              exact hinv.clsFree w (by vomega)
      have hfr₀ : Frame [v] [] [] [] [] σr σ₀ := by
        rcases hσ₀eq with rfl | rfl
        · exact Frame.refl _ _ _ _ _ _
        · exact frame_setCls _ _ _
      have hrf₀ : RestFree (p.restVars ++ Pat.restVarsList ps) σ₀ := by
        intro r hr
        rw [hfr₀.rest r (by simp), hfr₀.seqRest r (by simp), hfr₀.finRest r (by simp)]
        exact hrf r hr
      -- the nested plan
      obtain ⟨σ₁, hσ₁, hinv₁⟩ := completeNested (hall p (List.mem_cons_self ..)) v fr₁ b σ₀ σ cs[i]
        hk (fun x hx => hlt x (List.mem_append_left _ hx)) (by vomega)
        (hrf₀.mono (List.subset_append_left _ _)) hnd'.1 hinv₀ hpc hcls₀
      rw [h₂] at hσ₁ hinv₁
      simp only at hσ₁ hinv₁
      obtain ⟨hf₁, -, hle₂⟩ := structNested (structAt p) v fr₁ σ₀ σ₁
        (fun x hx => by have := hlt x (by simp [hx]); vomega) hinv₀.free
        (hrf₀.mono (List.subset_append_left _ _)) hnd'.1 (by rw [h₂]; exact hσ₁)
      rw [h₂] at hf₁ hle₂
      simp only at hf₁ hle₂
      have hrf₂ : RestFree (Pat.restVarsList ps) σ₁ := by
        intro r hr
        have hnot : r ∉ p.restVars := fun hr' => hnd'.2.2 r hr' r hr rfl
        rw [hf₁.rest r hnot, hf₁.seqRest r hnot, hf₁.finRest r hnot]
        exact hrf₀ r (List.mem_append_right _ hr)
      have hnv₁ : σ₁.node nv = some id := hf₁.ext.2.1 nv id (by rw [hfr₀.node]; exact hnv)
      obtain ⟨σ', hσ', hinv'⟩ := ih (fun q hq => hall q (List.mem_cons_of_mem _ hq)) nv (i + 1) fr₂ b
        σ₁ σ id n cs hk (fun x hx => hlt x (List.mem_append_right _ hx)) (by vomega) hrf₂ hnd'.2.1
        hinv₁ hnv₁ hmem hch (by simp at hlen ⊢; vomega) hm
      rw [h₃] at hσ' hinv'
      simp only at hσ' hinv'
      refine ⟨σ', ?_, hinv'⟩
      rw [List.cons_append, mem_run_cons]
      exact ⟨σ₀, hσ₀, mem_run_append.2 ⟨σ₁, hσ₁, hσ'⟩⟩

/-! ### Zip and range helpers for the completeness cases -/

theorem mem_zip_map_fst {α β γ : Type} {l : List (α × β)} {cs : List γ} {et : (α × β) × γ}
    (h : et ∈ l.zip cs) : (et.1.1, et.2) ∈ (l.map (·.1)).zip cs := by
  rw [List.zip_map_left, List.mem_map]
  exact ⟨et, h, rfl⟩

theorem of_mem_zip_map {α β γ : Type} {f : α → β} {l : List α} {cs : List γ} {p : β} {c : γ}
    (h : (p, c) ∈ (l.map f).zip cs) : ∃ e ∈ l.zip cs, f e.1 = p ∧ e.2 = c := by
  rw [List.zip_map_left, List.mem_map] at h
  obtain ⟨e, he, heq⟩ := h
  simp only [Prod.map, id, Prod.mk.injEq] at heq
  exact ⟨e, he, heq.1, heq.2⟩

theorem keys_range {b lo hi : Nat} {ps : List Pat} {vs : List Var}
    (hrel : List.Forall₂ (ElemRel lo hi) ps vs) (hlt : ∀ x ∈ Pat.varsList ps, x < b) :
    ∀ v ∈ vs, v < b ∨ (lo ≤ v ∧ v < hi) := by
  intro v hv
  obtain ⟨p, hp, hpv⟩ := forall₂_exists_left hrel v hv
  rcases hpv.mem_or_range with h | h
  · exact Or.inl (hlt v (mem_varsList_of_mem hp h))
  · exact Or.inr h

theorem keys_range_ac {b lo hi : Nat} {es : List (Pat × Mult)} {vs : List (Var × Mult)}
    (hrel : List.Forall₂ (fun e v => e.2 = v.2 ∧ ElemRel lo hi e.1 v.1) es vs)
    (hlt : ∀ x ∈ Pat.varsElems es, x < b) :
    ∀ v ∈ vs.map (·.1), v < b ∨ (lo ≤ v ∧ v < hi) := by
  intro v hv
  rw [List.mem_map] at hv
  obtain ⟨v', hv', rfl⟩ := hv
  obtain ⟨e, he, -, hpv⟩ := forall₂_exists_left hrel v' hv'
  rcases hpv.mem_or_range with h | h
  · exact Or.inl (hlt _ (mem_varsElems_of_mem he h))
  · exact Or.inr h

/-- A key below `b` paired with child `c` is a var element matched at `c`. -/
theorem var_key_cls {b lo hi : Nat} {ps : List Pat} {vs : List Var} {cs : List C} {σ : Binding}
    {G : Graph} (hb : b ≤ lo) (hrel : List.Forall₂ (ElemRel lo hi) ps vs)
    (hall : ∀ pc ∈ ps.zip cs, MatchC G pc.1 pc.2 σ) :
    ∀ v c, (v, c) ∈ vs.zip cs → v < b → σ.cls v = some c := by
  intro v c hvc hvb
  obtain ⟨⟨p, c'⟩, hpc, hrel', hc⟩ := zip_transfer hrel.flip cs (v, c) hvc
  simp only at hrel' hc
  subst hc
  rcases hrel' with ⟨x, rfl, rfl⟩ | ⟨-, hlo, -⟩
  · cases hall _ hpc with
    | var hx => exact hx
    | app _ _ hh _ => simp [Pat.head] at hh
  · vomega

theorem var_key_cls_ac {b lo hi : Nat} {es : List (Pat × Mult)} {vs : List (Var × Mult)}
    {cs : List C} {σ : Binding} {G : Graph} (hb : b ≤ lo)
    (hrel : List.Forall₂ (fun e v => e.2 = v.2 ∧ ElemRel lo hi e.1 v.1) es vs)
    (hall : ∀ et ∈ es.zip cs, MatchC G et.1.1 et.2 σ) :
    ∀ v c, (v, c) ∈ (vs.map (·.1)).zip cs → v < b → σ.cls v = some c := by
  intro v c hvc hvb
  obtain ⟨⟨⟨v', μ⟩, c'⟩, hvc', hv', hc⟩ := of_mem_zip_map hvc
  simp only at hv' hc
  subst hv'; subst hc
  obtain ⟨⟨⟨p, μ'⟩, c''⟩, hpc, ⟨-, hrel'⟩, hc⟩ := zip_transfer hrel.flip cs ((v', μ), c') hvc'
  simp only at hrel' hc
  subst hc
  rcases hrel' with ⟨x, hx, rfl⟩ | ⟨-, hlo, -⟩
  · have := hall _ hpc
    simp only at this
    rw [hx] at this
    cases this with
    | var hx => exact hx
    | app _ _ hh _ => simp [Pat.head] at hh
  · vomega

theorem hall_of_forall₂ {G : Graph} {σ : Binding} {ps : List Pat} {cs : List C}
    (hlen : ps.length = cs.length) (hall : ∀ pc ∈ ps.zip cs, MatchC G pc.1 pc.2 σ) :
    List.Forall₂ (fun p c => MatchC G p c σ) ps cs :=
  List.forall₂_iff_zip.2 ⟨hlen, fun hab => hall _ hab⟩

theorem hall_of_forall₂_ac {G : Graph} {σ : Binding} {es : List (Pat × Mult)} {cs : List C}
    (hlen : es.length = cs.length) (hall : ∀ et ∈ es.zip cs, MatchC G et.1.1 et.2 σ) :
    List.Forall₂ (fun e c => MatchC G e.1 c σ) es cs :=
  List.forall₂_iff_zip.2 ⟨hlen, fun hab => hall _ hab⟩

/-! ### Completeness of a compiled application pattern -/

theorem completeAt_of_sub {G : Graph} (P : Pat)
    (ih : ∀ p, sizeOf p < sizeOf P → CompleteAt G p) : CompleteAt G P := by
  intro cv fresh b σr σ id n hk hh hlt hb hrf hnd hinv hmem hm hz
  cases P with
  | var x => simp [Pat.head] at hh
  | plain f args =>
      cases hm with
      | plain hlen hall =>
      rename_i cs
      rcases h₁ : compilePlainArgs args fresh 0 (fresh + 1) with ⟨s, fr⟩
      rw [compileAt_plain f args cv fresh h₁]
      simp only
      have hj : joinBind G σr fresh id ∈ runStep G (joinStep fresh f cv) σr :=
        mem_joinStep.2 ⟨id, _, hmem, rfl, hz, rfl⟩
      have hinv₁ := hinv.joinBind G hb id
      obtain ⟨σ', hσ', hinv'⟩ := completeArgs args (fun p hp => ih p (sizeOf_lt_plain hp f)) fresh 0
        (fresh + 1) b (joinBind G σr fresh id) σ id _ cs hk hlt (by vomega) (hrf.joinBind G fresh id) hnd
        hinv₁ (joinBind_node_self _ _ _ _) hmem rfl (by simp [hlen])
        (by simpa using hall_of_forall₂ hlen hall)
      rw [h₁] at hσ' hinv'
      simp only at hσ' hinv'
      obtain ⟨hf, -, -⟩ := structArgs args (fun q _ => structAt q) fresh 0 (fresh + 1) _ σ'
        (fun x hx => by have := hlt x (by simp [hx]); vomega) hinv₁.free (hrf.joinBind G fresh id) hnd (by rw [h₁]; exact hσ')
      rw [h₁] at hf
      simp only at hf
      exact ⟨σ', mem_run_cons.2 ⟨_, hj, hσ'⟩, hf.ext.2.1 fresh id (joinBind_node_self _ _ _ _), hinv'⟩
  | comm f p q =>
      have hcase : ∃ a₀ b₀ ca cb, n = ⟨f, .spair a₀ b₀⟩ ∧ MatchC G p ca σ ∧ MatchC G q cb σ ∧
          ((ca = a₀ ∧ cb = b₀) ∨ (ca = b₀ ∧ cb = a₀)) := by
        cases hm with
        | comm₁ hp hq => exact ⟨_, _, _, _, rfl, hp, hq, Or.inl ⟨rfl, rfl⟩⟩
        | comm₂ hp hq => exact ⟨_, _, _, _, rfl, hp, hq, Or.inr ⟨rfl, rfl⟩⟩
      obtain ⟨a₀, b₀, ca, cb, rfl, hp, hq, hab⟩ := hcase
      rcases h₁ : elemVar p (fresh + 1) with ⟨vp, fr₁⟩
      rcases h₂ : elemVar q fr₁ with ⟨vq, fr₂⟩
      rcases h₃ : compileNested p vp fr₂ with ⟨sp, fr₃⟩
      rcases h₄ : compileNested q vq fr₃ with ⟨sq, fr₄⟩
      rw [compileAt_comm f p q cv fresh h₁ h₂ h₃ h₄]
      simp only
      have hj : joinBind G σr fresh id ∈ runStep G (joinStep fresh f cv) σr :=
        mem_joinStep.2 ⟨id, _, hmem, rfl, hz, rfl⟩
      have hinv₁ := hinv.joinBind G hb id
      have hsp := elemVar_spec p (fresh + 1) h₁
      have hsq := elemVar_spec q fr₁ h₂
      rw [vars_comm] at hlt
      rw [restVars_comm] at hrf hnd
      have hnd' := List.nodup_append.1 hnd
      -- the star binding for the commutative step
      have hkeys : ∀ pr ∈ [(vp, ca), (vq, cb)], pr.1 < b ∨ fresh + 1 ≤ pr.1 := by
        intro pr hpr
        simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hpr
        rcases hpr with rfl | rfl
        · rcases hsp with ⟨x, hpx, hvx, -⟩ | ⟨-, hvp, -⟩
          · rw [hvx]; exact Or.inl (hlt x (List.mem_append_left _ (by rw [hpx]; simp)))
          · rw [hvp]; exact Or.inr (le_refl _)
        · rcases hsq with ⟨x, hqx, hvx, -⟩ | ⟨-, hvq, -⟩
          · rw [hvx]; exact Or.inl (hlt x (List.mem_append_right _ (by rw [hqx]; simp)))
          · rw [hvq]
            rcases hsp with ⟨-, -, -, hfr₁⟩ | ⟨-, -, hfr₁⟩ <;> exact Or.inr (by vomega)
      have hext₁ := extends_star (pairs := [(vp, ca), (vq, cb)]) hinv₁ hkeys
      have hstar_p : (star b (joinBind G σr fresh id) σ [(vp, ca), (vq, cb)]).cls vp = some ca := by
        rcases hsp with ⟨x, hpx, hvx, -⟩ | ⟨-, hvp, hfr₁⟩
        · subst hpx
          rw [hvx]
          cases hp with
          | var hx => exact star_cls_lt (hlt x (List.mem_append_left _ (by simp))) hx
          | app _ _ hh' _ => simp [Pat.head] at hh'
        · refine star_cls_ge (by vomega) (by simp) ?_
          intro pr hpr hpr1
          simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hpr
          rcases hpr with rfl | rfl
          · rfl
          · exfalso
            simp only at hpr1
            rcases hsq with ⟨x, hqx, hvx, -⟩ | ⟨-, hvq, -⟩
            · have := hlt x (List.mem_append_right _ (by rw [hqx]; simp)); vomega
            · vomega
      have hstar_q : (star b (joinBind G σr fresh id) σ [(vp, ca), (vq, cb)]).cls vq = some cb := by
        rcases hsq with ⟨x, hqx, hvx, -⟩ | ⟨-, hvq, -⟩
        · subst hqx
          rw [hvx]
          cases hq with
          | var hx => exact star_cls_lt (hlt x (List.mem_append_right _ (by simp))) hx
          | app _ _ hh' _ => simp [Pat.head] at hh'
        · refine star_cls_ge (by rcases hsp with ⟨-, -, -, hfr₁⟩ | ⟨-, -, hfr₁⟩ <;> vomega) (by simp) ?_
          intro pr hpr hpr1
          simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hpr
          rcases hpr with rfl | rfl
          · exfalso
            simp only at hpr1
            rcases hsp with ⟨x, hpx, hvx, hfr₁⟩ | ⟨-, hvp, hfr₁⟩
            · have := hlt x (List.mem_append_left _ (by rw [hpx]; simp)); vomega
            · vomega
          · rfl
      obtain ⟨σ₂, hσ₂, hext₂⟩ := decompose_comm_complete' vp vq a₀ b₀ _ _ hext₁
        (by rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · exact Or.inl ⟨hstar_p, hstar_q⟩
            · exact Or.inr ⟨hstar_p, hstar_q⟩)
      have hσ₂' : σ₂ ∈ runStep G (.decomposeComm fresh vp vq) (joinBind G σr fresh id) := by
        simp only [runStep, nodeOf_of_node hk (joinBind_node_self _ _ _ _) hmem]
        exact hσ₂
      have hfr₂ := frame_decomposeComm hσ₂
      have hle₁ : fresh + 1 ≤ fr₁ := by rcases hsp with ⟨-, -, -, hfr₁⟩ | ⟨-, -, hfr₁⟩ <;> vomega
      have hle₂ : fr₁ ≤ fr₂ := by rcases hsq with ⟨-, -, -, hfr₂⟩ | ⟨-, -, hfr₂⟩ <;> vomega
      have hinv₂ : CInv b fr₂ σ₂ σ := by
        refine cinv_of_extends_star hinv₁ (by vomega) (by vomega) ?_ hext₂ hfr₂.node
        intro pr hpr
        rcases hkeys pr hpr with h | h
        · exact Or.inl h
        · right
          simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hpr
          rcases hpr with rfl | rfl
          · rcases hsp with ⟨x, hpx, hvx, -⟩ | ⟨-, hvp, hfr₁⟩
            · exfalso
              have := hlt x (List.mem_append_left _ (by rw [hpx]; simp))
              simp only at h
              vomega
            · simp only at h ⊢; vomega
          · rcases hsq with ⟨x, hqx, hvx, -⟩ | ⟨-, hvq, hfr₂⟩
            · exfalso
              have := hlt x (List.mem_append_right _ (by rw [hqx]; simp))
              simp only at h
              vomega
            · simp only at h ⊢; vomega
      -- the element variables are bound to the matched classes
      obtain ⟨-, hcls₂⟩ := decompose_comm_sound' vp vq a₀ b₀ _ σ₂ hσ₂
      have hvp : σ₂.cls vp = some ca := by
        rcases hcls₂ with ⟨h, -⟩ | ⟨h, -⟩
        · have := hext₂.1 vp _ h; rw [hstar_p] at this; rw [h, Option.some.inj this]
        · have := hext₂.1 vp _ h; rw [hstar_p] at this; rw [h, Option.some.inj this]
      have hvq : σ₂.cls vq = some cb := by
        rcases hcls₂ with ⟨-, h⟩ | ⟨-, h⟩
        · have := hext₂.1 vq _ h; rw [hstar_q] at this; rw [h, Option.some.inj this]
        · have := hext₂.1 vq _ h; rw [hstar_q] at this; rw [h, Option.some.inj this]
      have hrf₂ : RestFree (p.restVars ++ q.restVars) σ₂ := by
        intro r hr
        rw [hfr₂.rest r (by simp), hfr₂.seqRest r (by simp), hfr₂.finRest r (by simp)]
        exact hrf r hr
      obtain ⟨σ₃, hσ₃, hinv₃⟩ := completeNested (ih p (sizeOf_lt_comm_left f p q)) vp fr₂ b σ₂ σ ca
        hk (fun x hx => hlt x (List.mem_append_left _ hx)) (by vomega)
        (hrf₂.mono (List.subset_append_left _ _)) hnd'.1 hinv₂ hp hvp
      rw [h₃] at hσ₃ hinv₃
      simp only at hσ₃ hinv₃
      obtain ⟨hf₃, -, hle₃⟩ := structNested (structAt p) vp fr₂ σ₂ σ₃
        (fun x hx => by have := hlt x (by simp [hx]); vomega) hinv₂.free
        (hrf₂.mono (List.subset_append_left _ _)) hnd'.1 (by rw [h₃]; exact hσ₃)
      rw [h₃] at hf₃ hle₃
      simp only at hf₃ hle₃
      have hrf₃ : RestFree q.restVars σ₃ := by
        intro r hr
        have hnot : r ∉ p.restVars := fun hr' => hnd'.2.2 r hr' r hr rfl
        rw [hf₃.rest r hnot, hf₃.seqRest r hnot, hf₃.finRest r hnot]
        exact hrf₂ r (List.mem_append_right _ hr)
      obtain ⟨σ', hσ', hinv'⟩ := completeNested (ih q (sizeOf_lt_comm_right f p q)) vq fr₃ b σ₃ σ cb
        hk (fun x hx => hlt x (List.mem_append_right _ hx)) (by vomega) hrf₃ hnd'.2.1 hinv₃ hq
        (hf₃.ext.1 vq cb hvq)
      rw [h₄] at hσ' hinv'
      simp only at hσ' hinv'
      obtain ⟨hf₄, -, -⟩ := structNested (structAt q) vq fr₃ σ₃ σ'
        (fun x hx => by have := hlt x (by simp [hx]); vomega) hinv₃.free hrf₃ hnd'.2.1
        (by rw [h₄]; exact hσ')
      rw [h₄] at hf₄
      simp only at hf₄
      refine ⟨σ', ?_, ?_, hinv'⟩
      · rw [List.cons_append, List.cons_append, mem_run_cons]
        exact ⟨_, hj, mem_run_cons.2 ⟨σ₂, hσ₂', mem_run_append.2 ⟨σ₃, hσ₃, hσ'⟩⟩⟩
      · exact hf₄.ext.2.1 fresh id (hf₃.ext.2.1 fresh id
          (by rw [hfr₂.node]; exact joinBind_node_self _ _ _ _))
  | assoc f pre args suf =>
      cases hm with
      | assoc hlen hpre hsuf hall =>
      rename_i u mid w
      rcases h₁ : elemVars args (fresh + 1) with ⟨vs, fr₁⟩
      rcases h₂ : compileNestedList args vs fr₁ with ⟨s, fr₂⟩
      rw [compileAt_assoc f pre args suf cv fresh h₁ h₂]
      simp only
      have hj : joinBind G σr fresh id ∈ runStep G (joinStep fresh f cv) σr :=
        mem_joinStep.2 ⟨id, _, hmem, rfl, hz, rfl⟩
      have hinv₁ := hinv.joinBind G hb id
      obtain ⟨hle₁, hrel⟩ := elemVars_spec args (fresh + 1) h₁
      rw [vars_assoc] at hlt
      rw [restVars_assoc] at hrf hnd
      have hnd' := List.nodup_append.1 hnd
      have hlt_args : ∀ x ∈ Pat.varsList args, x < b := fun x hx =>
        hlt x (List.mem_append_left _ (List.mem_append_right _ hx))
      have hrange := keys_range hrel hlt_args
      have hkeys : ∀ pr ∈ vs.zip mid, pr.1 < b ∨ fresh + 1 ≤ pr.1 := by
        intro pr hpr
        rcases hrange pr.1 (List.of_mem_zip hpr).1 with h | h
        · exact Or.inl h
        · exact Or.inr h.1
      have hext₁ := extends_star (pairs := vs.zip mid) hinv₁ hkeys
      have hdist := elemVars_distinct args (fresh + 1) h₁ (fun x hx => by have := hlt_args x hx; vomega)
      have hcls := star_cls_keys (σ1 := joinBind G σr fresh id) (σ := σ) (by vomega) hrange
        (var_key_cls (by vomega) hrel hall) hdist
      have hlen' : mid.length = vs.length := by rw [← hlen, hrel.length_eq]
      have hpre' : SeqRestOk (star b (joinBind G σr fresh id) σ (vs.zip mid)) pre u := by
        cases pre with
        | none => exact hpre
        | some r => exact star_seqRest_lt (hlt r (by simp)) hpre
      have hsuf' : SeqRestOk (star b (joinBind G σr fresh id) σ (vs.zip mid)) suf w := by
        cases suf with
        | none => exact hsuf
        | some r => exact star_seqRest_lt (hlt r (by simp)) hsuf
      obtain ⟨σ₂, hσ₂, hext₂⟩ := expand_a_complete' pre suf vs u mid w _ _ hext₁ hlen' hpre' hsuf' hcls
      have hσ₂' : σ₂ ∈ runStep G (.expandA fresh pre vs suf) (joinBind G σr fresh id) := by
        simp only [runStep, nodeOf_of_node hk (joinBind_node_self _ _ _ _) hmem]
        exact hσ₂
      have hfr₂ := frame_expandA hσ₂
      have hinv₂ : CInv b fr₁ σ₂ σ := by
        refine cinv_of_extends_star hinv₁ (by vomega) (by vomega) ?_ hext₂ hfr₂.node
        intro pr hpr
        rcases hrange pr.1 (List.of_mem_zip hpr).1 with h | h
        · exact Or.inl h
        · exact Or.inr h.2
      -- the element variables are bound to `mid`
      have hpre₀ : ∀ r, pre = some r → (joinBind G σr fresh id).seqRest r = none := by
        intro r hr; subst hr; exact (hrf r (by simp)).2.1
      have hsuf₀ : ∀ r, suf = some r → (joinBind G σr fresh id).seqRest r = none := by
        intro r hr; subst hr; exact (hrf r (by simp)).2.1
      have hdist' : ∀ r, pre = some r → suf ≠ some r := by
        intro r hr hs; subst hr; subst hs
        simp at hnd
      obtain ⟨-, u', mid', w', -, hlen'', -, -, hcls'⟩ :=
        expand_a_sound' pre suf vs _ _ σ₂ hpre₀ hsuf₀ hdist' hσ₂
      have hmid' : List.Forall₂ (fun v c => σ₂.cls v = some c) vs mid' :=
        forall₂_cls_of_zip hlen''.symm hcls'
      have hmid_eq : mid' = mid := by
        refine forall₂_cls_unique (f := (star b (joinBind G σr fresh id) σ (vs.zip mid)).cls)
          (hmid'.imp (fun v c h => hext₂.1 v c h)) ?_
        exact List.forall₂_iff_zip.2 ⟨hlen'.symm, fun hab => hcls _ hab⟩
      subst hmid_eq
      have hrf₂ : RestFree (Pat.restVarsList args) σ₂ := by
        intro r hr
        have hnot : r ∉ pre.toList ++ suf.toList := fun hr' => hnd'.2.2 r hr' r hr rfl
        rw [hfr₂.rest r (by simp), hfr₂.seqRest r hnot, hfr₂.finRest r (by simp)]
        exact hrf r (List.mem_append_right _ hr)
      obtain ⟨σ', hσ', hinv'⟩ := completeNestedList args
        (fun p hp => ih p (sizeOf_lt_assoc hp f pre suf)) vs mid' fr₁ b σ₂ σ hk hlt_args (by vomega)
        hrf₂ hnd'.2.1 hinv₂ (hall_of_forall₂ hlen hall) hmid'
      rw [h₂] at hσ' hinv'
      simp only at hσ' hinv'
      obtain ⟨hf₃, -, -⟩ := structNestedList args (fun q _ => structAt q) vs fr₁ σ₂ σ'
        (fun x hx => by have := hlt x (by simp [hx]); vomega) hinv₂.free
        hrf₂ hnd'.2.1 (by rw [h₂]; exact hσ')
      rw [h₂] at hf₃
      simp only at hf₃
      refine ⟨σ', mem_run_cons.2 ⟨_, hj, mem_run_cons.2 ⟨σ₂, hσ₂', hσ'⟩⟩, ?_, hinv'⟩
      exact hf₃.ext.2.1 fresh id (by rw [hfr₂.node]; exact joinBind_node_self _ _ _ _)
  | ac f elems rest =>
      cases hm with
      | ac hnd_t hlen_t hmem_t hall hmult hrest =>
      rename_i m taken
      rcases h₁ : elemVarsAC elems (fresh + 1) with ⟨vs, fr₁⟩
      rcases h₂ : compileNestedAC elems (vs.map (·.1)) fr₁ with ⟨s, fr₂⟩
      rw [compileAt_ac f elems rest cv fresh h₁ h₂]
      simp only
      have hj : joinBind G σr fresh id ∈ runStep G (joinStep fresh f cv) σr :=
        mem_joinStep.2 ⟨id, _, hmem, rfl, hz, rfl⟩
      have hinv₁ := hinv.joinBind G hb id
      obtain ⟨hle₁, hrel⟩ := elemVarsAC_spec elems (fresh + 1) h₁
      rw [vars_ac] at hlt
      rw [restVars_ac] at hrf hnd
      have hnd' := List.nodup_append.1 hnd
      have hlt_el : ∀ x ∈ Pat.varsElems elems, x < b := fun x hx => hlt x (List.mem_append_left _ hx)
      have hrange := keys_range_ac hrel hlt_el
      have hkeys : ∀ pr ∈ (vs.map (·.1)).zip taken, pr.1 < b ∨ fresh + 1 ≤ pr.1 := by
        intro pr hpr
        rcases hrange pr.1 (List.of_mem_zip hpr).1 with h | h
        · exact Or.inl h
        · exact Or.inr h.1
      have hext₁ := extends_star (pairs := (vs.map (·.1)).zip taken) hinv₁ hkeys
      have hdist := elemVarsAC_distinct elems (fresh + 1) h₁
        (fun x hx => by have := hlt_el x hx; vomega)
      have hcls := star_cls_keys (σ1 := joinBind G σr fresh id) (σ := σ) (by vomega) hrange
        (var_key_cls_ac (by vomega) hrel hall) hdist
      have hlen_v : vs.length = taken.length := by rw [← hlen_t, hrel.length_eq]
      have hcls_v : ∀ et ∈ vs.zip taken,
          (star b (joinBind G σr fresh id) σ ((vs.map (·.1)).zip taken)).cls et.1.1 = some et.2 :=
        fun et het => hcls _ (mem_zip_map_fst het)
      have hmult' : ∀ et ∈ vs.zip taken,
          MultOk (star b (joinBind G σr fresh id) σ ((vs.map (·.1)).zip taken)) et.1.2 (m.count et.2) := by
        intro et het
        obtain ⟨et', het', ⟨hμ, -⟩, hc⟩ := zip_transfer hrel.flip taken et het
        have hok := hmult et' het'
        rw [hμ, ← hc] at hok
        cases hμ' : et.1.2 with
        | exact k => rw [hμ'] at hok; exact hok
        | var k lo hi =>
            rw [hμ'] at hok
            obtain ⟨hk', hlo, hhi⟩ := hok
            refine ⟨star_mult_lt ?_ hk', hlo, hhi⟩
            apply hlt_el
            exact mem_varsElems_of_mult (List.of_mem_zip het').1 (by rw [hμ, hμ']; simp [Mult.vars])
      have hrest' : MsetRestOk (star b (joinBind G σr fresh id) σ ((vs.map (·.1)).zip taken)) rest m taken := by
        cases rest with
        | none => exact hrest
        | some r => exact star_rest_lt (hlt r (by simp)) hrest
      obtain ⟨σ₂, hσ₂, hext₂⟩ := decompose_ac_complete' vs rest m _ _ taken hext₁ hnd_t hlen_v hmem_t
        hcls_v hmult' hrest'
      have hσ₂' : σ₂ ∈ runStep G (.decomposeAC fresh vs rest) (joinBind G σr fresh id) := by
        simp only [runStep, nodeOf_of_node hk (joinBind_node_self _ _ _ _) hmem]
        exact hσ₂
      have hfr₂ := frame_decomposeAC vs rest _ _ _ hσ₂
      have hinv₂ : CInv b fr₁ σ₂ σ := by
        refine cinv_of_extends_star hinv₁ (by vomega) (by vomega) ?_ hext₂ hfr₂.node
        intro pr hpr
        rcases hrange pr.1 (List.of_mem_zip hpr).1 with h | h
        · exact Or.inl h
        · exact Or.inr h.2
      have hfresh : ∀ r ∈ rest, (joinBind G σr fresh id).rest r = none := by
        intro r hr; exact (hrf r (List.mem_append_left _ (Option.mem_toList.2 hr))).1
      obtain ⟨-, taken', -, hlen', -, hcls', -, -⟩ := decompose_ac_sound' vs rest m _ σ₂ hfresh hσ₂
      have htk' : List.Forall₂ (fun v c => σ₂.cls v = some c) (vs.map (·.1)) taken' :=
        forall₂_cls_of_zip_fst hlen' hcls'
      have htk_eq : taken' = taken := by
        refine forall₂_cls_unique (f := (star b (joinBind G σr fresh id) σ ((vs.map (·.1)).zip taken)).cls)
          (htk'.imp (fun v c h => hext₂.1 v c h)) ?_
        rw [List.forall₂_map_left_iff]
        exact List.forall₂_iff_zip.2 ⟨hlen_v, fun hab => hcls _ (mem_zip_map_fst hab)⟩
      subst htk_eq
      have hrf₂ : RestFree (Pat.restVarsElems elems) σ₂ := by
        intro r hr
        have hnot : r ∉ rest.toList := fun hr' => hnd'.2.2 r hr' r hr rfl
        rw [hfr₂.rest r hnot, hfr₂.seqRest r (by simp), hfr₂.finRest r (by simp)]
        exact hrf r (List.mem_append_right _ hr)
      obtain ⟨σ', hσ', hinv'⟩ := completeNestedAC elems (fun e he => ih e.1 (sizeOf_lt_ac he f rest))
        (vs.map (·.1)) taken' fr₁ b σ₂ σ hk hlt_el (by vomega) hrf₂ hnd'.2.1 hinv₂
        (hall_of_forall₂_ac hlen_t hall) htk'
      rw [h₂] at hσ' hinv'
      simp only at hσ' hinv'
      obtain ⟨hf₃, -, -⟩ := structNestedAC elems (fun q _ => structAt q.1) (vs.map (·.1)) fr₁ σ₂ σ'
        (fun x hx => by have := hlt x (by simp [hx]); vomega) hinv₂.free hrf₂ hnd'.2.1 (by rw [h₂]; exact hσ')
      rw [h₂] at hf₃
      simp only at hf₃
      refine ⟨σ', mem_run_cons.2 ⟨_, hj, mem_run_cons.2 ⟨σ₂, hσ₂', hσ'⟩⟩, ?_, hinv'⟩
      exact hf₃.ext.2.1 fresh id (by rw [hfr₂.node]; exact joinBind_node_self _ _ _ _)
  | aci f elems rest =>
      cases hm with
      | aci hnd_t hlen_t hmem_t hall hrest =>
      rename_i st taken
      rcases h₁ : elemVars elems (fresh + 1) with ⟨vs, fr₁⟩
      rcases h₂ : compileNestedList elems vs fr₁ with ⟨s, fr₂⟩
      rw [compileAt_aci f elems rest cv fresh h₁ h₂]
      simp only
      have hj : joinBind G σr fresh id ∈ runStep G (joinStep fresh f cv) σr :=
        mem_joinStep.2 ⟨id, _, hmem, rfl, hz, rfl⟩
      have hinv₁ := hinv.joinBind G hb id
      obtain ⟨hle₁, hrel⟩ := elemVars_spec elems (fresh + 1) h₁
      rw [vars_aci] at hlt
      rw [restVars_aci] at hrf hnd
      have hnd' := List.nodup_append.1 hnd
      have hlt_el : ∀ x ∈ Pat.varsList elems, x < b := fun x hx => hlt x (List.mem_append_left _ hx)
      have hrange := keys_range hrel hlt_el
      have hkeys : ∀ pr ∈ vs.zip taken, pr.1 < b ∨ fresh + 1 ≤ pr.1 := by
        intro pr hpr
        rcases hrange pr.1 (List.of_mem_zip hpr).1 with h | h
        · exact Or.inl h
        · exact Or.inr h.1
      have hext₁ := extends_star (pairs := vs.zip taken) hinv₁ hkeys
      have hdist := elemVars_distinct elems (fresh + 1) h₁ (fun x hx => by have := hlt_el x hx; vomega)
      have hcls := star_cls_keys (σ1 := joinBind G σr fresh id) (σ := σ) (by vomega) hrange
        (var_key_cls (by vomega) hrel hall) hdist
      have hlen_v : vs.length = taken.length := by rw [← hlen_t, hrel.length_eq]
      have hrest' : SetRestOk (star b (joinBind G σr fresh id) σ (vs.zip taken)) rest st taken := by
        cases rest with
        | none => exact hrest
        | some r => exact star_finRest_lt (hlt r (by simp)) hrest
      obtain ⟨σ₂, hσ₂, hext₂⟩ := decompose_aci_complete' vs rest st _ _ taken hext₁ hnd_t hlen_v hmem_t
        hcls hrest'
      have hσ₂' : σ₂ ∈ runStep G (.decomposeACI fresh vs rest) (joinBind G σr fresh id) := by
        simp only [runStep, nodeOf_of_node hk (joinBind_node_self _ _ _ _) hmem]
        exact hσ₂
      have hfr₂ := frame_decomposeACI vs rest _ _ _ hσ₂
      have hinv₂ : CInv b fr₁ σ₂ σ := by
        refine cinv_of_extends_star hinv₁ (by vomega) (by vomega) ?_ hext₂ hfr₂.node
        intro pr hpr
        rcases hrange pr.1 (List.of_mem_zip hpr).1 with h | h
        · exact Or.inl h
        · exact Or.inr h.2
      have hfresh : ∀ r ∈ rest, (joinBind G σr fresh id).finRest r = none := by
        intro r hr; exact (hrf r (List.mem_append_left _ (Option.mem_toList.2 hr))).2.2
      obtain ⟨-, taken', -, hlen', -, hcls', -⟩ := decompose_aci_sound' vs rest st _ σ₂ hfresh hσ₂
      have htk' : List.Forall₂ (fun v c => σ₂.cls v = some c) vs taken' :=
        forall₂_cls_of_zip hlen' hcls'
      have htk_eq : taken' = taken := by
        refine forall₂_cls_unique (f := (star b (joinBind G σr fresh id) σ (vs.zip taken)).cls)
          (htk'.imp (fun v c h => hext₂.1 v c h)) ?_
        exact List.forall₂_iff_zip.2 ⟨hlen_v, fun hab => hcls _ hab⟩
      subst htk_eq
      have hrf₂ : RestFree (Pat.restVarsList elems) σ₂ := by
        intro r hr
        have hnot : r ∉ rest.toList := fun hr' => hnd'.2.2 r hr' r hr rfl
        rw [hfr₂.rest r (by simp), hfr₂.seqRest r (by simp), hfr₂.finRest r hnot]
        exact hrf r (List.mem_append_right _ hr)
      obtain ⟨σ', hσ', hinv'⟩ := completeNestedList elems (fun p hp => ih p (sizeOf_lt_aci hp f rest))
        vs taken' fr₁ b σ₂ σ hk hlt_el (by vomega) hrf₂ hnd'.2.1 hinv₂ (hall_of_forall₂ hlen_t hall) htk'
      rw [h₂] at hσ' hinv'
      simp only at hσ' hinv'
      obtain ⟨hf₃, -, -⟩ := structNestedList elems (fun q _ => structAt q) vs fr₁ σ₂ σ'
        (fun x hx => by have := hlt x (by simp [hx]); vomega) hinv₂.free
        hrf₂ hnd'.2.1 (by rw [h₂]; exact hσ')
      rw [h₂] at hf₃
      simp only at hf₃
      refine ⟨σ', mem_run_cons.2 ⟨_, hj, mem_run_cons.2 ⟨σ₂, hσ₂', hσ'⟩⟩, ?_, hinv'⟩
      exact hf₃.ext.2.1 fresh id (by rw [hfr₂.node]; exact joinBind_node_self _ _ _ _)

theorem completeAt_all {G : Graph} : ∀ (n : Nat) (P : Pat), sizeOf P = n → CompleteAt G P := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
      intro P hP
      exact completeAt_of_sub P (fun p hp => ih _ (hP ▸ hp) p rfl)

theorem completeAt {G : Graph} (P : Pat) : CompleteAt G P := completeAt_all _ P rfl

/-- `Extends` restricted to the variables below `b`, on every map but
`node`: the comparison the completeness theorem can make between an
emitted binding, which also binds the plan's fresh node and class
variables, and the match witness. -/
def ExtendsBelow (b : Nat) (σ' σ : Binding) : Prop :=
  (∀ x c, x < b → σ'.cls x = some c → σ.cls x = some c) ∧
  (∀ k m, k < b → σ'.mult k = some m → σ.mult k = some m) ∧
  (∀ r m, r < b → σ'.rest r = some m → σ.rest r = some m) ∧
  (∀ r u, r < b → σ'.seqRest r = some u → σ.seqRest r = some u) ∧
  (∀ r s, r < b → σ'.finRest r = some s → σ.finRest r = some s)

/-- Lemma 12 (`interp_complete`), corrected. The statement in `Lemmas.lean`
is false: it concludes `Extends σ' σ` for the emitted `σ'`, but `σ'` binds
the node variable `fresh` (and the fresh class variables of nested
applications), which the witness `σ` need not bind. Counterexample:
`G.nodes = [(0, ⟨f, .tuple []⟩)]`, `P = .plain f []`, `fresh = 1`, `σ`
with every map `none`: `MatchN` holds (the `plain` clause is vacuous), the
only emitted binding has `node 1 = some 0`, and `Extends σ' σ` demands
`σ.node 1 = some 0`. The corrected conclusion compares the two bindings
below `fresh` and on every map but `node` (`ExtendsBelow`). The added
hypothesis `hnd` (distinct rest variables) is needed for the same reason
as in `interp_sound'`. -/
theorem interp_complete' (G : Graph) (P : Pat) (fresh : Nat) (σ : Binding)
    (id : NodeId) (n : Node)
    (hkeys : G.KeysNodup) (hP : P.head.isSome = true)
    (hf : ∀ x ∈ P.vars, x < fresh) (hnd : P.restVars.Nodup)
    (hmem : (id, n) ∈ G.nodes) (hm : MatchN G P n σ) :
    ∃ σ' ∈ run G (compile P fresh) Binding.empty,
      σ'.node fresh = some id ∧ ExtendsBelow fresh σ' σ := by
  obtain ⟨σ', hσ', hid, hinv⟩ := completeAt P none fresh fresh Binding.empty σ id n hkeys hP hf
    (le_refl _) (fun _ _ => ⟨rfl, rfl, rfl⟩) hnd (CInv.empty _ _ _) hmem hm (fun _ h => by cases h)
  exact ⟨σ', hσ', hid, hinv.cls, hinv.mult, hinv.rest, hinv.seqRest, hinv.finRest⟩

end Semper.EMatch
