import SemperProofs.EMatch.Engine.Atoms

/-!
# Atoms versus declarative matching

`atoms_iff_match`: an application pattern `P` matches at class `c` under
`σ` iff some binding `σ'` agreeing with `σ` on `P.vars` binds the root
class variable `r` to `c` and satisfies every atom of `atoms P r`.
-/

namespace Semper.EMatch

open Binding

/-! ## The flattening, unfolded -/

theorem atomsAt_var (x n : Var) (fresh : Nat) : atomsAt (.var x) n fresh = ([], fresh) := by
  rw [atomsAt]

theorem atomsAt_plain (f : Sym) (args : List Pat) (n : Var) (fresh : Nat)
    {vs : List Var} {as : List RAtom} {fr : Nat} (h : atomsChildren args fresh = (vs, as, fr)) :
    atomsAt (.plain f args) n fresh = (as ++ [⟨n, f, .plain vs⟩], fr) := by
  rw [atomsAt]; simp [h]

theorem atomsAt_comm (f : Sym) (p q : Pat) (n : Var) (fresh : Nat)
    {vp vq : Var} {ap aq : List RAtom} {fr₁ fr₂ : Nat}
    (h₁ : atomsChild p fresh = (vp, ap, fr₁)) (h₂ : atomsChild q fr₁ = (vq, aq, fr₂)) :
    atomsAt (.comm f p q) n fresh = (ap ++ aq ++ [⟨n, f, .comm vp vq⟩], fr₂) := by
  rw [atomsAt]; simp [h₁, h₂]

theorem atomsAt_assoc (f : Sym) (pre : Option Var) (args : List Pat) (suf : Option Var)
    (n : Var) (fresh : Nat) {vs : List Var} {as : List RAtom} {fr : Nat}
    (h : atomsChildren args fresh = (vs, as, fr)) :
    atomsAt (.assoc f pre args suf) n fresh = (as ++ [⟨n, f, .assoc pre vs suf⟩], fr) := by
  rw [atomsAt]; simp [h]

theorem atomsAt_ac (f : Sym) (elems : List (Pat × Mult)) (rest : Option Var) (n : Var)
    (fresh : Nat) {vs : List (Var × Mult)} {as : List RAtom} {fr : Nat}
    (h : atomsChildrenAC elems fresh = (vs, as, fr)) :
    atomsAt (.ac f elems rest) n fresh = (as ++ [⟨n, f, .ac vs rest⟩], fr) := by
  rw [atomsAt]; simp [h]

theorem atomsAt_aci (f : Sym) (elems : List Pat) (rest : Option Var) (n : Var) (fresh : Nat)
    {vs : List Var} {as : List RAtom} {fr : Nat} (h : atomsChildren elems fresh = (vs, as, fr)) :
    atomsAt (.aci f elems rest) n fresh = (as ++ [⟨n, f, .aci vs rest⟩], fr) := by
  rw [atomsAt]; simp [h]

theorem atomsChild_var (x : Var) (fresh : Nat) : atomsChild (.var x) fresh = (x, [], fresh) := by
  rw [atomsChild]

/-- A child is a variable with no atom, or an application flattened at the
fresh node variable. -/
theorem atomsChild_spec (p : Pat) (fresh : Nat) {v : Var} {ap : List RAtom} {fr : Nat}
    (h : atomsChild p fresh = (v, ap, fr)) :
    (∃ x, p = .var x ∧ v = x ∧ ap = [] ∧ fr = fresh) ∨
    (p.head.isSome = true ∧ v = fresh ∧ atomsAt p fresh (fresh + 1) = (ap, fr)) := by
  cases p with
  | var x =>
      rw [atomsChild_var] at h
      simp at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact Or.inl ⟨x, rfl, rfl, rfl, rfl⟩
  | plain f args =>
      rw [atomsChild] at h
      rcases h' : atomsAt (.plain f args) fresh (fresh + 1) with ⟨as', fr'⟩
      rw [h'] at h; simp at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact Or.inr ⟨rfl, rfl, rfl⟩
  | comm f p q =>
      rw [atomsChild] at h
      rcases h' : atomsAt (.comm f p q) fresh (fresh + 1) with ⟨as', fr'⟩
      rw [h'] at h; simp at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact Or.inr ⟨rfl, rfl, rfl⟩
  | assoc f pre args suf =>
      rw [atomsChild] at h
      rcases h' : atomsAt (.assoc f pre args suf) fresh (fresh + 1) with ⟨as', fr'⟩
      rw [h'] at h; simp at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact Or.inr ⟨rfl, rfl, rfl⟩
  | ac f elems rest =>
      rw [atomsChild] at h
      rcases h' : atomsAt (.ac f elems rest) fresh (fresh + 1) with ⟨as', fr'⟩
      rw [h'] at h; simp at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact Or.inr ⟨rfl, rfl, rfl⟩
  | aci f elems rest =>
      rw [atomsChild] at h
      rcases h' : atomsAt (.aci f elems rest) fresh (fresh + 1) with ⟨as', fr'⟩
      rw [h'] at h; simp at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact Or.inr ⟨rfl, rfl, rfl⟩

theorem atomsChildren_nil (fresh : Nat) : atomsChildren [] fresh = ([], [], fresh) := by
  rw [atomsChildren]

theorem atomsChildren_cons (p : Pat) (ps : List Pat) (fresh : Nat) {v : Var} {vs : List Var}
    {ap as : List RAtom} {fr₁ fr₂ : Nat}
    (h₁ : atomsChild p fresh = (v, ap, fr₁)) (h₂ : atomsChildren ps fr₁ = (vs, as, fr₂)) :
    atomsChildren (p :: ps) fresh = (v :: vs, ap ++ as, fr₂) := by
  rw [atomsChildren]; simp [h₁, h₂]

theorem atomsChildrenAC_nil (fresh : Nat) : atomsChildrenAC [] fresh = ([], [], fresh) := by
  rw [atomsChildrenAC]

theorem atomsChildrenAC_cons (p : Pat) (μ : Mult) (es : List (Pat × Mult)) (fresh : Nat)
    {v : Var} {vs : List (Var × Mult)} {ap as : List RAtom} {fr₁ fr₂ : Nat}
    (h₁ : atomsChild p fresh = (v, ap, fr₁)) (h₂ : atomsChildrenAC es fr₁ = (vs, as, fr₂)) :
    atomsChildrenAC ((p, μ) :: es) fresh = ((v, μ) :: vs, ap ++ as, fr₂) := by
  rw [atomsChildrenAC]; simp [h₁, h₂]

/-! ## Agreement -/

theorem AgreeOn.symm {V : List Var} {σ σ' : Binding} (h : AgreeOn V σ σ') : AgreeOn V σ' σ :=
  fun x hx => ⟨(h x hx).1.symm, (h x hx).2.1.symm, (h x hx).2.2.1.symm, (h x hx).2.2.2.1.symm,
    (h x hx).2.2.2.2.symm⟩

theorem AgreeOn.mono {V V' : List Var} {σ σ' : Binding} (h : AgreeOn V σ σ')
    (hV : ∀ x ∈ V', x ∈ V) : AgreeOn V' σ σ' :=
  fun x hx => h x (hV x hx)

theorem MultOk.agree {σ σ' : Binding} {μ : Mult} {m : Nat} (h : MultOk σ μ m)
    (ha : ∀ k ∈ μ.vars, σ.mult k = σ'.mult k) : MultOk σ' μ m := by
  cases μ with
  | exact k => exact h
  | var k lo hi =>
      simp only [MultOk] at h ⊢
      rw [← ha k (by simp [Mult.vars])]
      exact h

theorem SeqRestOk.agree {σ σ' : Binding} {r : Option Var} {u : List C} (h : SeqRestOk σ r u)
    (ha : ∀ x ∈ r.toList, σ.seqRest x = σ'.seqRest x) : SeqRestOk σ' r u := by
  cases r with
  | none => exact h
  | some r => simp only [SeqRestOk] at h ⊢; rw [← ha r (by simp)]; exact h

theorem MsetRestOk.agree {σ σ' : Binding} {r : Option Var} {m : Multiset C} {taken : List C}
    (h : MsetRestOk σ r m taken) (ha : ∀ x ∈ r.toList, σ.rest x = σ'.rest x) :
    MsetRestOk σ' r m taken := by
  cases r with
  | none => exact h
  | some r => simp only [MsetRestOk] at h ⊢; rw [← ha r (by simp)]; exact h

theorem SetRestOk.agree {σ σ' : Binding} {r : Option Var} {s : Finset C} {taken : List C}
    (h : SetRestOk σ r s taken) (ha : ∀ x ∈ r.toList, σ.finRest x = σ'.finRest x) :
    SetRestOk σ' r s taken := by
  cases r with
  | none => exact h
  | some r => simp only [SetRestOk] at h ⊢; rw [← ha r (by simp)]; exact h

mutual
/-- Matching only reads the pattern's variables. -/
theorem MatchC_agree {G : Graph} {P : Pat} {c : C} {σ σ' : Binding}
    (h : MatchC G P c σ) (ha : AgreeOn P.vars σ σ') : MatchC G P c σ' :=
  match h with
  | .var hx => .var (by rw [← (ha _ (by simp)).1]; exact hx)
  | .app hmem hf hh hn => .app hmem hf hh (MatchN_agree hn ha)
theorem MatchN_agree {G : Graph} {P : Pat} {n : Node} {σ σ' : Binding}
    (h : MatchN G P n σ) (ha : AgreeOn P.vars σ σ') : MatchN G P n σ' :=
  match h with
  | .plain hl hall =>
      .plain hl (fun pc hpc => MatchC_agree (hall pc hpc)
        (ha.mono (fun x hx => by simpa using mem_varsList_of_mem (List.of_mem_zip hpc).1 hx)))
  | .comm₁ hp hq =>
      .comm₁ (MatchC_agree hp (ha.mono (fun x hx => by simp [hx])))
        (MatchC_agree hq (ha.mono (fun x hx => by simp [hx])))
  | .comm₂ hp hq =>
      .comm₂ (MatchC_agree hp (ha.mono (fun x hx => by simp [hx])))
        (MatchC_agree hq (ha.mono (fun x hx => by simp [hx])))
  | .assoc hl hpre hsuf hall =>
      .assoc hl (hpre.agree (fun r hr => (ha r (by simp [hr])).2.2.2.1))
        (hsuf.agree (fun r hr => (ha r (by simp [hr])).2.2.2.1))
        (fun pc hpc => MatchC_agree (hall pc hpc)
          (ha.mono (fun x hx => by simp [mem_varsList_of_mem (List.of_mem_zip hpc).1 hx])))
  | .ac hnd hl hmem hall hmult hrest =>
      .ac hnd hl hmem
        (fun et het => MatchC_agree (hall et het)
          (ha.mono (fun x hx => by simp [mem_varsElems_of_mem (List.of_mem_zip het).1 hx])))
        (fun et het => (hmult et het).agree
          (fun k hk => (ha k (by simp [mem_varsElems_of_mult (List.of_mem_zip het).1 hk])).2.1))
        (hrest.agree (fun r hr => (ha r (by simp [hr])).2.2.1))
  | .aci hnd hl hmem hall hrest =>
      .aci hnd hl hmem
        (fun et het => MatchC_agree (hall et het)
          (ha.mono (fun x hx => by simp [mem_varsList_of_mem (List.of_mem_zip het).1 hx])))
        (hrest.agree (fun r hr => (ha r (by simp [hr])).2.2.2.2))
end

/-! ## Atom variables -/

theorem varsList_map_var (cs : List Var) : Pat.varsList (cs.map .var) = cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp [varsList_cons, ih]

theorem mem_varsElems_map_var {es : List (Var × Mult)} {x : Var} :
    x ∈ Pat.varsElems (es.map fun e => (Pat.var e.1, e.2)) ↔ ∃ e ∈ es, x = e.1 ∨ x ∈ e.2.vars := by
  induction es with
  | nil => simp
  | cons e es ih =>
      obtain ⟨v, μ⟩ := e
      simp [varsElems_cons, ih, or_assoc]

theorem mem_multVars_ac {n : Var} {f : Sym} {es : List (Var × Mult)} {rest : Option Var}
    {k : Var} : k ∈ (RAtom.mk n f (.ac es rest)).multVars ↔ ∃ e ∈ es, k ∈ e.2.vars := by
  simp only [RAtom.multVars, mem_multVars]

theorem shallow_vars_sub (a : RAtom) : ∀ x ∈ a.shallow.vars, x ∈ a.vars := by
  obtain ⟨n, f, sh⟩ := a
  intro x hx
  cases sh with
  | plain cs =>
      simp [RAtom.shallow, varsList_map_var] at hx
      simp [RAtom.vars, RAtom.elems, RAtom.multVars, RAtom.restVars, RAtom.seqRestVars,
        RAtom.msetRestVars, RAtom.setRestVars, hx]
  | comm a b =>
      simp [RAtom.shallow] at hx
      simp [RAtom.vars, RAtom.elems, RAtom.multVars, RAtom.restVars, RAtom.seqRestVars,
        RAtom.msetRestVars, RAtom.setRestVars, hx]
  | assoc pre fx suf =>
      simp [RAtom.shallow, varsList_map_var] at hx
      simp [RAtom.vars, RAtom.elems, RAtom.multVars, RAtom.restVars, RAtom.seqRestVars,
        RAtom.msetRestVars, RAtom.setRestVars]
      tauto
  | ac es rest =>
      simp only [RAtom.shallow, vars_ac, List.mem_append, mem_varsElems_map_var] at hx
      simp only [RAtom.vars, RAtom.elems, RAtom.restVars, RAtom.seqRestVars,
        RAtom.msetRestVars, RAtom.setRestVars, List.mem_cons, List.mem_append, List.mem_map,
        mem_multVars_ac, List.nil_append, List.append_nil]
      rcases hx with ⟨e, he, rfl | hk⟩ | hr
      · exact Or.inl (Or.inl (Or.inr ⟨e, he, rfl⟩))
      · exact Or.inl (Or.inr ⟨e, he, hk⟩)
      · exact Or.inr hr
  | aci es rest =>
      simp [RAtom.shallow, varsList_map_var] at hx
      simp [RAtom.vars, RAtom.elems, RAtom.multVars, RAtom.restVars, RAtom.seqRestVars,
        RAtom.msetRestVars, RAtom.setRestVars]
      tauto

/-- Atom satisfaction only reads the atom's variables. -/
theorem AtomSat.agree {G : Graph} {σ σ' : Binding} {a : RAtom} (h : AtomSat G σ a)
    (ha : ∀ x ∈ a.vars, σ.node x = σ'.node x ∧ σ.cls x = σ'.cls x ∧ σ.mult x = σ'.mult x ∧
      σ.rest x = σ'.rest x ∧ σ.seqRest x = σ'.seqRest x ∧ σ.finRest x = σ'.finRest x) :
    AtomSat G σ' a := by
  obtain ⟨id, nd, hnode, hmem, hcls, hop, hm⟩ := h
  have hn : a.node ∈ a.vars := by simp [RAtom.vars]
  refine ⟨id, nd, ?_, hmem, ?_, hop, MatchN_agree hm (fun x hx => (ha x (shallow_vars_sub a x hx)).2)⟩
  · rw [← (ha _ hn).1]; exact hnode
  · rw [← (ha _ hn).2.1]; exact hcls

/-! ## Bindings that keep a set of variables -/

/-- `σ'` keeps the node and class entries of `σ` at every variable satisfying
`K`, and keeps the other maps entirely. -/
def Keeps (K : Var → Prop) (σ σ' : Binding) : Prop :=
  (∀ v, K v → σ'.node v = σ.node v ∧ σ'.cls v = σ.cls v) ∧
  σ'.mult = σ.mult ∧ σ'.rest = σ.rest ∧ σ'.seqRest = σ.seqRest ∧ σ'.finRest = σ.finRest

theorem Keeps.refl (K : Var → Prop) (σ : Binding) : Keeps K σ σ :=
  ⟨fun _ _ => ⟨rfl, rfl⟩, rfl, rfl, rfl, rfl⟩

theorem Keeps.trans {K K' : Var → Prop} {σ σ' σ'' : Binding} (h : Keeps K σ σ')
    (h' : Keeps K' σ' σ'') : Keeps (fun v => K v ∧ K' v) σ σ'' :=
  ⟨fun v hv => ⟨(h'.1 v hv.2).1.trans (h.1 v hv.1).1, (h'.1 v hv.2).2.trans (h.1 v hv.1).2⟩,
    h'.2.1.trans h.2.1, h'.2.2.1.trans h.2.2.1, h'.2.2.2.1.trans h.2.2.2.1,
    h'.2.2.2.2.trans h.2.2.2.2⟩

theorem Keeps.mono {K K' : Var → Prop} {σ σ' : Binding} (h : Keeps K σ σ')
    (hK : ∀ v, K' v → K v) : Keeps K' σ σ' :=
  ⟨fun v hv => h.1 v (hK v hv), h.2⟩

theorem Keeps.agreeOn {K : Var → Prop} {σ σ' : Binding} (h : Keeps K σ σ') {V : List Var}
    (hV : ∀ x ∈ V, K x) : AgreeOn V σ σ' :=
  fun x hx => ⟨(h.1 x (hV x hx)).2.symm, by rw [h.2.1], by rw [h.2.2.1], by rw [h.2.2.2.1],
    by rw [h.2.2.2.2]⟩

theorem AtomSat.keeps {K : Var → Prop} {G : Graph} {σ σ' : Binding} {a : RAtom}
    (h : Keeps K σ σ') (hK : ∀ x ∈ a.vars, K x) (hs : AtomSat G σ a) : AtomSat G σ' a :=
  hs.agree (fun x hx => ⟨(h.1 x (hK x hx)).1.symm, (h.1 x (hK x hx)).2.symm, by rw [h.2.1],
    by rw [h.2.2.1], by rw [h.2.2.2.1], by rw [h.2.2.2.2]⟩)

/-- Bind a node variable to a node and its class. -/
def bindNode (σ : Binding) (n : Var) (id : NodeId) (c : C) : Binding :=
  { σ with node := Function.update σ.node n (some id), cls := Function.update σ.cls n (some c) }

@[simp] theorem bindNode_node_self (σ : Binding) (n : Var) (id : NodeId) (c : C) :
    (bindNode σ n id c).node n = some id := by simp [bindNode]

@[simp] theorem bindNode_cls_self (σ : Binding) (n : Var) (id : NodeId) (c : C) :
    (bindNode σ n id c).cls n = some c := by simp [bindNode]

theorem keeps_bindNode (σ : Binding) (n : Var) (id : NodeId) (c : C) :
    Keeps (fun v => v ≠ n) σ (bindNode σ n id c) :=
  ⟨fun v hv => by simp [bindNode, Function.update_of_ne hv], rfl, rfl, rfl, rfl⟩

/-! ## Variables and fresh range of the atoms -/

/-- The atoms of `P` at `n` from `fresh` mention `n`, the pattern's
variables and the fresh range `[fresh, fr)`, where `fr` is the returned
counter; the counter does not decrease. -/
def VarsOk (P : Pat) (n : Var) (fresh : Nat) : Prop :=
  fresh ≤ (atomsAt P n fresh).2 ∧
  ∀ a ∈ (atomsAt P n fresh).1, ∀ x ∈ a.vars,
    x = n ∨ x ∈ P.vars ∨ (fresh ≤ x ∧ x < (atomsAt P n fresh).2)

theorem range_mono {x lo hi lo' hi' : Nat} (h : lo ≤ x ∧ x < hi) (h₁ : lo' ≤ lo)
    (h₂ : hi ≤ hi') : lo' ≤ x ∧ x < hi' :=
  ⟨le_trans h₁ h.1, lt_of_lt_of_le h.2 h₂⟩

theorem varsChild (p : Pat) (hp : ∀ n fresh, VarsOk p n fresh) (fresh : Nat)
    {v : Var} {ap : List RAtom} {fr : Nat} (h : atomsChild p fresh = (v, ap, fr)) :
    fresh ≤ fr ∧ (v ∈ p.vars ∨ (fresh ≤ v ∧ v < fr)) ∧
      ∀ a ∈ ap, ∀ x ∈ a.vars, x ∈ p.vars ∨ (fresh ≤ x ∧ x < fr) := by
  rcases atomsChild_spec p fresh h with ⟨x, rfl, rfl, rfl, rfl⟩ | ⟨hh, rfl, h'⟩
  · exact ⟨le_refl _, Or.inl (by simp), fun a ha => by simp at ha⟩
  · obtain ⟨hle, hvars⟩ := hp v (v + 1)
    rw [h'] at hle hvars
    dsimp only at hle hvars
    refine ⟨by vomega, Or.inr ⟨le_refl _, by vomega⟩, ?_⟩
    intro a ha x hx
    rcases hvars a ha x hx with hx | hx | hx
    · exact Or.inr ⟨le_of_eq hx.symm, by vomega⟩
    · exact Or.inl hx
    · exact Or.inr (range_mono hx (by vomega) (le_refl _))

theorem varsChildren : ∀ (ps : List Pat), (∀ p ∈ ps, ∀ n fresh, VarsOk p n fresh) →
    ∀ (fresh : Nat) {vs : List Var} {as : List RAtom} {fr : Nat},
    atomsChildren ps fresh = (vs, as, fr) →
    fresh ≤ fr ∧ (∀ v ∈ vs, v ∈ Pat.varsList ps ∨ (fresh ≤ v ∧ v < fr)) ∧
      ∀ a ∈ as, ∀ x ∈ a.vars, x ∈ Pat.varsList ps ∨ (fresh ≤ x ∧ x < fr) := by
  intro ps
  induction ps with
  | nil =>
      intro _ fresh vs as fr h
      rw [atomsChildren_nil] at h
      simp at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨le_refl _, fun v hv => by simp at hv, fun a ha => by simp at ha⟩
  | cons p ps ih =>
      intro hps fresh vs as fr h
      rcases h₁ : atomsChild p fresh with ⟨v, ap, fr₁⟩
      rcases h₂ : atomsChildren ps fr₁ with ⟨vs', as', fr₂⟩
      rw [atomsChildren_cons p ps fresh h₁ h₂] at h
      simp at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      obtain ⟨hle₁, hv, hap⟩ := varsChild p (hps p (by simp)) fresh h₁
      obtain ⟨hle₂, hvs, has⟩ := ih (fun q hq => hps q (by simp [hq])) fr₁ h₂
      refine ⟨by vomega, ?_, ?_⟩
      · intro w hw
        rw [List.mem_cons] at hw
        rcases hw with rfl | hw
        · rcases hv with hv | hv
          · exact Or.inl (by simp [hv])
          · exact Or.inr (range_mono hv (le_refl _) hle₂)
        · rcases hvs w hw with hw | hw
          · exact Or.inl (by simp [hw])
          · exact Or.inr (range_mono hw hle₁ (le_refl _))
      · intro a ha x hx
        rw [List.mem_append] at ha
        rcases ha with ha | ha
        · rcases hap a ha x hx with hx | hx
          · exact Or.inl (by simp [hx])
          · exact Or.inr (range_mono hx (le_refl _) hle₂)
        · rcases has a ha x hx with hx | hx
          · exact Or.inl (by simp [hx])
          · exact Or.inr (range_mono hx hle₁ (le_refl _))

theorem varsChildrenAC : ∀ (es : List (Pat × Mult)), (∀ e ∈ es, ∀ n fresh, VarsOk e.1 n fresh) →
    ∀ (fresh : Nat) {vs : List (Var × Mult)} {as : List RAtom} {fr : Nat},
    atomsChildrenAC es fresh = (vs, as, fr) →
    fresh ≤ fr ∧ List.Forall₂ (fun e v => e.2 = v.2) es vs ∧
      (∀ v ∈ vs, v.1 ∈ Pat.varsElems es ∨ (fresh ≤ v.1 ∧ v.1 < fr)) ∧
      ∀ a ∈ as, ∀ x ∈ a.vars, x ∈ Pat.varsElems es ∨ (fresh ≤ x ∧ x < fr) := by
  intro es
  induction es with
  | nil =>
      intro _ fresh vs as fr h
      rw [atomsChildrenAC_nil] at h
      simp at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨le_refl _, List.Forall₂.nil, fun v hv => by simp at hv, fun a ha => by simp at ha⟩
  | cons e es ih =>
      intro hes fresh vs as fr h
      obtain ⟨p, μ⟩ := e
      rcases h₁ : atomsChild p fresh with ⟨v, ap, fr₁⟩
      rcases h₂ : atomsChildrenAC es fr₁ with ⟨vs', as', fr₂⟩
      rw [atomsChildrenAC_cons p μ es fresh h₁ h₂] at h
      simp at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      obtain ⟨hle₁, hv, hap⟩ := varsChild p (hes (p, μ) (by simp)) fresh h₁
      obtain ⟨hle₂, hf, hvs, has⟩ := ih (fun q hq => hes q (by simp [hq])) fr₁ h₂
      refine ⟨by vomega, List.Forall₂.cons rfl hf, ?_, ?_⟩
      · intro w hw
        rw [List.mem_cons] at hw
        rcases hw with rfl | hw
        · rcases hv with hv | hv
          · exact Or.inl (by simp [varsElems_cons, hv])
          · exact Or.inr (range_mono hv (le_refl _) hle₂)
        · rcases hvs w hw with hw | hw
          · exact Or.inl (by simp [varsElems_cons, hw])
          · exact Or.inr (range_mono hw hle₁ (le_refl _))
      · intro a ha x hx
        rw [List.mem_append] at ha
        rcases ha with ha | ha
        · rcases hap a ha x hx with hx | hx
          · exact Or.inl (by simp [varsElems_cons, hx])
          · exact Or.inr (range_mono hx (le_refl _) hle₂)
        · rcases has a ha x hx with hx | hx
          · exact Or.inl (by simp [varsElems_cons, hx])
          · exact Or.inr (range_mono hx hle₁ (le_refl _))

theorem varsOk_of_sub (P : Pat) (ih : ∀ p, sizeOf p < sizeOf P → ∀ n fresh, VarsOk p n fresh) :
    ∀ n fresh, VarsOk P n fresh := by
  intro n fresh
  cases P with
  | var x =>
      unfold VarsOk; rw [atomsAt_var]
      exact ⟨le_refl _, fun a ha => by simp at ha⟩
  | plain f args =>
      rcases h : atomsChildren args fresh with ⟨vs, as, fr⟩
      obtain ⟨hle, hvs, has⟩ := varsChildren args (fun p hp => ih p (sizeOf_lt_plain hp f)) fresh h
      unfold VarsOk; rw [atomsAt_plain f args n fresh h]; dsimp only
      refine ⟨hle, ?_⟩
      intro a ha x hx
      rw [List.mem_append, List.mem_singleton] at ha
      rcases ha with ha | rfl
      · have := has a ha x hx
        simp only [vars_plain]; tauto
      · have hvs' := hvs x
        simp only [RAtom.vars, RAtom.elems, RAtom.multVars, RAtom.restVars, RAtom.seqRestVars,
          RAtom.msetRestVars, RAtom.setRestVars, List.mem_cons, List.mem_append,
          List.not_mem_nil, or_false, List.append_nil, List.nil_append, vars_plain] at hx ⊢
        tauto
  | comm f p q =>
      rcases h₁ : atomsChild p fresh with ⟨vp, ap, fr₁⟩
      rcases h₂ : atomsChild q fr₁ with ⟨vq, aq, fr₂⟩
      obtain ⟨hle₁, hvp, hap⟩ := varsChild p (ih p (sizeOf_lt_comm_left f p q)) fresh h₁
      obtain ⟨hle₂, hvq, haq⟩ := varsChild q (ih q (sizeOf_lt_comm_right f p q)) fr₁ h₂
      unfold VarsOk; rw [atomsAt_comm f p q n fresh h₁ h₂]; dsimp only
      refine ⟨by vomega, ?_⟩
      intro a ha x hx
      simp only [List.mem_append, List.mem_singleton] at ha
      rcases ha with (ha | ha) | rfl
      · rcases hap a ha x hx with hx | hx
        · exact Or.inr (Or.inl (by simp [hx]))
        · exact Or.inr (Or.inr (range_mono hx (le_refl _) hle₂))
      · rcases haq a ha x hx with hx | hx
        · exact Or.inr (Or.inl (by simp [hx]))
        · exact Or.inr (Or.inr (range_mono hx hle₁ (le_refl _)))
      · simp only [RAtom.vars, RAtom.elems, RAtom.multVars, RAtom.restVars, RAtom.seqRestVars,
          RAtom.msetRestVars, RAtom.setRestVars, List.mem_cons, List.mem_append,
          List.not_mem_nil, or_false, List.append_nil, List.nil_append] at hx
        rcases hx with hx | hx | hx
        · exact Or.inl hx
        · rw [hx]
          rcases hvp with hvp | hvp
          · exact Or.inr (Or.inl (by simp [hvp]))
          · exact Or.inr (Or.inr (range_mono hvp (le_refl _) hle₂))
        · rw [hx]
          rcases hvq with hvq | hvq
          · exact Or.inr (Or.inl (by simp [hvq]))
          · exact Or.inr (Or.inr (range_mono hvq hle₁ (le_refl _)))
  | assoc f pre args suf =>
      rcases h : atomsChildren args fresh with ⟨vs, as, fr⟩
      obtain ⟨hle, hvs, has⟩ :=
        varsChildren args (fun p hp => ih p (sizeOf_lt_assoc hp f pre suf)) fresh h
      unfold VarsOk; rw [atomsAt_assoc f pre args suf n fresh h]; dsimp only
      refine ⟨hle, ?_⟩
      intro a ha x hx
      rw [List.mem_append, List.mem_singleton] at ha
      rcases ha with ha | rfl
      · have := has a ha x hx
        simp only [vars_assoc, List.mem_append]; tauto
      · have hvs' := hvs x
        simp only [RAtom.vars, RAtom.elems, RAtom.multVars, RAtom.restVars, RAtom.seqRestVars,
          RAtom.msetRestVars, RAtom.setRestVars, List.mem_cons, List.mem_append,
          List.not_mem_nil, or_false, List.append_nil, List.nil_append, vars_assoc] at hx ⊢
        tauto
  | ac f elems rest =>
      rcases h : atomsChildrenAC elems fresh with ⟨vs, as, fr⟩
      obtain ⟨hle, hf, hvs, has⟩ :=
        varsChildrenAC elems (fun e he => ih e.1 (sizeOf_lt_ac he f rest)) fresh h
      unfold VarsOk; rw [atomsAt_ac f elems rest n fresh h]; dsimp only
      refine ⟨hle, ?_⟩
      intro a ha x hx
      rw [List.mem_append, List.mem_singleton] at ha
      rcases ha with ha | rfl
      · have := has a ha x hx
        simp only [vars_ac, List.mem_append]; tauto
      · have hmult : x ∈ (RAtom.mk n f (.ac vs rest)).multVars → x ∈ Pat.varsElems elems := by
          rw [mem_multVars_ac]
          rintro ⟨v, hv, hx⟩
          obtain ⟨e, he, heq⟩ := forall₂_exists_left hf v hv
          exact mem_varsElems_of_mult he (heq ▸ hx)
        have hvs' : x ∈ vs.map (·.1) → x ∈ Pat.varsElems elems ∨ (fresh ≤ x ∧ x < fr) := by
          rw [List.mem_map]
          rintro ⟨v, hv, rfl⟩
          exact hvs v hv
        simp only [RAtom.vars, RAtom.elems, RAtom.restVars, RAtom.seqRestVars,
          RAtom.msetRestVars, RAtom.setRestVars, List.mem_cons, List.mem_append,
          List.not_mem_nil, or_false, List.append_nil, List.nil_append, vars_ac] at hx ⊢
        tauto
  | aci f elems rest =>
      rcases h : atomsChildren elems fresh with ⟨vs, as, fr⟩
      obtain ⟨hle, hvs, has⟩ :=
        varsChildren elems (fun p hp => ih p (sizeOf_lt_aci hp f rest)) fresh h
      unfold VarsOk; rw [atomsAt_aci f elems rest n fresh h]; dsimp only
      refine ⟨hle, ?_⟩
      intro a ha x hx
      rw [List.mem_append, List.mem_singleton] at ha
      rcases ha with ha | rfl
      · have := has a ha x hx
        simp only [vars_aci, List.mem_append]; tauto
      · have hvs' := hvs x
        simp only [RAtom.vars, RAtom.elems, RAtom.multVars, RAtom.restVars, RAtom.seqRestVars,
          RAtom.msetRestVars, RAtom.setRestVars, List.mem_cons, List.mem_append,
          List.not_mem_nil, or_false, List.append_nil, List.nil_append, vars_aci] at hx ⊢
        tauto

theorem varsOk_all : ∀ (k : Nat) (P : Pat), sizeOf P = k → ∀ n fresh, VarsOk P n fresh := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
      intro P hP
      exact varsOk_of_sub P (fun p hp => ih _ (hP ▸ hp) p rfl)

theorem varsOk (P : Pat) (n : Var) (fresh : Nat) : VarsOk P n fresh := varsOk_all _ P rfl _ _

/-! ## Atoms satisfied implies match -/

theorem matchC_var_iff {G : Graph} {x : Var} {c : C} {σ : Binding} :
    MatchC G (.var x) c σ ↔ σ.cls x = some c := by
  constructor
  · intro h
    cases h with
    | var h => exact h
    | app _ _ hh _ => simp [Pat.head] at hh
  · exact MatchC.var

theorem zip_map_left_mem {α β γ : Type} {g : α → β} {l₁ : List α} {l₂ : List γ} {ac : α × γ}
    (h : ac ∈ l₁.zip l₂) : (g ac.1, ac.2) ∈ (l₁.map g).zip l₂ := by
  rw [List.zip_map_left, List.mem_map]; exact ⟨ac, h, rfl⟩

theorem mem_zip_map_left {α β γ : Type} {g : α → β} {l₁ : List α} {l₂ : List γ} {et : β × γ}
    (h : et ∈ (l₁.map g).zip l₂) : ∃ ac ∈ l₁.zip l₂, et = (g ac.1, ac.2) := by
  rw [List.zip_map_left, List.mem_map] at h
  obtain ⟨ac, hac, rfl⟩ := h
  exact ⟨ac, hac, rfl⟩

theorem forall₂_comp {α β γ : Type} {R : α → β → Prop} {S : β → γ → Prop} :
    ∀ {l₁ : List α} {l₂ : List β} {l₃ : List γ}, List.Forall₂ R l₁ l₂ → List.Forall₂ S l₂ l₃ →
    List.Forall₂ (fun a c => ∃ b, R a b ∧ S b c) l₁ l₃ := by
  intro l₁ l₂ l₃ h₁
  induction h₁ generalizing l₃ with
  | nil => intro h₂; cases h₂; exact .nil
  | cons hab h ih =>
      intro h₂
      cases h₂ with
      | cons hbc h' => exact .cons ⟨_, hab, hbc⟩ (ih h')

theorem forall₂_cls_of_map_var {G : Graph} {σ : Binding} {vs : List Var} {cs : List C}
    (hl : (vs.map Pat.var).length = cs.length)
    (hall : ∀ pc ∈ (vs.map Pat.var).zip cs, MatchC G pc.1 pc.2 σ) :
    List.Forall₂ (fun v c => σ.cls v = some c) vs cs :=
  List.forall₂_iff_zip.2 ⟨by simpa using hl,
    fun hvc => matchC_var_iff.1 (hall _ (zip_map_left_mem hvc))⟩

theorem forall₂_cls_of_map_var_ac {G : Graph} {σ : Binding} {vs : List (Var × Mult)}
    {cs : List C} (hl : (vs.map fun e => (Pat.var e.1, e.2)).length = cs.length)
    (hall : ∀ pc ∈ (vs.map fun e => (Pat.var e.1, e.2)).zip cs, MatchC G pc.1.1 pc.2 σ) :
    List.Forall₂ (fun v c => σ.cls v.1 = some c) vs cs :=
  List.forall₂_iff_zip.2 ⟨by simpa using hl,
    fun hvc => matchC_var_iff.1 (hall _ (zip_map_left_mem hvc))⟩

/-- Backward direction, generalized: if every atom of `P` at `n` is
satisfied, `n` is bound to a stored node of `P`'s head that `P` matches. -/
def BackOk (G : Graph) (σ : Binding) (P : Pat) : Prop :=
  P.head.isSome = true → ∀ (n : Var) (fresh : Nat),
    (∀ a ∈ (atomsAt P n fresh).1, AtomSat G σ a) →
    ∃ id nd, σ.node n = some id ∧ (id, nd) ∈ G.nodes ∧ σ.cls n = some (G.find id) ∧
      P.head = some nd.op ∧ MatchN G P nd σ

theorem backChild {G : Graph} {σ : Binding} (p : Pat) (hp : BackOk G σ p) (fresh : Nat)
    {v : Var} {ap : List RAtom} {fr : Nat} (h : atomsChild p fresh = (v, ap, fr))
    (hs : ∀ a ∈ ap, AtomSat G σ a) : ∀ c, σ.cls v = some c → MatchC G p c σ := by
  intro c hc
  rcases atomsChild_spec p fresh h with ⟨x, rfl, rfl, rfl, rfl⟩ | ⟨hh, rfl, h'⟩
  · exact .var hc
  · obtain ⟨id, nd, hnode, hmem, hcls, hop, hm⟩ := hp hh v (v + 1) (by rw [h']; exact hs)
    rw [hcls] at hc
    exact .app hmem (Option.some.inj hc) hop hm

theorem backChildren {G : Graph} {σ : Binding} : ∀ (ps : List Pat), (∀ p ∈ ps, BackOk G σ p) →
    ∀ (fresh : Nat) {vs : List Var} {as : List RAtom} {fr : Nat},
    atomsChildren ps fresh = (vs, as, fr) → (∀ a ∈ as, AtomSat G σ a) →
    ∀ cs, List.Forall₂ (fun v c => σ.cls v = some c) vs cs →
    List.Forall₂ (fun p c => MatchC G p c σ) ps cs := by
  intro ps
  induction ps with
  | nil =>
      intro _ fresh vs as fr h _ cs hf
      rw [atomsChildren_nil] at h
      simp at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      cases hf; exact .nil
  | cons p ps ih =>
      intro hps fresh vs as fr h hs cs hf
      rcases h₁ : atomsChild p fresh with ⟨v, ap, fr₁⟩
      rcases h₂ : atomsChildren ps fr₁ with ⟨vs', as', fr₂⟩
      rw [atomsChildren_cons p ps fresh h₁ h₂] at h
      simp at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      cases hf with
      | cons hvc hf' =>
          exact .cons
            (backChild p (hps p (by simp)) fresh h₁ (fun a ha => hs a (by simp [ha])) _ hvc)
            (ih (fun q hq => hps q (by simp [hq])) fr₁ h₂ (fun a ha => hs a (by simp [ha])) _ hf')

theorem backChildrenAC {G : Graph} {σ : Binding} : ∀ (es : List (Pat × Mult)),
    (∀ e ∈ es, BackOk G σ e.1) →
    ∀ (fresh : Nat) {vs : List (Var × Mult)} {as : List RAtom} {fr : Nat},
    atomsChildrenAC es fresh = (vs, as, fr) → (∀ a ∈ as, AtomSat G σ a) →
    ∀ cs, List.Forall₂ (fun v c => σ.cls v.1 = some c) vs cs →
    List.Forall₂ (fun e c => MatchC G e.1 c σ) es cs := by
  intro es
  induction es with
  | nil =>
      intro _ fresh vs as fr h _ cs hf
      rw [atomsChildrenAC_nil] at h
      simp at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      cases hf; exact .nil
  | cons e es ih =>
      intro hes fresh vs as fr h hs cs hf
      obtain ⟨p, μ⟩ := e
      rcases h₁ : atomsChild p fresh with ⟨v, ap, fr₁⟩
      rcases h₂ : atomsChildrenAC es fr₁ with ⟨vs', as', fr₂⟩
      rw [atomsChildrenAC_cons p μ es fresh h₁ h₂] at h
      simp at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      cases hf with
      | cons hvc hf' =>
          exact .cons
            (backChild p (hes (p, μ) (by simp)) fresh h₁ (fun a ha => hs a (by simp [ha])) _ hvc)
            (ih (fun q hq => hes q (by simp [hq])) fr₁ h₂ (fun a ha => hs a (by simp [ha])) _ hf')

theorem back_of_sub {G : Graph} {σ : Binding} (P : Pat)
    (ih : ∀ p, sizeOf p < sizeOf P → BackOk G σ p) : BackOk G σ P := by
  intro hP n fresh hs
  cases P with
  | var x => simp [Pat.head] at hP
  | plain f args =>
      rcases h : atomsChildren args fresh with ⟨vs, as, fr⟩
      rw [atomsAt_plain f args n fresh h] at hs
      dsimp only at hs
      obtain ⟨id, nd, hnode, hmem, hcls, hop, hm⟩ := hs ⟨n, f, .plain vs⟩ (by simp)
      simp only [RAtom.shallow] at hm
      cases hm with
      | @plain _ _ cs _ hl hall =>
          have hm' := backChildren args (fun p hp => ih p (sizeOf_lt_plain hp f)) fresh h
            (fun a ha => hs a (by simp [ha])) _ (forall₂_cls_of_map_var hl hall)
          exact ⟨id, _, hnode, hmem, hcls, rfl,
            .plain (List.Forall₂.length_eq hm') (fun pc hpc => (List.forall₂_iff_zip.1 hm').2 hpc)⟩
  | comm f p q =>
      rcases h₁ : atomsChild p fresh with ⟨vp, ap, fr₁⟩
      rcases h₂ : atomsChild q fr₁ with ⟨vq, aq, fr₂⟩
      rw [atomsAt_comm f p q n fresh h₁ h₂] at hs
      dsimp only at hs
      obtain ⟨id, nd, hnode, hmem, hcls, hop, hm⟩ := hs ⟨n, f, .comm vp vq⟩ (by simp)
      simp only [RAtom.shallow] at hm
      have hp' := backChild p (ih p (sizeOf_lt_comm_left f p q)) fresh h₁
        (fun a ha => hs a (by simp [ha]))
      have hq' := backChild q (ih q (sizeOf_lt_comm_right f p q)) fr₁ h₂
        (fun a ha => hs a (by simp [ha]))
      cases hm with
      | comm₁ hp hq =>
          exact ⟨id, _, hnode, hmem, hcls, rfl,
            .comm₁ (hp' _ (matchC_var_iff.1 hp)) (hq' _ (matchC_var_iff.1 hq))⟩
      | comm₂ hp hq =>
          exact ⟨id, _, hnode, hmem, hcls, rfl,
            .comm₂ (hp' _ (matchC_var_iff.1 hp)) (hq' _ (matchC_var_iff.1 hq))⟩
  | assoc f pre args suf =>
      rcases h : atomsChildren args fresh with ⟨vs, as, fr⟩
      rw [atomsAt_assoc f pre args suf n fresh h] at hs
      dsimp only at hs
      obtain ⟨id, nd, hnode, hmem, hcls, hop, hm⟩ := hs ⟨n, f, .assoc pre vs suf⟩ (by simp)
      simp only [RAtom.shallow] at hm
      cases hm with
      | @assoc _ _ _ _ u mid v _ hl hpre hsuf hall =>
          have hm' := backChildren args (fun p hp => ih p (sizeOf_lt_assoc hp f pre suf)) fresh h
            (fun a ha => hs a (by simp [ha])) _ (forall₂_cls_of_map_var hl hall)
          exact ⟨id, _, hnode, hmem, hcls, rfl,
            .assoc (List.Forall₂.length_eq hm') hpre hsuf
              (fun pc hpc => (List.forall₂_iff_zip.1 hm').2 hpc)⟩
  | ac f elems rest =>
      rcases h : atomsChildrenAC elems fresh with ⟨vs, as, fr⟩
      rw [atomsAt_ac f elems rest n fresh h] at hs
      dsimp only at hs
      obtain ⟨id, nd, hnode, hmem, hcls, hop, hm⟩ := hs ⟨n, f, .ac vs rest⟩ (by simp)
      simp only [RAtom.shallow] at hm
      obtain ⟨-, hf, -, -⟩ := varsChildrenAC elems (fun e _ => varsOk e.1) fresh h
      cases hm with
      | @ac _ _ _ m taken _ hnd hl hmem' hall hmult hrest =>
          have hm' := backChildrenAC elems (fun e he => ih e.1 (sizeOf_lt_ac he f rest)) fresh h
            (fun a ha => hs a (by simp [ha])) _ (forall₂_cls_of_map_var_ac hl hall)
          refine ⟨id, _, hnode, hmem, hcls, rfl,
            .ac hnd (List.Forall₂.length_eq hm') hmem'
              (fun et het => (List.forall₂_iff_zip.1 hm').2 het) ?_ hrest⟩
          intro et het
          obtain ⟨et', het', h12, h2⟩ := zip_transfer hf taken et het
          rw [h12, h2]
          exact hmult _ (zip_map_left_mem het')
  | aci f elems rest =>
      rcases h : atomsChildren elems fresh with ⟨vs, as, fr⟩
      rw [atomsAt_aci f elems rest n fresh h] at hs
      dsimp only at hs
      obtain ⟨id, nd, hnode, hmem, hcls, hop, hm⟩ := hs ⟨n, f, .aci vs rest⟩ (by simp)
      simp only [RAtom.shallow] at hm
      cases hm with
      | @aci _ _ _ s taken _ hnd hl hmem' hall hrest =>
          have hm' := backChildren elems (fun p hp => ih p (sizeOf_lt_aci hp f rest)) fresh h
            (fun a ha => hs a (by simp [ha])) _ (forall₂_cls_of_map_var hl hall)
          exact ⟨id, _, hnode, hmem, hcls, rfl,
            .aci hnd (List.Forall₂.length_eq hm') hmem'
              (fun et het => (List.forall₂_iff_zip.1 hm').2 het) hrest⟩

theorem back_all {G : Graph} {σ : Binding} : ∀ (k : Nat) (P : Pat), sizeOf P = k → BackOk G σ P := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
      intro P hP
      exact back_of_sub P (fun p hp => ih _ (hP ▸ hp) p rfl)

theorem backOk {G : Graph} {σ : Binding} (P : Pat) : BackOk G σ P := back_all _ P rfl

/-! ## Match implies atoms satisfied -/

theorem ne_of_mem_or_range {x n fresh fr : Nat} {V : List Var}
    (hx : x ∈ V ∨ (fresh ≤ x ∧ x < fr)) (hn : n < fresh) (hnv : n ∉ V) : x ≠ n := by
  rintro rfl
  rcases hx with hx | hx
  · exact hnv hx
  · vomega

/-- Forward direction, generalized: a match of `P` at a stored node extends
(on `n` and the fresh range) to a binding satisfying the atoms of `P` at `n`. -/
def FwdOk (G : Graph) (P : Pat) : Prop :=
  ∀ (σ : Binding) (id : NodeId) (nd : Node) (n : Var) (fresh : Nat),
    (id, nd) ∈ G.nodes → MatchN G P nd σ → (∀ x ∈ P.vars, x < fresh) → n < fresh →
    n ∉ P.vars →
    ∃ σ', Keeps (fun v => v ≠ n ∧ (v < fresh ∨ (atomsAt P n fresh).2 ≤ v)) σ σ' ∧
      σ'.node n = some id ∧ σ'.cls n = some (G.find id) ∧
      ∀ a ∈ (atomsAt P n fresh).1, AtomSat G σ' a

theorem fwdChild {G : Graph} (p : Pat) (hp : FwdOk G p) (fresh : Nat) {v : Var}
    {ap : List RAtom} {fr : Nat} (h : atomsChild p fresh = (v, ap, fr)) (σ : Binding) (c : C)
    (hm : MatchC G p c σ) (hlt : ∀ x ∈ p.vars, x < fresh) :
    ∃ σ', Keeps (fun w => w < fresh ∨ fr ≤ w) σ σ' ∧ σ'.cls v = some c ∧
      ∀ a ∈ ap, AtomSat G σ' a := by
  rcases atomsChild_spec p fresh h with ⟨x, rfl, rfl, rfl, rfl⟩ | ⟨hh, rfl, h'⟩
  · exact ⟨σ, Keeps.refl _ _, matchC_var_iff.1 hm, fun a ha => by simp at ha⟩
  · have hle := (varsOk p v (v + 1)).1
    rw [h'] at hle
    dsimp only at hle
    cases hm with
    | var hx => simp [Pat.head] at hh
    | app hmem hf hhead hn =>
        obtain ⟨σ', hk, hnode, hcls, hs⟩ := hp σ _ _ v (v + 1) hmem hn
          (fun x hx => by have := hlt x hx; vomega) (by vomega)
          (fun hv => by have := hlt v hv; vomega)
        rw [h'] at hk hs
        dsimp only at hk hs
        refine ⟨σ', hk.mono ?_, by rw [hcls, hf], hs⟩
        intro w hw
        rcases hw with hw | hw
        · exact ⟨by vomega, Or.inl (by vomega)⟩
        · exact ⟨by vomega, Or.inr hw⟩

theorem fwdChildren {G : Graph} : ∀ (ps : List Pat), (∀ p ∈ ps, FwdOk G p) →
    ∀ (fresh : Nat) {vs : List Var} {as : List RAtom} {fr : Nat},
    atomsChildren ps fresh = (vs, as, fr) →
    ∀ (σ : Binding) (cs : List C), List.Forall₂ (fun p c => MatchC G p c σ) ps cs →
    (∀ x ∈ Pat.varsList ps, x < fresh) →
    ∃ σ', Keeps (fun w => w < fresh ∨ fr ≤ w) σ σ' ∧
      List.Forall₂ (fun v c => σ'.cls v = some c) vs cs ∧ ∀ a ∈ as, AtomSat G σ' a := by
  intro ps
  induction ps with
  | nil =>
      intro _ fresh vs as fr h σ cs hf _
      rw [atomsChildren_nil] at h
      simp at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      cases hf
      exact ⟨σ, Keeps.refl _ _, .nil, fun a ha => by simp at ha⟩
  | cons p ps ih =>
      intro hps fresh vs as fr h σ cs hf hlt
      rcases h₁ : atomsChild p fresh with ⟨v, ap, fr₁⟩
      rcases h₂ : atomsChildren ps fr₁ with ⟨vs', as', fr₂⟩
      rw [atomsChildren_cons p ps fresh h₁ h₂] at h
      simp at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      cases hf with
      | @cons _ c _ cs' hpc hf' =>
          obtain ⟨hle₁, hv, hap⟩ := varsChild p (fun n fr => varsOk p n fr) fresh h₁
          obtain ⟨hle₂, -, -⟩ := varsChildren ps (fun q _ n fr => varsOk q n fr) fr₁ h₂
          obtain ⟨σ₁, hk₁, hc₁, hs₁⟩ := fwdChild p (hps p (by simp)) fresh h₁ σ c hpc
            (fun x hx => hlt x (by simp [hx]))
          have hf₁ : List.Forall₂ (fun p c => MatchC G p c σ₁) ps cs' :=
            List.forall₂_iff_zip.2 ⟨hf'.length_eq, fun hqc =>
              MatchC_agree ((List.forall₂_iff_zip.1 hf').2 hqc)
                (hk₁.agreeOn (fun x hx => Or.inl (hlt x
                  (by simp [mem_varsList_of_mem (List.of_mem_zip hqc).1 hx]))))⟩
          obtain ⟨σ₂, hk₂, hf₂, hs₂⟩ := ih (fun q hq => hps q (by simp [hq])) fr₁ h₂ σ₁ cs' hf₁
            (fun x hx => by have := hlt x (by simp [hx]); vomega)
          have hkeep : ∀ x, x ∈ p.vars ∨ (fresh ≤ x ∧ x < fr₁) → x < fr₁ ∨ fr₂ ≤ x := by
            intro x hx
            rcases hx with hx | hx
            · have := hlt x (by simp [hx]); exact Or.inl (by vomega)
            · exact Or.inl hx.2
          refine ⟨σ₂, (hk₁.trans hk₂).mono ?_, .cons ?_ hf₂, ?_⟩
          · intro w hw
            rcases hw with hw | hw
            · exact ⟨Or.inl hw, Or.inl (by vomega)⟩
            · exact ⟨Or.inr (by vomega), Or.inr hw⟩
          · rw [← hc₁]; exact (hk₂.1 v (hkeep v hv)).2
          · intro a ha
            rw [List.mem_append] at ha
            rcases ha with ha | ha
            · exact AtomSat.keeps hk₂ (fun x hx => hkeep x (hap a ha x hx)) (hs₁ a ha)
            · exact hs₂ a ha

theorem fwdChildrenAC {G : Graph} : ∀ (es : List (Pat × Mult)), (∀ e ∈ es, FwdOk G e.1) →
    ∀ (fresh : Nat) {vs : List (Var × Mult)} {as : List RAtom} {fr : Nat},
    atomsChildrenAC es fresh = (vs, as, fr) →
    ∀ (σ : Binding) (cs : List C), List.Forall₂ (fun e c => MatchC G e.1 c σ) es cs →
    (∀ x ∈ Pat.varsElems es, x < fresh) →
    ∃ σ', Keeps (fun w => w < fresh ∨ fr ≤ w) σ σ' ∧
      List.Forall₂ (fun v c => σ'.cls v.1 = some c) vs cs ∧ ∀ a ∈ as, AtomSat G σ' a := by
  intro es
  induction es with
  | nil =>
      intro _ fresh vs as fr h σ cs hf _
      rw [atomsChildrenAC_nil] at h
      simp at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      cases hf
      exact ⟨σ, Keeps.refl _ _, .nil, fun a ha => by simp at ha⟩
  | cons e es ih =>
      intro hes fresh vs as fr h σ cs hf hlt
      obtain ⟨p, μ⟩ := e
      rcases h₁ : atomsChild p fresh with ⟨v, ap, fr₁⟩
      rcases h₂ : atomsChildrenAC es fr₁ with ⟨vs', as', fr₂⟩
      rw [atomsChildrenAC_cons p μ es fresh h₁ h₂] at h
      simp at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      cases hf with
      | @cons _ c _ cs' hpc hf' =>
          obtain ⟨hle₁, hv, hap⟩ := varsChild p (fun n fr => varsOk p n fr) fresh h₁
          obtain ⟨hle₂, -, -, -⟩ := varsChildrenAC es (fun q _ n fr => varsOk q.1 n fr) fr₁ h₂
          obtain ⟨σ₁, hk₁, hc₁, hs₁⟩ := fwdChild p (hes (p, μ) (by simp)) fresh h₁ σ c hpc
            (fun x hx => hlt x (by simp [varsElems_cons, hx]))
          have hf₁ : List.Forall₂ (fun e c => MatchC G e.1 c σ₁) es cs' :=
            List.forall₂_iff_zip.2 ⟨hf'.length_eq, fun hqc =>
              MatchC_agree ((List.forall₂_iff_zip.1 hf').2 hqc)
                (hk₁.agreeOn (fun x hx => Or.inl (hlt x
                  (by simp [varsElems_cons, mem_varsElems_of_mem (List.of_mem_zip hqc).1 hx]))))⟩
          obtain ⟨σ₂, hk₂, hf₂, hs₂⟩ := ih (fun q hq => hes q (by simp [hq])) fr₁ h₂ σ₁ cs' hf₁
            (fun x hx => by have := hlt x (by simp [varsElems_cons, hx]); vomega)
          have hkeep : ∀ x, x ∈ p.vars ∨ (fresh ≤ x ∧ x < fr₁) → x < fr₁ ∨ fr₂ ≤ x := by
            intro x hx
            rcases hx with hx | hx
            · have := hlt x (by simp [varsElems_cons, hx]); exact Or.inl (by vomega)
            · exact Or.inl hx.2
          refine ⟨σ₂, (hk₁.trans hk₂).mono ?_, .cons ?_ hf₂, ?_⟩
          · intro w hw
            rcases hw with hw | hw
            · exact ⟨Or.inl hw, Or.inl (by vomega)⟩
            · exact ⟨Or.inr (by vomega), Or.inr hw⟩
          · rw [← hc₁]; exact (hk₂.1 v (hkeep v hv)).2
          · intro a ha
            rw [List.mem_append] at ha
            rcases ha with ha | ha
            · exact AtomSat.keeps hk₂ (fun x hx => hkeep x (hap a ha x hx)) (hs₁ a ha)
            · exact hs₂ a ha

/-- The two children of a commutative application, processed left to right. -/
theorem fwdComm {G : Graph} (p q : Pat) (hp : FwdOk G p) (hq : FwdOk G q) (fresh : Nat)
    {vp vq : Var} {ap aq : List RAtom} {fr₁ fr₂ : Nat}
    (h₁ : atomsChild p fresh = (vp, ap, fr₁)) (h₂ : atomsChild q fr₁ = (vq, aq, fr₂))
    (σ : Binding) (a b : C) (hma : MatchC G p a σ) (hmb : MatchC G q b σ)
    (hlt : ∀ x ∈ p.vars ++ q.vars, x < fresh) :
    ∃ σ', Keeps (fun w => w < fresh ∨ fr₂ ≤ w) σ σ' ∧ σ'.cls vp = some a ∧ σ'.cls vq = some b ∧
      ∀ a ∈ ap ++ aq, AtomSat G σ' a := by
  obtain ⟨hle₁, hvp, hap⟩ := varsChild p (fun n fr => varsOk p n fr) fresh h₁
  obtain ⟨hle₂, hvq, haq⟩ := varsChild q (fun n fr => varsOk q n fr) fr₁ h₂
  obtain ⟨σ₁, hk₁, hc₁, hs₁⟩ := fwdChild p hp fresh h₁ σ a hma (fun x hx => hlt x (by simp [hx]))
  have hmb₁ : MatchC G q b σ₁ :=
    MatchC_agree hmb (hk₁.agreeOn (fun x hx => Or.inl (hlt x (by simp [hx]))))
  obtain ⟨σ₂, hk₂, hc₂, hs₂⟩ := fwdChild q hq fr₁ h₂ σ₁ b hmb₁
    (fun x hx => by have := hlt x (by simp [hx]); vomega)
  have hkeep : ∀ x, x ∈ p.vars ∨ (fresh ≤ x ∧ x < fr₁) → x < fr₁ ∨ fr₂ ≤ x := by
    intro x hx
    rcases hx with hx | hx
    · have := hlt x (by simp [hx]); exact Or.inl (by vomega)
    · exact Or.inl hx.2
  refine ⟨σ₂, (hk₁.trans hk₂).mono ?_, ?_, hc₂, ?_⟩
  · intro w hw
    rcases hw with hw | hw
    · exact ⟨Or.inl hw, Or.inl (by vomega)⟩
    · exact ⟨Or.inr (by vomega), Or.inr hw⟩
  · rw [← hc₁]; exact (hk₂.1 vp (hkeep vp hvp)).2
  · intro a ha
    rw [List.mem_append] at ha
    rcases ha with ha | ha
    · exact AtomSat.keeps hk₂ (fun x hx => hkeep x (hap a ha x hx)) (hs₁ a ha)
    · exact hs₂ a ha

theorem fwd_of_sub {G : Graph} (P : Pat) (ih : ∀ p, sizeOf p < sizeOf P → FwdOk G p) :
    FwdOk G P := by
  intro σ id nd n fresh hmem hm hlt hn hnv
  cases P with
  | var x => cases hm
  | plain f args =>
      rcases h : atomsChildren args fresh with ⟨vs, as, fr⟩
      obtain ⟨hle, hvs, has⟩ := varsChildren args (fun p _ n fr => varsOk p n fr) fresh h
      have hlt' : ∀ x ∈ Pat.varsList args, x < fresh := fun x hx => hlt x (by simpa using hx)
      have hnv' : n ∉ Pat.varsList args := fun hx => hnv (by simpa using hx)
      cases hm with
      | @plain _ _ cs _ hl hall =>
          obtain ⟨σ₁, hk₁, hf₁, hs₁⟩ := fwdChildren args (fun p hp => ih p (sizeOf_lt_plain hp f))
            fresh h σ cs (List.forall₂_iff_zip.2 ⟨hl, fun hpc => hall _ hpc⟩) hlt'
          have hk₂ := keeps_bindNode σ₁ n id (G.find id)
          rw [atomsAt_plain f args n fresh h]; dsimp only
          refine ⟨bindNode σ₁ n id (G.find id), (hk₁.trans hk₂).mono (fun w hw => ⟨hw.2, hw.1⟩),
            bindNode_node_self .., bindNode_cls_self .., ?_⟩
          intro a ha
          rw [List.mem_append, List.mem_singleton] at ha
          rcases ha with ha | rfl
          · exact AtomSat.keeps hk₂ (fun x hx => ne_of_mem_or_range (has a ha x hx) hn hnv')
              (hs₁ a ha)
          · refine ⟨id, ⟨f, .tuple cs⟩, bindNode_node_self .., hmem, bindNode_cls_self .., rfl, ?_⟩
            simp only [RAtom.shallow]
            refine MatchN.plain (by simpa using hf₁.length_eq) ?_
            intro pc hpc
            obtain ⟨vc, hvc, rfl⟩ := mem_zip_map_left hpc
            refine MatchC.var ?_
            rw [← (List.forall₂_iff_zip.1 hf₁).2 hvc]
            exact (hk₂.1 vc.1 (ne_of_mem_or_range (hvs vc.1 (List.of_mem_zip hvc).1) hn hnv')).2
  | comm f p q =>
      rcases h₁ : atomsChild p fresh with ⟨vp, ap, fr₁⟩
      rcases h₂ : atomsChild q fr₁ with ⟨vq, aq, fr₂⟩
      obtain ⟨hle₁, hvp, hap⟩ := varsChild p (fun n fr => varsOk p n fr) fresh h₁
      obtain ⟨hle₂, hvq, haq⟩ := varsChild q (fun n fr => varsOk q n fr) fr₁ h₂
      have hlt' : ∀ x ∈ p.vars ++ q.vars, x < fresh := fun x hx => hlt x (by simpa using hx)
      have hnv' : n ∉ p.vars ++ q.vars := fun hx => hnv (by simpa using hx)
      have hvp' : vp ∈ p.vars ++ q.vars ∨ (fresh ≤ vp ∧ vp < fr₂) := by
        rcases hvp with hvp | hvp
        · exact Or.inl (by simp [hvp])
        · exact Or.inr (range_mono hvp (le_refl _) hle₂)
      have hvq' : vq ∈ p.vars ++ q.vars ∨ (fresh ≤ vq ∧ vq < fr₂) := by
        rcases hvq with hvq | hvq
        · exact Or.inl (by simp [hvq])
        · exact Or.inr (range_mono hvq hle₁ (le_refl _))
      have hvars : ∀ a ∈ ap ++ aq, ∀ x ∈ a.vars, x ∈ p.vars ++ q.vars ∨ (fresh ≤ x ∧ x < fr₂) := by
        intro a ha x hx
        rw [List.mem_append] at ha
        rcases ha with ha | ha
        · rcases hap a ha x hx with hx | hx
          · exact Or.inl (by simp [hx])
          · exact Or.inr (range_mono hx (le_refl _) hle₂)
        · rcases haq a ha x hx with hx | hx
          · exact Or.inl (by simp [hx])
          · exact Or.inr (range_mono hx hle₁ (le_refl _))
      rw [atomsAt_comm f p q n fresh h₁ h₂]; dsimp only
      cases hm with
      | @comm₁ _ _ _ a b _ hma hmb =>
          obtain ⟨σ₁, hk₁, hca, hcb, hs₁⟩ := fwdComm p q (ih p (sizeOf_lt_comm_left f p q))
            (ih q (sizeOf_lt_comm_right f p q)) fresh h₁ h₂ σ a b hma hmb hlt'
          have hk₂ := keeps_bindNode σ₁ n id (G.find id)
          refine ⟨bindNode σ₁ n id (G.find id), (hk₁.trans hk₂).mono (fun w hw => ⟨hw.2, hw.1⟩),
            bindNode_node_self .., bindNode_cls_self .., ?_⟩
          intro a' ha
          rw [List.mem_append, List.mem_singleton] at ha
          rcases ha with ha | rfl
          · exact AtomSat.keeps hk₂ (fun x hx => ne_of_mem_or_range (hvars a' ha x hx) hn hnv')
              (hs₁ a' ha)
          · refine ⟨id, ⟨f, .spair a b⟩, bindNode_node_self .., hmem, bindNode_cls_self .., rfl, ?_⟩
            simp only [RAtom.shallow]
            refine MatchN.comm₁ (MatchC.var ?_) (MatchC.var ?_)
            · rw [← hca]; exact (hk₂.1 vp (ne_of_mem_or_range hvp' hn hnv')).2
            · rw [← hcb]; exact (hk₂.1 vq (ne_of_mem_or_range hvq' hn hnv')).2
      | @comm₂ _ _ _ a b _ hmb hma =>
          obtain ⟨σ₁, hk₁, hcb, hca, hs₁⟩ := fwdComm p q (ih p (sizeOf_lt_comm_left f p q))
            (ih q (sizeOf_lt_comm_right f p q)) fresh h₁ h₂ σ b a hmb hma hlt'
          have hk₂ := keeps_bindNode σ₁ n id (G.find id)
          refine ⟨bindNode σ₁ n id (G.find id), (hk₁.trans hk₂).mono (fun w hw => ⟨hw.2, hw.1⟩),
            bindNode_node_self .., bindNode_cls_self .., ?_⟩
          intro a' ha
          rw [List.mem_append, List.mem_singleton] at ha
          rcases ha with ha | rfl
          · exact AtomSat.keeps hk₂ (fun x hx => ne_of_mem_or_range (hvars a' ha x hx) hn hnv')
              (hs₁ a' ha)
          · refine ⟨id, ⟨f, .spair a b⟩, bindNode_node_self .., hmem, bindNode_cls_self .., rfl, ?_⟩
            simp only [RAtom.shallow]
            refine MatchN.comm₂ (MatchC.var ?_) (MatchC.var ?_)
            · rw [← hcb]; exact (hk₂.1 vp (ne_of_mem_or_range hvp' hn hnv')).2
            · rw [← hca]; exact (hk₂.1 vq (ne_of_mem_or_range hvq' hn hnv')).2
  | assoc f pre args suf =>
      rcases h : atomsChildren args fresh with ⟨vs, as, fr⟩
      obtain ⟨hle, hvs, has⟩ := varsChildren args (fun p _ n fr => varsOk p n fr) fresh h
      have hlt' : ∀ x ∈ Pat.varsList args, x < fresh := fun x hx => hlt x (by simp [hx])
      have hnv' : n ∉ Pat.varsList args := fun hx => hnv (by simp [hx])
      cases hm with
      | @assoc _ _ _ _ u mid v _ hl hpre hsuf hall =>
          obtain ⟨σ₁, hk₁, hf₁, hs₁⟩ := fwdChildren args
            (fun p hp => ih p (sizeOf_lt_assoc hp f pre suf))
            fresh h σ mid (List.forall₂_iff_zip.2 ⟨hl, fun hpc => hall _ hpc⟩) hlt'
          have hk₂ := keeps_bindNode σ₁ n id (G.find id)
          have hk := hk₁.trans hk₂
          rw [atomsAt_assoc f pre args suf n fresh h]; dsimp only
          refine ⟨bindNode σ₁ n id (G.find id), hk.mono (fun w hw => ⟨hw.2, hw.1⟩),
            bindNode_node_self .., bindNode_cls_self .., ?_⟩
          intro a ha
          rw [List.mem_append, List.mem_singleton] at ha
          rcases ha with ha | rfl
          · exact AtomSat.keeps hk₂ (fun x hx => ne_of_mem_or_range (has a ha x hx) hn hnv')
              (hs₁ a ha)
          · refine ⟨id, ⟨f, .seq (u ++ mid ++ v)⟩, bindNode_node_self .., hmem,
              bindNode_cls_self .., rfl, ?_⟩
            simp only [RAtom.shallow]
            refine MatchN.assoc (by simpa using hf₁.length_eq)
              (hpre.agree (fun x _ => by rw [hk.2.2.2.1]))
              (hsuf.agree (fun x _ => by rw [hk.2.2.2.1])) ?_
            intro pc hpc
            obtain ⟨vc, hvc, rfl⟩ := mem_zip_map_left hpc
            refine MatchC.var ?_
            rw [← (List.forall₂_iff_zip.1 hf₁).2 hvc]
            exact (hk₂.1 vc.1 (ne_of_mem_or_range (hvs vc.1 (List.of_mem_zip hvc).1) hn hnv')).2
  | ac f elems rest =>
      rcases h : atomsChildrenAC elems fresh with ⟨vs, as, fr⟩
      obtain ⟨hle, hf, hvs, has⟩ := varsChildrenAC elems (fun e _ n fr => varsOk e.1 n fr) fresh h
      have hlt' : ∀ x ∈ Pat.varsElems elems, x < fresh := fun x hx => hlt x (by simp [hx])
      have hnv' : n ∉ Pat.varsElems elems := fun hx => hnv (by simp [hx])
      cases hm with
      | @ac _ _ _ m taken _ hnd hl hmem' hall hmult hrest =>
          obtain ⟨σ₁, hk₁, hf₁, hs₁⟩ := fwdChildrenAC elems
            (fun e he => ih e.1 (sizeOf_lt_ac he f rest))
            fresh h σ taken (List.forall₂_iff_zip.2 ⟨hl, fun het => hall _ het⟩) hlt'
          have hk₂ := keeps_bindNode σ₁ n id (G.find id)
          have hk := hk₁.trans hk₂
          rw [atomsAt_ac f elems rest n fresh h]; dsimp only
          refine ⟨bindNode σ₁ n id (G.find id), hk.mono (fun w hw => ⟨hw.2, hw.1⟩),
            bindNode_node_self .., bindNode_cls_self .., ?_⟩
          intro a ha
          rw [List.mem_append, List.mem_singleton] at ha
          rcases ha with ha | rfl
          · exact AtomSat.keeps hk₂ (fun x hx => ne_of_mem_or_range (has a ha x hx) hn hnv')
              (hs₁ a ha)
          · refine ⟨id, ⟨f, .mset m⟩, bindNode_node_self .., hmem, bindNode_cls_self .., rfl, ?_⟩
            simp only [RAtom.shallow]
            refine MatchN.ac hnd (by simpa using hf₁.length_eq) hmem' ?_ ?_
              (hrest.agree (fun x _ => by rw [hk.2.2.1]))
            · intro et het
              obtain ⟨vc, hvc, rfl⟩ := mem_zip_map_left het
              refine MatchC.var ?_
              rw [← (List.forall₂_iff_zip.1 hf₁).2 hvc]
              exact (hk₂.1 vc.1.1
                (ne_of_mem_or_range (hvs vc.1 (List.of_mem_zip hvc).1) hn hnv')).2
            · intro et het
              obtain ⟨vc, hvc, rfl⟩ := mem_zip_map_left het
              obtain ⟨et', het', h12, h2⟩ := zip_transfer hf.flip taken vc hvc
              have h12' : et'.1.2 = vc.1.2 := h12
              show MultOk (bindNode σ₁ n id (G.find id)) vc.1.2 (m.count vc.2)
              rw [← h12', h2]
              exact (hmult et' het').agree (fun k _ => by rw [hk.2.1])
  | aci f elems rest =>
      rcases h : atomsChildren elems fresh with ⟨vs, as, fr⟩
      obtain ⟨hle, hvs, has⟩ := varsChildren elems (fun p _ n fr => varsOk p n fr) fresh h
      have hlt' : ∀ x ∈ Pat.varsList elems, x < fresh := fun x hx => hlt x (by simp [hx])
      have hnv' : n ∉ Pat.varsList elems := fun hx => hnv (by simp [hx])
      cases hm with
      | @aci _ _ _ s taken _ hnd hl hmem' hall hrest =>
          obtain ⟨σ₁, hk₁, hf₁, hs₁⟩ := fwdChildren elems
            (fun p hp => ih p (sizeOf_lt_aci hp f rest))
            fresh h σ taken (List.forall₂_iff_zip.2 ⟨hl, fun hpc => hall _ hpc⟩) hlt'
          have hk₂ := keeps_bindNode σ₁ n id (G.find id)
          have hk := hk₁.trans hk₂
          rw [atomsAt_aci f elems rest n fresh h]; dsimp only
          refine ⟨bindNode σ₁ n id (G.find id), hk.mono (fun w hw => ⟨hw.2, hw.1⟩),
            bindNode_node_self .., bindNode_cls_self .., ?_⟩
          intro a ha
          rw [List.mem_append, List.mem_singleton] at ha
          rcases ha with ha | rfl
          · exact AtomSat.keeps hk₂ (fun x hx => ne_of_mem_or_range (has a ha x hx) hn hnv')
              (hs₁ a ha)
          · refine ⟨id, ⟨f, .set s⟩, bindNode_node_self .., hmem, bindNode_cls_self .., rfl, ?_⟩
            simp only [RAtom.shallow]
            refine MatchN.aci hnd (by simpa using hf₁.length_eq) hmem' ?_
              (hrest.agree (fun x _ => by rw [hk.2.2.2.2]))
            intro pc hpc
            obtain ⟨vc, hvc, rfl⟩ := mem_zip_map_left hpc
            refine MatchC.var ?_
            rw [← (List.forall₂_iff_zip.1 hf₁).2 hvc]
            exact (hk₂.1 vc.1 (ne_of_mem_or_range (hvs vc.1 (List.of_mem_zip hvc).1) hn hnv')).2

theorem fwd_all {G : Graph} : ∀ (k : Nat) (P : Pat), sizeOf P = k → FwdOk G P := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
      intro P hP
      exact fwd_of_sub P (fun p hp => ih _ (hP ▸ hp) p rfl)

theorem fwdOk {G : Graph} (P : Pat) : FwdOk G P := fwd_all _ P rfl

/-! ## The root -/

theorem le_foldr_max (l : List Nat) (r : Nat) :
    r ≤ l.foldr max r ∧ ∀ x ∈ l, x ≤ l.foldr max r := by
  induction l with
  | nil => simp
  | cons y l ih =>
      simp only [List.foldr_cons]
      refine ⟨le_trans ih.1 (le_max_right _ _), ?_⟩
      intro x hx
      rw [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact le_max_left _ _
      · exact le_trans (ih.2 x hx) (le_max_right _ _)

/-- An application pattern matches at `c` under `σ` iff some binding
agreeing with `σ` on the pattern's variables binds the root variable `r`
to `c` and satisfies every atom of the flattening. -/
theorem atoms_iff_match (G : Graph) (P : Pat) (r : Var) (c : C) (σ : Binding)
    (hP : P.head.isSome = true) (hr : r ∉ P.vars) :
    MatchC G P c σ ↔
      ∃ σ', AgreeOn P.vars σ σ' ∧ σ'.cls r = some c ∧ ∀ a ∈ atoms P r, AtomSat G σ' a := by
  constructor
  · intro h
    cases h with
    | var hx => simp [Pat.head] at hP
    | app hmem hf hh hn =>
        have hb := le_foldr_max P.vars r
        have hfr : ∀ x ∈ P.vars, x < P.freshAbove r := fun x hx => by
          have := hb.2 x hx; unfold Pat.freshAbove; vomega
        obtain ⟨σ', hk, hnode, hcls, hs⟩ := fwdOk P σ _ _ r (P.freshAbove r) hmem hn hfr
          (by have := hb.1; unfold Pat.freshAbove; vomega) hr
        refine ⟨σ', hk.agreeOn (fun x hx => ⟨fun hxr => hr (by rw [← hxr]; exact hx),
          Or.inl (hfr x hx)⟩), by rw [hcls, hf], hs⟩
  · rintro ⟨σ', ha, hc, hs⟩
    obtain ⟨id, nd, hnode, hmem, hcls, hop, hm⟩ := backOk P hP r (P.freshAbove r) hs
    rw [hcls] at hc
    exact MatchC_agree (.app hmem (Option.some.inj hc) hop hm) ha.symm

end Semper.EMatch
