import SemperProofs.Fidelity.Subsume

/-!
# Right-hand sides built as normal forms (fidelity row: `Den` literal)

`Den` (`Saturate/Actions.lean`) asks for a stored node whose children are
the literal values of the subterms. The engine's `add` (`egraph.rs:962-1110`,
`add_mset` 1156-1240) does not store that node for an n-ary operator:

1. it splices a child whose class has a same-operator AC/ACI summand
   (`flatten_ac_children`, `flatten_mset_children`, `egraph.rs:4504-4705`;
   `flatten_seq_children` 4706 for A operators);
2. it normalizes (`nary_canon::normalize`): coalesces or dedups, drops the
   unit's class, clamps nilpotent counts, cancels inverse pairs found in the
   hash-cons (`plain1.probe(inv, [x])`);
3. a degenerate result is an existing class, not a node: `Unit` returns the
   unit node's class, `Single g` returns `find g` (`egraph.rs:1071-1078`).

For such a right-hand side the hypotheses `ActRound.inserts`/`unions` cannot
be met by the engine (`den_misses_single` below). `DenN` replaces the stored
literal by a chain of normalization steps, each read on the graph, ending in
a stored node, a single class, or the unit. The steps are the engine's,
read existentially (any order, any splice choice): the engine's result is
one such chain. `Den` is the zero-step case (`Den.toDenN`).

`DenN` is stable under the rounds (`DenN.persist`: steps read nodes and
classes only, mapped by the new `find`), so the store saturation theorem
of `Fidelity/Subsume.lean` lifts: `fired_after_actions_N`,
`inv_step_N`, `saturation_complete_N` (with `:subsume` runs and
normalized right-hand sides).
-/

namespace Semper.EMatch.Fidelity

open Semper.EMatch

/-- The laws of an n-ary operator as `add` reads them (`nary_laws`,
`egraph.rs:751`; `unit_node`, `egraph.rs:690`): the unit node, the
nilpotent order, the inverse operator. -/
structure OpLaws where
  unit : Option NodeId
  nilpotent : Option Nat
  invOp : Option Sym

/-- One step on an AC child multiset. -/
inductive ACStep (G : Graph) (L : Sym → OpLaws) (f : Sym) : Multiset C → Multiset C → Prop
  /-- Splice one copy of a class holding a same-op AC node. -/
  | splice {m₁ rest : Multiset C} {id : NodeId} :
      (id, ⟨f, .mset m₁⟩) ∈ G.nodes → ACStep G L f ({G.find id} + rest) (m₁ + rest)
  /-- Drop one copy of the unit's class. -/
  | unit {u : NodeId} {rest : Multiset C} :
      (L f).unit = some u → ACStep G L f ({G.find u} + rest) rest
  /-- Drop `r` copies of a class (`x^r = e`). -/
  | nil {r : Nat} {x : C} {rest : Multiset C} :
      (L f).nilpotent = some r → ACStep G L f (r • {x} + rest) rest
  /-- Cancel `x` against the class of a stored `inv(x)`. -/
  | inv {g : Sym} {x : C} {id : NodeId} {rest : Multiset C} :
      (L f).invOp = some g → (id, ⟨g, .tuple [x]⟩) ∈ G.nodes →
      ACStep G L f ({x} + {G.find id} + rest) rest

/-- One step on an ACI child set. -/
inductive ACIStep (G : Graph) (L : Sym → OpLaws) (f : Sym) : Finset C → Finset C → Prop
  | splice {s₁ rest : Finset C} {id : NodeId} :
      (id, ⟨f, .set s₁⟩) ∈ G.nodes → ACIStep G L f (insert (G.find id) rest) (s₁ ∪ rest)
  | unit {u : NodeId} {rest : Finset C} :
      (L f).unit = some u → ACIStep G L f (insert (G.find u) rest) rest

/-- One step on an A child sequence. -/
inductive AStep (G : Graph) (L : Sym → OpLaws) (f : Sym) : List C → List C → Prop
  | splice {a b l₁ : List C} {id : NodeId} :
      (id, ⟨f, .seq l₁⟩) ∈ G.nodes → AStep G L f (a ++ [G.find id] ++ b) (a ++ l₁ ++ b)
  | unit {a b : List C} {u : NodeId} :
      (L f).unit = some u → AStep G L f (a ++ [G.find u] ++ b) (a ++ b)

/-- The class `add` returns for a normalized child list: a stored node, the
single child (`Normal::Single`), or the unit (`Normal::Unit`). -/
def Final (G : Graph) (L : Sym → OpLaws) (f : Sym) (ch : Children) (single : C → Prop)
    (empty : Prop) (c : C) : Prop :=
  (∃ id, (id, ⟨f, ch⟩) ∈ G.nodes ∧ c = G.find id) ∨
  (∃ x, single x ∧ c = G.find x) ∨
  (empty ∧ ∃ u, (L f).unit = some u ∧ c = G.find u)

/-- `DenN G L σ t c`: the right-hand side `t` is built in `G` with value
`c`, n-ary applications up to the normalization steps. -/
inductive DenN (G : Graph) (L : Sym → OpLaws) (σ : Binding) : Pat → C → Prop
  | var {x : Var} {c : C} : σ.cls x = some c → DenN G L σ (.var x) (G.find c)
  | plain {f : Sym} {args : List Pat} {cs : List C} {id : NodeId} :
      args.length = cs.length → (∀ pc ∈ args.zip cs, DenN G L σ pc.1 pc.2) →
      (id, ⟨f, .tuple cs⟩) ∈ G.nodes → DenN G L σ (.plain f args) (G.find id)
  | comm {f : Sym} {p q : Pat} {a b : C} {id : NodeId} :
      DenN G L σ p a → DenN G L σ q b →
      ((id, ⟨f, .spair a b⟩) ∈ G.nodes ∨ (id, ⟨f, .spair b a⟩) ∈ G.nodes) →
      DenN G L σ (.comm f p q) (G.find id)
  | assoc {f : Sym} {pre suf : Option Var} {args : List Pat} {cs u v l' : List C} {c : C} :
      args.length = cs.length → (∀ pc ∈ args.zip cs, DenN G L σ pc.1 pc.2) →
      SeqRestOk σ pre u → SeqRestOk σ suf v →
      Relation.ReflTransGen (AStep G L f) (u.map G.find ++ cs ++ v.map G.find) l' →
      Final G L f (.seq l') (fun x => l' = [x]) (l' = []) c →
      DenN G L σ (.assoc f pre args suf) c
  | ac {f : Sym} {elems : List (Pat × Mult)} {rest : Option Var} {cks : List (C × Nat)}
      {m₀ m' : Multiset C} {c : C} :
      elems.length = cks.length →
      (∀ ek ∈ elems.zip cks, RMultOk σ ek.1.2 ek.2.2) →
      (∀ ek ∈ elems.zip cks, ek.2.2 ≠ 0 → DenN G L σ ek.1.1 ek.2.1) →
      MsetRestVal σ rest m₀ →
      Relation.ReflTransGen (ACStep G L f) (acChildren cks + m₀.map G.find) m' →
      Final G L f (.mset m') (fun x => m' = {x}) (m' = 0) c →
      DenN G L σ (.ac f elems rest) c
  | aci {f : Sym} {elems : List Pat} {rest : Option Var} {cs : List C} {s₀ s' : Finset C}
      {c : C} :
      elems.length = cs.length → (∀ pc ∈ elems.zip cs, DenN G L σ pc.1 pc.2) →
      SetRestVal σ rest s₀ →
      Relation.ReflTransGen (ACIStep G L f) (cs.toFinset ∪ s₀.image G.find) s' →
      Final G L f (.set s') (fun x => s' = {x}) (s' = ∅) c →
      DenN G L σ (.aci f elems rest) c

/-! ## `Den` is the zero-step case -/

theorem _root_.Semper.EMatch.Den.toDenN {G : Graph} {L : Sym → OpLaws} {σ : Binding} {t : Pat} {c : C}
    (h : Den G σ t c) : DenN G L σ t c := by
  induction h with
  | var hx => exact DenN.var hx
  | plain hl _ hmem ih => exact DenN.plain hl ih hmem
  | comm _ _ hmem iha ihb => exact DenN.comm iha ihb hmem
  | assoc hl _ hpre hsuf hmem ih =>
      exact DenN.assoc hl ih hpre hsuf Relation.ReflTransGen.refl (Or.inl ⟨_, hmem, rfl⟩)
  | ac hl hmult _ hrest hmem ih =>
      exact DenN.ac hl hmult ih hrest Relation.ReflTransGen.refl (Or.inl ⟨_, hmem, rfl⟩)
  | aci hl _ hrest hmem ih =>
      exact DenN.aci hl ih hrest Relation.ReflTransGen.refl (Or.inl ⟨_, hmem, rfl⟩)

/-- Every value of `DenN` is `G.find` of something. -/
theorem DenN.exists_find {G : Graph} {L : Sym → OpLaws} {σ : Binding} {t : Pat} {c : C}
    (h : DenN G L σ t c) : ∃ c₀, c = G.find c₀ := by
  cases h with
  | var => exact ⟨_, rfl⟩
  | plain => exact ⟨_, rfl⟩
  | comm => exact ⟨_, rfl⟩
  | assoc _ _ _ _ _ hf => rcases hf with ⟨id, -, rfl⟩ | ⟨x, -, rfl⟩ | ⟨-, u, -, rfl⟩ <;> exact ⟨_, rfl⟩
  | ac _ _ _ _ _ hf => rcases hf with ⟨id, -, rfl⟩ | ⟨x, -, rfl⟩ | ⟨-, u, -, rfl⟩ <;> exact ⟨_, rfl⟩
  | aci _ _ _ _ hf => rcases hf with ⟨id, -, rfl⟩ | ⟨x, -, rfl⟩ | ⟨-, u, -, rfl⟩ <;> exact ⟨_, rfl⟩

theorem DenN.find_eq {G : Graph} (hidem : G.FindIdem) {L : Sym → OpLaws} {σ : Binding}
    {t : Pat} {c : C} (h : DenN G L σ t c) : G.find c = c := by
  obtain ⟨c₀, rfl⟩ := h.exists_find
  exact hidem c₀

/-! ## Persistence across a round -/

section Persist

variable {Sb Sa : Store} (h : StorePersist Sb Sa) {L : Sym → OpLaws} {f : Sym}
include h

omit h in
theorem rtg_map {α : Type} {r s : α → α → Prop} (g : α → α) (hg : ∀ a b, r a b → s (g a) (g b))
    {a b : α} (hr : Relation.ReflTransGen r a b) : Relation.ReflTransGen s (g a) (g b) := by
  induction hr with
  | refl => exact .refl
  | tail _ hbc ih => exact ih.tail (hg _ _ hbc)

theorem StorePersist.find_before (c : C) : Sa.find (Sb.find c) = Sa.find c :=
  h.no_split _ _ (h.before_idem c)

theorem StorePersist.find_comp : Sa.find ∘ Sb.find = Sa.find :=
  funext h.find_before

theorem StorePersist.find_self (c : C) : Sa.find (Sa.find c) = Sa.find c := h.after_idem c

theorem ACStep.map {m m' : Multiset C} (hs : ACStep Sb.graph L f m m') :
    ACStep Sa.graph L f (m.map Sa.find) (m'.map Sa.find) := by
  cases hs with
  | splice hmem =>
      rename_i m₁ rest id
      obtain ⟨⟨op, ch⟩, hmem', hop, hch⟩ := h.persist _ _ hmem
      cases ch <;> simp [CanonCh] at hch
      simp only at hop
      subst hop hch
      have h1 : ACStep Sa.graph L _ ({Sa.find id} + rest.map Sa.find) _ :=
        ACStep.splice (L := L) (rest := rest.map Sa.find) hmem'
      simpa [Multiset.map_add, h.find_before] using h1
  | unit hu =>
      simpa [Multiset.map_add, h.find_before] using ACStep.unit (G := Sa.graph) (f := f) hu
  | nil hr =>
      simpa [Multiset.map_add, Multiset.map_nsmul] using ACStep.nil (G := Sa.graph) hr
  | inv hg hmem =>
      obtain ⟨⟨op, ch⟩, hmem', hop, hch⟩ := h.persist _ _ hmem
      cases ch <;> simp [CanonCh] at hch
      simp only at hop
      subst hop hch
      have h1 : ACStep Sa.graph L f ({_} + {Sa.find _} + m'.map Sa.find) (m'.map Sa.find) :=
        ACStep.inv (L := L) (f := f) (rest := m'.map Sa.find) hg hmem'
      simpa [Multiset.map_add, h.find_before] using h1

theorem ACIStep.map {s s' : Finset C} (hs : ACIStep Sb.graph L f s s') :
    ACIStep Sa.graph L f (s.image Sa.find) (s'.image Sa.find) := by
  cases hs with
  | splice hmem =>
      rename_i s₁ rest id
      obtain ⟨⟨op, ch⟩, hmem', hop, hch⟩ := h.persist _ _ hmem
      cases ch <;> simp [CanonCh] at hch
      simp only at hop
      subst hop hch
      have h1 : ACIStep Sa.graph L _ (insert (Sa.find id) (rest.image Sa.find)) _ :=
        ACIStep.splice (L := L) (rest := rest.image Sa.find) hmem'
      simpa [Finset.image_insert, Finset.image_union, h.find_before] using h1
  | unit hu =>
      simpa [Finset.image_insert, h.find_before] using ACIStep.unit (G := Sa.graph) (f := f) hu

theorem AStep.map {l l' : List C} (hs : AStep Sb.graph L f l l') :
    AStep Sa.graph L f (l.map Sa.find) (l'.map Sa.find) := by
  cases hs with
  | splice hmem =>
      rename_i a b l₁ id
      obtain ⟨⟨op, ch⟩, hmem', hop, hch⟩ := h.persist _ _ hmem
      cases ch <;> simp [CanonCh] at hch
      simp only at hop
      subst hop hch
      have h1 : AStep Sa.graph L _ (a.map Sa.find ++ [Sa.find id] ++ b.map Sa.find) _ :=
        AStep.splice (L := L) (a := a.map Sa.find) (b := b.map Sa.find) hmem'
      simpa [h.find_before] using h1
  | unit hu =>
      simpa [h.find_before] using AStep.unit (G := Sa.graph) (f := f) (a := _) (b := _) hu

theorem Final.map_mset {m : Multiset C} {c : C}
    (hf : Final Sb.graph L f (.mset m) (fun x => m = {x}) (m = 0) c) :
    Final Sa.graph L f (.mset (m.map Sa.find)) (fun x => m.map Sa.find = {x})
      (m.map Sa.find = 0) (Sa.find c) := by
  rcases hf with ⟨id, hmem, rfl⟩ | ⟨x, rfl, rfl⟩ | ⟨rfl, u, hu, rfl⟩
  · obtain ⟨⟨op, ch⟩, hmem', hop, hch⟩ := h.persist _ _ hmem
    cases ch <;> simp [CanonCh] at hch
    simp only at hop
    subst hop hch
    exact Or.inl ⟨id, hmem', by simp [h.find_before]⟩
  · exact Or.inr (Or.inl ⟨Sa.find x, by simp, by simp [h.find_before, h.find_self]⟩)
  · exact Or.inr (Or.inr ⟨by simp, u, hu, by simp [h.find_before]⟩)

theorem Final.map_set {s : Finset C} {c : C}
    (hf : Final Sb.graph L f (.set s) (fun x => s = {x}) (s = ∅) c) :
    Final Sa.graph L f (.set (s.image Sa.find)) (fun x => s.image Sa.find = {x})
      (s.image Sa.find = ∅) (Sa.find c) := by
  rcases hf with ⟨id, hmem, rfl⟩ | ⟨x, rfl, rfl⟩ | ⟨rfl, u, hu, rfl⟩
  · obtain ⟨⟨op, ch⟩, hmem', hop, hch⟩ := h.persist _ _ hmem
    cases ch <;> simp [CanonCh] at hch
    simp only at hop
    subst hop hch
    exact Or.inl ⟨id, hmem', by simp [h.find_before]⟩
  · exact Or.inr (Or.inl ⟨Sa.find x, by simp, by simp [h.find_before, h.find_self]⟩)
  · exact Or.inr (Or.inr ⟨by simp, u, hu, by simp [h.find_before]⟩)

theorem Final.map_seq {l : List C} {c : C}
    (hf : Final Sb.graph L f (.seq l) (fun x => l = [x]) (l = []) c) :
    Final Sa.graph L f (.seq (l.map Sa.find)) (fun x => l.map Sa.find = [x])
      (l.map Sa.find = []) (Sa.find c) := by
  rcases hf with ⟨id, hmem, rfl⟩ | ⟨x, rfl, rfl⟩ | ⟨rfl, u, hu, rfl⟩
  · obtain ⟨⟨op, ch⟩, hmem', hop, hch⟩ := h.persist _ _ hmem
    cases ch <;> simp [CanonCh] at hch
    simp only at hop
    subst hop hch
    exact Or.inl ⟨id, hmem', by simp [h.find_before]⟩
  · exact Or.inr (Or.inl ⟨Sa.find x, by simp, by simp [h.find_before, h.find_self]⟩)
  · exact Or.inr (Or.inr ⟨by simp, u, hu, by simp [h.find_before]⟩)

/-- `DenN.persist`: a term built before the round is built after it, with
the new value; nothing about subsumption is assumed. -/
theorem DenN.persist {σ : Binding} {t : Pat} {c : C} (hd : DenN Sb.graph L σ t c) :
    DenN Sa.graph L σ t (Sa.find c) := by
  have hfb := h.find_before
  have hfc := h.find_comp
  induction hd with
  | var hx =>
      simp only [Store.graph_find, hfb]
      exact DenN.var hx
  | plain hl hall hmem ih =>
      rename_i f args cs id
      obtain ⟨⟨op, ch⟩, hmem', hop, hch⟩ := h.persist _ _ hmem
      cases ch <;> simp [CanonCh] at hch
      simp only at hop
      subst hop hch
      simp only [Store.graph_find, hfb]
      refine DenN.plain (by simp [hl]) ?_ hmem'
      intro pc hpc
      rw [List.zip_map_right, List.mem_map] at hpc
      obtain ⟨pc', hpc', rfl⟩ := hpc
      exact ih pc' hpc'
  | comm ha hb hmem iha ihb =>
      rename_i f p q a b id
      simp only [Store.graph_find, hfb]
      rcases hmem with hmem | hmem
      · obtain ⟨⟨op, ch⟩, hmem', hop, hch⟩ := h.persist _ _ hmem
        cases ch <;> simp [CanonCh] at hch
        simp only at hop
        subst hop
        rcases hch with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact DenN.comm iha ihb (Or.inl hmem')
        · exact DenN.comm iha ihb (Or.inr hmem')
      · obtain ⟨⟨op, ch⟩, hmem', hop, hch⟩ := h.persist _ _ hmem
        cases ch <;> simp [CanonCh] at hch
        simp only at hop
        subst hop
        rcases hch with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact DenN.comm iha ihb (Or.inr hmem')
        · exact DenN.comm iha ihb (Or.inl hmem')
  | assoc hl hall hpre hsuf hsteps hfin ih =>
      rename_i f pre suf args cs u v l' c
      refine DenN.assoc (cs := cs.map Sa.find) (u := u) (v := v) (l' := l'.map Sa.find)
        (by simp [hl]) ?_ hpre hsuf ?_ (Final.map_seq h hfin)
      · intro pc hpc
        rw [List.zip_map_right, List.mem_map] at hpc
        obtain ⟨pc', hpc', rfl⟩ := hpc
        exact ih pc' hpc'
      · have := rtg_map (List.map Sa.find) (fun _ _ hs => AStep.map h hs) hsteps
        simpa [List.map_append, List.map_map, hfc] using this
  | ac hl hmult hden hrest hsteps hfin ih =>
      rename_i f elems rest cks m₀ m' c
      refine DenN.ac (cks := cks.map fun ck => (Sa.find ck.1, ck.2)) (m₀ := m₀) (m' := m'.map Sa.find)
        (by simp [hl]) ?_ ?_ hrest ?_ (Final.map_mset h hfin)
      · intro ek hek
        rw [List.zip_map_right, List.mem_map] at hek
        obtain ⟨ek', hek', rfl⟩ := hek
        exact hmult ek' hek'
      · intro ek hek hk
        rw [List.zip_map_right, List.mem_map] at hek
        obtain ⟨ek', hek', rfl⟩ := hek
        exact ih ek' hek' hk
      · have := rtg_map (Multiset.map Sa.find) (fun _ _ hs => ACStep.map h hs) hsteps
        simpa [Multiset.map_add, Multiset.map_map, acChildren_map, hfc, hfb] using this
  | aci hl hall hrest hsteps hfin ih =>
      rename_i f elems rest cs s₀ s' c
      refine DenN.aci (cs := cs.map Sa.find) (s₀ := s₀) (s' := s'.image Sa.find)
        (by simp [hl]) ?_ hrest ?_ (Final.map_set h hfin)
      · intro pc hpc
        rw [List.zip_map_right, List.mem_map] at hpc
        obtain ⟨pc', hpc', rfl⟩ := hpc
        exact ih pc' hpc'
      · have := rtg_map (Finset.image Sa.find) (fun _ _ hs => ACIStep.map h hs) hsteps
        have htf : (cs.map Sa.find).toFinset = cs.toFinset.image Sa.find := by ext; simp
        simpa [Finset.image_union, Finset.image_image, htf, hfc] using this

end Persist

end Semper.EMatch.Fidelity
