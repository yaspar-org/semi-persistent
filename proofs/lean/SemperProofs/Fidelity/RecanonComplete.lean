import SemperProofs.Fidelity.StopTest

/-!
# Recanonicalization with completion on (the `respelled` re-match, completion on)

`denN_persist_fails` (`Fidelity/Recanon.lean`) shows that a right-hand side
built through a node a law rewrote at rebuild need not keep its value: the
chains `SChainN` and `AChain` therefore route the rules that build an n-ary
term to the naive matcher after such a rebuild, which the engine does with
completion off (`respelled`, `saturate.rs`). With completion on the engine
does not re-match them and expects completion to join the two spellings.
This file states and proves that expectation at the level of the store.

* `EqAC`, `EqACI`, `EqA`: the equational theory of an n-ary operator modulo
  the store, on child multisets, sets and sequences: the equivalence the
  normalization steps generate (`ACStep`, `ACIStep`, `AStep`: splice, unit
  drop, nilpotent clamp, inverse cancellation).
* `DenE`: a right-hand side is present *modulo the theory*: `DenN` with the
  normalization chain replaced by `EqAC`. The class holds a stored node (or
  is the leaf) whose spelling is equal, modulo the laws and the store's
  equations, to the spelling built from the match.
* `DenE.persist`: a right-hand side present modulo the theory before a
  round is present modulo the theory after it, under `StorePersistE`
  (`StorePersistN` plus literal persistence of the sequence nodes). No
  routing, no literal persistence of the AC nodes: the old node and the new
  spelling are equal in the theory, whatever laws the rebuild applied, and
  however many splices the old chain went through (the case of
  `denN_persist_fails`). The key lemma is `ACStep.mapE`: one normalization
  step before the round is an equality of the theory after it, through the
  recanonicalized node (`NFMset`).
* `saturation_complete_E`: the fixpoint theorem on `SChainE`, the chain with
  an arbitrary routing per round (the engine's routing with completion on
  is `route naive false = naive`), concluding `InvE`: every match on the
  index is fired modulo the theory.
* `TheoryClosed`: the store is closed under the theory: two classes equal
  modulo the laws and the store's equations are one class. It is the store
  reading of the completion completeness theorem at a fixpoint
  (`ac_equal_same_class`, `CompleteAtoms.same_class`: two `=_E`-equal
  active nodes are in one class). `denE_denN_eq`: under it, a right-hand
  side present modulo the theory has every value `add` would build in that
  class. `saturation_complete_closed`: with completion on, at the fixpoint,
  every union the rules ask for holds between any values its two sides
  have, and the match root's class holds a node denoting the right-hand
  side modulo the theory.
* `PersistFails.sa_not_closed`, `PersistFails.completed`: the after-store of
  the counter-model is not closed under the theory (the two values `d` and
  `e'` are equal in it: `f{p, q} = e`), so the counter-model does not
  contradict the theorem; its completion `Sc` (the two classes merged) is
  closed, meets `StorePersistE` from the before-store, and there the
  instance is reached: `f{x}` has the value `Sc.find e'` and no other.

What the theorem does not say: that the new spelling is stored as a node
(the engine does not build it, and completion materializes the normal form
of the old node, `nf_present`, not every spelling). It says that whatever
spelling `add` would build is in the match root's class, which is what the
re-match would establish.

Engine fixture: `egraph/tests/egg/semi_recanon_completion_on.egg` (the
counter-model's shape under eager completion, semi-naive).
-/

namespace Semper.EMatch.Fidelity

open Semper.EMatch

/-! ## The theory of an n-ary operator on the store -/

/-- The equational theory of the AC operator `f` modulo the store: the
equivalence the normalization steps generate on child multisets. -/
def EqAC (G : Graph) (L : Sym → OpLaws) (f : Sym) : Multiset C → Multiset C → Prop :=
  Relation.EqvGen (ACStep G L f)

/-- The same for an ACI operator, on child sets. -/
def EqACI (G : Graph) (L : Sym → OpLaws) (f : Sym) : Finset C → Finset C → Prop :=
  Relation.EqvGen (ACIStep G L f)

/-- The same for an A operator, on child sequences. -/
def EqA (G : Graph) (L : Sym → OpLaws) (f : Sym) : List C → List C → Prop :=
  Relation.EqvGen (AStep G L f)

theorem eqvGen_of_rtg {α : Type} {r : α → α → Prop} {a b : α}
    (h : Relation.ReflTransGen r a b) : Relation.EqvGen r a b := by
  induction h with
  | refl => exact .refl _
  | tail _ hbc ih => exact ih.trans _ _ _ (.rel _ _ hbc)

theorem rtg_mono {α : Type} {r s : α → α → Prop} (h : ∀ a b, r a b → s a b) {a b : α}
    (hr : Relation.ReflTransGen r a b) : Relation.ReflTransGen s a b := by
  induction hr with
  | refl => exact .refl
  | tail _ hbc ih => exact ih.tail (h _ _ hbc)

theorem eqvGen_map {α β : Type} {r : α → α → Prop} {s : β → β → Prop} (g : α → β)
    (hg : ∀ a b, r a b → Relation.EqvGen s (g a) (g b)) {a b : α}
    (h : Relation.EqvGen r a b) : Relation.EqvGen s (g a) (g b) := by
  induction h with
  | rel _ _ hab => exact hg _ _ hab
  | refl => exact .refl _
  | symm _ _ _ ih => exact ih.symm _ _
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans _ _ _ ih₂

theorem eqvGen_invariant {α β : Type} {r : α → α → Prop} (v : α → β)
    (hv : ∀ a b, r a b → v a = v b) {a b : α} (h : Relation.EqvGen r a b) : v a = v b := by
  induction h with
  | rel _ _ hab => exact hv _ _ hab
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

section Steps

variable {G : Graph} {L : Sym → OpLaws} {f : Sym}

/-- A step is compatible with a common rest. -/
theorem ACStep.add_right {m m' : Multiset C} (rest : Multiset C) (h : ACStep G L f m m') :
    ACStep G L f (m + rest) (m' + rest) := by
  cases h with
  | splice hmem => rw [add_assoc, add_assoc]; exact .splice hmem
  | unit hu => rw [add_assoc]; exact .unit hu
  | nil hr => rw [add_assoc]; exact .nil hr
  | inv hg hmem => rw [add_assoc]; exact .inv hg hmem

theorem ACIStep.union_right {s s' : Finset C} (rest : Finset C) (h : ACIStep G L f s s') :
    ACIStep G L f (s ∪ rest) (s' ∪ rest) := by
  cases h with
  | splice hmem => rw [Finset.insert_union, Finset.union_assoc]; exact .splice hmem
  | unit hu => rw [Finset.insert_union]; exact .unit hu

theorem EqAC.of_rtg {m m' : Multiset C} (h : Relation.ReflTransGen (ACStep G L f) m m') :
    EqAC G L f m m' := eqvGen_of_rtg h

theorem EqACI.of_rtg {s s' : Finset C} (h : Relation.ReflTransGen (ACIStep G L f) s s') :
    EqACI G L f s s' := eqvGen_of_rtg h

theorem EqA.of_rtg {l l' : List C} (h : Relation.ReflTransGen (AStep G L f) l l') :
    EqA G L f l l' := eqvGen_of_rtg h

theorem EqAC.add_right {m m' : Multiset C} (rest : Multiset C) (h : EqAC G L f m m') :
    EqAC G L f (m + rest) (m' + rest) :=
  eqvGen_map (· + rest) (fun _ _ hs => .rel _ _ (hs.add_right rest)) h

theorem EqACI.union_right {s s' : Finset C} (rest : Finset C) (h : EqACI G L f s s') :
    EqACI G L f (s ∪ rest) (s' ∪ rest) :=
  eqvGen_map (· ∪ rest) (fun _ _ hs => .rel _ _ (hs.union_right rest)) h

/-- A recanonicalization step only removes elements. -/
theorem RStep.le {m m' : Multiset C} (h : RStep G L f m m') : m' ≤ m := by
  cases h with
  | unit _ => exact Multiset.le_add_left _ _
  | nil _ => exact Multiset.le_add_left _ _

theorem rtg_RStep_le {m m' : Multiset C} (h : Relation.ReflTransGen (RStep G L f) m m') :
    m' ≤ m := by
  induction h with
  | refl => exact le_rfl
  | tail _ hs ih => exact hs.le.trans ih

theorem RSetStep.subset {s s' : Finset C} (h : RSetStep G L f s s') : s' ⊆ s := by
  cases h with
  | unit _ => exact Finset.subset_insert _ _

theorem rtg_RSetStep_subset {s s' : Finset C} (h : Relation.ReflTransGen (RSetStep G L f) s s') :
    s' ⊆ s := by
  induction h with
  | refl => exact Finset.Subset.refl _
  | tail _ hs ih => exact hs.subset.trans ih

/-! ### Canonical elements along a chain -/

/-- Every element is a representative. -/
def MCanon (G : Graph) (m : Multiset C) : Prop := ∀ x ∈ m, G.find x = x
def SCanon (G : Graph) (s : Finset C) : Prop := ∀ x ∈ s, G.find x = x
def LCanon (G : Graph) (l : List C) : Prop := ∀ x ∈ l, G.find x = x

theorem MCanon.add {m n : Multiset C} (hm : MCanon G m) (hn : MCanon G n) : MCanon G (m + n) := by
  intro x hx
  rcases Multiset.mem_add.1 hx with h | h
  · exact hm x h
  · exact hn x h

theorem MCanon.of_le {m n : Multiset C} (hm : MCanon G m) (h : n ≤ m) : MCanon G n :=
  fun x hx => hm x (Multiset.mem_of_le h hx)

theorem MCanon.map (hi : G.FindIdem) (m : Multiset C) : MCanon G (m.map G.find) := by
  intro x hx
  obtain ⟨y, -, rfl⟩ := Multiset.mem_map.1 hx
  exact hi y

theorem ACStep.canon (hc : G.ChildrenCanon) {m m' : Multiset C} (h : ACStep G L f m m')
    (hm : MCanon G m) : MCanon G m' := by
  cases h with
  | splice hmem =>
      exact MCanon.add (fun x hx => hc _ hmem x hx) (hm.of_le (Multiset.le_add_left _ _))
  | unit _ => exact hm.of_le (Multiset.le_add_left _ _)
  | nil _ => exact hm.of_le (Multiset.le_add_left _ _)
  | inv _ _ => exact hm.of_le (Multiset.le_add_left _ _)

theorem rtg_ACStep_canon (hc : G.ChildrenCanon) {m m' : Multiset C}
    (h : Relation.ReflTransGen (ACStep G L f) m m') (hm : MCanon G m) : MCanon G m' := by
  induction h with
  | refl => exact hm
  | tail _ hs ih => exact hs.canon hc ih

theorem SCanon.union {s t : Finset C} (hs : SCanon G s) (ht : SCanon G t) : SCanon G (s ∪ t) := by
  intro x hx
  rcases Finset.mem_union.1 hx with h | h
  · exact hs x h
  · exact ht x h

theorem SCanon.of_subset {s t : Finset C} (hs : SCanon G s) (h : t ⊆ s) : SCanon G t :=
  fun x hx => hs x (h hx)

theorem ACIStep.canon (hc : G.ChildrenCanon) {s s' : Finset C} (h : ACIStep G L f s s')
    (hs : SCanon G s) : SCanon G s' := by
  cases h with
  | splice hmem =>
      exact SCanon.union (fun x hx => hc _ hmem x hx) (hs.of_subset (Finset.subset_insert _ _))
  | unit _ => exact hs.of_subset (Finset.subset_insert _ _)

theorem rtg_ACIStep_canon (hc : G.ChildrenCanon) {s s' : Finset C}
    (h : Relation.ReflTransGen (ACIStep G L f) s s') (hs : SCanon G s) : SCanon G s' := by
  induction h with
  | refl => exact hs
  | tail _ hs' ih => exact hs'.canon hc ih

theorem LCanon.append {l l' : List C} (h : LCanon G l) (h' : LCanon G l') : LCanon G (l ++ l') := by
  intro x hx
  rcases List.mem_append.1 hx with hx | hx
  · exact h x hx
  · exact h' x hx

theorem AStep.canon (hc : G.ChildrenCanon) {l l' : List C} (h : AStep G L f l l')
    (hl : LCanon G l) : LCanon G l' := by
  cases h with
  | splice hmem =>
      rename_i a b l₁ id
      have ha : LCanon G a := fun x hx => hl x (by simp [hx])
      have hb : LCanon G b := fun x hx => hl x (by simp [hx])
      exact (ha.append (fun x hx => hc _ hmem x hx)).append hb
  | unit hu =>
      rename_i a b u
      have ha : LCanon G a := fun x hx => hl x (by simp [hx])
      have hb : LCanon G b := fun x hx => hl x (by simp [hx])
      exact ha.append hb

theorem rtg_AStep_canon (hc : G.ChildrenCanon) {l l' : List C}
    (h : Relation.ReflTransGen (AStep G L f) l l') (hl : LCanon G l) : LCanon G l' := by
  induction h with
  | refl => exact hl
  | tail _ hs ih => exact hs.canon hc ih

/-! ### A final class is equal to its spelling -/

/-- The class `add` returns for a normalized multiset is equal to it in the
theory: the stored node is a splice, the single is itself, the unit is a
unit drop. -/
theorem Final.eqAC {m : Multiset C} {c : C}
    (hf : Final G L f (.mset m) (fun x => m = {x}) (m = 0) c) (hm : MCanon G m) :
    EqAC G L f m {c} := by
  rcases hf with ⟨id, hmem, rfl⟩ | ⟨x, rfl, rfl⟩ | ⟨rfl, u, hu, rfl⟩
  · have := ACStep.splice (G := G) (L := L) (rest := 0) hmem
    simp only [add_zero] at this
    exact .symm _ _ (.rel _ _ this)
  · rw [hm x (by simp)]
    exact .refl _
  · have := ACStep.unit (G := G) (L := L) (f := f) (rest := 0) hu
    simp only [add_zero] at this
    exact .symm _ _ (.rel _ _ this)

theorem Final.eqACI {s : Finset C} {c : C}
    (hf : Final G L f (.set s) (fun x => s = {x}) (s = ∅) c) (hs : SCanon G s) :
    EqACI G L f s {c} := by
  rcases hf with ⟨id, hmem, rfl⟩ | ⟨x, rfl, rfl⟩ | ⟨rfl, u, hu, rfl⟩
  · have := ACIStep.splice (G := G) (L := L) (rest := ∅) hmem
    simp only [Finset.union_empty, Finset.insert_empty] at this
    exact .symm _ _ (.rel _ _ this)
  · rw [hs x (by simp)]
    exact .refl _
  · have := ACIStep.unit (G := G) (L := L) (f := f) (rest := ∅) hu
    simp only [Finset.insert_empty] at this
    exact .symm _ _ (.rel _ _ this)

theorem Final.eqA {l : List C} {c : C}
    (hf : Final G L f (.seq l) (fun x => l = [x]) (l = []) c) (hl : LCanon G l) :
    EqA G L f l [c] := by
  rcases hf with ⟨id, hmem, rfl⟩ | ⟨x, rfl, rfl⟩ | ⟨rfl, u, hu, rfl⟩
  · have := AStep.splice (G := G) (L := L) (a := []) (b := []) hmem
    simp only [List.nil_append, List.append_nil] at this
    exact .symm _ _ (.rel _ _ this)
  · rw [hl x (by simp)]
    exact .refl _
  · have := AStep.unit (G := G) (L := L) (f := f) (a := []) (b := []) hu
    simp only [List.nil_append, List.append_nil] at this
    exact .symm _ _ (.rel _ _ this)

end Steps

/-! ## Right-hand sides present modulo the theory -/

/-- `DenE G L σ t c`: the right-hand side `t` is present in `G` under `σ`
with value `c`, modulo the theory: as `DenN`, with the normalization chain
of an n-ary application replaced by the equational theory of its operator
on the store. The spelling the chain ends at is canonical, and its class
is `c` (`Final`: a stored node, the single element, or the unit). -/
inductive DenE (G : Graph) (L : Sym → OpLaws) (σ : Binding) : Pat → C → Prop
  | var {x : Var} {c : C} : σ.cls x = some c → DenE G L σ (.var x) (G.find c)
  | plain {f : Sym} {args : List Pat} {cs : List C} {id : NodeId} :
      args.length = cs.length → (∀ pc ∈ args.zip cs, DenE G L σ pc.1 pc.2) →
      (id, ⟨f, .tuple cs⟩) ∈ G.nodes → DenE G L σ (.plain f args) (G.find id)
  | comm {f : Sym} {p q : Pat} {a b : C} {id : NodeId} :
      DenE G L σ p a → DenE G L σ q b →
      ((id, ⟨f, .spair a b⟩) ∈ G.nodes ∨ (id, ⟨f, .spair b a⟩) ∈ G.nodes) →
      DenE G L σ (.comm f p q) (G.find id)
  | assoc {f : Sym} {pre suf : Option Var} {args : List Pat} {cs u v l' : List C} {c : C} :
      args.length = cs.length → (∀ pc ∈ args.zip cs, DenE G L σ pc.1 pc.2) →
      SeqRestOk σ pre u → SeqRestOk σ suf v →
      EqA G L f (u.map G.find ++ cs ++ v.map G.find) l' → LCanon G l' →
      Final G L f (.seq l') (fun x => l' = [x]) (l' = []) c →
      DenE G L σ (.assoc f pre args suf) c
  | ac {f : Sym} {elems : List (Pat × Mult)} {rest : Option Var} {cks : List (C × Nat)}
      {m₀ m' : Multiset C} {c : C} :
      elems.length = cks.length →
      (∀ ek ∈ elems.zip cks, RMultOk σ ek.1.2 ek.2.2) →
      (∀ ek ∈ elems.zip cks, ek.2.2 ≠ 0 → DenE G L σ ek.1.1 ek.2.1) →
      MsetRestVal σ rest m₀ →
      EqAC G L f (acChildren cks + m₀.map G.find) m' → MCanon G m' →
      Final G L f (.mset m') (fun x => m' = {x}) (m' = 0) c →
      DenE G L σ (.ac f elems rest) c
  | aci {f : Sym} {elems : List Pat} {rest : Option Var} {cs : List C} {s₀ s' : Finset C}
      {c : C} :
      elems.length = cs.length → (∀ pc ∈ elems.zip cs, DenE G L σ pc.1 pc.2) →
      SetRestVal σ rest s₀ →
      EqACI G L f (cs.toFinset ∪ s₀.image G.find) s' → SCanon G s' →
      Final G L f (.set s') (fun x => s' = {x}) (s' = ∅) c →
      DenE G L σ (.aci f elems rest) c

theorem DenE.exists_find {G : Graph} {L : Sym → OpLaws} {σ : Binding} {t : Pat} {c : C}
    (h : DenE G L σ t c) : ∃ c₀, c = G.find c₀ := by
  cases h with
  | var => exact ⟨_, rfl⟩
  | plain => exact ⟨_, rfl⟩
  | comm => exact ⟨_, rfl⟩
  | assoc _ _ _ _ _ _ hf => rcases hf with ⟨id, -, rfl⟩ | ⟨x, -, rfl⟩ | ⟨-, u, -, rfl⟩ <;> exact ⟨_, rfl⟩
  | ac _ _ _ _ _ _ hf => rcases hf with ⟨id, -, rfl⟩ | ⟨x, -, rfl⟩ | ⟨-, u, -, rfl⟩ <;> exact ⟨_, rfl⟩
  | aci _ _ _ _ _ hf => rcases hf with ⟨id, -, rfl⟩ | ⟨x, -, rfl⟩ | ⟨-, u, -, rfl⟩ <;> exact ⟨_, rfl⟩

theorem DenE.find_eq {G : Graph} (hidem : G.FindIdem) {L : Sym → OpLaws} {σ : Binding}
    {t : Pat} {c : C} (h : DenE G L σ t c) : G.find c = c := by
  obtain ⟨c₀, rfl⟩ := h.exists_find
  exact hidem c₀

/-! ### List helpers -/

theorem exists_mem_zip_of_mem_right {α β : Type} :
    ∀ {l₁ : List α} {l₂ : List β}, l₁.length = l₂.length → ∀ {b : β}, b ∈ l₂ →
      ∃ a, (a, b) ∈ l₁.zip l₂
  | [], [], _, _, hb => by simp at hb
  | [], _ :: _, h, _, _ => by simp at h
  | _ :: _, [], h, _, _ => by simp at h
  | a :: l₁, b' :: l₂, h, b, hb => by
      simp only [List.mem_cons] at hb
      rcases hb with rfl | hb
      · exact ⟨a, by simp⟩
      · obtain ⟨a', ha'⟩ := exists_mem_zip_of_mem_right (by simpa using h) hb
        exact ⟨a', by simp [ha']⟩

theorem mem_acChildren {x : C} : ∀ {cks : List (C × Nat)}, x ∈ acChildren cks →
    ∃ ck ∈ cks, ck.2 ≠ 0 ∧ x = ck.1
  | [], h => by simp [acChildren] at h
  | (c, k) :: cks, h => by
      simp only [acChildren, Multiset.mem_add, Multiset.mem_nsmul, Multiset.mem_singleton] at h
      rcases h with ⟨hk, hxc⟩ | h
      · exact ⟨(c, k), by simp, hk, hxc⟩
      · obtain ⟨ck, hck, hk, hx⟩ := mem_acChildren h
        exact ⟨ck, by simp [hck], hk, hx⟩

/-- The spelling of an AC application built from representatives is
canonical: every element is a value of a subterm with a non-zero count or a
mapped rest element. -/
theorem acChildren_canon {G : Graph} (hi : G.FindIdem) {cks : List (C × Nat)}
    (hv : ∀ ck ∈ cks, ck.2 ≠ 0 → ∃ c₀, ck.1 = G.find c₀) (m₀ : Multiset C) :
    MCanon G (acChildren cks + m₀.map G.find) := by
  refine MCanon.add ?_ (MCanon.map hi m₀)
  intro x hx
  obtain ⟨ck, hck, hk, rfl⟩ := mem_acChildren hx
  obtain ⟨c₀, hc₀⟩ := hv ck hck hk
  rw [hc₀]; exact hi c₀

/-! ### `DenN` is the chain case -/

theorem DenN.toDenE {G : Graph} (hc : G.ChildrenCanon) (hi : G.FindIdem) {L : Sym → OpLaws}
    {σ : Binding} {t : Pat} {c : C} (h : DenN G L σ t c) : DenE G L σ t c := by
  induction h with
  | var hx => exact DenE.var hx
  | plain hl _ hmem ih => exact DenE.plain hl ih hmem
  | comm _ _ hmem iha ihb => exact DenE.comm iha ihb hmem
  | assoc hl hall hpre hsuf hsteps hfin ih =>
      rename_i f pre suf args cs u v l' c
      have hstart : LCanon G (u.map G.find ++ cs ++ v.map G.find) := by
        intro x hx
        simp only [List.mem_append, List.mem_map] at hx
        rcases hx with (⟨y, -, rfl⟩ | hx) | ⟨y, -, rfl⟩
        · exact hi y
        · obtain ⟨a, ha⟩ := exists_mem_zip_of_mem_right hl hx
          obtain ⟨c₀, hc₀⟩ := (hall _ ha).exists_find
          simp only at hc₀; rw [hc₀]; exact hi c₀
        · exact hi y
      exact DenE.assoc hl ih hpre hsuf (EqA.of_rtg hsteps) (rtg_AStep_canon hc hsteps hstart) hfin
  | ac hl hmult hden hrest hsteps hfin ih =>
      rename_i f elems rest cks m₀ m' c
      have hstart : MCanon G (acChildren cks + m₀.map G.find) := by
        refine acChildren_canon hi ?_ m₀
        intro ck hck hk
        obtain ⟨e, he⟩ := exists_mem_zip_of_mem_right hl hck
        exact (hden _ he hk).exists_find
      exact DenE.ac hl hmult ih hrest (EqAC.of_rtg hsteps) (rtg_ACStep_canon hc hsteps hstart) hfin
  | aci hl hall hrest hsteps hfin ih =>
      rename_i f elems rest cs s₀ s' c
      have hstart : SCanon G (cs.toFinset ∪ s₀.image G.find) := by
        intro x hx
        simp only [Finset.mem_union, List.mem_toFinset, Finset.mem_image] at hx
        rcases hx with hx | ⟨y, -, rfl⟩
        · obtain ⟨a, ha⟩ := exists_mem_zip_of_mem_right hl hx
          obtain ⟨c₀, hc₀⟩ := (hall _ ha).exists_find
          simp only at hc₀; rw [hc₀]; exact hi c₀
        · exact hi y
      exact DenE.aci hl ih hrest (EqACI.of_rtg hsteps) (rtg_ACIStep_canon hc hsteps hstart) hfin

/-! ## Persistence across a rebuild that applied the laws -/

/-- Sequence nodes persist literally: `recanonize_node` maps the children of
a sequence node through `find` and applies no law (`OrderedCanon`).
`LiteralFixed` covers the tuple and pair nodes only (`Children.isVariadic`
is true of a sequence). -/
def LiteralSeq (Sb Sa : Store) : Prop :=
  ∀ id f l, (id, ⟨f, .seq l⟩) ∈ Sb.nodes → (id, ⟨f, .seq (l.map Sa.find)⟩) ∈ Sa.nodes

/-- `StorePersistN` with the sequence nodes persisting literally. -/
structure StorePersistE (L : Sym → OpLaws) (Sb Sa : Store) : Prop extends StorePersistN L Sb Sa where
  seq : LiteralSeq Sb Sa

theorem StorePersist.toE {Sb Sa : Store} (h : StorePersist Sb Sa) (L : Sym → OpLaws) :
    StorePersistE L Sb Sa where
  toStorePersistN := h.toN L
  seq := by
    intro id f l hmem
    obtain ⟨⟨op, ch⟩, hmem', hop, hch⟩ := h.persist _ _ hmem
    cases ch <;> simp [CanonCh] at hch
    simp only at hop
    subst hop hch
    exact hmem'

section PersistE

variable {L : Sym → OpLaws} {Sb Sa : Store} (h : StorePersistE L Sb Sa)
include h

theorem StorePersistE.find_before (c : C) : Sa.find (Sb.find c) = Sa.find c :=
  h.no_split _ _ (h.before_idem c)

theorem StorePersistE.find_comp : Sa.find ∘ Sb.find = Sa.find :=
  funext h.find_before

theorem StorePersistE.find_self (c : C) : Sa.find (Sa.find c) = Sa.find c := h.after_idem c

/-- A fixed-arity node persists with its children mapped (`LiteralFixed`
unpacked for a tuple). -/
theorem StorePersistE.tuple {id : NodeId} {g : Sym} {cs : List C}
    (hmem : (id, ⟨g, .tuple cs⟩) ∈ Sb.nodes) : (id, ⟨g, .tuple (cs.map Sa.find)⟩) ∈ Sa.nodes := by
  obtain ⟨⟨op, ch⟩, hmem', hop, hch⟩ := h.fixed _ _ hmem rfl
  cases ch <;> simp [CanonCh] at hch
  simp only at hop
  subst hop hch
  exact hmem'

/-- **One normalization step before the round is an equality of the theory
after it.** A splice through a node the rebuild recanonicalized is a
splice through its normal form (stored, or collapsed to the single or the
unit), joined to the mapped children by the recanonicalization steps. -/
theorem ACStep.mapE {f : Sym} {m m' : Multiset C} (hs : ACStep Sb.graph L f m m') :
    EqAC Sa.graph L f (m.map Sa.find) (m'.map Sa.find) := by
  cases hs with
  | splice hmem =>
      rename_i m₁ rest id
      obtain ⟨m₁'', hr, hfin⟩ := h.mset _ _ _ hmem
      have hR : EqAC Sa.graph L f (m₁.map Sa.find + rest.map Sa.find) (m₁'' + rest.map Sa.find) :=
        (EqAC.of_rtg (rtg_mono (fun _ _ hs => RStep.toAC hs) hr)).add_right _
      have hgoal : EqAC Sa.graph L f ({Sa.find id} + rest.map Sa.find) (m₁'' + rest.map Sa.find) := by
        rcases hfin with ⟨id', hmem', hid⟩ | ⟨x, rfl, hid⟩ | ⟨rfl, u, hu, hid⟩
        · rw [hid]
          exact .rel _ _ (ACStep.splice (L := L) (rest := rest.map Sa.find) hmem')
        · have hx : x ∈ m₁.map Sa.find := Multiset.mem_of_le (rtg_RStep_le hr) (by simp)
          obtain ⟨y, -, rfl⟩ := Multiset.mem_map.1 hx
          simp only [Store.graph_find] at hid
          rw [hid, h.find_self]
          exact .refl _
        · rw [hid, zero_add]
          exact .rel _ _ (ACStep.unit (G := Sa.graph) (L := L) (f := f) hu)
      have e : ({Sb.find id} + rest).map Sa.find = {Sa.find id} + rest.map Sa.find := by
        simp [h.find_before]
      simp only [Store.graph_find]
      rw [e, Multiset.map_add]
      exact hgoal.trans _ _ _ (hR.symm _ _)
  | unit hu =>
      refine .rel _ _ ?_
      simpa [Multiset.map_add, h.find_before] using ACStep.unit (G := Sa.graph) (f := f) hu
  | nil hr =>
      refine .rel _ _ ?_
      simpa [Multiset.map_add, Multiset.map_nsmul] using ACStep.nil (G := Sa.graph) hr
  | inv hg hmem =>
      refine .rel _ _ ?_
      have hmem' := h.tuple hmem
      have h1 : ACStep Sa.graph L f ({_} + {Sa.find _} + m'.map Sa.find) (m'.map Sa.find) :=
        ACStep.inv (L := L) (f := f) (rest := m'.map Sa.find) hg hmem'
      simpa [Multiset.map_add, h.find_before] using h1

theorem ACIStep.mapE {f : Sym} {s s' : Finset C} (hs : ACIStep Sb.graph L f s s') :
    EqACI Sa.graph L f (s.image Sa.find) (s'.image Sa.find) := by
  cases hs with
  | splice hmem =>
      rename_i s₁ rest id
      obtain ⟨s₁'', hr, hfin⟩ := h.set _ _ _ hmem
      have hR : EqACI Sa.graph L f (s₁.image Sa.find ∪ rest.image Sa.find)
          (s₁'' ∪ rest.image Sa.find) :=
        (EqACI.of_rtg (rtg_mono (fun _ _ hs => RSetStep.toACI hs) hr)).union_right _
      have hgoal : EqACI Sa.graph L f (insert (Sa.find id) (rest.image Sa.find))
          (s₁'' ∪ rest.image Sa.find) := by
        rcases hfin with ⟨id', hmem', hid⟩ | ⟨x, rfl, hid⟩ | ⟨rfl, u, hu, hid⟩
        · rw [hid]
          exact .rel _ _ (ACIStep.splice (L := L) (rest := rest.image Sa.find) hmem')
        · have hx : x ∈ s₁.image Sa.find := rtg_RSetStep_subset hr (by simp)
          obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 hx
          simp only [Store.graph_find] at hid
          rw [hid, h.find_self, Finset.singleton_union]
          exact .refl _
        · rw [hid, Finset.empty_union]
          exact .rel _ _ (ACIStep.unit (G := Sa.graph) (L := L) (f := f) hu)
      have e : (insert (Sb.find id) rest).image Sa.find = insert (Sa.find id) (rest.image Sa.find) := by
        simp [Finset.image_insert, h.find_before]
      simp only [Store.graph_find]
      rw [e, Finset.image_union]
      exact hgoal.trans _ _ _ (hR.symm _ _)
  | unit hu =>
      refine .rel _ _ ?_
      simpa [Finset.image_insert, h.find_before] using ACIStep.unit (G := Sa.graph) (f := f) hu

theorem AStep.mapE {f : Sym} {l l' : List C} (hs : AStep Sb.graph L f l l') :
    EqA Sa.graph L f (l.map Sa.find) (l'.map Sa.find) := by
  refine .rel _ _ ?_
  cases hs with
  | splice hmem =>
      rename_i a b l₁ id
      have hmem' := h.seq _ _ _ hmem
      have h1 : AStep Sa.graph L _ (a.map Sa.find ++ [Sa.find id] ++ b.map Sa.find) _ :=
        AStep.splice (L := L) (a := a.map Sa.find) (b := b.map Sa.find) hmem'
      simpa [h.find_before] using h1
  | unit hu =>
      simpa [h.find_before] using AStep.unit (G := Sa.graph) (f := f) (a := _) (b := _) hu

theorem EqAC.mapE {f : Sym} {m m' : Multiset C} (hs : EqAC Sb.graph L f m m') :
    EqAC Sa.graph L f (m.map Sa.find) (m'.map Sa.find) :=
  eqvGen_map (Multiset.map Sa.find) (fun _ _ hs => ACStep.mapE h hs) hs

theorem EqACI.mapE {f : Sym} {s s' : Finset C} (hs : EqACI Sb.graph L f s s') :
    EqACI Sa.graph L f (s.image Sa.find) (s'.image Sa.find) :=
  eqvGen_map (Finset.image Sa.find) (fun _ _ hs => ACIStep.mapE h hs) hs

theorem EqA.mapE {f : Sym} {l l' : List C} (hs : EqA Sb.graph L f l l') :
    EqA Sa.graph L f (l.map Sa.find) (l'.map Sa.find) :=
  eqvGen_map (List.map Sa.find) (fun _ _ hs => AStep.mapE h hs) hs

/-- The class a normalized multiset ends in persists: the recanonicalized
node (or the leaf it collapsed to) is in the mapped class, and its spelling
is joined to the mapped one by the recanonicalization steps. -/
theorem Final.persistE_mset {f : Sym} {m : Multiset C} {c : C}
    (hf : Final Sb.graph L f (.mset m) (fun x => m = {x}) (m = 0) c) :
    ∃ m'', EqAC Sa.graph L f (m.map Sa.find) m'' ∧ MCanon Sa.graph m'' ∧
      Final Sa.graph L f (.mset m'') (fun x => m'' = {x}) (m'' = 0) (Sa.find c) := by
  rcases hf with ⟨id, hmem, rfl⟩ | ⟨x, rfl, rfl⟩ | ⟨rfl, u, hu, rfl⟩
  · obtain ⟨m'', hr, hfin⟩ := h.mset _ _ _ hmem
    refine ⟨m'', EqAC.of_rtg (rtg_mono (fun _ _ hs => RStep.toAC hs) hr), ?_, ?_⟩
    · exact (MCanon.map h.after_idem m).of_le (rtg_RStep_le hr)
    · simpa [Store.graph_find, h.find_before] using hfin
  · refine ⟨{Sa.find x}, by simp [Multiset.map_singleton]; exact .refl _, ?_, ?_⟩
    · intro y hy; simp at hy; subst hy; exact h.find_self x
    · exact Or.inr (Or.inl ⟨Sa.find x, rfl, by simp [Store.graph_find, h.find_before, h.find_self]⟩)
  · refine ⟨0, by simp; exact .refl _, by intro y hy; simp at hy, ?_⟩
    exact Or.inr (Or.inr ⟨rfl, u, hu, by simp [Store.graph_find, h.find_before]⟩)

theorem Final.persistE_set {f : Sym} {s : Finset C} {c : C}
    (hf : Final Sb.graph L f (.set s) (fun x => s = {x}) (s = ∅) c) :
    ∃ s'', EqACI Sa.graph L f (s.image Sa.find) s'' ∧ SCanon Sa.graph s'' ∧
      Final Sa.graph L f (.set s'') (fun x => s'' = {x}) (s'' = ∅) (Sa.find c) := by
  rcases hf with ⟨id, hmem, rfl⟩ | ⟨x, rfl, rfl⟩ | ⟨rfl, u, hu, rfl⟩
  · obtain ⟨s'', hr, hfin⟩ := h.set _ _ _ hmem
    refine ⟨s'', EqACI.of_rtg (rtg_mono (fun _ _ hs => RSetStep.toACI hs) hr), ?_, ?_⟩
    · intro y hy
      obtain ⟨z, -, rfl⟩ := Finset.mem_image.1 (rtg_RSetStep_subset hr hy)
      exact h.after_idem z
    · simpa [Store.graph_find, h.find_before] using hfin
  · refine ⟨{Sa.find x}, by simp [Finset.image_singleton]; exact .refl _, ?_, ?_⟩
    · intro y hy; simp at hy; subst hy; exact h.find_self x
    · exact Or.inr (Or.inl ⟨Sa.find x, rfl, by simp [Store.graph_find, h.find_before, h.find_self]⟩)
  · refine ⟨∅, by simp; exact .refl _, by intro y hy; simp at hy, ?_⟩
    exact Or.inr (Or.inr ⟨rfl, u, hu, by simp [Store.graph_find, h.find_before]⟩)

theorem Final.persistE_seq {f : Sym} {l : List C} {c : C}
    (hf : Final Sb.graph L f (.seq l) (fun x => l = [x]) (l = []) c) :
    Final Sa.graph L f (.seq (l.map Sa.find)) (fun x => l.map Sa.find = [x])
      (l.map Sa.find = []) (Sa.find c) := by
  rcases hf with ⟨id, hmem, rfl⟩ | ⟨x, rfl, rfl⟩ | ⟨rfl, u, hu, rfl⟩
  · exact Or.inl ⟨id, h.seq _ _ _ hmem, by simp [Store.graph_find, h.find_before]⟩
  · exact Or.inr (Or.inl ⟨Sa.find x, by simp, by simp [Store.graph_find, h.find_before, h.find_self]⟩)
  · exact Or.inr (Or.inr ⟨by simp, u, hu, by simp [Store.graph_find, h.find_before]⟩)

/-- **A right-hand side present modulo the theory stays present modulo the
theory across a rebuild that applied the laws.** No routing and no literal
persistence of the n-ary nodes: the value is the mapped class. -/
theorem DenE.persist {σ : Binding} {t : Pat} {c : C} (hd : DenE Sb.graph L σ t c) :
    DenE Sa.graph L σ t (Sa.find c) := by
  have hfb := h.find_before
  have hfc := h.find_comp
  induction hd with
  | var hx =>
      simp only [Store.graph_find, hfb]
      exact DenE.var hx
  | plain hl hall hmem ih =>
      rename_i f args cs id
      have hmem' := h.tuple hmem
      simp only [Store.graph_find, hfb]
      refine DenE.plain (by simp [hl]) ?_ hmem'
      intro pc hpc
      rw [List.zip_map_right, List.mem_map] at hpc
      obtain ⟨pc', hpc', rfl⟩ := hpc
      exact ih pc' hpc'
  | comm ha hb hmem iha ihb =>
      rename_i f p q a b id
      simp only [Store.graph_find, hfb]
      rcases hmem with hmem | hmem
      · obtain ⟨⟨op, ch⟩, hmem', hop, hch⟩ := h.fixed _ _ hmem rfl
        cases ch <;> simp [CanonCh] at hch
        simp only at hop
        subst hop
        rcases hch with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact DenE.comm iha ihb (Or.inl hmem')
        · exact DenE.comm iha ihb (Or.inr hmem')
      · obtain ⟨⟨op, ch⟩, hmem', hop, hch⟩ := h.fixed _ _ hmem rfl
        cases ch <;> simp [CanonCh] at hch
        simp only at hop
        subst hop
        rcases hch with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact DenE.comm iha ihb (Or.inr hmem')
        · exact DenE.comm iha ihb (Or.inl hmem')
  | assoc hl hall hpre hsuf hsteps hcan hfin ih =>
      rename_i f pre suf args cs u v l' c
      refine DenE.assoc (cs := cs.map Sa.find) (u := u) (v := v) (l' := l'.map Sa.find)
        (by simp [hl]) ?_ hpre hsuf ?_ ?_ (Final.persistE_seq h hfin)
      · intro pc hpc
        rw [List.zip_map_right, List.mem_map] at hpc
        obtain ⟨pc', hpc', rfl⟩ := hpc
        exact ih pc' hpc'
      · have := EqA.mapE h hsteps
        simpa [List.map_append, List.map_map, hfc] using this
      · intro x hx
        obtain ⟨y, -, rfl⟩ := List.mem_map.1 hx
        exact h.after_idem y
  | ac hl hmult hden hrest hsteps hcan hfin ih =>
      rename_i f elems rest cks m₀ m' c
      obtain ⟨m'', hE, hcan'', hfin''⟩ := Final.persistE_mset h hfin
      refine DenE.ac (cks := cks.map fun ck => (Sa.find ck.1, ck.2)) (m₀ := m₀) (m' := m'')
        (by simp [hl]) ?_ ?_ hrest ?_ hcan'' hfin''
      · intro ek hek
        rw [List.zip_map_right, List.mem_map] at hek
        obtain ⟨ek', hek', rfl⟩ := hek
        exact hmult ek' hek'
      · intro ek hek hk
        rw [List.zip_map_right, List.mem_map] at hek
        obtain ⟨ek', hek', rfl⟩ := hek
        exact ih ek' hek' hk
      · have := EqAC.mapE h hsteps
        have e : (acChildren cks + m₀.map Sb.find).map Sa.find =
            acChildren (cks.map fun ck => (Sa.find ck.1, ck.2)) + m₀.map Sa.find := by
          simp [Multiset.map_add, Multiset.map_map, acChildren_map, hfb]
        simp only [Store.graph_find] at this ⊢
        rw [e] at this
        exact this.trans _ _ _ hE
  | aci hl hall hrest hsteps hcan hfin ih =>
      rename_i f elems rest cs s₀ s' c
      obtain ⟨s'', hE, hcan'', hfin''⟩ := Final.persistE_set h hfin
      refine DenE.aci (cs := cs.map Sa.find) (s₀ := s₀) (s' := s'')
        (by simp [hl]) ?_ hrest ?_ hcan'' hfin''
      · intro pc hpc
        rw [List.zip_map_right, List.mem_map] at hpc
        obtain ⟨pc', hpc', rfl⟩ := hpc
        exact ih pc' hpc'
      · have := EqACI.mapE h hsteps
        have htf : (cs.map Sa.find).toFinset = cs.toFinset.image Sa.find := by ext; simp
        have e : (cs.toFinset ∪ s₀.image Sb.find).image Sa.find =
            (cs.map Sa.find).toFinset ∪ s₀.image Sa.find := by
          simp [Finset.image_union, Finset.image_image, htf, hfc]
        simp only [Store.graph_find] at this ⊢
        rw [e] at this
        exact this.trans _ _ _ hE

end PersistE

/-! ## Fired modulo the theory, and the chain without routing -/

/-- The consequence of one action, modulo the theory. -/
def ActFiredE (G : Graph) (L : Sym → OpLaws) (σ : Binding) : Action → Prop
  | .insert t => ∃ c, DenE G L σ t c
  | .union a b => ∃ c, DenE G L σ a c ∧ DenE G L σ b c
  | .subsume _ => True

/-- Every consequence of the instance is present modulo the theory: the
match root's class holds a node denoting the right-hand side. -/
def FiredE (G : Graph) (L : Sym → OpLaws) (σ : Binding) (rule : Rule) : Prop :=
  ∀ act ∈ rule.actions, ActFiredE G L σ act

theorem FiredN.toFiredE {G : Graph} (hc : G.ChildrenCanon) (hi : G.FindIdem) {L : Sym → OpLaws}
    {σ : Binding} {rule : Rule} (h : FiredN G L σ rule) : FiredE G L σ rule := by
  intro act hact
  have := h act hact
  cases act with
  | insert t => obtain ⟨c, hc'⟩ := this; exact ⟨c, hc'.toDenE hc hi⟩
  | union a b => obtain ⟨c, ha, hb⟩ := this; exact ⟨c, ha.toDenE hc hi, hb.toDenE hc hi⟩
  | subsume _ => trivial

/-- A fired instance stays fired modulo the theory across any rebuild
meeting `StorePersistE`: no routing. -/
theorem firedE_persist {L : Sym → OpLaws} {Sb Sa : Store} (h : StorePersistE L Sb Sa)
    {σ : Binding} {rule : Rule} (hf : FiredE Sb.graph L σ rule) : FiredE Sa.graph L σ rule := by
  intro act hact
  have := hf act hact
  cases act with
  | insert t => obtain ⟨c, hc⟩ := this; exact ⟨_, hc.persist h⟩
  | union a b => obtain ⟨c, ha, hb⟩ := this; exact ⟨_, ha.persist h, hb.persist h⟩
  | subsume _ => trivial

variable {L : Sym → OpLaws}

/-- The invariant with latency, modulo the theory, with no guard. -/
def InvLagE (A : SActRoundN L) (rules : List Rule) : Prop :=
  ∀ rule ∈ rules, ∀ σ, Matches A.Sb.index rule.atoms σ → FiredE A.Sa.graph L σ rule

theorem invLagE_zero {sig : Sym → Kind} {rules : List Rule} (A : SActRoundN L)
    (hwf : StoreWF A.Sb A.Sa) (hatoms : RulesWF sig A.R.before rules) (hmatch : MatchersOK rules)
    (hemit : EmitsAllN A rules) : InvLagE A rules := by
  intro rule hr σ hm
  rw [← A.before_eq] at hm
  exact (fired_after_actions_N A hwf.after_idem
    (hemit rule hr σ ((MatcherOK.naive_iff (hmatch rule hr) (hatoms rule hr) σ).2 hm))).toFiredE
    hwf.children_canon hwf.after_idem

/-- `inv_step_N` modulo the theory, under any routing: an old instance is
transported by `firedE_persist`, whatever laws the rebuild applied; a new
one is emitted by the naive run or a variant and fired by the actions. -/
theorem inv_step_E {sig : Sym → Kind} {naive : Rule → Bool} {rules : List Rule}
    {prev A : SActRoundN L} (hlink : A.Sb = prev.Sa)
    (hprev : prev.R.WF) (htr : prev.R.tracking = true) (hAp : StorePersistE L A.Sb A.Sa)
    (hatoms₀ : RulesWF sig prev.R.before rules) (hatoms₁ : RulesWF sig prev.R.after rules)
    (hmatch : MatchersOK rules) (hemit : EmitsRoundN naive prev.R A rules)
    (hinv : InvLagE prev rules) : InvLagE A rules := by
  intro rule hr σ hm
  have hRlink : A.R.before = prev.R.after := by rw [A.before_eq, prev.after_eq, hlink]
  have hm' : Matches prev.R.after rule.atoms σ := by rw [prev.after_eq, ← hlink]; exact hm
  have hnew : σ ∈ rule.matcher.naive prev.R.after :=
    (MatcherOK.naive_iff (hmatch rule hr) (hatoms₁ rule hr) σ).2 hm'
  obtain ⟨h1, h2⟩ := hemit rule hr
  rw [hRlink] at h1 h2
  have hfire : A.emitted rule σ → FiredE A.Sa.graph L σ rule := fun he =>
    (fired_after_actions_N A hAp.after_idem he).toFiredE hAp.children_canon hAp.after_idem
  by_cases hold : Matches prev.R.before rule.atoms σ
  · rw [prev.before_eq] at hold
    have hf := hinv rule hr σ hold
    rw [← hlink] at hf
    exact firedE_persist hAp hf
  · cases hn : naive rule with
    | true => exact hfire (h1 hn σ hnew)
    | false =>
        apply hfire
        have hold' : σ ∉ rule.matcher.naive prev.R.before := fun h =>
          hold ((MatcherOK.naive_iff (hmatch rule hr) (hatoms₀ rule hr) σ).1 h)
        obtain ⟨k, ak, hk, hv⟩ :=
          MatcherOK.round_complete (hmatch rule hr) hprev htr (hatoms₀ rule hr) (hatoms₁ rule hr) hnew hold'
        exact h2 hn k ak hk σ hv

/-- A chain of store rounds with any routing per round: with completion on
the engine's routing is `route naive false = naive` (no `respelled`
re-match). `SChainN` is a special case (`SChainN.toE`). -/
def SChainE (rules : List Rule) : SActRoundN L → List (SActRoundN L) → Prop
  | _, [] => True
  | prev, A :: As => A.Sb = prev.Sa ∧ (∃ rt : Rule → Bool, EmitsRoundN rt prev.R A rules) ∧
      SChainE rules A As

theorem SChainN.toE {naive : Rule → Bool} {rules : List Rule} :
    ∀ {A₀ : SActRoundN L} {As : List (SActRoundN L)}, SChainN naive rules A₀ As → SChainE rules A₀ As
  | _, [], _ => trivial
  | _, _ :: _, ⟨hlink, ⟨_, _, hemit⟩, hchain⟩ => ⟨hlink, ⟨_, hemit⟩, SChainN.toE hchain⟩

/-- `RoundOKN` with the sequence nodes persisting literally. -/
structure RoundOKE (sig : Sym → Kind) (rules : List Rule) (A : SActRoundN L) : Prop where
  wf : A.R.WF
  tracking : A.R.tracking = true
  store : StorePersistE L A.Sb A.Sa
  atoms : RulesWF sig A.R.after rules

theorem RoundOKE.toN {sig : Sym → Kind} {rules : List Rule} {A : SActRoundN L}
    (h : RoundOKE sig rules A) : RoundOKN sig rules A :=
  ⟨h.wf, h.tracking, h.store.toStorePersistN, h.atoms⟩

theorem invLag_chain_E {sig : Sym → Kind} {rules : List Rule}
    (hmatch : MatchersOK rules) : ∀ (A₀ : SActRoundN L) (As : List (SActRoundN L)),
    RulesWF sig A₀.R.before rules → (∀ A ∈ A₀ :: As, RoundOKE sig rules A) →
    EmitsAllN A₀ rules → SChainE rules A₀ As → ∀ A ∈ A₀ :: As, InvLagE A rules := by
  intro A₀ As h₀ hok hemit₀ hchain
  have main : ∀ (B : SActRoundN L) (Bs : List (SActRoundN L)),
      RulesWF sig B.R.before rules → (∀ A ∈ B :: Bs, RoundOKE sig rules A) →
      InvLagE B rules → SChainE rules B Bs → ∀ A ∈ Bs, InvLagE A rules := by
    intro B Bs
    induction Bs generalizing B with
    | nil => intro _ _ _ _ A hA; simp at hA
    | cons A As ih =>
        intro h₀ hok hinv hchain A' hA'
        obtain ⟨hlink, ⟨rt, hemit⟩, hchain'⟩ := hchain
        have hokB := hok B (by simp)
        have hokA := hok A (by simp)
        have hinvA : InvLagE A rules :=
          inv_step_E hlink hokB.wf hokB.tracking hokA.store h₀ hokB.atoms hmatch hemit hinv
        have hRlink : A.R.before = B.R.after := by rw [A.before_eq, B.after_eq, hlink]
        rcases List.mem_cons.1 hA' with rfl | hA'
        · exact hinvA
        · exact ih A (by rw [hRlink]; exact hokB.atoms) (fun C hC => hok C (by simp [hC])) hinvA
            hchain' A' hA'
  have hinv₀ := invLagE_zero A₀ (hok A₀ (by simp)).store.toStoreWF h₀ hmatch hemit₀
  intro A hA
  rcases List.mem_cons.1 hA with rfl | hA
  · exact hinv₀
  · exact main A₀ As h₀ hok hinv₀ hchain A hA

/-- Every match on the index of `S` is fired modulo the theory in its store. -/
def InvE (S : Store) (L : Sym → OpLaws) (rules : List Rule) : Prop :=
  ∀ rule ∈ rules, ∀ σ, Matches S.index rule.atoms σ → FiredE S.graph L σ rule

/-- **`saturation_complete_N` without the routing.** Along a run with any
routing per round, at a round that changed nothing, every match on the index
is fired modulo the theory: the root class holds a node denoting the
right-hand side, whatever laws the rebuilds applied to the nodes it was
built through. -/
theorem saturation_complete_E {sig : Sym → Kind} {rules : List Rule}
    (A₀ : SActRoundN L) (As : List (SActRoundN L)) (hmatch : MatchersOK rules)
    (h₀ : RulesWF sig A₀.R.before rules) (hok : ∀ A ∈ A₀ :: As, RoundOKE sig rules A)
    (hemit₀ : EmitsAllN A₀ rules) (hchain : SChainE rules A₀ As)
    {A : SActRoundN L} (hA : A ∈ A₀ :: As) (hfix : A.Unchanged) : InvE A.Sa L rules := by
  have hinv := invLag_chain_E hmatch A₀ As h₀ hok hemit₀ hchain A hA
  obtain ⟨hn, hf, hs⟩ := hfix
  have hfeq : A.Sa.find = A.Sb.find := funext hf
  have hin : ∀ p, p ∈ A.Sa.index.nodes ↔ p ∈ A.Sb.index.nodes := by
    intro p; simp only [Store.mem_index, hn, hs]
  intro rule hr σ hm
  exact hinv rule hr σ (matches_congr hin hfeq hm)

/-- `saturation_complete_E` at the round where the engine's stop test holds. -/
theorem saturation_complete_E_engine {sig : Sym → Kind} {rules : List Rule}
    (A₀ : SActRoundN L) (As : List (SActRoundN L)) (hmatch : MatchersOK rules)
    (h₀ : RulesWF sig A₀.R.before rules) (hok : ∀ A ∈ A₀ :: As, RoundOKE sig rules A)
    (hemit₀ : EmitsAllN A₀ rules) (hchain : SChainE rules A₀ As)
    {A : SActRoundN L} (hA : A ∈ A₀ :: As) {K : Completion} (E : EnginePhase K A.Sb A.Sa)
    (hstop : E.Stop) : InvE A.Sa L rules :=
  saturation_complete_E A₀ As hmatch h₀ hok hemit₀ hchain hA (engine_stop_unchanged_N A E hstop)

/-! ## The store at a completion fixpoint -/

/-- **The store is closed under the theory.** Two classes equal modulo the
laws and the store's equations are one class, for every n-ary operator;
two nodes of one content, or a pair in either order, are in one class
(the hash-cons). This is the store reading of the completion completeness
theorem at a fixpoint: `ac_equal_same_class` and `CompleteAtoms.same_class`
(two `=_E`-equal active nodes of a converged state are in one class),
`I0Active` (every class holds an active node), and congruence closure. -/
structure TheoryClosed (S : Store) (L : Sym → OpLaws) : Prop where
  mset : ∀ f c c', EqAC S.graph L f {S.find c} {S.find c'} → S.find c = S.find c'
  set : ∀ f c c', EqACI S.graph L f {S.find c} {S.find c'} → S.find c = S.find c'
  seq : ∀ f c c', EqA S.graph L f [S.find c] [S.find c'] → S.find c = S.find c'
  node : ∀ id₁ id₂ n, (id₁, n) ∈ S.nodes → (id₂, n) ∈ S.nodes → S.find id₁ = S.find id₂
  pair : ∀ id₁ id₂ f a b, (id₁, ⟨f, .spair a b⟩) ∈ S.nodes → (id₂, ⟨f, .spair b a⟩) ∈ S.nodes →
    S.find id₁ = S.find id₂

/-! ### The values of a right-hand side are determined by the binding -/

theorem rmultOk_unique {σ : Binding} {μ : Mult} {n n' : Nat} (h : RMultOk σ μ n)
    (h' : RMultOk σ μ n') : n = n' := by
  cases μ with
  | exact k => simp only [RMultOk] at h h'; omega
  | var k _ _ => simp only [RMultOk] at h h'; rw [h] at h'; exact Option.some.inj h'

theorem seqRestOk_unique {σ : Binding} {r : Option Var} {u u' : List C} (h : SeqRestOk σ r u)
    (h' : SeqRestOk σ r u') : u = u' := by
  cases r with
  | none => simp only [SeqRestOk] at h h'; rw [h, h']
  | some r => simp only [SeqRestOk] at h h'; rw [h] at h'; exact Option.some.inj h'

theorem msetRestVal_unique {σ : Binding} {r : Option Var} {m m' : Multiset C}
    (h : MsetRestVal σ r m) (h' : MsetRestVal σ r m') : m = m' := by
  cases r with
  | none => simp only [MsetRestVal] at h h'; rw [h, h']
  | some r => simp only [MsetRestVal] at h h'; rw [h] at h'; exact Option.some.inj h'

theorem setRestVal_unique {σ : Binding} {r : Option Var} {s s' : Finset C}
    (h : SetRestVal σ r s) (h' : SetRestVal σ r s') : s = s' := by
  cases r with
  | none => simp only [SetRestVal] at h h'; rw [h, h']
  | some r => simp only [SetRestVal] at h h'; rw [h] at h'; exact Option.some.inj h'

/-- Two value lists of the same argument list agree when every value of
the first is the only value of its argument. -/
theorem zip_vals_eq {P : Pat → C → Prop} {args : List Pat} : ∀ {cs cs' : List C},
    args.length = cs.length → args.length = cs'.length →
    (∀ pc ∈ args.zip cs, ∀ c', P pc.1 c' → pc.2 = c') →
    (∀ pc ∈ args.zip cs', P pc.1 pc.2) → cs = cs' := by
  induction args with
  | nil => intro cs cs' h h' _ _; cases cs <;> cases cs' <;> simp_all
  | cons a args ih =>
      intro cs cs' h h' hih hd
      cases cs with
      | nil => simp at h
      | cons c cs =>
        cases cs' with
        | nil => simp at h'
        | cons c' cs' =>
          have e1 : c = c' := hih (a, c) (by simp) c' (hd (a, c') (by simp))
          have e2 : cs = cs' := ih (by simpa using h) (by simpa using h')
            (fun pc hpc => hih pc (by simp [hpc])) (fun pc hpc => hd pc (by simp [hpc]))
          rw [e1, e2]

/-- The same for the counted elements of an AC application: an element of
count `0` contributes nothing, whatever its value. -/
theorem acChildren_eq {σ : Binding} {P : Pat → C → Prop} {elems : List (Pat × Mult)} :
    ∀ {cks cks' : List (C × Nat)},
    elems.length = cks.length → elems.length = cks'.length →
    (∀ ek ∈ elems.zip cks, RMultOk σ ek.1.2 ek.2.2) →
    (∀ ek ∈ elems.zip cks', RMultOk σ ek.1.2 ek.2.2) →
    (∀ ek ∈ elems.zip cks, ek.2.2 ≠ 0 → ∀ c', P ek.1.1 c' → ek.2.1 = c') →
    (∀ ek ∈ elems.zip cks', ek.2.2 ≠ 0 → P ek.1.1 ek.2.1) →
    acChildren cks = acChildren cks' := by
  induction elems with
  | nil => intro cks cks' h h' _ _ _ _; cases cks <;> cases cks' <;> simp_all
  | cons e elems ih =>
      intro cks cks' h h' hm hm' hih hd
      cases cks with
      | nil => simp at h
      | cons ck cks =>
        cases cks' with
        | nil => simp at h'
        | cons ck' cks' =>
          obtain ⟨c, k⟩ := ck
          obtain ⟨c', k'⟩ := ck'
          have hk : k = k' := rmultOk_unique (hm (e, (c, k)) (by simp)) (hm' (e, (c', k')) (by simp))
          subst hk
          have tail : acChildren cks = acChildren cks' :=
            ih (by simpa using h) (by simpa using h') (fun ek hek => hm ek (by simp [hek]))
              (fun ek hek => hm' ek (by simp [hek])) (fun ek hek => hih ek (by simp [hek]))
              (fun ek hek => hd ek (by simp [hek]))
          by_cases hk0 : k = 0
          · subst hk0; simp [acChildren, tail]
          · have hc : c = c' := hih (e, (c, k)) (by simp) hk0 c' (hd (e, (c', k)) (by simp) hk0)
            rw [hc]; simp [acChildren, tail]

theorem Final.find_eq {G : Graph} (hi : G.FindIdem) {L : Sym → OpLaws} {f : Sym} {ch : Children}
    {single : C → Prop} {empty : Prop} {c : C} (hf : Final G L f ch single empty c) :
    G.find c = c := by
  rcases hf with ⟨id, -, rfl⟩ | ⟨x, -, rfl⟩ | ⟨-, u, -, rfl⟩ <;> exact hi _

/-- **Under closure, a right-hand side present modulo the theory has every
value `add` would build in that class.** A `DenN` value is a chain to a
stored spelling; it is equal in the theory to the `DenE` class, so the two
are one class. -/
theorem denE_denN_eq {S : Store} (hi : S.graph.FindIdem) (hc : S.graph.ChildrenCanon)
    (hcl : TheoryClosed S L) {σ : Binding} {t : Pat} {c c' : C} (hE : DenE S.graph L σ t c)
    (hN : DenN S.graph L σ t c') : c = c' := by
  induction hE generalizing c' with
  | var hx =>
      cases hN with
      | var hx' => rw [hx] at hx'; cases hx'; rfl
  | plain hl hall hmem ih =>
      cases hN with
      | plain hl' hall' hmem' =>
          have e := zip_vals_eq hl hl' ih hall'
          subst e
          exact hcl.node _ _ _ hmem hmem'
  | comm ha hb hmem iha ihb =>
      cases hN with
      | comm ha' hb' hmem' =>
          have e1 := iha ha'
          have e2 := ihb hb'
          subst e1 e2
          rcases hmem with h1 | h1 <;> rcases hmem' with h2 | h2
          · exact hcl.node _ _ _ h1 h2
          · exact hcl.pair _ _ _ _ _ h1 h2
          · exact hcl.pair _ _ _ _ _ h1 h2
          · exact hcl.node _ _ _ h1 h2
  | assoc hl hall hpre hsuf hsteps hcan hfin ih =>
      rename_i f pre suf args cs u v l' c
      cases hN with
      | assoc hl' hall' hpre' hsuf' hsteps' hfin' =>
          rename_i cs' u' v' l₂
          have ecs := zip_vals_eq hl hl' ih hall'
          have eu := seqRestOk_unique hpre hpre'
          have ev := seqRestOk_unique hsuf hsuf'
          subst ecs eu ev
          have hstart : LCanon S.graph (u.map S.graph.find ++ cs ++ v.map S.graph.find) := by
            intro x hx
            simp only [List.mem_append, List.mem_map] at hx
            rcases hx with (⟨y, -, rfl⟩ | hx) | ⟨y, -, rfl⟩
            · exact hi y
            · obtain ⟨a, ha⟩ := exists_mem_zip_of_mem_right hl hx
              obtain ⟨c₀, hc₀⟩ := (hall' _ ha).exists_find
              simp only at hc₀; rw [hc₀]; exact hi c₀
            · exact hi y
          have h1 : EqA S.graph L f [c] l' := (hfin.eqA hcan).symm _ _
          have h2 : EqA S.graph L f l₂ [c'] := hfin'.eqA (rtg_AStep_canon hc hsteps' hstart)
          have h3 : EqA S.graph L f [c] [c'] :=
            (h1.trans _ _ _ (hsteps.symm _ _)).trans _ _ _ ((EqA.of_rtg hsteps').trans _ _ _ h2)
          have hcc : S.find c = c := hfin.find_eq hi
          have hcc' : S.find c' = c' := hfin'.find_eq hi
          have := hcl.seq f c c' (by rw [hcc, hcc']; exact h3)
          rwa [hcc, hcc'] at this
  | ac hl hmult hden hrest hsteps hcan hfin ih =>
      rename_i f elems rest cks m₀ m' c
      cases hN with
      | ac hl' hmult' hden' hrest' hsteps' hfin' =>
          rename_i cks' m₀' m₂
          have ecks := acChildren_eq hl hl' hmult hmult' ih hden'
          have em := msetRestVal_unique hrest hrest'
          subst em
          rw [← ecks] at hsteps'
          have hstart : MCanon S.graph (acChildren cks + m₀.map S.graph.find) := by
            rw [ecks]
            refine acChildren_canon hi ?_ m₀
            intro ck hck hk
            obtain ⟨e, he⟩ := exists_mem_zip_of_mem_right hl' hck
            exact (hden' _ he hk).exists_find
          have h1 : EqAC S.graph L f {c} m' := (hfin.eqAC hcan).symm _ _
          have h2 : EqAC S.graph L f m₂ {c'} := hfin'.eqAC (rtg_ACStep_canon hc hsteps' hstart)
          have h3 : EqAC S.graph L f {c} {c'} :=
            (h1.trans _ _ _ (hsteps.symm _ _)).trans _ _ _ ((EqAC.of_rtg hsteps').trans _ _ _ h2)
          have hcc : S.find c = c := hfin.find_eq hi
          have hcc' : S.find c' = c' := hfin'.find_eq hi
          have := hcl.mset f c c' (by rw [hcc, hcc']; exact h3)
          rwa [hcc, hcc'] at this
  | aci hl hall hrest hsteps hcan hfin ih =>
      rename_i f elems rest cs s₀ s' c
      cases hN with
      | aci hl' hall' hrest' hsteps' hfin' =>
          rename_i cs' s₀' s₂
          have ecs := zip_vals_eq hl hl' ih hall'
          have es := setRestVal_unique hrest hrest'
          subst ecs es
          have hstart : SCanon S.graph (cs.toFinset ∪ s₀.image S.graph.find) := by
            intro x hx
            simp only [Finset.mem_union, List.mem_toFinset, Finset.mem_image] at hx
            rcases hx with hx | ⟨y, -, rfl⟩
            · obtain ⟨a, ha⟩ := exists_mem_zip_of_mem_right hl hx
              obtain ⟨c₀, hc₀⟩ := (hall' _ ha).exists_find
              simp only at hc₀; rw [hc₀]; exact hi c₀
            · exact hi y
          have h1 : EqACI S.graph L f {c} s' := (hfin.eqACI hcan).symm _ _
          have h2 : EqACI S.graph L f s₂ {c'} := hfin'.eqACI (rtg_ACIStep_canon hc hsteps' hstart)
          have h3 : EqACI S.graph L f {c} {c'} :=
            (h1.trans _ _ _ (hsteps.symm _ _)).trans _ _ _ ((EqACI.of_rtg hsteps').trans _ _ _ h2)
          have hcc : S.find c = c := hfin.find_eq hi
          have hcc' : S.find c' = c' := hfin'.find_eq hi
          have := hcl.set f c c' (by rw [hcc, hcc']; exact h3)
          rwa [hcc, hcc'] at this

/-- Under closure, the two sides of a union the invariant asks for have one
value, whichever spellings `add` builds for them. -/
theorem invE_union_eq {S : Store} (hi : S.graph.FindIdem) (hc : S.graph.ChildrenCanon)
    (hcl : TheoryClosed S L) {rules : List Rule} (hinv : InvE S L rules) {rule : Rule}
    (hr : rule ∈ rules) {σ : Binding} (hm : Matches S.index rule.atoms σ) {a b : Pat}
    (hab : Action.union a b ∈ rule.actions) {c₁ c₂ : C} (ha : DenN S.graph L σ a c₁)
    (hb : DenN S.graph L σ b c₂) : c₁ = c₂ := by
  obtain ⟨c, hEa, hEb⟩ := hinv rule hr σ hm (.union a b) hab
  rw [← denE_denN_eq hi hc hcl hEa ha, ← denE_denN_eq hi hc hcl hEb hb]

/-- **Saturation with completion on.** A run with any routing per round (no
`respelled` re-match), a round `A` that changed nothing, and its store
closed under the theory (the completion fixpoint). Every match on the index
is fired modulo the theory, and every union its rule asks for holds between
any values `add` builds for the two sides: a re-match would merge nothing. -/
theorem saturation_complete_closed {sig : Sym → Kind} {rules : List Rule}
    (A₀ : SActRoundN L) (As : List (SActRoundN L)) (hmatch : MatchersOK rules)
    (h₀ : RulesWF sig A₀.R.before rules) (hok : ∀ A ∈ A₀ :: As, RoundOKE sig rules A)
    (hemit₀ : EmitsAllN A₀ rules) (hchain : SChainE rules A₀ As)
    {A : SActRoundN L} (hA : A ∈ A₀ :: As) (hfix : A.Unchanged) (hcl : TheoryClosed A.Sa L) :
    ∀ rule ∈ rules, ∀ σ, Matches A.Sa.index rule.atoms σ →
      FiredE A.Sa.graph L σ rule ∧
      ∀ a b, Action.union a b ∈ rule.actions →
        ∀ c₁ c₂, DenN A.Sa.graph L σ a c₁ → DenN A.Sa.graph L σ b c₂ → c₁ = c₂ := by
  have hinv := saturation_complete_E A₀ As hmatch h₀ hok hemit₀ hchain hA hfix
  intro rule hr σ hm
  have hst := (hok A hA).store
  exact ⟨hinv rule hr σ hm, fun a b hab c₁ c₂ ha hb =>
    invE_union_eq hst.after_idem hst.children_canon hcl hinv hr hm hab ha hb⟩

/-! ## The counter-model, completed -/

namespace PersistFails

theorem no_set_A {id : NodeId} {f : Sym} {s : Finset C} (h : (id, ⟨f, .set s⟩) ∈ nodesA) :
    False := by
  simp [nodesA, leaf] at h

theorem no_seq_A {id : NodeId} {f : Sym} {l : List C} (h : (id, ⟨f, .seq l⟩) ∈ nodesA) :
    False := by
  simp [nodesA, leaf] at h

theorem no_seq_B {id : NodeId} {f : Sym} {l : List C} (h : (id, ⟨f, .seq l⟩) ∈ nodesB) :
    False := by
  simp [nodesB, leaf] at h

theorem no_pair_A {id : NodeId} {f : Sym} {a b : C} (h : (id, ⟨f, .spair a b⟩) ∈ nodesA) :
    False := by
  simp [nodesA, leaf] at h

/-- **The after-store of the counter-model is not closed under the theory.**
`d = f{c, w}` and `e' = f{p, q, c, w}` are equal in it, since `f{p, q}` is in
the unit's class, and they are two classes: `Sa` is not a completion
fixpoint, and `denN_persist_fails` says nothing against
`saturation_complete_closed`. -/
theorem sa_not_closed : ¬ TheoryClosed Sa laws := by
  intro hcl
  have h1 : EqAC Sa.graph laws fop {6} {2, 3} := by
    have := ACStep.splice (G := Sa.graph) (L := laws) (f := fop) (rest := 0) (id := 6)
      (m₁ := {2, 3}) (mem_A.2 (by simp))
    have e1 : ({Sa.graph.find 6} : Multiset C) + 0 = {6} := by decide
    have e2 : ({2, 3} : Multiset C) + 0 = {2, 3} := by decide
    rw [e1, e2] at this
    exact Relation.EqvGen.rel _ _ this
  have h2 : EqAC Sa.graph laws fop ({4} + {2, 3}) {2, 3} :=
    Relation.EqvGen.rel _ _
      (by simpa [show Sa.graph.find 4 = 4 from rfl] using
        ACStep.unit (G := Sa.graph) (L := laws) (f := fop) (rest := {2, 3}) (u := 4) rfl)
  have h3 : EqAC Sa.graph laws fop ({4} + {2, 3}) {0, 1, 2, 3} := by
    have := ACStep.splice (G := Sa.graph) (L := laws) (f := fop) (rest := {2, 3}) (id := 8)
      (m₁ := {0, 1}) (mem_A.2 (by simp))
    have e1 : ({Sa.graph.find 8} : Multiset C) + {2, 3} = {4} + {2, 3} := by decide
    have e2 : ({0, 1} : Multiset C) + {2, 3} = {0, 1, 2, 3} := by decide
    rw [e1, e2] at this
    exact Relation.EqvGen.rel _ _ this
  have h4 : EqAC Sa.graph laws fop {7} {0, 1, 2, 3} := by
    have := ACStep.splice (G := Sa.graph) (L := laws) (f := fop) (rest := 0) (id := 7)
      (m₁ := {0, 1, 2, 3}) (mem_A.2 (by simp))
    have e1 : ({Sa.graph.find 7} : Multiset C) + 0 = {7} := by decide
    have e2 : ({0, 1, 2, 3} : Multiset C) + 0 = {0, 1, 2, 3} := by decide
    rw [e1, e2] at this
    exact Relation.EqvGen.rel _ _ this
  have h67 : EqAC Sa.graph laws fop {Sa.find 6} {Sa.find 7} := by
    show EqAC Sa.graph laws fop {6} {7}
    exact h1.trans _ _ _ ((h2.symm _ _).trans _ _ _ (h3.trans _ _ _ (h4.symm _ _)))
  have := hcl.mset fop 6 7 h67
  exact absurd this (by decide)

/-- The completed store: `e' = 7` merged into the class of `d = 6` (completion
rewrites `f{p, q, c, w}` by `f{p, q} → e` to `f{c, w}` and joins the two); the
node `e'` stays stored. -/
def findC : NodeId → C := fun id => if id = 8 ∨ id = 5 then 4 else if id = 7 then 6 else id

def Sc : Store := ⟨nodesA, findC, flags⟩

theorem wfC : StoreWF Sb Sc where
  before_idem := wf.before_idem
  after_idem := by
    intro id; simp only [Sc, Store.graph_find, findC]
    split_ifs <;> simp_all
  no_split := by
    intro id id' h
    simp only [Sb, findB] at h
    simp only [Sc, findC]
    split_ifs at h ⊢ <;> simp_all
  children_canon := by
    intro p hp
    rcases mem_A.1 hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [Sc, leaf, Children.Canon, findC]
  dedup := by
    intro id₁ id₂ n h₁ h₂
    have hnd : (nodesA.map Prod.snd).Nodup := by decide
    have := List.inj_on_of_nodup_map hnd h₁ h₂ rfl
    simp only [Prod.mk.injEq] at this
    rw [this.1]

theorem hcB : Sb.graph.ChildrenCanon := by
  intro p hp
  rcases mem_B.1 hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [Sb, leaf, Children.Canon, findB]

/-- The round from the before-store to the completed store meets
`StorePersistE`: the unit drop on `d`, and `e'` unchanged in content. -/
theorem persistC : StorePersistE laws Sb Sc where
  toStoreWF := wfC
  fixed := by
    intro id n hmem hv
    rcases mem_B.1 hmem with h | h | h | h | h | h | h | h | h <;>
      simp only [leaf, Prod.mk.injEq] at h <;> obtain ⟨rfl, rfl⟩ := h
    all_goals first
      | (simp [Children.isVariadic] at hv; done)
      | exact ⟨_, mem_A.2 (by simp [leaf]), rfl, by simp [CanonCh]⟩
  mset := by
    intro id f m hmem
    rcases mem_mset_B hmem with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · refine ⟨{2, 3}, ?_, Or.inl ⟨6, mem_A.2 (by simp), rfl⟩⟩
      have hm : ({5, 2, 3} : Multiset C).map findC = {findC 4} + {2, 3} := by decide
      show Relation.ReflTransGen (RStep Sc.graph laws fop) (Multiset.map findC {5, 2, 3}) {2, 3}
      rw [hm]
      exact Relation.ReflTransGen.single (RStep.unit (G := Sc.graph) (L := laws) (f := fop) rfl)
    · refine ⟨_, Relation.ReflTransGen.refl, Or.inl ⟨7, ?_, rfl⟩⟩
      show (7, ⟨fop, .mset (({0, 1, 2, 3} : Multiset C).map findC)⟩) ∈ nodesA
      rw [show ({0, 1, 2, 3} : Multiset C).map findC = {0, 1, 2, 3} by decide]
      exact mem_A.2 (by simp)
    · refine ⟨_, Relation.ReflTransGen.refl, Or.inl ⟨8, ?_, rfl⟩⟩
      show (8, ⟨fop, .mset (({0, 1} : Multiset C).map findC)⟩) ∈ nodesA
      rw [show ({0, 1} : Multiset C).map findC = {0, 1} by decide]
      exact mem_A.2 (by simp)
  set := fun _ _ _ hmem => (no_set_B hmem).elim
  seq := fun _ _ _ hmem => (no_seq_B hmem).elim

/-! ### Closure of the completed store

An invariant of the theory separates the classes: the weight of a
multiset is additive, `f{p, q} = e` is `w p + w q = 0`, and `d = f{c, w}` is
`w d = w c + w w`. On canonical classes the weight is injective. -/

/-- The weight of a class: `p ↦ 1`, `q ↦ -1` (their product is the unit),
`c, w` their own names, `d` the sum of `c` and `w`, the unit and the
non-canonical ids `0`, any other class its own name. -/
def w : C → ℤ × ℕ := fun c =>
  ((if c = 0 then 1 else if c = 1 then -1 else 0),
    if c = 2 ∨ c = 3 then c else if c = 6 then 5
    else if c = 0 ∨ c = 1 ∨ c = 4 ∨ c = 5 ∨ c = 7 ∨ c = 8 then 0 else c)

def W (m : Multiset C) : ℤ × ℕ := (m.map w).sum

theorem W_add (m n : Multiset C) : W (m + n) = W m + W n := by
  simp [W, Multiset.map_add, Multiset.sum_add]

theorem W_single (c : C) : W {c} = w c := by simp [W]

theorem W_step {f : Sym} {m m' : Multiset C} (h : ACStep Sc.graph laws f m m') : W m = W m' := by
  cases h with
  | splice hmem =>
      rename_i m₁ rest id
      rw [W_add, W_add, W_single]
      congr 1
      rcases mem_mset_A hmem with ⟨rfl, -, rfl⟩ | ⟨rfl, -, rfl⟩ | ⟨rfl, -, rfl⟩ <;> decide
  | unit hu =>
      simp only [laws, Option.some.injEq] at hu
      subst hu
      rw [W_add, W_single]
      have : w (Sc.graph.find 4) = 0 := by decide
      rw [this, zero_add]
  | nil hr => simp [laws] at hr
  | inv hg => simp [laws] at hg

theorem W_eq {f : Sym} {m m' : Multiset C} (h : EqAC Sc.graph laws f m m') : W m = W m' :=
  eqvGen_invariant W (fun _ _ hs => W_step hs) h

/-- The inverse of the weight on canonical classes. -/
def winv : ℤ × ℕ → C := fun p =>
  if p.1 = 1 then 0 else if p.1 = -1 then 1 else if p.2 = 0 then 4 else if p.2 = 5 then 6 else p.2

theorem winv_w {a : C} (ha : findC a = a) : winv (w a) = a := by
  have hne : ¬ (a = 8 ∨ a = 5) ∧ a ≠ 7 := by
    unfold findC at ha
    split_ifs at ha with h1 h2
    · rw [← ha] at h1; simp at h1
    · rw [← ha] at h2; simp at h2
    · exact ⟨h1, h2⟩
  rcases Nat.lt_or_ge a 9 with hlt | hge
  · interval_cases a <;> simp_all <;> decide
  · have hbig : ∀ k, k < 9 → a ≠ k := fun k hk h => by
      subst h; exact absurd (lt_of_lt_of_le hk hge) (lt_irrefl _)
    simp [w, winv, hbig 0 (by decide), hbig 1 (by decide), hbig 2 (by decide), hbig 3 (by decide),
      hbig 4 (by decide), hbig 5 (by decide), hbig 6 (by decide), hbig 7 (by decide),
      hbig 8 (by decide)]

theorem w_inj {a b : C} (ha : findC a = a) (hb : findC b = b) (h : w a = w b) : a = b := by
  rw [← winv_w ha, ← winv_w hb, h]

theorem erase4_singleton_inj {a b : C}
    (h : ({a} : Finset C).erase 4 = ({b} : Finset C).erase 4) : a = b := by
  by_cases ha : a = 4
  · by_cases hb : b = 4
    · rw [ha, hb]
    · have : b ∈ ({a} : Finset C).erase 4 := h ▸ Finset.mem_erase.2 ⟨hb, by simp⟩
      exact (Finset.mem_singleton.1 (Finset.mem_erase.1 this).2).symm
  · have : a ∈ ({b} : Finset C).erase 4 := h ▸ Finset.mem_erase.2 ⟨ha, by simp⟩
    exact Finset.mem_singleton.1 (Finset.mem_erase.1 this).2

theorem erase4_step {f : Sym} {s s' : Finset C} (h : ACIStep Sc.graph laws f s s') :
    s.erase 4 = s'.erase 4 := by
  cases h with
  | splice hmem => exact (no_set_A hmem).elim
  | unit hu =>
      simp only [laws, Option.some.injEq] at hu
      subst hu
      rw [show Sc.graph.find 4 = 4 from rfl, Finset.erase_insert_eq_erase]

theorem filter4_singleton_inj {a b : C}
    (h : [a].filter (fun x => decide (x ≠ 4)) = [b].filter (fun x => decide (x ≠ 4))) : a = b := by
  by_cases ha : a = 4 <;> by_cases hb : b = 4
  · rw [ha, hb]
  · simp [ha, hb] at h
  · simp [ha, hb] at h
  · simpa [ha, hb] using h

theorem filter4_step {f : Sym} {l l' : List C} (h : AStep Sc.graph laws f l l') :
    l.filter (fun x => decide (x ≠ 4)) = l'.filter (fun x => decide (x ≠ 4)) := by
  cases h with
  | splice hmem => exact (no_seq_A hmem).elim
  | unit hu =>
      simp only [laws, Option.some.injEq] at hu
      subst hu
      rw [show Sc.graph.find 4 = 4 from rfl]
      simp [List.filter_append]

/-- **The completed store is closed under the theory.** -/
theorem closedC : TheoryClosed Sc laws where
  mset := by
    intro f c c' h
    have := W_eq h
    rw [W_single, W_single] at this
    exact w_inj (wfC.after_idem c) (wfC.after_idem c') this
  set := by
    intro f c c' h
    exact erase4_singleton_inj (eqvGen_invariant (fun s => Finset.erase s 4)
      (fun _ _ hs => erase4_step hs) h)
  seq := by
    intro f c c' h
    exact filter4_singleton_inj (eqvGen_invariant (fun l => l.filter (fun x => decide (x ≠ 4)))
      (fun _ _ hs => filter4_step hs) h)
  node := wfC.dedup
  pair := fun _ _ _ _ _ h _ => (no_pair_A h).elim

/-- **In the completed store the instance is reached.** The round from the
before-store to the completed store meets `StorePersistE`, the completed
store is closed under the theory, and there `f{x}` with `x ↦ d` has the
value `Sc.find e'` (the class of `d`, which `e'` joined) and no other. -/
theorem completed :
    StorePersistE laws Sb Sc ∧ TheoryClosed Sc laws ∧
      DenN Sc.graph laws σ t (Sc.find 7) ∧ ∀ c', DenN Sc.graph laws σ t c' → c' = Sc.find 7 := by
  refine ⟨persistC, closedC, ?_, ?_⟩
  · refine DenN.ac (cks := [(6, 1)]) (m₀ := 0) (m' := {6}) rfl ?_ ?_ ?_ ?_ ?_
    · simp [RMultOk]
    · intro ek hek _
      simp at hek; subst hek
      exact DenN.var (G := Sc.graph) (x := 0) (c := 6) (by simp [σ])
    · simp [MsetRestVal]
    · simp only [acChildren, one_smul, Multiset.map_zero, add_zero]
      exact Relation.ReflTransGen.refl
    · exact Or.inr (Or.inl ⟨6, rfl, by decide⟩)
  · intro c' h
    have hE : DenE Sc.graph laws σ t (Sc.find 7) := (denB.toDenE hcB wf.before_idem).persist persistC
    exact (denE_denN_eq wfC.after_idem wfC.children_canon closedC hE h).symm

end PersistFails

end Semper.EMatch.Fidelity
