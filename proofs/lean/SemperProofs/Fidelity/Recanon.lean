import SemperProofs.Fidelity.Normalize

/-!
# Recanonicalization as the laws apply it (fidelity row: `StorePersist` literal)

`StorePersist` (`Fidelity/Subsume.lean`) asks every stored node to survive a
round with its children mapped through the new `find`. `recanonize_node`
(`caches.rs`, `canon.rs`) does that for a tuple, pair or sequence node; for a
multiset node it also drops the unit's class and clamps the counts modulo
the nilpotent order (`MSetCanon`), for a set node it drops the unit's class
and deduplicates (`SetCanon`), and a result of one element or none is a
leaf: `rebuild` merges the node's class with that element's class or with
the unit's (`degeneracy_pair`). Inverse-pair cancellation is not part of
recanonicalization: the repair pass (`inverse_cancel_repair`) builds the
cancelled node with `add` and merges, which the round records as a merge.

`StorePersistN` states this: the fixed-arity nodes persist literally
(`LiteralFixed`), and an AC or ACI node either survives with the normal form
of its mapped children (`RStep`, `RSetStep`: the recanonicalization steps,
a sub-relation of `ACStep`/`ACIStep`) or collapses to a leaf (`Final`).

What follows from it:

* `DenN.persist_fixed`: a right-hand side without n-ary application built
  before the round is built after it (through `LiteralFixed`).
* `denN_persist_fails`: `DenN.persist` does not extend to n-ary right-hand
  sides. Two stores satisfying `StorePersistN` are exhibited in which a
  right-hand side `f{x}` with `x` bound to a class `d` has the value `e'`
  before the round and only the value `d` after it: a unit merge of a
  nested class changed the value of a chain through two splices without
  touching the node that holds the match. The saturation theorems therefore
  do not transport such an instance; they route the rules that build an
  n-ary term naive after a round whose rebuild was not literal
  (`route`, `SChainN`), which is the engine's `respelled` re-match.
* `StorePersist.toN`, `StorePersistN.toStorePersist`: literal persistence is
  the case where the normal form is the mapped children.
-/

namespace Semper.EMatch.Fidelity

open Semper.EMatch

/-- One recanonicalization step on an AC child multiset (`MSetCanon`): drop
one copy of the unit's class, or `r` copies of a class under `:nilpotent r`.
No splice and no cancellation: `ACStep` without those two constructors. -/
inductive RStep (G : Graph) (L : Sym → OpLaws) (f : Sym) : Multiset C → Multiset C → Prop
  | unit {u : NodeId} {rest : Multiset C} :
      (L f).unit = some u → RStep G L f ({G.find u} + rest) rest
  | nil {r : Nat} {x : C} {rest : Multiset C} :
      (L f).nilpotent = some r → RStep G L f (r • {x} + rest) rest

/-- One recanonicalization step on an ACI child set (`SetCanon`): drop the
unit's class (deduplication is the set itself). -/
inductive RSetStep (G : Graph) (L : Sym → OpLaws) (f : Sym) : Finset C → Finset C → Prop
  | unit {u : NodeId} {rest : Finset C} :
      (L f).unit = some u → RSetStep G L f (insert (G.find u) rest) rest

theorem RStep.toAC {G : Graph} {L : Sym → OpLaws} {f : Sym} {m m' : Multiset C}
    (h : RStep G L f m m') : ACStep G L f m m' := by
  cases h with
  | unit hu => exact ACStep.unit hu
  | nil hr => exact ACStep.nil hr

theorem RSetStep.toACI {G : Graph} {L : Sym → OpLaws} {f : Sym} {s s' : Finset C}
    (h : RSetStep G L f s s') : ACIStep G L f s s' := by
  cases h with
  | unit hu => exact ACIStep.unit hu

/-- The class a recanonicalized AC node ends in: its normal form is stored
(under the node's own id, or one it collided with), or is one element and
the node's class is that element's, or is empty and the node's class is the
unit's. -/
def NFMset (Sa : Store) (L : Sym → OpLaws) (f : Sym) (m : Multiset C) (c : C) : Prop :=
  ∃ m', Relation.ReflTransGen (RStep Sa.graph L f) m m' ∧
    Final Sa.graph L f (.mset m') (fun x => m' = {x}) (m' = 0) c

/-- The same for an ACI node. -/
def NFSet (Sa : Store) (L : Sym → OpLaws) (f : Sym) (s : Finset C) (c : C) : Prop :=
  ∃ s', Relation.ReflTransGen (RSetStep Sa.graph L f) s s' ∧
    Final Sa.graph L f (.set s') (fun x => s' = {x}) (s' = ∅) c

/-- What the round guarantees of the store, with recanonicalization as the
laws apply it: the round facts (`StoreWF`), the fixed-arity and sequence
nodes persist literally, and every AC or ACI node persists as the normal
form of its mapped children or collapses to a leaf. -/
structure StorePersistN (L : Sym → OpLaws) (Sb Sa : Store) : Prop extends StoreWF Sb Sa where
  fixed : LiteralFixed Sb Sa
  mset : ∀ id f m, (id, ⟨f, .mset m⟩) ∈ Sb.nodes → NFMset Sa L f (m.map Sa.find) (Sa.find id)
  set : ∀ id f s, (id, ⟨f, .set s⟩) ∈ Sb.nodes → NFSet Sa L f (s.image Sa.find) (Sa.find id)

/-- Literal persistence is the case with no recanonicalization step. -/
theorem StorePersist.toN {Sb Sa : Store} (h : StorePersist Sb Sa) (L : Sym → OpLaws) :
    StorePersistN L Sb Sa where
  toStoreWF := h.toStoreWF
  fixed := h.persist.toFixed
  mset := by
    intro id f m hmem
    obtain ⟨⟨op, ch⟩, hmem', hop, hch⟩ := h.persist _ _ hmem
    cases ch <;> simp [CanonCh] at hch
    simp only at hop
    subst hop hch
    exact ⟨_, Relation.ReflTransGen.refl, Or.inl ⟨id, hmem', rfl⟩⟩
  set := by
    intro id f s hmem
    obtain ⟨⟨op, ch⟩, hmem', hop, hch⟩ := h.persist _ _ hmem
    cases ch <;> simp [CanonCh] at hch
    simp only at hop
    subst hop hch
    exact ⟨_, Relation.ReflTransGen.refl, Or.inl ⟨id, hmem', rfl⟩⟩

theorem StorePersistN.toStorePersist {L : Sym → OpLaws} {Sb Sa : Store} (h : StorePersistN L Sb Sa)
    (hl : Literal Sb Sa) : StorePersist Sb Sa :=
  ⟨h.toStoreWF, hl⟩

theorem StorePersistN.toFixed {L : Sym → OpLaws} {Sb Sa : Store} (h : StorePersistN L Sb Sa) :
    StorePersistFixed Sb Sa :=
  ⟨h.toStoreWF, h.fixed⟩

/-! ## Right-hand sides without n-ary application persist -/

section Fixed

variable {L : Sym → OpLaws} {Sb Sa : Store} (h : StorePersistN L Sb Sa)
include h

theorem StorePersistN.find_before (c : C) : Sa.find (Sb.find c) = Sa.find c :=
  h.no_split _ _ (h.before_idem c)

/-- `DenN.persist` for a term without n-ary application: only the
fixed-arity nodes need to persist. -/
theorem DenN.persist_fixed {σ : Binding} {t : Pat} (ht : t.hasNary = false) {c : C}
    (hd : DenN Sb.graph L σ t c) : DenN Sa.graph L σ t (Sa.find c) := by
  have hfb := h.find_before
  induction hd with
  | var hx =>
      simp only [Store.graph_find, hfb]
      exact DenN.var hx
  | plain hl hall hmem ih =>
      rename_i f args cs id
      have hargs : ∀ p ∈ args, p.hasNary = false :=
        Pat.hasNaryList_eq_false.1 (by simpa [Pat.hasNary] using ht)
      obtain ⟨⟨op, ch⟩, hmem', hop, hch⟩ := h.fixed _ _ hmem rfl
      cases ch <;> simp [CanonCh] at hch
      simp only at hop
      subst hop hch
      simp only [Store.graph_find, hfb]
      refine DenN.plain (by simp [hl]) ?_ hmem'
      intro pc hpc
      rw [List.zip_map_right, List.mem_map] at hpc
      obtain ⟨pc', hpc', rfl⟩ := hpc
      exact ih pc' hpc' (hargs _ (List.of_mem_zip hpc').1)
  | comm ha hb hmem iha ihb =>
      rename_i f p q a b id
      have hpq : p.hasNary = false ∧ q.hasNary = false := by simpa [Pat.hasNary] using ht
      simp only [Store.graph_find, hfb]
      rcases hmem with hmem | hmem
      · obtain ⟨⟨op, ch⟩, hmem', hop, hch⟩ := h.fixed _ _ hmem rfl
        cases ch <;> simp [CanonCh] at hch
        simp only at hop
        subst hop
        rcases hch with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact DenN.comm (iha hpq.1) (ihb hpq.2) (Or.inl hmem')
        · exact DenN.comm (iha hpq.1) (ihb hpq.2) (Or.inr hmem')
      · obtain ⟨⟨op, ch⟩, hmem', hop, hch⟩ := h.fixed _ _ hmem rfl
        cases ch <;> simp [CanonCh] at hch
        simp only at hop
        subst hop
        rcases hch with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact DenN.comm (iha hpq.1) (ihb hpq.2) (Or.inr hmem')
        · exact DenN.comm (iha hpq.1) (ihb hpq.2) (Or.inl hmem')
  | assoc => simp [Pat.hasNary] at ht
  | ac => simp [Pat.hasNary] at ht
  | aci => simp [Pat.hasNary] at ht

end Fixed

/-! ## `DenN.persist` fails for n-ary right-hand sides

The stores below are a round in which the class `y = 5` of the leaf `Y`,
which also holds the node `f{p, q}` (`j = 8`), merges into the unit's class
`u = 4`. The node `d = 6` is `f{y, c, w}` before the round and `f{c, w}`
after it (the unit dropped); the node `e' = 7` is `f{p, q, c, w}` and does
not change. The right-hand side `f{x}` with `x ↦ d` is built before the
round by splicing `d` then `y`: its value is `e'`. After the round the only
chains from `{d}` splice `d` into `{c, w}`, whose value is `d`, and
`d ≠ e'`. -/

namespace PersistFails

/-- The leaf operators `10 + i` for the leaf `i`, the AC operator `20`. -/
def leaf (i : NodeId) : NodeId × Node := (i, ⟨10 + i, .tuple []⟩)

def fop : Sym := 20

def laws : Sym → OpLaws := fun _ => ⟨some 4, none, none⟩

def nodesB : List (NodeId × Node) :=
  [leaf 0, leaf 1, leaf 2, leaf 3, leaf 4, leaf 5,
    (6, ⟨fop, .mset {5, 2, 3}⟩), (7, ⟨fop, .mset {0, 1, 2, 3}⟩), (8, ⟨fop, .mset {0, 1}⟩)]

def nodesA : List (NodeId × Node) :=
  [leaf 0, leaf 1, leaf 2, leaf 3, leaf 4, leaf 5,
    (6, ⟨fop, .mset {2, 3}⟩), (7, ⟨fop, .mset {0, 1, 2, 3}⟩), (8, ⟨fop, .mset {0, 1}⟩)]

/-- Before: `j = 8` is in the class of `y = 5`. -/
def findB : NodeId → C := fun id => if id = 8 then 5 else id

/-- After: `y` and `j` are in the unit's class `4`. -/
def findA : NodeId → C := fun id => if id = 8 ∨ id = 5 then 4 else id

def flags : SkipFlags := ⟨fun _ => false, false, fun _ => false, fun _ => true⟩

def Sb : Store := ⟨nodesB, findB, flags⟩
def Sa : Store := ⟨nodesA, findA, flags⟩

/-- `x ↦ d`. -/
def σ : Binding := { Binding.empty with cls := fun x => if x = 0 then some 6 else none }

def t : Pat := .ac fop [(.var 0, .exact 1)] none

theorem mem_A {p : NodeId × Node} : p ∈ nodesA ↔
    p = leaf 0 ∨ p = leaf 1 ∨ p = leaf 2 ∨ p = leaf 3 ∨ p = leaf 4 ∨ p = leaf 5 ∨
    p = (6, ⟨fop, .mset {2, 3}⟩) ∨ p = (7, ⟨fop, .mset {0, 1, 2, 3}⟩) ∨
    p = (8, ⟨fop, .mset {0, 1}⟩) := by
  simp [nodesA]

theorem mem_B {p : NodeId × Node} : p ∈ nodesB ↔
    p = leaf 0 ∨ p = leaf 1 ∨ p = leaf 2 ∨ p = leaf 3 ∨ p = leaf 4 ∨ p = leaf 5 ∨
    p = (6, ⟨fop, .mset {5, 2, 3}⟩) ∨ p = (7, ⟨fop, .mset {0, 1, 2, 3}⟩) ∨
    p = (8, ⟨fop, .mset {0, 1}⟩) := by
  simp [nodesB]

/-- The AC nodes of `Sa`. -/
theorem mem_mset_A {id : NodeId} {f : Sym} {m : Multiset C}
    (h : (id, ⟨f, .mset m⟩) ∈ nodesA) :
    (id = 6 ∧ f = fop ∧ m = {2, 3}) ∨ (id = 7 ∧ f = fop ∧ m = {0, 1, 2, 3}) ∨
    (id = 8 ∧ f = fop ∧ m = {0, 1}) := by
  simpa [nodesA, leaf] using h

theorem mem_mset_B {id : NodeId} {f : Sym} {m : Multiset C}
    (h : (id, ⟨f, .mset m⟩) ∈ nodesB) :
    (id = 6 ∧ f = fop ∧ m = {5, 2, 3}) ∨ (id = 7 ∧ f = fop ∧ m = {0, 1, 2, 3}) ∨
    (id = 8 ∧ f = fop ∧ m = {0, 1}) := by
  simpa [nodesB, leaf] using h

theorem no_set_B {id : NodeId} {f : Sym} {s : Finset C} (h : (id, ⟨f, .set s⟩) ∈ nodesB) :
    False := by
  simp [nodesB, leaf] at h

theorem wf : StoreWF Sb Sa where
  before_idem := by
    intro id; simp only [Sb, Store.graph_find, findB]
    split <;> simp_all
  after_idem := by
    intro id; simp only [Sa, Store.graph_find, findA]
    split <;> simp_all
  no_split := by
    intro id id' h
    simp only [Sb, findB] at h
    simp only [Sa, findA]
    split at h <;> split at h <;> simp_all
  children_canon := by
    intro p hp
    rcases mem_A.1 hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [Sa, leaf, Children.Canon, findA]
  dedup := by
    intro id₁ id₂ n h₁ h₂
    have hnd : (nodesA.map Prod.snd).Nodup := by decide
    have := List.inj_on_of_nodup_map hnd h₁ h₂ rfl
    simp only [Prod.mk.injEq] at this
    rw [this.1]

theorem persistN : StorePersistN laws Sb Sa where
  toStoreWF := wf
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
    · -- d = f{5, 2, 3}: the unit dropped, the node survives as f{2, 3}
      refine ⟨{2, 3}, ?_, Or.inl ⟨6, mem_A.2 (by simp), rfl⟩⟩
      have hm : ({5, 2, 3} : Multiset C).map findA = {findA 4} + {2, 3} := by decide
      show Relation.ReflTransGen (RStep Sa.graph laws fop) (Multiset.map findA {5, 2, 3}) {2, 3}
      rw [hm]
      exact Relation.ReflTransGen.single (RStep.unit (G := Sa.graph) (L := laws) (f := fop) rfl)
    · refine ⟨_, Relation.ReflTransGen.refl, Or.inl ⟨7, ?_, rfl⟩⟩
      show (7, ⟨fop, .mset (({0, 1, 2, 3} : Multiset C).map findA)⟩) ∈ nodesA
      rw [show ({0, 1, 2, 3} : Multiset C).map findA = {0, 1, 2, 3} by decide]
      exact mem_A.2 (by simp)
    · refine ⟨_, Relation.ReflTransGen.refl, Or.inl ⟨8, ?_, rfl⟩⟩
      show (8, ⟨fop, .mset (({0, 1} : Multiset C).map findA)⟩) ∈ nodesA
      rw [show ({0, 1} : Multiset C).map findA = {0, 1} by decide]
      exact mem_A.2 (by simp)
  set := fun _ _ _ hmem => (no_set_B hmem).elim

/-- Before the round: `f{x}` with `x ↦ d` has the value `e' = 7`. -/
theorem denB : DenN Sb.graph laws σ t 7 := by
  have h1 : Relation.ReflTransGen (ACStep Sb.graph laws fop) ({6} : Multiset C) {0, 1, 2, 3} := by
    refine Relation.ReflTransGen.head (b := {5, 2, 3}) ?_ (Relation.ReflTransGen.single ?_)
    · have := ACStep.splice (G := Sb.graph) (L := laws) (f := fop) (rest := 0)
        (id := 6) (m₁ := {5, 2, 3}) (mem_B.2 (by simp))
      simpa [show Sb.graph.find 6 = 6 from rfl] using this
    · have := ACStep.splice (G := Sb.graph) (L := laws) (f := fop) (rest := {2, 3})
        (id := 8) (m₁ := {0, 1}) (mem_B.2 (by simp))
      have e1 : ({Sb.graph.find 8} : Multiset C) + {2, 3} = {5, 2, 3} := by decide
      have e2 : ({0, 1} : Multiset C) + {2, 3} = {0, 1, 2, 3} := by decide
      rwa [e1, e2] at this
  refine DenN.ac (cks := [(6, 1)]) (m₀ := 0) (m' := {0, 1, 2, 3}) rfl ?_ ?_ ?_ ?_ ?_
  · simp [RMultOk]
  · intro ek hek _
    simp at hek; subst hek
    exact DenN.var (G := Sb.graph) (x := 0) (c := 6) (by simp [σ])
  · simp [MsetRestVal]
  · simpa [acChildren] using h1
  · exact Or.inl ⟨7, mem_B.2 (by simp), rfl⟩

theorem not_mem_reach {c : C} (hc : c ≠ 6 ∧ c ≠ 2 ∧ c ≠ 3) {rest : Multiset C}
    (ih : {c} + rest = {6} ∨ {c} + rest = {2, 3}) : False := by
  rcases ih with h | h
  · have : c ∈ ({6} : Multiset C) := h ▸ by simp
    simp at this; exact hc.1 this
  · have : c ∈ ({2, 3} : Multiset C) := h ▸ by simp
    simp at this
    rcases this with rfl | rfl
    · exact hc.2.1 rfl
    · exact hc.2.2 rfl

/-- After the round the chains from `{d}` reach `{d}` and `{c, w}` only. -/
theorem reachA {m : Multiset C} (h : Relation.ReflTransGen (ACStep Sa.graph laws fop) {6} m) :
    m = {6} ∨ m = {2, 3} := by
  induction h with
  | refl => exact Or.inl rfl
  | tail _ hs ih =>
      cases hs with
      | @splice m' rest id hmem =>
          rcases mem_mset_A hmem with ⟨rfl, -, rfl⟩ | ⟨rfl, -, rfl⟩ | ⟨rfl, -, rfl⟩
          · -- id = 6, class 6: only from {6}
            have h6 : Sa.graph.find 6 = 6 := rfl
            rw [h6] at ih
            rcases ih with h | h
            · have : rest = 0 := by
                have := congrArg Multiset.card h
                simpa using this
              subst this
              right; simp
            · exfalso
              have : (6 : C) ∈ ({2, 3} : Multiset C) := h ▸ by simp
              simp at this
          · exact (not_mem_reach (c := Sa.graph.find 7) (by decide) ih).elim
          · exact (not_mem_reach (c := Sa.graph.find 8) (by decide) ih).elim
      | unit hu =>
          simp only [laws, Option.some.injEq] at hu
          subst hu
          exact (not_mem_reach (c := Sa.graph.find 4) (by decide) ih).elim
      | nil hr => simp [laws] at hr
      | inv hg => simp [laws] at hg

/-- After the round, `f{x}` with `x ↦ d` has no value but `d = 6`. -/
theorem denA_only {c : C} (hd : DenN Sa.graph laws σ t c) : c = 6 := by
  cases hd with
  | ac hl hmult hden hrest hsteps hfin =>
      rename_i cks m₀ m'
      obtain ⟨⟨c₀, k⟩, rfl⟩ : ∃ ck, cks = [ck] := by
        cases cks with
        | nil => simp at hl
        | cons ck cks => cases cks with
          | nil => exact ⟨ck, rfl⟩
          | cons _ _ => simp at hl
      have hk : k = 1 := by
        have := hmult ((.var 0, .exact 1), (c₀, k)) (by simp)
        simpa [RMultOk] using this
      subst hk
      have hc₀ : c₀ = 6 := by
        have := hden ((.var 0, .exact 1), (c₀, 1)) (by simp) (by simp)
        cases this with
        | var hx =>
            simp only [σ, ite_true, Option.some.injEq] at hx
            subst hx; rfl
      subst hc₀
      have hm₀ : m₀ = 0 := by simpa [MsetRestVal] using hrest
      subst hm₀
      simp only [acChildren, one_smul, Multiset.map_zero, add_zero] at hsteps
      rcases reachA hsteps with rfl | rfl
      · rcases hfin with ⟨id, hmem, rfl⟩ | ⟨x, hx, rfl⟩ | ⟨h0, -⟩
        · exfalso
          rcases mem_mset_A hmem with ⟨-, -, h⟩ | ⟨-, -, h⟩ | ⟨-, -, h⟩ <;>
            exact absurd h (by decide)
        · have : x = 6 := by simpa using hx.symm
          subst this; rfl
        · exact absurd h0 (by decide)
      · rcases hfin with ⟨id, hmem, rfl⟩ | ⟨x, hx, -⟩ | ⟨h0, -⟩
        · rcases mem_mset_A hmem with ⟨rfl, -, -⟩ | ⟨-, -, h⟩ | ⟨-, -, h⟩
          · rfl
          · exact absurd h (by decide)
          · exact absurd h (by decide)
        · exact absurd (congrArg Multiset.card hx) (by simp)
        · exact absurd h0 (by decide)

end PersistFails

/-- **`DenN.persist` does not extend to normal-form recanonicalization.**
There are a round `Sb → Sa` satisfying `StorePersistN`, a binding and a
right-hand side `f{x}` built before the round with value `c` such that no
chain after the round has the value `Sa.find c`. -/
theorem denN_persist_fails :
    ∃ (L : Sym → OpLaws) (Sb Sa : Store) (σ : Binding) (t : Pat) (c : C),
      StorePersistN L Sb Sa ∧ DenN Sb.graph L σ t c ∧ ¬ DenN Sa.graph L σ t (Sa.find c) := by
  refine ⟨PersistFails.laws, PersistFails.Sb, PersistFails.Sa, PersistFails.σ, PersistFails.t, 7,
    PersistFails.persistN, PersistFails.denB, fun h => ?_⟩
  have := PersistFails.denA_only h
  exact absurd this (by decide)

end Semper.EMatch.Fidelity
