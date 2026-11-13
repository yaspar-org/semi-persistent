import SemperProofs.EMatch.Flatten.Views

/-!
# `:flatten` on folds: only the spine may open

`:assoc-left` and `:assoc-right` are folds, not associative operators
(`doc/book/src/04-declaring-algebra.md`): a left fold `f(f(a,b),c)` is
`f(a,b,c)`, but `f(a,f(b,c))` keeps its grouped right child. The engine
passes `FlatKind::Assoc` for a fold atom (`schedule.rs:1246-1305`), and its
walk opened a nested same-operator child at **every** position, so the view
`[a, b, c]` of the node `f[a, K]`, `K ∋ f[b, c]`, matched `(f x y z)` as the
term `f(f(a,b),c)`: an unsound match (reproducer `flatten_fold_spine.egg`).

This file reads a fold in any magma (`lfold`, `rfold` over a type with
`Mul`; `BTm`, the free terms, is one instance) and proves which side is
right:

* `fold_open_off_spine_unsound`: in the opening-tree model of `Views.lean`
  (every position may open), there is a graph whose class denotations into
  the free magma are consistent with the left fold and a raw view of a node
  whose left fold differs from the node's (the reproducer, as a
  counter-model);
* `OTLeft` / `OTRight`: the opening trees that open only the spine (the
  first, resp. last, position of the root and of every opened member), and
  `otLeft_sound` / `otRight_sound`: every such view denotes the node's term
  when the denotation is consistent, in every magma. This is the walk after
  the fix (`flatten::spine`);
* `consistentL_cyclic_satisfiable`: a class holding `Sub[X, c]` (what
  `x - 0 = x` makes) has a consistent denotation into `ℕ`, though none into
  the free magma (`consistentL_cyclic_free_unsat`), so the soundness
  theorems are not vacuous on such graphs.

The `:assoc` development (completeness of the demand rule, the plan theorems)
is about the unrestricted trees; for a fold, the views are the restricted
trees' views, a subset closed under closing a leaf (closing keeps a class
whole, which is always allowed).
-/

namespace Semper.EMatch.Flatten

open Semper.EMatch

/-! ## Folds in a magma

A fold reads in any type with a binary operation (`Mul M`, a magma: no law
is assumed). The soundness theorems below are stated for every such `M` and
every denotation; the free terms `BTm` are one instance, used where a
counter-model needs two different groupings to denote different terms. -/

section Magma

variable {M : Type*} [Mul M]

/-- The left fold of a nonempty list: `[t₁, …, tₙ] ↦ (…(t₁ * t₂) …) * tₙ`. -/
def lfold : List M → Option M
  | [] => none
  | t :: ts => some (ts.foldl (· * ·) t)

/-- The right fold of a nonempty list: `[t₁, …, tₙ] ↦ t₁ * (… (tₙ₋₁ * tₙ))`. -/
def rfold : List M → Option M
  | [] => none
  | [t] => some t
  | t :: ts => (rfold ts).map (t * ·)

/-- Splicing a left fold at the head is the fold of the concatenation. -/
theorem lfold_splice {xs : List M} {t : M} (h : lfold xs = some t) (ys : List M) :
    lfold (t :: ys) = lfold (xs ++ ys) := by
  cases xs with
  | nil => simp [lfold] at h
  | cons x xs =>
      simp only [lfold, Option.some.injEq] at h ⊢
      subst h
      simp [List.foldl_append]

theorem rfold_cons_of_ne {t : M} {ts : List M} (h : ts ≠ []) :
    rfold (t :: ts) = (rfold ts).map (t * ·) := by
  cases ts with
  | nil => exact absurd rfl h
  | cons _ _ => rfl

theorem rfold_ne_none {ts : List M} (h : ts ≠ []) : rfold ts ≠ none := by
  induction ts with
  | nil => exact absurd rfl h
  | cons t ts ih =>
      by_cases hts : ts = []
      · subst hts; simp [rfold]
      · rw [rfold_cons_of_ne hts]
        simpa using ih hts

/-- Splicing a right fold at the tail is the fold of the concatenation. -/
theorem rfold_splice {ys : List M} {t : M} (h : rfold ys = some t) :
    ∀ xs : List M, rfold (xs ++ [t]) = rfold (xs ++ ys)
  | [] => by simpa [rfold] using h.symm
  | x :: xs => by
      have hys : ys ≠ [] := by rintro rfl; simp [rfold] at h
      rw [List.cons_append, List.cons_append, rfold_cons_of_ne (by simp),
        rfold_cons_of_ne (by simp [hys]), rfold_splice h xs]

end Magma

/-- Binary terms over classes: the free magma, the instance in which two
groupings of the same leaves denote different terms. -/
inductive BTm where
  | leaf (c : C)
  | node (l r : BTm)
  deriving DecidableEq, Repr

instance : Mul BTm := ⟨BTm.node⟩

/-! ## Consistent denotations -/

/-- A denotation of the classes into a magma `M`, consistent with the left
fold `f`: every `f`-member of `X` (a sequence node) denotes `den X` as the
left fold of its children's denotations. -/
def ConsistentL {M : Type*} [Mul M] (ctx : Ctx) (den : C → M) : Prop :=
  ∀ id m X cs, ctx.IsMember id m X → m.children = .seq cs → lfold (cs.map den) = some (den X)

/-- The same for the right fold. -/
def ConsistentR {M : Type*} [Mul M] (ctx : Ctx) (den : C → M) : Prop :=
  ∀ id m X cs, ctx.IsMember id m X → m.children = .seq cs → rfold (cs.map den) = some (den X)

/-! ## Cyclic classes have consistent denotations

`x - 0 = x` merges `Sub[X, c]` into `X`, so the class `X` holds a fold over
itself; a class can also hold two spellings `Sub[a, b]` and `Sub[a, b, c]`.
No denotation into the free magma is consistent with such a class
(`consistentL_cyclic_free_unsat`), but one into `ℕ` with multiplication is
(`consistentL_cyclic_satisfiable`), so the soundness theorems, stated for
every magma, say something about these graphs. -/

/-- `Sub` (op 7) a left fold, classes `a = 1, b = 2, c = 3, X = 4`, and the
members `X ∋ Sub[X, c]` (node 10), `X ∋ Sub[a, b]` (node 11) and
`X ∋ Sub[a, b, c]` (node 12). -/
def exCyc : Ctx :=
  ⟨⟨[(10, ⟨7, .seq [4, 3]⟩), (11, ⟨7, .seq [1, 2]⟩), (12, ⟨7, .seq [1, 2, 3]⟩)],
    fun id => if id = 10 ∨ id = 11 ∨ id = 12 then 4 else id⟩, 7, .assoc, fun _ => true⟩

/-- `c ↦ 1`, `a ↦ 2`, `b ↦ 3`, `X ↦ 6`. -/
def exCycDen : C → ℕ := fun c => if c = 3 then 1 else if c = 1 then 2 else if c = 2 then 3 else 6

theorem exCyc_consistent : ConsistentL exCyc exCycDen := by
  intro id m X cs hm hcs
  obtain ⟨hmem, -, hX, -⟩ := hm
  simp only [exCyc, List.mem_cons, Prod.mk.injEq, List.not_mem_nil,
    or_false] at hmem
  rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp only [exCyc] at hX <;> subst hX <;> simp only [Children.seq.injEq] at hcs <;>
    subst hcs <;> decide

/-- **A class holding a fold over itself has a consistent denotation.** In
`exCyc` the class `X` holds `Sub[X, c]`, `Sub[a, b]` and `Sub[a, b, c]`, and
`exCycDen` into `ℕ` (multiplication, `c ↦ 1`) is consistent with the left
fold. -/
theorem consistentL_cyclic_satisfiable :
    ∃ (ctx : Ctx) (X c : C) (den : C → ℕ), ctx.κ = .assoc ∧
      (∃ id m, ctx.IsMember id m X ∧ m.children = .seq [X, c]) ∧
      (∃ a b id₁ m₁ id₂ m₂, ctx.IsMember id₁ m₁ X ∧ m₁.children = .seq [a, b] ∧
        ctx.IsMember id₂ m₂ X ∧ m₂.children = .seq [a, b, c]) ∧
      ConsistentL ctx den :=
  ⟨exCyc, 4, 3, exCycDen, rfl,
    ⟨10, ⟨7, .seq [4, 3]⟩, ⟨by simp [exCyc], rfl, by simp [exCyc], rfl⟩, rfl⟩,
    ⟨1, 2, 11, ⟨7, .seq [1, 2]⟩, 12, ⟨7, .seq [1, 2, 3]⟩,
      ⟨by simp [exCyc], rfl, by simp [exCyc], rfl⟩, rfl,
      ⟨by simp [exCyc], rfl, by simp [exCyc], rfl⟩, rfl⟩,
    exCyc_consistent⟩

theorem BTm.node_ne_left : ∀ (t r : BTm), BTm.node t r ≠ t
  | .leaf _, _, h => BTm.noConfusion h
  | .node l r', _, h => by
      injection h with h₁ _
      exact BTm.node_ne_left l r' h₁

/-- In the free magma no denotation is consistent with `exCyc`: the member
`Sub[X, c]` would make `den X` a proper subterm of itself. -/
theorem consistentL_cyclic_free_unsat (den : C → BTm) : ¬ ConsistentL exCyc den := by
  intro hc
  have h := hc 10 ⟨7, .seq [4, 3]⟩ 4 [4, 3] ⟨by simp [exCyc], rfl, by simp [exCyc], rfl⟩ rfl
  simp only [List.map, lfold, List.foldl, Option.some.injEq] at h
  exact BTm.node_ne_left _ _ h

/-! ## The unrestricted trees are unsound for a fold -/

/-- The reproducer as a context: `Sub` (op 7) a left fold, classes
`a = 1, b = 2, c = 3, K = 4`, the member `K ∋ Sub[b, c]` (node 10), and the
root `Sub[a, K]`. -/
def exFold : Ctx :=
  ⟨⟨[(10, ⟨7, .seq [2, 3]⟩)], fun id => if id = 10 then 4 else id⟩, 7, .assoc, fun _ => true⟩

def exFoldRoot : Node := ⟨7, .seq [1, 4]⟩

/-- The denotation: `a, b, c` leaves, `K` the left fold of `[b, c]`. -/
def exFoldDen : C → BTm := fun c => if c = 4 then .node (.leaf 2) (.leaf 3) else .leaf c

theorem exFold_consistent : ConsistentL exFold exFoldDen := by
  intro id m X cs hm hcs
  obtain ⟨hmem, -, hX, -⟩ := hm
  simp only [exFold, List.mem_singleton, Prod.mk.injEq] at hmem
  obtain ⟨rfl, rfl⟩ := hmem
  simp only [exFold] at hX
  subst hX
  simp only [Children.seq.injEq] at hcs
  subst hcs
  decide

/-- The view `[a, b, c]` of `Sub[a, K]`: open `K` at the second position. -/
theorem exFold_view : RawView exFold exFoldRoot [(1, 1), (2, 1), (3, 1)] [[2, 3]] := by
  unfold RawView ViewNode
  have hmem : exFold.IsMember 10 ⟨7, .seq [2, 3]⟩ 4 := by
    refine ⟨by simp [exFold], rfl, by simp [exFold], rfl⟩
  have hin : OT exFold 1 (insert 4 ∅) (kids .assoc (.seq [2, 3])) [(2, 1), (3, 1)] [] :=
    OT.keep (OT.keep OT.nil)
  have h := OT.keep (X := 1) (j := 1) (k := 1) (P := ∅)
    (OT.opn (k := 1) (j := 1) (rest := []) (by simp) hmem hin (OT.nil (k := 1) (P := ∅)))
  simpa [kids, exFoldRoot, exFold, leafify] using h

/-- **Opening a fold off its spine is unsound**: with a denotation consistent
with the left fold, the view of `Sub[a, K]` that opens `K` (the second
child) denotes `Sub(Sub(a, b), c)`, not the node's `Sub(a, Sub(b, c))`. -/
theorem fold_open_off_spine_unsound :
    ∃ (ctx : Ctx) (n : Node) (v : List (C × Nat)) (ls : List (List C)) (den : C → BTm),
      ConsistentL ctx den ∧ RawView ctx n v ls ∧
        lfold ((v.map Prod.fst).map den) ≠ lfold ((kids .assoc n.children).map (fun e => den e.1)) :=
  ⟨exFold, exFoldRoot, _, _, exFoldDen, exFold_consistent, exFold_view, by decide⟩

/-! ## The spine trees are sound -/

/-- Opening trees of a left fold: only the head of every child list may
open (`flatten::spine` with `AssocDir::Left`). Multiplicities are 1 for
sequences, so the trees are over class lists. -/
inductive OTLeft (ctx : Ctx) : Finset C → List C → List C → Prop
  | nil {P : Finset C} : OTLeft ctx P [] []
  | keep {P : Finset C} {xs : List C} : OTLeft ctx P xs xs
  | opn {P : Finset C} {X : C} {rest : List C} {id : NodeId} {m : Node} {cs v : List C} :
      X ∉ P → ctx.IsMember id m X → m.children = .seq cs →
      OTLeft ctx (insert X P) cs v → OTLeft ctx P (X :: rest) (v ++ rest)

/-- Opening trees of a right fold: only the last child may open. -/
inductive OTRight (ctx : Ctx) : Finset C → List C → List C → Prop
  | keep {P : Finset C} {xs : List C} : OTRight ctx P xs xs
  | opn {P : Finset C} {X : C} {rest : List C} {id : NodeId} {m : Node} {cs v : List C} :
      X ∉ P → ctx.IsMember id m X → m.children = .seq cs →
      OTRight ctx (insert X P) cs v → OTRight ctx P (rest ++ [X]) (rest ++ v)

/-- **The spine views of a left fold denote the node's term.** -/
theorem otLeft_sound {M : Type*} [Mul M] {ctx : Ctx} {den : C → M} (hc : ConsistentL ctx den) :
    ∀ {P : Finset C} {ks v : List C}, OTLeft ctx P ks v →
      lfold (v.map den) = lfold (ks.map den) := by
  intro P ks v h
  induction h with
  | nil => rfl
  | keep => rfl
  | @opn P X rest id m cs v hX hm hcs _ ih =>
      have hden : lfold (v.map den) = some (den X) := by rw [ih]; exact hc id m X cs hm hcs
      rw [List.map_append, ← lfold_splice hden]
      rfl

/-- **The spine views of a right fold denote the node's term.** -/
theorem otRight_sound {M : Type*} [Mul M] {ctx : Ctx} {den : C → M} (hc : ConsistentR ctx den) :
    ∀ {P : Finset C} {ks v : List C}, OTRight ctx P ks v →
      rfold (v.map den) = rfold (ks.map den) := by
  intro P ks v h
  induction h with
  | keep => rfl
  | @opn P X rest id m cs v hX hm hcs _ ih =>
      have hden : rfold (v.map den) = some (den X) := by rw [ih]; exact hc id m X cs hm hcs
      rw [List.map_append, List.map_append, ← rfold_splice hden]
      simp

end Semper.EMatch.Flatten
