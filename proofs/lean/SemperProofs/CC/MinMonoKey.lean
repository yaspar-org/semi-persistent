import SemperProofs.CC.Slot

/-!
# Completion order keys: recanonization never grows a node (fidelity row EG1)

`Slot.lean` keeps I5 (each class's stored minimal monomial is the degree-lex
least of its active monomials) under mint, merge, shrink and retirement. It has no
operation for a node that *grows* in place, and the engine used to have one:
completion compared monomials by class representative id, and a merge whose
surviving representative is the larger id renames a child upward, so the
node grows in `degLex` (`grow_wa.egg`: `Add{a, b}` with `a` merged into the
later `w` becomes `Add{b, w}`, above its classmate `Add{c, e}`). The class's
stored minimal monomial was that node, so it named the grown monomial and I5
failed:
`idOrder_grow_breaks_I5`.

The engine now orders monomials by per-class *order keys* (`egraph.rs`,
`order_key`, `monomial_cmp_key`): a fresh class's key is its id, and a merged
class takes the lesser of the two keys (`key_merge`), whatever representative
the union-find keeps. Here a key function `k : Fin n → Fin n` maps classes to
keys and `keyDegLex k` compares the keyed monomials `M.map k`.

* `rename_key_le`: a merge of `b` into `a` renames `b` to `a` in every node and
  lowers the merged class's key; the keyed monomial of every node, renamed or
  not (`survivor_key_le`), stays or shrinks.
* `recanon_op`: so each node's change at a merge is a no-op or an `Op.shrink`
  of the existing `SlotState.Op`, and `reachable_I5` covers the engine with no
  new operation (`keyed_reachable_I5`). The engine refreshes both kinds of
  shrink: the renamed parents through the recanonization sweep, the parents of
  a survivor whose key went down through `refresh_key_lowered`.
* The key order has what the completion proofs use of `degLex`: it is
  well-founded (`keyDegLex_wf`), compatible with adding a common monomial
  (`keyDegLex_add_right`), and total on monomials over classes with distinct
  keys (`keyDegLex_total`); keys stay distinct across a merge
  (`key_merge_injOn`).
-/

namespace SemperProofs.CC

open Relation

variable {n : ℕ}

/-! ## `degLex` facts used below -/

theorem degLex_add_right {A B : Monomial n} (h : degLex A B) (C : Monomial n) :
    degLex (A + C) (B + C) := by
  have := degLex_compat (Multiset.le_add_right A C) h
  rwa [add_tsub_cancel_left, add_comm C B] at this

theorem degLex_singleton {x y : Fin n} (h : y < x) : degLex ({x} : Monomial n) {y} := by
  refine Or.inr ⟨by simp, x, fun d hd => ?_, ?_⟩
  · have h1 : d ≠ x := ne_of_gt hd
    have h2 : d ≠ y := ne_of_gt (lt_trans h hd)
    simp [h1, h2]
  · have : x ≠ y := ne_of_gt h
    simp [this]

theorem degLex_cons_right {A B : Monomial n} (h : degLex A B) (a : Fin n) :
    degLex (a ::ₘ A) (a ::ₘ B) := by
  rw [← Multiset.singleton_add, ← Multiset.singleton_add, add_comm {a} A, add_comm {a} B]
  exact degLex_add_right h _

theorem degLex_cons_left {a b : Fin n} (h : b < a) (A : Monomial n) :
    degLex (a ::ₘ A) (b ::ₘ A) := by
  rw [← Multiset.singleton_add, ← Multiset.singleton_add]
  exact degLex_add_right (degLex_singleton h) A

/-- Replacing every element by one no larger never increases a monomial. -/
theorem map_le_of_pointwise {α : Type*} (M : Multiset α) (k g : α → Fin n)
    (h : ∀ x ∈ M, g x ≤ k x) : M.map g = M.map k ∨ degLex (M.map k) (M.map g) := by
  induction M using Multiset.induction_on with
  | empty => exact Or.inl rfl
  | cons x M ih =>
      have ih := ih (fun y hy => h y (Multiset.mem_cons_of_mem hy))
      have hx := h x (Multiset.mem_cons_self x M)
      simp only [Multiset.map_cons]
      rcases hx.lt_or_eq with hlt | heq
      · right
        rcases ih with ih | ih
        · rw [ih]; exact degLex_cons_left hlt _
        · exact degLex_trans (degLex_cons_left hlt _) (degLex_cons_right ih _)
      · rw [heq]
        rcases ih with ih | ih
        · left; rw [ih]
        · right; exact degLex_cons_right ih _

/-! ## The key order -/

/-- Degree-lex over keys: compare the keyed monomials. -/
def keyDegLex (k : Fin n → Fin n) (M N : Monomial n) : Prop :=
  degLex (M.map k) (N.map k)

theorem keyDegLex_wf (k : Fin n → Fin n) :
    WellFounded (fun N M : Monomial n => keyDegLex k M N) :=
  InvImage.wf (fun M : Monomial n => M.map k) degLex_wf

theorem keyDegLex_add_right {k : Fin n → Fin n} {A B : Monomial n} (h : keyDegLex k A B)
    (C : Monomial n) : keyDegLex k (A + C) (B + C) := by
  unfold keyDegLex at *
  rw [Multiset.map_add, Multiset.map_add]
  exact degLex_add_right h _

/-- With keys distinct on a set of classes, the key order is total on the
monomials over that set. -/
theorem keyDegLex_total {k : Fin n → Fin n} {S : Set (Fin n)} (hk : Set.InjOn k S)
    {M N : Monomial n} (hM : ∀ x ∈ M, x ∈ S) (hN : ∀ x ∈ N, x ∈ S) :
    keyDegLex k M N ∨ M = N ∨ keyDegLex k N M := by
  rcases degLex_trichotomous (M.map k) (N.map k) with h | h | h
  · exact Or.inl h
  · right; left
    classical
    rcases isEmpty_or_nonempty (Fin n) with hE | hE
    · rw [Multiset.eq_zero_of_forall_notMem (s := M) (fun x _ => hE.elim x),
        Multiset.eq_zero_of_forall_notMem (s := N) (fun x _ => hE.elim x)]
    have hinv := hk.leftInvOn_invFunOn
    have back : ∀ P : Monomial n, (∀ x ∈ P, x ∈ S) →
        (P.map k).map (Function.invFunOn k S) = P := by
      intro P hP
      rw [Multiset.map_map]
      conv_rhs => rw [← Multiset.map_id P]
      exact Multiset.map_congr rfl (fun x hx => hinv (hP x hx))
    rw [← back M hM, ← back N hN, h]
  · exact Or.inr (Or.inr h)

/-- The key function after merging class `b` into `a`: the merged class takes
the lesser key (`fold_min_monomial`). -/
def mergeKey (k : Fin n → Fin n) (a b : Fin n) : Fin n → Fin n :=
  fun x => if x = a then min (k a) (k b) else k x

/-- `key_merge`: the merged class's key is the minimum of the two. -/
theorem key_merge (k : Fin n → Fin n) (a b : Fin n) : mergeKey k a b a = min (k a) (k b) := by
  simp [mergeKey]

/-- Keys stay distinct: with distinct keys on the live classes `S`, after
merging `b ∈ S` into `a ∈ S` the keys are distinct on `S \ {b}`. -/
theorem key_merge_injOn {k : Fin n → Fin n} {S : Set (Fin n)} (hk : Set.InjOn k S)
    {a b : Fin n} (ha : a ∈ S) (hb : b ∈ S) : Set.InjOn (mergeKey k a b) (S \ {b}) := by
  intro x hx y hy hxy
  have hxb : x ≠ b := hx.2
  have hyb : y ≠ b := hy.2
  have aux : ∀ z ∈ S, z ≠ a → z ≠ b → min (k a) (k b) ≠ k z := by
    intro z hz hza hzb h
    rcases min_choice (k a) (k b) with hm | hm <;> rw [hm] at h
    · exact hza (hk hz ha h.symm)
    · exact hzb (hk hz hb h.symm)
  by_cases hxa : x = a <;> by_cases hya : y = a
  · rw [hxa, hya]
  · simp only [mergeKey, hxa, hya, ↓reduceIte] at hxy
    exact absurd hxy (aux y hy.1 hya hyb)
  · simp only [mergeKey, hxa, hya, ↓reduceIte] at hxy
    exact absurd hxy.symm (aux x hx.1 hxa hxb)
  · simp only [mergeKey, hxa, hya, ↓reduceIte] at hxy
    exact hk hx.1 hy.1 hxy

/-- Renaming a child `b` to `a` (the recanonization after the merge). -/
def ren (a b : Fin n) : Fin n → Fin n := fun x => if x = b then a else x

theorem mergeKey_ren_le (k : Fin n → Fin n) (a b x : Fin n) :
    mergeKey k a b (ren a b x) ≤ k x := by
  unfold mergeKey ren
  by_cases hxb : x = b
  · simp [hxb]
  · by_cases hxa : x = a
    · simp [hxa]
    · simp [hxb, hxa]

theorem mergeKey_le (k : Fin n → Fin n) (a b x : Fin n) : mergeKey k a b x ≤ k x := by
  unfold mergeKey
  by_cases hxa : x = a
  · subst hxa; simp
  · simp [hxa]

/-- `rename_key_le`: a node holding the absorbed class as a child, renamed to
the survivor and read with the merged keys, stays or shrinks. -/
theorem rename_key_le (k : Fin n → Fin n) (a b : Fin n) (M : Monomial n) :
    (M.map (ren a b)).map (mergeKey k a b) = M.map k ∨
      degLex (M.map k) ((M.map (ren a b)).map (mergeKey k a b)) := by
  rw [Multiset.map_map]
  exact map_le_of_pointwise M k _ (fun x _ => mergeKey_ren_le k a b x)

/-- A node that holds the survivor as a child keeps its span and is read with
the merged keys: it stays or shrinks (the parents `refresh_key_lowered`
visits). -/
theorem survivor_key_le (k : Fin n → Fin n) (a b : Fin n) (M : Monomial n) :
    M.map (mergeKey k a b) = M.map k ∨ degLex (M.map k) (M.map (mergeKey k a b)) :=
  map_le_of_pointwise M k _ (fun x _ => mergeKey_le k a b x)

namespace SlotState

/-- Each node's change at a merge is a no-op or an `Op.shrink` of the
existing model: the `SlotState` over keyed monomials needs no new operation. -/
theorem recanon_op {st : SlotState n} {c : Fin n} {M N : Monomial n} (hM : M ∈ st.active c)
    (h : N = M ∨ degLex M N) : N = M ∨ Op st (st.shrinkRefresh c M N) := by
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr (Op.shrink hM h)

/-- The keyed node of `M` after a merge of `b` into `a`, with or without the
rename, is a no-op or an `Op.shrink`. -/
theorem merge_recanon_op {st : SlotState n} {c : Fin n} (k : Fin n → Fin n) (a b : Fin n)
    {M : Monomial n} (hM : M.map k ∈ st.active c) :
    ((M.map (ren a b)).map (mergeKey k a b) = M.map k ∨
        Op st (st.shrinkRefresh c (M.map k) ((M.map (ren a b)).map (mergeKey k a b)))) ∧
      (M.map (mergeKey k a b) = M.map k ∨
        Op st (st.shrinkRefresh c (M.map k) (M.map (mergeKey k a b)))) :=
  ⟨recanon_op hM (rename_key_le k a b M), recanon_op hM (survivor_key_le k a b M)⟩

/-- `reachable_I5` for the engine with keys: its runs are runs of `Op`
(every recanonization being a no-op or a shrink by `merge_recanon_op`). -/
theorem keyed_reachable_I5 {st₀ st : SlotState n} (h₀ : I5 st₀) (hrun : OpsStar st₀ st) :
    I5 st :=
  reachable_I5 h₀ hrun

/-! ## The counter-model for the id order: `grow_wa.egg` -/

/-- In-place growth of an active node `M` to `M'` with the class's stored
minimal monomial left on the node: what the id order did when a child merged into a class with a larger
representative. -/
def idOrderGrow (st : SlotState n) (c : Fin n) (M M' : Monomial n) : SlotState n :=
  ⟨fun x => if x = c then insert M' ((st.active x).erase M) else st.active x,
   fun x => if x = c ∧ st.slot x = some M then some M' else st.slot x⟩

/-- Classes `a = 0, b = 1, c = 3, e = 4, w = 6`; class `5` holds `Add{a, b}`
and `Add{c, e}` with minimal monomial `Add{a, b}`. -/
def growBefore : SlotState 7 :=
  ⟨fun x => if x = 5 then {({0, 1} : Monomial 7), {3, 4}} else ∅,
   fun x => if x = 5 then some ({0, 1} : Monomial 7) else none⟩

theorem growBefore_I5 : I5 growBefore := by
  intro x
  by_cases hx : x = 5
  · subst hx
    simp only [growBefore, ite_true]
    refine ⟨fun _ => ⟨{0, 1}, rfl, Finset.mem_insert_self _ _, fun m' hm' => ?_⟩,
      fun h => absurd h (Finset.insert_ne_empty _ _)⟩
    rcases Finset.mem_insert.mp hm' with h | h
    · exact Or.inl h
    · rw [Finset.mem_singleton] at h
      subst h
      exact Or.inr (by decide)
  · simp only [growBefore, hx, ite_false]; exact good_empty

/-- `idOrder_grow_breaks_I5`: under the id order, `(union (w) (a))` keeping
`w` renames `a` to `w` and the node holding the minimal monomial grows to
`Add{b, w}`, above `Add{c, e}` (equal size, largest differing class `w`). The
stored minimal monomial names the grown node: I5 fails, and completion misses `Add{c, e, y} = Add{b, w, y}`.
Under keys the same merge gives the merged class the key of `a`, so the node
does not change (`rename_key_le`). -/
theorem idOrder_grow_breaks_I5 :
    I5 growBefore ∧ degLex ({1, 6} : Monomial 7) {0, 1} ∧
      ¬ I5 (growBefore.idOrderGrow 5 {0, 1} {1, 6}) := by
  refine ⟨growBefore_I5, by decide, fun h => ?_⟩
  have hgood := h 5
  simp only [idOrderGrow, growBefore, ite_true, true_and] at hgood
  obtain ⟨m, hm, hmin⟩ := hgood.1 ⟨{1, 6}, Finset.mem_insert_self _ _⟩
  have hm' : m = ({1, 6} : Monomial 7) := by
    injection hm with hm; exact hm.symm
  subst hm'
  have h34 : ({3, 4} : Monomial 7) ∈
      insert ({1, 6} : Monomial 7) (({({0, 1} : Monomial 7), {3, 4}} : Finset _).erase {0, 1}) := by
    decide
  rcases hmin.2 {3, 4} h34 with h' | h'
  · exact absurd h' (by decide)
  · exact absurd h' (by decide)

/-- The same merge under keys: `w` (key 6) absorbs `a` (key 0); the merged
class's key is `0`, so `Add{a, b}` read through the renamed child keeps its
keyed monomial. -/
theorem grow_wa_keyed :
    (({0, 1} : Monomial 7).map (ren 6 0)).map (mergeKey id 6 0) = ({0, 1} : Monomial 7).map id := by
  decide

end SlotState

end SemperProofs.CC
