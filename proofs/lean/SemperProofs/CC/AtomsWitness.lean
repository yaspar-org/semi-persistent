import SemperProofs.CC.Atoms

/-!
# A state with leaf constants that meets every hypothesis

The program

```
(union (+ a b) c)
(let t (+ a b d))
(let u (+ c d))
```

over plain AC, at the completion fixpoint. The classes are `a = 0`,
`b = 1`, `c = 2`, `d = 3` (leaf constants: no `+`-node, each atomic) and
`t = u = 4`. The stored nodes are `{a, b}` in `c`'s class and `{a, b, d}`,
`{c, d}` in class 4: completion rewrote `{a, b, d}` by the rule
`{a, b} → {c}` to `{c, d}`, merged the two classes and retired `{a, b, d}`
(`FLAG_AC_COLLAPSED`: the node stays in the graph and matchable, but it is
no completion rule, `RoundFixed.lhs_reduced`). The atoms are
`A = {a, b, c, d}`; the right-hand side of each atom's class is its
one-element monomial, that of class 4 is `{c, d}`. The view has one rule,
`{a, b} → {c}`.

`witness_complete` proves every hypothesis of `completion_complete_atoms`
(`CompleteAtoms`) for this state, by hand and `decide`, with the asserted
equation `{a, b} = {c}` between a stored node and a leaf constant.
`witness_I3` checks the retirement discipline: the retired node rewrites
to a node of its class. `witness_not_all` shows that the former hypothesis
`I0ActiveAll` fails on the stored state, so the former theorem did not
apply to it.
-/

namespace SemperProofs.CC.AtomsWitness

open Relation SemperProofs.CC

/-- The stored state. -/
def wst : State 5 where
  find := id
  nodes := {(({0, 1} : Monomial 5), 2), (({0, 1, 3} : Monomial 5), 4),
    (({2, 3} : Monomial 5), 4)}
  retired := {(({0, 1, 3} : Monomial 5), 4)}
  rhs := ![{0}, {1}, {2}, {3}, {2, 3}]

/-- The atomic classes: the leaf constants `a, b, c, d`. -/
def wA : Set (Fin 5) := {x | x.val < 4}

instance : DecidablePred (· ∈ wA) := fun x => inferInstanceAs (Decidable (x.val < 4))

/-- The asserted equation `a + b = c`. -/
def wS : Set (Monomial 5 × Monomial 5) := {(({0, 1} : Monomial 5), ({2} : Monomial 5))}

/-- The completion view. -/
abbrev wv : State 5 := wst.withAtoms wA none

/-- The one rule of the view. -/
def r₁ : Monomial 5 × Monomial 5 := ({0, 1}, {2})

theorem stored_mem {M : Monomial 5} {c : Fin 5} (h : (M, c) ∈ wst.active) :
    (M = {0, 1} ∧ c = 2) ∨ (M = {2, 3} ∧ c = 4) := by
  simp only [State.active, wst, Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff,
    Prod.mk.injEq] at h
  rcases h with ⟨h | h | h, hr⟩
  · exact Or.inl h
  · exact absurd h hr
  · exact Or.inr h

theorem stored_active {M : Monomial 5} {c : Fin 5}
    (h : (M = {0, 1} ∧ c = 2) ∨ (M = {2, 3} ∧ c = 4)) : (M, c) ∈ wst.active := by
  simp only [State.active, wst, Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff,
    Prod.mk.injEq]
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨Or.inl ⟨rfl, rfl⟩, fun h => absurd h.1 (by decide)⟩
  · exact ⟨Or.inr (Or.inr ⟨rfl, rfl⟩), fun h => absurd h.1 (by decide)⟩

/-- The retired node. -/
theorem retired_mem : ((({0, 1, 3} : Monomial 5), 4) : Monomial 5 × Fin 5) ∈ wv.retired :=
  ⟨rfl, fun h => by
    rcases h with ⟨-, h⟩ | ⟨h, -⟩
    · exact absurd h (by decide)
    · exact absurd h.symm (Option.some_ne_none _)⟩

theorem view_mem {M : Monomial 5} {c : Fin 5} (h : (M, c) ∈ wv.active) :
    (M = {0, 1} ∧ c = 2) ∨ (M = {2, 3} ∧ c = 4) ∨ (c.val < 4 ∧ M = {c}) := by
  rcases State.mem_active_withAtoms.1 h with h | h
  · rcases stored_mem h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · rcases h with h | ⟨h, -⟩
    · exact Or.inr (Or.inr h)
    · exact absurd h.symm (Option.some_ne_none c)

theorem atom_mem {x : Fin 5} (hx : x.val < 4) : (({x} : Monomial 5), x) ∈ wv.active :=
  State.atom_active (A := wA) (u := none) hx

theorem rhs_atom {c : Fin 5} (hc : c.val < 4) : wst.rhs c = {c} := by
  fin_cases c <;> first | rfl | exact absurd hc (by decide)

theorem r₁_mem : r₁ ∈ wv.rules :=
  ⟨2, 2, State.active_withAtoms (stored_active (Or.inl ⟨rfl, rfl⟩)), rfl, by decide,
    Or.inr (Or.inl ⟨by decide, rfl⟩), rfl⟩

/-- The one rule of the view is `r₁`: `{c, d}` is its class's right-hand
side, and an atom's one-element monomial is its class's right-hand side. -/
theorem view_rules {p : Monomial 5 × Monomial 5} (h : p ∈ wv.rules) : p = r₁ := by
  obtain ⟨c, c', hp, h2, hlt, -, -⟩ := h
  rcases view_mem hp with ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨hc, h1⟩
  · exact Prod.ext h1 h2
  · rw [h1, h2] at hlt
    exact absurd hlt (by decide)
  · change p.2 = wst.rhs c at h2
    rw [h1, h2, rhs_atom hc] at hlt
    exact absurd hlt (degLex_irrefl _)

/-- A step of the view's rule, for a clamp-free law set. -/
theorem view_step {L : Laws 5} (hL : ∀ M, L.clamp M = M) {M N : Monomial 5}
    (h : Rw L wv.rules M N) :
    ({0, 1} : Monomial 5) ≤ M ∧ N = M - {0, 1} + {2} := by
  obtain ⟨A, B, hAB, hA, rfl⟩ := h
  rw [hL]
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (view_rules hAB)
  exact ⟨hA, rfl⟩

/-- A set closed under the steps holds along every reduction. -/
theorem reach_closed {L : Laws 5} {P : Monomial 5 → Prop}
    (hP : ∀ M N, P M → Rw L wv.rules M N → P N) {M N : Monomial 5}
    (h : ReflTransGen (Rw L wv.rules) M N) (hM : P M) : P N := by
  induction h with
  | refl => exact hM
  | tail _ hs ih => exact hP _ _ ih hs

/-- A monomial not containing the left-hand side is normal. -/
theorem view_normal {L : Laws 5} (hL : ∀ M, L.clamp M = M) {M : Monomial 5}
    (h₁ : ¬ ({0, 1} : Monomial 5) ≤ M) (P : Monomial 5) : ¬ Rw L wv.rules M P :=
  fun h => h₁ (view_step hL h).1

/-- The monomials reachable from the view's active nodes, by start. -/
def Reach (M N : Monomial 5) : Prop :=
  (M = {0, 1} ∧ (N = {0, 1} ∨ N = {2})) ∨
  (M = {2, 3} ∧ N = {2, 3}) ∨
  (∃ x : Fin 5, M = {x} ∧ N = {x})

theorem reach {L : Laws 5} (hL : ∀ M, L.clamp M = M) {M c N}
    (hM : (M, c) ∈ wv.active) (h : ReflTransGen (Rw L wv.rules) M N) : Reach M N := by
  refine reach_closed (P := Reach M) ?_ h ?_
  · intro P Q hP hPQ
    obtain ⟨hle, rfl⟩ := view_step hL hPQ
    rcases hP with ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl⟩ | ⟨x, rfl, rfl⟩
    · exact Or.inl ⟨rfl, Or.inr (by decide)⟩
    · exact absurd hle (by decide)
    · exact absurd hle (by decide)
    · exfalso; have := Multiset.card_le_card hle; simp at this
  · rcases view_mem hM with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨-, rfl⟩
    · exact Or.inl ⟨rfl, Or.inl rfl⟩
    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · exact Or.inr (Or.inr ⟨c, rfl, rfl⟩)

theorem not_normal₁ {L : Laws 5} (hL : ∀ M, L.clamp M = M) :
    ¬ ∀ P, ¬ Rw L wv.rules ({0, 1} : Monomial 5) P :=
  fun h => h {2} ⟨_, _, r₁_mem, le_rfl, by rw [hL]; decide⟩

theorem joinable_of_eq {r : Monomial 5 → Monomial 5 → Prop} {a b : Monomial 5} (h : a = b) :
    Joinable r a b :=
  ⟨b, h ▸ ReflTransGen.refl, ReflTransGen.refl⟩

/-- A one-element monomial is no monomial of another size. -/
theorem single_ne {x : Fin 5} {M : Monomial 5} (h : ({x} : Monomial 5) = M)
    (hc : Multiset.card M ≠ 1 := by decide) : False :=
  hc (by rw [← h, Multiset.card_singleton])

/-- The class of an active node of the view with a two-element monomial. -/
theorem class_of {M : Monomial 5} {c : Fin 5} (hM : (M, c) ∈ wv.active)
    (hcard : Multiset.card M ≠ 1 := by decide) :
    (M = {0, 1} ∧ c = 2) ∨ (M = {2, 3} ∧ c = 4) := by
  rcases view_mem hM with h | h | ⟨-, h⟩
  · exact Or.inl h
  · exact Or.inr h
  · exact (single_ne h.symm hcard).elim

theorem class_23 {c : Fin 5} (hM : (({2, 3} : Monomial 5), c) ∈ wv.active) : c = 4 := by
  rcases class_of hM with ⟨h, -⟩ | ⟨-, rfl⟩
  · exact absurd h (by decide)
  · rfl

theorem class_01 {c : Fin 5} (hM : (({0, 1} : Monomial 5), c) ∈ wv.active) : c = 2 := by
  rcases class_of hM with ⟨-, rfl⟩ | ⟨h, -⟩
  · rfl
  · exact absurd h (by decide)

/-- An active node of the view with a one-element monomial `{y}` is the
implicit node of the atom `y`. -/
theorem class_single {y c : Fin 5} (hM : (({y} : Monomial 5), c) ∈ wv.active) :
    y = c ∧ c ∈ wA := by
  rcases view_mem hM with ⟨h, -⟩ | ⟨h, -⟩ | ⟨hc, h⟩
  · exact (single_ne h).elim
  · exact (single_ne h).elim
  · exact ⟨Multiset.singleton_inj.1 h, hc⟩

/-- The fixed round with leaf constants. The view has one rule, so
`lhs_reduced` and `cp_joinable` have no pair of distinct rules. -/
theorem witness_fixed : RoundFixedA (Laws.plainAC 5) wst wA none := by
  have hL : ∀ M, (Laws.plainAC 5).clamp M = M := fun _ => rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro M c N hM hMN hN hx
    rcases reach hL hM hMN with ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl⟩ | ⟨x, rfl, rfl⟩
    · exact absurd hN (not_normal₁ hL)
    · exact (hx 2 (Or.inl ⟨by decide, rfl⟩)).elim
    · exact ⟨4, stored_active (Or.inr ⟨rfl, rfl⟩), by rw [class_23 hM]⟩
    · obtain ⟨rfl, hc⟩ := class_single hM
      exact (hx x (Or.inl ⟨hc, rfl⟩)).elim
  · intro M c N x hM hx hMx hN
    rcases hx with ⟨-, hNx⟩ | ⟨hx, -⟩
    swap
    · exact absurd hx (Option.some_ne_none x).symm
    change N = {x} at hNx
    subst hNx
    rcases reach hL hM hMx with ⟨rfl, he | he⟩ | ⟨rfl, he⟩ | ⟨y, rfl, he⟩
    · exact (single_ne he).elim
    · obtain rfl := Multiset.singleton_inj.1 he
      rw [class_01 hM]
    · exact (single_ne he).elim
    · obtain rfl := Multiset.singleton_inj.1 he
      rw [(class_single hM).1]
  · intro p q hp hq hne
    rw [view_rules hp, view_rules hq] at hne
    exact absurd rfl hne
  · intro p q hp hq hne
    rw [view_rules hp, view_rules hq] at hne
    exact absurd rfl hne

/-- **Non-vacuity of `completion_complete_atoms`.** The state with leaf
constants above meets every hypothesis. Plain AC has no law instance, so
`AxiomCP` is empty. -/
theorem witness_complete : CompleteAtoms (Laws.plainAC 5) wS wst wA none := by
  have hL : ∀ M, (Laws.plainAC 5).clamp M = M := fun _ => rfl
  let ss : SlotState 5 :=
    ⟨![{{0}}, {{1}}, {{0, 1}, {2}}, {{3}}, {{2, 3}}], fun c => some (wst.rhs c)⟩
  refine ⟨⟨ss, ss, ?_, ReflTransGen.refl, ?_, fun _ _ => rfl⟩, ?_, fun _ => hL _, witness_fixed,
    fun _ _ h => h.elim, ?_, AxiomCP.of_no_ax fun _ h => h, ?_, ?_, fun h => h.elim⟩
  · intro c
    fin_cases c <;>
      exact ⟨fun _ => ⟨_, rfl, by unfold SlotState.IsMin; decide⟩, fun h => absurd h (by decide)⟩
  · intro M c hM
    rcases view_mem hM with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨hc, rfl⟩
    · decide
    · decide
    · fin_cases c <;> first | decide | exact absurd hc (by decide)
  · intro M c hM
    rcases view_mem hM with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨hc, rfl⟩
    · exact ⟨2, atom_mem (by decide), rfl⟩
    · exact ⟨4, State.active_withAtoms (stored_active (Or.inr ⟨rfl, rfl⟩)), rfl⟩
    · refine ⟨c, ?_, rfl⟩
      change (wst.rhs c, c) ∈ wv.active
      rw [rhs_atom hc]
      exact atom_mem hc
  · intro M N h
    obtain ⟨A, B, hAB, -, -⟩ := h
    exact hAB
  · intro P c d hc hd
    rcases stored_mem hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    rcases stored_mem hd with ⟨h, rfl⟩ | ⟨h, rfl⟩ <;>
    first | rfl | exact absurd h (by decide)
  · intro M N h
    simp only [wS, Set.mem_singleton_iff, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨2, 2, State.active_withAtoms (stored_active (Or.inl ⟨rfl, rfl⟩)),
      atom_mem (by decide), rfl⟩

/-- The retirement discipline on the view: the retired node `{a, b, d}`
rewrites in one step, by the rule `{a, b} → {c}`, to the node `{c, d}` of
its class. -/
theorem witness_I3 : I3 (Laws.plainAC 5) wv := by
  intro M c hM
  obtain ⟨hM, -⟩ := hM
  simp only [wst, Set.mem_singleton_iff, Prod.mk.injEq] at hM
  obtain ⟨rfl, rfl⟩ := hM
  refine ⟨{2, 3}, 4, TransGen.single ⟨_, _, r₁_mem, by decide, by decide⟩, ?_, rfl⟩
  exact Or.inl (Or.inr (Or.inr rfl))

/-- The former hypothesis `I0ActiveAll` fails on the stored state: the leaf
constant `a` holds no node. -/
theorem witness_not_all : ¬ I0ActiveAll wst := by
  intro h
  obtain ⟨c', hc', -⟩ := h 0
  rcases stored_mem hc' with ⟨h, -⟩ | ⟨h, -⟩ <;> exact absurd h (by decide)

/-- The theorem applied: `{a, b}` lands in `c`'s class, and the retired
node `{a, b, d}` is not an active node, so the theorem does not speak
about it; its class is that of `{c, d}` by construction (`wst.find`). -/
example : wst.find 2 = wst.find 2 :=
  witness_complete.atom_class (stored_active (Or.inl ⟨rfl, rfl⟩)) (by decide) (E.ax rfl)

end SemperProofs.CC.AtomsWitness
