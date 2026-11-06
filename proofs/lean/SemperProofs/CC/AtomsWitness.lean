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
`{a, b} → {c}` to `{c, d}` and merged the two classes. The atoms are
`A = {a, b, c, d}`; the right-hand side of each atom's class is its
one-element monomial, that of class 4 is `{c, d}`.

`witness_complete` proves every hypothesis of `completion_complete_atoms`
(`CompleteAtoms`) for this state, by hand and `decide`, with the asserted
equation `{a, b} = {c}` between a stored node and a leaf constant.
`witness_not_all` shows that the former hypothesis `I0ActiveAll` fails on
the stored state, so the former theorem did not apply to it.
-/

namespace SemperProofs.CC.AtomsWitness

open Relation SemperProofs.CC

/-- The stored state. -/
def wst : State 5 where
  find := id
  nodes := {(({0, 1} : Monomial 5), 2), (({0, 1, 3} : Monomial 5), 4),
    (({2, 3} : Monomial 5), 4)}
  retired := ∅
  rhs := ![{0}, {1}, {2}, {3}, {2, 3}]

/-- The atomic classes: the leaf constants `a, b, c, d`. -/
def wA : Set (Fin 5) := {x | x.val < 4}

instance : DecidablePred (· ∈ wA) := fun x => inferInstanceAs (Decidable (x.val < 4))

/-- The asserted equation `a + b = c`. -/
def wS : Set (Monomial 5 × Monomial 5) := {(({0, 1} : Monomial 5), ({2} : Monomial 5))}

/-- The completion view. -/
abbrev wv : State 5 := wst.withAtoms wA none

/-- The two rules of the view. -/
def r₁ : Monomial 5 × Monomial 5 := ({0, 1}, {2})
def r₂ : Monomial 5 × Monomial 5 := ({0, 1, 3}, {2, 3})

theorem stored_mem {M : Monomial 5} {c : Fin 5} (h : (M, c) ∈ wst.active) :
    (M = {0, 1} ∧ c = 2) ∨ (M = {0, 1, 3} ∧ c = 4) ∨ (M = {2, 3} ∧ c = 4) := by
  simpa only [State.active, wst, Set.sdiff_empty, Set.mem_insert_iff, Set.mem_singleton_iff,
    Prod.mk.injEq] using h

theorem stored_active {M : Monomial 5} {c : Fin 5}
    (h : (M = {0, 1} ∧ c = 2) ∨ (M = {0, 1, 3} ∧ c = 4) ∨ (M = {2, 3} ∧ c = 4)) :
    (M, c) ∈ wst.active := by
  simpa only [State.active, wst, Set.sdiff_empty, Set.mem_insert_iff, Set.mem_singleton_iff,
    Prod.mk.injEq] using h

theorem view_mem {M : Monomial 5} {c : Fin 5} (h : (M, c) ∈ wv.active) :
    (M = {0, 1} ∧ c = 2) ∨ (M = {0, 1, 3} ∧ c = 4) ∨ (M = {2, 3} ∧ c = 4) ∨
      (c.val < 4 ∧ M = {c}) := by
  rcases State.mem_active_withAtoms.1 h with h | h
  · rcases stored_mem h with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
  · rcases h with h | ⟨h, -⟩
    · exact Or.inr (Or.inr (Or.inr h))
    · exact absurd h.symm (Option.some_ne_none c)

theorem atom_mem {x : Fin 5} (hx : x.val < 4) : (({x} : Monomial 5), x) ∈ wv.active :=
  State.atom_active (A := wA) (u := none) hx

theorem rhs_atom {c : Fin 5} (hc : c.val < 4) : wst.rhs c = {c} := by
  fin_cases c <;> first | rfl | exact absurd hc (by decide)

theorem r₁_mem : r₁ ∈ wv.rules :=
  ⟨2, 2, State.active_withAtoms (stored_active (Or.inl ⟨rfl, rfl⟩)), rfl, by decide,
    Or.inr (Or.inl ⟨by decide, rfl⟩), rfl⟩

theorem r₂_mem : r₂ ∈ wv.rules :=
  ⟨4, 4, State.active_withAtoms (stored_active (Or.inr (Or.inl ⟨rfl, rfl⟩))), rfl, by decide,
    Or.inl (Or.inr (Or.inr rfl)), rfl⟩

/-- The rules of the view are `r₁` and `r₂`. -/
theorem view_rules {p : Monomial 5 × Monomial 5} (h : p ∈ wv.rules) : p = r₁ ∨ p = r₂ := by
  obtain ⟨c, c', hp, h2, hlt, -, -⟩ := h
  rcases view_mem hp with ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨hc, h1⟩
  · exact Or.inl (Prod.ext h1 h2)
  · exact Or.inr (Prod.ext h1 h2)
  · rw [h1, h2] at hlt
    exact absurd hlt (by decide)
  · change p.2 = wst.rhs c at h2
    rw [h1, h2, rhs_atom hc] at hlt
    exact absurd hlt (degLex_irrefl _)

/-- A step of the view's rules, for a clamp-free law set. -/
theorem view_step {L : Laws 5} (hL : ∀ M, L.clamp M = M) {M N : Monomial 5}
    (h : Rw L wv.rules M N) :
    (({0, 1} : Monomial 5) ≤ M ∧ N = M - {0, 1} + {2}) ∨
      (({0, 1, 3} : Monomial 5) ≤ M ∧ N = M - {0, 1, 3} + {2, 3}) := by
  obtain ⟨A, B, hAB, hA, rfl⟩ := h
  rw [hL]
  rcases view_rules hAB with h | h <;> obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
  · exact Or.inl ⟨hA, rfl⟩
  · exact Or.inr ⟨hA, rfl⟩

/-- A set closed under the steps holds along every reduction. -/
theorem reach_closed {L : Laws 5} {P : Monomial 5 → Prop}
    (hP : ∀ M N, P M → Rw L wv.rules M N → P N) {M N : Monomial 5}
    (h : ReflTransGen (Rw L wv.rules) M N) (hM : P M) : P N := by
  induction h with
  | refl => exact hM
  | tail _ hs ih => exact hP _ _ ih hs

/-- A monomial containing neither left-hand side is normal. -/
theorem view_normal {L : Laws 5} (hL : ∀ M, L.clamp M = M) {M : Monomial 5}
    (h₁ : ¬ ({0, 1} : Monomial 5) ≤ M) (h₂ : ¬ ({0, 1, 3} : Monomial 5) ≤ M) (P : Monomial 5) :
    ¬ Rw L wv.rules M P := by
  intro h
  rcases view_step hL h with ⟨h, -⟩ | ⟨h, -⟩
  · exact h₁ h
  · exact h₂ h

/-- The monomials reachable from the view's active nodes, by start. -/
def Reach (M N : Monomial 5) : Prop :=
  (M = {0, 1} ∧ (N = {0, 1} ∨ N = {2})) ∨
  (M = {0, 1, 3} ∧ (N = {0, 1, 3} ∨ N = {2, 3})) ∨
  (M = {2, 3} ∧ N = {2, 3}) ∨
  (∃ x : Fin 5, M = {x} ∧ N = {x})

theorem reach {L : Laws 5} (hL : ∀ M, L.clamp M = M) {M c N}
    (hM : (M, c) ∈ wv.active) (h : ReflTransGen (Rw L wv.rules) M N) : Reach M N := by
  refine reach_closed (P := Reach M) ?_ h ?_
  · intro P Q hP hPQ
    rcases view_step hL hPQ with ⟨hle, rfl⟩ | ⟨hle, rfl⟩ <;>
    rcases hP with ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl⟩ | ⟨x, rfl, rfl⟩
    all_goals first
      | exact absurd hle (by decide)
      | (left; exact ⟨rfl, Or.inr (by decide)⟩)
      | (right; left; exact ⟨rfl, Or.inr (by decide)⟩)
      | (exfalso; have := Multiset.card_le_card hle; simp at this)
  · rcases view_mem hM with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨-, rfl⟩
    · exact Or.inl ⟨rfl, Or.inl rfl⟩
    · exact Or.inr (Or.inl ⟨rfl, Or.inl rfl⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨c, rfl, rfl⟩))

theorem not_normal₁ {L : Laws 5} (hL : ∀ M, L.clamp M = M) :
    ¬ ∀ P, ¬ Rw L wv.rules ({0, 1} : Monomial 5) P :=
  fun h => h {2} ⟨_, _, r₁_mem, le_rfl, by rw [hL]; decide⟩

theorem not_normal₂ {L : Laws 5} (hL : ∀ M, L.clamp M = M) :
    ¬ ∀ P, ¬ Rw L wv.rules ({0, 1, 3} : Monomial 5) P :=
  fun h => h {2, 3} ⟨_, _, r₂_mem, le_rfl, by rw [hL]; decide⟩

theorem joinable_of_eq {r : Monomial 5 → Monomial 5 → Prop} {a b : Monomial 5} (h : a = b) :
    Joinable r a b :=
  ⟨b, h ▸ ReflTransGen.refl, ReflTransGen.refl⟩

/-- A one-element monomial is no monomial of another size. -/
theorem single_ne {x : Fin 5} {M : Monomial 5} (h : ({x} : Monomial 5) = M)
    (hc : Multiset.card M ≠ 1 := by decide) : False :=
  hc (by rw [← h, Multiset.card_singleton])

/-- The class of an active node of the view with a two- or three-element
monomial. -/
theorem class_of {M : Monomial 5} {c : Fin 5} (hM : (M, c) ∈ wv.active)
    (hcard : Multiset.card M ≠ 1 := by decide) :
    (M = {0, 1} ∧ c = 2) ∨ (M = {0, 1, 3} ∧ c = 4) ∨ (M = {2, 3} ∧ c = 4) := by
  rcases view_mem hM with h | h | h | ⟨-, h⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)
  · exact (single_ne h.symm hcard).elim

theorem class_013 {c : Fin 5} (hM : (({0, 1, 3} : Monomial 5), c) ∈ wv.active) : c = 4 := by
  rcases class_of hM with ⟨h, -⟩ | ⟨-, rfl⟩ | ⟨h, -⟩
  · exact absurd h (by decide)
  · rfl
  · exact absurd h (by decide)

theorem class_23 {c : Fin 5} (hM : (({2, 3} : Monomial 5), c) ∈ wv.active) : c = 4 := by
  rcases class_of hM with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, rfl⟩
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · rfl

theorem class_01 {c : Fin 5} (hM : (({0, 1} : Monomial 5), c) ∈ wv.active) : c = 2 := by
  rcases class_of hM with ⟨-, rfl⟩ | ⟨h, -⟩ | ⟨h, -⟩
  · rfl
  · exact absurd h (by decide)
  · exact absurd h (by decide)

/-- An active node of the view with a one-element monomial `{y}` is the
implicit node of the atom `y`. -/
theorem class_single {y c : Fin 5} (hM : (({y} : Monomial 5), c) ∈ wv.active) :
    y = c ∧ c ∈ wA := by
  rcases view_mem hM with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨hc, h⟩
  · exact (single_ne h).elim
  · exact (single_ne h).elim
  · exact (single_ne h).elim
  · exact ⟨Multiset.singleton_inj.1 h, hc⟩

/-- The fixed round with leaf constants. -/
theorem witness_fixed : RoundFixedA (Laws.plainAC 5) wst wA none := by
  have hL : ∀ M, (Laws.plainAC 5).clamp M = M := fun _ => rfl
  refine ⟨?_, ?_, ?_⟩
  · intro M c N hM hMN hN hx
    rcases reach hL hM hMN with
      ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl⟩ | ⟨x, rfl, rfl⟩
    · exact absurd hN (not_normal₁ hL)
    · exact (hx 2 (Or.inl ⟨by decide, rfl⟩)).elim
    · exact absurd hN (not_normal₂ hL)
    · exact ⟨4, stored_active (Or.inr (Or.inr ⟨rfl, rfl⟩)), by rw [class_013 hM]⟩
    · exact ⟨4, stored_active (Or.inr (Or.inr ⟨rfl, rfl⟩)), by rw [class_23 hM]⟩
    · obtain ⟨rfl, hc⟩ := class_single hM
      exact (hx x (Or.inl ⟨hc, rfl⟩)).elim
  · intro M c N x hM hx hMx hN
    rcases hx with ⟨-, hNx⟩ | ⟨hx, -⟩
    swap
    · exact absurd hx (Option.some_ne_none x).symm
    change N = {x} at hNx
    subst hNx
    rcases reach hL hM hMx with
      ⟨rfl, he | he⟩ | ⟨rfl, he | he⟩ | ⟨rfl, he⟩ | ⟨y, rfl, he⟩
    · exact (single_ne he).elim
    · obtain rfl := Multiset.singleton_inj.1 he
      rw [class_01 hM]
    · exact (single_ne he).elim
    · exact (single_ne he).elim
    · exact (single_ne he).elim
    · obtain rfl := Multiset.singleton_inj.1 he
      rw [(class_single hM).1]
  · intro p q hp hq hne _
    rcases view_rules hp with rfl | rfl <;> rcases view_rules hq with rfl | rfl
    all_goals first
      | exact absurd rfl hne
      | exact joinable_of_eq (by decide)

/-- **Non-vacuity of `completion_complete_atoms`.** The state with leaf
constants above meets every hypothesis. -/
theorem witness_complete : CompleteAtoms (Laws.plainAC 5) wS wst wA none := by
  have hL : ∀ M, (Laws.plainAC 5).clamp M = M := fun _ => rfl
  let ss : SlotState 5 :=
    ⟨![{{0}}, {{1}}, {{0, 1}, {2}}, {{3}}, {{0, 1, 3}, {2, 3}}], fun c => some (wst.rhs c)⟩
  refine ⟨⟨ss, ss, ?_, ReflTransGen.refl, ?_, fun _ _ => rfl⟩, ?_, fun _ => hL _, witness_fixed,
    fun _ _ h => h.elim, ?_, ?_, ?_, ?_, fun h => h.elim⟩
  · intro c
    fin_cases c <;>
      exact ⟨fun _ => ⟨_, rfl, by unfold SlotState.IsMin; decide⟩, fun h => absurd h (by decide)⟩
  · intro M c hM
    rcases view_mem hM with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨hc, rfl⟩
    · decide
    · decide
    · decide
    · fin_cases c <;> first | decide | exact absurd hc (by decide)
  · intro M c hM
    rcases view_mem hM with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨hc, rfl⟩
    · exact ⟨2, atom_mem (by decide), rfl⟩
    · exact ⟨4, State.active_withAtoms (stored_active (Or.inr (Or.inr ⟨rfl, rfl⟩))), rfl⟩
    · exact ⟨4, State.active_withAtoms (stored_active (Or.inr (Or.inr ⟨rfl, rfl⟩))), rfl⟩
    · refine ⟨c, ?_, rfl⟩
      change (wst.rhs c, c) ∈ wv.active
      rw [rhs_atom hc]
      exact atom_mem hc
  · intro M N h
    obtain ⟨A, B, hAB, -, -⟩ := h
    exact hAB
  · intro p q hp hq hne _
    have hp' : p ∈ wv.rules := hp.resolve_right (fun h => h)
    have hq' : q ∈ wv.rules := hq.resolve_right (fun h => h)
    rcases view_rules hp' with rfl | rfl <;> rcases view_rules hq' with rfl | rfl
    all_goals first
      | exact absurd rfl hne
      | exact joinable_of_eq (by decide)
  · intro P c d hc hd
    rcases stored_mem hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    rcases stored_mem hd with ⟨h, rfl⟩ | ⟨h, rfl⟩ | ⟨h, rfl⟩ <;>
    first | rfl | exact absurd h (by decide)
  · intro M N h
    simp only [wS, Set.mem_singleton_iff, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨2, 2, State.active_withAtoms (stored_active (Or.inl ⟨rfl, rfl⟩)),
      atom_mem (by decide), rfl⟩

/-- The former hypothesis `I0ActiveAll` fails on the stored state: the leaf
constant `a` holds no node. -/
theorem witness_not_all : ¬ I0ActiveAll wst := by
  intro h
  obtain ⟨c', hc', -⟩ := h 0
  rcases stored_mem hc' with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> exact absurd h (by decide)

/-- The theorem applied: the node `{a, b, d}` equals the leaf constant
term `c + d`, and `{a, b}` lands in `c`'s class. -/
example : wst.find 4 = wst.find 4 ∧ wst.find 2 = wst.find 2 := by
  have hE : E (Laws.plainAC 5) wS ({0, 1, 3} : Monomial 5) {2, 3} := by
    have h := E.congr (L := Laws.plainAC 5) ({3} : Monomial 5) (E.ax (S := wS) rfl)
    have e₁ : ({0, 1} : Monomial 5) + {3} = {0, 1, 3} := by decide
    have e₂ : ({2} : Monomial 5) + {3} = {2, 3} := by decide
    rwa [e₁, e₂] at h
  exact ⟨witness_complete.nodes (stored_active (Or.inr (Or.inl ⟨rfl, rfl⟩)))
      (stored_active (Or.inr (Or.inr ⟨rfl, rfl⟩))) hE,
    witness_complete.atom_class (stored_active (Or.inl ⟨rfl, rfl⟩)) (by decide)
      (E.ax rfl)⟩

end SemperProofs.CC.AtomsWitness
