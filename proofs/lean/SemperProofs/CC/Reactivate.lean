import SemperProofs.CC.Assemble

/-!
# The reactivation pass and the retirement discipline `I3`

A collapsed node (`FLAG_AC_COLLAPSED`, retired in the model) is no rule.
The engine collapses a node against the rules of the round that reduced
it; a later merge can reorient or retire every rule that reduced it, and
the node is then an equation that no rule represents. The pass
`unretire_irreducible_collapsed` (`egraph.rs`) runs after every congruence
rebuild of the completion loop and reactivates every collapsed node that
no current rule and no law reduces; the debug check
`check_no_irreducible_collapsed` asserts the result.

This file models the pass and derives `I3` from its fixpoint.

* `Reducible L st M`: the test of the pass. A rule of `st.rules` has its
  left-hand side inside `M` (`RuleReducible`), or a law changes `M`
  (`LawReducible`: `L.clamp M ≠ M`, that is a unit summand, a count the
  nilpotent or idempotent clamp lowers, an inverse pair).
  `reducible_iff_RwL` and `reducible_iff_RwAx` read it as the existence of
  a step of `State.RwL`, and of plain rewriting by the rules and the law
  instances.
* `State.reactivateOn`: the transcription of the pass, a fold of
  `State.reactivateStep` over the list of collapsed nodes with the rules
  read once at entry. `State.reactivate` is its result stated without the
  list: every retired node whose monomial is not `Reducible` is un-retired
  and each class takes the least of its stored right-hand side and the
  reactivated monomials (`reactivateOn_eq`).
* `reactivate_reachable`, `reactivate_I2`, `reactivate_I4`,
  `reactivate_I5`: the pass is a run of `Infer.unretire` and `Infer.setRhs`
  and keeps the invariants.
* `reactivate_fixed_iff`: the pass changes nothing exactly when every
  retired node is `Reducible`. `reactivate_idem`: the state the pass
  returns is such a state.
* `I3_of_reactivate_fixed`: at a state the pass leaves unchanged, `I3`
  holds, given the hypotheses of completeness at convergence.
  `ReactivateCE.reactivate_fixed_not_I3`: without them it does not.

## Where the derivation applies

The derivation goes through confluence of rewriting by the rules and the
law instances: the pass makes a retired node reducible, and confluence
places its normal form in its class. The engine-level theorems for an
operator with inverses (`completion_complete_inverse_engine`,
`completion_complete_combined_engine`,
`completion_complete_identityInverse_engine`, `Laws/InvRulesMain.lean`) use
`I3` before confluence is available: they read a node asserted by R3 to R5,
possibly retired since, as joinable with its class, and that joinability is
what closes the critical pairs of a rule with an inverse pair. They keep
`I3` as a hypothesis. For a cancellative operator the derivation needs
`hcancel`, which lattice closure does not give.

## What the model identifies

The engine's check passes two kinds of collapsed node without a reduction.

* A copy of an active node (same operator, class and monomial). The
  model's node is the pair of a monomial and a class id, and the pass
  itself makes no exception for a copy: it reactivates an irreducible one.
  The model follows the pass. `st.reactivate L = st` is the state the pass
  returns (`reactivate_idem`), which is stronger than what the check
  accepts.
* A degenerate monomial (empty, or one summand of count 1). Canonization
  stores no such `f`-node: the node is an equality with the unit or with
  the child's class, recorded as a merge. In the model the empty monomial
  and `{x}` are the implicit nodes of `State.withAtoms`, which are never
  retired, so the case does not arise among the retired nodes of the view.

The pass tests the rules and the inverse pair only. The other laws of the
check (unit summand, nilpotent and idempotent counts) are normalized away
when a node is canonized, so a stored monomial never meets them; in the
model all four are `LawReducible`.
-/

namespace SemperProofs.CC

open Relation

variable {n : ℕ}

/-! ## The test of the pass -/

/-- A rule of `R` has its left-hand side inside `M`
(`multiset_subset(lhs, &mono)`). -/
def RuleReducible (R : Rules n) (M : Monomial n) : Prop := ∃ A B, (A, B) ∈ R ∧ A ≤ M

/-- A law changes `M`: `clamp` removes a child (`group_cancel_pairs` for an
inverse pair; a unit summand or an over-threshold count for the other
laws). -/
def LawReducible (L : Laws n) (M : Monomial n) : Prop := L.clamp M ≠ M

/-- The test of the reactivation pass: `M` is reducible by a rule of the
state or by a law. -/
def Reducible (L : Laws n) (st : State n) (M : Monomial n) : Prop :=
  RuleReducible st.rules M ∨ LawReducible L M

/-- `Reducible` is the existence of a step by a rule or a law. -/
theorem reducible_iff_RwL {L : Laws n} {st : State n} {M : Monomial n} :
    Reducible L st M ↔ ∃ N, st.RwL L M N := by
  constructor
  · rintro (⟨A, B, hAB, hA⟩ | h)
    · exact ⟨_, Or.inl ⟨A, B, hAB, hA, rfl⟩⟩
    · exact ⟨_, Or.inr ⟨rfl, h⟩⟩
  · rintro ⟨N, ⟨A, B, hAB, hA, -⟩ | ⟨-, h⟩⟩
    · exact Or.inl ⟨A, B, hAB, hA⟩
    · exact Or.inr h

/-- `Reducible` is the existence of a plain step by a rule or a law
instance, when `clamp` outputs are normal for the law instances. -/
theorem reducible_iff_RwAx {L : Laws n} {st : State n}
    (hnf_ax : ∀ M N, ¬ Rw (plain n) L.axRules (L.clamp M) N) {M : Monomial n} :
    Reducible L st M ↔ ∃ N, RwAx L st.rules M N := by
  constructor
  · rintro (⟨A, B, hAB, hA⟩ | h)
    · exact ⟨_, A, B, Or.inl hAB, hA, rfl⟩
    · rcases L.clamp_law M with hc | hc
      · exact absurd hc h
      · exact ⟨_, RwAx_of_law hc⟩
  · rintro ⟨N, A, B, hAB | hAB, hA, -⟩
    · exact Or.inl ⟨A, B, hAB, hA⟩
    · refine Or.inr fun hc => hnf_ax M _ ⟨A, B, hAB, ?_, rfl⟩
      rw [hc]
      exact hA

/-! ## The pass -/

namespace State

variable (st : State n)

/-- The stored right-hand sides after the nodes of `T` are active again:
each class takes the `≫`-least of its stored right-hand side and the
monomials of `T` in the class (`refresh_min_monomial`, once per node of
`T`). Read on representatives, as `rhs` is. -/
noncomputable def lowRhs (T : Set (Monomial n × Fin n)) (x : Fin n) : Monomial n :=
  (degLex_wf (n := n)).min (insert (st.rhs x) {M | ∃ c, (M, c) ∈ T ∧ st.find c = x})
    ⟨st.rhs x, Set.mem_insert _ _⟩

/-- Un-retire every node of `T`, with the refresh. -/
noncomputable def unretireAll (T : Set (Monomial n × Fin n)) : State n :=
  { st with retired := st.retired \ T, rhs := st.lowRhs T }

/-- **The reactivation pass** (`unretire_irreducible_collapsed`): every
retired node whose monomial is not `Reducible` is un-retired, with the
refresh. The rules are those of the state at entry. -/
noncomputable def reactivate (L : Laws n) : State n :=
  st.unretireAll {p | p ∈ st.retired ∧ ¬ Reducible L st p.1}

open Classical in
/-- One iteration of the pass's second loop, at the collapsed node `p`;
`R` is the rule set read by the first loop.

```rust
for id in collapsed {
    let op = self.node_op(id);
    self.node_monomial_into(id, &mut mono);
    if rules.iter().any(|(o, lhs)| *o == op && multiset_subset(lhs, &mono)) {
        continue;                                   // RuleReducible R p.1
    }
    if let Some(inv) = self.inverse_op(op)
        && self.group_cancel_pairs(inv, &mut mono)
    {
        continue;                                   // LawReducible L p.1
    }
    self.clear_node_flag(id, FLAG_AC_COLLAPSED);    // unretire p.1 p.2
    self.refresh_min_monomial(id);                  // refreshRhs p.1 p.2
}
``` -/
noncomputable def reactivateStep (L : Laws n) (R : Rules n) (st : State n)
    (p : Monomial n × Fin n) : State n :=
  if RuleReducible R p.1 ∨ LawReducible L p.1 then st
  else { st.unretire p.1 p.2 with rhs := st.refreshRhs p.1 p.2 }

/-- **The pass as the engine runs it.** `collapsed` is the list the first
loop builds (every completion node carrying `FLAG_AC_COLLAPSED`), and the
rule set is read once, before any node is reactivated.

```rust
for id in self.completion_node_ids() {
    let flags = self.node_flags(id);
    if flags & FLAG_SUBSUMED != 0 { continue; }
    if flags & FLAG_AC_COLLAPSED != 0 { collapsed.push(id); continue; }
    self.node_monomial_into(id, &mut mono);
    if self.class_rhs_into(id, &mut rhs)
        && self.monomial_cmp_key(&mono, &rhs) == Ordering::Greater
    {
        rules.push((self.node_op(id), mono.clone()));   // st.rules
    }
}
``` -/
noncomputable def reactivateOn (L : Laws n) (collapsed : List (Monomial n × Fin n)) : State n :=
  collapsed.foldl (reactivateStep L st.rules) st

end State

/-! ## The least right-hand side -/

theorem lowRhs_mem (st : State n) (T : Set (Monomial n × Fin n)) (x : Fin n) :
    st.lowRhs T x = st.rhs x ∨ ∃ c, (st.lowRhs T x, c) ∈ T ∧ st.find c = x := by
  have h := (degLex_wf (n := n)).min_mem
    (insert (st.rhs x) {M | ∃ c, (M, c) ∈ T ∧ st.find c = x}) ⟨st.rhs x, Set.mem_insert _ _⟩
  exact h

/-- The least right-hand side is at or below every candidate. -/
theorem lowRhs_le (st : State n) (T : Set (Monomial n × Fin n)) (x : Fin n) {N : Monomial n}
    (hN : N = st.rhs x ∨ ∃ c, (N, c) ∈ T ∧ st.find c = x) :
    st.lowRhs T x = N ∨ degLex N (st.lowRhs T x) := by
  have h : ¬ degLex (st.lowRhs T x) N := (degLex_wf (n := n)).not_lt_min
    (insert (st.rhs x) {M | ∃ c, (M, c) ∈ T ∧ st.find c = x}) hN
  rcases degLex_trichotomous N (st.lowRhs T x) with h' | h' | h'
  · exact Or.inr h'
  · exact Or.inl h'.symm
  · exact absurd h' h

/-- A candidate at or below every candidate is the least right-hand side. -/
theorem lowRhs_unique (st : State n) (T : Set (Monomial n × Fin n)) (x : Fin n) {m : Monomial n}
    (hm : m = st.rhs x ∨ ∃ c, (m, c) ∈ T ∧ st.find c = x)
    (hle : ∀ N, (N = st.rhs x ∨ ∃ c, (N, c) ∈ T ∧ st.find c = x) → m = N ∨ degLex N m) :
    st.lowRhs T x = m := by
  rcases lowRhs_le st T x hm with h | h
  · exact h
  · rcases hle _ (lowRhs_mem st T x) with h' | h'
    · exact h'.symm
    · exact absurd (degLex_trans h h') (degLex_irrefl _)

/-- A class with no node of `T` keeps its right-hand side. -/
theorem lowRhs_of_not_mem (st : State n) (T : Set (Monomial n × Fin n)) (x : Fin n)
    (h : ∀ M c, (M, c) ∈ T → st.find c ≠ x) : st.lowRhs T x = st.rhs x := by
  rcases lowRhs_mem st T x with h' | ⟨c, hc, hx⟩
  · exact h'
  · exact absurd hx (h _ c hc)

theorem unretireAll_empty (st : State n) : st.unretireAll ∅ = st := by
  have hr : st.lowRhs ∅ = st.rhs :=
    funext fun x => lowRhs_of_not_mem st ∅ x (fun _ _ h => absurd h (Set.notMem_empty _))
  obtain ⟨f, nd, rt, rh⟩ := st
  simp only [State.unretireAll, State.mk.injEq, true_and]
  exact ⟨Set.sdiff_empty, hr⟩

/-! ## The pass changes nothing exactly when every retired node is reducible -/

/-- **The fixpoint of the pass.** The pass leaves the state unchanged
exactly when every retired node is reducible by a rule or a law. -/
theorem reactivate_fixed_iff {L : Laws n} {st : State n} :
    st.reactivate L = st ↔ ∀ M c, (M, c) ∈ st.retired → Reducible L st M := by
  constructor
  · intro h M c hM
    have hr : st.retired \ {p | p ∈ st.retired ∧ ¬ Reducible L st p.1} = st.retired :=
      congrArg State.retired h
    rw [← hr] at hM
    by_contra hred
    exact hM.2 ⟨hM.1, hred⟩
  · intro h
    have hT : {p : Monomial n × Fin n | p ∈ st.retired ∧ ¬ Reducible L st p.1} = ∅ :=
      Set.eq_empty_iff_forall_notMem.2 fun p hp => hp.2 (h p.1 p.2 hp.1)
    unfold State.reactivate
    rw [hT]
    exact unretireAll_empty st

/-! ## The fold is the pass -/

/-- One iteration at an irreducible node adds it to the reactivated set. -/
theorem reactivateStep_unretireAll {L : Laws n} (st : State n) (T : Set (Monomial n × Fin n))
    (p : Monomial n × Fin n) :
    State.reactivateStep L st.rules (st.unretireAll T) p =
      st.unretireAll (T ∪ {q | q = p ∧ ¬ Reducible L st p.1}) := by
  unfold State.reactivateStep
  by_cases hred : RuleReducible st.rules p.1 ∨ LawReducible L p.1
  · rw [if_pos hred]
    have : T ∪ {q | q = p ∧ ¬ Reducible L st p.1} = T := by
      ext q
      simp only [Set.mem_union, Set.mem_setOf_eq, or_iff_left_iff_imp]
      exact fun h => absurd hred h.2
    rw [this]
  · rw [if_neg hred]
    have hT : T ∪ {q | q = p ∧ ¬ Reducible L st p.1} = T ∪ {p} := by
      ext q
      simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_singleton_iff]
      exact ⟨fun h => h.imp id And.left, fun h => h.imp id fun h => ⟨h, hred⟩⟩
    rw [hT]
    obtain ⟨M, c⟩ := p
    have hret : (st.retired \ T) \ {(M, c)} = st.retired \ (T ∪ {(M, c)}) := by
      ext q
      simp only [Set.mem_sdiff, Set.mem_union, Set.mem_singleton_iff, not_or, and_assoc]
    have hrhs : (st.unretireAll T).refreshRhs M c = st.lowRhs (T ∪ {(M, c)}) := by
      funext x
      symm
      show st.lowRhs (T ∪ {(M, c)}) x =
        if x = st.find c ∧ degLex (st.lowRhs T (st.find c)) M then M else st.lowRhs T x
      by_cases hx : x = st.find c ∧ degLex (st.lowRhs T (st.find c)) M
      · rw [if_pos hx]
        obtain ⟨rfl, hlt⟩ := hx
        refine lowRhs_unique st _ _ (Or.inr ⟨c, Or.inr rfl, rfl⟩) ?_
        rintro N (rfl | ⟨d, hd | hd, hdx⟩)
        · rcases lowRhs_le st T (st.find c) (Or.inl rfl) with h | h
          · rw [← h]; exact Or.inr hlt
          · exact Or.inr (degLex_trans h hlt)
        · rcases lowRhs_le st T (st.find c) (Or.inr ⟨d, hd, hdx⟩) with h | h
          · rw [← h]; exact Or.inr hlt
          · exact Or.inr (degLex_trans h hlt)
        · exact Or.inl (Prod.mk.inj hd).1.symm
      · rw [if_neg hx]
        refine lowRhs_unique st _ _ ?_ ?_
        · exact (lowRhs_mem st T x).imp id fun ⟨d, hd, hdx⟩ => ⟨d, Or.inl hd, hdx⟩
        · rintro N (rfl | ⟨d, hd | hd, hdx⟩)
          · exact lowRhs_le st T x (Or.inl rfl)
          · exact lowRhs_le st T x (Or.inr ⟨d, hd, hdx⟩)
          · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hd
            subst hdx
            rcases degLex_trichotomous N (st.lowRhs T (st.find d)) with h | h | h
            · exact Or.inr h
            · exact Or.inl h.symm
            · exact absurd ⟨rfl, h⟩ hx
    show ({ (st.unretireAll T).unretire M c with rhs := (st.unretireAll T).refreshRhs M c } :
      State n) = st.unretireAll (T ∪ {(M, c)})
    rw [hrhs]
    simp only [State.unretireAll, State.unretire, hret]

theorem foldl_reactivateStep {L : Laws n} (st : State n) (l : List (Monomial n × Fin n))
    (T : Set (Monomial n × Fin n)) :
    l.foldl (State.reactivateStep L st.rules) (st.unretireAll T) =
      st.unretireAll (T ∪ {q | q ∈ l ∧ ¬ Reducible L st q.1}) := by
  induction l generalizing T with
  | nil => simp
  | cons p l ih =>
    rw [List.foldl_cons, reactivateStep_unretireAll, ih]
    congr 1
    ext q
    simp only [Set.mem_union, Set.mem_setOf_eq, List.mem_cons]
    constructor
    · rintro ((h | ⟨rfl, h⟩) | ⟨h, h'⟩)
      · exact Or.inl h
      · exact Or.inr ⟨Or.inl rfl, h⟩
      · exact Or.inr ⟨Or.inr h, h'⟩
    · rintro (h | ⟨rfl | h, h'⟩)
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr ⟨rfl, h'⟩)
      · exact Or.inr ⟨h, h'⟩

/-- **The transcription computes the pass.** The fold over a list that
holds exactly the retired nodes, in any order and with any repetition, is
`State.reactivate`. -/
theorem reactivateOn_eq {L : Laws n} {st : State n} {l : List (Monomial n × Fin n)}
    (hl : ∀ p, p ∈ l ↔ p ∈ st.retired) : st.reactivateOn L l = st.reactivate L := by
  have h := foldl_reactivateStep (L := L) st l ∅
  rw [unretireAll_empty] at h
  unfold State.reactivateOn State.reactivate
  rw [h]
  congr 1
  ext q
  simp only [Set.empty_union, Set.mem_setOf_eq, hl]

/-! ## The pass is a run of inference steps and keeps the invariants -/

/-- One iteration keeps I5 (`unretire_refresh_I5`). -/
theorem reactivateStep_I5 {L : Laws n} {R : Rules n} {st : State n} (h5 : I5 st)
    (p : Monomial n × Fin n) : I5 (State.reactivateStep L R st p) := by
  unfold State.reactivateStep
  split
  · exact h5
  · exact unretire_refresh_I5 h5 p.1 p.2

theorem foldl_reactivateStep_I5 {L : Laws n} {R : Rules n} (l : List (Monomial n × Fin n))
    {st : State n} (h5 : I5 st) : I5 (l.foldl (State.reactivateStep L R) st) := by
  induction l generalizing st with
  | nil => exact h5
  | cons p l ih => exact ih (reactivateStep_I5 h5 p)

/-- One iteration at a retired node is at most two inference steps
(`unretire_refresh_reachable`). -/
theorem reactivateStep_reachable {L L' : Laws n} {R : Rules n} {st : State n}
    {p : Monomial n × Fin n} (hp : p ∈ st.retired) :
    Reachable L' st (State.reactivateStep L R st p) := by
  unfold State.reactivateStep
  split
  · exact ReflTransGen.refl
  · exact unretire_refresh_reachable hp

theorem reactivateStep_retired {L : Laws n} {R : Rules n} {st : State n}
    {p q : Monomial n × Fin n} (hq : q ∈ st.retired) (hne : q ≠ p) :
    q ∈ (State.reactivateStep L R st p).retired := by
  unfold State.reactivateStep
  split
  · exact hq
  · exact ⟨hq, hne⟩

theorem foldl_reactivateStep_reachable {L L' : Laws n} {R : Rules n}
    (l : List (Monomial n × Fin n)) {st : State n} (hl : ∀ p ∈ l, p ∈ st.retired)
    (hnd : l.Nodup) : Reachable L' st (l.foldl (State.reactivateStep L R) st) := by
  induction l generalizing st with
  | nil => exact ReflTransGen.refl
  | cons p l ih =>
    rw [List.nodup_cons] at hnd
    refine (reactivateStep_reachable (hl p List.mem_cons_self)).trans (ih ?_ hnd.2)
    intro q hq
    exact reactivateStep_retired (hl q (List.mem_cons_of_mem _ hq))
      (fun h => hnd.1 (h ▸ hq))

/-- A finite retired set has a list that holds exactly its nodes, once each:
the engine's `collapsed` vector. -/
theorem exists_collapsed_list {st : State n} (hfin : st.retired.Finite) :
    ∃ l : List (Monomial n × Fin n), l.Nodup ∧ ∀ p, p ∈ l ↔ p ∈ st.retired :=
  ⟨hfin.toFinset.toList, Finset.nodup_toList _, fun p => by
    rw [Finset.mem_toList, Set.Finite.mem_toFinset]⟩

/-- **The pass is a run of `Infer.unretire` and `Infer.setRhs` steps.** The
retired set is finite, as the engine's node table is. -/
theorem reactivate_reachable {L L' : Laws n} {st : State n} (hfin : st.retired.Finite) :
    Reachable L' st (st.reactivate L) := by
  obtain ⟨l, hnd, hl⟩ := exists_collapsed_list hfin
  rw [← reactivateOn_eq hl]
  exact foldl_reactivateStep_reachable l (fun p hp => (hl p).1 hp) hnd

/-- The pass keeps I2: it changes neither the nodes nor the partition. -/
theorem reactivate_I2 {L L' : Laws n} {S : Set (Monomial n × Monomial n)} {st : State n}
    (h2 : I2 L' S st) : I2 L' S (st.reactivate L) := h2

/-- The pass keeps I4. -/
theorem reactivate_I4 {L : Laws n} {pool : Finset (Fin n)} {st : State n} (h4 : I4 pool st) :
    I4 pool (st.reactivate L) := h4

/-- **The pass keeps I5**, by `unretire_refresh_I5` at each reactivated
node. -/
theorem reactivate_I5 {L : Laws n} {st : State n} (hfin : st.retired.Finite) (h5 : I5 st) :
    I5 (st.reactivate L) := by
  obtain ⟨l, -, hl⟩ := exists_collapsed_list hfin
  rw [← reactivateOn_eq hl]
  exact foldl_reactivateStep_I5 l h5

/-- The pass keeps `RetiredCovered`: it only shrinks the retired set and so
only grows the active one. -/
theorem reactivate_retiredCovered {L : Laws n} {st : State n} (h : RetiredCovered st) :
    RetiredCovered (st.reactivate L) := by
  intro M c hM
  obtain ⟨hn, K, c', hK, hc⟩ := h M c hM.1
  exact ⟨hn, K, c', ⟨hK.1, fun h' => hK.2 h'.1⟩, hc⟩

/-! ## The state the pass returns is a fixpoint of the pass -/

/-- A rule of the state at entry keeps its left-hand side as a rule after
the pass: its node stays active, the class's right-hand side is the old one
or a reactivated monomial below it, and both are nodes of the class. -/
theorem ruleReducible_reactivate {L : Laws n} {st : State n} (hsub : st.retired ⊆ st.nodes)
    {M : Monomial n} (h : RuleReducible st.rules M) :
    RuleReducible (st.reactivate L).rules M := by
  obtain ⟨A, B, ⟨c, c', hA, hB, hlt, hBn, hcc⟩, hAM⟩ := h
  have hB' : B = st.rhs (st.find c) := hB
  subst hB'
  set T : Set (Monomial n × Fin n) := {p | p ∈ st.retired ∧ ¬ Reducible L st p.1} with hT
  have hact : (A, c) ∈ (st.reactivate L).active := ⟨hA.1, fun h => hA.2 h.1⟩
  have hlt' : degLex A (st.lowRhs T (st.find c)) := by
    rcases lowRhs_le st T (st.find c) (Or.inl rfl) with h | h
    · rw [h]; exact hlt
    · exact degLex_trans hlt h
  have hnode : ∃ d, (st.lowRhs T (st.find c), d) ∈ st.nodes ∧ st.find d = st.find c := by
    rcases lowRhs_mem st T (st.find c) with h | ⟨d, hd, hdc⟩
    · rw [h]; exact ⟨c', hBn, hcc⟩
    · exact ⟨d, hsub hd.1, hdc⟩
  obtain ⟨d, hd, hdc⟩ := hnode
  exact ⟨A, st.lowRhs T (st.find c), ⟨c, d, hact, rfl, hlt', hd, hdc⟩, hAM⟩

/-- **One pass is enough.** The state the pass returns is left unchanged by
the pass: reactivation only adds rules, so a node the pass left retired is
still reducible. This is the state the engine holds after
`unretire_irreducible_collapsed`, and so when the completion loop reports
a fixpoint, since the pass runs after the last rebuild. -/
theorem reactivate_idem {L : Laws n} {st : State n} (hsub : st.retired ⊆ st.nodes) :
    (st.reactivate L).reactivate L = st.reactivate L := by
  rw [reactivate_fixed_iff]
  intro M c hM
  have hred : Reducible L st M := by
    by_contra hred
    exact hM.2 ⟨hM.1, hred⟩
  exact hred.imp (ruleReducible_reactivate hsub) id

/-! ## `I3` at a fixpoint of the pass -/

/-- `I3` from reducibility of the retired nodes and confluence. A retired
node `M` is `=_E`-equal to an active node `K` of its class (`hcov`, `h2`),
so the two are joinable (`hjoin`), and `K` reduces to the class's
right-hand side, which is normal (`hnorm`): `M` reduces to it under plain
rewriting. The normal form of `M` under the steps of `State.RwL` is normal
for plain rewriting too (`hnf_ax`), so by confluence it is that right-hand
side, a node of the class (`h0`); `M` is reducible, so the chain has at
least one step. -/
theorem I3_of_reducible {L : Laws n} {S : Set (Monomial n × Monomial n)} {st : State n}
    (hred : ∀ M c, (M, c) ∈ st.retired → Reducible L st M)
    (hcov : RetiredCovered st) (h2 : I2 L S st) (h0 : I0Active st)
    (hconv : Converged L st) (hconf : Confluent (RwAx L st.rules))
    (hjoin : ∀ M N, E L S M N → Joinable (RwAx L st.rules) M N)
    (hnorm : ∀ K e, (K, e) ∈ st.active → ∀ Q, ¬ RwAx L st.rules (st.rhs (st.find e)) Q)
    (hnf_ax : ∀ M N, ¬ Rw (plain n) L.axRules (L.clamp M) N) : I3 L st := by
  intro M c hM
  obtain ⟨hMn, K, c', hK, hcc⟩ := hcov M c hM
  have hE : E L S M K := h2 M c K c' hMn hK.1 hcc.symm
  obtain ⟨P, hMP, hKP⟩ := hjoin M K hE
  have hKr : ReflTransGen (RwAx L st.rules) K (st.rhs (st.find c')) :=
    Rw_rtg_embed (hconv.nodes_reduce K c' hK)
  obtain ⟨Q, hrQ, hPQ⟩ := hconf _ _ _ hKr hKP
  have e₁ := rtg_of_normal (hnorm K c' hK) hrQ
  have hMr : ReflTransGen (RwAx L st.rules) M (st.rhs (st.find c')) := by
    rw [e₁]; exact hMP.trans hPQ
  obtain ⟨N, hMN, hN⟩ := exists_nf (RwL_wf L st) M
  have hNc : L.clamp N = N := by
    by_contra h
    exact hN _ (Or.inr ⟨rfl, h⟩)
  have hNn : ∀ Q, ¬ RwAx L st.rules N Q :=
    plain_normal_of_normal hnf_ax ⟨N, hNc.symm⟩ (fun Q h => hN Q (Or.inl h))
  obtain ⟨U, hNU, hrU⟩ := hconf _ _ _ (RwL_rtg_embed hMN) hMr
  have e₂ := rtg_of_normal hNn hNU
  have e₃ := rtg_of_normal (hnorm K c' hK) hrU
  have hNr : N = st.rhs (st.find c') := e₂.trans e₃.symm
  have htg : TransGen (st.RwL L) M N := by
    rcases reflTransGen_iff_eq_or_transGen.1 hMN with h | h
    · subst h
      obtain ⟨N', hN'⟩ := reducible_iff_RwL.1 (hred _ c hM)
      exact absurd hN' (hN _)
    · exact h
  obtain ⟨c'', hc'', hcc''⟩ := h0 K c' hK
  exact ⟨N, c'', htg, hNr ▸ hc''.1, hcc''.trans hcc⟩

/-- **`I3` from the reactivation pass at the fixpoint.** At a state the pass
leaves unchanged (`hreact`), every retired node reduces, in at least one
step by a rule or a law, to a node of its class. The other hypotheses are
those of completeness at convergence (`completion_complete_at_convergence'`),
without congruence, and with I5 itself in place of the slot run:

* `hcov`: a retired node is a stored node whose class holds an active node,
  the only node the retired one is known equal to (an `Infer` invariant,
  `retiredCovered_of_reachable`);
* `h2`: that equality is an `=_E`-consequence;
* `h0`, `h5`, `hcanon`, `hfix`: the fixed round, which makes every active
  node reduce to its class's right-hand side and that right-hand side
  normal (`roundFixed_converged`, `rhs_normal`);
* `hlaw`, `hnf_ax`, `hcp`: plain rewriting by the rules and the law
  instances is confluent (`RwAx_confluent`);
* `hS`, `hcancel`: `=_E`-equal monomials are joinable (`E_joinable_RwAx`).

Reducibility alone does not place a reduct of the retired node in its
class: the engine normalizes active nodes only. Confluence does, and the
landing class is derived from it. -/
theorem I3_of_reactivate_fixed {L : Laws n} {S : Set (Monomial n × Monomial n)} {st : State n}
    (hreact : st.reactivate L = st) (hcov : RetiredCovered st) (h2 : I2 L S st)
    (h0 : I0Active st) (h5 : I5 st) (hcanon : ∀ c, L.clamp (st.rhs c) = st.rhs c)
    (hfix : RoundFixed L st)
    (hlaw : ∀ P Q, L.lawRel P Q → degLex P Q)
    (hnf_ax : ∀ M N, ¬ Rw (plain n) L.axRules (L.clamp M) N)
    (hcp : ∀ r₁ r₂, r₁ ∈ st.rules ∪ L.axRules → r₂ ∈ st.rules ∪ L.axRules → r₁ ≠ r₂ →
      Overlap r₁.1 r₂.1 →
      Joinable (Rw (plain n) (st.rules ∪ L.axRules))
        (criticalPair (plain n) r₁ r₂).1 (criticalPair (plain n) r₁ r₂).2)
    (hS : ∀ M N, (M, N) ∈ S →
      ∃ c d, (M, c) ∈ st.active ∧ (N, d) ∈ st.active ∧ st.find c = st.find d)
    (hcancel : L.cancellative → ∀ M N X,
      Joinable (Rw (plain n) (st.rules ∪ L.axRules)) (M + X) (N + X) →
      Joinable (Rw (plain n) (st.rules ∪ L.axRules)) M N) : I3 L st := by
  have hconv : Converged L st := roundFixed_converged (I0On_of_active h0) h5 hcanon hfix
  have hconf : Confluent (RwAx L st.rules) :=
    RwAx_confluent L st.rules (rules_oriented st) hlaw hcp
  exact I3_of_reducible (reactivate_fixed_iff.1 hreact) hcov h2 h0 hconv hconf
    (fun _ _ h => E_joinable_RwAx hconv hconf hS hcancel h)
    (fun _ e hK => plain_normal_of_normal hnf_ax ⟨st.rhs (st.find e), (hcanon _).symm⟩
      (rhs_normal h0 h5 hfix hK))
    hnf_ax

/-! ## Reducibility alone does not give `I3`

A state that the pass leaves unchanged and whose retired node sits in a
class with an active node, at which `I3` fails: over plain AC, the rule
`{a, a} → {b}` reduces the retired node `{a, a, a}` of the class of `c`, and
its only reduct `{a, b}` is no node. The state is not sound for any set of
asserted equations between active nodes (`{a, a, a} = {c}` follows from
none), which is where `I3_of_reactivate_fixed` uses `I2` and `hS`. -/

namespace ReactivateCE

/-- Classes `a = 0`, `b = 1`, `c = 2`; nodes `{a, a}` and `{b}` in the class
of `b`, the retired `{a, a, a}` and `{c}` in the class of `c`. -/
def st : State 3 where
  find := id
  nodes := {(({0, 0} : Monomial 3), 1), (({1} : Monomial 3), 1),
    (({0, 0, 0} : Monomial 3), 2), (({2} : Monomial 3), 2)}
  retired := {(({0, 0, 0} : Monomial 3), 2)}
  rhs := ![{0}, {1}, {2}]

theorem nodes_mem {M : Monomial 3} {c : Fin 3} (h : (M, c) ∈ st.nodes) :
    (M = {0, 0} ∧ c = 1) ∨ (M = {1} ∧ c = 1) ∨ (M = {0, 0, 0} ∧ c = 2) ∨ (M = {2} ∧ c = 2) := by
  simpa only [st, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] using h

theorem rule_mem : ((({0, 0} : Monomial 3), ({1} : Monomial 3)) : Monomial 3 × Monomial 3) ∈
    st.rules :=
  ⟨1, 1, ⟨Or.inl rfl, fun h => absurd (congrArg Prod.snd h) (by decide)⟩, rfl, by decide,
    Or.inr (Or.inl rfl), rfl⟩

theorem rules_eq {p : Monomial 3 × Monomial 3} (h : p ∈ st.rules) : p = ({0, 0}, {1}) := by
  obtain ⟨c, c', hp, h2, hlt, -, -⟩ := h
  rcases nodes_mem hp.1 with ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨h1, rfl⟩
  · exact Prod.ext h1 h2
  · rw [h1, h2] at hlt
    exact absurd hlt (by decide)
  · exact absurd (show (p.1, (2 : Fin 3)) ∈ st.retired by rw [h1]; rfl) hp.2
  · rw [h1, h2] at hlt
    exact absurd hlt (by decide)

/-- A step keeps the count of `c`. -/
theorem step_count {M N : Monomial 3} (h : st.RwL (Laws.plainAC 3) M N) :
    N.count 2 = M.count 2 := by
  rcases h with ⟨A, B, hAB, -, rfl⟩ | ⟨-, hne⟩
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (rules_eq hAB)
    show (M - {0, 0} + {1}).count 2 = M.count 2
    rw [Multiset.count_add, Multiset.count_sub]
    have h₁ : ({0, 0} : Monomial 3).count 2 = 0 := by decide
    have h₂ : ({1} : Monomial 3).count 2 = 0 := by decide
    omega
  · exact absurd rfl hne

theorem reactivate_fixed : st.reactivate (Laws.plainAC 3) = st := by
  rw [reactivate_fixed_iff]
  intro M c hM
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (show (M, c) = (({0, 0, 0} : Monomial 3), (2 : Fin 3)) from hM)
  exact Or.inl ⟨_, _, rule_mem, by decide⟩

theorem covered : RetiredCovered st := by
  intro M c hM
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (show (M, c) = (({0, 0, 0} : Monomial 3), (2 : Fin 3)) from hM)
  exact ⟨Or.inr (Or.inr (Or.inl rfl)), {2}, 2,
    ⟨Or.inr (Or.inr (Or.inr rfl)), fun h => absurd (congrArg Prod.fst h) (by decide)⟩, rfl⟩

theorem not_I3 : ¬ I3 (Laws.plainAC 3) st := by
  intro h3
  obtain ⟨M', c', htg, hM', hc'⟩ := h3 {0, 0, 0} 2 rfl
  have hcount : M'.count 2 = 0 := by
    have : ∀ {A B : Monomial 3}, TransGen (st.RwL (Laws.plainAC 3)) A B →
        B.count 2 = A.count 2 := by
      intro A B h
      induction h with
      | single h => exact step_count h
      | tail _ h ih => rw [step_count h, ih]
    rw [this htg]
    decide
  have hlt : degLex ({0, 0, 0} : Monomial 3) M' := by
    have : ∀ {A B : Monomial 3}, TransGen (st.RwL (Laws.plainAC 3)) A B → degLex A B := by
      intro A B h
      induction h with
      | single h => exact RwL_degLex h
      | tail _ h ih => exact degLex_trans ih (RwL_degLex h)
    exact this htg
  have hc : c' = 2 := hc'
  subst hc
  rcases nodes_mem hM' with ⟨-, h⟩ | ⟨-, h⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact degLex_irrefl _ hlt
  · exact absurd hcount (by decide)

/-- **The pass and the cover do not give `I3` by themselves.** -/
theorem reactivate_fixed_not_I3 :
    ∃ st : State 3, st.reactivate (Laws.plainAC 3) = st ∧ RetiredCovered st ∧
      ¬ I3 (Laws.plainAC 3) st :=
  ⟨st, reactivate_fixed, covered, not_I3⟩

end ReactivateCE

end SemperProofs.CC
