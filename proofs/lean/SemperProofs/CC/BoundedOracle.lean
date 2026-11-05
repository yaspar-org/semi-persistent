import SemperProofs.CC.Laws.Combined

/-!
# A bounded oracle for `E`, and its soundness

The conformance generator of the completion side (`Conform/CC/`) decides
`=_E` approximately: it enumerates every monomial of total count at most a
bound `B`, gives each an index, and runs a union-find over the indices to a
fixpoint. This file holds the executable core of that union-find and proves
that every pair it identifies is `=_E`-equal (`run_sound`); the generator
instantiates it, so a `check-eq` it emits is a consequence of the theory and
a failing one is an incompleteness of the engine.

The core is generic in the encoding. A `Spec` gives the number of indices,
a partial table `add i x` (the index of monomial `i` plus summand `x`, when
it stays within the bound), the base pairs (asserted equations and law
instances), whether the operator is cancellative, and a candidate
generator. Soundness assumes an interpretation `I` of indices as monomials
with `I (add i x) = I i + A x` and every base pair `=_E`-equal; it does not
depend on the candidate generator, because every candidate is re-validated
against the current partition (`pairOf`) before it is united.

* `unite` is union by relabeling: the larger of the two representatives is
  replaced by the smaller one in every entry.
* A pass collects the valid candidates against a snapshot of the partition
  and unites them; `close` iterates passes until one changes nothing.
* A congruence candidate `(i, i', x)` with `i ~ i'` unites `add i x` with
  `add i' x` (`E.congr` with `X := A x`); a cancellation candidate
  `(i, i', x)` with `add i x ~ add i' x` unites `i` with `i'` (`E.cancel`).
  Single summands suffice: congruence and cancellation by `X` are iterated
  single steps through monomials no larger than the end points.

The base law pairs are the one-step generators of the laws (`{u} → ∅`,
`aᵏ → ∅`, `{x, inv x} → ∅`, `{a, a} → {a}`). `poolLaws G` is the law set
whose instances are a rule set `G`; for a normal-form law set `N` it is
`N.genLaws`, so by `NFLaw.E_iff` soundness transfers to `N.toLaws`
(`run_sound_nf`), e.g. to `Laws.combined` under `InvUnitFree`.
-/

namespace SemperProofs.CC.Bounded

open SemperProofs.CC

/-! ## Union-find by relabeling -/

/-- The representative of index `i`; an index out of range is its own. -/
def find (rep : Array Nat) (i : Nat) : Nat :=
  if h : i < rep.size then rep[i] else i

/-- Relabel `hi` to `lo`. -/
def relabel (lo hi r : Nat) : Nat := if r = hi then lo else r

/-- Unite the classes of `a` and `b`; the smaller representative survives. -/
def unite (rep : Array Nat) (a b : Nat) : Array Nat :=
  if a < rep.size ∧ b < rep.size then
    rep.map (relabel (min (find rep a) (find rep b)) (max (find rep a) (find rep b)))
  else rep

/-- Unite every pair of a list, in order. -/
def uniteAll (rep : Array Nat) (ps : List (Nat × Nat)) : Array Nat :=
  ps.foldl (fun r p => unite r p.1 p.2) rep

theorem size_unite (rep : Array Nat) (a b : Nat) : (unite rep a b).size = rep.size := by
  unfold unite; split <;> simp

theorem size_uniteAll (rep : Array Nat) (ps : List (Nat × Nat)) :
    (uniteAll rep ps).size = rep.size := by
  induction ps generalizing rep with
  | nil => rfl
  | cons p ps ih => simp only [uniteAll, List.foldl_cons] at ih ⊢; rw [ih, size_unite]

/-- The partition invariant: two indices with one representative are related. -/
def Inv (R : Monomial n → Monomial n → Prop) (I : Nat → Monomial n) (rep : Array Nat) : Prop :=
  ∀ i j, i < rep.size → j < rep.size → find rep i = find rep j → R (I i) (I j)

theorem find_unite {rep : Array Nat} {a b i : Nat} (ha : a < rep.size) (hb : b < rep.size)
    (hi : i < rep.size) :
    find (unite rep a b) i =
      relabel (min (find rep a) (find rep b)) (max (find rep a) (find rep b)) (find rep i) := by
  simp only [find, hi, dite_true, unite, ha, hb, and_self, ite_true, Array.getElem_map, Array.size_map]

theorem relabel_eq {lo hi x y : Nat} (hl : lo = min a b) (hh : hi = max a b)
    (h : relabel lo hi x = relabel lo hi y) :
    x = y ∨ ((x = a ∨ x = b) ∧ (y = a ∨ y = b)) := by
  unfold relabel at h
  split_ifs at h <;> omega

theorem unite_inv {R : Monomial n → Monomial n → Prop} (hR : Equivalence R)
    {I : Nat → Monomial n} {rep : Array Nat} (h : Inv R I rep) {a b : Nat}
    (hab : R (I a) (I b)) : Inv R I (unite rep a b) := by
  by_cases hin : a < rep.size ∧ b < rep.size
  swap
  · simp only [unite, hin, ite_false]; exact h
  obtain ⟨ha, hb⟩ := hin
  intro i j hi hj he
  rw [size_unite] at hi hj
  rw [find_unite ha hb hi, find_unite ha hb hj] at he
  rcases relabel_eq rfl rfl he with e | ⟨ei, ej⟩
  · exact h i j hi hj e
  · -- each of `i`, `j` is related to `a`
    have toA : ∀ k, k < rep.size → (find rep k = find rep a ∨ find rep k = find rep b) →
        R (I k) (I a) := by
      intro k hk hk'
      rcases hk' with e | e
      · exact h k a hk ha e
      · exact hR.trans (h k b hk hb e) (hR.symm hab)
    exact hR.trans (toA i hi ei) (hR.symm (toA j hj ej))

theorem uniteAll_inv {R : Monomial n → Monomial n → Prop} (hR : Equivalence R)
    {I : Nat → Monomial n} {rep : Array Nat} (h : Inv R I rep) {ps : List (Nat × Nat)}
    (hps : ∀ p ∈ ps, R (I p.1) (I p.2)) : Inv R I (uniteAll rep ps) := by
  induction ps generalizing rep with
  | nil => exact h
  | cons p ps ih =>
    simp only [uniteAll, List.foldl_cons]
    exact ih (unite_inv hR h (hps p (List.mem_cons_self ..)))
      (fun q hq => hps q (List.mem_cons_of_mem _ hq))

theorem range_inv {R : Monomial n → Monomial n → Prop} (hR : Equivalence R)
    (I : Nat → Monomial n) (m : Nat) : Inv R I (Array.range m) := by
  intro i j hi hj he
  simp only [find, hi, hj, dite_true, Array.getElem_range] at he
  subst he; exact hR.refl _

/-! ## The closure -/

/-- A candidate union: a base pair, single-summand congruence, or cancellation. -/
inductive Cand where
  | congr (i i' x : Nat)
  | cancel (i i' x : Nat)
  deriving Repr

/-- The encoding of a bounded monomial universe. -/
structure Spec where
  /-- Number of indices. -/
  size : Nat
  /-- `add i x`: the index of monomial `i` plus summand `x`, if within the bound. -/
  add : Nat → Nat → Option Nat
  /-- Asserted equations and law instances. -/
  base : List (Nat × Nat)
  /-- Whether the operator is cancellative. -/
  cancel : Bool
  /-- The candidates of a pass (any heuristic: they are re-validated). -/
  cands : Array Nat → List Cand
  /-- Bound on the number of passes. -/
  fuel : Nat

/-- The pair a candidate unites, if it is valid against the partition `rep`. -/
def pairOf (T : Spec) (rep : Array Nat) : Cand → Option (Nat × Nat)
  | .congr i i' x =>
    if i < rep.size ∧ i' < rep.size ∧ find rep i = find rep i' then
      match T.add i x, T.add i' x with
      | some j, some j' => some (j, j')
      | _, _ => none
    else none
  | .cancel i i' x =>
    if T.cancel = true then
      match T.add i x, T.add i' x with
      | some j, some j' =>
        if j < rep.size ∧ j' < rep.size ∧ find rep j = find rep j' then some (i, i') else none
      | _, _ => none
    else none

/-- One pass: unite every valid candidate of the snapshot `rep`. -/
def step (T : Spec) (rep : Array Nat) : Array Nat :=
  uniteAll rep ((T.cands rep).filterMap (pairOf T rep))

/-- Passes until one changes nothing (or the fuel runs out). -/
def close (T : Spec) : Nat → Array Nat → Array Nat
  | 0, rep => rep
  | f + 1, rep =>
    let rep' := step T rep
    if rep' = rep then rep else close T f rep'

/-- The oracle: base pairs, then passes to a fixpoint. -/
def run (T : Spec) : Array Nat :=
  close T T.fuel (uniteAll (Array.range T.size) T.base)

theorem size_close (T : Spec) (f : Nat) (rep : Array Nat) : (close T f rep).size = rep.size := by
  induction f generalizing rep with
  | zero => rfl
  | succ f ih =>
    simp only [close]
    split
    · rfl
    · rw [ih, step, size_uniteAll]

theorem size_run (T : Spec) : (run T).size = T.size := by
  rw [run, size_close, size_uniteAll, Array.size_range]

/-! ## Soundness -/

section Sound

variable {n : ℕ} (L : Laws n) (S : Set (Monomial n × Monomial n))

theorem E_equivalence : Equivalence (E L S) := ⟨E.refl, E.symm, E.trans⟩

variable {L S} {T : Spec} {I : Nat → Monomial n} {A : Nat → Monomial n}

theorem pairOf_sound (hadd : ∀ i x j, T.add i x = some j → I j = I i + A x)
    (hcan : T.cancel = true → L.cancellative) {rep : Array Nat} (h : Inv (E L S) I rep)
    {c : Cand} {p : Nat × Nat} (hp : pairOf T rep c = some p) : E L S (I p.1) (I p.2) := by
  cases c with
  | congr i i' x =>
    simp only [pairOf] at hp
    split_ifs at hp with hc
    obtain ⟨hi, hi', he⟩ := hc
    split at hp
    · rename_i j j' hj hj'
      cases hp
      rw [hadd i x j hj, hadd i' x j' hj']
      exact E.congr _ (h i i' hi hi' he)
    · cases hp
  | cancel i i' x =>
    simp only [pairOf] at hp
    split_ifs at hp with hc
    split at hp
    · rename_i j j' hj hj'
      split_ifs at hp with hc'
      cases hp
      obtain ⟨hjs, hjs', he⟩ := hc'
      have := h j j' hjs hjs' he
      rw [hadd i x j hj, hadd i' x j' hj'] at this
      exact E.cancel (hcan hc) this
    · cases hp

theorem step_inv (hadd : ∀ i x j, T.add i x = some j → I j = I i + A x)
    (hcan : T.cancel = true → L.cancellative) {rep : Array Nat} (h : Inv (E L S) I rep) :
    Inv (E L S) I (step T rep) := by
  apply uniteAll_inv (E_equivalence L S) h
  intro p hp
  obtain ⟨c, _, hc⟩ := List.mem_filterMap.mp hp
  exact pairOf_sound hadd hcan h hc

theorem close_inv (hadd : ∀ i x j, T.add i x = some j → I j = I i + A x)
    (hcan : T.cancel = true → L.cancellative) (f : Nat) {rep : Array Nat}
    (h : Inv (E L S) I rep) : Inv (E L S) I (close T f rep) := by
  induction f generalizing rep with
  | zero => exact h
  | succ f ih =>
    simp only [close]
    split
    · exact h
    · exact ih (step_inv hadd hcan h)

/-- **Soundness of the bounded oracle.** Every pair of indices the oracle
puts in one class is `=_E`-equal under any interpretation that respects
the `add` table, the base pairs and cancellativity. -/
theorem run_sound (hadd : ∀ i x j, T.add i x = some j → I j = I i + A x)
    (hbase : ∀ p ∈ T.base, E L S (I p.1) (I p.2))
    (hcan : T.cancel = true → L.cancellative) :
    ∀ i j, i < T.size → j < T.size → find (run T) i = find (run T) j → E L S (I i) (I j) := by
  intro i j hi hj he
  have h0 : Inv (E L S) I (uniteAll (Array.range T.size) T.base) :=
    uniteAll_inv (E_equivalence L S) (range_inv (E_equivalence L S) I _) hbase
  have := close_inv hadd hcan T.fuel h0
  rw [← size_run T] at hi hj
  exact this i j hi hj he

end Sound

/-! ## The law instances as base pairs -/

section Laws

variable {n : ℕ}

/-- The law set whose instances are the rules `G` (no clamp). -/
def poolLaws (G : Rules n) (cancel : Prop) : Laws n where
  lawRel M P := (M, P) ∈ G
  clamp := id
  clamp_le _ := le_rfl
  clamp_law _ := Or.inl rfl
  cancellative := cancel

/-- A generator instance is an equation of the pooled theory. -/
theorem E_poolLaws_of_mem {G : Rules n} {cancel : Prop} {S : Set (Monomial n × Monomial n)}
    {M P : Monomial n} (h : (M, P) ∈ G) : E (poolLaws G cancel) S M P :=
  E.law h

/-- The one-step generators the oracle uses: identity, nilpotent, inverse, idempotent. -/
def oracleGen (u : Option (Fin n)) (k : Option ℕ) (inv : Fin n → Option (Fin n)) (idem : Bool) :
    Rules n :=
  {r | (∃ v, u = some v ∧ r = (({v} : Monomial n), 0)) ∨
       (∃ m a, k = some m ∧ r = (Multiset.replicate m a, 0)) ∨
       r ∈ invGen inv ∨
       (idem = true ∧ ∃ a, r = (Multiset.replicate 2 a, ({a} : Monomial n)))}

/-- For a normal-form law set, the pooled theory of its generators is its
generator theory. -/
theorem genLaws_eq (N : NFLaw n) : N.genLaws = poolLaws N.gen N.cancellative := rfl

/-- **Soundness for a normal-form law set.** If the base pairs are equations
of the theory generated by `N`'s one-step instances, every pair the oracle
identifies is `=_E`-equal under `N.toLaws` (e.g. `Laws.combined`). -/
theorem run_sound_nf (N : NFLaw n) {S : Set (Monomial n × Monomial n)} {T : Spec}
    {I A : Nat → Monomial n}
    (hadd : ∀ i x j, T.add i x = some j → I j = I i + A x)
    (hbase : ∀ p ∈ T.base, E (poolLaws N.gen N.cancellative) S (I p.1) (I p.2))
    (hcan : T.cancel = true → N.cancellative) :
    ∀ i j, i < T.size → j < T.size → find (run T) i = find (run T) j →
      E N.toLaws S (I i) (I j) := by
  intro i j hi hj he
  rw [NFLaw.E_iff, genLaws_eq]
  exact run_sound (L := poolLaws N.gen N.cancellative) hadd hbase hcan i j hi hj he

/-- The engine's combined law set's generators are oracle generators. -/
theorem combinedNF_gen_sub (u : Fin n) (k : ℕ) (hk : 2 ≤ k) (inv : Fin n → Option (Fin n))
    (cancel : Prop) (hu : InvUnitFree inv u) :
    (combinedNF u k hk inv cancel hu).gen ⊆ oracleGen (some u) (some k) inv false := by
  rw [combinedNF_gen]
  rintro r ((h | ⟨a, h⟩) | h)
  · exact Or.inl ⟨u, rfl, h⟩
  · exact Or.inr (Or.inl ⟨k, a, rfl, h⟩)
  · exact Or.inr (Or.inr (Or.inl h))

end Laws

end SemperProofs.CC.Bounded
