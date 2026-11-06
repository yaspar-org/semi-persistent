import SemperProofs.CC.Lemmas
import SemperProofs.CC.Proofs.CriticalPairModulo
import SemperProofs.CC.Proofs.RunStabilizes
import SemperProofs.CC.Slot
import SemperProofs.CC.Assemble

/-!
# AC-congruence closure: final theorems

Collects the development under its final names. Everything here is a
one-line application of a theorem proved in `Lemmas.lean`,
`Proofs/CriticalPairModulo.lean`, `Proofs/RunStabilizes.lean` or `Slot.lean`.
-/

namespace SemperProofs.CC

open Relation

variable {n : ℕ}

/-- L16: along an infinite run of inferences the node set and the
partition are eventually constant. -/
theorem run_stabilizes {L : Laws n} (run : ℕ → State n)
    (hrun : ∀ i, Infer L (run i) (run (i + 1))) :
    ∃ k, ∀ i, k ≤ i → (run i).nodes = (run k).nodes ∧ (run i).find = (run k).find :=
  run_stabilizes' run hrun

/-- L11: confluence of clamp-normalized rewriting from the critical pairs
of the rules together with the law instances. -/
theorem confluent_modulo (L : Laws n) (R : Rules n)
    (hor : Oriented R)
    (hlaw : ∀ P Q, L.lawRel P Q → degLex P Q)
    (hnf : ∀ M N, ¬ Rw (plain n) L.axRules (L.clamp M) N)
    (hcp : ∀ r₁ r₂, r₁ ∈ R ∪ L.axRules → r₂ ∈ R ∪ L.axRules → r₁ ≠ r₂ →
      Overlap r₁.1 r₂.1 →
      Joinable (Rw (plain n) (R ∪ L.axRules))
        (criticalPair (plain n) r₁ r₂).1 (criticalPair (plain n) r₁ r₂).2) :
    Confluent (Rw L R) :=
  confluent_modulo' L R hor hlaw hnf hcp

/-- Soundness (sketch (c)): every state reachable from a state whose
classes are `=_E`-equal has `=_E`-equal classes. No bound, no I1, I4 or
I5 is needed. -/
theorem completion_sound {L : Laws n} {S : Set (Monomial n × Monomial n)}
    {st₀ st : State n} (hreach : Reachable L st₀ st) (h₀ : I2 L S st₀) : I2 L S st :=
  soundness hreach h₀

/-- Completeness at convergence (sketch (e)) for the fixed engine.

Two `=_E`-equal active nodes are in one class, provided:

* the run maintained the min-monomial slots with the refresh (`OpsStar`
  with `shrinkRefresh`), from a state where the slots were least (`h5₀`),
  and the completion state agrees with the slot state (`ha`); this
  discharges I5 through `reachable_I5`;
* every class's right-hand side is one of its own nodes (`I0`), is
  `clamp`-canonical (`hcanon`), and is a normal form of the rules (`hnf`);
* the last round changed nothing (`RoundFixed`);
* the rules are oriented (`hor`), every law instance shrinks in degree-lex
  (`hlaw`), `clamp` outputs are normal for the law instances (`hnf_ax`),
  and every critical pair of two distinct overlapping rules of
  `R ∪ Ax` is joinable (`hcp`); these give confluence through
  `confluent_modulo` and are properties of the laws and of the converged
  rule set;
* congruent nodes are in one class (`hcc`) and every `=_E`-equal pair is
  joinable (`hjoin`), which is the induction of L13 restated as a
  hypothesis on the converged state.

Kept for reference: `hjoin` is not satisfiable in general (see
`Assemble.lean`); the final theorem `completion_complete_at_convergence`
below replaces it by engine-level hypotheses. -/
theorem completion_complete_at_convergence_of_join {L : Laws n}
    {S : Set (Monomial n × Monomial n)} {st : State n}
    {ss₀ ss : SlotState n}
    (h5₀ : SlotState.I5 ss₀) (hrun : SlotState.OpsStar ss₀ ss) (ha : SlotState.Agrees st ss)
    (h0 : I0 st) (hcanon : ∀ c, L.clamp (st.rhs c) = st.rhs c) (hfix : RoundFixed L st)
    (hor : Oriented st.rules)
    (hlaw : ∀ P Q, L.lawRel P Q → degLex P Q)
    (hnf_ax : ∀ M N, ¬ Rw (plain n) L.axRules (L.clamp M) N)
    (hcp : ∀ r₁ r₂, r₁ ∈ st.rules ∪ L.axRules → r₂ ∈ st.rules ∪ L.axRules → r₁ ≠ r₂ →
      Overlap r₁.1 r₂.1 →
      Joinable (Rw (plain n) (st.rules ∪ L.axRules))
        (criticalPair (plain n) r₁ r₂).1 (criticalPair (plain n) r₁ r₂).2)
    (hnf : ∀ c P, ¬ Rw L st.rules (st.rhs (st.find c)) P)
    (hcc : ∀ P c d, (P, c) ∈ st.nodes → (P, d) ∈ st.nodes → st.find c = st.find d)
    (hjoin : ∀ M N, E L S M N → Joinable (Rw L st.rules) M N)
    {M N : Monomial n} {c d : Fin n} (hM : (M, c) ∈ st.active) (hN : (N, d) ∈ st.active)
    (hMN : E L S M N) : st.find c = st.find d :=
  SlotState.fix_sufficient h5₀ hrun ha h0 hcanon hfix
    (confluent_modulo L st.rules hor hlaw hnf_ax hcp) hnf hcc hjoin hM hN hMN

/-- Completeness at convergence (sketch (e)) for the fixed engine, from
engine-level hypotheses only; see `Assemble.lean` for the list. The
asserted equations enter as pairs of active nodes in one class (`hS`);
joinability of `=_E`-equal pairs, orientation of the rules and normality
of the right-hand sides are derived, not assumed. `I0Active` constrains only
the classes that hold an active node, and `hcc` only the active nodes, so a
class with no node of the operator (a leaf constant) is allowed; `Atoms.lean`
gives the form in which such a constant is the one-element monomial `{x}`. -/
theorem completion_complete_at_convergence {L : Laws n}
    {S : Set (Monomial n × Monomial n)} {st : State n}
    {ss₀ ss : SlotState n}
    (h5₀ : SlotState.I5 ss₀) (hrun : SlotState.OpsStar ss₀ ss) (ha : SlotState.Agrees st ss)
    (h0 : I0Active st) (hcanon : ∀ c, L.clamp (st.rhs c) = st.rhs c) (hfix : RoundFixed L st)
    (hlaw : ∀ P Q, L.lawRel P Q → degLex P Q)
    (hnf_ax : ∀ M N, ¬ Rw (plain n) L.axRules (L.clamp M) N)
    (hcp : ∀ r₁ r₂, r₁ ∈ st.rules ∪ L.axRules → r₂ ∈ st.rules ∪ L.axRules → r₁ ≠ r₂ →
      Overlap r₁.1 r₂.1 →
      Joinable (Rw (plain n) (st.rules ∪ L.axRules))
        (criticalPair (plain n) r₁ r₂).1 (criticalPair (plain n) r₁ r₂).2)
    (hcc : ∀ P c d, (P, c) ∈ st.active → (P, d) ∈ st.active → st.find c = st.find d)
    (hS : ∀ M N, (M, N) ∈ S →
      ∃ c d, (M, c) ∈ st.active ∧ (N, d) ∈ st.active ∧ st.find c = st.find d)
    (hcancel : L.cancellative → ∀ M N X,
      Joinable (Rw (plain n) (st.rules ∪ L.axRules)) (M + X) (N + X) →
      Joinable (Rw (plain n) (st.rules ∪ L.axRules)) M N)
    {M N : Monomial n} {c d : Fin n} (hM : (M, c) ∈ st.active) (hN : (N, d) ∈ st.active)
    (hMN : E L S M N) : st.find c = st.find d :=
  completion_complete_at_convergence' h5₀ hrun ha h0 hcanon hfix hlaw hnf_ax hcp hcc
    hS hcancel hM hN hMN

/-- The statement before 2026-11-06, as a corollary: `I0Active` over every
class of `Fin n` (`I0ActiveAll`) and congruence over every node, retired
ones included. -/
theorem completion_complete_at_convergence_of_all {L : Laws n}
    {S : Set (Monomial n × Monomial n)} {st : State n}
    {ss₀ ss : SlotState n}
    (h5₀ : SlotState.I5 ss₀) (hrun : SlotState.OpsStar ss₀ ss) (ha : SlotState.Agrees st ss)
    (h0 : I0ActiveAll st) (hcanon : ∀ c, L.clamp (st.rhs c) = st.rhs c)
    (hfix : RoundFixed L st)
    (hlaw : ∀ P Q, L.lawRel P Q → degLex P Q)
    (hnf_ax : ∀ M N, ¬ Rw (plain n) L.axRules (L.clamp M) N)
    (hcp : ∀ r₁ r₂, r₁ ∈ st.rules ∪ L.axRules → r₂ ∈ st.rules ∪ L.axRules → r₁ ≠ r₂ →
      Overlap r₁.1 r₂.1 →
      Joinable (Rw (plain n) (st.rules ∪ L.axRules))
        (criticalPair (plain n) r₁ r₂).1 (criticalPair (plain n) r₁ r₂).2)
    (hcc : ∀ P c d, (P, c) ∈ st.nodes → (P, d) ∈ st.nodes → st.find c = st.find d)
    (hS : ∀ M N, (M, N) ∈ S →
      ∃ c d, (M, c) ∈ st.active ∧ (N, d) ∈ st.active ∧ st.find c = st.find d)
    (hcancel : L.cancellative → ∀ M N X,
      Joinable (Rw (plain n) (st.rules ∪ L.axRules)) (M + X) (N + X) →
      Joinable (Rw (plain n) (st.rules ∪ L.axRules)) M N)
    {M N : Monomial n} {c d : Fin n} (hM : (M, c) ∈ st.active) (hN : (N, d) ∈ st.active)
    (hMN : E L S M N) : st.find c = st.find d :=
  completion_complete_at_convergence h5₀ hrun ha (I0Active_of_all h0) hcanon hfix hlaw hnf_ax
    hcp (fun P c d hc hd => hcc P c d hc.1 hd.1) hS hcancel hM hN hMN

end SemperProofs.CC
