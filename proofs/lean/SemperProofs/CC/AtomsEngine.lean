import SemperProofs.CC.Atoms
import SemperProofs.CC.Lattice
import SemperProofs.CC.Laws.InvRulesMain
import SemperProofs.CC.Laws.AxiomCP

/-!
# The engine-level completeness theorems with leaf constants

The theorems `completion_complete_cancellative_engine` (`Lattice.lean`),
`completion_complete_inverse_engine` and `completion_complete_combined_engine`
(`Laws/InvRulesMain.lean`), read on the completion view `st.withAtoms A`
of `Atoms.lean`. As in `completion_complete_atoms`, the fixed round is
`RoundFixedA` (the one-element collapse included), congruence `hcc` and
the retirement discipline `I3` are stated on the stored state, and every
other hypothesis on the view.

The inverse rules R1-R5 are stated on the one-element nodes `{x}` of the
classes a `g`-node touches (`InvNodes`, `RoundFixedInvNil.r4`). On the
view these are the implicit nodes of the atoms: `invNodes_withAtoms` gives
`InvNodes` of the view when every class a `g`-node touches is atomic, which
the engine guarantees (a child of a non-`f` node and a class holding one
are `atomic`), with no stored one-element node.

`CompleteAtoms.ofLaws` builds the bundle for a law set the model names
(`LawSpec`) from the per-law conditions on the view's rules in place of
`AxiomCP`, which `axiomCP_of_laws` derives.
-/

namespace SemperProofs.CC

open Relation

variable {n : ℕ}

/-- `I3` passes to the completion view: its retired nodes are stored
retired nodes, and its rules and nodes contain the stored ones. -/
theorem I3_withAtoms {L : Laws n} {st : State n} {A : Set (Fin n)} {u : Option (Fin n)} (h3 : I3 L st) :
    I3 L (st.withAtoms A u) := by
  intro M c hM
  obtain ⟨M', c', hMM', hM', hc'⟩ := h3 M c hM.1
  refine ⟨M', c', ?_, Or.inl hM', hc'⟩
  clear hM' hc'
  induction hMM' with
  | single h => exact TransGen.single (Rw_mono State.rules_withAtoms h)
  | tail _ h ih => exact ih.tail (Rw_mono State.rules_withAtoms h)

/-- `InvNodes` of the completion view from the stored `g`-nodes, when every
class a `g`-node touches is atomic: the one-element nodes the inverse rules
are stated on are the implicit nodes of those atoms. -/
theorem invNodes_withAtoms {st : State n} {A : Set (Fin n)} {u : Option (Fin n)} {gnodes : Set (Fin n × Fin n)}
    {inv : Fin n → Option (Fin n)}
    (hinv : ∀ x y, inv x = some y ↔ st.find x = x ∧ st.find y = y ∧
      ∃ x' y', (x', y') ∈ gnodes ∧ st.find x' = x ∧ st.find y' = y)
    (hidem : ∀ x, st.find (st.find x) = st.find x)
    (hA : ∀ x y, (x, y) ∈ gnodes → st.find x ∈ A ∧ st.find y ∈ A) :
    InvNodes (st.withAtoms A u) gnodes inv where
  inv_iff := hinv
  atom_child x y h := ⟨st.find x, Or.inr (Or.inl ⟨(hA x y h).1, rfl⟩), hidem x⟩
  atom_class x y h := ⟨st.find y, Or.inr (Or.inl ⟨(hA x y h).2, rfl⟩), hidem y⟩

/-- `completion_complete_cancellative_engine` with leaf constants. -/
theorem completion_complete_cancellative_engine_atoms {L : Laws n}
    {S : Set (Monomial n × Monomial n)} {st : State n} {A : Set (Fin n)} {u : Option (Fin n)}
    {ss₀ ss : SlotState n}
    (h5₀ : SlotState.I5 ss₀) (hrun : SlotState.OpsStar ss₀ ss)
    (ha : SlotState.Agrees (st.withAtoms A u) ss)
    (h0 : I0Active (st.withAtoms A u)) (hcanon : ∀ c, L.clamp (st.rhs c) = st.rhs c)
    (hfix : RoundFixedA L st A u)
    (hlaw : ∀ P Q, L.lawRel P Q → degLex P Q)
    (hnf_ax : ∀ M N, ¬ Rw (plain n) L.axRules (L.clamp M) N)
    (hcp : ∀ r₁ r₂, r₁ ∈ (st.withAtoms A u).rules ∪ L.axRules →
      r₂ ∈ (st.withAtoms A u).rules ∪ L.axRules → r₁ ≠ r₂ → Overlap r₁.1 r₂.1 →
      Joinable (Rw (plain n) ((st.withAtoms A u).rules ∪ L.axRules))
        (criticalPair (plain n) r₁ r₂).1 (criticalPair (plain n) r₁ r₂).2)
    (hcc : ∀ P c d, (P, c) ∈ st.active → (P, d) ∈ st.active → st.find c = st.find d)
    (hS : ∀ M N, (M, N) ∈ S → ∃ c d, (M, c) ∈ (st.withAtoms A u).active ∧
      (N, d) ∈ (st.withAtoms A u).active ∧ st.find c = st.find d)
    (hlat : L.cancellative → Lattice.LatticeClosed L (st.withAtoms A u))
    {M N : Monomial n} {c d : Fin n} (hM : (M, c) ∈ (st.withAtoms A u).active)
    (hN : (N, d) ∈ (st.withAtoms A u).active) (hMN : E L S M N) : st.find c = st.find d :=
  Lattice.completion_complete_cancellative_engine h5₀ hrun ha h0 hcanon hfix.roundFixed hlaw
    hnf_ax hcp (hfix.congr hcc) hS hlat hM hN hMN

/-- `completion_complete_inverse_engine` with leaf constants. -/
theorem completion_complete_inverse_engine_atoms (inv : Fin n → Option (Fin n)) (cancel : Prop)
    {S : Set (Monomial n × Monomial n)} {st : State n} {A : Set (Fin n)} {u : Option (Fin n)}
    {ss₀ ss : SlotState n} {gnodes : Set (Fin n × Fin n)}
    (h5₀ : SlotState.I5 ss₀) (hrun : SlotState.OpsStar ss₀ ss)
    (ha : SlotState.Agrees (st.withAtoms A u) ss)
    (h0 : I0Active (st.withAtoms A u))
    (hcanon : ∀ c, (Laws.inverse inv cancel).clamp (st.rhs c) = st.rhs c)
    (hfix : RoundFixedA (Laws.inverse inv cancel) st A u)
    (h3 : I3 (Laws.inverse inv cancel) st)
    (hfixinv : RoundFixedInv (invWalk inv) inv (st.withAtoms A u))
    (hinv : InvNodes (st.withAtoms A u) gnodes inv)
    (hlhs : ∀ A' B, (A', B) ∈ (st.withAtoms A u).rules → InvNormal inv A')
    (hcc : ∀ P c d, (P, c) ∈ st.active → (P, d) ∈ st.active → st.find c = st.find d)
    (hS : ∀ M N, (M, N) ∈ S → ∃ c d, (M, c) ∈ (st.withAtoms A u).active ∧
      (N, d) ∈ (st.withAtoms A u).active ∧ st.find c = st.find d)
    (hcancel : cancel → ∀ M N X,
      Joinable (Rw (plain n) ((st.withAtoms A u).rules ∪ (Laws.inverse inv cancel).axRules))
        (M + X) (N + X) →
      Joinable (Rw (plain n) ((st.withAtoms A u).rules ∪ (Laws.inverse inv cancel).axRules)) M N)
    {M N : Monomial n} {c d : Fin n} (hM : (M, c) ∈ (st.withAtoms A u).active)
    (hN : (N, d) ∈ (st.withAtoms A u).active) (hMN : E (Laws.inverse inv cancel) S M N) :
    st.find c = st.find d :=
  completion_complete_inverse_engine inv cancel h5₀ hrun ha h0 hcanon hfix.roundFixed
    (I3_withAtoms h3) hfixinv hinv hlhs (hfix.congr hcc) hS hcancel hM hN hMN

/-- `completion_complete_combined_engine` with leaf constants; the unit `u`
is the implicit node `(∅, u)` of the view. -/
theorem completion_complete_combined_engine_atoms (u : Fin n) (k : ℕ) (hk : 2 ≤ k)
    (inv : Fin n → Option (Fin n)) (cancel : Prop)
    {S : Set (Monomial n × Monomial n)} {st : State n} {A : Set (Fin n)}
    {ss₀ ss : SlotState n} {gnodes : Set (Fin n × Fin n)}
    (hurep : st.find u = u)
    (hfixu : RoundFixedInvUnit inv u (st.withAtoms A (some u)))
    (hinv : InvNodes (st.withAtoms A (some u)) gnodes inv)
    (hfixinv : RoundFixedInv (combinedClamp u k inv) inv (st.withAtoms A (some u)))
    (hfixk : RoundFixedInvNil (combinedClamp u k inv) inv k (st.withAtoms A (some u)))
    (h5₀ : SlotState.I5 ss₀) (hrun : SlotState.OpsStar ss₀ ss)
    (ha : SlotState.Agrees (st.withAtoms A (some u)) ss)
    (h0 : I0Active (st.withAtoms A (some u)))
    (hcanon : ∀ c, (Laws.combined u k hk inv cancel
      (invUnitFree_of_fixed hfixu hinv hurep)).clamp (st.rhs c) = st.rhs c)
    (hfix : RoundFixedA (Laws.combined u k hk inv cancel
      (invUnitFree_of_fixed hfixu hinv hurep)) st A (some u))
    (h3 : I3 (Laws.combined u k hk inv cancel (invUnitFree_of_fixed hfixu hinv hurep)) st)
    (hlhs_u : ∀ A' B, (A', B) ∈ (st.withAtoms A (some u)).rules → u ∉ A')
    (hlhs_k : ∀ A' B, (A', B) ∈ (st.withAtoms A (some u)).rules → ∀ a, A'.count a < k)
    (hlhs_inv : ∀ A' B, (A', B) ∈ (st.withAtoms A (some u)).rules → InvNormal inv A')
    (hax_nil : ∀ A' B, (A', B) ∈ (st.withAtoms A (some u)).rules → ∀ a ∈ A',
      Joinable (Rw (plain n) ((st.withAtoms A (some u)).rules ∪
          (Laws.combined u k hk inv cancel (invUnitFree_of_fixed hfixu hinv hurep)).axRules))
        (B + Multiset.replicate (k - A'.count a) a) (A'.filter (· ≠ a)))
    (hcc : ∀ P c d, (P, c) ∈ st.active → (P, d) ∈ st.active → st.find c = st.find d)
    (hS : ∀ M N, (M, N) ∈ S → ∃ c d, (M, c) ∈ (st.withAtoms A (some u)).active ∧
      (N, d) ∈ (st.withAtoms A (some u)).active ∧ st.find c = st.find d)
    (hcancel : (Laws.combined u k hk inv cancel
        (invUnitFree_of_fixed hfixu hinv hurep)).cancellative → ∀ M N X,
      Joinable (Rw (plain n) ((st.withAtoms A (some u)).rules ∪
          (Laws.combined u k hk inv cancel (invUnitFree_of_fixed hfixu hinv hurep)).axRules))
        (M + X) (N + X) →
      Joinable (Rw (plain n) ((st.withAtoms A (some u)).rules ∪
          (Laws.combined u k hk inv cancel (invUnitFree_of_fixed hfixu hinv hurep)).axRules))
        M N)
    {M N : Monomial n} {c d : Fin n} (hM : (M, c) ∈ (st.withAtoms A (some u)).active)
    (hN : (N, d) ∈ (st.withAtoms A (some u)).active)
    (hMN : E (Laws.combined u k hk inv cancel (invUnitFree_of_fixed hfixu hinv hurep)) S M N) :
    st.find c = st.find d :=
  completion_complete_combined_engine (st := st.withAtoms A (some u)) u k hk inv cancel hurep hfixu hinv hfixinv hfixk h5₀
    hrun ha h0 hcanon hfix.roundFixed (I3_withAtoms h3) hlhs_u hlhs_k hlhs_inv hax_nil
    (hfix.congr hcc) hS hcancel hM hN hMN

/-- **`CompleteAtoms` from the per-law conditions.** For a law set the model
names, the bundle is built from the engine-side hypotheses and the
conditions `LawSpec.Conds` on the view's rules; `hlaw` and `hnf_ax` are the
law's, and `hcp_ax` is `axiomCP_of_laws` at the fixed round of the view.
No hypothesis on the critical pairs that involve a law instance remains. -/
theorem CompleteAtoms.ofLaws (sp : LawSpec n) {S : Set (Monomial n × Monomial n)}
    {st : State n} {A : Set (Fin n)} {u : Option (Fin n)}
    (slots : ∃ ss₀ ss : SlotState n,
      SlotState.I5 ss₀ ∧ SlotState.OpsStar ss₀ ss ∧ SlotState.Agrees (st.withAtoms A u) ss)
    (h0 : I0Active (st.withAtoms A u)) (hcanon : ∀ c, sp.laws.clamp (st.rhs c) = st.rhs c)
    (hfix : RoundFixedA sp.laws st A u) (hc : sp.Conds (st.withAtoms A u).rules)
    (hcc : ∀ P c d, (P, c) ∈ st.active → (P, d) ∈ st.active → st.find c = st.find d)
    (hS : ∀ M N, (M, N) ∈ S → ∃ c d, (M, c) ∈ (st.withAtoms A u).active ∧
      (N, d) ∈ (st.withAtoms A u).active ∧ st.find c = st.find d)
    (hlat : sp.laws.cancellative → Lattice.LatticeClosed sp.laws (st.withAtoms A u)) :
    CompleteAtoms sp.laws S st A u where
  slots := slots
  h0 := h0
  hcanon := hcanon
  hfix := hfix
  hlaw := sp.hlaw
  hnf_ax := sp.hnf_ax
  hcp_ax := axiomCP_of_laws sp hfix.roundFixed hc
  hcc := hcc
  hS := hS
  hlat := hlat

end SemperProofs.CC
