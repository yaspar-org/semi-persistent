import SemperProofs.CC.Laws.InvRulesMain

/-!
# `AxiomCP` from the per-law conditions

`AxiomCP L R` (`CC/Assemble.lean`) is the joinability of every critical
pair of `R ∪ Ax` that involves a law instance. The bundles `CompleteHyps`
and `CompleteAtoms` take it as a hypothesis for an abstract law set.
`CC/Laws/CriticalPairs.lean` reduces the whole critical-pair hypothesis
`HCP`, law by law, to the rule-rule pairs and conditions on the stored
left-hand sides. This file closes the loop for the law sets the model
names: `LawSpec` enumerates them, `LawSpec.Conds` is the conjunction of the
per-law conditions of `CriticalPairs.lean`, and `axiomCP_of_laws` derives
`AxiomCP` from a fixed round and those conditions.

The engine accepts, on an AC operator, the tag sets plain, `:identity`,
`:idempotent`, `:idempotent :identity`, `:identity :nilpotent k`,
`:identity :inverse` and `:identity :nilpotent k :inverse`
(`egraph/src/sortcheck.rs`: `:nilpotent` and `:inverse` require
`:identity`, `:idempotent` excludes `:nilpotent`, `:inverse` and
`:cancellative`). The model names plain, `identity`, `nilpotent`,
`idempotent`, `inverse` and `combined` (identity, nilpotent, inverse); the
tag set `:identity :nilpotent k` is `combined` with the empty inverse
(`LawSpec.identityNilpotent`). The tag sets `:idempotent :identity` and
`:identity :inverse` without `:nilpotent` have no `Laws` instance and are
outside `LawSpec`.

The inverse conditions (`InvMatching`, `InverseAxiomCP`,
`NilpotentInverseCP`) are what the fixpoints of the inverse rules R1 to R5
establish (`Laws/InvRulesMain.lean`); `LawSpec.conds_inverse_of_fixed` and
`LawSpec.conds_combined_of_fixed` assemble `Conds` from them.
-/

namespace SemperProofs.CC

open Relation

variable {n : ℕ}

/-- The whole critical-pair hypothesis gives its part involving a law
instance. -/
theorem AxiomCP.of_hcp {L : Laws n} {R : Rules n} (h : HCP L R) : AxiomCP L R :=
  fun r₁ r₂ h₁ h₂ _ hne hov => h r₁ r₂ h₁ h₂ hne hov

/-! ## The per-law conditions -/

/-- The identity law's condition on the rules: no left-hand side holds the
unit (what `nary_canon` stores). -/
def IdentityConds (u : Fin n) (R : Rules n) : Prop :=
  ∀ A B, (A, B) ∈ R → u ∉ A

/-- The nilpotent law's conditions on the rules: counts below `k` on every
left-hand side, and the engine's axiom pairs
`(B ⊎ {a : k − m}, A − {a : m})` joinable. -/
structure NilpotentConds (L : Laws n) (k : ℕ) (R : Rules n) : Prop where
  lhs : ∀ A B, (A, B) ∈ R → ∀ a, A.count a < k
  ax : ∀ A B, (A, B) ∈ R → ∀ a ∈ A,
    Joinable (Rw (plain n) (R ∪ L.axRules))
      (B + Multiset.replicate (k - A.count a) a) (A.filter (· ≠ a))

/-- The idempotent law's conditions on the rules: duplicate-free left-hand
sides, and the axiom pairs `(B ⊎ {a}, A)` joinable. -/
structure IdempotentConds (L : Laws n) (R : Rules n) : Prop where
  lhs : ∀ A B, (A, B) ∈ R → A.Nodup
  ax : ∀ A B, (A, B) ∈ R → ∀ a ∈ A, Joinable (Rw (plain n) (R ∪ L.axRules)) (B + {a}) A

/-- The inverse law's conditions on the rules: the inverse graph is a
matching, left-hand sides hold no cancellable pair, and the rule-inverse
pairs join. -/
structure InverseConds (L : Laws n) (inv : Fin n → Option (Fin n)) (R : Rules n) : Prop where
  matching : InvMatching inv
  lhs : ∀ A B, (A, B) ∈ R → InvNormal inv A
  ax : InverseAxiomCP L inv R

/-- The conditions of the composition identity, nilpotent, inverse: those
of the three laws, and the nilpotent-inverse law-law pairs joinable. -/
structure CombinedConds (L : Laws n) (u : Fin n) (k : ℕ) (inv : Fin n → Option (Fin n))
    (R : Rules n) : Prop where
  matching : InvMatching inv
  lhs_u : ∀ A B, (A, B) ∈ R → u ∉ A
  lhs_k : ∀ A B, (A, B) ∈ R → ∀ a, A.count a < k
  lhs_inv : ∀ A B, (A, B) ∈ R → InvNormal inv A
  ax_nil : ∀ A B, (A, B) ∈ R → ∀ a ∈ A,
    Joinable (Rw (plain n) (R ∪ L.axRules))
      (B + Multiset.replicate (k - A.count a) a) (A.filter (· ≠ a))
  ax_inv : InverseAxiomCP L inv R
  nilinv : NilpotentInverseCP (R ∪ L.axRules) k inv

/-! ## The law sets the model names -/

/-- The law sets the completeness theorems are instantiated for, with their
parameters. `cancel` is the cancellative flag, which the laws carry and
the critical pairs do not read. -/
inductive LawSpec (n : ℕ) where
  /-- Plain AC: no law instance. -/
  | plain
  /-- `:identity u`. -/
  | identity (u : Fin n) (cancel : Prop)
  /-- `:nilpotent k` alone (the model's law set; the engine pairs it with an identity). -/
  | nilpotent (k : ℕ) (hk : 2 ≤ k) (cancel : Prop)
  /-- `:idempotent`. -/
  | idempotent (cancel : Prop)
  /-- `:inverse` alone (the model's law set; the engine pairs it with an identity). -/
  | inverse (inv : Fin n → Option (Fin n)) (cancel : Prop)
  /-- `:identity u :nilpotent k :inverse`, the engine's composition, under
  `InvUnitFree`. -/
  | combined (u : Fin n) (k : ℕ) (hk : 2 ≤ k) (inv : Fin n → Option (Fin n)) (cancel : Prop)
      (hu : InvUnitFree inv u)

namespace LawSpec

/-- The `Laws` of a law set. -/
def laws : LawSpec n → Laws n
  | .plain => Laws.plainAC n
  | .identity u cancel => Laws.identity u cancel
  | .nilpotent k hk cancel => Laws.nilpotent k hk cancel
  | .idempotent cancel => Laws.idempotent cancel
  | .inverse inv cancel => Laws.inverse inv cancel
  | .combined u k hk inv cancel hu => Laws.combined u k hk inv cancel hu

/-- The per-law conditions on a rule set, as `CriticalPairs.lean` states
them. -/
def Conds : LawSpec n → Rules n → Prop
  | .plain, _ => True
  | .identity u _, R => IdentityConds u R
  | .nilpotent k hk cancel, R => NilpotentConds (Laws.nilpotent k hk cancel) k R
  | .idempotent cancel, R => IdempotentConds (Laws.idempotent cancel) R
  | .inverse inv cancel, R => InverseConds (Laws.inverse inv cancel) inv R
  | .combined u k hk inv cancel hu, R => CombinedConds (Laws.combined u k hk inv cancel hu) u k inv R

/-- `:identity u :nilpotent k`: `combined` with the empty inverse. -/
def identityNilpotent (u : Fin n) (k : ℕ) (hk : 2 ≤ k) (cancel : Prop) : LawSpec n :=
  .combined u k hk (fun _ => none) cancel (fun _ _ h => by cases h)

/-- `hlaw` for every law set: law instances decrease `degLex`. -/
theorem hlaw (sp : LawSpec n) : ∀ P Q, sp.laws.lawRel P Q → degLex P Q := by
  cases sp with
  | plain => exact fun _ _ h => h.elim
  | identity u cancel => exact identity_hlaw u cancel
  | nilpotent k hk cancel => exact nilpotent_hlaw
  | idempotent cancel => exact idempotent_hlaw
  | inverse inv cancel => exact inverse_hlaw inv cancel
  | combined u k hk inv cancel hu => exact combined_hlaw u k hk inv cancel hu

/-- `hnf_ax` for every law set: clamp outputs are law-normal. -/
theorem hnf_ax (sp : LawSpec n) :
    ∀ M N, ¬ Rw (SemperProofs.CC.plain n) sp.laws.axRules (sp.laws.clamp M) N := by
  cases sp with
  | plain => exact fun _ _ ⟨_, _, h, _, _⟩ => h.elim
  | identity u cancel => exact identity_hnf_ax u cancel
  | nilpotent k hk cancel => exact nilpotent_hnf_ax
  | idempotent cancel => exact idempotent_hnf_ax
  | inverse inv cancel => exact inverse_hnf_ax inv cancel
  | combined u k hk inv cancel hu => exact combined_hnf_ax u k hk inv cancel hu

/-- **The critical-pair hypothesis from the rule-rule pairs and the per-law
conditions**, for every law set the model names: one case per law, each
by the theorem of `CriticalPairs.lean`. Plain AC has no law instance, so
every pair is a rule-rule pair. -/
theorem hcp (sp : LawSpec n) {R : Rules n} (hor : Oriented R) (hRR : RuleRuleCP sp.laws R)
    (hc : sp.Conds R) : HCP sp.laws R := by
  cases sp with
  | plain =>
    intro r₁ r₂ h₁ h₂ hne hov
    rcases h₁ with h₁ | h₁
    · rcases h₂ with h₂ | h₂
      · exact hRR r₁ r₂ h₁ h₂ hne hov
      · exact (h₂ : False).elim
    · exact (h₁ : False).elim
  | identity u cancel => exact hcp_identity u cancel hor hRR hc
  | nilpotent k hk cancel => exact hcp_nilpotent k hk cancel hor hRR hc.lhs hc.ax
  | idempotent cancel => exact hcp_idempotent cancel hor hRR hc.lhs hc.ax
  | inverse inv cancel => exact hcp_inverse inv cancel hor hRR hc.matching hc.lhs hc.ax
  | combined u k hk inv cancel hu =>
    exact hcp_combined u k hk inv cancel hu hor hRR hc.matching hc.lhs_u hc.lhs_k hc.lhs_inv
      hc.ax_nil hc.ax_inv hc.nilinv

end LawSpec

/-- **`AxiomCP` from a fixed round and the per-law conditions.** For every
law set the model names, a `RoundFixed` state whose rules satisfy the
law's conditions joins every critical pair that involves a law instance:
the fixed round gives the rule-rule pairs (`ruleRuleCP_of_fixed`), the
per-law theorem gives the whole `HCP`, and `AxiomCP` is its law part. -/
theorem axiomCP_of_laws (sp : LawSpec n) {st : State n} (hfix : RoundFixed sp.laws st)
    (hc : sp.Conds st.rules) : AxiomCP sp.laws st.rules :=
  AxiomCP.of_hcp (sp.hcp (rules_oriented st) (ruleRuleCP_of_fixed hfix) hc)

/-! ## The inverse conditions from the fixpoints of R1 to R5 -/

namespace LawSpec

/-- The conditions of `inverse` from a fixed round under R1 and R3, the
`g`-nodes read by `inv`, the retirement discipline and cancellation-normal
left-hand sides (as `completion_complete_inverse_engine` takes them). -/
theorem conds_inverse_of_fixed (inv : Fin n → Option (Fin n)) (cancel : Prop) {st : State n}
    {gnodes : Set (Fin n × Fin n)}
    (hconv : Converged (Laws.inverse inv cancel) st) (h3 : I3 (Laws.inverse inv cancel) st)
    (hfixinv : RoundFixedInv (invWalk inv) inv st) (hinv : InvNodes st gnodes inv)
    (hlhs : ∀ A B, (A, B) ∈ st.rules → InvNormal inv A) :
    (LawSpec.inverse inv cancel).Conds st.rules where
  matching := invMatching_of_fixed hfixinv hinv
  lhs := hlhs
  ax := inverseAxiomCP_of_fixed hconv h3 hfixinv

/-- The conditions of `combined` from a fixed round under R1 to R5, the
`g`-nodes read by `inv`, the retirement discipline and canonical left-hand
sides (as `completion_complete_combined_engine` takes them). -/
theorem conds_combined_of_fixed (u : Fin n) (k : ℕ) (hk : 2 ≤ k) (inv : Fin n → Option (Fin n))
    (cancel : Prop) (hu : InvUnitFree inv u) {st : State n} {gnodes : Set (Fin n × Fin n)}
    (hconv : Converged (Laws.combined u k hk inv cancel hu) st)
    (h3 : I3 (Laws.combined u k hk inv cancel hu) st)
    (hfixinv : RoundFixedInv (combinedClamp u k inv) inv st)
    (hfixk : RoundFixedInvNil (combinedClamp u k inv) inv k st)
    (hinv : InvNodes st gnodes inv)
    (hlhs_u : ∀ A B, (A, B) ∈ st.rules → u ∉ A)
    (hlhs_k : ∀ A B, (A, B) ∈ st.rules → ∀ a, A.count a < k)
    (hlhs_inv : ∀ A B, (A, B) ∈ st.rules → InvNormal inv A)
    (hax_nil : ∀ A B, (A, B) ∈ st.rules → ∀ a ∈ A,
      Joinable (Rw (SemperProofs.CC.plain n)
          (st.rules ∪ (Laws.combined u k hk inv cancel hu).axRules))
        (B + Multiset.replicate (k - A.count a) a) (A.filter (· ≠ a))) :
    (LawSpec.combined u k hk inv cancel hu).Conds st.rules where
  matching := invMatching_of_fixed hfixinv hinv
  lhs_u := hlhs_u
  lhs_k := hlhs_k
  lhs_inv := hlhs_inv
  ax_nil := hax_nil
  ax_inv := inverseAxiomCP_of_fixed hconv h3 hfixinv
  nilinv :=
    nilpotentInverseCP_of_fixed hconv h3 (combined_hasInv u k hk inv cancel hu) hfixk
      (fun x hxx hk2 hodd =>
        combined_clamp_replicate_self u k hk cancel hu hxx (by omega) (by omega))

end LawSpec

end SemperProofs.CC
