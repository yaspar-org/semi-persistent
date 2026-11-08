import SemperProofs.Fidelity.Recanon

/-!
# Saturation with normalized right-hand sides and `:subsume`

The store rounds of `Fidelity/Subsume.lean` with `DenN` in place of `Den`:
the hypotheses on what the actions build are now ones the engine's `add`
meets (an n-ary term is present up to splicing, unit drop, nilpotent
clamp, inverse cancellation and degenerate arity). `fired_after_actions_N`
is `fired_after_actions` restated; `saturation_complete_N` is the fixpoint
theorem with neither `subsumed = ∅` nor literal right-hand sides.

`den_misses_single` is the reason: a one-element AC right-hand side, which
the engine evaluates to the element's class (`Normal::Single`,
`egraph.rs:1078`), has no `Den` derivation in a graph without a one-child
node, while it has a `DenN` one.
-/

namespace Semper.EMatch.Fidelity

open Semper.EMatch

/-- The consequence of one action, normalized right-hand sides. -/
def ActFiredN (G : Graph) (L : Sym → OpLaws) (σ : Binding) : Action → Prop
  | .insert t => ∃ c, DenN G L σ t c
  | .union a b => ∃ c, DenN G L σ a c ∧ DenN G L σ b c
  | .subsume _ => True

def FiredN (G : Graph) (L : Sym → OpLaws) (σ : Binding) (rule : Rule) : Prop :=
  ∀ act ∈ rule.actions, ActFiredN G L σ act

/-- `Fired` implies `FiredN`: the literal model is a special case. -/
theorem _root_.Semper.EMatch.Fired.toFiredN {G : Graph} {L : Sym → OpLaws} {σ : Binding} {rule : Rule}
    (h : Fired G σ rule) : FiredN G L σ rule := by
  intro act hact
  have := h act hact
  cases act with
  | insert t => obtain ⟨c, hc⟩ := this; exact ⟨c, hc.toDenN⟩
  | union a b => obtain ⟨c, ha, hb⟩ := this; exact ⟨c, ha.toDenN, hb.toDenN⟩
  | subsume _ => trivial

theorem firedN_persist {Sb Sa : Store} (h : StorePersist Sb Sa) {L : Sym → OpLaws}
    {σ : Binding} {rule : Rule} (hf : FiredN Sb.graph L σ rule) : FiredN Sa.graph L σ rule := by
  intro act hact
  have := hf act hact
  cases act with
  | insert t => obtain ⟨c, hc⟩ := this; exact ⟨_, hc.persist h⟩
  | union a b => obtain ⟨c, ha, hb⟩ := this; exact ⟨_, ha.persist h, hb.persist h⟩
  | subsume _ => trivial

/-- `firedN_persist` for a rule that builds no n-ary term, under normal-form
recanonicalization of the n-ary nodes (`StorePersistN`). -/
theorem firedN_persist_fixed {L : Sym → OpLaws} {Sb Sa : Store} (h : StorePersistN L Sb Sa)
    {σ : Binding} {rule : Rule} (hr : rule.buildsNary = false)
    (hf : FiredN Sb.graph L σ rule) : FiredN Sa.graph L σ rule := by
  have hr' : ∀ act ∈ rule.actions, act.hasNary = false := by
    simpa [Rule.buildsNary, List.any_eq_false] using hr
  intro act hact
  have hn := hr' act hact
  have := hf act hact
  cases act with
  | insert t =>
      obtain ⟨c, hc⟩ := this
      exact ⟨_, hc.persist_fixed h (by simpa [Action.hasNary] using hn)⟩
  | union a b =>
      obtain ⟨c, ha, hb⟩ := this
      have hab : a.hasNary = false ∧ b.hasNary = false := by simpa [Action.hasNary] using hn
      exact ⟨_, ha.persist_fixed h hab.1, hb.persist_fixed h hab.2⟩
  | subsume _ => trivial

/-- One round on stores, the actions building normal forms. -/
structure SActRoundN (L : Sym → OpLaws) where
  R : Round
  Sb : Store
  Sa : Store
  before_eq : R.before = Sb.index
  after_eq : R.after = Sa.index
  emitted : Rule → Binding → Prop
  /-- `Insert(t)`: `add` returns the class of `t`'s normal form. -/
  inserts : ∀ rule σ, emitted rule σ → ∀ t, Action.insert t ∈ rule.actions →
    ∃ c, DenN Sa.graph L σ t c
  unions : ∀ rule σ, emitted rule σ → ∀ a b, Action.union a b ∈ rule.actions →
    ∃ c₁ c₂, DenN Sa.graph L σ a c₁ ∧ DenN Sa.graph L σ b c₂ ∧ (c₁, c₂) ∈ R.unions
  subsumes : ∀ rule σ, emitted rule σ → ∀ x, Action.subsume x ∈ rule.actions →
    ∀ id, σ.node x = some id → Sa.flags.subsumed id = true
  unions_merged : ∀ u ∈ R.unions, Sa.find u.1 = Sa.find u.2

variable {L : Sym → OpLaws}

/-- `fired_after_actions` with normalized right-hand sides. -/
theorem fired_after_actions_N (A : SActRoundN L) (hidem : A.Sa.graph.FindIdem) {rule : Rule}
    {σ : Binding} (h : A.emitted rule σ) : FiredN A.Sa.graph L σ rule := by
  intro act hact
  cases act with
  | insert t => exact A.inserts rule σ h t hact
  | union a b =>
      obtain ⟨c₁, c₂, ha, hb, hu⟩ := A.unions rule σ h a b hact
      refine ⟨c₁, ha, ?_⟩
      have : c₁ = c₂ := by
        rw [← ha.find_eq hidem, ← hb.find_eq hidem]; exact A.unions_merged _ hu
      exact this ▸ hb
  | subsume _ => trivial

/-- The invariant with latency, guarded as `InvLagL`: a rule that builds an
n-ary term is fired when the round's rebuild persisted every stored node
literally. -/
def InvLagN (A : SActRoundN L) (rules : List Rule) : Prop :=
  ∀ rule ∈ rules, (rule.buildsNary = true → Literal A.Sb A.Sa) →
    ∀ σ, Matches A.Sb.index rule.atoms σ → FiredN A.Sa.graph L σ rule

def EmitsAllN (A : SActRoundN L) (rules : List Rule) : Prop :=
  ∀ rule ∈ rules, ∀ σ ∈ rule.matcher.naive A.R.before, A.emitted rule σ

def EmitsRoundN (naive : Rule → Bool) (prev : Round) (A : SActRoundN L) (rules : List Rule) :
    Prop :=
  ∀ rule ∈ rules,
    (naive rule = true → ∀ σ ∈ rule.matcher.naive A.R.before, A.emitted rule σ) ∧
    (naive rule = false → ∀ (k : Nat) (ak : RAtom), rule.atoms[k]? = some (.scan ak) →
      ∀ σ ∈ rule.matcher.variant A.R.before prev.isNew k, A.emitted rule σ)

theorem invLagN_zero {sig : Sym → Kind} {rules : List Rule} (A : SActRoundN L) (hwf : A.R.WF)
    (hatoms : RulesWF sig A.R.before rules) (hmatch : MatchersOK rules) (hemit : EmitsAllN A rules) :
    InvLagN A rules := by
  intro rule hr _ σ hm
  have hidem : A.Sa.graph.FindIdem := by
    have := hwf.find_idem; rw [A.after_eq] at this; exact this
  rw [← A.before_eq] at hm
  exact fired_after_actions_N A hidem
    (hemit rule hr σ ((MatcherOK.naive_iff (hmatch rule hr) (hatoms rule hr) σ).2 hm))

/-- `inv_step_store` with normalized right-hand sides and normal-form
recanonicalization: an old instance of a rule that builds an n-ary term is
transported when the round persisted every node literally, and otherwise
re-emitted by the naive run the routing forces (`route`, `resp = true`). -/
theorem inv_step_N {sig : Sym → Kind} {naive : Rule → Bool} {rules : List Rule}
    {prev A : SActRoundN L} (hlink : A.Sb = prev.Sa)
    (hprev : prev.R.WF) (htr : prev.R.tracking = true) (hAp : StorePersistN L A.Sb A.Sa)
    (hatoms₀ : RulesWF sig prev.R.before rules) (hatoms₁ : RulesWF sig prev.R.after rules)
    (hmatch : MatchersOK rules) {resp : Bool} (hresp : ¬ Literal prev.Sb prev.Sa → resp = true)
    (hemit : EmitsRoundN (route naive resp) prev.R A rules)
    (hinv : InvLagN prev rules) : InvLagN A rules := by
  intro rule hr hlit σ hm
  have hRlink : A.R.before = prev.R.after := by rw [A.before_eq, prev.after_eq, hlink]
  have hm' : Matches prev.R.after rule.atoms σ := by rw [prev.after_eq, ← hlink]; exact hm
  have hnew : σ ∈ rule.matcher.naive prev.R.after :=
    (MatcherOK.naive_iff (hmatch rule hr) (hatoms₁ rule hr) σ).2 hm'
  obtain ⟨h1, h2⟩ := hemit rule hr
  rw [hRlink] at h1 h2
  have hroute : route naive resp rule = true → FiredN A.Sa.graph L σ rule :=
    fun hn => fired_after_actions_N A hAp.after_idem (h1 hn σ hnew)
  by_cases hold : Matches prev.R.before rule.atoms σ
  · rw [prev.before_eq] at hold
    cases hb : rule.buildsNary with
    | false =>
        have hf := hinv rule hr (fun h => by rw [hb] at h; exact absurd h (by decide)) σ hold
        rw [← hlink] at hf
        exact firedN_persist_fixed hAp hb hf
    | true =>
        have hlitA := hlit hb
        by_cases hpp : Literal prev.Sb prev.Sa
        · have hf := hinv rule hr (fun _ => hpp) σ hold
          rw [← hlink] at hf
          exact firedN_persist (hAp.toStorePersist hlitA) hf
        · exact hroute (by simp [route, hresp hpp, hb])
  · cases hn : route naive resp rule with
    | true => exact hroute hn
    | false =>
        apply fired_after_actions_N A hAp.after_idem
        have hold' : σ ∉ rule.matcher.naive prev.R.before := fun h =>
          hold ((MatcherOK.naive_iff (hmatch rule hr) (hatoms₀ rule hr) σ).1 h)
        obtain ⟨k, ak, hk, hv⟩ :=
          MatcherOK.round_complete (hmatch rule hr) hprev htr (hatoms₀ rule hr) (hatoms₁ rule hr) hnew hold'
        exact h2 hn k ak hk σ hv

/-- A chain of store rounds, routed as `SChain`: after a round whose rebuild
did not persist every node literally, the rules that build an n-ary term
are matched in full (`route`, `resp = true`). -/
def SChainN (naive : Rule → Bool) (rules : List Rule) : SActRoundN L → List (SActRoundN L) → Prop
  | _, [] => True
  | prev, A :: As => A.Sb = prev.Sa ∧
      (∃ resp : Bool, (¬ Literal prev.Sb prev.Sa → resp = true) ∧
        EmitsRoundN (route naive resp) prev.R A rules) ∧
      SChainN naive rules A As

/-- The per-round hypotheses: the matcher's round facts, tracking on, the
store's persistence as the laws recanonicalize it (`StorePersistN`), and
well-formed atoms. -/
structure RoundOKN (sig : Sym → Kind) (rules : List Rule) (A : SActRoundN L) : Prop where
  wf : A.R.WF
  tracking : A.R.tracking = true
  store : StorePersistN L A.Sb A.Sa
  atoms : RulesWF sig A.R.after rules

theorem invLag_chain_N {sig : Sym → Kind} {naive : Rule → Bool} {rules : List Rule}
    (hmatch : MatchersOK rules) : ∀ (A₀ : SActRoundN L) (As : List (SActRoundN L)),
    RulesWF sig A₀.R.before rules → (∀ A ∈ A₀ :: As, RoundOKN sig rules A) →
    EmitsAllN A₀ rules → SChainN naive rules A₀ As → ∀ A ∈ A₀ :: As, InvLagN A rules := by
  intro A₀ As h₀ hok hemit₀ hchain
  have main : ∀ (B : SActRoundN L) (Bs : List (SActRoundN L)),
      RulesWF sig B.R.before rules → (∀ A ∈ B :: Bs, RoundOKN sig rules A) →
      InvLagN B rules → SChainN naive rules B Bs → ∀ A ∈ Bs, InvLagN A rules := by
    intro B Bs
    induction Bs generalizing B with
    | nil => intro _ _ _ _ A hA; simp at hA
    | cons A As ih =>
        intro h₀ hok hinv hchain A' hA'
        obtain ⟨hlink, ⟨resp, hresp, hemit⟩, hchain'⟩ := hchain
        have hokB := hok B (by simp)
        have hokA := hok A (by simp)
        have hinvA : InvLagN A rules :=
          inv_step_N hlink hokB.wf hokB.tracking hokA.store h₀ hokB.atoms hmatch hresp hemit hinv
        have hRlink : A.R.before = B.R.after := by rw [A.before_eq, B.after_eq, hlink]
        rcases List.mem_cons.1 hA' with rfl | hA'
        · exact hinvA
        · exact ih A (by rw [hRlink]; exact hokB.atoms) (fun C hC => hok C (by simp [hC])) hinvA
            hchain' A' hA'
  have hinv₀ := invLagN_zero A₀ (hok A₀ (by simp)).wf h₀ hmatch hemit₀
  intro A hA
  rcases List.mem_cons.1 hA with rfl | hA
  · exact hinv₀
  · exact main A₀ As h₀ hok hinv₀ hchain A hA

/-- Every match on the index of `S` is fired, as normal forms, in its store. -/
def InvN (S : Store) (L : Sym → OpLaws) (rules : List Rule) : Prop :=
  ∀ rule ∈ rules, ∀ σ, Matches S.index rule.atoms σ → FiredN S.graph L σ rule

def SActRoundN.Unchanged (A : SActRoundN L) : Prop :=
  (∀ p, p ∈ A.Sa.nodes ↔ p ∈ A.Sb.nodes) ∧ (∀ id, A.Sa.find id = A.Sb.find id) ∧
    ∀ id, A.Sa.skip id = A.Sb.skip id

/-- `saturation_complete_N`: at a round that changed nothing, every match
on the index the loop returns is fired, its right-hand sides present as
normal forms; `:subsume` rules allowed. -/
theorem saturation_complete_N {sig : Sym → Kind} {naive : Rule → Bool} {rules : List Rule}
    (A₀ : SActRoundN L) (As : List (SActRoundN L)) (hmatch : MatchersOK rules)
    (h₀ : RulesWF sig A₀.R.before rules) (hok : ∀ A ∈ A₀ :: As, RoundOKN sig rules A)
    (hemit₀ : EmitsAllN A₀ rules) (hchain : SChainN naive rules A₀ As)
    {A : SActRoundN L} (hA : A ∈ A₀ :: As) (hfix : A.Unchanged) : InvN A.Sa L rules := by
  have hinv := invLag_chain_N hmatch A₀ As h₀ hok hemit₀ hchain A hA
  obtain ⟨hn, hf, hs⟩ := hfix
  have hlit : Literal A.Sb A.Sa := literal_of_unchanged (hok A hA).store.children_canon hn
  have hfeq : A.Sa.find = A.Sb.find := funext hf
  have hin : ∀ p, p ∈ A.Sa.index.nodes ↔ p ∈ A.Sb.index.nodes := by
    intro p; simp only [Store.mem_index, hn, hs]
  intro rule hr σ hm
  exact hinv rule hr (fun _ => hlit) σ (matches_congr hin hfeq hm)

/-! ## Why: the literal model misses a degenerate arity -/

/-- The graph with one leaf node `c = g()`. -/
def leafGraph (g : Sym) (c : C) : Graph := ⟨[(c, ⟨g, .tuple []⟩)], id⟩

/-- The binding `0 ↦ c`. -/
def bindZero (c : C) : Binding := { Binding.empty with cls := fun x => if x = 0 then some c else none }

/-- A one-element AC right-hand side `f{x}` with `x ↦ c`: the engine
returns `c`'s class (`Normal::Single`); `DenN` has that value, `Den` has
no value at all in a graph whose only node is the leaf. -/
theorem den_misses_single (f g : Sym) (c : C) (hfg : f ≠ g) :
    DenN (leafGraph g c) (fun _ => ⟨none, none, none⟩) (bindZero c)
        (.ac f [(.var 0, .exact 1)] none) c ∧
      ∀ c', ¬ Den (leafGraph g c) (bindZero c) (.ac f [(.var 0, .exact 1)] none) c' := by
  constructor
  · refine DenN.ac (cks := [(c, 1)]) (m₀ := 0) (m' := {c}) rfl ?_ ?_ ?_ ?_ ?_
    · simp [RMultOk]
    · intro ek hek _
      simp at hek; subst hek
      exact DenN.var (G := leafGraph g c) (x := 0) (c := c) (by simp [bindZero])
    · simp [MsetRestVal]
    · simp only [acChildren, one_smul, Multiset.map_zero, add_zero]
      exact Relation.ReflTransGen.refl
    · exact Or.inr (Or.inl ⟨c, rfl, rfl⟩)
  · intro c' hd
    cases hd with
    | ac _ _ _ _ hmem =>
        simp [leafGraph, hfg] at hmem

end Semper.EMatch.Fidelity
