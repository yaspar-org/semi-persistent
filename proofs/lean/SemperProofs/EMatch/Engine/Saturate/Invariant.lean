import SemperProofs.EMatch.Engine.Saturate.ActRound

/-!
# The saturation invariant and the fixpoint theorem (spec-actions §F)

`Inv G rules`: every match of every rule in `G` is fired in `G`. The
loop does not maintain it round by round: the matches of round `r` are
found on the snapshot `G_r` and their actions land in `G_{r+1}`. What it
maintains is the one-round-latency form `InvLag`: every match of the
snapshot a round matched on is fired in the snapshot after its actions.

* Round 0 runs every rule naive (`saturate.rs:917-942`): `invLag_zero`.
* Round `r ≥ 1` runs, per rule, the naive query on the frozen snapshot if
  `needs_naive_match` (`saturate.rs:582-616`) routes it there, else one
  variant per join atom on the delta of the round (`saturate.rs:946-981`).
  A match of `G_r` either matched `G_{r-1}` (fired in `G_r` by the previous
  `InvLag`, transported to `G_{r+1}` by `fired_transport'`) or is new, and
  `semi_naive_round_complete` says some variant of round `r` emits it
  (`delta_complete` for the tracked rules; `mem_runNaive_iff` for the rules
  routed naive): `inv_step`.
* `saturation_complete`: along a chain of rounds, at a round that changed
  nothing (`Round.Unchanged`: no node minted, no two classes merged, nothing
  subsumed, so the next snapshot is the same graph; this is where the loop
  stops, `saturate.rs:1018-1020`), `Inv` holds at that snapshot.

The routing is a parameter `naive : Rule → Bool`; the theorem covers both
branches. Tracking (`track_merge_members`) is required for the delta
(`delta_complete` needs it; `Rounds/Counter.lean` shows it is necessary).
-/

namespace Semper.EMatch

namespace Saturate

/-- Every match of every rule in `G` is fired in `G`. (In the namespace
`Saturate`: `Inv` is also the name of the scheduler's run invariant.) -/
def Inv (G : Graph) (rules : List Rule) : Prop :=
  ∀ rule ∈ rules, ∀ σ, Matches G rule.atoms σ → Fired G σ rule

/-- The invariant with one round of latency: every match of the snapshot
the round matched on is fired in the snapshot after its actions. -/
def InvLag (A : ActRound) (rules : List Rule) : Prop :=
  ∀ rule ∈ rules, ∀ σ, Matches A.R.before rule.atoms σ → Fired A.R.after σ rule

end Saturate

open Saturate

/-- Round 0: every rule runs naive on the frozen snapshot and every match
is applied (`saturate.rs:917-942`). -/
def EmitsAll (A : ActRound) (rules : List Rule) : Prop :=
  ∀ rule ∈ rules, ∀ σ ∈ runNaive A.R.before rule.plan, A.emitted rule σ

/-- Round `r ≥ 1`, after the transition `prev` (whose `after` is the
snapshot this round matches on): a rule routed naive has every naive
match applied (`saturate.rs:955-970`); a tracked rule has every match of
every variant applied, the variants reading the delta of `prev`
(`saturate.rs:971-981`). -/
def EmitsRound (naive : Rule → Bool) (prev : Round) (A : ActRound) (rules : List Rule) : Prop :=
  ∀ rule ∈ rules,
    (naive rule = true → ∀ σ ∈ runNaive A.R.before rule.plan, A.emitted rule σ) ∧
    (naive rule = false → ∀ (k : Nat) (ak : RAtom), rule.atoms[k]? = some (.scan ak) →
      ∀ σ ∈ runVariant A.R.before prev.isNew k rule.plan, A.emitted rule σ)

/-- The atoms of every rule are well formed on `G`. -/
def RulesWF (sig : Sym → Kind) (G : Graph) (rules : List Rule) : Prop :=
  ∀ rule ∈ rules, AtomsWF G sig rule.atoms

/-- Every rule's plan is a scheduled plan of its atoms. -/
def PlansOK (rules : List Rule) : Prop :=
  ∀ rule ∈ rules, SchedA rule.atoms ∅ ∅ rule.plan

/-- Round 0: `InvLag` holds outright. -/
theorem invLag_zero {sig : Sym → Kind} {rules : List Rule} (A : ActRound) (hwf : A.R.WF)
    (hatoms : RulesWF sig A.R.before rules) (hplan : PlansOK rules) (hemit : EmitsAll A rules) :
    InvLag A rules := by
  intro rule hr σ hm
  exact fired_after_actions A hwf
    (hemit rule hr σ ((mem_runNaive_iff (hatoms rule hr) (hplan rule hr) σ).2 hm))

/-- `inv_step`: from `InvLag` of round `r-1` to `InvLag` of round `r`.
A match of `G_r` that matched `G_{r-1}` is fired in `G_r` and transported;
a new one is emitted by a variant (tracked rule, `semi_naive_round_complete`)
or by the naive run (rule routed naive) and fired by the actions. -/
theorem inv_step {sig : Sym → Kind} {naive : Rule → Bool} {rules : List Rule}
    {prev A : ActRound} (hlink : A.R.before = prev.R.after)
    (hprev : prev.R.WF) (htr : prev.R.tracking = true)
    (hA : A.R.WF) (hAp : A.R.Persist) (hsub : A.R.subsumed = ∅)
    (hatoms₀ : RulesWF sig prev.R.before rules) (hatoms₁ : RulesWF sig prev.R.after rules)
    (hplan : PlansOK rules) (hemit : EmitsRound naive prev.R A rules)
    (hinv : InvLag prev rules) : InvLag A rules := by
  intro rule hr σ hm
  rw [hlink] at hm
  by_cases hold : Matches prev.R.before rule.atoms σ
  · have hf := hinv rule hr σ hold
    rw [← hlink] at hf
    exact fired_transport' hA hAp hsub hf
  · apply fired_after_actions A hA
    have hnew : σ ∈ runNaive prev.R.after rule.plan :=
      (mem_runNaive_iff (hatoms₁ rule hr) (hplan rule hr) σ).2 hm
    obtain ⟨h1, h2⟩ := hemit rule hr
    rw [hlink] at h1 h2
    cases hn : naive rule with
    | true => exact h1 hn σ hnew
    | false =>
        have hold' : σ ∉ runNaive prev.R.before rule.plan := fun h =>
          hold ((mem_runNaive_iff (hatoms₀ rule hr) (hplan rule hr) σ).1 h)
        obtain ⟨k, ak, hk, hv⟩ :=
          semi_naive_round_complete hprev htr (hatoms₀ rule hr) (hatoms₁ rule hr) (hplan rule hr)
            hnew hold'
        exact h2 hn k ak hk σ hv

/-! ## Chains of rounds -/

/-- A chain of rounds with actions after a first round `prev`: each round
matches on the previous round's after snapshot and emits what the loop
emits for it. -/
def AChain (naive : Rule → Bool) (rules : List Rule) : ActRound → List ActRound → Prop
  | _, [] => True
  | prev, A :: As => A.R.before = prev.R.after ∧ EmitsRound naive prev.R A rules ∧ AChain naive rules A As

/-- The per-round hypotheses: the round's `WF`, tracking on, persistence of
nodes, no subsumption, and the rules' atoms well formed on its after
snapshot. -/
structure RoundOK (sig : Sym → Kind) (rules : List Rule) (A : ActRound) : Prop where
  wf : A.R.WF
  tracking : A.R.tracking = true
  persist : A.R.Persist
  nosub : A.R.subsumed = ∅
  atoms : RulesWF sig A.R.after rules

theorem invLag_chain_aux {sig : Sym → Kind} {naive : Rule → Bool} {rules : List Rule}
    (hplan : PlansOK rules) : ∀ (A₀ : ActRound) (As : List ActRound),
    RulesWF sig A₀.R.before rules → (∀ A ∈ A₀ :: As, RoundOK sig rules A) →
    InvLag A₀ rules → AChain naive rules A₀ As → ∀ A ∈ As, InvLag A rules := by
  intro A₀ As
  induction As generalizing A₀ with
  | nil => intro _ _ _ _ A hA; simp at hA
  | cons A As ih =>
      intro h₀ hok hinv hchain A' hA'
      obtain ⟨hlink, hemit, hchain'⟩ := hchain
      have hok₀ := hok A₀ (by simp)
      have hokA := hok A (by simp)
      have hinvA : InvLag A rules :=
        inv_step hlink hok₀.wf hok₀.tracking hokA.wf hokA.persist hokA.nosub h₀ hok₀.atoms hplan
          hemit hinv
      rcases List.mem_cons.1 hA' with rfl | hA'
      · exact hinvA
      · exact ih A (by rw [hlink]; exact hok₀.atoms) (fun B hB => hok B (by simp [hB])) hinvA
          hchain' A' hA'

/-- `InvLag` holds at every round of a run: round 0 naive, then the chain. -/
theorem invLag_chain {sig : Sym → Kind} {naive : Rule → Bool} {rules : List Rule}
    (A₀ : ActRound) (As : List ActRound) (hplan : PlansOK rules)
    (h₀ : RulesWF sig A₀.R.before rules) (hok : ∀ A ∈ A₀ :: As, RoundOK sig rules A)
    (hemit₀ : EmitsAll A₀ rules) (hchain : AChain naive rules A₀ As) :
    ∀ A ∈ A₀ :: As, InvLag A rules := by
  have hinv₀ : InvLag A₀ rules := invLag_zero A₀ (hok A₀ (by simp)).wf h₀ hplan hemit₀
  intro A hA
  rcases List.mem_cons.1 hA with rfl | hA
  · exact hinv₀
  · exact invLag_chain_aux hplan A₀ As h₀ hok hinv₀ hchain A hA

/-- The chain with actions is a `Chain` of its rounds. -/
theorem achain_chain {naive : Rule → Bool} {rules : List Rule} :
    ∀ (A₀ : ActRound) (As : List ActRound), AChain naive rules A₀ As →
      Chain A₀.R.after (As.map (·.R))
  | _, [], _ => trivial
  | _, A :: As, ⟨hlink, _, hchain⟩ => ⟨hlink, achain_chain A As hchain⟩

/-! ## The fixpoint -/

/-- A round that changed nothing: the after snapshot has the same nodes
and the same `find` as the before snapshot (no node minted, no two
classes merged, nothing subsumed; `changes == 0`, `saturate.rs:1018-1020`,
up to `Insert` actions that hit the hash-cons). -/
def Round.Unchanged (R : Round) : Prop :=
  (∀ p, p ∈ R.after.nodes ↔ p ∈ R.before.nodes) ∧ ∀ id, R.after.find id = R.before.find id

/-- `Den` reads the graph through node membership and `find` only. -/
theorem den_congr {G G' : Graph} (hn : ∀ p, p ∈ G.nodes ↔ p ∈ G'.nodes)
    (hf : G.find = G'.find) {σ : Binding} {t : Pat} {c : C} (h : Den G σ t c) :
    Den G' σ t c := by
  induction h with
  | var hx => rw [hf]; exact Den.var hx
  | plain hl hall hmem ih => rw [hf]; exact Den.plain hl ih ((hn _).1 hmem)
  | comm ha hb hmem iha ihb =>
      rw [hf]; exact Den.comm iha ihb (hmem.imp (hn _).1 (hn _).1)
  | assoc hl hall hpre hsuf hmem ih =>
      rw [hf] at hmem ⊢; exact Den.assoc hl ih hpre hsuf ((hn _).1 hmem)
  | ac hl hmult hden hrest hmem ih =>
      rw [hf] at hmem ⊢; exact Den.ac hl hmult ih hrest ((hn _).1 hmem)
  | aci hl hall hrest hmem ih =>
      rw [hf] at hmem ⊢; exact Den.aci hl ih hrest ((hn _).1 hmem)

theorem fired_congr {G G' : Graph} (hn : ∀ p, p ∈ G.nodes ↔ p ∈ G'.nodes)
    (hf : G.find = G'.find) {σ : Binding} {rule : Rule} (h : Fired G σ rule) :
    Fired G' σ rule := by
  intro act hact
  have := h act hact
  cases act with
  | insert t => obtain ⟨c, hc⟩ := this; exact ⟨c, den_congr hn hf hc⟩
  | union a b => obtain ⟨c, ha, hb⟩ := this; exact ⟨c, den_congr hn hf ha, den_congr hn hf hb⟩
  | subsume _ => trivial

theorem matches_congr {G G' : Graph} (hn : ∀ p, p ∈ G.nodes ↔ p ∈ G'.nodes)
    (hf : G.find = G'.find) {atoms : List QAtom} {σ : Binding} (h : Matches G atoms σ) :
    Matches G' atoms σ :=
  { h with
    sat := fun q hq => by
      cases q with
      | scan a =>
          refine atomSat_transfer (h.sat _ hq) ?_
          intro id n _ hmem
          exact ⟨(hn _).1 hmem, by rw [hf]⟩
      | eq x y => exact h.sat _ hq }

/-- At a round that changed nothing, `InvLag` is `Inv` at both snapshots. -/
theorem inv_of_unchanged {rules : List Rule} (A : ActRound) (hinv : InvLag A rules)
    (hfix : A.R.Unchanged) : Saturate.Inv A.R.before rules ∧ Saturate.Inv A.R.after rules := by
  have hf : A.R.after.find = A.R.before.find := funext hfix.2
  constructor
  · intro rule hr σ hm
    exact fired_congr hfix.1 hf (hinv rule hr σ hm)
  · intro rule hr σ hm
    exact hinv rule hr σ (matches_congr hfix.1 hf hm)

/-- `saturation_complete`: along a run (round 0 naive, then a chain of
semi-naive rounds), at a round that changed nothing every match of every
rule is fired, at the snapshot the round matched on and at the one after. -/
theorem saturation_complete {sig : Sym → Kind} {naive : Rule → Bool} {rules : List Rule}
    (A₀ : ActRound) (As : List ActRound) (hplan : PlansOK rules)
    (h₀ : RulesWF sig A₀.R.before rules) (hok : ∀ A ∈ A₀ :: As, RoundOK sig rules A)
    (hemit₀ : EmitsAll A₀ rules) (hchain : AChain naive rules A₀ As)
    {A : ActRound} (hA : A ∈ A₀ :: As) (hfix : A.R.Unchanged) :
    Saturate.Inv A.R.before rules ∧ Saturate.Inv A.R.after rules :=
  inv_of_unchanged A (invLag_chain A₀ As hplan h₀ hok hemit₀ hchain A hA) hfix

end Semper.EMatch
