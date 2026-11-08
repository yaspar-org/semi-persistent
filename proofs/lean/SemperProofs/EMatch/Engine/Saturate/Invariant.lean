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
  `InvLagL`, transported to `G_{r+1}` by `fired_transport'` when the round
  persists every node literally, by `fired_transport_fixed'` when the rule
  builds no n-ary term, and otherwise re-emitted by the naive run the
  routing `route` forces) or is new, and `semi_naive_round_complete` says
  some variant of round `r` emits it (`delta_complete` for the tracked
  rules; `mem_runNaive_iff` for the rules routed naive): `inv_step`.
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

/-- The routing of a round: a rule is matched in full when it is routed naive
(`needs_naive_match`, `saturate.rs`) or when the previous rebuild rewrote a
stored node non-literally (`respelled`) and the rule builds an n-ary term. -/
def route (naive : Rule → Bool) (resp : Bool) (rule : Rule) : Bool :=
  naive rule || (resp && rule.buildsNary)

/-- The invariant with latency, guarded: a rule that builds an n-ary term is
fired only when the round's rebuild persisted every node literally. A rule
that builds none is fired unconditionally. At a round that changed nothing
the guard holds for every rule (`persist_of_unchanged`). -/
def InvLagL (A : ActRound) (rules : List Rule) : Prop :=
  ∀ rule ∈ rules, (rule.buildsNary = true → A.R.Persist) →
    ∀ σ, Matches A.R.before rule.atoms σ → Fired A.R.after σ rule

theorem InvLag.toL {A : ActRound} {rules : List Rule} (h : InvLag A rules) : InvLagL A rules :=
  fun rule hr _ σ hm => h rule hr σ hm

/-- `inv_step`: from `InvLagL` of round `r-1` to `InvLagL` of round `r`.
A match of `G_r` that matched `G_{r-1}` is fired in `G_r` and transported:
literally when the round persisted every node (`fired_transport'`), through
the fixed-arity nodes alone when the rule builds no n-ary term
(`fired_transport_fixed'`), and otherwise it is re-emitted by the naive run
(`route` with `resp = true`, which the previous round's non-literal rebuild
forces). A new one is emitted by a variant (tracked rule,
`semi_naive_round_complete`) or by the naive run and fired by the actions. -/
theorem inv_step {sig : Sym → Kind} {naive : Rule → Bool} {rules : List Rule}
    {prev A : ActRound} (hlink : A.R.before = prev.R.after)
    (hprev : prev.R.WF) (htr : prev.R.tracking = true)
    (hA : A.R.WF) (hAf : A.R.PersistFixed) (hsub : A.R.subsumed = ∅)
    (hatoms₀ : RulesWF sig prev.R.before rules) (hatoms₁ : RulesWF sig prev.R.after rules)
    (hplan : PlansOK rules) {resp : Bool} (hresp : ¬ prev.R.Persist → resp = true)
    (hemit : EmitsRound (route naive resp) prev.R A rules)
    (hinv : InvLagL prev rules) : InvLagL A rules := by
  intro rule hr hlit σ hm
  rw [hlink] at hm
  have hnew : σ ∈ runNaive prev.R.after rule.plan :=
    (mem_runNaive_iff (hatoms₁ rule hr) (hplan rule hr) σ).2 hm
  obtain ⟨h1, h2⟩ := hemit rule hr
  rw [hlink] at h1 h2
  -- the naive run of this round emits σ when the rule is routed naive
  have hroute : route naive resp rule = true → Fired A.R.after σ rule :=
    fun hn => fired_after_actions A hA (h1 hn σ hnew)
  by_cases hold : Matches prev.R.before rule.atoms σ
  · cases hb : rule.buildsNary with
    | false =>
        have hf := hinv rule hr (fun h => by rw [hb] at h; exact absurd h (by decide)) σ hold
        rw [← hlink] at hf
        exact fired_transport_fixed' hA hAf hsub hb hf
    | true =>
        have hpA := hlit hb
        by_cases hpp : prev.R.Persist
        · have hf := hinv rule hr (fun _ => hpp) σ hold
          rw [← hlink] at hf
          exact fired_transport' hA hpA hsub hf
        · exact hroute (by simp [route, hresp hpp, hb])
  · cases hn : route naive resp rule with
    | true => exact hroute hn
    | false =>
        apply fired_after_actions A hA
        have hold' : σ ∉ runNaive prev.R.before rule.plan := fun h =>
          hold ((mem_runNaive_iff (hatoms₀ rule hr) (hplan rule hr) σ).1 h)
        obtain ⟨k, ak, hk, hv⟩ :=
          semi_naive_round_complete hprev htr (hatoms₀ rule hr) (hatoms₁ rule hr) (hplan rule hr)
            hnew hold'
        exact h2 hn k ak hk σ hv

/-! ## Chains of rounds -/

/-- A chain of rounds with actions after a first round `prev`: each round
matches on the previous round's after snapshot and emits what the loop
emits for it under the round's routing. The routing is the static one
(`naive`) widened to the rules that build an n-ary term when the previous
round's rebuild did not persist every node literally (`resp = true`; the
engine's `respelled`, which `spelling_epoch` counts). -/
def AChain (naive : Rule → Bool) (rules : List Rule) : ActRound → List ActRound → Prop
  | _, [] => True
  | prev, A :: As => A.R.before = prev.R.after ∧
      (∃ resp : Bool, (¬ prev.R.Persist → resp = true) ∧
        EmitsRound (route naive resp) prev.R A rules) ∧
      AChain naive rules A As

/-- The per-round hypotheses: the round's `WF`, tracking on, literal
persistence of the fixed-arity and sequence nodes (`recanonize_node` on a
tuple, pair or sequence), no subsumption, and the rules' atoms well formed
on its after snapshot. Literal persistence of every node is not assumed:
a round without it routes the rules that build n-ary terms naive
(`AChain`). -/
structure RoundOK (sig : Sym → Kind) (rules : List Rule) (A : ActRound) : Prop where
  wf : A.R.WF
  tracking : A.R.tracking = true
  fixed : A.R.PersistFixed
  nosub : A.R.subsumed = ∅
  atoms : RulesWF sig A.R.after rules

theorem invLag_chain_aux {sig : Sym → Kind} {naive : Rule → Bool} {rules : List Rule}
    (hplan : PlansOK rules) : ∀ (A₀ : ActRound) (As : List ActRound),
    RulesWF sig A₀.R.before rules → (∀ A ∈ A₀ :: As, RoundOK sig rules A) →
    InvLagL A₀ rules → AChain naive rules A₀ As → ∀ A ∈ As, InvLagL A rules := by
  intro A₀ As
  induction As generalizing A₀ with
  | nil => intro _ _ _ _ A hA; simp at hA
  | cons A As ih =>
      intro h₀ hok hinv hchain A' hA'
      obtain ⟨hlink, ⟨resp, hresp, hemit⟩, hchain'⟩ := hchain
      have hok₀ := hok A₀ (by simp)
      have hokA := hok A (by simp)
      have hinvA : InvLagL A rules :=
        inv_step hlink hok₀.wf hok₀.tracking hokA.wf hokA.fixed hokA.nosub h₀ hok₀.atoms hplan
          hresp hemit hinv
      rcases List.mem_cons.1 hA' with rfl | hA'
      · exact hinvA
      · exact ih A (by rw [hlink]; exact hok₀.atoms) (fun B hB => hok B (by simp [hB])) hinvA
          hchain' A' hA'

/-- `InvLagL` holds at every round of a run: round 0 naive, then the chain. -/
theorem invLag_chain {sig : Sym → Kind} {naive : Rule → Bool} {rules : List Rule}
    (A₀ : ActRound) (As : List ActRound) (hplan : PlansOK rules)
    (h₀ : RulesWF sig A₀.R.before rules) (hok : ∀ A ∈ A₀ :: As, RoundOK sig rules A)
    (hemit₀ : EmitsAll A₀ rules) (hchain : AChain naive rules A₀ As) :
    ∀ A ∈ A₀ :: As, InvLagL A rules := by
  have hinv₀ : InvLagL A₀ rules :=
    InvLag.toL (invLag_zero A₀ (hok A₀ (by simp)).wf h₀ hplan hemit₀)
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

/-- A round that changed nothing persists every node literally: the node is
still stored, and its children are canonical in the after snapshot. -/
theorem Round.persist_of_unchanged {R : Round} (hwf : R.WF) (hb : R.before.FindIdem)
    (hfix : R.Unchanged) : R.Persist where
  before_find_idem := hb
  persist := by
    intro id n hmem _
    have hmem' : (id, n) ∈ R.after.nodes := (hfix.1 _).2 hmem
    exact ⟨n, hmem', rfl, canonCh_self (hwf.children_canon _ hmem')⟩

/-- At a round that changed nothing, `InvLagL` is `Inv` at both snapshots:
the round persists every node literally, so the guard holds. -/
theorem inv_of_unchanged {rules : List Rule} (A : ActRound) (hwf : A.R.WF)
    (hb : A.R.before.FindIdem) (hinvL : InvLagL A rules)
    (hfix : A.R.Unchanged) : Saturate.Inv A.R.before rules ∧ Saturate.Inv A.R.after rules := by
  have hinv : InvLag A rules :=
    fun rule hr σ hm => hinvL rule hr (fun _ => Round.persist_of_unchanged hwf hb hfix) σ hm
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
  inv_of_unchanged A (hok A hA).wf (hok A hA).fixed.before_find_idem
    (invLag_chain A₀ As hplan h₀ hok hemit₀ hchain A hA) hfix

end Semper.EMatch
