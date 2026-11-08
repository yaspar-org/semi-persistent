import SemperProofs.Fidelity.Index

/-!
# Saturation with `:subsume` (fidelity row: `subsumed = ∅`)

`saturation_complete` (`Saturate/Invariant.lean`) assumes no round
subsumes anything (`RoundOK.nosub`). The reason is that `Den` was read on
the index: a `(subsume t)` removes `t` from the index (`index.rs:521-523`),
so a consequence built of `t` stopped being "present". The engine does not
delete anything: `subsume` sets a flag on the stored node
(`egraph.rs:4262`), the flag survives recanonicalization (`caches.rs:558-562`),
the node keeps its class, and a later `add` of the same term hits it in
the hash-cons.

Here a round carries the two stores (`Fidelity/Index.lean`): matches are
read on the index (`Store.index`, skipping subsumed, shielded and
unmatchable-class nodes), consequences on the store (`Store.graph`). The
store keeps every node, subsumed or not: a fixed-arity node persists
literally in every round (`LiteralFixed`), and the invariant for a rule
that builds an n-ary term is guarded by literal persistence of every node
(`Literal`), which a round that changed nothing has; a round without it
routes those rules to the naive matcher (`route`, as the engine's
`respelled`). The invariant and the fixpoint theorem hold with no
hypothesis on subsumption: `inv_step_store`, `invLag_chain_store`,
`saturation_complete_store`.
A match at a subsumed node is excluded by the index itself
(`matches_index_iff`): it is never required to be fired.
-/

namespace Semper.EMatch.Fidelity

open Semper.EMatch

/-- What every rebuild establishes of the two stores: `find` only merges,
both snapshots are rebuilt (`find` idempotent, stored children canonical,
hash-cons dedup over every stored node, subsumed ones included: the
recanonicalization of `caches.rs:525-608` walks them and keeps their
flags). -/
structure StoreWF (Sb Sa : Store) : Prop where
  before_idem : Sb.graph.FindIdem
  after_idem : Sa.graph.FindIdem
  no_split : ∀ id id', Sb.find id = Sb.find id' → Sa.find id = Sa.find id'
  children_canon : Sa.graph.ChildrenCanon
  dedup : ∀ id₁ id₂ n, (id₁, n) ∈ Sa.nodes → (id₂, n) ∈ Sa.nodes → Sa.find id₁ = Sa.find id₂

/-- Literal persistence: every stored node stays stored with its children
mapped through the new `find`. What `recanonize_node` does when no law
applies; a unit drop, a nilpotent clamp or a degenerate arity breaks it
(`Fidelity/Recanon.lean`). -/
def Literal (Sb Sa : Store) : Prop :=
  ∀ id n, (id, n) ∈ Sb.nodes →
    ∃ n', (id, n') ∈ Sa.nodes ∧ n'.op = n.op ∧ CanonCh Sa.find n.children n'.children

/-- Literal persistence of the tuple, pair and sequence nodes: what
`recanonize_node` does to them in every rebuild (`PlainCanon`, `CCanon`,
`OrderedCanon` map the children through `find` and apply no law). -/
def LiteralFixed (Sb Sa : Store) : Prop :=
  ∀ id n, (id, n) ∈ Sb.nodes → n.children.isVariadic = false →
    ∃ n', (id, n') ∈ Sa.nodes ∧ n'.op = n.op ∧ CanonCh Sa.find n.children n'.children

theorem Literal.toFixed {Sb Sa : Store} (h : Literal Sb Sa) : LiteralFixed Sb Sa :=
  fun id n hmem _ => h id n hmem

/-- A round that changed nothing persists every node literally. -/
theorem literal_of_unchanged {Sb Sa : Store} (hc : Sa.graph.ChildrenCanon)
    (hn : ∀ p, p ∈ Sa.nodes ↔ p ∈ Sb.nodes) : Literal Sb Sa := by
  intro id n hmem
  have hmem' : (id, n) ∈ Sa.nodes := (hn _).2 hmem
  exact ⟨n, hmem', rfl, canonCh_self (G := Sa.graph) (hc _ hmem')⟩

/-- The round facts of the store plus literal persistence of every stored
node (the former assumption of every round; now the guard of the invariant,
`InvLagS`, and a consequence of `Unchanged` at the fixpoint). -/
structure StorePersist (Sb Sa : Store) : Prop extends StoreWF Sb Sa where
  persist : Literal Sb Sa

/-- The round facts plus literal persistence of the fixed-arity nodes. -/
structure StorePersistFixed (Sb Sa : Store) : Prop extends StoreWF Sb Sa where
  fixed : LiteralFixed Sb Sa

theorem StorePersist.toFixed {Sb Sa : Store} (h : StorePersist Sb Sa) : StorePersistFixed Sb Sa :=
  ⟨h.toStoreWF, h.persist.toFixed⟩

/-- The round between the two stores seen as a `Round` on the full graphs
with nothing subsumed (subsumption does not touch the store) and every
stored id logged; only `transport` is read from it. -/
def StorePersist.round (Sb Sa : Store) : Round where
  before := Sb.graph
  after := Sa.graph
  added := (Sa.nodes.map Prod.fst).toFinset
  unions := []
  subsumed := ∅
  touched := (Sa.nodes.map Prod.fst).toFinset
  mergeDelta := (Sa.nodes.map Prod.fst).toFinset
  tracking := true

theorem StoreWF.round_wf {Sb Sa : Store} (h : StoreWF Sb Sa) :
    (StorePersist.round Sb Sa).WF where
  created_added := by
    rintro id ⟨⟨n', hn'⟩, -⟩
    simp only [StorePersist.round, List.mem_toFinset, List.mem_map]
    exact ⟨_, hn', rfl⟩
  added_touched := fun _ h => h
  recanon_touched := by
    rintro id ⟨n, n', -, hn', -⟩
    simp only [StorePersist.round, List.mem_toFinset, List.mem_map]
    exact ⟨_, hn', rfl⟩
  subsumed_touched := by simp [StorePersist.round]
  absorbed_delta := by
    rintro - id ⟨n', hn'⟩ -
    simp only [StorePersist.round, List.mem_toFinset, List.mem_map]
    exact ⟨_, hn', rfl⟩
  no_split := h.no_split
  children_canon := h.children_canon
  find_idem := h.after_idem
  dedup := h.dedup

theorem StorePersist.round_persist {Sb Sa : Store} (h : StorePersist Sb Sa) :
    (StorePersist.round Sb Sa).Persist where
  before_find_idem := h.before_idem
  persist := fun id n hmem _ => h.persist id n hmem

/-- A fired instance on the store stays fired, whatever the round
subsumed. -/
theorem fired_transport_store {Sb Sa : Store} (h : StorePersist Sb Sa) {σ : Binding}
    {rule : Rule} (hf : Fired Sb.graph σ rule) : Fired Sa.graph σ rule :=
  fired_transport' (R := StorePersist.round Sb Sa) h.toStoreWF.round_wf h.round_persist rfl hf

theorem StorePersistFixed.round_persist {Sb Sa : Store} (h : StorePersistFixed Sb Sa) :
    (StorePersist.round Sb Sa).PersistFixed where
  before_find_idem := h.before_idem
  persist := fun id n hmem _ hv => h.fixed id n hmem hv

/-- A fired instance of a rule that builds no n-ary term stays fired on the
store, through the fixed-arity nodes alone. -/
theorem fired_transport_store_fixed {Sb Sa : Store} (h : StorePersistFixed Sb Sa) {σ : Binding}
    {rule : Rule} (hr : rule.buildsNary = false) (hf : Fired Sb.graph σ rule) :
    Fired Sa.graph σ rule :=
  fired_transport_fixed' (R := StorePersist.round Sb Sa) h.toStoreWF.round_wf h.round_persist rfl
    hr hf

/-- One round with its actions, on stores. `R` is the matcher's round on
the two indexes (its `WF` is the engine's touched-log contract, as
before); the actions build their terms in the store. -/
structure SActRound where
  R : Round
  Sb : Store
  Sa : Store
  before_eq : R.before = Sb.index
  after_eq : R.after = Sa.index
  emitted : Rule → Binding → Prop
  inserts : ∀ rule σ, emitted rule σ → ∀ t, Action.insert t ∈ rule.actions →
    ∃ c, Den Sa.graph σ t c
  unions : ∀ rule σ, emitted rule σ → ∀ a b, Action.union a b ∈ rule.actions →
    ∃ c₁ c₂, Den Sa.graph σ a c₁ ∧ Den Sa.graph σ b c₂ ∧ (c₁, c₂) ∈ R.unions
  /-- `(subsume x)` sets the flag (`egraph.rs:4262`). -/
  subsumes : ∀ rule σ, emitted rule σ → ∀ x, Action.subsume x ∈ rule.actions →
    ∀ id, σ.node x = some id → Sa.flags.subsumed id = true
  unions_merged : ∀ u ∈ R.unions, Sa.find u.1 = Sa.find u.2

theorem fired_after_actions_store (A : SActRound) (hidem : A.Sa.graph.FindIdem) {rule : Rule}
    {σ : Binding} (h : A.emitted rule σ) : Fired A.Sa.graph σ rule := by
  intro act hact
  cases act with
  | insert t => exact A.inserts rule σ h t hact
  | union a b =>
      obtain ⟨c₁, c₂, ha, hb, hu⟩ := A.unions rule σ h a b hact
      exact actFired_union_find hidem ha hb (A.unions_merged _ hu)
  | subsume _ => trivial

/-- `(subsume x)` leaves the matched node out of every later index. -/
theorem subsumed_unmatched (A : SActRound) {rule : Rule} {σ : Binding} (h : A.emitted rule σ)
    {x : Var} (hx : Action.subsume x ∈ rule.actions) {id : NodeId} (hid : σ.node x = some id) :
    A.Sa.skip id = true := by
  simp [Store.skip, A.subsumes rule σ h x hx id hid]

/-- The invariant with latency: matches on the index the round read are
fired in the store after it; for a rule that builds an n-ary term, when the
round's rebuild persisted every stored node literally (`InvLagL`). -/
def InvLagS (A : SActRound) (rules : List Rule) : Prop :=
  ∀ rule ∈ rules, (rule.buildsNary = true → Literal A.Sb A.Sa) →
    ∀ σ, Matches A.Sb.index rule.atoms σ → Fired A.Sa.graph σ rule

/-- What round 0 emits: every naive match on the index. -/
def EmitsAllS (A : SActRound) (rules : List Rule) : Prop :=
  ∀ rule ∈ rules, ∀ σ ∈ runNaive A.R.before rule.plan, A.emitted rule σ

/-- What round `r ≥ 1` emits (`EmitsRound` with stores). -/
def EmitsRoundS (naive : Rule → Bool) (prev : Round) (A : SActRound) (rules : List Rule) : Prop :=
  ∀ rule ∈ rules,
    (naive rule = true → ∀ σ ∈ runNaive A.R.before rule.plan, A.emitted rule σ) ∧
    (naive rule = false → ∀ (k : Nat) (ak : RAtom), rule.atoms[k]? = some (.scan ak) →
      ∀ σ ∈ runVariant A.R.before prev.isNew k rule.plan, A.emitted rule σ)

theorem invLagS_zero {sig : Sym → Kind} {rules : List Rule} (A : SActRound) (hwf : A.R.WF)
    (hatoms : RulesWF sig A.R.before rules) (hplan : PlansOK rules) (hemit : EmitsAllS A rules) :
    InvLagS A rules := by
  intro rule hr _ σ hm
  have hidem : A.Sa.graph.FindIdem := by
    have := hwf.find_idem; rw [A.after_eq] at this; exact this
  rw [← A.before_eq] at hm
  exact fired_after_actions_store A hidem
    (hemit rule hr σ ((mem_runNaive_iff (hatoms rule hr) (hplan rule hr) σ).2 hm))

/-- `inv_step` without `subsumed = ∅` and without literal persistence of
the n-ary nodes: a round whose rebuild was not literal routes the rules
that build n-ary terms naive (`route`, `resp = true`). -/
theorem inv_step_store {sig : Sym → Kind} {naive : Rule → Bool} {rules : List Rule}
    {prev A : SActRound} (hlink : A.Sb = prev.Sa)
    (hprev : prev.R.WF) (htr : prev.R.tracking = true)
    (_hA : A.R.WF) (hAp : StorePersistFixed A.Sb A.Sa)
    (hatoms₀ : RulesWF sig prev.R.before rules) (hatoms₁ : RulesWF sig prev.R.after rules)
    (hplan : PlansOK rules) {resp : Bool} (hresp : ¬ Literal prev.Sb prev.Sa → resp = true)
    (hemit : EmitsRoundS (route naive resp) prev.R A rules)
    (hinv : InvLagS prev rules) : InvLagS A rules := by
  intro rule hr hlit σ hm
  have hRlink : A.R.before = prev.R.after := by rw [A.before_eq, prev.after_eq, hlink]
  have hm' : Matches prev.R.after rule.atoms σ := by rw [prev.after_eq, ← hlink]; exact hm
  have hnew : σ ∈ runNaive prev.R.after rule.plan :=
    (mem_runNaive_iff (hatoms₁ rule hr) (hplan rule hr) σ).2 hm'
  obtain ⟨h1, h2⟩ := hemit rule hr
  rw [hRlink] at h1 h2
  have hroute : route naive resp rule = true → Fired A.Sa.graph σ rule :=
    fun hn => fired_after_actions_store A hAp.after_idem (h1 hn σ hnew)
  by_cases hold : Matches prev.R.before rule.atoms σ
  · rw [prev.before_eq] at hold
    cases hb : rule.buildsNary with
    | false =>
        have hf := hinv rule hr (fun h => by rw [hb] at h; exact absurd h (by decide)) σ hold
        rw [← hlink] at hf
        exact fired_transport_store_fixed hAp hb hf
    | true =>
        have hlitA := hlit hb
        by_cases hpp : Literal prev.Sb prev.Sa
        · have hf := hinv rule hr (fun _ => hpp) σ hold
          rw [← hlink] at hf
          exact fired_transport_store ⟨hAp.toStoreWF, hlitA⟩ hf
        · exact hroute (by simp [route, hresp hpp, hb])
  · cases hn : route naive resp rule with
    | true => exact hroute hn
    | false =>
        apply fired_after_actions_store A hAp.after_idem
        have hold' : σ ∉ runNaive prev.R.before rule.plan := fun h =>
          hold ((mem_runNaive_iff (hatoms₀ rule hr) (hplan rule hr) σ).1 h)
        obtain ⟨k, ak, hk, hv⟩ :=
          semi_naive_round_complete hprev htr (hatoms₀ rule hr) (hatoms₁ rule hr) (hplan rule hr)
            hnew hold'
        exact h2 hn k ak hk σ hv

/-- A chain of store rounds: each round reads the previous store and emits
what the loop emits under its routing, widened to the rules that build an
n-ary term after a round whose rebuild was not literal (`AChain`). -/
def SChain (naive : Rule → Bool) (rules : List Rule) : SActRound → List SActRound → Prop
  | _, [] => True
  | prev, A :: As => A.Sb = prev.Sa ∧
      (∃ resp : Bool, (¬ Literal prev.Sb prev.Sa → resp = true) ∧
        EmitsRoundS (route naive resp) prev.R A rules) ∧
      SChain naive rules A As

/-- The per-round hypotheses of `RoundOK` without `nosub`, plus the
store's round facts and the literal persistence of its fixed-arity nodes. -/
structure RoundOKS (sig : Sym → Kind) (rules : List Rule) (A : SActRound) : Prop where
  wf : A.R.WF
  tracking : A.R.tracking = true
  store : StorePersistFixed A.Sb A.Sa
  atoms : RulesWF sig A.R.after rules

theorem invLag_chain_store_aux {sig : Sym → Kind} {naive : Rule → Bool} {rules : List Rule}
    (hplan : PlansOK rules) : ∀ (A₀ : SActRound) (As : List SActRound),
    RulesWF sig A₀.R.before rules → (∀ A ∈ A₀ :: As, RoundOKS sig rules A) →
    InvLagS A₀ rules → SChain naive rules A₀ As → ∀ A ∈ As, InvLagS A rules := by
  intro A₀ As
  induction As generalizing A₀ with
  | nil => intro _ _ _ _ A hA; simp at hA
  | cons A As ih =>
      intro h₀ hok hinv hchain A' hA'
      obtain ⟨hlink, ⟨resp, hresp, hemit⟩, hchain'⟩ := hchain
      have hok₀ := hok A₀ (by simp)
      have hokA := hok A (by simp)
      have hinvA : InvLagS A rules :=
        inv_step_store hlink hok₀.wf hok₀.tracking hokA.wf hokA.store h₀ hok₀.atoms hplan hresp
          hemit hinv
      have hRlink : A.R.before = A₀.R.after := by rw [A.before_eq, A₀.after_eq, hlink]
      rcases List.mem_cons.1 hA' with rfl | hA'
      · exact hinvA
      · exact ih A (by rw [hRlink]; exact hok₀.atoms) (fun B hB => hok B (by simp [hB])) hinvA
          hchain' A' hA'

theorem invLag_chain_store {sig : Sym → Kind} {naive : Rule → Bool} {rules : List Rule}
    (A₀ : SActRound) (As : List SActRound) (hplan : PlansOK rules)
    (h₀ : RulesWF sig A₀.R.before rules) (hok : ∀ A ∈ A₀ :: As, RoundOKS sig rules A)
    (hemit₀ : EmitsAllS A₀ rules) (hchain : SChain naive rules A₀ As) :
    ∀ A ∈ A₀ :: As, InvLagS A rules := by
  have hinv₀ : InvLagS A₀ rules := invLagS_zero A₀ (hok A₀ (by simp)).wf h₀ hplan hemit₀
  intro A hA
  rcases List.mem_cons.1 hA with rfl | hA
  · exact hinv₀
  · exact invLag_chain_store_aux hplan A₀ As h₀ hok hinv₀ hchain A hA

/-- Every match on the index of `S` is fired in the store of `S`. -/
def InvS (S : Store) (rules : List Rule) : Prop :=
  ∀ rule ∈ rules, ∀ σ, Matches S.index rule.atoms σ → Fired S.graph σ rule

/-- A round that changed nothing: same stored nodes, same `find`, same
skip predicate (no node minted, no merge, nothing newly subsumed). -/
def SActRound.Unchanged (A : SActRound) : Prop :=
  (∀ p, p ∈ A.Sa.nodes ↔ p ∈ A.Sb.nodes) ∧ (∀ id, A.Sa.find id = A.Sb.find id) ∧
    ∀ id, A.Sa.skip id = A.Sb.skip id

/-- `saturation_complete` with `:subsume`: at a round that changed nothing,
every match on the index (so at no subsumed node) is fired in the store,
at both snapshots. -/
theorem saturation_complete_store {sig : Sym → Kind} {naive : Rule → Bool} {rules : List Rule}
    (A₀ : SActRound) (As : List SActRound) (hplan : PlansOK rules)
    (h₀ : RulesWF sig A₀.R.before rules) (hok : ∀ A ∈ A₀ :: As, RoundOKS sig rules A)
    (hemit₀ : EmitsAllS A₀ rules) (hchain : SChain naive rules A₀ As)
    {A : SActRound} (hA : A ∈ A₀ :: As) (hfix : A.Unchanged) :
    InvS A.Sb rules ∧ InvS A.Sa rules := by
  have hinvL := invLag_chain_store A₀ As hplan h₀ hok hemit₀ hchain A hA
  obtain ⟨hn, hf, hs⟩ := hfix
  have hlit : Literal A.Sb A.Sa := literal_of_unchanged (hok A hA).store.children_canon hn
  have hinv : ∀ rule ∈ rules, ∀ σ, Matches A.Sb.index rule.atoms σ → Fired A.Sa.graph σ rule :=
    fun rule hr σ hm => hinvL rule hr (fun _ => hlit) σ hm
  have hfeq : A.Sa.find = A.Sb.find := funext hf
  have hgn : ∀ p, p ∈ A.Sa.graph.nodes ↔ p ∈ A.Sb.graph.nodes := hn
  have hin : ∀ p, p ∈ A.Sb.index.nodes ↔ p ∈ A.Sa.index.nodes := by
    intro p; simp only [Store.mem_index, hn, hs]
  constructor
  · intro rule hr σ hm
    exact fired_congr hgn hfeq (hinv rule hr σ hm)
  · intro rule hr σ hm
    exact hinv rule hr σ (matches_congr (fun p => (hin p).symm) hfeq hm)

end Semper.EMatch.Fidelity
