import SemperProofs.EMatch.Engine.Saturate.Transport

/-!
# A round with its actions (spec-actions §F)

`ActRound` wraps a `Round` with the set of bindings whose actions the
round applied (`emitted`, per rule) and the condition that the actions
were applied: every `insert` has its term built in the after snapshot,
every `union` has both sides built with the pair of values recorded in
`R.unions`, every `subsume` has the node subsumed, and the rebuild merged
what the unions record (`egraph.rs:1601-1620`: the union-find is updated
at the merge; `egraph.rs:2377-2475`: the worklist is drained before the
next index build).

The round matches on `R.before` (the frozen snapshot of its round,
`saturate.rs:881-884`), runs the actions of every emitted binding on the
live graph (`saturate.rs:757-764`), and `R.after` is the snapshot after the
`rebuild` that opens the next round. Which bindings are emitted is a
hypothesis of the invariant's induction (`Saturate/Invariant.lean`): the
variants of the round for the tracked rules, the naive run for the rules
routed naive.
-/

namespace Semper.EMatch

/-- One round with its actions. -/
structure ActRound where
  /-- The transition: matching on `R.before`, actions, rebuild, `R.after`. -/
  R : Round
  /-- The bindings of each rule whose actions the round applied. -/
  emitted : Rule → Binding → Prop
  /-- `Insert(t)`, `apply.rs:1289-1292`: the term is built (a hash-cons hit
  returns the existing node, a miss mints one; either way the node is in
  the next snapshot with canonical children). -/
  inserts : ∀ rule σ, emitted rule σ → ∀ t, Action.insert t ∈ rule.actions →
    ∃ c, Den R.after σ t c
  /-- `Union(a, b)`, `apply.rs:1271-1288`: both sides are built and their
  classes are recorded as merged (or were already one class, in which case
  the pair is recorded as a trivial union). -/
  unions : ∀ rule σ, emitted rule σ → ∀ a b, Action.union a b ∈ rule.actions →
    ∃ c₁ c₂, Den R.after σ a c₁ ∧ Den R.after σ b c₂ ∧ (c₁, c₂) ∈ R.unions
  /-- `Subsume(x)`, `apply.rs:1300-1304`. -/
  subsumes : ∀ rule σ, emitted rule σ → ∀ x, Action.subsume x ∈ rule.actions →
    ∀ id, σ.node x = some id → id ∈ R.subsumed
  /-- The rebuild merges what the unions record: after the round the two
  sides of every recorded union have one representative. -/
  unions_merged : ∀ u ∈ R.unions, R.after.find u.1 = R.after.find u.2

/-- `fired_after_actions`: an emitted binding's instance is fired in the
after snapshot. -/
theorem fired_after_actions (A : ActRound) (hwf : A.R.WF) {rule : Rule} {σ : Binding}
    (h : A.emitted rule σ) : Fired A.R.after σ rule := by
  intro act hact
  cases act with
  | insert t => exact A.inserts rule σ h t hact
  | union a b =>
      obtain ⟨c₁, c₂, ha, hb, hu⟩ := A.unions rule σ h a b hact
      exact actFired_union_find hwf.find_idem ha hb (A.unions_merged _ hu)
  | subsume _ => trivial

end Semper.EMatch
