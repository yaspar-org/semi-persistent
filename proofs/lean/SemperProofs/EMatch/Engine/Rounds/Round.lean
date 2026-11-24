import SemperProofs.EMatch.Engine.SemiNaive
import SemperProofs.EMatch.Env.Snapshot

/-!
# A semi-naive round as a state transition (spec-semi-naive-rounds §A, §B)

A round `r ≥ 1` of `saturate_rules_semi` (`saturate.rs:871-1000`) is, from
the matcher's point of view, a transition between two frozen graphs:

* `before`: the snapshot of round `r-1` (the graph as of its index build);
* `after`: the snapshot of round `r` (the graph after the `rebuild` that
  opens round `r`, as of its index build).

Between the two snapshots the engine applied the actions of round `r-1`
(`union`: a merge recorded in the union-find only, children rewritten at
the next `rebuild`, `egraph.rs:1601-1620`; `add`: a node minted with the
children canonical for the *live* union-find, `egraph.rs:1039`, that
later merges may make stale) and the `rebuild` of round `r`
(`egraph.rs:2377-2470`: the worklist of absorbed use-lists is drained,
every parent of an absorbed class is recanonicalized, hash-cons
collisions and degenerate arities are merged, to a fixpoint).

The delta of round `r` is the touched log between the two index builds
(`saturate.rs:886-911`): ids minted (`egraph.rs:4055`), ids whose stored
children changed under recanonicalization (`caches.rs:547`, `caches.rs:985`:
pushed only when the span changed), ids subsumed (`egraph.rs:4256`), and,
when `track_merge_members` is set (`egraph.rs:882`, `egraph.rs:907`), the
members of every absorbed class at merge time (`egraph.rs:1660-1693`).

`Round` records the two snapshots and the engine's two sets (`touched`,
`mergeDelta`); `Round.WF` states what the operations guarantee about them.
The sets `Created`, `Recanon`, `Absorbed` are *derived* from the two
snapshots; `WF` says the engine's sets cover them.
-/

namespace Semper.EMatch

/-- One semi-naive round, from the snapshot of round `r-1` to the snapshot
of round `r`. -/
structure Round where
  /-- The frozen graph of round `r-1`. -/
  before : Graph
  /-- The frozen graph of round `r`. -/
  after : Graph
  /-- The ids minted between the two builds (`register_if_fresh`,
  `egraph.rs:4034-4058`): by the actions of round `r-1` and by the rebuild
  of round `r` (completion). -/
  added : Finset NodeId
  /-- The class merges recorded between the two builds, as pairs of
  pre-merge classes: direct `union`s of the actions, congruence collisions
  and degeneracies of the rebuild. All route through `merge_in_classes`
  (`egraph.rs:1637`). Documentary: `WF.no_split` is its only consequence
  the development uses. -/
  unions : List (C × C)
  /-- The ids subsumed between the two builds (`egraph.rs:4254-4257`). -/
  subsumed : Finset NodeId
  /-- The engine's touched log at the index build of round `r`
  (`eg.touched()`, `saturate.rs:891`), deduplicated (`index.rs:413-419`). -/
  touched : Finset NodeId
  /-- The merge-membership delta: the ids pushed by `merge_in_classes`
  (`egraph.rs:1693`). The engine stores them in the same log; they are kept
  apart here so that the untracked mode is the same structure with
  `mergeDelta = ∅`. -/
  mergeDelta : Finset NodeId
  /-- `track_merge_members` (`egraph.rs:190`): on under the CLI's
  `--use-semi-naive` (`egraph.rs:880-886`, `interpret.rs:488-497`), off in
  the free function `saturate::saturate_semi` (`saturate.rs:772-787`). -/
  tracking : Bool

namespace Round

/-- An id present after the round and absent before it. -/
def Created (R : Round) (id : NodeId) : Prop :=
  (∃ n', (id, n') ∈ R.after.nodes) ∧ ∀ n, (id, n) ∉ R.before.nodes

/-- An id whose stored node changed between the two snapshots (children
rewritten by recanonicalization). -/
def Recanon (R : Round) (id : NodeId) : Prop :=
  ∃ n n', (id, n) ∈ R.before.nodes ∧ (id, n') ∈ R.after.nodes ∧ n ≠ n'

/-- An id whose class representative changed: its class was absorbed by
some merge of the round. -/
def Absorbed (R : Round) (id : NodeId) : Prop :=
  R.after.find id ≠ R.before.find id

/-- The engine's "new" predicate of round `r`: the delta index is built
from `touched` (`index.rs:405-419`), which also holds the merge members
when tracking is on. -/
def isNew (R : Round) : NodeId → Bool :=
  fun id => decide (id ∈ R.touched ∨ id ∈ R.mergeDelta)

/-- What the round's operations guarantee (spec-semi-naive-rounds §B). -/
structure WF (R : Round) : Prop where
  /-- A fresh id is logged at registration (`egraph.rs:4055`). -/
  created_added : ∀ id, R.Created id → id ∈ R.added
  added_touched : ∀ id ∈ R.added, id ∈ R.touched
  /-- Recanonicalization logs an id exactly when its stored children
  changed (`caches.rs:541-547`, `caches.rs:970-985`). -/
  recanon_touched : ∀ id, R.Recanon id → id ∈ R.touched
  /-- `subsume` logs the id (`egraph.rs:4256`). -/
  subsumed_touched : ∀ id ∈ R.subsumed, id ∈ R.touched
  /-- With tracking on, every member of an absorbed class is logged at the
  merge (`egraph.rs:1660-1693`); an id whose representative changed was a
  member of the absorbed side of some merge of the round. Stated for the
  ids the after-snapshot indexes (a subsumed id is skipped by the index,
  `index.rs:521-523`). -/
  absorbed_delta : R.tracking = true → ∀ id, (∃ n', (id, n') ∈ R.after.nodes) →
    R.Absorbed id → id ∈ R.mergeDelta
  /-- Classes only merge (the union-find never splits). -/
  no_split : ∀ id id', R.before.find id = R.before.find id' → R.after.find id = R.after.find id'
  /-- H2: `rebuild` precedes the build, stored children are canonical. -/
  children_canon : R.after.ChildrenCanon
  /-- H1: `round_repr` returns representatives. -/
  find_idem : R.after.FindIdem
  /-- Hash-cons dedup: two stored nodes with the same content are in one
  class (collision merges, `caches.rs:575-585`, `egraph.rs:2456-2473`). -/
  dedup : ∀ id₁ id₂ n, (id₁, n) ∈ R.after.nodes → (id₂, n) ∈ R.after.nodes →
    R.after.find id₁ = R.after.find id₂

theorem WF.created_touched {R : Round} (h : R.WF) {id : NodeId} (hc : R.Created id) :
    id ∈ R.touched :=
  h.added_touched id (h.created_added id hc)

theorem isNew_eq_true {R : Round} {id : NodeId} :
    R.isNew id = true ↔ id ∈ R.touched ∨ id ∈ R.mergeDelta := by
  simp [isNew]

theorem isNew_eq_false {R : Round} {id : NodeId} :
    R.isNew id = false ↔ id ∉ R.touched ∧ id ∉ R.mergeDelta := by
  simp [isNew]

/-- An id present after the round that is not new is present before it,
with the same stored node and the same representative (tracking on). -/
theorem stable_of_not_new {R : Round} (hwf : R.WF) (htr : R.tracking = true) {id : NodeId}
    {n' : Node} (hmem : (id, n') ∈ R.after.nodes) (hold : R.isNew id = false) :
    (id, n') ∈ R.before.nodes ∧ R.before.find id = R.after.find id := by
  obtain ⟨ht, hd⟩ := isNew_eq_false.1 hold
  have hbefore : ∃ n, (id, n) ∈ R.before.nodes := by
    by_contra hno
    push Not at hno
    exact ht (hwf.created_touched ⟨⟨n', hmem⟩, hno⟩)
  obtain ⟨n, hn⟩ := hbefore
  have hnn : n = n' := by
    by_contra hne
    exact ht (hwf.recanon_touched id ⟨n, n', hn, hmem, hne⟩)
  subst hnn
  refine ⟨hn, ?_⟩
  by_contra hfind
  exact hd (hwf.absorbed_delta htr id ⟨n, hmem⟩ (Ne.symm hfind))

end Round

end Semper.EMatch
