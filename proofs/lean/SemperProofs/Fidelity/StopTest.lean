import SemperProofs.Fidelity.NormalizeSat

/-!
# The engine's stop test implies `Unchanged` (fidelity rows SA11, SA30)

`saturation_complete` and its store forms (`saturation_complete_store`,
`saturation_complete_N`) conclude at a round that changed nothing
(`Round.Unchanged`, `SActRound.Unchanged`: same stored nodes, same `find`,
same skip predicate). The engine does not test that. Its loop stops when
the actions of a round report no change (`saturate.rs`, `changes == 0`),
and before the fix a `union` reported a change only when the live finds
of its two sides differed, even when evaluating the sides had built new
nodes (`apply.rs`, `CompiledAction::Union`). Such a round stopped the run
with nodes that were never matched (`s11_self_union.egg`, `s11_assoc.egg`;
sequence rules, row SA30, have the same shape).

The fixed loop compares the graph's size before and after the action
phase (`EGraph::size_stamp`: node count, live class count) and still
counts a newly set `:subsume` flag through `changes`. This file models the
action phase as a sequence of the graph operations the actions perform,
whoever performs them (ordinary or sequence rules):

* `mint`: `register_if_fresh` on a hash-cons miss, a fresh id in a fresh
  class (node count +1, class count +1);
* `merge`: `merge_in_classes` on two distinct classes, recorded in the
  union-find only (class count -1);
* `subsume`: the flag is set (a change iff it was not set);
* `hit`: a hash-cons hit, or a union whose sides already share a class.

`Phase.nodeCount` and `Phase.classCount` count the first two;
`engine_stop_idle` says a phase with the same stamp and no fresh subsume
left the store as it was, and `engine_stop_unchanged` lifts that to the
round, given that the rebuild opening the next round has nothing to do
when nothing was minted or merged (`EnginePhase.rebuild_idle`: the
worklist is filled only by merges, and completion reads new nodes and
merges only). `Phase.stamp_ne` is the converse: a phase that minted or
merged moves the stamp, so the loop does not stop on it.
`saturation_complete_engine`, `saturation_complete_store_engine` and
`saturation_complete_N_engine` are the fixpoint theorems with the engine's
stop condition in place of `Unchanged`.
-/

namespace Semper.EMatch.Fidelity

open Semper.EMatch

/-- The stored ids. -/
def Store.ids (S : Store) : Finset NodeId := (S.nodes.map Prod.fst).toFinset

/-- `EGraph::node_count`. -/
def Store.nodeCount (S : Store) : Nat := S.ids.card

/-- The live classes: the representatives of the stored ids. -/
def Store.classes (S : Store) : Finset C := S.ids.image S.find

/-- `num_classes()`: the number of live classes. -/
def Store.classCount (S : Store) : Nat := S.classes.card

/-- `EGraph::size_stamp`. -/
def Store.stamp (S : Store) : Nat × Nat := (S.nodeCount, S.classCount)

theorem Store.eq_of {S S' : Store} (h1 : S'.nodes = S.nodes) (h2 : S'.find = S.find)
    (h3 : S'.flags = S.flags) : S' = S := by
  cases S; cases S'; cases h1; cases h2; cases h3; rfl

/-- One graph operation of the action phase, with the number of mints,
merges and fresh subsumes it performs. -/
inductive PStep : Store → Store → Nat → Nat → Nat → Prop
  /-- A hash-cons hit, or a union whose two sides already share a class. -/
  | hit (S : Store) : PStep S S 0 0 0
  /-- `register_if_fresh` on a miss: a fresh id, in a class of its own. -/
  | mint {S S' : Store} (id : NodeId) (n : Node) (hfresh : id ∉ S.ids)
      (hnodes : S'.nodes = (id, n) :: S.nodes) (hfind : ∀ z, z ≠ id → S'.find z = S.find z)
      (hcls : S'.find id ∉ S.classes) : PStep S S' 1 0 0
  /-- `merge_in_classes` on two distinct classes: `y`'s class takes `x`'s
  representative (either side may be `x`); the union-find only. -/
  | merge {S S' : Store} (x y : NodeId) (hx : x ∈ S.ids) (hy : y ∈ S.ids)
      (hne : S.find x ≠ S.find y) (hnodes : S'.nodes = S.nodes)
      (hfind : ∀ z, S'.find z = if S.find z = S.find y then S.find x else S.find z) :
      PStep S S' 0 1 0
  /-- `(subsume x)`: the flag is set, a change iff it was not. -/
  | subsume {S S' : Store} (id : NodeId) (hnodes : S'.nodes = S.nodes)
      (hfind : S'.find = S.find)
      (hflags : S'.flags = { S.flags with subsumed := Function.update S.flags.subsumed id true }) :
      PStep S S' 0 0 (if S.flags.subsumed id then 0 else 1)

theorem ids_of_nodes {S S' : Store} (h : S'.nodes = S.nodes) : S'.ids = S.ids := by
  simp [Store.ids, h]

theorem PStep.nodeCount {S S' : Store} {m g s : Nat} (h : PStep S S' m g s) :
    S'.nodeCount = S.nodeCount + m := by
  cases h with
  | hit => rfl
  | mint id n hfresh hnodes =>
      have : S'.ids = insert id S.ids := by simp [Store.ids, hnodes]
      simp only [Store.nodeCount, this, Finset.card_insert_of_notMem hfresh]
  | merge _ _ _ _ _ hnodes => simp [Store.nodeCount, ids_of_nodes hnodes]
  | subsume _ hnodes => simp [Store.nodeCount, ids_of_nodes hnodes]

theorem PStep.classCount {S S' : Store} {m g s : Nat} (h : PStep S S' m g s) :
    S'.classCount + g = S.classCount + m := by
  cases h with
  | hit => rfl
  | mint id n hfresh hnodes hfind hcls =>
      have hids : S'.ids = insert id S.ids := by simp [Store.ids, hnodes]
      have hold : S.ids.image S'.find = S.classes := by
        apply Finset.image_congr
        intro z hz
        exact hfind z (fun he => hfresh (he ▸ hz))
      have : S'.classes = insert (S'.find id) S.classes := by
        rw [Store.classes, hids, Finset.image_insert, hold]
      simp only [Store.classCount, this, Finset.card_insert_of_notMem hcls]
  | merge x y hx hy hne hnodes hfind =>
      have hcl : S'.classes = S.classes.erase (S.find y) := by
        ext c
        simp only [Store.classes, ids_of_nodes hnodes, Finset.mem_image, Finset.mem_erase]
        constructor
        · rintro ⟨z, hz, rfl⟩
          rw [hfind z]
          split
          · exact ⟨hne, x, hx, rfl⟩
          · rename_i hzy; exact ⟨hzy, z, hz, rfl⟩
        · rintro ⟨hcy, z, hz, rfl⟩
          refine ⟨z, hz, ?_⟩
          rw [hfind z]; simp [hcy]
      have hmem : S.find y ∈ S.classes := Finset.mem_image_of_mem _ hy
      simp only [Store.classCount, hcl, Finset.card_erase_add_one hmem, Nat.add_zero]
  | subsume _ hnodes hfind =>
      simp [Store.classCount, Store.classes, ids_of_nodes hnodes, hfind]

/-- A step that minted, merged and freshly subsumed nothing left the store
as it was. -/
theorem PStep.idle {S S' : Store} {m g s : Nat} (h : PStep S S' m g s) (hm : m = 0)
    (hg : g = 0) (hs : s = 0) : S' = S := by
  cases h with
  | hit => rfl
  | mint => exact absurd hm (by decide)
  | merge => exact absurd hg (by decide)
  | subsume id hnodes hfind hflags =>
      cases hsub : S.flags.subsumed id
      · simp [hsub] at hs
      · have hup : Function.update S.flags.subsumed id true = S.flags.subsumed := by
          funext z
          by_cases hz : z = id
          · subst hz; simp [hsub]
          · simp [Function.update_of_ne hz]
        refine Store.eq_of hnodes hfind ?_
        rw [hflags, hup]

/-- The action phase: a sequence of steps, with the total numbers of mints,
merges and fresh subsumes. -/
inductive Phase : Store → Store → Nat → Nat → Nat → Prop
  | refl (S : Store) : Phase S S 0 0 0
  | step {S S₁ S₂ : Store} {m g s m' g' s' : Nat} :
      PStep S S₁ m g s → Phase S₁ S₂ m' g' s' → Phase S S₂ (m + m') (g + g') (s + s')

theorem Phase.nodeCount {S S' : Store} {m g s : Nat} (h : Phase S S' m g s) :
    S'.nodeCount = S.nodeCount + m := by
  induction h with
  | refl => rfl
  | step hs _ ih => rw [ih, hs.nodeCount]; omega

theorem Phase.classCount {S S' : Store} {m g s : Nat} (h : Phase S S' m g s) :
    S'.classCount + g = S.classCount + m := by
  induction h with
  | refl => rfl
  | step hs _ ih => have := hs.classCount; omega

theorem Phase.idle {S S' : Store} {m g s : Nat} (h : Phase S S' m g s) (hm : m = 0)
    (hg : g = 0) (hs : s = 0) : S' = S := by
  induction h with
  | refl => rfl
  | step hst _ ih =>
      rw [ih (by omega) (by omega) (by omega)]
      exact hst.idle (by omega) (by omega) (by omega)

/-- The stamp is unchanged only if the phase minted and merged nothing. -/
theorem Phase.stamp_counts {S S' : Store} {m g s : Nat} (h : Phase S S' m g s)
    (hst : S'.stamp = S.stamp) : m = 0 ∧ g = 0 := by
  have h1 := h.nodeCount
  have h2 := h.classCount
  simp only [Store.stamp, Prod.mk.injEq] at hst
  omega

/-- The converse: a phase that minted or merged moves the stamp, so the
loop does not stop after it. -/
theorem Phase.stamp_ne {S S' : Store} {m g s : Nat} (h : Phase S S' m g s)
    (hmg : 0 < m + g) : S'.stamp ≠ S.stamp := by
  intro hst
  have := h.stamp_counts hst
  omega

/-- The stop test on the action phase: same stamp, no fresh subsume, and
the store is as it was. -/
theorem engine_stop_idle {S S' : Store} {m g s : Nat} (h : Phase S S' m g s)
    (hst : S'.stamp = S.stamp) (hs : s = 0) : S' = S :=
  have hc := h.stamp_counts hst
  h.idle hc.1 hc.2 hs

/-- A round as the engine runs it: the action phase from the snapshot the
round matched on (`Sb`, the store at the index build, after the rebuild)
to the live store `mid`, the actions' own change count (which counts a
fresh subsume, `apply.rs`, `CompiledAction::Subsume`), and the rebuild that
opens the next round, which produces `Sa`. -/
structure EnginePhase (Sb Sa : Store) where
  mid : Store
  mints : Nat
  merges : Nat
  subs : Nat
  run : Phase Sb mid mints merges subs
  /-- The sum of the actions' reported changes. -/
  changes : Nat
  subs_counted : subs ≤ changes
  /-- The rebuild drains the worklist, which only merges fill, and
  completion acts on new nodes and merges: with neither it changes
  nothing. -/
  rebuild_idle : mints = 0 → merges = 0 → Sa = mid

/-- The engine's stop test (`saturate.rs`): no action reported a change and
the size stamp did not move across the action phase. -/
def EnginePhase.Stop {Sb Sa : Store} (E : EnginePhase Sb Sa) : Prop :=
  E.changes = 0 ∧ E.mid.stamp = Sb.stamp

/-- At a stop the next snapshot is the one the round matched on. -/
theorem EnginePhase.after_eq {Sb Sa : Store} (E : EnginePhase Sb Sa) (h : E.Stop) :
    Sa = Sb := by
  have hs : E.subs = 0 := by have := E.subs_counted; have := h.1; omega
  have hc := E.run.stamp_counts h.2
  rw [E.rebuild_idle hc.1 hc.2]
  exact engine_stop_idle E.run h.2 hs

/-- `engine_stop_unchanged`: the engine's stop test implies the round
model's `Unchanged`. -/
theorem engine_stop_unchanged (A : SActRound) (E : EnginePhase A.Sb A.Sa) (h : E.Stop) :
    A.Unchanged := by
  have he := E.after_eq h
  exact ⟨fun p => by rw [he], fun id => by rw [he], fun id => by rw [he]⟩

theorem engine_stop_unchanged_N {L : Sym → OpLaws} (A : SActRoundN L)
    (E : EnginePhase A.Sb A.Sa) (h : E.Stop) : A.Unchanged := by
  have he := E.after_eq h
  exact ⟨fun p => by rw [he], fun id => by rw [he], fun id => by rw [he]⟩

/-- The same on a bare `Round` whose snapshots are the two stores' graphs. -/
theorem engine_stop_unchanged_round (R : Round) {Sb Sa : Store} (hb : R.before = Sb.graph)
    (ha : R.after = Sa.graph) (E : EnginePhase Sb Sa) (h : E.Stop) : R.Unchanged := by
  have he := E.after_eq h
  unfold Round.Unchanged
  rw [ha, hb, he]
  exact ⟨fun _ => Iff.rfl, fun _ => rfl⟩

/-- `saturation_complete` at the round where the engine stops. -/
theorem saturation_complete_engine {sig : Sym → Kind} {naive : Rule → Bool} {rules : List Rule}
    (A₀ : ActRound) (As : List ActRound) (hplan : PlansOK rules)
    (h₀ : RulesWF sig A₀.R.before rules) (hok : ∀ A ∈ A₀ :: As, RoundOK sig rules A)
    (hemit₀ : EmitsAll A₀ rules) (hchain : AChain naive rules A₀ As)
    {A : ActRound} (hA : A ∈ A₀ :: As) {Sb Sa : Store} (hb : A.R.before = Sb.graph)
    (ha : A.R.after = Sa.graph) (E : EnginePhase Sb Sa) (hstop : E.Stop) :
    Saturate.Inv A.R.before rules ∧ Saturate.Inv A.R.after rules :=
  saturation_complete A₀ As hplan h₀ hok hemit₀ hchain hA
    (engine_stop_unchanged_round A.R hb ha E hstop)

/-- `saturation_complete_store` at the round where the engine stops. -/
theorem saturation_complete_store_engine {sig : Sym → Kind} {naive : Rule → Bool}
    {rules : List Rule} (A₀ : SActRound) (As : List SActRound) (hplan : PlansOK rules)
    (h₀ : RulesWF sig A₀.R.before rules) (hok : ∀ A ∈ A₀ :: As, RoundOKS sig rules A)
    (hemit₀ : EmitsAllS A₀ rules) (hchain : SChain naive rules A₀ As)
    {A : SActRound} (hA : A ∈ A₀ :: As) (E : EnginePhase A.Sb A.Sa) (hstop : E.Stop) :
    InvS A.Sb rules ∧ InvS A.Sa rules :=
  saturation_complete_store A₀ As hplan h₀ hok hemit₀ hchain hA
    (engine_stop_unchanged A E hstop)

/-- `saturation_complete_N` at the round where the engine stops. -/
theorem saturation_complete_N_engine {L : Sym → OpLaws} {sig : Sym → Kind}
    {naive : Rule → Bool} {rules : List Rule}
    (A₀ : SActRoundN L) (As : List (SActRoundN L)) (hplan : PlansOK rules)
    (h₀ : RulesWF sig A₀.R.before rules) (hok : ∀ A ∈ A₀ :: As, RoundOKN sig rules A)
    (hemit₀ : EmitsAllN A₀ rules) (hchain : SChainN naive rules A₀ As)
    {A : SActRoundN L} (hA : A ∈ A₀ :: As) (E : EnginePhase A.Sb A.Sa) (hstop : E.Stop) :
    InvN A.Sa L rules :=
  saturation_complete_N A₀ As hplan h₀ hok hemit₀ hchain hA
    (engine_stop_unchanged_N A E hstop)

end Semper.EMatch.Fidelity
