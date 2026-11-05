import SemperProofs.EMatch.Engine.ByOp

/-!
# The `ByOp` placement policy (fidelity row: `OpFilterPolicy`)

`run_join` places a join's `ByOp` restriction either as a leapfrog
operand or, demoted, as a per-candidate test `op[id] = f`
(`ematch.rs:2723-2744`, `demote_by_op`). The decision depends on the
process-wide policy (`OpFilterPolicy`, `ematch.rs:2651-2685`; `Adaptive`
is shipped, the other two are pinned by tests) and on two bucket sizes:
`m`, the smallest other bucket, and `n = |by_op[f]|`, absent for a
single-lookup `ByOp` scan, which is never demoted.

`demoteByOp` transcribes the decision (`usize` saturating products are
`Nat` products: they differ only past `2^64`, where the decision changes
and, by the theorem below, the candidates do not). `placeByOp_eq` says
the candidate set is the same for every policy and every pair of sizes.
-/

namespace Semper.EMatch.Fidelity

open Semper.EMatch

/-- `OpFilterPolicy`, `ematch.rs:2651`. -/
inductive OpFilterPolicy where
  | adaptive
  | alwaysFilter
  | alwaysLeapfrog
  deriving DecidableEq, Repr

/-- `OP_FILTER_RELATION_PER_CANDIDATE`, `OP_FILTER_MIN_RELATION`,
`OP_FILTER_SEEK_COST` (`ematch.rs:2635-2647`). -/
def opFilterRelationPerCandidate : Nat := 512
def opFilterMinRelation : Nat := 131072
def opFilterSeekCost : Nat := 2

/-- `demote_by_op` (`ematch.rs:2723-2735`). -/
def demoteByOp (m : Nat) (n : Option Nat) : OpFilterPolicy → Bool
  | p => match n with
    | none => false
    | some n => match p with
      | .alwaysFilter => true
      | .alwaysLeapfrog => false
      | .adaptive =>
          decide (min opFilterMinRelation (m * opFilterRelationPerCandidate) ≤ n) &&
            decide (m ≤ n * opFilterSeekCost)

/-- The join's candidates with its `ByOp f` restriction placed as decided:
demoted, the other lookups are joined and each candidate is tested against
the operator table; kept, the restriction is one more operand. -/
def placeByOp (G : Graph) (σ : Binding) (ls : List Lookup) (f : Sym) (demote : Bool) :
    List NodeId :=
  if demote then (candidates G σ (ls.erase (.byOp f))).filter (fun id => decide (G.op id = some f))
  else candidates G σ ls

/-- The candidate set does not depend on the placement. -/
theorem placeByOp_eq (G : Graph) (σ : Binding) (ls : List Lookup) (f : Sym)
    (hk : G.KeysNodup) (hop : Lookup.byOp f ∈ ls) (demote : Bool) :
    placeByOp G σ ls f demote = candidates G σ ls := by
  cases demote
  · rfl
  · exact (byOp_demotion_op G σ ls f hk hop).symm

/-- For every policy and every pair of bucket sizes, the engine's join reads
the candidate set of the model's `candidates`. -/
theorem policy_candidates_eq (G : Graph) (σ : Binding) (ls : List Lookup) (f : Sym)
    (hk : G.KeysNodup) (hop : Lookup.byOp f ∈ ls) (p : OpFilterPolicy) (m : Nat) (n : Option Nat) :
    placeByOp G σ ls f (demoteByOp m n p) = candidates G σ ls :=
  placeByOp_eq G σ ls f hk hop _

/-- Two policies give the same candidates. -/
theorem policy_independent (G : Graph) (σ : Binding) (ls : List Lookup) (f : Sym)
    (hk : G.KeysNodup) (hop : Lookup.byOp f ∈ ls) (p q : OpFilterPolicy) (m m' : Nat)
    (n n' : Option Nat) :
    placeByOp G σ ls f (demoteByOp m n p) = placeByOp G σ ls f (demoteByOp m' n' q) := by
  rw [policy_candidates_eq G σ ls f hk hop, policy_candidates_eq G σ ls f hk hop]

/-- A single-lookup `ByOp` scan (`n = none`) is never demoted. -/
theorem demoteByOp_none (m : Nat) (p : OpFilterPolicy) : demoteByOp m none p = false := rfl

end Semper.EMatch.Fidelity
