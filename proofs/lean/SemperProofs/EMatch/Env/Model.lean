import SemperProofs.EMatch.Ref

/-!
# The engine's mutable match environment (`Match`, `ematch.rs:171-411`)

`Env` models the fields of `Match` the core steps read and write
(spec `spec-steps-env.md`, A.0 and B.2):

* `nodes[v] : Option<G>`: one slot per variable, holding a node id; a class
  variable is a slot read through `canon` (the Lean `G.find`, section D);
* `mults[k] : M`, with `ZERO` meaning unbound (`ematch.rs:2329-2336`);
* the three rest pools: a packed `Vec` plus a span `(start, len)` per rest
  variable; `push_*` appends at the tail and sets the span, `pop_*`
  truncates the pool to the span's start and resets the span to
  `empty_span = (0, 0)` (`ematch.rs:109-113`, `337-345`).

A span is modelled as `Option (Nat × Nat)`, `none` standing for the
engine's `empty_span`. The engine does not distinguish an unbound rest
from a rest bound to the empty slice at offset 0 (both `(0, 0)`); the model
does, and this only matters for a plan that reads a rest it never bound,
which `WF` (below) excludes.

Literal slots (`lit_vals`, `lit_seq_pool`) and `Collect` are out of scope
(spec B.2: the only fields `(Restore)` does not cover).

The abstraction `abs G κ : Env → Binding` (spec B.4) reads every slot as a
class through `find` (`σ.cls`), and the slots of node variables also as
node ids (`σ.node`): the engine has one namespace for both
(`ematch.rs:1893-1896`, spec A.0.1) while `Binding` keeps two maps, and
the reference `joinBind` writes both of a join target while `ExtractChild`
and the decompositions write only `cls`. The classification `κ`
(`κ v = true` for a node variable) decides which slots feed `σ.node`.
-/

namespace Semper.EMatch.Env

open Semper.EMatch

/-- A pool span `(start, len)`. -/
abbrev Span := Nat × Nat

/-- The engine's `Match`, restricted to the fields of the core steps. -/
@[ext]
structure Env where
  nodes : Var → Option NodeId
  mults : Var → Nat
  seqPool : List C
  seqSpan : Var → Option Span
  setPool : List C
  setSpan : Var → Option Span
  msetPool : List (C × Nat)
  msetSpan : Var → Option Span

namespace Env

/-- `Match::new`: everything unbound. -/
def empty : Env :=
  ⟨fun _ => none, fun _ => 0, [], fun _ => none, [], fun _ => none, [], fun _ => none⟩

/-- `Match::set`. -/
def set (e : Env) (x : Var) (g : NodeId) : Env :=
  { e with nodes := Function.update e.nodes x (some g) }

/-- `Match::clear`. -/
def clear (e : Env) (x : Var) : Env :=
  { e with nodes := Function.update e.nodes x none }

/-- `Match::set_opt` (the join's save/restore of its target). -/
def setOpt (e : Env) (x : Var) (v : Option NodeId) : Env :=
  { e with nodes := Function.update e.nodes x v }

/-- `Match::set_mult`. -/
def setMult (e : Env) (k : Var) (m : Nat) : Env :=
  { e with mults := Function.update e.mults k m }

/-- The start of a span, `0` for `empty_span`. -/
def spanStart : Option Span → Nat
  | none => 0
  | some (s, _) => s

/-- `Match::push_seq`. -/
def pushSeq (e : Env) (r : Var) (d : List C) : Env :=
  { e with seqPool := e.seqPool ++ d,
           seqSpan := Function.update e.seqSpan r (some (e.seqPool.length, d.length)) }

/-- `Match::pop_seq`: truncate to the span's start, reset the span. -/
def popSeq (e : Env) (r : Var) : Env :=
  { e with seqPool := e.seqPool.take (spanStart (e.seqSpan r)),
           seqSpan := Function.update e.seqSpan r none }

/-- `Match::push_set` / `push_set_residual`. -/
def pushSet (e : Env) (r : Var) (d : List C) : Env :=
  { e with setPool := e.setPool ++ d,
           setSpan := Function.update e.setSpan r (some (e.setPool.length, d.length)) }

/-- `Match::pop_set`. -/
def popSet (e : Env) (r : Var) : Env :=
  { e with setPool := e.setPool.take (spanStart (e.setSpan r)),
           setSpan := Function.update e.setSpan r none }

/-- `Match::push_mset_residual` (the caller filters the zero entries). -/
def pushMset (e : Env) (r : Var) (d : List (C × Nat)) : Env :=
  { e with msetPool := e.msetPool ++ d,
           msetSpan := Function.update e.msetSpan r (some (e.msetPool.length, d.length)) }

/-- `Match::pop_mset`. -/
def popMset (e : Env) (r : Var) : Env :=
  { e with msetPool := e.msetPool.take (spanStart (e.msetSpan r)),
           msetSpan := Function.update e.msetSpan r none }

/-- The slice a span denotes (`seq_slice` etc.), `none` for `empty_span`. -/
def slice {α : Type} (pool : List α) : Option Span → Option (List α)
  | none => none
  | some (s, l) => some ((pool.drop s).take l)

/-- The node bound to a node variable. -/
def nodeOf (e : Env) (G : Graph) (v : Var) : Option Node :=
  (e.nodes v).bind G.lookupNode

/-! ### Basic algebra of the writes -/

@[simp] theorem set_nodes (e : Env) (x : Var) (g : NodeId) :
    (e.set x g).nodes = Function.update e.nodes x (some g) := rfl
@[simp] theorem set_mults (e : Env) (x : Var) (g : NodeId) : (e.set x g).mults = e.mults := rfl
@[simp] theorem set_seqPool (e : Env) (x : Var) (g : NodeId) : (e.set x g).seqPool = e.seqPool := rfl
@[simp] theorem set_seqSpan (e : Env) (x : Var) (g : NodeId) : (e.set x g).seqSpan = e.seqSpan := rfl
@[simp] theorem set_setPool (e : Env) (x : Var) (g : NodeId) : (e.set x g).setPool = e.setPool := rfl
@[simp] theorem set_setSpan (e : Env) (x : Var) (g : NodeId) : (e.set x g).setSpan = e.setSpan := rfl
@[simp] theorem set_msetPool (e : Env) (x : Var) (g : NodeId) : (e.set x g).msetPool = e.msetPool := rfl
@[simp] theorem set_msetSpan (e : Env) (x : Var) (g : NodeId) : (e.set x g).msetSpan = e.msetSpan := rfl

@[simp] theorem clear_nodes (e : Env) (x : Var) :
    (e.clear x).nodes = Function.update e.nodes x none := rfl
@[simp] theorem clear_mults (e : Env) (x : Var) : (e.clear x).mults = e.mults := rfl
@[simp] theorem clear_seqPool (e : Env) (x : Var) : (e.clear x).seqPool = e.seqPool := rfl
@[simp] theorem clear_seqSpan (e : Env) (x : Var) : (e.clear x).seqSpan = e.seqSpan := rfl
@[simp] theorem clear_setPool (e : Env) (x : Var) : (e.clear x).setPool = e.setPool := rfl
@[simp] theorem clear_setSpan (e : Env) (x : Var) : (e.clear x).setSpan = e.setSpan := rfl
@[simp] theorem clear_msetPool (e : Env) (x : Var) : (e.clear x).msetPool = e.msetPool := rfl
@[simp] theorem clear_msetSpan (e : Env) (x : Var) : (e.clear x).msetSpan = e.msetSpan := rfl

@[simp] theorem setOpt_nodes (e : Env) (x : Var) (v : Option NodeId) :
    (e.setOpt x v).nodes = Function.update e.nodes x v := rfl
@[simp] theorem setOpt_mults (e : Env) (x : Var) (v : Option NodeId) : (e.setOpt x v).mults = e.mults := rfl
@[simp] theorem setOpt_seqPool (e : Env) (x : Var) (v : Option NodeId) : (e.setOpt x v).seqPool = e.seqPool := rfl
@[simp] theorem setOpt_seqSpan (e : Env) (x : Var) (v : Option NodeId) : (e.setOpt x v).seqSpan = e.seqSpan := rfl
@[simp] theorem setOpt_setPool (e : Env) (x : Var) (v : Option NodeId) : (e.setOpt x v).setPool = e.setPool := rfl
@[simp] theorem setOpt_setSpan (e : Env) (x : Var) (v : Option NodeId) : (e.setOpt x v).setSpan = e.setSpan := rfl
@[simp] theorem setOpt_msetPool (e : Env) (x : Var) (v : Option NodeId) : (e.setOpt x v).msetPool = e.msetPool := rfl
@[simp] theorem setOpt_msetSpan (e : Env) (x : Var) (v : Option NodeId) : (e.setOpt x v).msetSpan = e.msetSpan := rfl

@[simp] theorem setMult_nodes (e : Env) (k m : Nat) : (e.setMult k m).nodes = e.nodes := rfl
@[simp] theorem setMult_mults (e : Env) (k m : Nat) :
    (e.setMult k m).mults = Function.update e.mults k m := rfl
@[simp] theorem setMult_seqPool (e : Env) (k m : Nat) : (e.setMult k m).seqPool = e.seqPool := rfl
@[simp] theorem setMult_seqSpan (e : Env) (k m : Nat) : (e.setMult k m).seqSpan = e.seqSpan := rfl
@[simp] theorem setMult_setPool (e : Env) (k m : Nat) : (e.setMult k m).setPool = e.setPool := rfl
@[simp] theorem setMult_setSpan (e : Env) (k m : Nat) : (e.setMult k m).setSpan = e.setSpan := rfl
@[simp] theorem setMult_msetPool (e : Env) (k m : Nat) : (e.setMult k m).msetPool = e.msetPool := rfl
@[simp] theorem setMult_msetSpan (e : Env) (k m : Nat) : (e.setMult k m).msetSpan = e.msetSpan := rfl

@[simp] theorem pushSeq_nodes (e : Env) (r : Var) (d : List C) : (e.pushSeq r d).nodes = e.nodes := rfl
@[simp] theorem pushSeq_mults (e : Env) (r : Var) (d : List C) : (e.pushSeq r d).mults = e.mults := rfl
@[simp] theorem pushSeq_seqPool (e : Env) (r : Var) (d : List C) :
    (e.pushSeq r d).seqPool = e.seqPool ++ d := rfl
@[simp] theorem pushSeq_seqSpan (e : Env) (r : Var) (d : List C) :
    (e.pushSeq r d).seqSpan = Function.update e.seqSpan r (some (e.seqPool.length, d.length)) := rfl
@[simp] theorem pushSeq_setPool (e : Env) (r : Var) (d : List C) : (e.pushSeq r d).setPool = e.setPool := rfl
@[simp] theorem pushSeq_setSpan (e : Env) (r : Var) (d : List C) : (e.pushSeq r d).setSpan = e.setSpan := rfl
@[simp] theorem pushSeq_msetPool (e : Env) (r : Var) (d : List C) : (e.pushSeq r d).msetPool = e.msetPool := rfl
@[simp] theorem pushSeq_msetSpan (e : Env) (r : Var) (d : List C) : (e.pushSeq r d).msetSpan = e.msetSpan := rfl

@[simp] theorem pushSet_nodes (e : Env) (r : Var) (d : List C) : (e.pushSet r d).nodes = e.nodes := rfl
@[simp] theorem pushSet_mults (e : Env) (r : Var) (d : List C) : (e.pushSet r d).mults = e.mults := rfl
@[simp] theorem pushSet_seqPool (e : Env) (r : Var) (d : List C) : (e.pushSet r d).seqPool = e.seqPool := rfl
@[simp] theorem pushSet_seqSpan (e : Env) (r : Var) (d : List C) : (e.pushSet r d).seqSpan = e.seqSpan := rfl
@[simp] theorem pushSet_setPool (e : Env) (r : Var) (d : List C) :
    (e.pushSet r d).setPool = e.setPool ++ d := rfl
@[simp] theorem pushSet_setSpan (e : Env) (r : Var) (d : List C) :
    (e.pushSet r d).setSpan = Function.update e.setSpan r (some (e.setPool.length, d.length)) := rfl
@[simp] theorem pushSet_msetPool (e : Env) (r : Var) (d : List C) : (e.pushSet r d).msetPool = e.msetPool := rfl
@[simp] theorem pushSet_msetSpan (e : Env) (r : Var) (d : List C) : (e.pushSet r d).msetSpan = e.msetSpan := rfl

@[simp] theorem pushMset_nodes (e : Env) (r : Var) (d : List (C × Nat)) : (e.pushMset r d).nodes = e.nodes := rfl
@[simp] theorem pushMset_mults (e : Env) (r : Var) (d : List (C × Nat)) : (e.pushMset r d).mults = e.mults := rfl
@[simp] theorem pushMset_seqPool (e : Env) (r : Var) (d : List (C × Nat)) : (e.pushMset r d).seqPool = e.seqPool := rfl
@[simp] theorem pushMset_seqSpan (e : Env) (r : Var) (d : List (C × Nat)) : (e.pushMset r d).seqSpan = e.seqSpan := rfl
@[simp] theorem pushMset_setPool (e : Env) (r : Var) (d : List (C × Nat)) : (e.pushMset r d).setPool = e.setPool := rfl
@[simp] theorem pushMset_setSpan (e : Env) (r : Var) (d : List (C × Nat)) : (e.pushMset r d).setSpan = e.setSpan := rfl
@[simp] theorem pushMset_msetPool (e : Env) (r : Var) (d : List (C × Nat)) :
    (e.pushMset r d).msetPool = e.msetPool ++ d := rfl
@[simp] theorem pushMset_msetSpan (e : Env) (r : Var) (d : List (C × Nat)) :
    (e.pushMset r d).msetSpan = Function.update e.msetSpan r (some (e.msetPool.length, d.length)) := rfl

@[simp] theorem nodeOf_set_ne (e : Env) (G : Graph) (v x : Var) (g : NodeId) (h : x ≠ v) :
    (e.set x g).nodeOf G v = e.nodeOf G v := by
  simp [nodeOf, Function.update_of_ne h.symm]

@[simp] theorem nodeOf_setMult (e : Env) (G : Graph) (v k m : Nat) :
    (e.setMult k m).nodeOf G v = e.nodeOf G v := rfl
@[simp] theorem nodeOf_pushSeq (e : Env) (G : Graph) (v r : Var) (d : List C) :
    (e.pushSeq r d).nodeOf G v = e.nodeOf G v := rfl
@[simp] theorem nodeOf_pushSet (e : Env) (G : Graph) (v r : Var) (d : List C) :
    (e.pushSet r d).nodeOf G v = e.nodeOf G v := rfl
@[simp] theorem nodeOf_pushMset (e : Env) (G : Graph) (v r : Var) (d : List (C × Nat)) :
    (e.pushMset r d).nodeOf G v = e.nodeOf G v := rfl

/-- `clear` after `set` of an unbound slot is the identity (`ExtractChild`,
`BindGlobal`, the unbound paths of the decompositions). -/
theorem clear_set (e : Env) (x : Var) (g : NodeId) (h : e.nodes x = none) :
    (e.set x g).clear x = e := by
  ext1 <;> simp [Function.update_idem, Function.update_eq_self_iff, h]

/-- `set_opt(target, prev)` after any number of `set(target, _)` restores
the slot (`leapfrog_join`, `ematch.rs:2966-2977`). -/
theorem setOpt_set (e : Env) (x : Var) (g : NodeId) :
    (e.set x g).setOpt x (e.nodes x) = e := by
  ext1 <;> simp [Function.update_idem]

theorem setOpt_self (e : Env) (x : Var) : e.setOpt x (e.nodes x) = e := by
  ext1 <;> simp

theorem set_of_setOpt_eq {e e' : Env} {x : Var} {p : Option NodeId}
    (h : e'.setOpt x p = e) (g : NodeId) : e'.set x g = e.set x g := by
  subst h; ext1 <;> simp [Function.update_idem]

theorem setOpt_set_of_setOpt_eq {e e' : Env} {x : Var} {p : Option NodeId}
    (h : e'.setOpt x p = e) (g : NodeId) : (e'.set x g).setOpt x p = e := by
  subst h; ext1 <;> simp [Function.update_idem]

/-- The `was_unbound` reset (`ematch.rs:2439`, `2486`): zeroing after a
write to a zero slot is the identity. -/
theorem setMult_zero_setMult (e : Env) (k m : Nat) (h : e.mults k = 0) :
    (e.setMult k m).setMult k 0 = e := by
  ext1 <;> simp [Function.update_idem, Function.update_eq_self_iff, h]

/-- Re-writing a bound multiplicity with its own value is the identity (the
bound path of `decompose_ac_elem` when `mult_matches` forced `actual = prev`). -/
theorem setMult_self (e : Env) (k : Nat) : e.setMult k (e.mults k) = e := by
  ext1 <;> simp

theorem popSeq_pushSeq (e : Env) (r : Var) (d : List C) (h : e.seqSpan r = none) :
    (e.pushSeq r d).popSeq r = e := by
  ext1 <;> simp [popSeq, spanStart, Function.update_idem, Function.update_eq_self_iff, h,
    List.take_left]

theorem popSet_pushSet (e : Env) (r : Var) (d : List C) (h : e.setSpan r = none) :
    (e.pushSet r d).popSet r = e := by
  ext1 <;> simp [popSet, spanStart, Function.update_idem, Function.update_eq_self_iff, h,
    List.take_left]

theorem popMset_pushMset (e : Env) (r : Var) (d : List (C × Nat)) (h : e.msetSpan r = none) :
    (e.pushMset r d).popMset r = e := by
  ext1 <;> simp [popMset, spanStart, Function.update_idem, Function.update_eq_self_iff, h,
    List.take_left]

/-- Writes to other fields commute with `set`; used to push `set` past the
multiplicity write of the AC unbound path. -/
theorem setMult_set (e : Env) (x : Var) (g : NodeId) (k m : Nat) :
    (e.set x g).setMult k m = (e.setMult k m).set x g := rfl

end Env

/-! ## Well-formed pools: every live span lies inside its pool -/

/-- Every live span lies within its pool. `push` preserves it; `pop` after
a `push` whose continuation restored the environment preserves it because
the result *is* the environment before the push. -/
structure SpansOk (e : Env) : Prop where
  seq : ∀ r s l, e.seqSpan r = some (s, l) → s + l ≤ e.seqPool.length
  fin : ∀ r s l, e.setSpan r = some (s, l) → s + l ≤ e.setPool.length
  mset : ∀ r s l, e.msetSpan r = some (s, l) → s + l ≤ e.msetPool.length

namespace SpansOk

theorem set {e : Env} (h : SpansOk e) (x : Var) (g : NodeId) : SpansOk (e.set x g) :=
  ⟨h.seq, h.fin, h.mset⟩
theorem clear {e : Env} (h : SpansOk e) (x : Var) : SpansOk (e.clear x) :=
  ⟨h.seq, h.fin, h.mset⟩
theorem setOpt {e : Env} (h : SpansOk e) (x : Var) (v : Option NodeId) : SpansOk (e.setOpt x v) :=
  ⟨h.seq, h.fin, h.mset⟩
theorem setMult {e : Env} (h : SpansOk e) (k m : Nat) : SpansOk (e.setMult k m) :=
  ⟨h.seq, h.fin, h.mset⟩

theorem pushSeq {e : Env} (h : SpansOk e) (r : Var) (d : List C) : SpansOk (e.pushSeq r d) := by
  refine ⟨?_, h.fin, h.mset⟩
  intro r' s l hs
  simp only [Env.pushSeq_seqSpan, Env.pushSeq_seqPool, List.length_append] at hs ⊢
  by_cases hr : r' = r
  · subst hr; simp at hs; omega
  · rw [Function.update_of_ne hr] at hs; have := h.seq r' s l hs; omega

theorem pushSet {e : Env} (h : SpansOk e) (r : Var) (d : List C) : SpansOk (e.pushSet r d) := by
  refine ⟨h.seq, ?_, h.mset⟩
  intro r' s l hs
  simp only [Env.pushSet_setSpan, Env.pushSet_setPool, List.length_append] at hs ⊢
  by_cases hr : r' = r
  · subst hr; simp at hs; omega
  · rw [Function.update_of_ne hr] at hs; have := h.fin r' s l hs; omega

theorem pushMset {e : Env} (h : SpansOk e) (r : Var) (d : List (C × Nat)) :
    SpansOk (e.pushMset r d) := by
  refine ⟨h.seq, h.fin, ?_⟩
  intro r' s l hs
  simp only [Env.pushMset_msetSpan, Env.pushMset_msetPool, List.length_append] at hs ⊢
  by_cases hr : r' = r
  · subst hr; simp at hs; omega
  · rw [Function.update_of_ne hr] at hs; have := h.mset r' s l hs; omega

end SpansOk

theorem slice_append_of_le {α : Type} (pool d : List α) (s l : Nat) (h : s + l ≤ pool.length) :
    Env.slice (pool ++ d) (some (s, l)) = Env.slice pool (some (s, l)) := by
  simp only [Env.slice]
  rw [List.drop_append_of_le_length (by omega), List.take_append_of_le_length]
  simp; omega

theorem slice_push {α : Type} (pool d : List α) :
    Env.slice (pool ++ d) (some (pool.length, d.length)) = some d := by
  simp [Env.slice]

/-! ## The abstraction (spec B.4) -/

/-- `abs G κ e`: every slot read as a class through `find`, node variables
also read raw, multiplicity `0` as unbound, rests as the slices of their
spans. -/
def abs (G : Graph) (κ : Var → Bool) (e : Env) : Binding where
  cls := fun x => (e.nodes x).map G.find
  node := fun v => if κ v then e.nodes v else none
  mult := fun k => if e.mults k = 0 then none else some (e.mults k)
  rest := fun r => (Env.slice e.msetPool (e.msetSpan r)).map ofEntries
  seqRest := fun r => Env.slice e.seqPool (e.seqSpan r)
  finRest := fun r => (Env.slice e.setPool (e.setSpan r)).map List.toFinset

theorem Binding.ext' {σ σ' : Binding} (h1 : σ.cls = σ'.cls) (h2 : σ.node = σ'.node)
    (h3 : σ.mult = σ'.mult) (h4 : σ.rest = σ'.rest) (h5 : σ.seqRest = σ'.seqRest)
    (h6 : σ.finRest = σ'.finRest) : σ = σ' := by
  cases σ; cases σ'; simp_all

@[simp] theorem abs_cls (G : Graph) (κ : Var → Bool) (e : Env) (x : Var) :
    (abs G κ e).cls x = (e.nodes x).map G.find := rfl
@[simp] theorem abs_node (G : Graph) (κ : Var → Bool) (e : Env) (v : Var) :
    (abs G κ e).node v = if κ v then e.nodes v else none := rfl
@[simp] theorem abs_mult (G : Graph) (κ : Var → Bool) (e : Env) (k : Var) :
    (abs G κ e).mult k = if e.mults k = 0 then none else some (e.mults k) := rfl
@[simp] theorem abs_rest (G : Graph) (κ : Var → Bool) (e : Env) (r : Var) :
    (abs G κ e).rest r = (Env.slice e.msetPool (e.msetSpan r)).map ofEntries := rfl
@[simp] theorem abs_seqRest (G : Graph) (κ : Var → Bool) (e : Env) (r : Var) :
    (abs G κ e).seqRest r = Env.slice e.seqPool (e.seqSpan r) := rfl
@[simp] theorem abs_finRest (G : Graph) (κ : Var → Bool) (e : Env) (r : Var) :
    (abs G κ e).finRest r = (Env.slice e.setPool (e.setSpan r)).map List.toFinset := rfl

theorem abs_nodeOf (G : Graph) (κ : Var → Bool) (e : Env) (v : Var) (hv : κ v = true) :
    (abs G κ e).nodeOf G v = e.nodeOf G v := by
  simp [Binding.nodeOf, Env.nodeOf, hv]

/-- The abstraction satisfies the reference invariant `NodeCls`. -/
theorem abs_nodeCls (G : Graph) (κ : Var → Bool) (e : Env) : NodeCls G (abs G κ e) := by
  intro v id h
  simp only [abs_node] at h
  split at h
  · simp [h]
  · cases h

/-- `nodes[t] := id` on a node variable is the reference `joinBind`. -/
theorem abs_set_node (G : Graph) (κ : Var → Bool) (e : Env) (t : Var) (id : NodeId)
    (ht : κ t = true) : abs G κ (e.set t id) = joinBind G (abs G κ e) t id := by
  refine Binding.ext' ?_ ?_ rfl rfl rfl rfl <;> funext x
  · simp only [joinBind, Binding.setNode, Binding.setCls, abs_cls, Env.set_nodes]
    by_cases h : x = t
    · subst h; simp
    · simp [Function.update_of_ne h]
  · simp only [joinBind, Binding.setNode, Binding.setCls, abs_node, Env.set_nodes]
    by_cases h : x = t
    · subst h; simp [ht]
    · simp [Function.update_of_ne h]

/-- `nodes[x] := c` on a class variable holding a canonical class. -/
theorem abs_set_cls (G : Graph) (κ : Var → Bool) (e : Env) (x : Var) (c : C)
    (hx : κ x = false) (hc : G.find c = c) :
    abs G κ (e.set x c) = (abs G κ e).setCls x c := by
  refine Binding.ext' ?_ ?_ rfl rfl rfl rfl <;> funext y
  · simp only [Binding.setCls, abs_cls, Env.set_nodes]
    by_cases h : y = x
    · subst h; simp [hc]
    · simp [Function.update_of_ne h]
  · simp only [Binding.setCls, abs_node, Env.set_nodes]
    by_cases h : y = x
    · subst h; simp [hx]
    · simp [Function.update_of_ne h]

theorem abs_setMult (G : Graph) (κ : Var → Bool) (e : Env) (k m : Nat) (hm : m ≠ 0) :
    abs G κ (e.setMult k m) = (abs G κ e).setMult k m := by
  refine Binding.ext' rfl rfl ?_ rfl rfl rfl
  funext y
  simp only [Binding.setMult, abs_mult, Env.setMult_mults]
  by_cases h : y = k
  · subst h; simp [hm]
  · simp [Function.update_of_ne h]

theorem abs_pushSeq (G : Graph) (κ : Var → Bool) (e : Env) (r : Var) (d : List C)
    (hok : SpansOk e) : abs G κ (e.pushSeq r d) = (abs G κ e).setSeqRest r d := by
  refine Binding.ext' rfl rfl rfl rfl ?_ rfl
  funext y
  simp only [Binding.setSeqRest, abs_seqRest, Env.pushSeq_seqPool, Env.pushSeq_seqSpan]
  by_cases h : y = r
  · subst h; simp [slice_push]
  · rw [Function.update_of_ne h, Function.update_of_ne h, abs_seqRest]
    cases hs : e.seqSpan y with
    | none => rfl
    | some sl => obtain ⟨s, l⟩ := sl; exact slice_append_of_le _ _ _ _ (hok.seq y s l hs)

theorem abs_pushSet (G : Graph) (κ : Var → Bool) (e : Env) (r : Var) (d : List C)
    (hok : SpansOk e) : abs G κ (e.pushSet r d) = (abs G κ e).setSetRest r d.toFinset := by
  refine Binding.ext' rfl rfl rfl rfl rfl ?_
  funext y
  simp only [Binding.setSetRest, abs_finRest, Env.pushSet_setPool, Env.pushSet_setSpan]
  by_cases h : y = r
  · subst h; simp [slice_push]
  · rw [Function.update_of_ne h, Function.update_of_ne h, abs_finRest]
    cases hs : e.setSpan y with
    | none => rfl
    | some sl =>
        obtain ⟨s, l⟩ := sl
        rw [slice_append_of_le _ _ _ _ (hok.fin y s l hs)]

theorem abs_pushMset (G : Graph) (κ : Var → Bool) (e : Env) (r : Var) (d : List (C × Nat))
    (hok : SpansOk e) : abs G κ (e.pushMset r d) = (abs G κ e).setRest r (ofEntries d) := by
  refine Binding.ext' rfl rfl rfl ?_ rfl rfl
  funext y
  simp only [Binding.setRest, abs_rest, Env.pushMset_msetPool, Env.pushMset_msetSpan]
  by_cases h : y = r
  · subst h; simp [slice_push]
  · rw [Function.update_of_ne h, Function.update_of_ne h, abs_rest]
    cases hs : e.msetSpan y with
    | none => rfl
    | some sl =>
        obtain ⟨s, l⟩ := sl
        rw [slice_append_of_le _ _ _ _ (hok.mset y s l hs)]

/-! ## Bounded environments: only the variables of `B` are bound -/

/-- `Bounded e B`: every slot outside `B` is unbound (nodes `None`,
multiplicities `ZERO`, spans empty). The refinement theorem assumes it of
the entry environment with `B` the plan's bound set, and it is the
precise form of the engine's write-once discipline: a step writing a
variable outside `B` finds it unbound, so `clear`/`pop` restore it. -/
structure Bounded (e : Env) (B : List Var) : Prop where
  nodes : ∀ x, x ∉ B → e.nodes x = none
  mults : ∀ k, k ∉ B → e.mults k = 0
  seq : ∀ r, r ∉ B → e.seqSpan r = none
  fin : ∀ r, r ∉ B → e.setSpan r = none
  mset : ∀ r, r ∉ B → e.msetSpan r = none

namespace Bounded

theorem mono {e : Env} {B B' : List Var} (h : Bounded e B) (hB : ∀ x ∈ B, x ∈ B') :
    Bounded e B' :=
  ⟨fun x hx => h.nodes x (fun h' => hx (hB x h')),
   fun k hk => h.mults k (fun h' => hk (hB k h')),
   fun r hr => h.seq r (fun h' => hr (hB r h')),
   fun r hr => h.fin r (fun h' => hr (hB r h')),
   fun r hr => h.mset r (fun h' => hr (hB r h'))⟩

theorem cons {e : Env} {B : List Var} (h : Bounded e B) (x : Var) : Bounded e (x :: B) :=
  h.mono (fun y hy => List.mem_cons_of_mem x hy)

theorem append_left {e : Env} {B : List Var} (h : Bounded e B) (B' : List Var) :
    Bounded e (B' ++ B) :=
  h.mono (fun y hy => List.mem_append_right B' hy)

theorem set {e : Env} {B : List Var} (h : Bounded e B) {x : Var} (hx : x ∈ B) (g : NodeId) :
    Bounded (e.set x g) B := by
  refine ⟨?_, h.mults, h.seq, h.fin, h.mset⟩
  intro y hy
  have hne : y ≠ x := fun h' => hy (h' ▸ hx)
  simp [Function.update_of_ne hne, h.nodes y hy]

theorem setOpt {e : Env} {B : List Var} (h : Bounded e B) {x : Var} (hx : x ∈ B)
    (v : Option NodeId) : Bounded (e.setOpt x v) B := by
  refine ⟨?_, h.mults, h.seq, h.fin, h.mset⟩
  intro y hy
  have hne : y ≠ x := fun h' => hy (h' ▸ hx)
  simp [Function.update_of_ne hne, h.nodes y hy]

theorem clear {e : Env} {B : List Var} (h : Bounded e B) (x : Var) : Bounded (e.clear x) B := by
  refine ⟨?_, h.mults, h.seq, h.fin, h.mset⟩
  intro y hy
  by_cases hne : y = x
  · subst hne; simp
  · simp [Function.update_of_ne hne, h.nodes y hy]

theorem setMult {e : Env} {B : List Var} (h : Bounded e B) {k : Var} (hk : k ∈ B) (m : Nat) :
    Bounded (e.setMult k m) B := by
  refine ⟨h.nodes, ?_, h.seq, h.fin, h.mset⟩
  intro y hy
  have hne : y ≠ k := fun h' => hy (h' ▸ hk)
  simp [Function.update_of_ne hne, h.mults y hy]

theorem pushSeq {e : Env} {B : List Var} (h : Bounded e B) {r : Var} (hr : r ∈ B) (d : List C) :
    Bounded (e.pushSeq r d) B := by
  refine ⟨h.nodes, h.mults, ?_, h.fin, h.mset⟩
  intro y hy
  have hne : y ≠ r := fun h' => hy (h' ▸ hr)
  simp [Function.update_of_ne hne, h.seq y hy]

theorem pushSet {e : Env} {B : List Var} (h : Bounded e B) {r : Var} (hr : r ∈ B) (d : List C) :
    Bounded (e.pushSet r d) B := by
  refine ⟨h.nodes, h.mults, h.seq, ?_, h.mset⟩
  intro y hy
  have hne : y ≠ r := fun h' => hy (h' ▸ hr)
  simp [Function.update_of_ne hne, h.fin y hy]

theorem pushMset {e : Env} {B : List Var} (h : Bounded e B) {r : Var} (hr : r ∈ B)
    (d : List (C × Nat)) : Bounded (e.pushMset r d) B := by
  refine ⟨h.nodes, h.mults, h.seq, h.fin, ?_⟩
  intro y hy
  have hne : y ≠ r := fun h' => hy (h' ▸ hr)
  simp [Function.update_of_ne hne, h.mset y hy]

end Bounded

/-- The entry invariant of the refinement: bounded by `B` and well-formed pools. -/
structure EnvOk (e : Env) (B : List Var) : Prop where
  bounded : Bounded e B
  spans : SpansOk e

theorem EnvOk.empty : EnvOk Env.empty [] :=
  ⟨⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩,
   ⟨fun _ _ _ h => by simp [Env.empty] at h, fun _ _ _ h => by simp [Env.empty] at h,
    fun _ _ _ h => by simp [Env.empty] at h⟩⟩

/-! ## Canonical children (spec D, H2) -/

/-- The stored children of a node are canonical for `find`. -/
def _root_.Semper.EMatch.Children.Canon (G : Graph) : Children → Prop
  | .tuple cs => ∀ c ∈ cs, G.find c = c
  | .spair a b => G.find a = a ∧ G.find b = b
  | .seq cs => ∀ c ∈ cs, G.find c = c
  | .mset m => ∀ c ∈ m, G.find c = c
  | .set s => ∀ c ∈ s, G.find c = c

/-- `find` is idempotent: `round_repr` returns representatives (spec D, H1). -/
def _root_.Semper.EMatch.Graph.FindIdem (G : Graph) : Prop :=
  ∀ id, G.find (G.find id) = G.find id

/-- H2 (spec D): after `rebuild`, every stored child class is a `find`
fixed point. -/
def _root_.Semper.EMatch.Graph.ChildrenCanon (G : Graph) : Prop :=
  ∀ p ∈ G.nodes, Children.Canon G p.2.children

theorem Children.Canon.childAt {G : Graph} {ch : Children} (h : Children.Canon G ch)
    {pos : Nat} {c : C} (hc : ch.childAt pos = some c) : G.find c = c := by
  cases ch with
  | tuple cs => exact h c (List.mem_of_getElem? hc)
  | seq cs => exact h c (List.mem_of_getElem? hc)
  | spair a b =>
      cases pos with
      | zero => simp [Children.childAt] at hc; subst hc; exact h.1
      | succ n =>
          cases n with
          | zero => simp [Children.childAt] at hc; subst hc; exact h.2
          | succ n => simp [Children.childAt] at hc
  | mset m => simp [Children.childAt] at hc
  | set s => simp [Children.childAt] at hc

theorem mem_of_lookupNode' {G : Graph} {id : NodeId} {n : Node} (h : G.lookupNode id = some n) :
    (id, n) ∈ G.nodes := by
  unfold Graph.lookupNode at h
  cases hf : G.nodes.find? (fun p => p.1 = id) with
  | none => simp [hf] at h
  | some p =>
      simp only [hf, Option.map_some, Option.some.injEq] at h
      have hp := List.mem_of_find?_eq_some hf
      have hp1 := List.find?_some hf
      obtain ⟨a, b⟩ := p
      simp only [decide_eq_true_eq] at hp1
      simp only at h
      subst hp1; subst h; exact hp

theorem nodeOf_canon {G : Graph} (hG : G.ChildrenCanon) {e : Env} {v : Var} {n : Node}
    (h : e.nodeOf G v = some n) : Children.Canon G n.children := by
  unfold Env.nodeOf at h
  cases hv : e.nodes v with
  | none => simp [hv] at h
  | some id =>
      simp [hv] at h
      exact hG (id, n) (mem_of_lookupNode' h)

/-! ## Plan well-formedness for the refinement -/

/-- `WF κ B plan`: `PlanWF` (every read variable bound) plus what the
engine's write/undo discipline needs and `PlanWF` does not state:

* the classification `κ` agrees with the plan (join targets and
  decomposed nodes are node variables; element, join-key, copied and
  checked variables are class variables), since the engine's single
  namespace is split in `Binding` (`σ.node` is only written by `joinBind`);
* a variable written by `ExtractChild`/`CopyBinding` or a rest pushed by
  a decomposition is not already bound (`out ∉ B`, `t ∉ B`, `r ∉ B`): the
  engine writes it unconditionally and `clear`/`pop` reset it to
  *unbound*, not to its previous value (the scheduler never emits these on
  a bound variable; the reference `runStep` would instead check a bound
  target);
* `pre ≠ suf` for `ExpandA` (two pushes on one span would be popped twice,
  the second `pop` truncating the pool to `0`);
* no `exact 0` multiplicity (`resolve.rs:1999` rejects it; the engine's
  `mult_matches(Exact(0), 0)` would otherwise take a zeroed entry).

Element and multiplicity variables of a decomposition and the pair's
variables may be bound (the check paths) or shared across steps. -/
inductive WF (κ : Var → Bool) : List Var → Plan → Prop
  | nil {B : List Var} : WF κ B []
  | join {B : List Var} {t : Var} {ls : List Lookup} {ss : Plan} :
      κ t = true → (∀ l ∈ ls, ∀ x ∈ l.reads, x ∈ B ∧ κ x = false) →
      WF κ (t :: B) ss → WF κ B (.join t ls :: ss)
  | extractChild {B : List Var} {v out : Var} {pos : Nat} {ss : Plan} :
      v ∈ B → κ v = true → out ∉ B → κ out = false →
      WF κ (out :: B) ss → WF κ B (.extractChild v pos out :: ss)
  | checkChildEq {B : List Var} {v x : Var} {pos : Nat} {ss : Plan} :
      v ∈ B → κ v = true → x ∈ B → κ x = false →
      WF κ B ss → WF κ B (.checkChildEq v pos x :: ss)
  | checkEq {B : List Var} {x y : Var} {ss : Plan} :
      x ∈ B → κ x = false → y ∈ B → κ y = false →
      WF κ B ss → WF κ B (.checkEq x y :: ss)
  | copyBinding {B : List Var} {t o : Var} {ss : Plan} :
      o ∈ B → t ∉ B → κ t = false →
      WF κ (t :: B) ss → WF κ B (.copyBinding t o :: ss)
  | decomposeAC {B : List Var} {v : Var} {elems : List (Var × Mult)}
      {rest : Option Var} {ss : Plan} :
      v ∈ B → κ v = true → (∀ p ∈ elems, κ p.1 = false ∧ p.2 ≠ .exact 0) →
      (∀ r ∈ rest, r ∉ B) →
      WF κ (acBinds elems rest ++ B) ss → WF κ B (.decomposeAC v elems rest :: ss)
  | decomposeACI {B : List Var} {v : Var} {elems : List Var} {rest : Option Var} {ss : Plan} :
      v ∈ B → κ v = true → (∀ x ∈ elems, κ x = false) → (∀ r ∈ rest, r ∉ B) →
      WF κ (elems ++ rest.toList ++ B) ss → WF κ B (.decomposeACI v elems rest :: ss)
  | expandA {B : List Var} {v : Var} {pre suf : Option Var} {elems : List Var} {ss : Plan} :
      v ∈ B → κ v = true → (∀ x ∈ elems, κ x = false) →
      (∀ r ∈ pre, r ∉ B) → (∀ r ∈ suf, r ∉ B) → (∀ r ∈ pre, suf ≠ some r) →
      WF κ (pre.toList ++ elems ++ suf.toList ++ B) ss →
      WF κ B (.expandA v pre elems suf :: ss)
  | decomposeComm {B : List Var} {v x y : Var} {ss : Plan} :
      v ∈ B → κ v = true → κ x = false → κ y = false →
      WF κ (x :: y :: B) ss → WF κ B (.decomposeComm v x y :: ss)

/-- `WF` refines `PlanWF`. -/
theorem WF.toPlanWF {κ : Var → Bool} {B : List Var} {plan : Plan} (h : WF κ B plan) :
    PlanWF B plan := by
  induction h with
  | nil => exact .nil
  | join _ hr _ ih => exact .join (fun l hl x hx => (hr l hl x hx).1) ih
  | extractChild hv _ _ _ _ ih => exact .extractChild hv ih
  | checkChildEq hv _ hx _ _ ih => exact .checkChildEq hv hx ih
  | checkEq hx _ hy _ _ ih => exact .checkEq hx hy ih
  | copyBinding ho _ _ _ ih => exact .copyBinding ho ih
  | decomposeAC hv _ _ _ _ ih => exact .decomposeAC hv ih
  | decomposeACI hv _ _ _ _ ih => exact .decomposeACI hv ih
  | expandA hv _ _ _ _ _ _ ih => exact .expandA hv ih
  | decomposeComm hv _ _ _ _ ih => exact .decomposeComm hv ih

end Semper.EMatch.Env
