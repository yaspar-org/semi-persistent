import SemperProofs.EMatch.Env.Model

/-!
# The recursive executor over `Env` (`run_step`, `ematch.rs:1765-2100`)

`exec G κ plan e` is `run_step` in continuation-passing style: each step
performs the writes of spec B.2's table on `e`, calls the continuation
(the rest of the plan) and performs the undos on the environment the
continuation returns. The result is the list of emitted environments
(abstracted by `abs`, as `results.push(env)` copies them) and the final
environment, so that `(Restore)` is a statement about the second
component.

Per step (cites are `ematch.rs`):

* `Join` (`2966-2977`): `prev := get_opt(target)`; per key `set(target, id)`
  then continue; after the loop `set_opt(target, prev)`. The leapfrog
  intersection is the reference `candidates` on the abstraction.
* `ExtractChild` (`1870-1880`): `set(target, child)`, continue, `clear`.
* `CheckChildEq`/`CheckEq` (`1881-1897`): compare through `canon` (`G.find`).
* `CopyBinding` (`1914-1919`): `set(target, canon(nodes[other]))`, continue,
  `clear(target)`.
* `ExpandA` (`2146-2225`, `2234-2282`): the pushes per rest shape, then
  `bind_fixed_and_continue`: an already bound child is checked through
  `canon`, an unbound one is `set` and recorded; exactly the recorded
  variables are cleared, on failure too.
* `DecomposeAC` (`2360-2493`): the residual is the canonized entry list;
  bound path: first entry of that class accepted by `mult_matches`,
  `was_unbound` read before `set_mult`, reset to `ZERO` after iff it was
  unbound; unbound path: every entry accepted by `mult_matches`, `set`,
  `was_unbound`, `set_mult`, continue, `clear`, reset. Leaf:
  `push_mset_residual` of the nonzero entries and `pop_mset`, or require
  the residual all zero.
* `DecomposeACI` (`2513-2613`): same with a used set, modelled by erasing
  the taken class from the residual list (the engine marks the first unused
  position of that class; the two coincide on a residual with distinct
  classes, H2, and differ only in enumeration order otherwise).
* `DecomposeComm`: `DecomposeAC` on the pair's two uncoalesced entries
  `(a, 1), (b, 1)` (`egraph.rs:4291-4305`), written out for the two elements
  with exact multiplicity `1`.

`demand_accepts` (view pruning, `ematch.rs:579-600`) is `true` without
views and is omitted; `Flatten`, `Collect`, literals and globals are out of
scope.
-/

namespace Semper.EMatch.Env

open Semper.EMatch

/-- A continuation: the rest of the plan, run on an environment. -/
abbrev Cont := Env → List Binding × Env

/-- Sequential iteration threading the environment (`for` loops over keys,
residual entries, offsets). -/
def loop {α : Type} (f : α → Env → List Binding × Env) : List α → Env → List Binding × Env
  | [], e => ([], e)
  | a :: as, e => ((f a e).1 ++ (loop f as (f a e).2).1, (loop f as (f a e).2).2)

@[simp] theorem loop_nil {α : Type} (f : α → Env → List Binding × Env) (e : Env) :
    loop f [] e = ([], e) := rfl

@[simp] theorem loop_cons {α : Type} (f : α → Env → List Binding × Env) (a : α) (as : List α)
    (e : Env) :
    loop f (a :: as) e = ((f a e).1 ++ (loop f as (f a e).2).1, (loop f as (f a e).2).2) := rfl

/-! ### Multiplicities (`mult_matches`, `ematch.rs:2290-2336`) -/

/-- `bound_mult_val`: the raw slot, `0` meaning unbound. -/
def boundMult (e : Env) : Mult → Nat
  | .var k _ _ => e.mults k
  | .exact _ => 0

/-- `mult_matches(mult, avail, bound)`: an exact count must equal `avail`;
a multiplicity variable needs `avail ≠ 0`, agreement with a nonzero bound
value and the interval. -/
def multMatchesE : Mult → Nat → Nat → Bool
  | .exact n, avail, _ => decide (avail = n)
  | .var _ lo hi, avail, bound =>
      decide (avail ≠ 0) && (decide (bound = 0) || decide (avail = bound)) && inInterval lo hi avail

/-- `was_unbound` (`ematch.rs:2408`, `2456`): read before `set_mult`. -/
def wasUnbound (e : Env) : Mult → Bool
  | .var k _ _ => decide (e.mults k = 0)
  | .exact _ => false

/-- `set_mult(mv, actual)` for a multiplicity variable, nothing for an exact count. -/
def setMultOf (e : Env) : Mult → Nat → Env
  | .var k _ _, m => e.setMult k m
  | .exact _, _ => e

/-- The reset `set_mult(mv, ZERO)` iff `was_unbound` (`ematch.rs:2439`, `2486`). -/
def resetMult (e : Env) (μ : Mult) (wu : Bool) : Env :=
  match μ with
  | .var k _ _ => if wu then e.setMult k 0 else e
  | .exact _ => e

/-! ### Steps -/

variable (G : Graph) (κ : Var → Bool)

/-- `decompose_ac_elem`. The residual is a scratch buffer, not part of the
environment: its zeroing is the reference `zeroEntry`. -/
def execAC (k : Cont) : List (Var × Mult) → Option Var → List (C × Nat) → Env →
    List Binding × Env
  | [], rest, res, e =>
      match rest with
      | none => if res.all (fun p => p.2 = 0) then k e else ([], e)
      | some r =>
          let o := k (e.pushMset r (res.filter (fun p => p.2 ≠ 0)))
          (o.1, o.2.popMset r)
  | (x, μ) :: es, rest, res, e =>
      match e.nodes x with
      | some g =>
          match res.find? (fun p => p.1 = G.find g ∧ multMatchesE μ p.2 (boundMult e μ)) with
          | some p =>
              let wu := wasUnbound e μ
              let o := execAC k es rest (zeroEntry (G.find g) res) (setMultOf e μ p.2)
              (o.1, resetMult o.2 μ wu)
          | none => ([], e)
      | none =>
          loop (fun p e =>
            if multMatchesE μ p.2 (boundMult e μ) then
              let e₁ := e.set x p.1
              let wu := wasUnbound e₁ μ
              let o := execAC k es rest (zeroEntry p.1 res) (setMultOf e₁ μ p.2)
              (o.1, resetMult (o.2.clear x) μ wu)
            else ([], e)) res e

/-- `decompose_aci_elem`. -/
def execACI (k : Cont) : List Var → Option Var → List C → Env → List Binding × Env
  | [], rest, res, e =>
      match rest with
      | none => if res.isEmpty then k e else ([], e)
      | some r =>
          let o := k (e.pushSet r res)
          (o.1, o.2.popSet r)
  | x :: es, rest, res, e =>
      match e.nodes x with
      | some g => if G.find g ∈ res then execACI k es rest (res.erase (G.find g)) e else ([], e)
      | none =>
          loop (fun c e =>
            let o := execACI k es rest (res.erase c) (e.set x c)
            (o.1, o.2.clear x)) res e

/-- `unbind`: clear exactly the recorded variables. -/
def unbind (bound : List Var) (e : Env) : Env := bound.foldl (fun e x => e.clear x) e

@[simp] theorem unbind_nil (e : Env) : unbind [] e = e := rfl
@[simp] theorem unbind_cons (x : Var) (bound : List Var) (e : Env) :
    unbind (x :: bound) e = unbind bound (e.clear x) := rfl

/-- `bind_fixed_and_continue` on the children `cs` from the offset: the
fixed child variables in order, `bound` the variables this pass bound. -/
def bindFixed (k : Cont) : List Var → List C → List Var → Env → List Binding × Env
  | [], _, bound, e =>
      let o := k e
      (o.1, unbind bound o.2)
  | x :: xs, c :: cs, bound, e =>
      match e.nodes x with
      | some g => if G.find g = G.find c then bindFixed k xs cs bound e else ([], unbind bound e)
      | none => bindFixed k xs cs (x :: bound) (e.set x c)
  | _ :: _, [], bound, e => ([], unbind bound e)

/-- `run_expand_a`. -/
def execExpandA (k : Cont) (pre : Option Var) (elems : List Var) (suf : Option Var)
    (cs : List C) (e : Env) : List Binding × Env :=
  let n := elems.length
  match pre, suf with
  | none, none => if cs.length = n then bindFixed G k elems cs [] e else ([], e)
  | some p, none =>
      if cs.length < n then ([], e)
      else
        let split := cs.length - n
        let o := bindFixed G k elems (cs.drop split) [] (e.pushSeq p (cs.take split))
        (o.1, o.2.popSeq p)
  | none, some s =>
      if cs.length < n then ([], e)
      else
        let o := bindFixed G k elems cs [] (e.pushSeq s (cs.drop n))
        (o.1, o.2.popSeq s)
  | some p, some s =>
      if cs.length < n then ([], e)
      else
        loop (fun off e =>
          let o := bindFixed G k elems (cs.drop off) []
            ((e.pushSeq p (cs.take off)).pushSeq s (cs.drop (off + n)))
          (o.1, (o.2.popSeq s).popSeq p)) (List.range (cs.length - n + 1)) e

/-- The second element of a pair decomposition, taking the remaining entry
`c` with exact multiplicity `1`. -/
def execPairSnd (k : Cont) (y : Var) (c : C) (e : Env) : List Binding × Env :=
  match e.nodes y with
  | some g => if G.find g = c then k e else ([], e)
  | none =>
      let o := k (e.set y c)
      (o.1, o.2.clear y)

/-- `decompose_ac_elem` on the residual `[(a, 1), (b, 1)]` of a commutative
pair with elements `(x, Exact 1), (y, Exact 1)` and no rest: a bound `x`
takes the first entry of its class (no second attempt), an unbound `x`
tries both positions. -/
def execPair (k : Cont) (x y : Var) (a b : C) (e : Env) : List Binding × Env :=
  match e.nodes x with
  | some g =>
      if G.find g = a then execPairSnd G k y b e
      else if G.find g = b then execPairSnd G k y a e
      else ([], e)
  | none =>
      let o₁ := execPairSnd G k y b (e.set x a)
      let e₁ := o₁.2.clear x
      let o₂ := execPairSnd G k y a (e₁.set x b)
      (o₁.1 ++ o₂.1, o₂.2.clear x)

/-- Canonize a residual (`entry.0 = canon(entry.0)`, `ematch.rs:2013`). -/
def canonRes (res : List (C × Nat)) : List (C × Nat) := res.map (fun p => (G.find p.1, p.2))

/-- One step of `run_step` in CPS. -/
def execStep (k : Cont) : Step → Env → List Binding × Env
  | .join t ls, e =>
      let prev := e.nodes t
      let o := loop (fun id e => k (e.set t id)) (candidates G (abs G κ e) ls) e
      (o.1, o.2.setOpt t prev)
  | .extractChild v pos out, e =>
      match e.nodeOf G v with
      | some n =>
          match n.children.childAt pos with
          | some c =>
              let o := k (e.set out c)
              (o.1, o.2.clear out)
          | none => ([], e)
      | none => ([], e)
  | .checkChildEq v pos x, e =>
      match e.nodeOf G v, e.nodes x with
      | some n, some g =>
          match n.children.childAt pos with
          | some c => if G.find c = G.find g then k e else ([], e)
          | none => ([], e)
      | _, _ => ([], e)
  | .checkEq x y, e =>
      match e.nodes x, e.nodes y with
      | some a, some b => if G.find a = G.find b then k e else ([], e)
      | _, _ => ([], e)
  | .copyBinding t o, e =>
      match e.nodes o with
      | some g =>
          let r := k (e.set t (G.find g))
          (r.1, r.2.clear t)
      | none => ([], e)
  | .decomposeAC v elems rest, e =>
      match e.nodeOf G v with
      | some ⟨_, .mset m⟩ => execAC G k elems rest (canonRes G (Multiset.entries m)) e
      | _ => ([], e)
  | .decomposeACI v elems rest, e =>
      match e.nodeOf G v with
      | some ⟨_, .set s⟩ => execACI G k elems rest ((s.sort (· ≤ ·)).map G.find) e
      | _ => ([], e)
  | .expandA v pre elems suf, e =>
      match e.nodeOf G v with
      | some ⟨_, .seq cs⟩ => execExpandA G k pre elems suf cs e
      | _ => ([], e)
  | .decomposeComm v x y, e =>
      match e.nodeOf G v with
      | some ⟨_, .spair a b⟩ => execPair G k x y (G.find a) (G.find b) e
      | _ => ([], e)

/-- `run_step` over the whole plan: the end of the plan emits the
abstraction of the environment (`results.push(env)`, `ematch.rs:1789`). -/
def exec : Plan → Env → List Binding × Env
  | [], e => ([abs G κ e], e)
  | s :: ss, e => execStep G κ (exec ss) s e

@[simp] theorem exec_nil (e : Env) : exec G κ [] e = ([abs G κ e], e) := rfl
@[simp] theorem exec_cons (s : Step) (ss : Plan) (e : Env) :
    exec G κ (s :: ss) e = execStep G κ (exec G κ ss) s e := rfl

end Semper.EMatch.Env
