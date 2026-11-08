# A reader's guide to the Lean development

This guide explains what the Lean development in `proofs/lean` proves about the Semper
engine. It defines the notions the proofs use, states each headline theorem, and sketches its
proof. A reader who finishes it should be able to judge whether each Lean definition encodes
the engine behaviour it is named after. The guide is not a status page: `STATUS.md` records
the state of the build, and `scripts/check-proofs.sh` checks it.

Lean checks that each proof follows from its hypotheses. Lean does not check that a
definition describes the engine, or that the engine satisfies a hypothesis. Those two
questions are the subject of this guide. Each section therefore carries an adequacy note: the
places where the model departs from the engine, and the hypotheses that no theorem
discharges.

The statements below are quoted from the sources of branch `feat/completeness-proofs` as of
2026-11-06: upstream `main` at `6c37120b` plus the proof that the engine's regrouping skips
preserve the match set (Section 4.7) and the completeness theorems with leaf constants
(Section 5.9). The first edition of this guide (commit `a5cfa2d7`) was written against
`6c37120b`; Section 9 records which of its findings still hold. File paths are relative
to `proofs/lean/SemperProofs/` unless they start with `egraph/` or `proofs/`. `Flatten/`
abbreviates `EMatch/Flatten/`, and `Rounds/` and `Saturate/` abbreviate `EMatch/Engine/Rounds/`
and `EMatch/Engine/Saturate/`. A bare file name refers to the directory of the theorem last
cited, and a bare `:N` to the Lean file last cited. A fixture without a path is in
`egraph/tests/egg/`. The build and the axiom audit were not re-run for this guide;
[`STATUS.md`](STATUS.md) reports that `lake build` passes, that no declaration uses `sorry`,
and that every `#print axioms` in the `*Check.lean` files lists only `propext`,
`Classical.choice` and `Quot.sound`.

Branch `feat/real-rules` resolves items 1, 2 and 4 of Section 10: commit `f1e8be1a` replaces
the executor's partition of variables by per-step binding kinds (Section 3.7), and commit
`8932dc12` states the final theorem over the store with the represented graph as a part of
the index and proves a run that meets all its hypotheses (Section 7.7). Those sections, and
the resolution notes in Sections 7.3, 7.5, 9 and 10, describe that branch; the original
findings are kept as written. `scripts/check-proofs.sh` passes on it.

Several hypotheses are meant to be checked on each run rather than proved of the engine. The
design note [`runtime-completeness-checks.md`](../../egraph/doc/future/runtime-completeness-checks.md)
assigns each hypothesis to a check; the hypothesis tables below cite its tiers. The note is a
design: no check is implemented.

## Contents

1. Layers of the development
2. Common vocabulary
3. Matching on one frozen graph (`EMatch/`, `EMatch/Engine/`)
4. Flattened matching (`EMatch/Flatten/`)
5. Congruence closure modulo AC (`CC/`)
6. Rounds and saturation (`EMatch/Engine/Rounds/`, `EMatch/Engine/Saturate/`, `Fidelity/`)
7. The final theorem (`CC/Bridge/`, `Final/`)
8. Counterexamples and the engine defects they record
9. Gaps between the model and the engine, and the status of the first edition's findings
10. Open findings

## 1. Layers of the development

The development has five layers. Each one models one part of the engine and proves its
results relative to a specification of its own. The final theorem joins three of them.

| Layer | Directory | Models | Headline results |
|---|---|---|---|
| Matching | `EMatch/`, `EMatch/Engine/` | one rule matched on a frozen index: atoms, lowering, scheduling, semi-naive variants | `plan_matches`, `runND_matches`, `variant_partition` |
| Flattened matching | `EMatch/Flatten/` | `:flatten` rules: views of nested same-operator children, demand, regrouping and the engine's regrouping loop | `views_sound`/`views_complete`, `demand_engine_complete_*`, `regroup_match_iff`, `regroupSkip_match_iff` |
| Congruence closure | `CC/` | AC completion of one operator under its laws, with leaf constants | `completion_sound`, `completion_complete_at_convergence`, `completion_complete_atoms` |
| Saturation | `EMatch/Engine/Rounds/`, `Saturate/`, `Fidelity/` | the round loop: deltas, actions, rebuild, the stop test | `delta_complete`, `saturation_complete` |
| Final | `CC/Bridge/`, `Final/` | the matching graph read from a completion state | `saturation_modulo_complete`, `saturation_modulo_complete_atoms` |

Two further directories are tools rather than proofs. `Conform/` holds generators that emit
`.egg` programs whose expected answers come from the Lean reference interpreters. The
`*Check.lean` files print the axioms of the headline results.

The flattened-matching layer feeds nothing above it: no module of `Saturate/`, `Bridge/` or
`Final/` imports `Flatten/`. Its results concern one matching run, and the conformance
generators consume its executable models.

## 2. Common vocabulary

### 2.1 Graphs, nodes and classes

A **graph** (`Graph`, `EMatch/Defs.lean:57`) is a frozen snapshot of the index as the matcher
reads it: a list of identified nodes and a representative map.

```lean
inductive Children where
  | tuple (cs : List C)
  | spair (a b : C)
  | seq (cs : List C)
  | mset (m : Multiset C)
  | set (s : Finset C)

structure Graph where
  nodes : List (NodeId × Node)
  find : NodeId → C
```

A `Node` is an operator and its children. The five child shapes are the engine's kinds:
fixed arity (`tuple`), commutative pair (`spair`), sequence for `:assoc` (`seq`), multiset for
AC (`mset`), and set for ACI (`set`). Class ids, node ids, symbols and variables are all
natural numbers, and a node's class is `G.find id`.

The type carries no invariant. Ids may repeat, `find` need not be idempotent, and stored
children need not be representatives. Theorems add these properties as hypotheses when they
need them: `KeysNodup` (distinct node ids), `Conforms sig` (each operator has one child
shape), `FindIdem`, and `ChildrenCanon` (stored children are representatives).

### 2.2 Patterns and bindings

A **pattern** (`Pat`, `EMatch/Defs.lean:101`) mirrors the child shapes:

```lean
inductive Pat where
  | var (x : Var)
  | plain (f : Sym) (args : List Pat)
  | comm (f : Sym) (p q : Pat)
  | assoc (f : Sym) (pre : Option Var) (args : List Pat) (suf : Option Var)
  | ac (f : Sym) (elems : List (Pat × Mult)) (rest : Option Var)
  | aci (f : Sym) (elems : List Pat) (rest : Option Var)
```

An AC element carries a multiplicity annotation `Mult`: `exact m`, or a variable with bounds.
An element written without an annotation is `exact 1`. Literals, sequence filters and
predicates are not patterns; `EMatch/Steps/` treats them as separate atoms.

A **binding** (`Binding`, `EMatch/Defs.lean:126`) is six partial maps: class variables,
node variables, multiplicity variables, and the three kinds of rest (multiset, sequence,
set). `Binding.Extends σ σ'` says each map of `σ` is contained in the corresponding map of
`σ'`.

### 2.3 The matching specification

Every matching theorem is stated relative to one specification, the mutual inductive
relations `MatchC` (a pattern at a class) and `MatchN` (a pattern at a node),
`EMatch/Defs.lean:213-255`. Two constructors carry the content:

```lean
inductive MatchC (G : Graph) : Pat → C → Binding → Prop
  | var {x : Var} {c : C} {σ : Binding} :
      σ.cls x = some c → MatchC G (.var x) c σ
  | app {P : Pat} {c : C} {σ : Binding} {id : NodeId} {n : Node} :
      (id, n) ∈ G.nodes → G.find id = c → P.head = some n.op →
      MatchN G P n σ → MatchC G P c σ

  -- the AC case of MatchN
  | ac ... : taken.Nodup → elems.length = taken.length →
      (∀ c ∈ taken, c ∈ m) →
      (∀ et ∈ elems.zip taken, MatchC G et.1.1 et.2 σ) →
      (∀ et ∈ elems.zip taken, MultOk σ et.1.2 (m.count et.2)) →
      MsetRestOk σ rest m taken →
      MatchN G (.ac f elems rest) ⟨f, .mset m⟩ σ
```

A pattern matches a class when some stored node of that class has the pattern's head and
matches node-wise. Plain patterns match position by position. A commutative pair matches in
either order. A sequence splits as prefix, fixed middle and suffix.

AC matching is **maximum partition**. The pattern picks a list `taken` of distinct child
classes, one per element. Element `i` matches class `taken[i]`, and its annotation is checked
against the full count of that class in the multiset. The rest is the multiset of untaken
classes with their full counts; without a rest, every class must be taken. ACI is the same
over a set, without counts.

Three consequences follow, and the rest of the guide depends on them:

- An element takes one child entry with its whole multiplicity. It never takes part of an
  entry, and it never takes a sum of several children.
- An unannotated element accepts only an entry of count 1. So `(f x y)` matches `f{a, b}` but
  not `f{a, a}`, and `(f x)` does not match `f{a, a}` either.
- `MatchN` matches the syntax of the stored node up to rearrangement of its entries. It is
  not matching modulo the AC theory. Section 7 lifts it to the theory.

The specification never constrains node variables: `MatchC.app` does not mention `σ.node`.
Node variables appear only in the theorems' conclusions.

### 2.4 The congruence-closure vocabulary

The congruence-closure layer (`CC/Defs.lean`) has its own encoding, specialised to one
implicit AC operator `f`.

A **monomial** is a multiset of classes, `Monomial n = Multiset (Fin n)`. A node is a pair
`(M, c)`: the AC term `f(M)` stored in class `c`. There is no term language. Classes and
summands share the type `Fin n`, so a fixed pool of `n` class ids serves as both.

The **completion state** (`State`, `CC/Defs.lean:141`) holds a representative map `find`, a
set of nodes, a subset of retired nodes (the engine's `FLAG_AC_COLLAPSED`), and a stored
right-hand side `rhs` per class. The active nodes are `nodes \ retired`.

The operator's **laws** (`Laws`, `CC/Defs.lean:67`) are a relation of ground law instances, a
normalization `clamp` that only removes children, and a declared flag `cancellative`. The
instances in `CC/Laws/` cover identity, nilpotence, idempotence, inverse cancellation, and
their combination.

The **theory equality** `E L S` (`CC/Defs.lean:86`) is the least equivalence on monomials
that contains the asserted pairs `S` and the law instances, is closed under adding a common
summand, and is closed under removing one when the operator is cancellative:

```lean
inductive E (L : Laws n) (S : Set (Monomial n × Monomial n)) :
    Monomial n → Monomial n → Prop
  | ax {M N} : (M, N) ∈ S → E L S M N
  | refl (M) : E L S M M
  | symm {M N} : E L S M N → E L S N M
  | trans {M N P} : E L S M N → E L S N P → E L S M P
  | congr {M N} (X) : E L S M N → E L S (M + X) (N + X)
  | law {M N} : L.lawRel M N → E L S M N
  | cancel {M N X} : L.cancellative → E L S (M + X) (N + X) → E L S M N
```

**Adequacy.** Associativity and commutativity are built into the multiset representation.
The only congruence in `E` is adding a common context. Children are free atoms: `find` is
never applied to them, so `a = b` does not give `f{a, x} = f{b, x}` unless the pair is in
`S`. In the engine that step is recanonicalization; the model treats it as already done. The
lattice part of `CC/` (Section 5.7) brings back the reading "a class denotes its node's
term", as an assumption named `FlatSound`.

A class with no node of the operator, a **leaf constant** such as `a` in `(+ a b)`, has no
monomial of its own in this encoding: it occurs only as a summand. Section 5.9 reads such a
class `x` as the one-element monomial `{x}`, as the engine does, by adding implicit nodes
`({x}, x)` to the state.

## 3. Matching on one frozen graph

This layer proves that the engine's way of running one rule on one frozen index emits
exactly the matches of the specification. The engine does not interpret a pattern directly:
the resolver flattens it into atoms, the scheduler orders the atoms, and each atom is lowered
to index steps. The theorems follow that pipeline, one refinement per stage.

### 3.1 The pipeline

```
MatchC G P c σ                                    specification
  ⟺ atoms satisfied                              atoms_iff_match
  ⟺ Matches G atoms σ'                           (exact-domain form)
  ⟺ σ' ∈ run G plan ∅, any PlanOK plan           plan_matches
  ⟺ σ' ∈ runND ..., any choice function          runND_matches, runND_eq_plan
runVariant k = runNaive ∩ {atom k new, atoms < k old}   variant_partition
```

The interpreter `run` (`EMatch/Ref.lean:280`) is a depth-first list monad over index steps:
`join` over a list of lookups, `extractChild`, `checkChildEq`, `checkEq`, `copyBinding`, and
the decompositions. A join is modelled as the intersection of its lookups' buckets; the
galloping cursor is verified separately in Verus (`containers-verus`).

### 3.2 Atoms

An **atom** (`RAtom`, `EMatch/Engine/Atoms.lean:41`) is one node of a pattern with variables
in every child position: a node variable, an operator, and a shape. It mirrors `RAtom` in
`egraph/src/resolve.rs:131`. Its shallow pattern `a.shallow` is the one-level pattern with
those variables as arguments. `atoms P r` flattens `P` in post-order, rooted at node
variable `r`. A child application's class variable is its node variable, as in the engine's
single namespace.

An atom holds when its node variable is bound to a stored node with its operator, its class
variable is that node's class, and the node matches the shallow pattern:

```lean
def AtomSat (G : Graph) (σ : Binding) (a : RAtom) : Prop :=
  ∃ id n, σ.node a.node = some id ∧ (id, n) ∈ G.nodes ∧ σ.cls a.node = some (G.find id) ∧
    n.op = a.op ∧ MatchN G a.shallow n σ
```

`AtomSat` reuses `MatchN`, so atoms inherit the specification's maximum-partition semantics.

**`atoms_iff_match`** (`EMatch/Engine/AtomsMatch.lean:1133`):

```lean
theorem atoms_iff_match (G : Graph) (P : Pat) (r : Var) (c : C) (σ : Binding)
    (hP : P.head.isSome = true) (hr : r ∉ P.vars) :
    MatchC G P c σ ↔
      ∃ σ', AgreeOn P.vars σ σ' ∧ σ'.cls r = some c ∧ ∀ a ∈ atoms P r, AtomSat G σ' a
```

A pattern matches at class `c` exactly when some binding agrees with `σ` on the pattern
variables, binds the root to `c`, and satisfies every atom. The root must be an application
(`hP`) and the root variable fresh (`hr`); no graph hypothesis is needed.

*Proof.* The forward direction (`fwdOk`, `:1113`) walks the `MatchN` derivation and binds
each atom's node variable to the node that derivation used. The backward direction
(`backOk`, `:734`) rebuilds `MatchN` bottom-up through the variables the atoms share, then
transfers the result to `σ` (`MatchC_agree`, `:153`).

### 3.3 Lowering one atom

`lower a B` (`EMatch/Engine/Lower.lean:75`) compiles atom `a` under the set `B` of class
variables already bound. It emits one join, then either child reads (plain shapes) or one
decomposition. When the node variable is already bound the join is a re-join on
`[byRepr a.node, byOp a.op]`; otherwise it adds a child-position or containment lookup for
each bound child.

**`lower_sound_complete`** (`EMatch/Engine/Lower.lean:1147`):

```lean
theorem lower_sound_complete {G : Graph} {sig : Sym → Kind} (a : RAtom) (B : Finset Var)
    (σ : Binding) (hk : G.KeysNodup) (hconf : G.Conforms sig) (hwk : a.WK sig)
    (hdom : ClsDom σ B) (hn : σ.node a.node = none) (hrf : a.RestFresh σ) :
    ∀ σ', σ' ∈ run G (lower a B) σ ↔ LowerSpec G a B σ σ'
```

`LowerSpec` (`:104`) says `σ'` extends `σ`, binds classes exactly on `B ∪ a.binds`, writes no
other variable, and satisfies the atom. The theorem holds for every bound set, so it covers
every lowering a scheduler can choose. The hypotheses are the scheduler's bookkeeping: `B` is
exactly the bound classes (`hdom`), the node variable is not yet joined (`hn`), the rests are
unbound and distinct (`hrf`), and node ids and shapes are well formed (`hk`, `hconf`, `hwk`).

*Proof.* Soundness and completeness are proved shape by shape (`lower_sound`, `:806`;
`lower_complete`, `:966`) from the decomposition lemmas in `EMatch/Proofs/`. The equivalence
closes with `lowerSpec_unique` (`:1094`): two `LowerSpec` bindings, one below the other, are
equal, because `LowerSpec` fixes the domain.

### 3.4 Scheduled plans

A query is a list of `QAtom`s: scanning atoms and `Eq` atoms (`EMatch/Engine/Sched.lean:32`).
The plan grammar `Sched` (`:74`) admits any interleaving that lowers each scanning atom once
under the bound set at that point, and lowers an `Eq` atom eagerly once one side is bound:

```lean
inductive Sched (atoms : List QAtom) : Finset Nat → Finset Var → Plan → Prop
  | done ... : (∀ i a, atoms[i]? = some (.scan a) → i ∈ used) →
      (∀ i q, atoms[i]? = some q → i ∉ used → ¬ q.eagerFree B) → Sched atoms used B []
  | eager ... : atoms[i]? = some q → i ∉ used → q.eagerFree B →
      Sched atoms (insert i used) (B ∪ q.binds) rest →
      Sched atoms used B (q.eagerLower B ++ rest)
  | pick ... : atoms[i]? = some (.scan a) → i ∉ used →
      Sched atoms (insert i used) (B ∪ a.binds) rest →
      Sched atoms used B (lower a B ++ rest)

def PlanOK (atoms : List QAtom) (plan : Plan) : Prop := Sched atoms ∅ ∅ plan
```

`pick` is unrestricted, so any selectivity order is admitted. The grammar is looser than the
engine's "eager atoms first" rule and contains it.

The target of every scheduler theorem is `Matches G atoms σ'` (`EMatch/Engine/Plan.lean:21`):
every atom holds, and the binding's domain is exactly the atoms' variables. Fixing the
domain turns "some extension of a match is emitted" into an equality of binding sets.

**`plan_matches`** (`EMatch/Engine/Plan.lean:181`):

```lean
theorem plan_matches {G : Graph} {sig : Sym → Kind} {atoms : List QAtom} {plan : Plan}
    (hwf : AtomsWF G sig atoms) (h : PlanOK atoms plan) :
    ∀ σ', σ' ∈ run G plan Binding.empty ↔ Matches G atoms σ'
```

Every plan the grammar admits, whatever order it chose, emits exactly the matches of the
query. `AtomsWF` (`EMatch/Engine/SchedRun.lean:27`) collects the resolver's checks and the
index invariants: distinct node ids, one shape per operator, well-kinded atoms, distinct node
variables, linear rest variables, and every `Eq` operand bound by some scanning atom. The last
condition prevents the plan from ending with an `Eq` unchecked. For a single pattern,
`atoms_atomsWF` (`EMatch/Engine/AtomsWF.lean:417`) discharges `AtomsWF`.

*Proof.* `schedA_run` (`SchedRun.lean:587`) is an induction on the grammar with a run
invariant `Inv` at each decision point. The `pick` case uses `lower_sound` and
`lower_complete`. The `eager` case uses `eager_sound` and `eager_complete`. The `done` case
uses `bindable` to show every `Eq` was used.

**`runND_matches`** (`EMatch/Engine/Runtime.lean:192`) covers the engine's adaptive
scheduler, which picks the next atom per branch from the current binding:

```lean
theorem runND_matches {G : Graph} {sig : Sym → Kind} {atoms : List QAtom}
    (choose : Binding → Finset Nat → Nat) (hwf : AtomsWF G sig atoms) :
    ∀ σ', σ' ∈ runND G atoms choose atoms.length ∅ ∅ Binding.empty ↔ Matches G atoms σ'
```

The choice function is arbitrary, and different branches may choose different orders.
`runND_indep` and `runND_eq_plan` (`:204`, `:212`) follow: the result does not depend on the
heuristic and equals that of every `PlanOK` plan. The proof is an induction on fuel that
reuses the `pick` and `eager` steps of `schedA_run`.

**The single-pattern corollary.** `engine_plan_sound` and `engine_plan_complete`
(`EMatch/Engine/Main.lean:66`, `:74`) specialise the chain to one pattern:

```lean
theorem engine_plan_sound ... (h : PlanOK ((atoms P r).map QAtom.scan) plan)
    (hσ : σ ∈ run G plan Binding.empty) :
    ∃ id n, σ.node r = some id ∧ (id, n) ∈ G.nodes ∧ σ.cls r = some (G.find id) ∧ MatchN G P n σ

theorem engine_plan_complete ... (h : PlanOK ((atoms P r).map QAtom.scan) plan)
    (hmem : (id, n) ∈ G.nodes) (hm : MatchN G P n σ) :
    ∃ σ' ∈ run G plan Binding.empty, σ'.node r = some id ∧ BelowOn P.vars σ' σ
```

**Adequacy.** `BelowOn P.vars σ' σ` says only that `σ'` is contained in `σ` on the pattern
variables. Read alone, a binding that binds almost nothing would satisfy it. The intended
statement, that the emitted binding equals the witness on the pattern variables, follows by
applying soundness to `σ'`: it matches at the same node, so it binds every variable the
pattern forces. The same remark applies to `ExtendsBelow` in `ematch_complete`.

All results in this layer are about sets of bindings. The engine may emit a binding more than
once, and the counts may differ from the model's (`comm_pair_duplicate`,
`comm_bound_first_counts`, `EMatch/Env/Main.lean:58`, `:68`).

### 3.5 Semi-naive variants

A semi-naive round runs variant `k` of a rule for each scanning atom `k`. Variant `k` reads
only new nodes for atom `k`, only old nodes for atoms of smaller index, and every node for
atoms of larger index (`variantMode`, `EMatch/Engine/SemiNaive.lean:19`). The order is the
stable atom index, not plan order, as in `VariantIndex::mode` (`egraph/src/index.rs:955-963`).

**`variant_partition`** (`EMatch/Engine/SemiNaive.lean:30`):

```lean
theorem variant_partition ... (hwf : AtomsWF G sig atoms) (h : SchedA atoms ∅ ∅ ap)
    (hk : atoms[k]? = some (.scan ak)) :
    ∀ σ', σ' ∈ runVariant G isNew k ap ↔
      σ' ∈ runNaive G ap ∧ (∃ id, σ'.node ak.node = some id ∧ isNew id = true) ∧
        ∀ (j : Nat) (a : RAtom), j < k → atoms[j]? = some (.scan a) →
          ∃ id, σ'.node a.node = some id ∧ isNew id = false
```

Variant `k` emits exactly the naive matches whose atom-`k` node is new and whose
smaller-index nodes are old. `variants_disjoint` (`:65`) follows: two variants never emit the
same binding. `variants_cover_new` (`:88`) also follows: the union of the variants is exactly
the naive matches with at least one new scanning node. Its proof takes the least new atom
index. In this layer `isNew` is an arbitrary predicate; Section 6.2 connects it to "the node
changed during the round".

### 3.6 The reference compiler

`ematch_sound` and `ematch_complete` (`EMatch/Main.lean:143`, `:156`) relate the
specification to a second, simpler compiler (`compile`, `EMatch/Ref.lean:453`), which lowers
a pattern left to right without scheduling. This chain runs beside the engine chain and meets
it only at `MatchN`. Its decomposition lemmas (`decompose_ac_sound'`, `expand_a_complete'`
and the others in `EMatch/Proofs/`) are what the engine chain reuses. The theorems themselves
are not consumed downstream.

### 3.7 The mutable executor

`EMatch/Env/` models the engine's `Match` environment, which writes bindings in place and
undoes them on backtrack (`egraph/src/ematch.rs:171`). The engine has one slot per variable;
a node variable's slot holds a node id, a class variable's slot a class. `abs G κ e`
(`EMatch/Env/Model.lean`) reads every slot as a class through `find`, and the slots of the
variables of node kind (`κ v = true`) also as node ids. `env_restore` and `env_refine`
(`EMatch/Env/Main.lean`) state that the executor returns the environment it was given, and
that the bindings it emits are, as a set, the bindings `run` emits:

```lean
theorem env_refine (G : Graph) (hG : G.ChildrenCanon) (hidem : G.FindIdem)
    {κ : Var → Bool} {B : List Var} {plan : Plan} (hwf : WF κ B plan) (e : Env)
    (he : EnvOk e B) (hκ : KindOk κ e) (σ : Binding) :
    σ ∈ (exec G (joinKinds κ plan) plan e).1 ↔ σ ∈ run G plan (abs G κ e)
```

The binding kinds are per step (commit `f1e8be1a`). `κ` is the kind of each variable at the
entry of the plan. A join makes its target a node variable, whatever it was before:
unbound, or a class variable bound by `ExtractChild`, by a decomposition or by an earlier
atom, which the join then refines to a node of its class. `joinKinds κ plan` is the kind of
each variable at the end of the plan, and the emitted environments are read with it. A
lookup or a check reads a slot through `canon` whatever its kind, so `Env.WF` puts no kind
condition on join keys, check operands or decomposition elements; it requires only that a
step reading a node through `nodeOf` reads a node variable. `KindOk κ e` says every node
variable is bound in `e`, so an element a decomposition binds is a class variable. The
write-once conditions are unchanged: `ExtractChild`, `CopyBinding` and the rest pushes
write unbound variables only, `ExpandA`'s two rests are distinct, and no annotation is
`exact 0`.

`planOK_envWF` (`EMatch/Env/Plans.lean`) proves that every `PlanOK` plan is `WF` from
`Match::new` (all kinds `false`), under `EnvAtomsWF`, the resolver's variable discipline:
a class variable is no multiplicity or rest variable, a multiplicity variable is no rest
variable, rest variables are linear across atoms, an atom's prefix and suffix rests are
distinct, and no AC annotation is `exact 0`. `exec_matches` composes it with
`env_refine_empty` and `plan_matches`:

```lean
theorem exec_matches {G : Graph} {sig : Sym → Kind} {atoms : List QAtom} {plan : Plan}
    (hG : G.ChildrenCanon) (hidem : G.FindIdem) (hwf : AtomsWF G sig atoms)
    (hA : EnvAtomsWF atoms) (h : PlanOK atoms plan) (σ : Binding) :
    σ ∈ (exec G (planKinds plan) plan Env.empty).1 ↔ Matches G atoms σ
```

`nested_plans_wf` and `nested_exec_matches` work the pattern `(f (g x) y)` both ways round.
With the parent first, the plan is `join 2 [byOp f]`, `extractChild 2 0 3`,
`extractChild 2 1 1`, `join 3 [byRepr 3, byOp g]`, `extractChild 3 0 0`: `3` is bound as a
class and refined by the re-join, which reads its own target. With the nested atom first, it
is `join 3 [byOp g]`, `extractChild 3 0 0`, `join 2 [byOp f, byChildPos 0 3]`,
`checkChildEq 2 0 3`, `extractChild 2 1 1`: `3` is bound as a node and read as a class
(`nestedPlanParent_eq`, `nestedPlanChild_eq`, by `decide`).

**Adequacy.** The executor (`exec`) is unchanged; only its well-formedness and the
abstraction changed. The engine's join saves and restores a bound target
(`ematch.rs:3012-3023`, "`target` may already be bound"), as `exec` does, and its lookups
canonicalize the key slot (`bucket_in`); nothing the new model admits disagrees with the
engine. `EnvAtomsWF` is a hypothesis, not derived from the resolver. `exec` covers static
plans of scanning and `Eq` atoms: the adaptive scheduler (`runND`) and the steps of
Section 3.8 are not connected to it. Nothing downstream uses `Env/`: the saturation theorems
read the emitted bindings through `run` (`runNaive`), which `exec_matches` now shows the
executor agrees with.

The finding of the second edition, resolved by commit `f1e8be1a`, read:

> **Adequacy.** The theorem holds for plans that satisfy `Env.WF` (`EMatch/Env/Model.lean:612`),
> and that predicate excludes every plan the scheduler emits for a nested pattern. `Env.WF`
> partitions the variables by `κ` into node variables and class variables. Its `join` clause
> requires the join target to be a node variable (`κ t = true`) and every variable a lookup
> reads to be a class variable (`κ x = false`); its `extractChild` clause requires the
> extracted child to be a class variable. `atoms` gives a nested child one variable, which is
> both the parent's child class and the nested atom's node variable (Section 3.2). If the
> parent is lowered first, `extractChild` makes that variable a class variable and the nested
> atom's `join` makes it a node variable. If the nested atom is lowered first, its `join`
> makes it a node variable and the parent's `byChildPos` lookup reads it as a class variable.
> Either order violates `Env.WF`; the re-join `join a.node [byRepr a.node, byOp a.op]` violates
> it a second time, because it reads its own target. No theorem derives `Env.WF` from
> `PlanOK`. The executor refinement is therefore not connected to `plan_matches` for any
> nested pattern, and nothing downstream uses `Env/`.

### 3.8 Guards, literals and sequence collection

`EMatch/Steps/` adds `Neq`, global, literal, predicate and `Collect` atoms. `step_sound` and
`step_complete` (`EMatch/Steps/Main.lean:43`, `:55`) prove each lowering step sound and
complete against the atom's meaning. `collect_sound` and `collect_complete`
(`EMatch/Steps/Collect.lean:453`, `:462`) relate the sequence assembler to a declarative
relation, under the assumption that a node yields at most `MAX_MATCHES` (2^20) raw matches.

**Adequacy.** These are per-step results. The grammar `Sched` contains only scanning and `Eq`
atoms, so no theorem covers a whole query that mixes guards or literals with scanning atoms.
The declarative relation for `Collect` reuses most of the assembler's own functions
(`choicesAt`, `admit`, `matchedA`), so `collect_sound` and `collect_complete` are close to
restating the code.

## 4. Flattened matching

### 4.1 Problem

A rule tagged `:flatten` matches an n-ary pattern against the flattened term. A child class
`X` that holds an `f`-member `m` may be replaced in place by `m`'s children, recursively. For
example, the node `Plus{Y, Z}` with `Z ∋ Plus{Y, d}` has the flattened reading `{Y, Y, d}`.
Plain maximum-partition matching sees only the stored children.

An **opening tree** (`OT`, `EMatch/Flatten/Views.lean:96-111`) records, for each child
position, whether the child is kept whole or opened through one of its `f`-members. A class
already on the current path may not be opened again. Multiplicities multiply down the tree.
The tree's fringe is a **raw view**: a list of (class, count) pairs. A kept child of an opened
member is part of that member's **leaf group**.

The **canonical view** is the raw view normalized for the operator's kind and laws
(`normalize`, `Views.lean:226`): coalesce and sort for AC, deduplicate for ACI, then drop the
unit, clamp nilpotent counts, and cancel inverse pairs in one left-to-right pass. A raw view
whose normal form is empty, the unit, or a single class of count 1 is dropped. `Views ctx
laws n` is the set of canonical views of node `n`.

Opening produces redundant matches. If no item pattern takes anything from an opened member,
the same match, with a refolded rest, already exists on a less-opened view. The **demand
rule** filters these: a match on view `w` that takes the classes `taken` is kept when some
tree giving `w` opens nothing, or when every leaf of some tree giving `w` is satisfied.
Demand only removes matches. Every kept match is a match of the shallow pattern on a genuine
view, so demand bears on completeness and redundancy, never on soundness.

**Regrouping** handles the converse. Maximum partition gives each scalar item one entry, so
`(f x y)` does not match `f{a, b, c}` with `x` bound to a class `G ∋ f{a, b}`. Regrouping adds
views in which a group of at least two entries (but not the whole view) equal to the children
of some `f`-member of class `g` is replaced by `g`. The group is a sub-multiset for AC, a
subset for ACI, a contiguous run for `:assoc`, a prefix for a left fold, and a suffix for a
right fold.

### 4.2 The enumerator

**`views_sound`** and **`views_complete`** (`EMatch/Flatten/Enum.lean:244`, `:260`):

```lean
theorem views_sound {ctx : Ctx} {laws : Laws} {n : Node} {w : List (C × Nat)}
    {d : Demand} (h : (w, d) ∈ enumerate ctx laws n) :
    w ∈ Views ctx laws n ∧
      (d.unconditional = true ↔ [] ∈ Alts ctx laws n w) ∧
      (d.unconditional = false → ∀ ls, ls ∈ d.alts ↔ ls ∈ Alts ctx laws n w)

theorem views_complete {ctx : Ctx} {laws : Laws} {n : Node} {v w : List (C × Nat)}
    {ls : List (List C)} (hv : RawView ctx n v ls)
    (hn : normalize ctx.κ laws v = .node w) :
    ∃ d, (w, d) ∈ enumerate ctx laws n ∧
      (ls = [] → d.unconditional = true) ∧
      (ls ≠ [] → d.unconditional = true ∨ ls ∈ d.alts)
```

The enumerator emits exactly the canonical views of the opening trees, each with its demand:
unconditional when some tree giving the view opens nothing, and otherwise the trees' leaf
groups. Completeness needs no bound: each opening adds a class of the graph to the path, so
the number of classes is enough fuel (`rawNode_complete`, `:150`).

### 4.3 Demand rules

The development states five demand rules, all of the form "unconditional, or some
alternative has every leaf satisfied". They differ in what satisfies a leaf.

| Rule | Lean | A leaf is satisfied when | Status |
|---|---|---|---|
| Original | `Demand.accepts`, `Views.lean:252` | its group holds a taken class | incomplete for AC (`demand-gap.egg`); complete for ACI under `TwoClasses` |
| Corrected | `DemandX.acceptsFix`, `Fix.lean:262` | as above, or its opened class is taken | complete, laws-free, every kind |
| Per kind | `DemandX.acceptsKind`, `FixKind.lean:85` | the corrected rule on multisets, the original elsewhere | |
| Under laws | `DemandL.acceptsLaws`, `Laws.lean:876` | the corrected rule, or closing the leaf is not inert | complete under any laws |
| Engine | `DemandL.acceptsE`, `EngineRule.lean:50` | the laws rule, with the opened-class clause on multisets only | mirrors `Demand::accepts` in `egraph/src/flatten.rs` |

Closing a leaf is **not inert** (`nonInertB`, `Laws.lean:827`) when the laws could change the
normal form and lose the match. For AC this happens when the opened class is the unit, when
its refolded count clamps to zero, or when an inverse pair touches it or a leaf class. For
ACI it happens when the class is the unit. For `:assoc` it happens when the class is the unit
or the whole block is units.

`nonInertEng_eq` (`EngineRule.lean:376`) shows that the flag as the code computes it (a
residue loop and three inverse loops over masks) equals `nonInertB` on a leaf whose entries
form a contiguous block of the raw view. `acceptsE_ac_iff` (`:97`) shows the engine rule
equals the laws rule on multisets.

**Completeness up to refolding.** The headline theorem for the engine rule on multisets is
`demand_engine_complete_ac` (`EMatch/Flatten/EngineComplete.lean:35`). It has the hypotheses
and conclusion of `demand_laws_complete_ac` (`LawsMain.lean:128`), with `acceptsE`:

```lean
theorem demand_laws_complete_ac {ctx : Ctx} (hκ : ctx.κ = .ac) {laws : Laws} {n : Node}
    {v w : List (C × Nat)} {ls : List LeafL} {o : Nat} {f : Sym} {elems : List (Pat × Mult)}
    {r : Var} {σ : Binding} {taken : List C}
    (hv : RawViewL ctx n v ls o) (hn : normalize .ac laws v = .node w)
    (helems : ∀ e ∈ elems, ∃ x, e.1 = Pat.var x) (hne : elems ≠ [])
    (hm : MatchV ctx.G (.ac f elems (some r)) (ofView .ac w) σ taken) :
    ∃ (w' : List (C × Nat)) (d : DemandL) (rest₀ rest' : Multiset C),
      (w', d) ∈ enumerateL ctx laws n ∧ d.acceptsLaws taken ∧
      MatchV ctx.G (.ac f elems (some r)) (ofView .ac w') (σ.setRest r rest') taken ∧
      σ.rest r = some rest₀ ∧ RefoldsACL ctx laws taken rest₀ rest'
```

Take any match on the view of any opening tree. Some emitted view accepted by the rule
carries a match with the same item bindings. Only the rest changes, and the new rest is the
old one with some opened members folded back into their classes. The items must be variables
(atom flattening guarantees this), and there must be at least one item and a rest variable.

*Proof.* Strong induction on the number of openings (`laws_ac_aux`, `LawsMain.lean:52`). If
the rule accepts the tree, it is the witness. Otherwise some leaf is unsatisfied, hence inert;
closing it removes one opening. The match carries over to the closed tree with its rest
updated (`refold_ac_inert`, `Laws.lean:1381`), because the taken classes keep their
normalized counts. The closed view is still a node, because it holds a taken class and the
opened class.

The ACI version (`demand_engine_complete_aci`, `EngineComplete.lean:332`) needs `TwoClassesL`:
no raw view of the node collapses to a single class after unit drop. `STATUS.md` says rebuild
guarantees this by merging a one-class member into its child's class. No theorem derives it.
The `:assoc` versions need no extra hypothesis under laws; the laws-free one needs
`NoNullary` (no member with zero children).

**Adequacy.** The theorems named `demand_*_no_redundancy_*` show that every rejection is
covered by an accepted, strictly less-opened refolding. They do not show that accepted
matches are irredundant; the probe `proofs/repro/aci-overaccept.egg` records a redundant set
match the rule admits. No theorem states that a refolded rest denotes the same value as the
original, although the argument of `otl_den_ac` gives it.

### 4.4 The flattened plan

`planF` (`EMatch/Flatten/PlanDefs.lean:151`) lowers each n-ary atom to a join, a `Flatten`
step that writes the views into a register, and a decomposition that reads the register and
filters by demand. The plan theorems are stated relative to `AtomSatG E` (`PlanDefs.lean:159`):
an n-ary atom holds when its node matches, through its shallow pattern, some view the
enumerator `E` emits whose engine demand accepts the item classes.

**`flatten_plan_sound_of_spec`** and **`flatten_plan_complete_of_spec`**
(`EMatch/Flatten/Plan.lean:732-750`):

```lean
theorem flatten_plan_sound_of_spec {E : Enumerator} (hE : E.Spec) {c : FCtx} {sig : Sym → Kind}
    {as : List RAtom} (r : Nat) (hw : QueryFWF c sig as) {env' : EEnv}
    (h : env' ∈ runEG E c (planF as ∅ r) EEnv.empty) :
    (∀ a ∈ as, AtomSatG E c env'.σ a) ∧ ClsDom env'.σ (planBound as ∅)

theorem flatten_plan_complete_of_spec {E : Enumerator} (hE : E.Spec) {c : FCtx}
    {sig : Sym → Kind} {as : List RAtom} (r : Nat) (hw : QueryFWF c sig as) {σ' : Binding}
    (hsat : ∀ a ∈ as, AtomSatG E c σ' a) :
    ∃ env' ∈ runEG E c (planF as ∅ r) EEnv.empty, Extends env'.σ σ'
```

For any atom order and any enumerator meeting `Enumerator.Spec`, the flattened plan emits
exactly the bindings satisfying every atom. `Enumerator.Spec` (`Plan.lean:150`) requires that
every view is a normalization result and that pruning under a binding keeps exactly the
accepted matches.

**Adequacy.** `Enumerator.Spec` does not require a view to be a view of the node. The
declarative reading needs three theorems composed by the reader: `views_soundL` (the views
are views of the node), `demand_engine_complete_*` (demand loses only redundant matches), and
`flatten_plan_complete`. No single theorem states the composition.

### 4.5 Folds

`:assoc-left` and `:assoc-right` are fold notations over an operator that is not associative.
Only the spine (the first child for a left fold, the last for a right fold) may be opened or
regrouped. `fold_open_off_spine_unsound` (`EMatch/Flatten/Fold.lean:138`) is a formal
counterexample to opening off the spine. `otLeft_sound` and `otRight_sound` (`:164`, `:177`)
prove that spine-only opening trees preserve the fold's value. Regrouping a fold replaces a
prefix (left fold) or a suffix (right fold); Section 4.6 covers it.

**Adequacy.** These soundness theorems concern the inductive relations `OTLeft` and
`OTRight`. The executable spine enumerator (`rawOptD` with a direction, `FoldPlan.lean`) is
never proved to produce exactly those views: `OTLeft` appears in `FoldPlan.lean` only in a
docstring. `runED_both` (`FoldPlan.lean:135`) shows only that with no fold the fold-aware
interpreter is the proved one. Demand completeness for folds is argued in a docstring
(`Fold.lean:27-30`). Regrouping soundness for folds is proved for a single step only
(`regroup_step_sound_left`, `regroup_step_sound_right`, `RegroupSound.lean:467`, `:490`);
regrouping completeness for folds is proved for every chain (Section 4.6).

### 4.6 Regrouped views

**Problem.** Maximum partition gives each scalar item one entry of a view, so `(f x y)` does
not match `f{a, b, c}` with `x` bound to a class `G ∋ f{a, b}`. The engine
(`FlattenScratch::regroup`, `egraph/src/flatten.rs`) therefore also matches regrouped views,
in which a group of entries equal to the children of an `f`-member of class `g` is replaced
by `g`. A regrouped view may be regrouped again. So a variable may bind a class
`G2 ∋ f{G1, c}` with `G1 ∋ f{a, b}` (nested groups), several groups may together cover the
whole view, and for a left fold `(a - b) - c` is a group of `[a, b, c, d]` only after the
prefix `[a, b]` is.

**Definitions** (`EMatch/Flatten/RegroupDefs.lean`). A **record** (`RecR`, `:60`) is a view,
its flagged leaves, and the list of classes its matches must take (`needs`).

- `fitsR κ dir view g grp` (`:101`) lists the raw views that replace one occurrence of the
  group `grp`, the children of an `f`-member of class `g`, by `g`. The group is a
  sub-multiset (AC), a subset (ACI) or a contiguous run (`:assoc`) of at least two entries, a
  prefix for a left fold and a suffix for a right fold (`spineRun`), and never the whole
  view. A member over its own class (`g ∋ f{g, c}`) is not a group.
- `regroupRec` (`:142`) is one regrouping of a record: the raw view normalized as any view,
  `g` added to every leaf that holds a class of the group (`addG`), and the needed classes
  updated by `needsAfter`: the source's, less those the group absorbs, plus `g`.
- `regroupLevels` and `regroupAll` (`:161`, `:193`) iterate it from the walk's records
  (`baseRecsR`, `:247`), as many levels as the largest total count of a walk view
(`regroupFuel`), which suffices because each regrouping lowers the total count.
  No bound applies to the needed classes along the way.
- `withinLimit limit` (`:201`) keeps the records needing at most `limit` classes, one per
  item of the atom. The engine applies the same filter to the final records only
  (`Demand::needs`).
- A needed class `g` becomes the leaf `needLeaf g` (`:65`), satisfied exactly when `g` is
  taken (`needLeaf_okE`). Every demand rule of Section 4.3 therefore reads a regrouped record
  unchanged.
- `takeableR` (`:239`) is the `takeable` set of `Step::Flatten`: the bound item classes and
  every class below one through `f`-members. `enumerateRD` and `enumerateR` (`:258`, `:265`)
  are the enumeration with and without pruning by it, and `Enumerator.regroup` (`:273`)
  packs them for the plan interpreter `runEG`.

**Soundness**, laws-free and without folds (`regroup_views_sound_ac`,
`EMatch/Flatten/RegroupSound.lean:251`):

```lean
theorem regroup_views_sound_ac {ctx : Ctx} (hκ : ctx.κ = .ac) {den : C → M}
    (hc : ConsistentAC ctx den) {limit : Nat} {n : Node} {w : List (C × Nat)} {d : DemandL}
    (h : (w, d) ∈ enumerateR ctx .both Laws.free limit n) :
    denAC den w = denAC den (kids .ac n.children)
```

In every commutative monoid where each `f`-member denotes its class (`ConsistentAC`), every
view and every regrouped view of `n` denotes the value of `n`. `regroup_views_sound_aci` and
`regroup_views_sound_assoc` (`:365`, `:443`) are the versions for a join semilattice and a
monoid. `regroup_off_spine_unsound` (`:525`) is a counterexample to regrouping off a fold's
spine.

**Chains.** `EMatch/Flatten/RegroupChain.lean` states regrouping declaratively.
`RegroupsTo κ dir w g grp w'` (`:60`) is one regrouping of the view `w`: for AC, `grp` is a
sub-multiset of `w` of at least two entries, not all of `w`, and `w'` is `w - grp + {g}`; for
ACI, the same over sets, with at least two classes left; for `:assoc`, `grp` is a run of at
least two entries at a position `p` on the spine of the fold direction, not all of `w`, and
the run becomes the single entry `g`. `regroupsTo_left_iff` and `regroupsTo_right_iff`
(`:79`, `:93`) restate the fold cases as a prefix and a suffix. `RegroupStep` (`:117`) lifts
`RegroupsTo` to a record by an `f`-member of class `g` that does not hold `g`, with the
leaves through `addG` and the needed classes through `needsAfter`. `RegroupChain` (`:127`) is
its reflexive transitive closure.

**`regroup_match_iff`** (`EMatch/Flatten/RegroupChain.lean:701`):

```lean
theorem regroup_match_iff {c : FCtx} {dir : Sym → Dir} {σ : Binding} {a : RAtom}
    {κ : FlatKind} (hκ : a.shape.flatKind = some κ) (hlaws : c.laws a.op = Laws.free) :
    AtomSatG (Enumerator.regroup dir) c σ a ↔
      ∃ id n, σ.node a.node = some id ∧ (id, n) ∈ c.G.nodes ∧
        σ.cls a.node = some (c.G.find id) ∧ n.op = a.op ∧
        ∃ r₀ ∈ baseRecsR (c.ctx a.op κ) (dir a.op) Laws.free n, ∃ r,
          RegroupChain (c.ctx a.op κ) (dir a.op) r₀ r ∧ r.2.2.length ≤ a.elems.length ∧
          MatchN c.G a.shallow ⟨a.op, ofView κ r.1⟩ σ ∧
          ∀ l ∈ r.alt, l.okE κ (takenOf σ a.elems)
```

For a laws-free operator of any kind and fold direction, an n-ary atom holds under the
regrouping enumerator exactly when some finite chain of regroupings, starting from a walk
record of a stored node of the atom's class, reaches a record whose view the shallow pattern
matches. The last record of the chain needs at most as many classes as the atom has items,
and the item classes satisfy its leaves and take its needed classes. `regroup_views_iff`
(`:679`) is the same statement at the level of views, for any `limit`.

Two properties of the statement carry the engine behaviour:

- **The item limit bounds the final record only.** `RegroupChain` puts no bound on the
  records in between, because a later regrouping may absorb a needed class.
  `regroup_nested_matches` (`EMatch/Flatten/RegroupNested.lean:81`) is a chain from
  `{a, b, c, d, h, k}` through `{h, k, G1, G2}`, which needs two classes, to `{h, k, G3}` with
  `G3 ∋ F{G1, G2}`, which needs `G3` alone; with a limit of one the view `{h, k, G3}` is
  enumerated and accepts `x = G3`. The fixture `flatten_regroup_nested_needs.egg` records the
  same match in the engine, which applied the limit per step before `6c37120b`.
- **Nested and covering groups are chains.** `G2 ∋ f{G1, c}` is reached by regrouping `G1`
  first. Groups that together cover the view are successive steps, none of which is the whole
  view. `regroup_fold_nested` (`RegroupNested.lean:133`) reaches `(a - b) - c` in the left fold
  `((a - b) - c) - d` through `[a, b, c, d] → [G1, c, d] → [G2, d]`, one needed class at each
  step. The disjoint-group AC form (`regroup_chain_ac`, `regroup_match_complete_ac`,
  `RegroupComplete.lean:248`, `:435`) predates the chain theorems and bounds the needed
  classes by one per group.

*Proof.* `regroupStep_mem` (`RegroupChain.lean:424`) shows that a declarative step is a
regrouping of the model and strictly shrinks the view's total count, so a chain lies within
the levels the model computes (`regroupChain_mem_levels`, `:437`). The converse is
`regroupChain_of_mem_levels` (`:658`), from the per-kind fit lemmas of `RegroupFits.lean`
(`fitsR_ac_complete` in `RegroupComplete.lean:120`; `fitsR_aci_complete`,
`fitsR_assoc_complete`, `fitsR_left_complete`, `fitsR_right_complete`, `RegroupFits.lean:47`,
`:86`, `:102`, `:111`).

**Adequacy.**

- Completeness is laws-free (`hlaws`). Soundness is laws-free and, for folds, single-step.
  No theorem covers a match that needs both a leaf refold (Section 4.3) and a regrouping.
- The leaf and needs bookkeeping of `RegroupStep` reuses the model's `addG` and `needsAfter`.
  Completeness is therefore with respect to a declarative view transformation plus the
  engine's own demand bookkeeping.
- That the item limit loses no match (a record needing more distinct classes than there are
  items cannot have them all taken) is argued in the docstring of `withinLimit`
  (`RegroupDefs.lean:197-200`). `regroup_match_iff` includes the limit on its right-hand side,
  so it characterizes the engine's enumeration, not the unlimited one.
- The engine's bounds `MAX_REGROUP_VIEWS` (2^14 records) and `MAX_REGROUP_WORK` (2^20
  entries examined), and the count overflow of normalization, are not modelled. Past a bound
  the engine stops regrouping the node and sets `regroup_truncated`. The design note
  ([`runtime-completeness-checks.md`](../../egraph/doc/future/runtime-completeness-checks.md),
  Section 3) proposes a per-run check that the counters `flatten_regroup_truncated` and
  `flatten_overflowed` are zero.

### 4.7 The engine's regrouping loop and its skips

`regroupAll` derives every record level by level. The engine regroups view by view instead,
largest total count first, and skips records whose matches another record of the same view
already admits. `EMatch/Flatten/RegroupSkipDefs.lean` models that loop step for step:

- the state `SkipSt` (`:89`) holds the distinct views in order of entry, each view's records
  in insertion order, the views already regrouped, and the signatures of the records
  regrouping added to each view;
- the next view (`SkipSt.next`, `:139`) is the one not yet regrouped with the largest total
  count, the latest entry among equal counts, as the engine's `BinaryHeap` of
  `(size, entry)` pairs pops it;
- the candidate groups (`groupsOfEngine`, `:82`) are the `f`-members sorted by node id;
- for each candidate, each fit and each normalized target (`SkipSt.addTarget`, `:106`), the
  loop skips a target already regrouped, gives nothing to a target that has an unconditional
  record (no leaf, no needed class), derives only from the source's first unconditional
  record when it has one (`srcRecs`, `:70`), and drops a derived record whose signature the
  target already has (`SkipSt.addRec`, `:97`). A signature (`recSig`, `:59`) is the leaves'
  opened classes, flags and sorted classes, and the needed classes; `RecSig.same` (`:63`)
  compares both lists as multisets, as the engine does by sorting them.

`regroupSkipG` (`:180`) runs the loop with a fuel larger than the number of reachable views,
and `Enumerator.regroupSkip` (`:200`) is `Enumerator.regroup` with it in place of
`regroupAll`.

The proof turns on one relation. `Cov c b` (`EMatch/Flatten/RegroupSkip.lean:369`) says the
record `c` **covers** `b`: they have the same view, each leaf of `c` has a leaf of `b` with the
same opened class, flag and classes, and every class `c` needs, `b` needs. A covering record
passes the demand rule whenever the covered one does (`Cov.accepts`, `Cov.acceptsL`, `:404`,
`:416`) and needs no more classes (`Cov.length`, `:427`). Each skip drops only covered
records: an unconditional record covers every record of its view (`cov_uncond`, `:479`),
equal signatures cover each other (`cov_of_same`, `:490`), and regrouping two records the
same way preserves the cover (`Cov.derive`, `:471`).

**`regroupSkipG_iff`** (`EMatch/Flatten/RegroupSkip.lean:1222`):

```lean
theorem regroupSkipG_iff {ctx : Ctx} {dir : Dir} {laws : Laws} {base : List RecR}
    (hb : BaseGood ctx.κ base) {gs : List (C × List (C × Nat))}
    (hgs : ∀ gg ∈ gs, gg ∈ groupsOf ctx) (hgs' : ∀ gg ∈ groupsOf ctx, gg ∈ gs)
    {F : Nat} (hF : ∀ r ∈ base, viewSize r.1 ≤ F) {limit : Nat} {w : List (C × Nat)}
    {taken : List C} :
    (∃ r ∈ withinLimit limit (regroupSkipG ctx dir laws gs base), r.1 = w ∧
        ∀ l ∈ r.alt, l.okE ctx.κ taken) ↔
      ∃ r ∈ withinLimit limit (regroupLevels ctx dir laws F base), r.1 = w ∧
        ∀ l ∈ r.alt, l.okE ctx.κ taken
```

For any laws, kind, fold direction and order of the candidate groups, a view has a record
within the item limit that passes the engine's demand rule in the engine's loop exactly when
it has one in the full enumeration. The hypotheses are discharged for the engine's inputs:
`BaseGood` (positive counts, distinct classes for multisets and sets, no class needed twice)
by `baseGood_baseRecsR` (`:1273`), the two inclusions of the candidate list by
`groupsOfEngine_sub` and `groupsOfEngine_sup` (`:1266`, `:1269`), and `hF` by
`viewSize_le_regroupFuel`. `regroupSkipG_iffL` (`:1245`) is the same for the demand rule
under laws.

*Proof.* `regroupRec_shrink` (`:259`) shows that a regrouping strictly shrinks a view under
any laws, so the full enumeration is exactly the set of records reachable from the walk's
records (`mem_regroupLevels_iff_reach`, `:345`), and a view the loop has regrouped never
becomes a target again: the skip of a target already regrouped never fires in the model. The
loop invariant `SkipInv` (`:1008`) says that every record is reachable and every regrouped
view is **closed**: each regrouping of each of its records is covered by a record of the
target. A skipped record is covered at the moment it is skipped. `run_finished` (`:1093`)
shows the loop ends with every view regrouped, and `regroupSkipG_spec` (`:1179`) concludes
that every record kept is reachable and every reachable record is covered by a kept one, by
induction on the chain.

The match-level consequences follow by composition. `atomSat_regroupSkip_iff` (`:1355`)
states that an atom holds under `Enumerator.regroupSkip` exactly when it holds under
`Enumerator.regroup`. `regroupSkip_spec` (`:1328`) discharges `Enumerator.Spec`, so the plan
theorems of Section 4.4 apply (`regroupSkip_plan_sound`, `regroupSkip_plan_complete`,
`:1372`, `:1380`). **`regroupSkip_match_iff`** (`:1410`) is `regroup_match_iff` with
`Enumerator.regroupSkip` on the left, word for word on the right:

```lean
theorem regroupSkip_match_iff {c : FCtx} {dir : Sym → Dir} {σ : Binding} {a : RAtom}
    {κ : FlatKind} (hκ : a.shape.flatKind = some κ) (hlaws : c.laws a.op = Laws.free) :
    AtomSatG (Enumerator.regroupSkip dir) c σ a ↔ ...
```

**Adequacy.**

- The engine computes a view's size as a `u128` sum of counts saturated at `u64::MAX`. With
  a count past `u64::MAX` two views can have equal saturated sizes, and the engine's skip of
  a target already regrouped can then fire. The model's counts are `Nat`, and the skip never
  fires (`flatten.rs`, the comment above `Some(&t) if entries[t].3`). No theorem covers
  the saturated case.
- The engine's candidates are the `f`-members found through the use lists of the view's
  classes; the model's are every filed `f`-member (`hgs'` requires all of them). A member
  holding no class of the view has no fit, so the two lists give the same records, but no
  theorem states it.
- The bounds of Section 4.6 apply here too: the engine counts `MAX_REGROUP_VIEWS` after the
  skips, and the model has no bound.
- The conformance generators still use `regroupLevels` (`STATUS.md`): the engine's loop
  emits the same `check-eq` sets in another order, which changes the sampled `check-neq`
  candidates.

## 5. Congruence closure modulo AC

This layer models AC completion for one operator and proves two properties. Soundness:
completion merges only theory-equal nodes. Completeness at convergence: when a round changes
nothing, theory-equal active nodes share a class.

### 5.1 Rewriting, inference, invariants

A rule `(A, B)` rewrites `f(A)` to `f(B)`. One step of `Rw L R` (`CC/Defs.lean:103`)
replaces a sub-multiset `A` of `M` by `B`, then applies `clamp`:

```lean
def Rw (L : Laws n) (R : Rules n) (M N : Monomial n) : Prop :=
  ∃ A B, (A, B) ∈ R ∧ A ≤ M ∧ N = L.clamp ((M - A) + B)
```

The state's rules (`State.rules`, `:158`) are the active nodes strictly above their class's
stored `rhs` in the order `degLex`, provided the `rhs` is itself a node of the class. `degLex`
(`:36`) compares by size, then at the largest class where the counts differ; it is the
engine's `monomial_cmp` (`egraph/src/multiset.rs:315`). The orientation guard is part of the
definition, so a stale `rhs` drops rules rather than producing unoriented ones.

`Infer` (`CC/Defs.lean:191`) lists the inference steps. **mint** adds a reduct of a node in a
fresh class. **joinMerge** merges two nodes joined by a chain of rule steps, law steps, or
same-class steps. **cancelMerge** merges `M` and `N` when `M + X` and `N + X` share a class
and the operator is cancellative. **retire** retires a node, and **setRhs** overwrites the
stored right-hand sides. The relation is deliberately permissive (`retire` and `setRhs` have
no precondition): soundness then covers any engine step that is one of these cases.

The invariants (`CC/Defs.lean:214-236`, `CC/Assemble.lean:94`):

- **I0**: each class's `rhs` is a node of the class. `I0Active` requires, of each class that
  holds an active node, that its `rhs` be an active node of the class:

  ```lean
  def I0Active (st : State n) : Prop :=
    ∀ M c, (M, c) ∈ st.active →
      ∃ c', (st.rhs (st.find c), c') ∈ st.active ∧ st.find c' = st.find c
  ```

  Before commit `7838c767` the quantifier ranged over every class of `Fin n`; that form is
  now `I0ActiveAll` (`Assemble.lean:100`), and no state with a leaf constant satisfies it
  (`witness_not_all`, Section 5.9).
- **I2**: nodes of one class are theory-equal. This is the soundness invariant.
- **I3**: a retired node rewrites in at least one step to a node of its class.
- **I5**: each class's `rhs` is the `degLex`-least active node of the class.

`RoundFixed` (`CC/Defs.lean:253`) is the fixpoint condition. Every normal form of an active
node is an active node of the same class, and every critical pair of the state's rules is
joinable:

```lean
structure RoundFixed (L : Laws n) (st : State n) : Prop where
  nf_present : ∀ M c N, (M, c) ∈ st.active →
    Relation.ReflTransGen (Rw L st.rules) M N → (∀ P, ¬ Rw L st.rules N P) →
    ∃ c', (N, c') ∈ st.active ∧ st.find c' = st.find c
  cp_joinable : ∀ r₁ r₂, r₁ ∈ st.rules → r₂ ∈ st.rules → r₁ ≠ r₂ → Overlap r₁.1 r₂.1 →
    Joinable (Rw L st.rules) (criticalPair L r₁ r₂).1 (criticalPair L r₁ r₂).2
```

`RoundFixed` is a hypothesis about the final state; no theorem derives it from an engine run.

### 5.2 Soundness

**`completion_sound`** (`CC/Main.lean:44`):

```lean
theorem completion_sound {L : Laws n} {S : Set (Monomial n × Monomial n)}
    {st₀ st : State n} (hreach : Reachable L st₀ st) (h₀ : I2 L S st₀) : I2 L S st
```

If the initial classes are theory-equal, so are the classes of every reachable state.

*Proof.* Induction on the run (`soundness`, `CC/Lemmas.lean:219`), with one case per step
(`Infer_I2`, `:198`). A mint is alone in a fresh class. A join-merge chains I2 through the
merged pair (`merge_I2`, `:180`); each rule step is theory-equal because a rule is two nodes
of one class (`rules_sound`, `:154`), and rewriting inside a context preserves `E`
(`Rw_sound`, `:132`). A cancel-merge applies `E.cancel`. Retire and `setRhs` change neither
the nodes nor `find`.

### 5.3 Completeness at convergence

**`completion_complete_at_convergence`** (`CC/Main.lean:100`, proof in `CC/Assemble.lean:167`):

```lean
theorem completion_complete_at_convergence {L : Laws n}
    {S : Set (Monomial n × Monomial n)} {st : State n}
    {ss₀ ss : SlotState n}
    (h5₀ : SlotState.I5 ss₀) (hrun : SlotState.OpsStar ss₀ ss) (ha : SlotState.Agrees st ss)
    (h0 : I0Active st) (hcanon : ∀ c, L.clamp (st.rhs c) = st.rhs c) (hfix : RoundFixed L st)
    (hlaw : ∀ P Q, L.lawRel P Q → degLex P Q)
    (hnf_ax : ∀ M N, ¬ Rw (plain n) L.axRules (L.clamp M) N)
    (hcp : ∀ r₁ r₂, r₁ ∈ st.rules ∪ L.axRules → r₂ ∈ st.rules ∪ L.axRules → r₁ ≠ r₂ →
      Overlap r₁.1 r₂.1 →
      Joinable (Rw (plain n) (st.rules ∪ L.axRules))
        (criticalPair (plain n) r₁ r₂).1 (criticalPair (plain n) r₁ r₂).2)
    (hcc : ∀ P c d, (P, c) ∈ st.active → (P, d) ∈ st.active → st.find c = st.find d)
    (hS : ∀ M N, (M, N) ∈ S →
      ∃ c d, (M, c) ∈ st.active ∧ (N, d) ∈ st.active ∧ st.find c = st.find d)
    (hcancel : L.cancellative → ∀ M N X,
      Joinable (Rw (plain n) (st.rules ∪ L.axRules)) (M + X) (N + X) →
      Joinable (Rw (plain n) (st.rules ∪ L.axRules)) M N)
    {M N : Monomial n} {c d : Fin n} (hM : (M, c) ∈ st.active) (hN : (N, d) ∈ st.active)
    (hMN : E L S M N) : st.find c = st.find d
```

At a state where the last round changed nothing, two active nodes with theory-equal monomials
are in one class. Commit `7838c767` weakened two hypotheses: `h0` now constrains only the
classes that hold an active node, and `hcc` only the active nodes. The former statement is
the corollary `completion_complete_at_convergence_of_all` (`CC/Main.lean:125`). The
hypotheses, who is meant to supply each, and the check the runtime design note proposes
(tier 1: every run, one pass over the nodes; tier 2: in CI, by a proved Lean checker on a
dump of the final state):

| Hypothesis | Meaning | Supplied by | Runtime check |
|---|---|---|---|
| `h5₀`, `hrun`, `ha` | minimal-monomial maintenance from a good initial state, agreeing with `st` at the end | assumed; equivalent to assuming I5 (see below) | tier 1, as I5 |
| `h0` | each class holding an active node has an active node as `rhs` | assumed of the engine | tier 1 |
| `hcanon` | stored right-hand sides are clamp-normal | assumed of the engine (`nary_canon` output) | tier 1 |
| `hfix` | the round is fixed (`RoundFixed`) | assumed of the engine at convergence | tier 2 (`nf_present`, `cp_joinable`) |
| `hlaw`, `hnf_ax` | law instances decrease `degLex`; clamp outputs are law-normal | discharged for every `NFLaw` instance | once per signature |
| `hcp` | every critical pair of the rules and law instances is joinable under plain rewriting | reduced per law in `CC/Laws/`; the rule-rule part is assumed | tier 2 |
| `hcc` | two active nodes with the same monomial share a class | assumed of the engine (hash-consing) | tier 1 |
| `hS` | every asserted pair is two active nodes of one class | assumed of the input | none |
| `hcancel` | joinability cancels a common summand | not an engine fact (Section 5.7); `CompleteHyps` replaces it by `hlat` (lattice closure), which the engine establishes | tier 1, as lattice closure |

*Proof* (`CC/Assemble.lean:184-212`):

1. I5 holds of `st` (`reachable_I5`, `CC/Slot.lean:260`).
2. Each stored `rhs` is normal for `Rw L`: a step from it would go strictly down, and
   `nf_present` would put the normal form in the class, contradicting I5
   (`rhs_normal`, `Assemble.lean:113`). This step needs `h0` only at the two classes of the
   conclusion, which hold the active nodes `M` and `N`; that is why the weakened `I0Active`
   suffices.
3. Plain rewriting by the rules and law instances is confluent: Newman's lemma on a
   well-founded relation, with local confluence from `hcp` through the critical-pair lemma
   (`RwAx_confluent`, `Assemble.lean:41`; `newman`, `CC/Lemmas.lean:230`;
   `critical_pair_lemma`, `:270`).
4. Theory-equal monomials are joinable, by induction on `E` (`E_joinable_RwAx`,
   `Assemble.lean:53`). The `cancel` case is exactly `hcancel`.
5. Both nodes rewrite to their classes' right-hand sides, which are normal. Confluence makes
   the two right-hand sides equal. I0 gives a node with that monomial in each class, and
   `hcc` merges them.

The proof works with plain rewriting over rules and law instances, not with clamped rewriting
over rules alone. The header of `Assemble.lean` explains why: the `congr` case of the
induction builds monomials that are not clamp-normal, and those are not joinable under
clamped rewriting. `stub_counterexample` (`CC/Proofs/CriticalPairModulo.lean:202`) refutes the
earlier formulation.

**Adequacy.**

- The minimal-monomial hypotheses `h5₀`, `hrun`, `ha` are equivalent to assuming I5.
  `OpsStar` is a reflexive transitive closure, and the run of minimal-monomial operations is
  never linked to the inference run. Taking `ss₀ = ss`, the triple holds whenever some
  `SlotState` satisfies I5 and agrees with `st`. The engine content is that maintaining the
  minimal monomial preserves I5 (`reachable_I5`, Section 5.5). That every engine run consists
  of the modelled operations is argued in prose.
  `AtomsWitness.witness_complete` (Section 5.9) discharges the triple with `ss₀ = ss` and the
  reflexive run, which confirms the reduction.
- `hcp` is never derived from `RoundFixed`. The engine's critical-pair round establishes
  clamped joinability over the rules (`cp_joinable`). The theorem needs plain joinability
  over rules and law instances, including containment pairs. The engine skips disjoint and
  containment pairs in its critical-pair loop (`egraph/src/egraph.rs:3881`) and states, in
  the comment above, that the normalize pass handles containment; no theorem connects that
  pass to `hcp`. The runtime design note assigns `hcp` to tier 2 and also states that the
  engine's confirmation round checks it; the second statement is inaccurate for the
  containment pairs.
- The first edition recorded that `I0Active` quantified over every class id in `Fin n`, so
  every id had to carry an active node. Commit `7838c767` resolves it: `I0Active` constrains
  only the classes that hold an active node.

### 5.4 Confluence and termination

`confluent_modulo` (`CC/Main.lean:30`) states that clamped rewriting is confluent when rules
and law instances are oriented, clamp produces law-normal forms, and every critical pair of
rules and law instances joins under plain rewriting. `kapur_termination` (`CC/Lemmas.lean:426`)
proves Kapur's termination argument from Dickson's lemma over abstract sequences of left sides.
It is not connected to `Infer`. `run_stabilizes` (`CC/Main.lean:23`) states that nodes and
partition are eventually constant along any run. Its proof uses only that `Fin n` is finite and
that a mint needs a fresh class, so it does not bound the engine's rounds.

### 5.5 The minimal monomial

The engine stores each class's minimal monomial and refreshes it when a member shrinks.
`CC/Slot.lean` models the operations that maintain it (`SlotState`): mint, merge (fold the two
minima), shrink with refresh, and retire when a smaller classmate exists.

```lean
theorem reachable_I5 {st₀ st : SlotState n} (h₀ : I5 st₀) (hrun : OpsStar st₀ st) : I5 st
```

The proof is one case per operation (`op_I5`, `:251`). `shrinkNoRefresh_breaks_I5` (`:290`) is
the state of the engine bug in which a shrink did not refresh the minimal monomial.

The engine orders monomials by per-class order keys, not by representative id
(`CC/MinMonoKey.lean`). At a merge every node's keyed monomial stays or shrinks
(`rename_key_le`, `survivor_key_le`), so each recanonicalization is a no-op or a shrink
(`merge_recanon_op`, `:201`). `keyed_reachable_I5` (`:211`) restates `reachable_I5`; the
content is in `merge_recanon_op`. `idOrder_grow_breaks_I5` (`:250`) shows that under the id
order a node grows past its classmate and I5 fails.

### 5.6 Laws and the inverse rules

`CC/Laws/Main.lean` instantiates the completeness theorem for each law set. The law
hypotheses `hlaw` and `hnf_ax` are discharged, and `hcp` is reduced to conditions on the
rules (`RuleRuleCP`, and conditions on left-hand sides). For `:inverse`, the reduction leaves
four conditions the engine did not establish: `InvMatching`, `InvUnitFree`, `InverseAxiomCP`
and `NilpotentInverseCP`.

The engine now applies five inverse rules R1 to R5 (`inverse_law_repair`,
`egraph/src/egraph.rs:3361`). `CC/Laws/InvRules.lean` models them as inference steps;
`inv_rules_sound` (`:379`) extends soundness to them and requires a cancellative operator.
`CC/Laws/InvRulesMain.lean` derives the four conditions from the fixpoints of the rules
(`invMatching_of_fixed`, `invUnitFree_of_fixed`, `inverseAxiomCP_of_fixed`,
`nilpotentInverseCP_of_fixed`), giving `completion_complete_inverse_engine` (`:340`) and
`completion_complete_combined_engine` (`:371`).

**Adequacy.** `STATUS.md` describes the two `_engine` theorems as having engine-level
hypotheses only. They still take `hcancel`, `hcc`, `hS`, the minimal-monomial hypotheses, `I3`, the
rule-rule condition `hRR`, and conditions on left-hand sides. With a cancellative operator, which `inv_rules_sound`
requires, `hcancel` is the hypothesis Section 5.7 shows the engine does not establish.

### 5.7 The lattice round

Kapur's inferences alone do not establish `hcancel`. The fixture `cancel_lattice.egg` converged
without the equation `C5 = c1c3²`, which needs `c1c4² = c0²` and two copies of `c4 = c0c3`. The
engine therefore runs `lattice_round` at the completion fixpoint. Classes whose count vectors
differ by a member of the lattice spanned by the equations are merged.

`CC/Lattice.lean` formalizes the argument. A monomial's count vector is `vec M : Fin n → ℤ`.
`E_mem_lattice` (`:125`) shows theory-equal monomials differ by a lattice vector, for every
law set. `E_of_mem_lattice` and `E_iff_mem_lattice` (`:213`, `:218`) give the converse when the
theory is closed under cancellation (`CancelClosed`, from `cancelClosed_of_cancellative` or
`cancelClosed_of_nil`). `combined_E_iff` (`:272`) identifies, for the identity, nilpotent and
inverse laws, the lattice with the one spanned by the vectors `lattice_round` builds.
`stateLattice_eq_closure` (`:336`) shows the model's lattice is the span of the engine's
vectors (`engineRows`; `nodeEqs`: a class equals
its node's monomial; `classEqs`: classmates), and `engine_merge_E` (`:393`) shows each such
merge is a theory consequence under `FlatSound` (`:447`). `lattice_merge_sound` (`:500`) shows a lattice merge is a theory consequence and
preserves I2. `completion_complete_cancellative_engine` (`:565`) replaces `hcancel` by
`LatticeClosed`: active nodes whose vectors differ by a lattice member share a class.
`latticeClosed_of_engineFixed` (`:531`) derives `LatticeClosed` from the fixpoint of the
lattice step.

**Adequacy.** The lattice is that of the extended theory, which reads each class id as the term
its node holds (`nodeEqs`, `classEqs`). That reading agrees with the core theory only under
`FlatSound`, which is assumed and not shown invariant under `Infer`. In the cancellative branch
of `completion_complete_cancellative_engine`, the proof uses only `LatticeClosed` and `hS`.
`hcancel_not_derivable` (`:725`) shows `hcancel` does not follow from lattice closure: it is a
converged, lattice-closed state where two joinable sums cancel to distinct normal forms.
Coset representatives are modelled as lattice membership only. The variant with leaf
constants, `completion_complete_cancellative_engine_atoms`, is in Section 5.9.

### 5.8 The A-only round and the countermodel

`CC/ARound/` models `a_round`, the inter-reduction for associative-only operators, on a
separate list-based state. A sequence denotes a fold. A rewrite is allowed at offset 0 for a
left fold, at the last offset for a right fold, and anywhere for an associative operator.
`rewrite_left_sound`, `rewrite_right_sound` and `rewrite_both_sound` (`CC/ARound/Basic.lean:205`,
`:222`, `:245`) prove these sound in every magma or semigroup. `left_off_spine_unsound` and
`right_off_spine_unsound` (`:390`, `:420`) give counter-models in ℤ with subtraction for every
other offset. `aRound_sound` (`:495`) concludes that a spine-restricted merge preserves I2.

Three further files cover the engine's choices. `CC/ARound/Choice.lean` shows the least
spelling of a class is unique (`isLeastSpelling_unique`), every other spelling is oriented
towards it (`rule_of_ne_least`), an oriented rewrite decreases in shortlex
(`orientedRewrite_wf`), and the engine's first-occurrence choice is an allowed step that
exists whenever an occurrence does (`firstRule_theq`, `firstRule_complete`).
`CC/ARound/Store.lean` adds hash-consing, so a rewrite to an existing node merges its class:
`aRoundH_sound` preserves I2, and `aRoundH_wf` shows the merges from a finite node set
terminate. `CC/ARound/Nested.lean` shows spine splicing preserves the denotation
(`splice_den_left`, `splice_den_right`, `splice_den_both`) and gives counter-models for
off-spine splicing.

**Adequacy.** `ARound/` has no completeness theorem: completion modulo associativity alone
decides the word problem for semigroups, which is undecidable. Recanonicalization by
rebuild, the one-element collapse in `add`, and termination of `a_round` interleaved with
AC rounds are not modelled.

`CC/Countermodel.lean` gives the semantic side of `E`. `E_sound` (`:58`) states that
theory-equal monomials have equal value in every commutative-monoid model of the asserted
pairs and laws (cancellative if the operator is). `not_E_of_separates` (`:73`) follows: a
model that separates two monomials certifies that they are not theory-equal. The generator
`semper-conform-cc-cert` emits `check-neq` only on pairs such a model separates, so a failing
`check-neq` there is an engine unsoundness.

### 5.9 Leaf constants

**Problem.** In `(union (+ a b) c)` the classes `a`, `b` and `c` hold no `+`-node. They occur
in monomials only as summands, yet the equation relates the two-element monomial `{a, b}` to
the class `c`. The engine identifies the one-element monomial `{x}` with the class `x`
everywhere: `nary_canon::normalize` returns `Normal::Single(x)` for a single child of count 1
and `add` returns `x`'s class without building a node; recanonicalization that leaves a
stored node with one child records the pair (node, child) as a merge (`degeneracy_pair`); and
`class_rhs_into` gives an atomic class the right-hand side `{find c}`, which no stored node
spells. The empty monomial is identified the same way with the class of the operator's unit
(`Normal::Unit`).

**Definitions** (`CC/Atoms.lean`). `A : Set (Fin n)` is a set of atomic classes, in the engine
every class referenced as a child, and `u : Option (Fin n)` the unit class.

```lean
def atomNodes (A : Set (Fin n)) (u : Option (Fin n)) : Set (Monomial n × Fin n) :=
  {p | (p.2 ∈ A ∧ p.1 = {p.2}) ∨ (u = some p.2 ∧ p.1 = 0)}

def State.withAtoms (st : State n) (A : Set (Fin n)) (u : Option (Fin n)) : State n where
  find := st.find
  nodes := st.nodes ∪ atomNodes A u
  retired := st.retired \ atomNodes A u
  rhs := st.rhs
```

The **completion view** `st.withAtoms A u` (`:91`) adds the implicit nodes `({x}, x)` for
`x ∈ A` and `(∅, u)`, active and never retired (`atomNodes`, `:66`). `find` and the right-hand
sides are the stored ones, so the view's rules include `M → {x}` for an atomic class whose
right-hand side is `{x}`.

`AtomCollapse L st A u` (`:143`) is the **one-element collapse**: an active node of the view
whose normal form is the monomial of an implicit node is in that node's class. It is what
`add` returning `x`'s class achieves. `RoundFixedA L st A u` (`:153`) is the fixed round with
leaf constants: a normal form that is not an implicit node's monomial is a stored active node
of the class (`nf_present`), the collapse holds (`collapse`), and the critical pairs of the
view's rules are joinable (`cp_joinable`). `roundFixedA_iff` (`:169`) shows that
`RoundFixedA` is `RoundFixed` of the view plus `AtomCollapse`.

Two lemmas derive congruence on the view from congruence on the stored active nodes.
`RoundFixedA.materialized` (`:201`) shows that a stored active node whose monomial is an
implicit node's, such as a one-element node `({x}, c)` the engine keeps until the degeneracy
merge, is in the implicit node's class at a fixed round: this is the engine's
`degeneracy_pair` merge, derived. `RoundFixedA.congr` (`:220`) concludes, because no two
implicit nodes share a monomial (`atomNodes_func`, `:73`).

**`completion_complete_atoms`** (`CC/Atoms.lean:252`):

```lean
theorem completion_complete_atoms {L : Laws n} {S : Set (Monomial n × Monomial n)}
    {st : State n} {A : Set (Fin n)} {u : Option (Fin n)}
    {ss₀ ss : SlotState n}
    (h5₀ : SlotState.I5 ss₀) (hrun : SlotState.OpsStar ss₀ ss)
    (ha : SlotState.Agrees (st.withAtoms A u) ss)
    (h0 : I0Active (st.withAtoms A u)) (hcanon : ∀ c, L.clamp (st.rhs c) = st.rhs c)
    (hfix : RoundFixedA L st A u)
    (hlaw : ∀ P Q, L.lawRel P Q → degLex P Q)
    (hnf_ax : ∀ M N, ¬ Rw (plain n) L.axRules (L.clamp M) N)
    (hcp : ∀ r₁ r₂, r₁ ∈ (st.withAtoms A u).rules ∪ L.axRules →
      r₂ ∈ (st.withAtoms A u).rules ∪ L.axRules → r₁ ≠ r₂ → Overlap r₁.1 r₂.1 →
      Joinable (Rw (plain n) ((st.withAtoms A u).rules ∪ L.axRules))
        (criticalPair (plain n) r₁ r₂).1 (criticalPair (plain n) r₁ r₂).2)
    (hcc : ∀ P c d, (P, c) ∈ st.active → (P, d) ∈ st.active → st.find c = st.find d)
    (hS : ∀ M N, (M, N) ∈ S → ∃ c d, (M, c) ∈ (st.withAtoms A u).active ∧
      (N, d) ∈ (st.withAtoms A u).active ∧ st.find c = st.find d)
    (hcancel : L.cancellative → ∀ M N X,
      Joinable (Rw (plain n) ((st.withAtoms A u).rules ∪ L.axRules)) (M + X) (N + X) →
      Joinable (Rw (plain n) ((st.withAtoms A u).rules ∪ L.axRules)) M N)
    {M N : Monomial n} {c d : Fin n} (hM : (M, c) ∈ (st.withAtoms A u).active)
    (hN : (N, d) ∈ (st.withAtoms A u).active) (hMN : E L S M N) : st.find c = st.find d
```

Two theory-equal monomials of the view, each a stored active node, the one-element monomial
`{x}` of an atom, or the empty monomial of the unit, are in one class. The proof applies
`completion_complete_at_convergence` to the view, with `hfix.roundFixed` and
`hfix.congr hcc`. `CompleteAtoms` (`:277`) packages the hypotheses, and its corollaries name
the cases: `nodes` (two stored nodes), `atom_class` (`:317`, a node theory-equal to `{x}` is in
`x`'s class), `atoms`, `unit_class` and `materialized`.

| Hypothesis | Stated on | Supplied by | Runtime check |
|---|---|---|---|
| `h5₀`, `hrun`, `ha` | the view | assumed; equivalent to assuming I5 of the view | tier 1, as I5 |
| `h0` | the view | assumed: an atomic class's `rhs` is `{x}` (`class_rhs_into`) | tier 1, "a class with none is a leaf whose normal form is `{c}`" |
| `hcanon` | the stored `rhs` | assumed of the engine | tier 1 |
| `hfix` (`RoundFixedA`) | the view, plus the collapse | assumed of the engine at convergence | tier 2, as `nf_present` and `cp_joinable` |
| `hcp` | the view's rules, which include `M → {x}` | assumed; not derived from `RoundFixedA` | tier 2 |
| `hcc` | the stored active nodes | assumed of the engine (hash-consing) | tier 1 |
| `hS` | the view: an asserted pair may relate a node to a constant | assumed of the input | none |
| `hcancel` | the view's rules | not an engine fact (Section 5.7); `CompleteAtoms` takes `hlat : L.cancellative → LatticeClosed L (st.withAtoms A u)` in its place since commit `1be51963` | tier 1, as lattice closure |
| `A` | a parameter | not derived from the engine's `atomic` bit | none |

`CC/AtomsEngine.lean` restates the engine-level theorems on the view:
`completion_complete_cancellative_engine_atoms` (`:57`, `LatticeClosed` of the view in place
of `hcancel`), `completion_complete_inverse_engine_atoms` (`:80`) and
`completion_complete_combined_engine_atoms` (`:108`, the unit as the implicit node
`(∅, u)`). `I3_withAtoms` (`:32`) carries the retirement invariant to the view, and
`invNodes_withAtoms` (`:45`) derives the one-element nodes the inverse rules R1 to R5 are
stated on from the implicit nodes, when every class a `g`-node touches is atomic.

**Non-vacuity.** `CC/AtomsWitness.lean` takes the program

```
(union (+ a b) c)
(let t (+ a b d))
(let u (+ c d))
```

over plain AC at its completion fixpoint: classes `a, b, c, d = 0, …, 3` are leaf constants,
the stored nodes are `{a, b}` in `c`'s class and `{a, b, d}`, `{c, d}` in class 4, and every
atom's right-hand side is its one-element monomial. `witness_complete` (`:251`) proves every
hypothesis of `CompleteAtoms` for this state, with the asserted equation `{a, b} = {c}`
between a stored node and a leaf constant. `witness_not_all` (`:297`) shows that
`I0ActiveAll` fails on the stored state: before `7838c767`, `completion_complete_at_convergence`
did not apply to any state with a leaf constant.

**Adequacy.**

- `A` is a parameter. The engine's `atomic` bit, set when a class is used as a child or holds
  a non-AC node, is not modelled, and the theorems hold for every `A` that meets their
  hypotheses.
- The witness is plain AC: it does not exercise the unit, the laws, `hcancel` (vacuous for a
  non-cancellative operator) or a non-trivial minimal-monomial history (`ss₀ = ss`). Its
  closing `example` derives `wst.find 4 = wst.find 4` and `wst.find 2 = wst.find 2`, which
  hold by reflexivity; it shows that the corollaries apply, not that they derive a merge the
  state lacks.
- `AtomCollapse` is assumed. That completion merges a node whose normal form is `{x}` into
  `x`'s class is the docstring's reading of `add`; no theorem relates it to a completion run.
- The docstring of `CC/Atoms.lean` (`:53`) names `completion_complete_atom_class`, which does
  not exist; the theorem is `CompleteAtoms.atom_class`.

## 6. Rounds and saturation

### 6.1 Rounds

A **round** (`Round`, `EMatch/Engine/Rounds/Round.lean:40`) is one transition of the
semi-naive loop as the matcher sees it. It holds the index snapshot of round r-1 (`before`),
the snapshot of round r after its actions and rebuild (`after`), and the engine's logs between
the two index builds. The logs are the added ids, the recorded unions, the subsumed ids, the
touched log, and the merge-membership delta. A node is new (`isNew`) when it is in the touched
log or the merge delta.

`Round.WF` (`:93`) states what rebuild guarantees:

```lean
structure WF (R : Round) : Prop where
  created_added : ∀ id, R.Created id → id ∈ R.added
  added_touched : ∀ id ∈ R.added, id ∈ R.touched
  recanon_touched : ∀ id, R.Recanon id → id ∈ R.touched
  subsumed_touched : ∀ id ∈ R.subsumed, id ∈ R.touched
  absorbed_delta : R.tracking = true → ∀ id, (∃ n', (id, n') ∈ R.after.nodes) →
    R.Absorbed id → id ∈ R.mergeDelta
  no_split : ∀ id id', R.before.find id = R.before.find id' → R.after.find id = R.after.find id'
  children_canon : R.after.ChildrenCanon
  find_idem : R.after.FindIdem
  dedup : ∀ id₁ id₂ n, (id₁, n) ∈ R.after.nodes → (id₂, n) ∈ R.after.nodes →
    R.after.find id₁ = R.after.find id₂
```

Each field corresponds to an engine operation. A fresh id is logged at registration
(`register_if_fresh`). Recanonicalization logs an id when its stored children change
(`egraph/src/caches.rs:541-547`). A merge pushes the absorbed class's members when tracking is
on (`merge_in_classes`). The union-find only merges. Rebuild precedes the index build, so
children are canonical. Hash-cons collisions merge, so equal nodes share a class. All fields
are assumptions about the engine; Section 6.4 notes the one partial derivation.

### 6.2 The delta

**`delta_complete`** (`EMatch/Engine/Rounds/Delta.lean:41`):

```lean
theorem delta_complete {R : Round} (hwf : R.WF) (htr : R.tracking = true)
    {atoms : List QAtom} {σ' : Binding}
    (hafter : Matches R.after atoms σ') (hbefore : ¬ Matches R.before atoms σ') :
    ∃ (k : Nat) (ak : RAtom), atoms[k]? = some (.scan ak) ∧
      ∃ id, σ'.node ak.node = some id ∧ R.isNew id = true
```

With merge tracking on, a binding that matches after the round and not before binds some
scanning atom's node to a new id.

*Proof.* By contraposition. A present node that is not new existed before with the same
stored node and the same representative (`Round.stable_of_not_new`, `Round.lean:134`). A
shallow pattern has variable arguments, so it reads the graph only through the node itself
(`matchN_shallow_iff`, `AtomDelta.lean:31`). Each atom satisfied after is therefore satisfied
before. `Eq` atoms do not read the graph.

**`semi_naive_round_complete`** (`EMatch/Engine/Rounds/Complete.lean:30`) combines
`delta_complete` with `variants_cover_new`. A naive match of the new snapshot that was not a
naive match of the old one is emitted by some variant, namely the one of its first new atom.

Two counter-models show the hypotheses are needed. `delta_incomplete_untracked`
(`Rounds/Counter.lean:184`) is a well-formed round without tracking in which a new match has no
new scanning node: a merge whose survivor is the id the parent already stores. That is why
the merge-membership delta exists. `delta_incomplete_global` (`:98`) is a well-formed tracked
round in which a rule constrains a class variable to a global's class; the absorbed class's
members enter the delta, but no atom scans them. The engine fixed this, the sixth recorded
engine gap, by routing such rules to naive matching.

### 6.3 Actions and their consequences

A rule (`Rule`, `EMatch/Engine/Saturate/Actions.lean:117`) is a list of query atoms, an
annotated plan, and a list of actions: `insert t`, `union a b`, or `subsume x`. A rewrite
`L => R` is `[union (var root) R]`, plus `subsume root` under `:subsume`.

`Den G σ t c` (`Actions.lean:62`) states that the right-hand-side term `t` is present in `G`
under `σ` with value `c`. A variable denotes its bound class. An application denotes the
class of a stored node whose children are literally the values of its subterms.

```lean
def ActFired (G : Graph) (σ : Binding) : Action → Prop
  | .insert t => ∃ c, Den G σ t c
  | .union a b => ∃ c, Den G σ a c ∧ Den G σ b c
  | .subsume _ => True

def Fired (G : Graph) (σ : Binding) (rule : Rule) : Prop :=
  ∀ act ∈ rule.actions, ActFired G σ act
```

An instance is fired when every inserted term is present and both sides of every union are
present in one class. For a rewrite, `Fired` says `R` is present in the class of the matched
root.

An `ActRound` (`Saturate/ActRound.lean:27`) is a round plus the bindings whose actions it
applied, with the facts that each applied action's consequence is present after the round and
each recorded union is merged. These four fields are assumptions about `apply.rs` and rebuild.

**Adequacy.** `Den` is literal. The engine's `add` splices same-operator children, drops
units, clamps nilpotent counts, cancels inverses, and returns an existing class for a
one-element term (`Normal::Single`). For such right-hand sides the `ActRound` facts cannot
hold; `den_misses_single` (`Fidelity/NormalizeSat.lean:210`) is the witness. `DenN`
(`Fidelity/Normalize.lean:85`) admits these normal forms. The final theorem uses `Den`.

### 6.4 The saturation invariant

The invariant has one round of latency. Matches on the snapshot a round read are fired in the
snapshot after its actions:

```lean
def InvLag (A : ActRound) (rules : List Rule) : Prop :=
  ∀ rule ∈ rules, ∀ σ, Matches A.R.before rule.atoms σ → Fired A.R.after σ rule
```

**`inv_step`** (`Saturate/Invariant.lean:85`) carries `InvLag` from round r-1 to round r.
Take a match on `A.R.before = prev.R.after`. If it was a match before the previous round, the
previous invariant fired it, and `fired_transport'` (`Saturate/Transport.lean:342`) keeps it
fired across a round without subsumption. Otherwise it is new: a naive-routed rule emits it
directly, and a tracked rule emits it from a variant (`semi_naive_round_complete`). Either way
the round's actions fire it (`fired_after_actions`, `ActRound.lean:51`).

`fired_transport` needs `Round.Persist` (`Transport.lean:45`): every non-subsumed node of
`before` survives in `after` with the same operator and its children mapped through the new
`find`. It also needs no subsumption, because a `:subsume` can remove from the index a node a
consequence is built of (`tests/egg/subsume.egg`).

**`saturation_complete`** (`Saturate/Invariant.lean:231`):

```lean
theorem saturation_complete {sig : Sym → Kind} {naive : Rule → Bool} {rules : List Rule}
    (A₀ : ActRound) (As : List ActRound) (hplan : PlansOK rules)
    (h₀ : RulesWF sig A₀.R.before rules) (hok : ∀ A ∈ A₀ :: As, RoundOK sig rules A)
    (hemit₀ : EmitsAll A₀ rules) (hchain : AChain naive rules A₀ As)
    {A : ActRound} (hA : A ∈ A₀ :: As) (hfix : A.R.Unchanged) :
    Saturate.Inv A.R.before rules ∧ Saturate.Inv A.R.after rules
```

Along a run (round 0 naive, then rounds each routing every rule naive or tracked), at a round
that changed nothing, every match of every rule is fired. `RoundOK` (`:125`) packs, per round,
`Round.WF`, tracking on, `Persist`, no subsumption, and well-formed rule atoms. `EmitsAll` and
`AChain` say the round applied every binding of every naive run or every variant run. The
routing `naive` is a free parameter, so every routing the engine uses is covered.
`Round.Unchanged` (`:177`) means the same node set and the same `find` before and after.

*Proof.* `invLag_chain` (`:153`) by induction with `inv_step`. At an unchanged round, `Den`,
`Fired` and `Matches` read the graph only through node membership and `find`, so the
one-round lag closes (`inv_of_unchanged`, `:219`).

**Adequacy.** The emission hypotheses state that the engine's matcher emits at least the
model's naive and variant sets on the frozen index and applies every one. The plan theorems
of Section 3 characterise the model's runs, not the Rust join. The engine skips an action
whose right-hand side has no value (`apply.rs:1346`). Budget exits stop the loop without a
fixpoint, and the theorem says nothing about them. `Persist` assumes recanonicalization is a
literal map; a unit drop or degenerate collapse at rebuild breaks it. The statement of
`WF.dedup` is derived for a modelled sequence store (`dedup_of_inv`,
`Rounds/SeqSplice.lean:234`), but no theorem builds a `Round.WF` from it.

### 6.5 The fidelity variants

`Fidelity/` closes several of these gaps, one at a time, for the saturation theorem:

- `Fidelity/Index.lean`: the index is the store filtered by the skip predicates of
  `egraph/src/index.rs:521-537`. `matches_index_iff` (`Fidelity/Index.lean:89`) states that matching the index
  is matching the store at unskipped nodes.
- `Fidelity/Subsume.lean`: `saturation_complete_store` (`:238`) allows `:subsume`. Matches
  are read on the index and consequences on the store.
- `Fidelity/Normalize.lean`, `NormalizeSat.lean`: `saturation_complete_N` (`:186`) reads
  right-hand sides as the normal forms `add` builds (`DenN`).
- `Fidelity/Sound.lean`: `denN_sound` (`:123`) states that what the actions build denotes the
  right-hand side in every model of the graph and the operator laws. Round-level soundness
  with rebuild's merges is open.
- `Fidelity/StopTest.lean`: `engine_stop_unchanged` (`:234`) derives `Unchanged` from the
  engine's stop test, which requires no reported change and an unmoved size stamp
  (node count, class count). It assumes `rebuild_idle`: a rebuild after an action phase that
  minted and merged nothing changes nothing. `saturation_complete_engine` (`:253`) and its
  variants take the stop test in place of `Unchanged`.

## 7. The final theorem

### 7.1 The represented graph

The final theorem reads an e-matching graph off a completion state
(`CC/Bridge/Represents.lean:36-63`):

```lean
def nodeId (p : Monomial n × Fin n) : NodeId := n + Encodable.encode p

def mkNode (st : State n) (f : Sym) (p : Monomial n × Fin n) : Node :=
  ⟨f, .mset (p.1.map fun x => clsId (st.find x))⟩

noncomputable def represents (st : State n) (f : Sym) (A : Finset (Monomial n × Fin n)) : Graph :=
  ⟨A.toList.map fun p => (nodeId p, mkNode st f p), findId st⟩

def Enumerates (st : State n) (A : Finset (Monomial n × Fin n)) : Prop :=
  ∀ p, p ∈ A ↔ p ∈ st.active
```

There is one `f`-multiset node per active node of the state. Its children are the
representatives of the summand classes, and its class is the representative of its CC class.
Class ids are `0` to `n - 1`, and node ids are offset by `n`.

The bridge theorems need only half of `Enumerates`: `Within st A` (`Represents.lean:69`)
says every node of `A` is an active node of `st`. Commit `15b5fa2e` restated
`ac_equal_same_class_graph`, `matches_closed_under_theory` and the engine-match theorems of
`CC/Bridge/Modulo.lean` with `Within`, because an enumeration of the stored active nodes is
`Within` the completion view of Section 5.9 but does not enumerate it.

### 7.2 Statement

**`saturation_modulo_complete`** (`Final/Main.lean:225`):

```lean
theorem saturation_modulo_complete {sig : Sym → Kind} {naive : Rule → Bool} {rules : List Rule}
    (A₀ : ActRound) (As : List ActRound) (hplan : PlansOK rules)
    (h₀ : RulesWF sig A₀.R.before rules) (hok : ∀ A ∈ A₀ :: As, RoundOK sig rules A)
    (hemit₀ : EmitsAll A₀ rules) (hchain : AChain naive rules A₀ As)
    {A : ActRound} (hA : A ∈ A₀ :: As) (hfix : A.R.Unchanged)
    {L : Laws n} {S : Set (Monomial n × Monomial n)} {st : State n}
    {act : Finset (Monomial n × Fin n)} (hcomp : CompleteHyps L S st)
    (henum : Enumerates st act) {f : Sym} (hG : A.R.after = represents st f act) :
    ∀ rule ∈ rules, ∀ (P : Pat) (r : Var), rule.atoms = (atoms P r).map QAtom.scan →
      P.head = some f →
      ∀ p ∈ act, ∀ p' ∈ act, E L S p.1 p'.1 →
      ∀ σ, Matches A.R.after rule.atoms σ → σ.node r = some (nodeId p') →
        Fired A.R.after σ rule ∧
        σ.cls r = some (A.R.after.find (nodeId p)) ∧
        MatchC A.R.after P (A.R.after.find (nodeId p)) σ
```

Take a run of the saturation loop and a round `A` that changed nothing. Assume its after
snapshot is the graph of operator `f` read from a converged completion state. Consider a rule
that is one pattern `P` with head `f`, two theory-equal active nodes `p` and `p'`, and a match
`σ` rooted at `p'`'s node. Then the instance is fired, `σ`'s root class is `p`'s class, and
`σ` matches `P` at that class. At the fixpoint, a rule has fired on every instance modulo the
theory, at the class level.

`CompleteHyps` (`CC/Bridge/Modulo.lean:36`) packages the hypotheses of
`completion_complete_at_convergence` as they appear in Section 5.3, with `hcancel` replaced by
`hlat : L.cancellative → LatticeClosed L st` since commit `1be51963`: `ac_equal_same_class`
goes through `completion_complete_cancellative_engine` (Section 5.7).

**`saturation_modulo_complete_atoms`** (`Final/Main.lean:255`) is the same statement for a
completion state with leaf constants. Its completion hypothesis is `CompleteAtoms L S st X u`
(Section 5.9), `act` enumerates the stored active nodes, and the graph is `represents st f act`,
the graph of the stored nodes:

```lean
theorem saturation_modulo_complete_atoms ...
    {L : Laws n} {S : Set (Monomial n × Monomial n)} {st : State n} {X : Set (Fin n)}
    {u : Option (Fin n)} {act : Finset (Monomial n × Fin n)} (hcomp : CompleteAtoms L S st X u)
    (henum : Enumerates st act) {f : Sym} (hG : A.R.after = represents st f act) :
    ∀ rule ∈ rules, ∀ (P : Pat) (r : Var), rule.atoms = (atoms P r).map QAtom.scan →
      P.head = some f →
      ∀ p ∈ act, ∀ p' ∈ act, E L S p.1 p'.1 →
      ∀ σ, Matches A.R.after rule.atoms σ → σ.node r = some (nodeId p') →
        Fired A.R.after σ rule ∧
        σ.cls r = some (A.R.after.find (nodeId p)) ∧
        MatchC A.R.after P (A.R.after.find (nodeId p)) σ
```

The rounds hypotheses, elided above, are those of `saturation_modulo_complete`. The asserted
equations and the theory may relate a node to a constant (`a + b = c`); the conclusion is
about stored nodes `p`, `p'`. The proof instantiates `saturation_modulo_complete_within`
(`:119`) at the view `st.withAtoms X u`, with `CompleteHyps.ofAtoms` (`CC/Bridge/Modulo.lean:60`)
and `Enumerates.within_withAtoms` (`:86`); the graph of the view is the graph of the stored
state by definition (`represents_withAtoms`, `:77`).

### 7.3 Hypotheses

| Hypothesis | Meaning | Status |
|---|---|---|
| `A₀`, `As` | the rounds, with their applied bindings and action facts | assumed; `Den` is literal (Section 6.3) |
| `hplan` | each rule's plan is in the scheduler grammar | assumed; no theorem proves the Rust scheduler emits `SchedA` plans |
| `h₀`, `hok` | rule atoms well formed; per round: `WF`, tracking, `Persist`, no subsumption | assumed; `Persist` fails when rebuild drops a unit or collapses a node |
| `hemit₀`, `hchain` | every naive or variant binding was applied | assumed of the engine's matcher |
| `hfix` | round `A` changed nothing | assumed here; `engine_stop_unchanged` derives it from the stop test, but this theorem does not use it |
| `hcomp` | completion has converged | assumed; includes `hlat` (lattice closure, in place of `hcancel`); `CompleteAtoms` in the leaf-constant form |
| `henum` | `act` is the set of stored active nodes | definitional |
| `hG` | the fixpoint snapshot is the represented graph | assumed; the weakest point (Section 7.5); replaced by `SubRep` on the index in `saturation_modulo_complete_store_atoms` (Section 7.7) |
| `rule.atoms = ...`, `P.head = some f` | the rule's query is one pattern with head `f` | side conditions; no `Eq` atoms, no globals |

The runtime design note checks `hplan` and `h₀` once per rule at compilation, assigns `hfix`
to tier 2 (the stop test), and replaces the history hypotheses `hok`, `hemit₀` and `hchain` by
one naive matching round at the final state, which checks the conclusion of
`saturation_complete` directly. It has no check for `hG`, which no engine state satisfies
(Section 7.5).

### 7.4 Proof

Since commit `8932dc12` the proof is that of `saturation_modulo_complete_sub`
(`Final/Main.lean:89`), which takes `SubRep A.R.after st f act ι` in place of `hG`;
`saturation_modulo_complete_within` (`:119`) applies it with `represents_subRep`, and
`saturation_modulo_complete` applies that with `henum.within`. It has three independent
parts. The text below describes the proof before that commit; the changes are noted.

1. **Fired.** `saturation_complete` gives `Saturate.Inv A.R.after rules`, which applied to the
   match is the first conjunct.
2. **The root.** After rewriting with `hG`, `matches_at_active` (`Final/Main.lean:36`) applies
   `backOk` to the atoms. It finds an active `q` with `σ.node r = some (nodeId q)` and `MatchN`
   at `mkNode st f q`. Injectivity of `nodeId` gives `q = p'`. (Now `matches_at_sub`, `:67`:
   `backOk` gives a node of `A.R.after` under the id `ι p'`, and `KeysNodup` identifies it
   with the represented node `mkNode st f p'`.)
3. **The theory.** `ac_equal_same_class_graph` (`CC/Bridge/Modulo.lean:101`) gives
   `find (nodeId p') = find (nodeId p)`, by `completion_complete_at_convergence`.
   `matches_closed_under_theory` (`:144`) lifts the node match at `p'` to a class match at `p`'s
   class through `MatchC.app`. (Now `ac_equal_same_class_sub` and
   `matches_closed_under_theory_sub`, `CC/Bridge/Sub.lean`, the same argument on a part.)

The theory enters only through "theory-equal active nodes share a class". Lifting a node match
to a class match is one constructor. Neither `NoCollapse` nor `matches_transport` appears in
the proof: `saturation_complete` never transports a match across a merge, because it
case-splits on whether the match existed before the round.

### 7.5 What the theorem does not say

**The represented graph holds only active `f`-nodes.** `represents` contains one `f`-multiset
node per active node and nothing else. Summand classes have no nodes, other operators are
absent, and retired nodes are dropped. The engine's index holds leaf nodes, other operators,
and retired `FLAG_AC_COLLAPSED` nodes, which the index does not skip (`index.rs:521-537`). So
`hG` restricts the theorem to an index that contains only active `f`-multiset nodes. No
theorem relates `st` to the earlier rounds or to the engine's rebuild. The leaf-constant form
keeps this restriction: `represents st f act` has no node for a leaf constant either, so the
leaf constants enter `saturation_modulo_complete_atoms` only through the theory `E L S`. A
rule whose pattern names a constant, such as `(rewrite (+ a b) c)` with `a`, `b`, `c` nullary
operators, has no match on this graph, because `.plain a []` matches only a stored node of
operator `a`. The theorem covers such a rule only in the empty sense.

*Resolved by commit `8932dc12`.* `saturation_modulo_complete_store_atoms` replaces `hG` by
`SubRep A.Sa.index st f act ι`: the represented graph is a part of the index, which may hold
leaf nodes, other operators, the nodes the right-hand sides build and retired nodes
(Section 7.7). `saturation_modulo_complete_sub` does the same for the literal form.

**The hypotheses are contradictory for many rules.** `Fired` requires every application in the
right-hand side to be a stored node of `A.R.after` (through `Den`). Under `hG` the only stored
nodes are `f`-multiset nodes with literal children. Suppose a rule has a match at the fixpoint
and its right-hand side builds any other node, for example `(rewrite (f x y) (g x))`.
`saturation_complete` derives `Fired` for that match, and `Fired` cannot hold. The hypotheses
are then jointly unsatisfiable, and the theorem holds vacuously for that rule set. The theorem
has content for rules whose right-hand sides are variables or literal `f`-terms the store holds
as written. Neither the docstring nor `STATUS.md` states this restriction. No theorem in the
development exhibits rounds, a state and rules that satisfy all the hypotheses together.

The same holds of `saturation_modulo_complete_atoms`, with one more case. Its `hG` is the same
equation with the same `represents`, and `Den` reads only `A.R.after`, so a right-hand side
that builds a node other than an active `f`-multiset node of `act` again makes the hypotheses
contradictory once the rule has a match. A right-hand side that names a leaf constant, or
that is a one-element `f`-term `(f x)`, needs a stored node the graph does not have: the
implicit nodes of the view are not nodes of `represents`. `AtomsWitness.witness_complete`
establishes `CompleteAtoms` for one state, which removes the doubt about the completion
hypotheses alone; it does not construct rounds, so the joint satisfiability of the saturation
hypotheses with `hG` remains unshown.

*Resolved by commit `8932dc12`.* `saturation_modulo_complete_store_atoms` reads the
right-hand sides as the normal forms `add` builds (`DenN`, `FiredN`) on the store, and the
completion state only through the `f`-part of the index. `witness_saturation_modulo_complete`
(`Final/Witness.lean`) applies it to two concrete rounds of a rule whose right-hand side is a
node of another operator, with every hypothesis proved (Section 7.7). The old statements are
kept; their docstrings now state the restriction (limit 3).

**The final theorem uses the least faithful layer.** It uses literal `Den`, no subsumption, the
graph read as the index, and `Unchanged` assumed. Section 6.5 lists the theorems that remove
each restriction. None of them is composed with the bridge into a theorem modulo the theory.

**Two limits are stated in the docstring.** A theory-equal term absent from the graph has no
node and is matched through its class only. The per-node form, "a binding at `p` yields one at
`p'`", is false: `per_node_form_fails` (`CC/Bridge/Modulo.lean:251`) gives a state with nodes
`f{0, 1, 2}` and `f{0, 3}` in one class, where `f{x, y, z}` matches the first and cannot match
the second. That witness does not establish `CompleteHyps` for its state. The second limit is
that maximum partition loses a two-item match when its two children classes merge
(`proofs/repro/ac_collapse.egg`). The proof does not need a hypothesis about it.

### 7.6 The matching-side theorem

**`saturation_modulo_sound`** (`Final/Main.lean:288`) states that every binding the naive run
emits on the represented graph is a match at some active node `p'`, and a class-level match at
every `p` theory-equal to `p'`. It involves no rounds. `STATUS.md` calls it the converse of the
completeness theorem; it is the soundness of one matching run on one graph. Its docstring says
that soundness of the actions is not modelled, because `Fired` asks only that a consequence is
present, and a hash-cons hit or a completion-minted node can also account for it.

### 7.7 The final theorem over the store

Commit `8932dc12` states the final theorem on the store model of `Fidelity/` (Section 6.5),
with the completion state entering through the `f`-part of the index only.
`SubRep G st f act ι` (`CC/Bridge/Sub.lean`) says that each `p ∈ act` is stored in `G` under
the id `ι p` with the children of `mkNode st f p`, and that `G.find (ι p)` is its class in
`st`. Nothing is said of `G`'s other nodes. `represents_subRep` gives the old graph as the
case `ι = nodeId`. `ac_equal_same_class_sub` and `matches_closed_under_theory_sub` are the
bridge theorems on such a part.

**`saturation_modulo_complete_store_atoms`** (`Final/Store.lean`):

```lean
theorem saturation_modulo_complete_store_atoms {ops : Sym → OpLaws} {sig : Sym → Kind}
    {naive : Rule → Bool} {rules : List Rule}
    (A₀ : SActRoundN ops) (As : List (SActRoundN ops)) (hplan : PlansOK rules)
    (h₀ : RulesWF sig A₀.R.before rules) (hok : ∀ A ∈ A₀ :: As, RoundOKN sig rules A)
    (hemit₀ : EmitsAllN A₀ rules) (hchain : SChainN naive rules A₀ As)
    {A : SActRoundN ops} (hA : A ∈ A₀ :: As) (hfix : A.Unchanged)
    {L : Laws n} {S : Set (Monomial n × Monomial n)} {st : State n} {X : Set (Fin n)}
    {u : Option (Fin n)} {act : Finset (Monomial n × Fin n)} (hcomp : CompleteAtoms L S st X u)
    (hw : Within st act) {f : Sym} {ι : Monomial n × Fin n → NodeId}
    (hs : SubRep A.Sa.index st f act ι) :
    ∀ rule ∈ rules, ∀ (P : Pat) (r : Var), rule.atoms = (atoms P r).map QAtom.scan →
      P.head = some f →
      ∀ p ∈ act, ∀ p' ∈ act, E L S p.1 p'.1 →
      ∀ σ, Matches A.Sa.index rule.atoms σ → σ.node r = some (ι p') →
        FiredN A.Sa.graph ops σ rule ∧
        σ.cls r = some (A.Sa.find (ι p)) ∧
        MatchC A.Sa.index P (A.Sa.find (ι p)) σ ∧
        MatchN A.Sa.index P (mkNode st f p') σ
```

Matches are read on the index, which is the store filtered by the skip predicates
(Section 6.5); consequences are read on the store as normal forms; `:subsume` is allowed.
The conclusion adds to the old one that the matched node is the represented node of `p'`.
`saturation_modulo_complete_store` is the form with `CompleteHyps`,
`saturation_modulo_complete_store_engine` takes the engine's stop test in place of
`Unchanged`, and `saturation_modulo_complete_store_cover` adds `FCover` (every `f`-node of
the index is the node of some `p ∈ act`) and then concludes for every match, whatever its
root. The proof is that of Section 7.4 with `saturation_complete_N` in place of
`saturation_complete`; `matches_at_sub` identifies the matched node through `KeysNodup`.

**The witness.** `Final/Witness.lean` takes the completion state of `CC/AtomsWitness.lean`
(the program `(union (+ a b) c)`, `t = a + b + d`, `u = c + d`) and adds the rule
`(rewrite (+ x y) (g x y))` with `g` a plain binary operator. The store holds the four leaf
constants, the three `+`-nodes `{a, b}`, `{a, b, d}`, `{c, d}`, and after round 0 the four
`g`-nodes `g(a, b)`, `g(b, a)`, `g(c, d)`, `g(d, c)`. Round 0 matches on the initial store and
builds the `g`-nodes; round 1 matches on the result, builds nothing new and is the fixpoint.
Every hypothesis is proved by hand and `decide`, no `native_decide`:
`witness_saturation_modulo_complete` is the final theorem itself, applied to this run, and
`witness_fires_modulo` reads its conclusion at the match `x ↦ c, y ↦ d` rooted at `{c, d}` for
the theory-equal node `{a, b, d}`. The rule is routed naive in both rounds, so the semi-naive
branch of `SChainN` is not exercised; the matches are characterized on the concrete graphs
(`match_cases`), not by running the plan.

**What remains.** `SubRep`, `CompleteAtoms` and the round facts are still hypotheses: no
theorem relates the completion state to the rounds or to the engine's rebuild, so the
theorem says nothing about a run whose index does not hold the active nodes of a converged
state. `hcp` and the minimal-monomial hypotheses stay in `CompleteAtoms`
(Section 10, items 5 and 6), and `hcancel` is replaced by lattice closure (item 3, resolved), and `StorePersist` assumes recanonicalization is a literal
map (item 9).

## 8. Counterexamples and the engine defects they record

Several theorems are refutations. Each records an engine defect that was fixed, or a
hypothesis that cannot be dropped. Those marked "eval" are `#eval` scripts whose expected
outputs appear only in comments; nothing asserts them.

| Lean | File | What it shows | Fixture |
|---|---|---|---|
| `shrinkNoRefresh_breaks_I5` | `CC/Slot.lean:290` | a shrink without refreshing the minimal monomial breaks I5 and drops a rule; fixed by `refresh_min_monomial` | |
| `idOrder_grow_breaks_I5` | `CC/MinMonoKey.lean:250` | under the id order a renamed node grows past its classmate; fixed by per-class order keys | `ac_minmono_grow_wa.egg` |
| `witness_not_all` | `CC/AtomsWitness.lean:297` | the former `I0Active` (now `I0ActiveAll`) fails on a state with a leaf constant, and on every state with a class that holds no active node; fixed by weakening `I0Active` in `7838c767` | |
| `hcancel_not_derivable` | `CC/Lattice.lean:725` | lattice closure does not give `hcancel` | `cancel_lattice.egg` |
| `left_off_spine_unsound`, `right_off_spine_unsound` | `CC/ARound/Basic.lean:390`, `:420` | `a_round` before commit `7beed39f` rewrote off the spine and was unsound | `ac_fold_completion_spine.egg` |
| `stub_counterexample` | `CC/Proofs/CriticalPairModulo.lean:202` | the earlier local-confluence lemma is false; motivates rules plus law instances in `hcp` | |
| `invGen_cp_not_joinable` | `CC/Laws/Inverse.lean:512` | without `InvMatching` a generator critical pair is not joinable | |
| `combined_counterexample` | `CC/Laws/Combined.lean:160` | without `InvUnitFree` the composite clamp has two normal forms | |
| `delta_incomplete_untracked` | `Rounds/Counter.lean:184` | without the merge delta a new match has no new node | `semi_merge_membership_delta.egg` |
| `delta_incomplete_global` | `Rounds/Counter.lean:98` | a rule with a global misses a match under tracking; fixed by naive routing | `semi_eq_global_local.egg` |
| `raw_breaks_dedup` | `Rounds/SeqSplice.lean:292` | `add` spliced a same-operator child with stale children: two equal nodes in two classes | `seq_hashcons_miss_min.egg`, `rounds_r1_0581.egg` |
| `den_misses_single` | `Fidelity/NormalizeSat.lean:210` | literal `Den` has no value for a one-element AC right-hand side | |
| `per_node_form_fails` | `CC/Bridge/Modulo.lean:251` | matching modulo the theory holds at the class level only | |
| `fold_open_off_spine_unsound` | `Flatten/Fold.lean:138` | the flatten walk opened every position of a fold; fixed by `flatten::spine` | `flatten_fold_spine.egg` |
| `regroup_off_spine_unsound` | `Flatten/RegroupSound.lean:525` | regrouping off a fold's spine is unsound | |
| original demand rule on AC (eval) | `Flatten/FixCheck.lean:39-64` | the rule rejected a match that lives on no other view; fixed in commit `d95883f5` | `proofs/repro/demand-gap.egg` |
| kept-count rule under laws (eval) | `Flatten/LawsCheck.lean` | five cases where the corrected rule loses a match under inverse, identity, nilpotent and unit laws | |


## 9. Gaps between the model and the engine, and the status of the first edition's findings

This section collects the gaps from the adequacy notes above, in the order a reader trying
to strengthen the final theorem would meet them. The first edition of this guide (commit
`a5cfa2d7`, written against `6c37120b`) recorded each item below. Each now carries one of
three statuses, checked against the sources of this branch: **still true**; **resolved**,
with the commit and the theorem that resolve it; or **changed**, with what changed. Items
marked **new** were found for this edition.

**Hypotheses the engine does not discharge.**

1. **Still true.** `hG`: the final theorem is about an index that contains only active
   `f`-multiset nodes (Section 7.5). `saturation_modulo_complete_atoms` keeps the same `hG`;
   its graph has no node for a leaf constant. *Resolved since, by commit `8932dc12`:*
   `saturation_modulo_complete_store_atoms` takes `SubRep` on the index (Section 7.7).
2. **Still true, and it extends to the leaf-constant form.** Literal `Den` makes
   `saturation_modulo_complete` hold vacuously for any rule with a match whose right-hand side
   builds a node other than an active `f`-multiset node: under `hG` the only stored nodes are
   those, and `Fired` requires every right-hand-side application to be a stored node of
   `A.R.after`. `saturation_modulo_complete_atoms` has the same `hG` and the same `Fired`
   (Final/Main.lean:183-200), so the same rules make its hypotheses contradictory; a
   right-hand side naming a leaf constant or a one-element `f`-term is one more such case,
   because the implicit nodes of the view are not nodes of `represents` (Section 7.5).
   Neither docstring nor `STATUS.md` states the restriction, and no theorem exhibits rounds,
   a state and rules satisfying all the hypotheses together. This is the most serious
   finding of the guide: the hypotheses are joint, so one such rule with a match makes the
   theorem vacuous for every rule of the set, and a rule set whose right-hand sides use a
   second operator or a constant is the common case. *Resolved since, by commit `8932dc12`:*
   `saturation_modulo_complete_store_atoms` reads right-hand sides as normal forms on the
   store, and `witness_saturation_modulo_complete` proves all its hypotheses on a run of
   `(rewrite (+ x y) (g x y))` (Section 7.7).
3. **Resolved, by commit `1be51963`.** `CompleteHyps` and `CompleteAtoms` take
   `hlat : L.cancellative → LatticeClosed` in place of `hcancel`; `CompleteAtoms.same_class`
   and `ac_equal_same_class` go through `complete_of_latticeClosed` for a cancellative
   operator and through the rewriting argument, where `hcancel` is vacuous, otherwise. The
   final theorems are unchanged in statement. `hcancel` remains only in
   `completion_complete_at_convergence`, `completion_complete_atoms` and the inverse and
   combined `_engine` theorems, which the bundles no longer use for a cancellative operator.
4. **Still true, changed in detail.** `hcp` is not derived from `RoundFixed`. The engine
   skips disjoint and containment pairs (`egraph/src/egraph.rs:3881`) and states that the
   normalize pass handles containment; no theorem connects that pass to `hcp`. In the
   leaf-constant form `hcp` also ranges over the view's rules `M → {x}`.
5. **Still true.** The minimal-monomial hypotheses amount to assuming I5:
   `witness_complete` discharges them with `ss₀ = ss` and the reflexive run.
6. **Still true.** `TwoClassesL`, which ACI demand completeness needs, is assumed. The probe
   `aci1.egg` that `EMatch/Flatten/EngineComplete.lean:24` cites is not in the repository.
7. **Still true.** `Round.Persist` and `StorePersist` assume recanonicalization is a literal
   map. Rebuild's inverse-pair cancellation (`canon_repair_round`) and the nilpotent clamp
   are not.
8. **Still true.** `EnginePhase.rebuild_idle` is assumed. A completion that aborted on its
   budget could resume work in a later rebuild; the model does not represent
   `CompletionOutcome`. The runtime design note proposes a per-run check that the outcome is
   `Converged`.
9. **Resolved** by `7838c767` (`I0Active`, `CC/Assemble.lean:94`;
   `completion_complete_at_convergence_of_all`, `CC/Main.lean:125`). The first edition
   recorded that `I0Active` quantified over every class id of `Fin n`. It now constrains only
   the classes that hold an active node, and `hcc` only the active nodes;
   `witness_not_all` shows the former hypothesis failed on a state with leaf constants.
10. **New.** `AtomCollapse` and the set `A` of atomic classes are assumed (Section 5.9). No
    theorem derives the collapse from a completion run or `A` from the engine's `atomic` bit.

**Model components not connected to each other.**

1. **Still true, and stronger than recorded.** The mutable executor (`Env/`) is not
   connected to the scheduler theorems. The first edition located the conflict in the re-join
   `byRepr a.node`; `Env.WF`'s partition of variables into node and class variables already
   excludes every plan of a nested pattern, in either lowering order, because a nested child
   has one variable that is both a class and a node variable (Section 3.7). *Resolved since,
   by commit `f1e8be1a`:* per-step binding kinds, `planOK_envWF` and `exec_matches`
   (Section 3.7).
2. **Still true.** `runND` models the adaptive scheduler, and `exec` models static plans only.
3. **Still true.** Guards, literals and globals have per-step theorems only (Section 3.8).
4. **Still true.** The executable fold enumerator is not linked to `OTLeft` and `OTRight`
   (Section 4.5).
5. **Still true.** `Flatten/` feeds nothing above it: no module of `Saturate/`, `Bridge/`,
   `Final/` or `Fidelity/` imports it; `:flatten` and sequence rules across rounds are not
   modelled.
6. **Still true.** The fidelity variants of saturation are not composed with the bridge
   (Section 7.5). `saturation_modulo_complete_atoms` also uses `saturation_complete`, not
   `saturation_complete_engine`, `_store` or `_N`.
7. **Still true.** `ARound/` uses its own state, not `State`; joint termination with AC rounds
   is not proved.
8. **Resolved** by `29666b9a` and `992d9205` (`regroupSkipG_iff`,
   `EMatch/Flatten/RegroupSkip.lean:1222`; `regroupSkip_match_iff`, `:1410`). The first
   edition recorded that the engine's regrouping skips were not modelled and were argued
   acceptance-preserving in comments only. `RegroupSkipDefs.lean` now models the loop with
   its skips, and the match set equals that of the full enumeration for any laws (Section
   4.7). `212d3bc6` points the engine's comment at the proof.

**Engine behaviour not modelled.**

1. **Still true.** The engine re-activates collapsed nodes after a recanonicalization
   (`egraph/src/egraph.rs:2847-2857`). No `Infer` step un-retires a node.
   `refresh_min_monomial` returns early on collapsed nodes (`egraph.rs:1824`) and is called
   before the flag is cleared, so the re-activated node may not be folded into the minimal
   monomial. Whether this can break I5 is undecided.
2. **Still true.** The engine's `Comm` atom joins through `by_contains`, as AC does
   (`egraph/src/schedule.rs:749`). The model's `byContains` ignores pairs and adds a
   `decomposeComm` step with no Rust counterpart.
3. **Changed.** The view bounds `MAX_VIEWS`, `MAX_WORK` and `MAX_ELEMS`, the regrouping
   bounds `MAX_REGROUP_VIEWS` and `MAX_REGROUP_WORK`, and multiplicity widths appear as
   hypotheses or not at all. The regrouping skips are now modelled (item 8 above). The
   saturated view size of the engine's loop is not (Section 4.7).
4. **Still true.** Emitted lists are compared as sets; `Nodup` is not modelled beyond single
   steps.
5. **Still true.** The build-time spelling of an AC right-hand side (`flatten_mset_children`,
   which reads each argument class's `atomic` bit and minimal monomial) is outside
   `saturation_complete`. The engine covers it with `spelling_epoch`.
6. **New.** The engine's regrouping candidates come from the use lists of the view's
   classes; the model's are every filed `f`-member. The two give the same records, because a
   member holding no class of the view has no fit, but no theorem states it.

**Stale statements in the sources.** These do not affect the proofs, but they mislead a reader
who checks the Rust.

1. **Changed.** `Rounds/Round.lean:65-67` and `Rounds/Counter.lean:21-22` still say tracking
   is off in `saturate_semi`; `saturate_rules_semi` turns it on for every entry point
   (`egraph/src/saturate.rs:946-950`). The first edition also listed
   `Saturate/Invariant.lean:27-28`; that docstring says tracking is required, which is
   accurate, and the citation was an error of the first edition.
2. **Still true.** `InverseAxiomCP` (`CC/Laws/CriticalPairs.lean:146-149`) and
   `completion_complete_inverse` (`CC/Laws/Main.lean:96-101`) say the engine generates no
   rule-inverse pairs, citing `egraph.rs:3068`, which is now inside `a_round`. The engine
   generates them (`egraph/src/egraph.rs:3799-3829`).
3. **Still true.** The final theorem's docstring (`Final/Main.lean:131-132`) equates
   `Unchanged` with the loop's `changes == 0`. `Fidelity/StopTest.lean` shows that test was
   insufficient before the size-stamp fix.
4. **Still true.** `Flatten/RegroupFits.lean:17-19` says the chain theorems are proved for AC
   only; `Flatten/RegroupChain.lean` proves them for every kind.
5. **Still true.** Most line numbers cited in docstrings for `egraph.rs`, `saturate.rs`,
   `ematch.rs` and `flatten.rs` have drifted; the functions exist under the same names. The
   citations `egraph.rs:4291-4305` (`EMatch/Env/Exec.lean:39`) and `apply.rs:1401-1411`
   (`EMatch/Env/Snapshot.lean:46`) point at unrelated code. `Fidelity/StopTest.lean:14`
   cites `s11_self_union.egg` and `s11_assoc.egg`, which appear to have been renamed to
   `stop_self_union_mints.egg` and `stop_assoc_flatten_mints.egg`. `ac_collapse.egg` is in
   `proofs/repro/`. `spec-flatten.md`, cited by `EMatch/Flatten/Views.lean:6`, `Laws.lean:12`
   and `Main.lean:10`, is not in the repository; neither is
   `doc/goal-canonical-flatten-views.md`, which the Rust sources cite
   (`egraph/src/nary_canon.rs:4`, `seq_collect.rs:252`).
6. **New.** `CC/Atoms.lean:53` names `completion_complete_atom_class`, which does not exist
   (the theorem is `CompleteAtoms.atom_class`). `EMatch/Flatten/RegroupSkip.lean:10` names
   `regroupSkip_iff`, which does not exist (the theorem is `regroupSkipG_iff`).
7. **New.** `CC/MinMonoKey.lean:11`, `:215` and `STATUS.md` cite `grow_wa.egg`; the fixture
   is `egraph/tests/egg/ac_minmono_grow_wa.egg`.
8. **New.** The runtime design note
   ([`runtime-completeness-checks.md`](../../egraph/doc/future/runtime-completeness-checks.md))
   says in Section 6 that the regrouping skips are not modelled and have no check; since
   `29666b9a` they need none. Its Section 4 says the confirmation round checks `hcp`, which
   does not hold for the containment pairs the engine skips.

**Errors of the first edition, corrected here.** It cited `QAtom` and `Sched` one line early
(they are at `EMatch/Engine/Sched.lean:32` and `:74`), and `Round.Persist` at a line inside a
later proof (it is at `Saturate/Transport.lean:45`). It named the fixture of
`idOrder_grow_breaks_I5` `grow_wa.egg`; the fixture is `ac_minmono_grow_wa.egg`. It gave the
A-only round's file without its `CC/` prefix (`CC/ARound/Basic.lean`). It cited the chain
lemmas `regroupStep_mem`, `regroupChain_mem_levels` and `regroupChain_of_mem_levels` by bare
line numbers after a citation of `Flatten/RegroupNested.lean`, which its own convention read as that
file; they are in `Flatten/RegroupChain.lean`. The citation of `Saturate/Invariant.lean` among the stale tracking
statements was wrong (item 1 above).

## 10. Open findings

Each real finding with a proposed fix, most serious first. None is fixed in this edition:
the guide records them, and the fixes belong to the Lean sources, `STATUS.md` and the design
note. Items 1, 2 and 4 have since been resolved on branch `feat/real-rules`; each carries its
resolution after the original text.

1. Literal `Den` with `hG` makes both final theorems vacuous for any rule with a match whose
   right-hand side builds a node other than a stored active `f`-multiset node. Fix: state the
   final theorem over `DenN` and the store (`saturation_complete_N` with the bridge), and
   prove a witness with rounds, a state and one rewrite rule meeting every hypothesis.
   **Resolved** by commit `8932dc12`: `saturation_modulo_complete_store`,
   `saturation_modulo_complete_store_atoms` (and `_store_engine`, `_store_cover`) over
   `SActRoundN`, `DenN` and the index; `witness_saturation_modulo_complete` instantiates
   `saturation_modulo_complete_store_atoms` on two rounds of `(rewrite (+ x y) (g x y))` over
   leaf constants, and `witness_fires_modulo` reads its conclusion (Section 7.7). The old
   theorems are kept, with the restriction in their docstrings.
2. `hG` restricts the final theorems to a graph of active `f`-multiset nodes, with no leaf,
   retired or other-operator nodes. Fix: read the graph as the index filtered by
   `Fidelity/Index.lean`, with `represents` a subgraph of it, and prove the bridge for the
   subgraph. **Resolved** by commit `8932dc12`: `SubRep` and `FCover` (`CC/Bridge/Sub.lean`),
   `ac_equal_same_class_sub`, `matches_closed_under_theory_sub`; the store theorems take
   `SubRep A.Sa.index st f act ι`, and `saturation_modulo_complete_sub` restates the literal
   form with it.
3. *Resolved, commit `1be51963`.* `hcancel` stayed in `CompleteHyps` and `CompleteAtoms`, and
   the engine does not establish it. Fix applied: the bundles take `LatticeClosed` in place of
   `hcancel`.
4. `Env.WF` excludes every nested pattern, so `env_refine` does not cover the plans the
   scheduler emits. Fix: replace the `κ` partition by per-variable binding kinds that allow a
   variable to be both a child class and a joined node, and prove `PlanOK → Env.WF`.
   **Resolved** by commit `f1e8be1a`: `Env.WF κ B plan` with per-step kinds (`joinKinds`,
   `KindOk`), `env_refine` re-proved, `planOK_envWF` under `EnvAtomsWF`, `exec_matches`, and
   the worked plans of `(f (g x) y)` (`nested_plans_wf`, `nested_exec_matches`; Section 3.7).
5. `hcp` is not derived from `RoundFixed`, and the engine skips containment pairs. Fix: prove
   `hcp` from `cp_joinable` plus a model of the normalize pass, or state the containment pairs
   as an explicit hypothesis checked in tier 2.
6. The minimal-monomial hypotheses amount to assuming I5. Fix: replace `h5₀`, `hrun`, `ha`
   by `I5 st` in the statements, or link `OpsStar` to the inference run.
7. `AtomCollapse` and the atomic set `A` are assumed. Fix: derive `AtomCollapse` from a model
   of `add` returning `x`'s class, and `A` from a model of the `atomic` bit.
8. `TwoClassesL` is assumed, and the cited `aci1.egg` is missing. Fix: derive it from
   rebuild's merge of a one-class member, or commit the probe and cite it from `proofs/repro`.
9. `Round.Persist`, `StorePersist` and `rebuild_idle` are assumed. Fix: weaken `Persist` to
   normal-form recanonicalization (`DenN.persist`) and model `CompletionOutcome`.
10. The re-activation of collapsed nodes may break I5. Fix: add an un-retire step to `Infer`
    and prove I5 is preserved, or change the engine to refresh after clearing the flag.
11. The engine's regrouping loop saturates view sizes at `u64::MAX`, where the skip of a
    regrouped target can fire. Fix: prove the skip harmless under saturation, or assert in
    the engine that no regrouped target is reached.
12. The engine's regrouping candidates are a subset of the model's. Fix: prove that a member
    with no class in the view has no fit, and restate `hgs'` over members with a fit.
13. Soundness of regrouping under laws and for fold chains, and completeness under laws, are
    unproved. Fix: extend `regroup_views_sound_*` to `regroupLevels` with laws and to
    `OTLeft`/`OTRight` chains.
14. The executable fold enumerator is not linked to `OTLeft` and `OTRight`. Fix: prove
    `rawOptD` with a direction enumerates exactly their views.
15. Stale docstrings: tracking in `Rounds/Round.lean:65-67` and `Rounds/Counter.lean:21-22`;
    `egraph.rs:3068` in `CC/Laws/CriticalPairs.lean:146-149` and `CC/Laws/Main.lean:96-101`;
    `changes == 0` in `Final/Main.lean:131-132`; AC only in `Flatten/RegroupFits.lean:17-19`;
    `completion_complete_atom_class` in `CC/Atoms.lean:53`; `regroupSkip_iff` in
    `Flatten/RegroupSkip.lean:10`; `grow_wa.egg` in `CC/MinMonoKey.lean` and `STATUS.md`;
    drifted Rust line numbers and the renamed or missing files of Section 9. Fix: one pass over the
    docstrings replacing line numbers by function names.
16. `STATUS.md` calls the `_engine` theorems engine-level and `saturation_modulo_sound` the
    converse of completeness, and does not state the vacuity of item 1. Fix: state the
    remaining hypotheses and the restriction to right-hand sides the graph holds.
17. The runtime design note claims the skips have no check and the confirmation round
    checks `hcp`. Fix: drop the first claim and assign the containment pairs to tier 2.
