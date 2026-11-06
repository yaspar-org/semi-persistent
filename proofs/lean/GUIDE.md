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

The statements below are quoted from the sources as of 2026-11-06. File paths are relative
to `proofs/lean/SemperProofs/` unless they start with `egraph/`. In Sections 4, 6 and 8,
`Flatten/` abbreviates `EMatch/Flatten/`, and `Rounds/` and `Saturate/` abbreviate
`EMatch/Engine/Rounds/` and `EMatch/Engine/Saturate/`. A bare file name refers to the
directory of the theorem last cited. The build and the axiom
audit were not re-run for this guide; `STATUS.md` reports that `lake build` passes, that no
declaration uses `sorry`, and that every `#print axioms` in the `*Check.lean` files lists only
`propext`, `Classical.choice` and `Quot.sound`.

## Contents

1. Layers of the development
2. Common vocabulary
3. Matching on one frozen graph (`EMatch/`, `EMatch/Engine/`)
4. Flattened matching (`EMatch/Flatten/`)
5. Congruence closure modulo AC (`CC/`)
6. Rounds and saturation (`EMatch/Engine/Rounds/`, `EMatch/Engine/Saturate/`, `Fidelity/`)
7. The final theorem (`CC/Bridge/`, `Final/`)
8. Counterexamples and the engine defects they record
9. Gaps between the model and the engine

## 1. Layers of the development

The development has five layers. Each one models one part of the engine and proves its
results relative to a specification of its own. The final theorem joins three of them.

| Layer | Directory | Models | Headline results |
|---|---|---|---|
| Matching | `EMatch/`, `EMatch/Engine/` | one rule matched on a frozen index: atoms, lowering, scheduling, semi-naive variants | `plan_matches`, `runND_matches`, `variant_partition` |
| Flattened matching | `EMatch/Flatten/` | `:flatten` rules: views of nested same-operator children, demand, regrouping | `views_sound`/`views_complete`, `demand_engine_complete_*`, `regroup_match_iff` |
| Congruence closure | `CC/` | AC completion of one operator under its laws | `completion_sound`, `completion_complete_at_convergence` |
| Saturation | `EMatch/Engine/Rounds/`, `Saturate/`, `Fidelity/` | the round loop: deltas, actions, rebuild, the stop test | `delta_complete`, `saturation_complete` |
| Final | `CC/Bridge/`, `Final/` | the matching graph read from a completion state | `saturation_modulo_complete` |

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

A query is a list of `QAtom`s: scanning atoms and `Eq` atoms (`EMatch/Engine/Sched.lean:31`).
The plan grammar `Sched` (`:73`) admits any interleaving that lowers each scanning atom once
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
undoes them on backtrack (`egraph/src/ematch.rs:171`). `env_restore` and `env_refine`
(`EMatch/Env/Main.lean:28`, `:38`) state that the executor returns the environment it was
given, and that the bindings it emits are, as a set, the bindings `run` emits:

```lean
theorem env_refine (G : Graph) (κ : Var → Bool) (hG : G.ChildrenCanon) (hidem : G.FindIdem)
    {B : List Var} {plan : Plan} (hwf : WF κ B plan) (e : Env) (he : EnvOk e B) (σ : Binding) :
    σ ∈ (exec G κ plan e).1 ↔ σ ∈ run G plan (abs G κ e)
```

**Adequacy.** The theorem holds for plans that satisfy `Env.WF` (`EMatch/Env/Model.lean:612`),
and that predicate excludes plans the scheduler emits. Its `join` clause requires the join
target to be a node variable (`κ t = true`) and every variable a lookup reads to be a class
variable (`κ x = false`). The re-join `join a.node [byRepr a.node, byOp a.op]` that `lower`
emits for a bound node variable reads its own target, so it violates the clause. Every nested
atom lowered after its parent produces such a re-join. No theorem derives `Env.WF` from
`PlanOK`. The executor refinement is therefore not connected to `plan_matches` for nested
patterns, and nothing downstream uses `Env/`.

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
prove that spine-only opening trees preserve the fold's value.

**Adequacy.** These soundness theorems concern the inductive relations `OTLeft` and
`OTRight`. The executable spine enumerator (`rawOptD` with a direction, `FoldPlan.lean`) is
never proved to produce exactly those views. `runED_both` (`FoldPlan.lean:135`) shows only
that with no fold the fold-aware interpreter is the proved one. Demand completeness for folds
is argued in a docstring (`Fold.lean:27-30`), and regrouping soundness for folds is proved
for a single step only.

### 4.6 Regrouping

`fitsR` (`EMatch/Flatten/RegroupDefs.lean:99`) lists the raw views obtained by replacing one
occurrence of a group by its class. `regroupRec` and `regroupLevels` (`:140-163`) iterate it.
A regrouped record needs its group class to be taken, recorded as an extra leaf `needLeaf g`
so the demand rules apply unchanged. The engine keeps a record only if it needs at most as
many classes as the atom has items (`withinLimit`, `:199`).

Soundness, laws-free and without folds (`regroup_views_sound_ac`,
`EMatch/Flatten/RegroupSound.lean:251`):

```lean
theorem regroup_views_sound_ac {ctx : Ctx} (hκ : ctx.κ = .ac) {den : C → M}
    (hc : ConsistentAC ctx den) {limit : Nat} {n : Node} {w : List (C × Nat)} {d : DemandL}
    (h : (w, d) ∈ enumerateR ctx .both Laws.free limit n) :
    denAC den w = denAC den (kids .ac n.children)
```

In every commutative monoid where each `f`-member denotes its class, every view and every
regrouped view of `n` denotes the value of `n`. The ACI and `:assoc` versions use a join
semilattice and a monoid.

Completeness, laws-free, every kind and fold direction (`regroup_match_iff`,
`EMatch/Flatten/RegroupChain.lean:701`):

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

An n-ary atom holds under the regrouping enumerator exactly when a finite chain of
regroupings, starting from a view of the walk, reaches a view the shallow pattern matches.
The last record of the chain must need at most as many classes as the atom has items, and the
demand (leaves and needed classes) must be satisfied. `RegroupChain` is the reflexive
transitive closure of `RegroupStep`, and its view part `RegroupsTo` (`:60`) is declarative
multiset, set or list arithmetic. The limit bounds only the final record:
`regroup_nested_matches` (`RegroupNested.lean:81`) reaches a view through a record that needs
two classes midway.

*Proof.* Each step is a regrouping in the model and strictly shrinks the view's total count
(`regroupStep_mem`, `:424`). A chain therefore lies within the levels the model computes
(`regroupChain_mem_levels`, `:437`), and the converse holds (`regroupChain_of_mem_levels`,
`:658`).

**Adequacy.** The leaf and needs bookkeeping in `RegroupStep` reuses the model's `addG` and
`needsAfter`, so completeness is with respect to a declarative view transformation plus the
engine's own demand bookkeeping. Operators with laws are not covered. No theorem covers a
match that needs both a leaf refold and a regrouping. The engine's bounds `MAX_REGROUP_VIEWS`
(2^14 records) and `MAX_REGROUP_WORK` (2^20 entries) and its record skipping are not modelled;
the skipping is argued acceptance-preserving in comments.

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

The invariants (`CC/Defs.lean:214-236`, `CC/Assemble.lean:88`):

- **I0**: each class's `rhs` is a node of the class. `I0Active` requires an active node.
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

**`completion_complete_at_convergence`** (`CC/Main.lean:97`, proof in `CC/Assemble.lean:150`):

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
    (hcc : ∀ P c d, (P, c) ∈ st.nodes → (P, d) ∈ st.nodes → st.find c = st.find d)
    (hS : ∀ M N, (M, N) ∈ S →
      ∃ c d, (M, c) ∈ st.active ∧ (N, d) ∈ st.active ∧ st.find c = st.find d)
    (hcancel : L.cancellative → ∀ M N X,
      Joinable (Rw (plain n) (st.rules ∪ L.axRules)) (M + X) (N + X) →
      Joinable (Rw (plain n) (st.rules ∪ L.axRules)) M N)
    {M N : Monomial n} {c d : Fin n} (hM : (M, c) ∈ st.active) (hN : (N, d) ∈ st.active)
    (hMN : E L S M N) : st.find c = st.find d
```

At a state where the last round changed nothing, two active nodes with theory-equal monomials
are in one class. The hypotheses, and who is meant to supply each:

| Hypothesis | Meaning | Supplied by |
|---|---|---|
| `h5₀`, `hrun`, `ha` | slot maintenance from a good initial slot state, agreeing with `st` at the end | assumed; equivalent to assuming I5 (see below) |
| `h0` | every class's `rhs` is an active node of the class | assumed of the engine |
| `hcanon` | stored right-hand sides are clamp-normal | assumed of the engine (`nary_canon` output) |
| `hfix` | the round is fixed (`RoundFixed`) | assumed of the engine at convergence |
| `hlaw`, `hnf_ax` | law instances decrease `degLex`; clamp outputs are law-normal | discharged for every `NFLaw` instance |
| `hcp` | every critical pair of the rules and law instances is joinable under plain rewriting | reduced per law in `CC/Laws/`; the rule-rule part is assumed |
| `hcc` | two nodes with the same monomial share a class | assumed of the engine (hash-consing) |
| `hS` | every asserted pair is two active nodes of one class | assumed of the input |
| `hcancel` | joinability cancels a common summand | assumed; not an engine fact (Section 5.7) |

*Proof* (`CC/Assemble.lean:168-195`):

1. I5 holds of `st` (`reachable_I5`, `CC/Slot.lean:260`).
2. Each stored `rhs` is normal for `Rw L`: a step from it would go strictly down, and
   `nf_present` would put the normal form in the class, contradicting I5
   (`rhs_normal`, `Assemble.lean:98`).
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

- The slot hypotheses are equivalent to assuming I5. `OpsStar` is a reflexive transitive
  closure, and the slot run is never linked to the inference run. Taking `ss₀ = ss`, the
  triple holds whenever some slot state satisfies I5 and agrees with `st`. The engine content
  is that slot maintenance preserves I5 (`reachable_I5`, Section 5.5). That every engine run
  consists of the modelled slot operations is argued in prose.
- `hcp` is never derived from `RoundFixed`. The engine's critical-pair round establishes
  clamped joinability over the rules (`cp_joinable`). The theorem needs plain joinability
  over rules and law instances, including containment pairs, which the engine skips
  (`egraph/src/egraph.rs:3876`).
- `I0Active` quantifies over every class id in `Fin n`, so every id must carry an active node.
  The pool `n` must count exactly the classes in use.

### 5.4 Confluence and termination

`confluent_modulo` (`CC/Main.lean:30`) states that clamped rewriting is confluent when rules
and law instances are oriented, clamp produces law-normal forms, and every critical pair of
rules and law instances joins under plain rewriting. `kapur_termination` (`CC/Lemmas.lean:418`)
proves Kapur's termination argument from Dickson's lemma over abstract sequences of left sides.
It is not connected to `Infer`. `run_stabilizes` (`CC/Main.lean:23`) states that nodes and
partition are eventually constant along any run. Its proof uses only that `Fin n` is finite and
that a mint needs a fresh class, so it does not bound the engine's rounds.

### 5.5 The minimal-monomial slot

The engine stores each class's minimal monomial in a slot and refreshes it when a member
shrinks. `CC/Slot.lean` models the slot operations: mint, merge (fold the two minima), shrink
with refresh, and retire when a smaller classmate exists.

```lean
theorem reachable_I5 {st₀ st : SlotState n} (h₀ : I5 st₀) (hrun : OpsStar st₀ st) : I5 st
```

The proof is one case per operation (`op_I5`, `:251`). `shrinkNoRefresh_breaks_I5` (`:290`) is
the state of the engine bug in which a shrink did not refresh the slot.

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
hypotheses only. They still take `hcancel`, `hcc`, `hS`, the rule-rule condition `hRR`, and
conditions on left-hand sides. With a cancellative operator, which `inv_rules_sound`
requires, `hcancel` is the hypothesis Section 5.7 shows the engine does not establish.

### 5.7 The lattice round

Kapur's inferences alone do not establish `hcancel`. The fixture `cancel_lattice.egg` converged
without the equation `C5 = c1c3²`, which needs `c1c4² = c0²` and two copies of `c4 = c0c3`. The
engine therefore runs `lattice_round` at the completion fixpoint. Classes whose count vectors
differ by a member of the lattice spanned by the equations are merged.

`CC/Lattice.lean` formalizes the argument. A monomial's count vector is `vec M : Fin n → ℤ`.
`E_mem_lattice` (`:125`) shows theory-equal monomials differ by a lattice vector, for every
law set. `E_iff_mem_lattice` (`:218`) gives the converse when the theory is closed under
cancellation. `lattice_merge_sound` (`:500`) shows a lattice merge is a theory consequence and
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
Coset representatives are modelled as lattice membership only.

### 5.8 The A-only round and the countermodel

`CC/ARound/` models `a_round`, the inter-reduction for associative-only operators, on a
separate list-based state. A sequence denotes a fold. A rewrite is allowed at offset 0 for a
left fold, at the last offset for a right fold, and anywhere for an associative operator.
`rewrite_left_sound`, `rewrite_right_sound` and `rewrite_both_sound` (`ARound/Basic.lean:205`,
`:222`, `:245`) prove these sound in every magma or semigroup. `left_off_spine_unsound` and
`right_off_spine_unsound` (`:390`, `:420`) give counter-models in ℤ with subtraction for every
other offset. `aRound_sound` (`:495`) concludes that a spine-restricted merge preserves I2.

`CC/Countermodel.lean` gives the semantic side of `E`. `E_sound` (`:58`) states that
theory-equal monomials have equal value in every commutative-monoid model of the asserted
pairs and laws (cancellative if the operator is). `not_E_of_separates` (`:73`) follows: a
model that separates two monomials certifies that they are not theory-equal. The generator
`semper-conform-cc-cert` emits `check-neq` only on pairs such a model separates, so a failing
`check-neq` there is an engine unsoundness.

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

`fired_transport` needs `Round.Persist` (`Transport.lean:160`): every non-subsumed node of
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
  `egraph/src/index.rs:521-537`. `matches_index_iff` (`:89`) states that matching the index
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

### 7.2 Statement

**`saturation_modulo_complete`** (`Final/Main.lean:126`):

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

`CompleteHyps` (`CC/Bridge/Modulo.lean:35`) packages the hypotheses of
`completion_complete_at_convergence` as they appear in Section 5.3, including `hcancel`.

### 7.3 Hypotheses

| Hypothesis | Meaning | Status |
|---|---|---|
| `A₀`, `As` | the rounds, with their applied bindings and action facts | assumed; `Den` is literal (Section 6.3) |
| `hplan` | each rule's plan is in the scheduler grammar | assumed; no theorem proves the Rust scheduler emits `SchedA` plans |
| `h₀`, `hok` | rule atoms well formed; per round: `WF`, tracking, `Persist`, no subsumption | assumed; `Persist` fails when rebuild drops a unit or collapses a node |
| `hemit₀`, `hchain` | every naive or variant binding was applied | assumed of the engine's matcher |
| `hfix` | round `A` changed nothing | assumed here; `engine_stop_unchanged` derives it from the stop test, but this theorem does not use it |
| `hcomp` | completion has converged | assumed; includes `hcancel` |
| `henum` | `act` is the set of active nodes | definitional |
| `hG` | the fixpoint snapshot is the represented graph | assumed; the weakest point (Section 7.5) |
| `rule.atoms = ...`, `P.head = some f` | the rule's query is one pattern with head `f` | side conditions; no `Eq` atoms, no globals |

### 7.4 Proof

The proof (`Final/Main.lean:141-150`) has three independent parts.

1. **Fired.** `saturation_complete` gives `Saturate.Inv A.R.after rules`, which applied to the
   match is the first conjunct.
2. **The root.** After rewriting with `hG`, `matches_at_active` (`Final/Main.lean:36`) applies
   `backOk` to the atoms. It finds an active `q` with `σ.node r = some (nodeId q)` and `MatchN`
   at `mkNode st f q`. Injectivity of `nodeId` gives `q = p'`.
3. **The theory.** `ac_equal_same_class_graph` (`CC/Bridge/Modulo.lean:66`) gives
   `find (nodeId p') = find (nodeId p)`, by `completion_complete_at_convergence`.
   `matches_closed_under_theory` (`:109`) lifts the node match at `p'` to a class match at `p`'s
   class through `MatchC.app`.

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
theorem relates `st` to the earlier rounds or to the engine's rebuild.

**The hypotheses are contradictory for many rules.** `Fired` requires every application in the
right-hand side to be a stored node of `A.R.after` (through `Den`). Under `hG` the only stored
nodes are `f`-multiset nodes with literal children. Suppose a rule has a match at the fixpoint
and its right-hand side builds any other node, for example `(rewrite (f x y) (g x))`.
`saturation_complete` derives `Fired` for that match, and `Fired` cannot hold. The hypotheses
are then jointly unsatisfiable, and the theorem holds vacuously for that rule set. The theorem
has content for rules whose right-hand sides are variables or literal `f`-terms the store holds
as written. Neither the docstring nor `STATUS.md` states this restriction. No theorem in the
development exhibits rounds, a state and rules that satisfy all the hypotheses together.

**The final theorem uses the least faithful layer.** It uses literal `Den`, no subsumption, the
graph read as the index, and `Unchanged` assumed. Section 6.5 lists the theorems that remove
each restriction. None of them is composed with the bridge into a theorem modulo the theory.

**Two limits are stated in the docstring.** A theory-equal term absent from the graph has no
node and is matched through its class only. The per-node form, "a binding at `p` yields one at
`p'`", is false: `per_node_form_fails` (`CC/Bridge/Modulo.lean:216`) gives a state with nodes
`f{0, 1, 2}` and `f{0, 3}` in one class, where `f{x, y, z}` matches the first and cannot match
the second. That witness does not establish `CompleteHyps` for its state. The second limit is
that maximum partition loses a two-item match when its two children classes merge
(`proofs/repro/ac_collapse.egg`). The proof does not need a hypothesis about it.

### 7.6 The matching-side theorem

**`saturation_modulo_sound`** (`Final/Main.lean:166`) states that every binding the naive run
emits on the represented graph is a match at some active node `p'`, and a class-level match at
every `p` theory-equal to `p'`. It involves no rounds. `STATUS.md` calls it the converse of the
completeness theorem; it is the soundness of one matching run on one graph. Its docstring says
that soundness of the actions is not modelled, because `Fired` asks only that a consequence is
present, and a hash-cons hit or a completion-minted node can also account for it.

## 8. Counterexamples and the engine defects they record

Several theorems are refutations. Each records an engine defect that was fixed, or a
hypothesis that cannot be dropped. Those marked "eval" are `#eval` scripts whose expected
outputs appear only in comments; nothing asserts them.

| Lean | File | What it shows | Fixture |
|---|---|---|---|
| `shrinkNoRefresh_breaks_I5` | `CC/Slot.lean:290` | a shrink without slot refresh breaks I5 and drops a rule; fixed by `refresh_min_monomial` | |
| `idOrder_grow_breaks_I5` | `CC/MinMonoKey.lean:250` | under the id order a renamed node grows past its classmate; fixed by order keys (row EG1) | `grow_wa.egg` |
| `hcancel_not_derivable` | `CC/Lattice.lean:725` | lattice closure does not give `hcancel` | `cancel_lattice.egg` |
| `left_off_spine_unsound`, `right_off_spine_unsound` | `CC/ARound/Basic.lean:390`, `:420` | `a_round` before commit `7beed39f` rewrote off the spine and was unsound | `ac_fold_completion_spine.egg` |
| `stub_counterexample` | `CC/Proofs/CriticalPairModulo.lean:202` | the earlier local-confluence lemma is false; motivates rules plus law instances in `hcp` | |
| `invGen_cp_not_joinable` | `CC/Laws/Inverse.lean:512` | without `InvMatching` a generator critical pair is not joinable | |
| `combined_counterexample` | `CC/Laws/Combined.lean:160` | without `InvUnitFree` the composite clamp has two normal forms | |
| `delta_incomplete_untracked` | `Rounds/Counter.lean:184` | without the merge delta a new match has no new node | `semi_merge_membership_delta.egg` |
| `delta_incomplete_global` | `Rounds/Counter.lean:98` | a rule with a global misses a match under tracking; fixed by naive routing | `semi_eq_global_local.egg` |
| `raw_breaks_dedup` | `Rounds/SeqSplice.lean:292` | `add` spliced a same-operator child with stale children: two equal nodes in two classes | `seq_hashcons_miss_min.egg`, `rounds_r1_0581.egg` |
| `den_misses_single` | `Fidelity/NormalizeSat.lean:210` | literal `Den` has no value for a one-element AC right-hand side | |
| `per_node_form_fails` | `CC/Bridge/Modulo.lean:216` | matching modulo the theory holds at the class level only | |
| `fold_open_off_spine_unsound` | `Flatten/Fold.lean:138` | the flatten walk opened every position of a fold; fixed by `flatten::spine` | `flatten_fold_spine.egg` |
| `regroup_off_spine_unsound` | `Flatten/RegroupSound.lean:525` | regrouping off a fold's spine is unsound | |
| original demand rule on AC (eval) | `Flatten/FixCheck.lean:39-64` | the rule rejected a match that lives on no other view; fixed in commit `d95883f5` | `proofs/repro/demand-gap.egg` |
| kept-count rule under laws (eval) | `Flatten/LawsCheck.lean` | five cases where the corrected rule loses a match under inverse, identity, nilpotent and unit laws | |

The fixtures without a path are in `egraph/tests/egg/`.

## 9. Gaps between the model and the engine

This section collects the gaps from the adequacy notes above, in the order a reader trying
to strengthen the final theorem would meet them.

**Hypotheses the engine does not discharge.**

1. `hG`: the final theorem is about an index that contains only active `f`-multiset nodes
   (Section 7.5).
2. Literal `Den` makes the final theorem vacuous for rules that build any other node and
   have a match (Section 7.5).
3. `hcancel` remains in `CompleteHyps` and in the `_engine` theorems, although
   `hcancel_not_derivable` shows the engine does not establish it. The lattice variant
   `completion_complete_cancellative_engine` is not what the bridge uses.
4. `hcp` is not derived from `RoundFixed`. The engine skips containment pairs.
5. The slot hypotheses amount to assuming I5.
6. `TwoClassesL`, which ACI demand completeness needs, is assumed. The probe `aci1.egg` that
   `STATUS.md` cites is not in the repository.
7. `Round.Persist` and `StorePersist` assume recanonicalization is a literal map. Rebuild's
   inverse-pair cancellation (`canon_repair_round`) and the nilpotent clamp are not.
8. `EnginePhase.rebuild_idle` is assumed. A completion that aborted on its budget could
   resume work in a later rebuild; the model does not represent `CompletionOutcome`.

**Model components not connected to each other.**

1. The mutable executor (`Env/`) is not connected to the scheduler theorems: `Env.WF`
   excludes the re-join that `lower` emits for nested atoms (Section 3.7).
2. `runND` models the adaptive scheduler, and `exec` models static plans only.
3. Guards, literals and globals have per-step theorems only (Section 3.8).
4. The executable fold enumerator is not linked to `OTLeft` and `OTRight` (Section 4.5).
5. `Flatten/` feeds nothing above it; `:flatten` and sequence rules across rounds are not
   modelled.
6. The fidelity variants of saturation are not composed with the bridge (Section 7.5).
7. `ARound/` uses its own state, not `State`; joint termination with AC rounds is not proved.

**Engine behaviour not modelled.**

1. The engine re-activates collapsed nodes after a recanonicalization
   (`egraph/src/egraph.rs:2849-2857`). No `Infer` step un-retires a node.
   `refresh_min_monomial` returns early on collapsed nodes and is called before the flag is
   cleared, so the re-activated node may not be folded into the slot. Whether this can break
   I5 is undecided.
2. The engine's `Comm` join keeps a `by_contains` lookup and lowers through `DecomposeAC`.
   The model's `byContains` ignores pairs and adds a `decomposeComm` step with no Rust
   counterpart.
3. The view bounds `MAX_VIEWS`, `MAX_WORK` and `MAX_ELEMS`, the regrouping bounds, and
   multiplicity widths appear as hypotheses or not at all.
4. Emitted lists are compared as sets; `Nodup` is not modelled beyond single steps.
5. The build-time spelling of an AC right-hand side (`flatten_mset_children`, which reads each
   argument class's `atomic` bit and minimal monomial) is outside `saturation_complete`. The
   engine covers it with `spelling_epoch`.

**Stale statements in the sources.** These do not affect the proofs, but they mislead a reader
who checks the Rust.

1. `Rounds/Round.lean:65-67`, `Rounds/Counter.lean:21-22` and `Saturate/Invariant.lean:27-28`
   say tracking is off in `saturate_semi`. `saturate_rules_semi` now turns it on for every
   entry point (`egraph/src/saturate.rs:946-950`).
2. `InverseAxiomCP` (`CC/Laws/CriticalPairs.lean:146-149`) and `completion_complete_inverse`
   (`CC/Laws/Main.lean:99-101`) say the engine generates no rule-inverse pairs. It now does
   (`egraph/src/egraph.rs:3798-3830`).
3. The final theorem's docstring equates `Unchanged` with the loop's `changes == 0`.
   `Fidelity/StopTest.lean` shows that test was insufficient before the size-stamp fix.
4. `RegroupFits.lean:17-19` says the chain theorems are proved for AC only; `RegroupChain.lean`
   proves them for every kind.
5. Most line numbers cited in docstrings for `egraph.rs`, `saturate.rs`, `ematch.rs` and
   `flatten.rs` have drifted; the functions exist under the same names. The citations
   `egraph.rs:4291-4305` and `apply.rs:1401-1411` now point at unrelated code. The fixtures
   `s11_self_union.egg` and `s11_assoc.egg` appear to have been renamed to
   `stop_self_union_mints.egg` and `stop_assoc_flatten_mints.egg`. `ac_collapse.egg` moved
   to `proofs/repro/`. `spec-flatten.md` and `doc/goal-canonical-flatten-views.md` are not in
   the repository.
