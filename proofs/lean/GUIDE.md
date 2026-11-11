# A reader's guide to the Lean development

This guide explains what the Lean development in `proofs/lean` proves about the Semper
engine: the notions the proofs use, each headline theorem, and a sketch of its proof, so
that a reader can judge whether each Lean definition encodes the engine behaviour it is
named after. It describes the development as it stands on branch `feat/completeness-proofs`.
[`STATUS.md`](STATUS.md) is the per-file index of the same development, and
`scripts/check-proofs.sh` checks the build: `lake build` passes, no declaration uses `sorry`,
and every `#print axioms` in the `*Check.lean` files lists only `propext`, `Classical.choice`
and `Quot.sound`. [`HISTORY.md`](HISTORY.md) records how the development reached this state:
the engine defects the proofs located, the findings of the earlier editions of this guide
with the commits that close them, and the claims that have been withdrawn. The guide cites no
commit; a reader who wants the provenance of a theorem reads HISTORY.md.

Lean checks that each proof follows from its hypotheses, not that a definition describes the
engine or that the engine satisfies a hypothesis. Those two questions are the subject of this
guide. Each main theorem carries a paragraph marked **Reading** (what it assumes of the
engine, who supplies each hypothesis, what it concludes, what it leaves outside) and a table
that places each hypothesis in one of three classes:

- **derived**: a theorem derives it from a check the engine performs or from a definition
  that transcribes the engine's code; the table names the check and the theorem;
- **assumed**: it states a correspondence between the Rust state and the model that no
  theorem derives; Section 9 lists every such hypothesis as a gap;
- **limit**: a documented limit of the guarantee, with the counter-model theorem that shows
  the hypothesis cannot be dropped.

Sections 3 to 7 are Part A, what the development proves, with the pseudo-code of each
algorithm the model states placed next to the theorems about it. Section 8 is Part B, the
conformance and mirror tests that compare the executable models with the engine, and the
fixtures grouped by the theorem or invariant each probes. Section 9 is Part C, the remaining
gaps, each with what closes it and its acceptance criterion. Section 10 lists the
constraints the engine keeps, each with the counter-model and fixture that evidence it.

Conventions. File paths are relative to `proofs/lean/SemperProofs/` unless they start with
`egraph/` or `proofs/`. `Flatten/` abbreviates `EMatch/Flatten/`; `Rounds/` and `Saturate/`
abbreviate `EMatch/Engine/Rounds/` and `EMatch/Engine/Saturate/`. A bare file name refers to
the directory of the theorem last cited, and a bare `:N` to the Lean file last cited. A
fixture without a path is in `egraph/tests/egg/`. Line numbers are those of the sources at
the time of writing and drift; the names are stable. A pseudo-code block states an algorithm
as the Lean model does: a trailing comment names the Lean definition or step the line
corresponds to, then the Rust function (`egraph/src/` unless a path is given), and the
sentence after the block says where the engine does more or differently.

Several hypotheses are meant to be checked on each run rather than proved of the engine. The
design note [`runtime-completeness-checks.md`](../../egraph/doc/future/runtime-completeness-checks.md)
assigns each to a tier (tier 1: every run, one pass over the nodes; tier 2: in CI, by a
proved Lean checker on a dump of the final state); the hypothesis tables cite its tiers. Two
of its tier 1 checks exist in the engine as debug checks (`check_min_monomial_invariant`,
`debug_check_congruent_dup_invariant`); the others are design (Section 9).

## Contents

1. Layers of the development
2. Common vocabulary

Part A. What the development proves

3. Matching on one frozen graph (`EMatch/`, `EMatch/Engine/`)
4. Flattened matching (`EMatch/Flatten/`)
5. Congruence closure modulo AC (`CC/`)
6. Rounds and saturation (`EMatch/Engine/Rounds/`, `EMatch/Engine/Saturate/`, `Fidelity/`)
7. The final theorem (`CC/Bridge/`, `Final/`)

Part B. Conformance

8. Conformance and mirror tests, and the fixtures

Part C. Gaps and constraints

9. Remaining gaps
10. Constraints on the engine, with their evidence

## 1. Layers of the development

The development has five layers. Each models one part of the engine and proves its results
relative to a specification of its own. The final theorem joins three of them.

| Layer | Directory | Models | Headline results |
|---|---|---|---|
| Matching | `EMatch/`, `EMatch/Engine/` | one rule matched on a frozen index: atoms, lowering, scheduling, semi-naive variants | `plan_matches`, `runND_matches`, `variant_partition` |
| Flattened matching | `EMatch/Flatten/` | `:flatten` rules: views of nested same-operator children, demand, regrouping, the engine's regrouping loop and its overlap stage under idempotence | `views_sound`/`views_complete`, `demand_engine_complete_*`, `regroup_match_iff`, `regroupSkip_match_iff`, `regroupSkipO_match_iff_laws` |
| Congruence closure | `CC/` | AC completion of one operator under its laws, with leaf constants | `completion_sound`, `completion_complete_at_convergence`, `completion_complete_atoms` |
| Saturation | `EMatch/Engine/Rounds/`, `Saturate/`, `Fidelity/` | the round loop: deltas, actions, rebuild, the stop test | `delta_complete`, `saturation_complete` |
| Final | `CC/Bridge/`, `Final/` | the matching graph read from a completion state | `saturation_modulo_complete`, `saturation_modulo_complete_atoms` |

Two further directories are tools. `Conform/` holds generators that emit `.egg` programs
whose expected answers come from the Lean reference interpreters. The `*Check.lean` files
print the axioms of the headline results.

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
AC (`mset`), and set for ACI (`set`). Class ids, node ids, symbols and variables are natural
numbers, and a node's class is `G.find id`.

The type carries no invariant: ids may repeat, `find` need not be idempotent, and stored
children need not be representatives. Theorems add these as hypotheses when needed:
`KeysNodup` (distinct node ids), `Conforms sig` (one child shape per operator), `FindIdem`,
and `ChildrenCanon` (stored children are representatives).

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

An AC element carries a multiplicity annotation `Mult`: `exact m`, or a variable with bounds;
an element without an annotation is `exact 1`. Literals, sequence filters and predicates are
not patterns; `EMatch/Steps/` treats them as separate atoms.

A **binding** (`Binding`, `EMatch/Defs.lean:126`) is six partial maps: class variables, node
variables, multiplicity variables, and the three kinds of rest (multiset, sequence, set).
`Binding.Extends σ σ'` says each map of `σ` is contained in the corresponding map of `σ'`.

### 2.3 The matching specification

Every matching theorem is stated relative to the mutual inductive relations `MatchC` (a
pattern at a class) and `MatchN` (a pattern at a node), `EMatch/Defs.lean:213-255`. Two
constructors carry the content:

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
matches node-wise. Plain patterns match position by position, a commutative pair in either
order, a sequence as prefix, fixed middle and suffix.

AC matching is **maximum partition**: the pattern picks a list `taken` of distinct child
classes, one per element; element `i` matches class `taken[i]`, and its annotation is checked
against the full count of that class in the multiset. The rest is the multiset of untaken
classes with their full counts; without a rest, every class must be taken. ACI is the same
over a set, without counts. Three consequences carry through the guide:

- An element takes one child entry with its whole multiplicity, never part of an entry and
  never a sum of several children.
- An unannotated element accepts only an entry of count 1: `(f x y)` matches `f{a, b}` but
  not `f{a, a}`, and `(f x)` does not match `f{a, a}`.
- `MatchN` matches the syntax of the stored node up to rearrangement of its entries, not
  modulo the AC theory. Section 7 lifts it to the theory.

The specification never constrains node variables: `MatchC.app` does not mention `σ.node`.
Node variables appear only in the theorems' conclusions.

### 2.4 The congruence-closure vocabulary

The congruence-closure layer (`CC/Defs.lean`) has its own encoding, specialised to one
implicit AC operator `f`.

A **monomial** is a multiset of classes, `Monomial n = Multiset (Fin n)`. A node is a pair
`(M, c)`: the AC term `f(M)` stored in class `c`. There is no term language. Classes and
summands share the type `Fin n`, so one pool of `n` class ids serves as both.

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
term" as the assumption `FlatSound`.

A class with no node of the operator, a **leaf constant** such as `a` in `(+ a b)`, has no
monomial of its own in this encoding and occurs only as a summand. Section 5.9 reads such a
class `x` as the one-element monomial `{x}`, as the engine does, by adding implicit nodes
`({x}, x)` to the state.

## 3. Matching on one frozen graph

This layer proves that the engine's way of running one rule on one frozen index emits
exactly the matches of the specification. The resolver flattens a pattern into atoms, the
scheduler orders the atoms, and each atom is lowered to index steps. The theorems follow
that pipeline, one refinement per stage.

### 3.1 The pipeline

```
MatchC G P c σ                                    specification
  ⟺ atoms satisfied                              atoms_iff_match
  ⟺ Matches G atoms σ'                           (exact-domain form)
  ⟺ σ' ∈ run G plan ∅, any PlanOK plan           plan_matches
  ⟺ σ' ∈ runND ..., any choice function          runND_matches, runND_eq_plan
  ⟺ σ' ∈ runEngine ..., the engine's choice       runEngine_matches, chooseEngine_mem
runVariant k = runNaive ∩ {atom k new, atoms < k old}   variant_partition
```

The interpreter `run` (`EMatch/Ref.lean:280`) is a depth-first list monad over index steps:
`join` over a list of lookups, `extractChild`, `checkChildEq`, `checkEq`, `copyBinding`, and
the decompositions. A join is the intersection of its lookups' buckets; the galloping cursor
is verified separately in Verus (`containers-verus`).

### 3.2 Atoms

An **atom** (`RAtom`, `EMatch/Engine/Atoms.lean:41`, mirroring `RAtom` in
`egraph/src/resolve.rs:131`) is one node of a pattern with variables in every child
position: a node variable, an operator, and a shape. Its shallow pattern `a.shallow` is the
one-level pattern with those variables as arguments. `atoms P r` flattens `P` in post-order,
rooted at node variable `r`. A child application's class variable is its node variable, as
in the engine's single namespace. An atom holds when its node variable is bound to a stored
node with its operator, its class variable is that node's class, and the node matches the
shallow pattern:

```lean
def AtomSat (G : Graph) (σ : Binding) (a : RAtom) : Prop :=
  ∃ id n, σ.node a.node = some id ∧ (id, n) ∈ G.nodes ∧ σ.cls a.node = some (G.find id) ∧
    n.op = a.op ∧ MatchN G a.shallow n σ
```

`AtomSat` reuses `MatchN`, so atoms inherit maximum partition.

**`atoms_iff_match`** (`EMatch/Engine/AtomsMatch.lean:1133`):

```lean
theorem atoms_iff_match (G : Graph) (P : Pat) (r : Var) (c : C) (σ : Binding)
    (hP : P.head.isSome = true) (hr : r ∉ P.vars) :
    MatchC G P c σ ↔
      ∃ σ', AgreeOn P.vars σ σ' ∧ σ'.cls r = some c ∧ ∀ a ∈ atoms P r, AtomSat G σ' a
```

The root must be an application (`hP`) and the root variable fresh (`hr`); no graph
hypothesis is needed. The forward direction (`fwdOk`, `:1113`) walks the `MatchN` derivation
and binds each atom's node variable to the node that derivation used; the backward direction
(`backOk`, `:734`) rebuilds `MatchN` bottom-up through the shared variables, then transfers
the result to `σ` (`MatchC_agree`, `:153`).

### 3.3 Lowering one atom

`lower a B` (`EMatch/Engine/Lower.lean:75`) compiles atom `a` under the set `B` of class
variables already bound: one join, then either child reads (plain shapes) or one
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
The proof is shape by shape (`lower_sound`, `:806`; `lower_complete`, `:966`) from the
decomposition lemmas in `EMatch/Proofs/`, closed by `lowerSpec_unique` (`:1094`): two
`LowerSpec` bindings, one below the other, are equal, because `LowerSpec` fixes the domain.

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

`pick` is unrestricted, so any selectivity order is admitted; the grammar contains the
engine's "eager atoms first" rule. The target of every scheduler theorem is
`Matches G atoms σ'` (`EMatch/Engine/Plan.lean:21`): every atom holds, and the binding's
domain is exactly the atoms' variables, which turns "some extension of a match is emitted"
into an equality of binding sets.

**`plan_matches`** (`EMatch/Engine/Plan.lean:181`):

```lean
theorem plan_matches {G : Graph} {sig : Sym → Kind} {atoms : List QAtom} {plan : Plan}
    (hwf : AtomsWF G sig atoms) (h : PlanOK atoms plan) :
    ∀ σ', σ' ∈ run G plan Binding.empty ↔ Matches G atoms σ'
```

**Reading.** `hwf : AtomsWF`, where `AtomsWF` (`EMatch/Engine/SchedRun.lean:27`) bundles
the resolver's checks on the query (well-kinded atoms, distinct node variables, linear rest variables, every `Eq`
operand bound by some scanning atom, so no plan ends with an `Eq` unchecked) with two
invariants of the rebuilt index (distinct node ids, one child shape per operator); the
resolver and rebuild supply them, and `atoms_atomsWF` (`EMatch/Engine/AtomsWF.lean:417`)
discharges it for a single pattern. `h : PlanOK` says the plan is one the grammar admits;
`scheduleEngine_planOK` (`EMatch/Engine/Schedule.lean`, below) proves it of the plan
`schedule_with_stats` builds. The conclusion is an equality of binding sets,
for every order the grammar allows. Outside: how many times a binding is emitted, the Rust
join (an intersection of buckets in the model), and guards, literals and globals, which
`Sched` does not contain.

*Proof.* `schedA_run` (`SchedRun.lean:587`) is an induction on the grammar with a run
invariant `Inv` at each decision point. The `pick` case uses `lower_sound` and
`lower_complete`, the `eager` case `eager_sound` and `eager_complete`, the `done` case
`bindable` to show every `Eq` is used.

**`runND_matches`** (`EMatch/Engine/Runtime.lean:192`) covers the engine's adaptive
scheduler, which picks the next atom per branch from the current binding:

```lean
theorem runND_matches {G : Graph} {sig : Sym → Kind} {atoms : List QAtom}
    (choose : Binding → Finset Nat → Nat) (hwf : AtomsWF G sig atoms) :
    ∀ σ', σ' ∈ runND G atoms choose atoms.length ∅ ∅ Binding.empty ↔ Matches G atoms σ'
```

**Reading.** The same `hwf` as `plan_matches`, and no plan: the scheduler is the loop itself,
with an arbitrary choice function `choose` from the current binding and the unused atoms,
and branches may order the atoms differently. The conclusion is the same binding set, so
`runND_indep` and `runND_eq_plan` (`:204`, `:212`) follow: the result does not depend on the
heuristic and equals that of every `PlanOK` plan. The fuel `atoms.length` is exact: each
step uses one atom. The proof is an induction on fuel reusing the `pick` and `eager` steps
of `schedA_run`. Outside: the cost of the choice, and the engine's `choose_atom`, which
`runEngine_matches` instantiates.

**The engine's choice and the semi-naive settings.** `runNDA`
(`Runtime.lean`) is `runND` with each lowered block run under a per-atom index setting
(`IndexMode`), as the engine runs its variants through the same adaptive loop;
`runNDA_matches` gives `Matches ∧ ModeOk`, and `runNDA_eq_runA` equates it with every
`SchedA` plan under the same settings. `chooseEngine` (`EMatch/Engine/Choose.lean`)
transcribes `choose_atom` (`ematch.rs:1609-1659`) and `cursor_len` (`:1673-1705`): among the
unused scanning atoms, in index order, the one whose join opens the shortest bucket under
the bindings in hand, read in the store its setting selects, a later atom replacing the best
so far only when strictly cheaper. The join priced is the one `emit_atom` emits
(`engineJoinLookups`: `joinLookups`, plus the `byContains` lookups of a `:comm` atom that
`lower` omits); the bound set is `boundSet`, equal to the scheduler's by `boundSet_eq`.
`chooseEngine_mem` says it is a choice function `runND` accepts (the `min'` fallback never
fires, `chooseEngine_unusedScan`), and `runEngine_matches`, `runEngine_naive_matches`,
`runEngine_indep`, `runEngine_eq_plan` instantiate the `runND` theorems with it.

```lean
theorem runEngine_matches {G : Graph} {sig : Sym → Kind} {isNew : NodeId → Bool}
    {mode : Nat → IndexMode} {atoms : List QAtom} (hwf : AtomsWF G sig atoms) :
    ∀ σ', σ' ∈ runEngine G isNew mode atoms ↔ Matches G atoms σ' ∧ ModeOk isNew atoms mode σ'

theorem matcherOK_engine (atoms : List QAtom) : MatcherOK atoms (.engine atoms)
```

**Reading.** `runEngine` is `runNDA` with `chooseEngine`. Under `hwf` alone, the engine's
adaptive loop emits exactly the bindings that satisfy the atoms and respect the per-atom
index settings (`ModeOk`: an atom read in the delta binds a new node, an atom read in the
full index less the delta an old one). A `Rule` carries its matching procedure as a
`Matcher` (`EMatch/Engine/Matcher.lean`): `Matcher.static ap` is the static plan under
`runA`, `Matcher.engine atoms` the adaptive scheduler with `chooseEngine`,
`Matcher.runtime atoms choose` the same with any choice function. `MatcherOK atoms m` says
`m` emits exactly `Matches ∧ ModeOk` wherever the atoms are well formed; `matcherOK_static`
proves it from `SchedA`, `matcherOK_runtime` and `matcherOK_engine` prove it with no
hypothesis. `MatcherOK.naive_iff` and `MatcherOK.round_complete` are `mem_runNaive_iff` and
`semi_naive_round_complete` on a matcher, so the saturation theorems (Sections 6 and 7)
take `hmatch : MatchersOK rules`, a theorem for the adaptive scheduler, in place of a plan
hypothesis `hplan : PlansOK rules`. Assumed: the correspondence between `chooseEngine` and
`choose_atom`, which the unit test below checks on 4945 decisions, and between
`scheduleEngine` and `schedule_with_stats`, which the second test checks on 2679 plans.
Outside: the pricing of the join (`cursor_len`) and the estimate of the static scheduler
(`estimate_cost`), which the model takes as parameters, and the `Flatten` step, which the
adaptive scheduler never runs (Section 4).

The unit test `atom_choice_agrees_with_the_model_on_the_rounds_corpus` (`ematch.rs`)
compares, at every phase-B decision of the `conform-rounds` corpus run naive and
semi-naive under runtime scheduling, the atom `choose_atom` takes with the one a Rust
transliteration of `chooseEngine` takes from the same bindings and bucket lengths (the
decisions depend on the partial bindings, which the dumps do not carry, so Lean cannot
replay them). 200 files, 4945 decisions, 1591 with several candidates, all agree. Two
mutations of the transliteration are caught: pricing a `:comm` atom over `lower`'s lookups
(30 disagreements) and breaking ties toward the highest index (808).

**The static scheduler** (`EMatch/Engine/Schedule.lean`). `scheduleEngine` transcribes
`schedule_inner` (`schedule.rs:865-954`), the loop behind `schedule_with_stats`,
`schedule_with_stats_sampled` and `schedule_with_bound`: the eager pass `lower_eager`
(`:1102-1139`) to a fixpoint (`eagerAt`, `eagerSweep`, `eagerFix`: an `Eq` with a bound side
is checked or copied, a plain atom whose node is bound is re-joined in its class, which is
`lower a B` with `a.node ∈ B`), then the cheapest unused scanning atom in index order, a
later one replacing the best so far only when strictly cheaper (`pickStep`, `pickBest`),
lowered by `emit_atom` under the bound set in hand (`lower a B`), until no scanning atom is
left. The price is a parameter `cost : APlan → Finset Var → Nat → κ` over any strictly
ordered `κ` (the `f64` of `estimate_cost`), read from the plan emitted so far and the bound
set; the seed `pre` is the bound set `schedule_with_bound` starts from.

```lean
theorem scheduleEngine_schedA (cost : APlan → Finset Var → Nat → κ) (pre : Finset Var)
    (atoms : List QAtom) : SchedA atoms ∅ pre (scheduleEngine cost pre atoms)

theorem matcherOK_static_engine (cost : APlan → Finset Var → Nat → κ) (atoms : List QAtom) :
    MatcherOK atoms (.staticEngine cost atoms)

theorem matchersOK_compiled ... (h : ∀ rule ∈ rules, rule.matcher = .engine rule.atoms ∨
      ∃ cost : APlan → Finset Var → Nat → κ, rule.matcher = .staticEngine cost rule.atoms) :
    MatchersOK rules
```

**Reading.** No hypothesis: whatever the prices, the seed and the atoms, the plan the static
scheduler emits is in the grammar, so `MatchersOK` is a theorem for the shipped default as it
is for the adaptive scheduler (`Matcher.staticEngine cost atoms` is `Matcher.static` of the
plan; `matchersOK_compiled` in `Saturate/Invariant.lean` covers a rule set matched by either).
`scheduleEngine_planOK`, `scheduleEngine_naive_matches` and `scheduleEngine_eq_runEngine`
restate `plan_matches` and `runEngine_eq_plan` on the plan. The `done` case needs the eager
fixpoint: `eagerFix_fixed` says that after the pass no unused atom is free, which is what
`SchedA.done` asks, and `schedA_matches` then uses `bindable` to see every `Eq` used; the
`pick` and `eager` cases are the constructors of `SchedA` on the state the loop carries
(`Prefix`). The fuels are exact: each productive sweep and each iteration use an atom
(`unusedCount`). Outside: the atoms the model does not have (literals, guards,
disequalities, global equalities, `Collect`), `:flatten` queries, and the price itself.

The unit test `static_plan_agrees_with_the_model_on_the_rounds_corpus` (`schedule.rs`)
compares, for every plan `schedule_inner` builds while the `conform-rounds` corpus runs
naive and semi-naive, the engine's steps with those a Rust transliteration of
`scheduleEngine` (`model::schedule`) emits from the engine's prices: the same atom order, the
same binding kind for every variable, the same join lookups (`engineJoinLookups`, as the
choice test). 200 files, 2999 plans; 2679 compared (1185 with several atoms, 4071 picks),
all agree; 320 are outside the model, each for a rule with a `(= x g)` atom. Three mutations
of the transliteration are caught: breaking ties toward the highest index (608
disagreements), lowering a plain atom whose node is bound as a pick instead of in the eager
pass (17), and running the eager pass before the first pick only (458). A fourth, one sweep
in place of the fixpoint, no corpus rule detects; `eager_chain_agrees_with_the_model`
does, on `(g c)`, `(= a b)`, `(= b c)`.

**Pseudo-code: the adaptive scheduler and the static scheduler.**

```
chooseEngine(G, isNew, mode, atoms, σ, S):            -- chooseEngine; ematch.rs choose_atom
  best := none
  for i in 0 .. |atoms|, i ∈ S:                       -- chooseStep, index order
    cost := length of the shortest bucket of the join emit_atom would emit for atom i,
            under σ's bindings, in the index setting of atom i   -- atomCost, engineJoinLookups; cursor_len, bucket_in
    if best = none or cost < best.cost: best := (cost, i)         -- strictly cheaper replaces
  return best.i                                       -- chooseEngine_mem: a member of S

runND(G, atoms, choose, fuel, used, B, σ):            -- runND; ematch.rs adaptive loop
  if fuel = 0: emit σ
  if some unused Eq atom has a bound side:            -- eagerCandidate, Sched.eager
    run its eager lowering under B, then recurse on each result   -- q.eagerLower B
  else if some scanning atom is unused:               -- Sched.pick
    i := choose(σ, unused scanning atoms)             -- any choice function; chooseEngine
    run (lower atoms[i] B) on σ, recurse on each result with i used and B ∪ binds   -- lower
  else emit σ                                         -- Sched.done
```

`runNDA` is the same loop with each lowered block run under the per-atom index setting; the
engine also prices a `:comm` atom over the `byContains` lookups `emit_atom` adds, which
`engineJoinLookups` copies.

The static scheduler is the same two phases run once, at plan time, on the bound set alone:

```
scheduleEngine(cost, pre, atoms):                     -- scheduleEngine; schedule.rs schedule_inner
  used := ∅, B := pre, steps := []
  repeat at most |atoms| times:                       -- schedLoop
    repeat:                                           -- eagerFix; lower_eager
      for i in 0 .. |atoms|, i ∉ used:                -- eagerSweep, eagerAt; try_eager_lower
        if atoms[i] = (= x y) and (x ∈ B or y ∈ B):   -- SchedA.eager
          steps ++= eagerLower atoms[i] B; used += i; B ∪= {x, y}
        if atoms[i] plain with its node in B:         -- SchedA.pick, the re-join in its class
          steps ++= lower atoms[i] B; used += i; B ∪= binds atoms[i]
    until a sweep lowered nothing                     -- eagerFix_fixed: no unused atom is free
    best := none
    for i in 0 .. |atoms|, i ∉ used, atoms[i] scanning:          -- pickStep, index order
      if best = none or cost(steps, B, i) < best.cost: best := (i, cost)   -- strictly cheaper replaces
    if best = none: return steps                      -- SchedA.done
    steps ++= lower atoms[best.i] B; used += best.i; B ∪= binds atoms[best.i]   -- SchedA.pick; emit_atom
```

**Hypotheses of the matching theorems, classified.** The theorems of this section share one
hypothesis on the query and take the rest as parameters.

| Hypothesis | Theorem | Class | Source |
|---|---|---|---|
| `hwf : AtomsWF G sig atoms` (well-kinded atoms, distinct node variables, linear rests, every `Eq` operand bound by a scanning atom) | `plan_matches`, `runND_matches`, `runEngine_matches` | assumed, derived for one pattern | the resolver's checks (`resolve.rs`); `atoms_atomsWF` derives it for the atoms of a single pattern |
| `KeysNodup`, `Conforms sig` (inside `AtomsWF`) | the same | assumed | rebuild and the operator declarations; no theorem reads them off `index.rs` |
| `h : PlanOK atoms plan`, `SchedA` | `plan_matches`, `variant_partition` | derived | `scheduleEngine_schedA`: the plan `schedule_inner` builds is in the grammar for every price; the correspondence of `scheduleEngine` with `schedule_inner` is checked by the static-plan mirror (Section 8) |
| `choose` | `runND_matches` | derived | any choice function; `chooseEngine_mem` discharges it for the transcription of `choose_atom`, whose correspondence the atom-choice mirror checks (Section 8) |
| `cost`, `cursor_len` | `scheduleEngine_schedA`, `runEngine_matches` | parameter | the price is a parameter of the model; no theorem is about its value |
| `ChildrenCanon`, `FindIdem` | `exec_matches`, `env_refine` | assumed | two invariants rebuild establishes; stated by `Round.WF` (Section 6.1) |
| `EnvAtomsWF atoms` (the resolver's variable discipline) | `planOK_envWF`, `exec_matches` | assumed | `resolve.rs`; no theorem derives it (Section 9) |
| multiplicity of emitted bindings | all | limit | the theorems are about sets; `comm_pair_duplicate`, `comm_bound_first_counts` show the counts differ |

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
variables; equality on them follows by applying soundness to `σ'`, which matches at the same
node and so binds every variable the pattern forces. The same remark applies to
`ExtendsBelow` in `ematch_complete`. All results in this layer are about sets of bindings:
the engine may emit a binding more than once, with counts that differ from the model's
(`comm_pair_duplicate`, `comm_bound_first_counts`, `EMatch/Env/Main.lean:58`, `:68`).

### 3.5 Semi-naive variants

A semi-naive round runs variant `k` of a rule for each scanning atom `k`: only new nodes for
atom `k`, only old nodes for atoms of smaller index, every node for atoms of larger index
(`variantMode`, `EMatch/Engine/SemiNaive.lean:19`), by stable atom index as in
`VariantIndex::mode` (`egraph/src/index.rs:955-963`).

**`variant_partition`** (`EMatch/Engine/SemiNaive.lean:30`):

```lean
theorem variant_partition ... (hwf : AtomsWF G sig atoms) (h : SchedA atoms ∅ ∅ ap)
    (hk : atoms[k]? = some (.scan ak)) :
    ∀ σ', σ' ∈ runVariant G isNew k ap ↔
      σ' ∈ runNaive G ap ∧ (∃ id, σ'.node ak.node = some id ∧ isNew id = true) ∧
        ∀ (j : Nat) (a : RAtom), j < k → atoms[j]? = some (.scan a) →
          ∃ id, σ'.node a.node = some id ∧ isNew id = false
```

**Reading.** `isNew` is any predicate on node ids; the theorem is about one snapshot. Under
`hwf` and a static plan `SchedA`, variant `k` emits exactly the naive matches whose atom-`k`
node is new and whose smaller-index nodes are old. `variants_disjoint` (`:65`) follows: two
variants never emit the same binding. `variants_cover_new` (`:88`) follows by taking the
least new atom index: the union of the variants is exactly the naive matches with at least
one new scanning node. These are what semi-naive matching needs within a round: no match
twice, no match with a new node lost. What "new" means across a round is Section 6.2.

### 3.6 The reference compiler

`ematch_sound` and `ematch_complete` (`EMatch/Main.lean:143`, `:156`) relate the
specification to a second, simpler compiler (`compile`, `EMatch/Ref.lean:453`), which lowers
a pattern left to right without scheduling. This chain meets the engine chain only at
`MatchN`. Its decomposition lemmas (`decompose_ac_sound'`, `expand_a_complete'` and the
others in `EMatch/Proofs/`) are what the engine chain reuses; the theorems themselves are
not consumed downstream.

### 3.7 The mutable executor

`EMatch/Env/` models the engine's `Match` environment, which writes bindings in place and
undoes them on backtrack (`egraph/src/ematch.rs:171`), one cell per variable: a node id for
a node variable, a class for a class variable. `abs G κ e` (`EMatch/Env/Model.lean`) reads
every cell as a class through `find`, and the cells of node kind (`κ v = true`) also as node
ids. `env_restore` and `env_refine` (`EMatch/Env/Main.lean`) state that the executor returns
the environment it receives, and that the bindings it emits are, as a set, the bindings
`run` emits:

```lean
theorem env_refine (G : Graph) (hG : G.ChildrenCanon) (hidem : G.FindIdem)
    {κ : Var → Bool} {B : List Var} {plan : Plan} (hwf : WF κ B plan) (e : Env)
    (he : EnvOk e B) (hκ : KindOk κ e) (σ : Binding) :
    σ ∈ (exec G (joinKinds κ plan) plan e).1 ↔ σ ∈ run G plan (abs G κ e)
```

The binding kinds are per step. `κ` is the kind of each variable at the
entry of the plan; a join makes its target a node variable, whatever its kind at entry (unbound,
or a class variable bound by `ExtractChild`, a decomposition or an earlier atom, which the
join refines to a node of its class); `joinKinds κ plan` is the kind at the end of the plan,
with which the emitted environments are read. A lookup or a check reads a cell through
`canon` whatever its kind, so `Env.WF` puts no kind condition on join keys, check operands or
decomposition elements and requires only that a step reading a node through `nodeOf` reads
a node variable. `KindOk κ e` says every node variable is bound in `e`, so an element a
decomposition binds is a class variable. The write-once conditions are unchanged:
`ExtractChild`, `CopyBinding` and the rest pushes write unbound variables only, `ExpandA`'s
two rests are distinct, and no annotation is `exact 0`.

```lean
theorem planOK_envWF {atoms : List QAtom} {plan : Plan} (hA : EnvAtomsWF atoms)
    (h : PlanOK atoms plan) : WF (fun _ => false) [] plan

theorem exec_matches {G : Graph} {sig : Sym → Kind} {atoms : List QAtom} {plan : Plan}
    (hG : G.ChildrenCanon) (hidem : G.FindIdem) (hwf : AtomsWF G sig atoms)
    (hA : EnvAtomsWF atoms) (h : PlanOK atoms plan) (σ : Binding) :
    σ ∈ (exec G (planKinds plan) plan Env.empty).1 ↔ Matches G atoms σ
```

**Reading.** `planOK_envWF` (`EMatch/Env/Plans.lean`) says every plan the grammar admits is
well formed for the mutable executor from `Match::new` (all kinds `false`), under the
resolver's variable discipline `EnvAtomsWF`: a class variable is no multiplicity or rest
variable, a multiplicity variable is no rest variable, rest variables are linear across
atoms, an atom's prefix and suffix rests are distinct, and no AC annotation is `exact 0`.
The resolver supplies `EnvAtomsWF`; no theorem derives it from `resolve.rs`. `exec_matches`
composes it with `env_refine_empty` and `plan_matches`: the executor emits exactly the
matches, as a set, on a snapshot with canonical children and idempotent `find` (two
invariants rebuild guarantees). `nested_plans_wf` and `nested_exec_matches` work the
pattern `(f (g x) y)` both ways round: with the parent first, `join 2 [byOp f]`,
`extractChild 2 0 3`, `extractChild 2 1 1`, `join 3 [byRepr 3, byOp g]`,
`extractChild 3 0 0`, where `3` is bound as a class and refined by the re-join, which reads
its own target; with the nested atom first, `join 3 [byOp g]`, `extractChild 3 0 0`,
`join 2 [byOp f, byChildPos 0 3]`, `checkChildEq 2 0 3`, `extractChild 2 1 1`, where `3` is
bound as a node and read as a class (`nestedPlanParent_eq`, `nestedPlanChild_eq`, by
`decide`). Outside: the adaptive scheduler (`exec` runs static plans only), the steps of
Section 3.8, and the multiplicity of emitted bindings.

**Adequacy.** The engine's join saves and restores a bound target
(`ematch.rs:3012-3023`, "`target` may already be bound"), as `exec` does, and its lookups
canonicalize the key cell (`bucket_in`). Nothing downstream uses `Env/`: the saturation
theorems read the emitted bindings through `run` (`runNaive`), which `exec_matches` shows
the executor agrees with.

### 3.8 Guards, literals and sequence collection

`EMatch/Steps/` adds `Neq`, global, literal, predicate and `Collect` atoms. `step_sound` and
`step_complete` (`EMatch/Steps/Main.lean:43`, `:55`) prove each lowering step sound and
complete against the atom's meaning. `collect_sound` and `collect_complete`
(`EMatch/Steps/Collect.lean:453`, `:462`) relate the sequence assembler to a declarative
relation, assuming a node yields at most `MAX_MATCHES` (2^20) raw matches.

**Adequacy.** These are per-step results. `Sched` contains only scanning and `Eq` atoms, so
no theorem covers a whole query that mixes guards or literals with scanning atoms. The
declarative relation for `Collect` reuses most of the assembler's own functions
(`choicesAt`, `admit`, `matchedA`), so `collect_sound` and `collect_complete` are close to
restating the code.

### 3.9 The cursor matcher

`run_query_iter` (`egraph/src/ematch.rs`) drives `MatchIterator`, a stack-based matcher that
yields one match at a time: `next_match` enters the plan's steps in order, a step that binds
several ways pushes a frame, and `backtrack` advances the top frame or drops it. No production
path reaches it; `run_query` is what the engine runs. `EMatch/Engine/Cursor.lean` models its
AC and ACI decomposition frames (`FrameKind::ACDecompose`, `FrameKind::ACIDecompose`) as a
state machine over a generic entry store, with the search `ac_find_first` as `findStep` and
`findLoop`, the advance `ac_advance` as `postYield` and `advance`, the yields as `drive`, and
the store operations `ac_scan` and `ac_undo` as `acAccept`, `acApply` and `acUndo`
(`aciAccept`, `aciApply`, `aciUndo` for the set twin).

**Theorem A, termination** (`findLoop_terminates`, `advance_terminates`):

```lean
theorem findLoop_terminates (from_ : Nat) (s : State α) (h : IdxInv ops s) :
    ∀ k, ops.fuel ≤ ops.pos s + k → ∃ r, ops.findLoop true from_ k s = some r

theorem advance_terminates (s : State α) (h : IdxInv ops s) : ∃ r, ops.advance s = some r
```

The measure `pos` reads the entry indices `ri_at` as one number in base `len + 1`, most
significant first, and adds the position `ei`; `findStep_pos_lt` says every move of the fixed
search increases it, a forward move by taking an entry at or past the start, a backward move
by advancing the previous element's index and zeroing the later ones, and `pos_lt_fuel`
bounds it. The search before commit `4e267030` is `findStep false`: `preFix_cycles` exhibits
two states of three elements over two entries that it maps to each other, and
`preFix_diverges` says `findLoop false` returns for no fuel from either; `preFix_fixed_ends`
says the fixed search ends on the same state.

**Theorem B, the yields** (`drive_eq_enum`, `acFrame_eq_decomposeAC`, `aciFrame_eq_decomposeACI`):

```lean
theorem drive_eq_enum (hl : ops.Laws good) (h₀ : good 0 a₀) (hn : 0 < ops.n) (k : Nat) :
    ops.drive k (ops.init a₀) = (ops.enum 0 a₀).take k

theorem acFrame_eq_decomposeAC (elems : List (Var × Mult)) (rest : Option Var)
    (res₀ : List (C × Nat)) (σ₀ : Binding) (hnd : (res₀.map Prod.fst).Nodup)
    (hpos : ∀ p ∈ elems, MultPos p.2) (hμ : ∀ k ∈ multVars elems, σ₀.mult k = none)
    (hne : elems ≠ []) :
    (∀ k, (drive k (init (acInit elems res₀ σ₀))).filterMap (acLeaf rest) =
        ((enum 0 (acInit elems res₀ σ₀)).take k).filterMap (acLeaf rest)) ∧
    ∀ k, (enum 0 (acInit elems res₀ σ₀)).length ≤ k →
      (drive k (init (acInit elems res₀ σ₀))).filterMap (acLeaf rest) = decomposeAC elems rest res₀ σ₀

theorem decomposeAC_nodup (es : List (Var × Mult)) (rest : Option Var) :
    ∀ res σ, (res.map Prod.fst).Nodup → (decomposeAC es rest res σ).Nodup
```

**Reading.** `enum e a` is the recursive enumeration of the complete assignments of elements
`e..n-1` from store `a` in entry order, the executor's search; `drive k s` is what the frame
yields from `s` with fuel for `k` yields, the first search then one advance per yield.
`drive_eq_enum` says the frame yields the enumeration element by element, for every store
whose `undo` reverses `apply` on reachable stores (`Laws`). The proof keeps `remaining a₀ s`,
what the frame has left to yield: the completions from the position, then for each element
below it the completions from the entry after the one it holds; every move preserves it
(`findStep_cont_remaining`), a failed search leaves nothing, and at a complete assignment it
is the store followed by what `postYield` leaves. `acFrame_eq_decomposeAC` instantiates it
for the AC store and connects `enum` to the executor's `decomposeAC`
(`enum_eq_decomposeAC`): the frame's yields after the leaf (the rest pushed, or the exact
check) are the executor's list, element for element, so the same set with the same order.
`decomposeAC_nodup` says that list has no duplicates when the entries' classes are distinct,
as a node's `(class, count)` entries are after rebuild. The hypotheses are the executor's:
distinct entry classes, no annotation that accepts count 0 (`EnvAtomsWF`), and the elements'
multiplicity variables unbound at entry. The ACI twin (`aciFrame_eq_decomposeACI`,
`decomposeACI_nodup`) has distinct set children as its hypothesis.

**Adequacy.** The frame stack above the decompositions (`next_match`, `backtrack` over the
plan, the join and sliding-window frames) is not modelled: the equality of
`run_query_iter`'s match multiset with `run_query`'s for a whole plan is checked, not proved,
by `cursor_agrees_with_the_recursive_executor_on_the_rounds_corpus` (Section 8), and the
transliteration of the frame is checked against the engine's cursor on random residuals by
`cursor_frames_agree_with_the_lean_model_on_random_residuals`. The model transcribes the
engine after the fixes those two checks and the model found: `ac_advance` completed the
later elements greedily and undid the moved element twice (an assignment with a bound later
element was missed, and an index past the residual read); a single-shot sequence step left
its children bound when the join below moved on; an AC node was read through
`mset_children`, which panics on a commutative pair; and a bound element took any entry of
its class, so a commutative pair with equal children gave an assignment twice where
`decompose_ac_elem` gives it once. The cursor reads the full index only, so under semi-naive
it finds the naive match set; the corpus comparison runs naive.

## 4. Flattened matching

### 4.1 Problem

A rule tagged `:flatten` matches an n-ary pattern against the flattened term. A child class
`X` that holds an `f`-member `m` may be replaced in place by `m`'s children, recursively: the
node `Plus{Y, Z}` with `Z ∋ Plus{Y, d}` has the flattened reading `{Y, Y, d}`. Maximum
partition sees only the stored children.

An **opening tree** (`OT`, `EMatch/Flatten/Views.lean:96-111`) records, for each child
position, whether the child is kept whole or opened through one of its `f`-members; a class
already on the current path may not be opened again, and multiplicities multiply down the
tree. The tree's fringe is a **raw view**: a list of (class, count) pairs. A kept child of an
opened member is part of that member's **leaf group**. The **canonical view** is the raw
view normalized for the operator's kind and laws (`normalize`, `Views.lean:226`): coalesce
and sort for AC, deduplicate for ACI, then drop the unit, clamp nilpotent counts, and cancel
inverse pairs in one left-to-right pass. A raw view whose normal form is empty, the unit, or
a single class of count 1 is dropped. `Views ctx laws n` is the set of canonical views of
node `n`.

Opening produces redundant matches: if no item pattern takes anything from an opened member,
the same match, with a refolded rest, already exists on a less-opened view. The **demand
rule** filters these: a match on view `w` that takes the classes `taken` is kept when some
tree giving `w` opens nothing, or when every leaf of some tree giving `w` is satisfied.
Demand only removes matches of the shallow pattern on genuine views, so it bears on
completeness and redundancy, never on soundness.

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

**Reading.** No hypothesis on the graph: the enumerator is total. `views_sound` says every
emitted view is a canonical view of some opening tree of the node, with its demand as the
specification says: unconditional when some tree giving the view opens nothing, otherwise
the trees' leaf groups. `views_complete` says every opening tree's view is emitted, with a
demand that accepts that tree's leaves. Together they identify the executable enumerator
with the declarative `Views` and `Alts`. Completeness needs no bound: each opening adds a
class of the graph to the path, so the number of classes is enough fuel (`rawNode_complete`,
`:150`). Outside: the engine's bounds on the walk (`MAX_VIEWS`, `MAX_WORK`, `MAX_ELEMS`),
which skip a node and count it in `flatten_skipped`; the model enumerates without bound.

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
normal form and lose the match: for AC, when the opened class is the unit, when its refolded
count clamps to zero, or when an inverse pair touches it or a leaf class; for ACI, when the
class is the unit; for `:assoc`, when the class is the unit or the whole block is units.

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

**Reading.** The operator is a multiset (`hκ`), under any laws. The input is a match of the
shallow pattern on the view of some opening tree (`hv`, `hn`, `hm`), with variable items
(`helems`, guaranteed by atom flattening), at least one item and a rest variable. The
conclusion: the enumerator emits some view whose demand accepts the match's item classes
and that carries a match with the same item bindings; only the rest differs, by refolding
opened members into their classes. So the rule loses no match up to refolding of the rest.
Outside: a match with no rest variable or no item, and the claim that accepted matches are
irredundant (`proofs/repro/aci-overaccept.egg` shows one that is not).

*Proof.* Strong induction on the number of openings (`laws_ac_aux`, `LawsMain.lean:52`). If
the rule accepts the tree, it is the witness. Otherwise some leaf is unsatisfied, hence inert;
closing it removes one opening. The match carries over to the closed tree with its rest
updated (`refold_ac_inert`, `Laws.lean:1381`), because the taken classes keep their
normalized counts. The closed view is still a node, because it holds a taken class and the
opened class.

The ACI version (`demand_engine_complete_aci`, `EngineComplete.lean`) needs `TwoClassesL`: no
raw view of the node collapses to a single class after unit drop. The `:assoc` versions need
no extra hypothesis under laws; the laws-free one needs `NoNullary` (no member with zero
children).

```lean
theorem twoClassesL_of_members {laws : Laws} {ctx : Ctx} {n : Node}
    (hm : MembersTwoClassesL laws ctx) (hn : NodeTwoClassesL laws ctx n) :
    TwoClassesL laws ctx n
```

**Reading.** `TwoClassesL` is derived from two facts about the stored graph: every filed
`f`-member holds two classes less the unit (`MembersTwoClassesL`), and so does the node
(`NodeTwoClassesL`), because an opening tree either keeps the classes of its positions or
holds the classes of an opened member's view (`OTL.twoClasses`). Both facts are the
collapse invariant the engine's `add` and rebuild establish: a set node whose normal form is
one class is not stored and its class is returned (`egraph.rs`,
`Normal::Single(g) => find(g)`), and rebuild re-normalizes a stored node whose children
merged and merges it into that class. The fixture `egraph/tests/egg/aci1.egg` records it:
`z = And{x, s}`, `n = And{x, z}`, and `s ∪ Tru` merges `z`, then `n`, with `x`, so that
`(And v ..r)` matches only `And{a, b}`. `demand_engine_complete_aci` takes the invariant as a
hypothesis on the context, as `NoNullary` for sequences.

**Adequacy.** The theorems named `demand_*_no_redundancy_*` show that every rejection is
covered by an accepted, strictly less-opened refolding. They do not show that accepted
matches are irredundant; `proofs/repro/aci-overaccept.egg` records a redundant set match the
rule admits. No theorem states that a refolded rest denotes the same value as the original,
although the argument of `otl_den_ac` gives it.

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

**Reading.** The theorems are parametric in the enumerator `E`, which must meet
`Enumerator.Spec` (`Plan.lean:150`): every view is a normalization result, and pruning under
a binding keeps exactly the accepted matches. `QueryFWF` (`hw`) is the well-formedness of
the flattened query, supplied by the resolver and the index. The conclusion is set equality
between the plan's emitted bindings and the bindings satisfying every n-ary atom under
`AtomSatG E`, for any atom order.

**Adequacy.** `Enumerator.Spec` does not require a view to be a view of the node. The
declarative reading needs three theorems composed by the reader: `views_soundL` for the walk
and `regroup_views_sound_*` for regrouping (the views are views of the node),
`demand_engine_complete_*` (demand loses only redundant matches), and
`flatten_plan_complete`. No single theorem states the composition.

### 4.5 Folds

`:assoc-left` and `:assoc-right` are fold notations over an operator that is not associative.
Only the spine (the first child for a left fold, the last for a right fold) may be opened or
regrouped. A fold reads in any magma: `lfold` and `rfold` (`EMatch/Flatten/Fold.lean`) are
over a type `M` with a binary operation (`[Mul M]`, no law), and `ConsistentL ctx den`,
`ConsistentR ctx den` take a denotation `den : C → M` into any such type. The free terms
`BTm` are one instance, used by the counter-models, where two groupings of the same leaves
denote different terms. `fold_open_off_spine_unsound` (`:219`) is a formal counterexample to
opening off the spine. `otLeft_sound` and `otRight_sound` (`:245`, `:258`) prove that
spine-only opening trees preserve the fold's value in every magma. Regrouping a fold
replaces a prefix (left fold) or a suffix (right fold); Section 4.6 covers it.

```lean
theorem consistentL_cyclic_satisfiable :
    ∃ (ctx : Ctx) (X c : C) (den : C → ℕ), ctx.κ = .assoc ∧
      (∃ id m, ctx.IsMember id m X ∧ m.children = .seq [X, c]) ∧
      (∃ a b id₁ m₁ id₂ m₂, ctx.IsMember id₁ m₁ X ∧ m₁.children = .seq [a, b] ∧
        ctx.IsMember id₂ m₂ X ∧ m₂.children = .seq [a, b, c]) ∧
      ConsistentL ctx den
```

**Reading.** A class can hold a fold over itself: `x - 0 = x` puts `Sub[X, c]` into `X`,
and a class can hold two spellings `Sub[a, b]` and `Sub[a, b, c]`. No denotation into the
free terms is consistent with such a class (`consistentL_cyclic_free_unsat`: `den X` would be
a proper subterm of itself), but one into `ℕ` with multiplication is (`c ↦ 1`, `a ↦ 2`,
`b ↦ 3`, `X ↦ 6`). Since every fold soundness theorem takes the magma as a parameter, its
consistency hypothesis is satisfiable on graphs with such classes, and the theorems are not
vacuous there.

**The executable enumerator is the spine trees** (`EMatch/Flatten/FoldEnum.lean`). `rawOptD ctx dir` with `Dir.left` or `Dir.right` is the walk of
`flatten::enumerate` with `spine(dir, i, len)`. `rawNodeD_left_iff` and `rawNodeD_right_iff`
prove that its raw views of a fold node are exactly the views of `OTLeft`, resp. `OTRight`:

```lean
theorem rawNodeD_left_iff {ctx : Ctx} (hκ : ctx.κ = .assoc) (hs : SeqShaped ctx) {n : Node}
    {cs : List C} (hn : n.children = .seq cs) {w : List (C × Nat)} :
    (∃ ls, (w, ls) ∈ rawNodeD ctx .left (fuelOf ctx.G) n 1 ∅) ↔
      ∃ v, w = withK 1 v ∧ OTLeft ctx ∅ cs v
```

**Reading.** For a sequence operator whose every `f`-member is a sequence node (`SeqShaped ctx`,
determined by the operator declaration), the executable fold enumerator run leftwards produces a
raw view of a fold node exactly when the view is a spine-only opening tree's view (`OTLeft`);
`withK 1 v` is the class list `v` with count one, and `rawNodeD_right_iff` is the mirror with
`OTRight`. The soundness direction (`rawNodeD_left_sound`) is by induction on the fuel, the
completeness direction (`rawNodeD_left_complete`) by induction on the tree, with the fuel of
the graph as in `rawOptL_complete`. Outside: laws (a fold declares none) and regrouping,
which `regroup_views_sound_left` covers below.

```lean
theorem regroup_views_sound_left {ctx : Ctx} (hκ : ctx.κ = .assoc) (hs : SeqShaped ctx)
    {M : Type*} [Mul M] {den : C → M} (hc : ConsistentL ctx den) {limit : Nat} {n : Node}
    {cs : List C} (hn : n.children = .seq cs) {w : List (C × Nat)} {d : DemandL}
    (h : (w, d) ∈ enumerateR ctx .left Laws.free limit n) :
    lfold ((w.map Prod.fst).map den) = lfold (cs.map den)
```

**Reading.** In every interpretation of the operator as a binary operation on a type `M`,
with a denotation of the classes under which every `f`-member denotes its class as a left fold
(`ConsistentL`, the reading of the store), every view the regrouping enumerator produces for
a left fold, opened or regrouped, denotes the same element as the node's own children. The
free terms `BTm` are one of these interpretations, so on a graph that has a consistent
denotation into them the view and the node are the same term; a graph with a cyclic class has
none, and there the theorem applies through any interpretation in which the class's equations
hold (`consistentL_cyclic_satisfiable`). The right version is `regroup_views_sound_right`;
`regroupSkip_views_sound_left` and `regroupSkip_views_sound_right` say the same of the
engine's loop with its skips. The proofs use only `lfold_splice` and `rfold_splice`, never
the freeness of the terms. Outside: laws, and a fold combined with any law, which the sort
checker rejects.

At the level of distinct views, `enumerateLD_left_iff` and `enumerateLD_right_iff` read the
fold enumerator's views as the normal forms of the spine views, and `enumerateLD_left_sound`,
`enumerateLD_right_sound` carry `otLeft_sound` and `otRight_sound` to the executable mirror.
`rawNodeD_sub_both` places the views of any direction among the views of `.both`, so every
monoid-level theorem over `.both` applies to a fold.

**The fold mirror against the engine.** The conformance oracle runs `runER` with the fold
directions of the case (`Conform/Flatten/Oracle.lean`, `FCase.dirOf`), so every
`conform-flatten` sample with a fold compares this enumerator, regrouped, with the engine's.
The comparison covers 800 samples (the 400 committed `conform` and
`conform-flatten` samples, and 400 more of seed 3 of the `:flatten` generator, not
committed), 230 with a fold in the pattern: every `check-eq` and `check-neq` holds in the
engine, and the number of distinct `Tag` nodes the engine builds, one per binding, equals
the number of distinct `Tag` terms the model checks, so the binding sets agree. On 15
samples without a fold the node count is not comparable (several roots share a `Tag` term,
so the roots merge and the engine omits the congruent duplicates); their checks hold.

**Adequacy.** Demand completeness for folds is argued in a docstring (`Fold.lean:33-36`). The
fold theorems are laws-free: the engine declares no law on a fold (laws need `:comm`,
`sortcheck.rs`), and the model's only `:assoc` law, an identity, has no reading in an
arbitrary magma; under an identity the monoid theorems for any direction
(`regroup_views_sound_assoc_laws_dir`) apply, in which a fold reads as an associative
product.

### 4.6 Regrouped views

**Problem.** The engine (`FlattenScratch::regroup`, `egraph/src/flatten.rs`) also matches
regrouped views (Section 4.1). A regrouped view may be regrouped again, so a variable may
bind a class `G2 ∋ f{G1, c}` with `G1 ∋ f{a, b}` (nested groups), several groups may together
cover the whole view, and for a left fold `(a - b) - c` is a group of `[a, b, c, d]` only after
the prefix `[a, b]` is.

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
  (`regroupFuel`), which suffices because each regrouping lowers the total count. No bound
  applies to the needed classes along the way.
- `withinLimit limit` (`:201`) keeps the records needing at most `limit` classes, one per
  item of the atom. The engine applies the same filter to the final records only
  (`Demand::needs`).
- A needed class `g` becomes the leaf `needLeaf g` (`:65`), satisfied exactly when `g` is
  taken (`needLeaf_okE`), so every demand rule of Section 4.3 reads a regrouped record
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

**Reading.** The operator is a laws-free multiset, and `den` is any valuation of classes into
a commutative monoid under which each filed `f`-member denotes its class (`ConsistentAC`, the
reading of a congruence-closed store). Every view the regrouping enumerator produces, after
any number of regroupings and for any item limit, denotes the node's value, so a rewrite
matched on a regrouped view merges only theory-equal terms. `regroup_views_sound_aci` and
`regroup_views_sound_assoc` (`:365`, `:443`) are the versions for a join semilattice and a
monoid; the laws versions (`regroup_views_sound_ac_laws`, adequacy below) add a model of the
laws. Outside: regrouping off a fold's spine, which `regroup_off_spine_unsound` (`:527`)
refutes.

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

**Reading.** The only hypotheses are that the atom is n-ary (`hκ`) and its operator has no
laws (`hlaws`); the graph, kind and fold direction are arbitrary. The left side is the
engine's semantics of one flattened atom with regrouping; the right side is declarative: some
stored node of the atom's operator, some walk record of it, some finite chain of regroupings
to a record whose view the shallow pattern matches, whose needed classes number at most the
atom's items, and whose leaves and needed classes the item classes satisfy. As an
equivalence it bounds the engine's matches from above and from below. `regroup_views_iff`
(`:679`) is the same statement at the level of views, for any `limit`. Outside: laws
(`regroup_match_iff_laws`), the engine's loop order and skips (`regroupSkip_match_iff`), and
the engine's bounds (`regroupBounded_query_exact`). Two properties of the statement carry
engine behaviour:

- **The item limit bounds the final record only.** `RegroupChain` puts no bound on the
  records in between, because a later regrouping may absorb a needed class.
  `regroup_nested_matches` (`EMatch/Flatten/RegroupNested.lean:81`) is a chain from
  `{a, b, c, d, h, k}` through `{h, k, G1, G2}`, which needs two classes, to `{h, k, G3}` with
  `G3 ∋ F{G1, G2}`, which needs `G3` alone; with a limit of one the view `{h, k, G3}` is
  enumerated and accepts `x = G3`. The fixture `flatten_regroup_nested_needs.egg` records the
  same match in the engine.
- **Nested and covering groups are chains.** `G2 ∋ f{G1, c}` is reached by regrouping `G1`
  first. Groups that together cover the view are successive steps, none of which is the whole
  view. `regroup_fold_nested` (`RegroupNested.lean:133`) reaches `(a - b) - c` in the left fold
  `((a - b) - c) - d` through `[a, b, c, d] → [G1, c, d] → [G2, d]`, one needed class at each
  step. The disjoint-group AC form (`regroup_chain_ac`, `regroup_match_complete_ac`,
  `RegroupComplete.lean:248`, `:435`) is a separate statement that bounds the needed
  classes by one per group.

*Proof.* `regroupStep_mem` (`RegroupChain.lean:424`) shows that a declarative step is a
regrouping of the model and strictly shrinks the view's total count, so a chain lies within
the levels the model computes (`regroupChain_mem_levels`, `:437`). The converse is
`regroupChain_of_mem_levels` (`:658`), from the per-kind fit lemmas of `RegroupFits.lean`
(`fitsR_ac_complete` in `RegroupComplete.lean:120`; `fitsR_aci_complete`,
`fitsR_assoc_complete`, `fitsR_left_complete`, `fitsR_right_complete`, `RegroupFits.lean:47`,
`:86`, `:102`, `:111`).

**Adequacy.**

- `regroup_match_iff_laws` (`RegroupLaws.lean`) lifts the completeness to
  any laws, kind and fold direction, with the chains `RegroupChainL`; for a fold its chains
  start from the normal forms of the spine views (`baseRecsR_left_views_iff`,
  `baseRecsR_right_views_iff`) and step by prefix or suffix (`regroupsTo_left_iff`,
  `regroupsTo_right_iff`), so no fold match is excluded. Soundness under laws is
  `regroup_views_sound_{ac,aci,assoc}_laws` (`RegroupLaws.lean`); for folds
  (`EMatch/Flatten/FoldRegroup.lean`) `regroup_views_sound_left`,
  `regroup_views_sound_right` and the engine-loop versions `regroupSkip_views_sound_left`,
  `regroupSkip_views_sound_right` prove that every view of `enumerateR` and `enumerateRSkip`
  for a laws-free fold denotes the node's fold in every magma, through
  `reach_lfold_left`/`reach_rfold_right` (the walk's records by `rawNodeD_left_sound` and
  `otLeft_sound`, each regrouping by `regroup_step_sound_left`). The declarative chains keep
  the fold too (`regroupsTo_left_sound`, `regroupStep_left_sound`, `regroupChain_left_sound`,
  `regroup_chain_left_sound`, and the right versions). `regroup_views_sound_assoc_laws_dir`
  and `regroupSkip_views_sound_assoc_laws_dir` extend the monoid soundness under an identity
  from `.both` to every direction. No theorem covers a match that needs both a leaf refold
  (Section 4.3) and a regrouping.
- `RegroupStep` reuses the model's `addG` and `needsAfter`, so completeness is with respect
  to a declarative view transformation plus the engine's own demand bookkeeping.
- That the item limit loses no match (a record needing more distinct classes than there are
  items cannot have them all taken) is argued in the docstring of `withinLimit`
  (`RegroupDefs.lean:197-200`). `regroup_match_iff` includes the limit on its right-hand side,
  so it characterizes the engine's enumeration, not the unlimited one.
- The engine's bounds `MAX_REGROUP_VIEWS` (2^14 records) and `MAX_REGROUP_WORK` (2^20
  entries examined), and the count overflow of normalization, are modelled in
  `EMatch/Flatten/RegroupBounds.lean` (`BSt.run`, the loop with the engine's
  counters; `regroupBounded_halt_iff`, `regroupBounded_exact`, `regroupBounded_query_exact`,
  Section 4.7). Past a bound the engine stops regrouping the node and sets
  `regroup_truncated`. The design note
  ([`runtime-completeness-checks.md`](../../egraph/doc/future/runtime-completeness-checks.md),
  Section 3) proposes a per-run check that the counters `flatten_regroup_truncated`,
  `flatten_skipped` and `flatten_overflowed` are zero, the hypothesis `hz` of
  `regroupBounded_query_exact`.

**Under laws, and what stays lost.**

```lean
theorem regroup_match_iff_laws {c : FCtx} {dir : Sym → Dir} {σ : Binding} {a : RAtom}
    {κ : FlatKind} (hκ : a.shape.flatKind = some κ) :
    AtomSatG (Enumerator.regroup dir) c σ a ↔
      ∃ id n, σ.node a.node = some id ∧ (id, n) ∈ c.G.nodes ∧
        σ.cls a.node = some (c.G.find id) ∧ n.op = a.op ∧
        ∃ r₀ ∈ baseRecsR (c.ctx a.op κ) (dir a.op) (c.laws a.op) n, ∃ r,
          RegroupChainL (c.ctx a.op κ) (dir a.op) (c.laws a.op) r₀ r ∧
          r.2.2.length ≤ a.elems.length ∧
          MatchN c.G a.shallow ⟨a.op, ofView κ r.1⟩ σ ∧
          ∀ l ∈ r.alt, l.okE κ (takenOf σ a.elems)
```

**Reading.** The same equivalence as `regroup_match_iff` without the laws-free hypothesis:
the chains `RegroupChainL` step by a laws-free regrouping followed by normalization under
the operator's laws, so a step may drop the unit, clamp a count to zero or cancel an inverse
pair. The needed classes of a record are those its normalized view still holds
(`needsAfter`), and a leaf that gains a dropped class is flagged (`addG`); the fixture
`flatten_regroup_laws_drop_need.egg` records that behaviour in the engine. The theorem says what the
engine finds under laws, relative to the classes present; it does not say the engine finds
every match the theory entails. Two kinds of match it excludes are stated as theorems:

```lean
theorem regroup_insert_unit_lost :
    (∀ (M : Type) [AddCommMonoid M] (den : C → M), ConsistentAC exInsCtx den →
        LawsModelAC exUnitLaws den → den 6 + den 8 = den 1 + den 3) ∧
      ∀ d, (Multiset.entries {6, 8}, d) ∉
        enumerateRSkip exInsCtx .both exUnitLaws 2 exInsRoot

theorem regroup_idem_overlap_lost :
    (∀ (M : Type) [SemilatticeSup M] [OrderBot M] (den : C → M), ConsistentACI exAciCtx den →
        den 1 ⊔ den 3 ⊔ den 4 = den 1 ⊔ den 2 ⊔ den 3) ∧
      ∀ d, ([(1, 1), (3, 1), (4, 1)], d) ∉ enumerateRSkip exAciCtx .both Laws.free 3 exAciRoot
```

**Reading.** Each is a concrete graph in which a view equal to the node in every model of
the laws is not enumerated by the regrouping loop. In the first, with `zero ∋ add{B, D}`, the
view `add{A, C}` of `add{add{A, B}, add{C, D}}` is reached only by inserting the unit and
regrouping; a chain opens and contracts and never inserts, and insertions have no bound. The
fixture `flatten_regroup_laws_insert.egg` records the loss in the engine; `(set-option
:completion eager)` proves the equality instead. A documented limit of the regrouping
guarantee, not a defect. In the second, `S{A, B, C}` equals `S{A, C, sab}` by idempotence,
but a regrouping replaces the group and never keeps a member beside its class
(`regroup_idem_overlap_loop_lost`, the second conjunct of the statement quoted above, which
the sources hold as two theorems); the view is sound in every join semilattice
(`regroup_idem_overlap_sound`, its first conjunct). The engine forms it in a stage after the
loop, below.

**Overlap views under idempotence** (`EMatch/Flatten/RegroupOverlapDefs.lean`,
`RegroupOverlap.lean`, `RegroupOverlapBounds.lean`). For an `:assoc-comm-idem` operator, after the regrouping loop, the engine
also matches the *overlap views* of every view the loop ends with: the view with the class
`g` of an `f`-member added and some members of its group dropped. A dropped member is
covered by `g`, a kept member is absorbed, so the view denotes the node in every join
semilattice where the members denote their classes (`overlap_step_sound_aci`,
`overlap_step_sound_aci_laws` under an identity; `regroupO_views_sound_aci_laws`,
`regroupSkipO_views_sound_aci_laws` for every view of both enumerations). The pattern's item
count fixes how many members are kept: with `base` the entries of the view plus one when
`g` is not in the view, the stage drops `k = base - limit` members, so the view has `limit` entries, one
per item, and a rest variable holds nothing (`overlapDrops`, `overlapFits`). The group must
have at least two classes, all in the view, not `g`; at least one member is kept; a group with
`g` already in the view and nothing to drop would repeat the view. The candidates are the
loop's: the `S`-members on the use lists of the view's classes, the matched node among them,
so a pattern with one item more than a node has children binds that item to the node's own
class (`S{s, A, B} = s` for `s = S{A, B}`), as the conformance sample `conform/c1_0101.egg`
shows. The dropped sets are the
`k`-element sublists of the group's classes in the order of `List.sublists` (`dropSets`), the
engine's order of combinations. An overlap record keeps the leaves and needs of a regrouping
by the same group (`deriveRec`), so it needs `g`, and the demand rule reads it unchanged. The
stage regroups nothing and overlaps no overlap view: an overlap view is one step from a view
of the loop, and its source records are the loop's (`SkipSt.overlapAll`). Two items never
bind the same class: an overlap view is a set, `g` enters it once, and the set decomposition
takes a distinct entry per item, as on every set view. For an operator without idempotence
every family is empty and each definition is the one without the stage
(`enumerateRO_eq_of_not_aci`, `enumerateRSkipO_eq_of_not_aci`,
`regroupChainO_iff_of_not_aci`).

```lean
theorem regroupSkipO_match_iff_laws {c : FCtx} {dir : Sym → Dir} {σ : Binding} {a : RAtom}
    {κ : FlatKind} (hκ : a.shape.flatKind = some κ) :
    AtomSatG (Enumerator.regroupSkipO dir) c σ a ↔
      ∃ id n, σ.node a.node = some id ∧ (id, n) ∈ c.G.nodes ∧
        σ.cls a.node = some (c.G.find id) ∧ n.op = a.op ∧
        ∃ r₀ ∈ baseRecsR (c.ctx a.op κ) (dir a.op) (c.laws a.op) n, ∃ r,
          RegroupChainO (c.ctx a.op κ) (dir a.op) (c.laws a.op) a.elems.length r₀ r ∧
          r.2.2.length ≤ a.elems.length ∧
          MatchN c.G a.shallow ⟨a.op, ofView κ r.1⟩ σ ∧
          ∀ l ∈ r.alt, l.okE κ (takenOf σ a.elems)

theorem regroup_idem_overlap_found :
    ∃ d, ([(1, 1), (3, 1), (4, 1)], d) ∈ enumerateRSkipO exAciCtx .both Laws.free 3 exAciRoot ∧
      d.acceptsE .aci [1, 3, 4]
```

**Reading.** `regroupSkipO_match_iff_laws` is `regroupSkip_match_iff_laws` with the stage:
`RegroupChainO` is a chain of regroupings under the laws followed by at most one overlap step
(`OverlapStepL`: an `f`-member of class `g`, a raw overlap fit of its group, normalized under
the laws, with the derived leaves and needs). The theorem says what the engine finds for an
idempotent operator, relative to the classes present; `regroupO_match_iff_laws` is the same
for the full enumeration with the stage, and `regroupSkipO_views_iff_laws`,
`regroupO_views_iff_laws` the versions at the level of views. The statements without the
stage (`regroup_match_iff_laws`, `regroupSkip_match_iff_laws`) hold
of the loop alone. `regroup_idem_overlap_found` is the counter-model turned witness: in the
graph of `regroup_idem_overlap_sound`, the view `{a, c, G}` is enumerated for a pattern of
three items and accepts the item classes, so `(S x y z)` binds `x = a, y = c, z = G`
(`flatten_regroup_laws_idem.egg`, whose last check is `check-eq`, and which also checks the
four-item match `(S w x y z)` keeping both members). Two matches the stage
does not form: a view with two overlap groups (`{A, C, sab, scd}` of `S{A, B, C, D}`), and a
kept member in a rest variable; both are documented limits of the stage, as the unit
insertion is of the loop.

*Proof.* The stage is a fold over the loop's views; `overlapAll_spec`
(`RegroupOverlap.lean`) shows, with the loop's `Core` invariant as its hypothesis, that every
record it adds is one overlap step from a reachable record (`ReachO`) and that every overlap
step of every loop view by a candidate group is covered (`Cov`) by a record of the result:
its three skips (a target with an unconditional record, the source's first unconditional
record alone, the signature deduplication) drop only covered records, by `cov_uncond`,
`Cov.derive` and `cov_of_same` as in the loop. `regroupSkipO_spec` joins it with
`regroupSkipG_spec`, `regroupSkipO_iff` and `enumerateRSkipO_iff` conclude that the engine's
enumeration with the stage accepts the same matches as `regroupAllO`, the full enumeration
followed by the stage, and `prune_regroupO` (through `recRel_overlap`) keeps the pruning
match-preserving, so `Enumerator.regroupSkipO` meets the plan specification
(`regroupSkipO_specE`, `regroupSkipO_plan_sound`, `regroupSkipO_plan_complete`,
`regroupSkipO_plan_complete_laws`). `regroupAllSkipOAt_eq` is `regroupAllSkipAt_eq` with the
stage: a group holding no class of the view has no overlap fit (`overlapFits_nil_of_not_cand`).

**The bounds.** The stage counts against the same budgets as the loop: the use lists of
each source view, the children of each candidate and one unit per raw fit against
`MAX_REGROUP_WORK`, each record added against `MAX_REGROUP_VIEWS`, elements against
`MAX_ELEMS`, checked where the engine checks them (`BSt.overlapAll`,
`RegroupOverlapDefs.lean`). The raw fits are counted one by one because a group of `m`
classes has `C(m, k)` of them, and the count must stop the stage before the family is
enumerated. `RegroupOverlapBounds.lean` repeats the simulation of `RegroupBounds.lean` for
the stage (`overlapAll_stepR`, `overlapAll_projR`): `regroupBoundedO_cases`,
`regroupBoundedO_halt_iff`, `regroupBoundedO_exact`, `regroupBoundedO_sub`,
`regroupBoundedO_reach`, and the final theorems `regroupBoundedO_plan_sound`,
`regroupBoundedO_plan_complete`, `regroupBoundedO_query_exact`, `regroupBoundedO_match_exact`:
with the three counters zero the bindings emitted are exactly those of
`Enumerator.regroupSkipO`, and a truncated run reports only matches. No fixture exercises a
truncation inside the stage (Section 9): a family large enough to pass
`MAX_REGROUP_VIEWS` needs a set of about fifty children, on which the set decomposition of a
five-item pattern enumerates `48 · 47 · 46 · 45 · 44` partial assignments per node before the
stage is reached, hours in a debug build.

**Cost.** The stage runs only for `:assoc-comm-idem` operators and patterns with items
(`SkipSt.overlapAll`'s guard, `kind == FlatKind::Aci && limit > 0` in `flatten.rs`): an AC or
sequence operator pays nothing. For a set operator it reads the use lists of each loop view
once more and, per candidate group of `m` classes, enumerates `C(m, k)` combinations, each
normalized and deduplicated by signature; the budgets bound both. The suite timings on
record are 155 s for `egg_tests.rs`, 126 s for `flatten_differential.rs` and 51 s for
`conform.rs` (debug build, one thread, medians of three), measured without the stage; the
stage is guarded by the kind, so an operator without idempotence runs the same code.

### 4.7 The engine's regrouping loop and its skips

`regroupAll` derives every record level by level. The engine regroups view by view instead,
largest total count first, and skips records whose matches another record of the same view
already admits. `EMatch/Flatten/RegroupSkipDefs.lean` models that loop step for step
(the pseudo-code follows). The state `SkipSt` (`:89`) holds the distinct views in
order of entry, each view's records in insertion order, the views already regrouped, and the
signatures of the records regrouping added to each view. The next view (`SkipSt.next`,
`:139`) is the one not yet regrouped with the largest total count, the latest entry among
equal counts, as the engine's `BinaryHeap` of `(size, entry)` pairs pops it. The candidate
groups (`groupsOfEngine`, `:82`) are the `f`-members sorted by node id. For each candidate,
each fit and each normalized target (`SkipSt.addTarget`, `:106`), the loop gives nothing to
a target that has an unconditional record (no leaf, no
needed class), derives only from the source's first unconditional record when it has one
(`srcRecs`, `:70`), and drops a derived record whose signature the target already has
(`SkipSt.addRec`, `:97`); a signature (`recSig`, `:59`) is the leaves' opened classes, flags
and sorted classes, and the needed classes, compared as multisets by `RecSig.same` (`:63`),
as the engine does by sorting them. `regroupSkipG` (`:180`) runs the loop with a fuel larger
than the number of reachable views, and `Enumerator.regroupSkip` (`:200`) is
`Enumerator.regroup` with it in place of `regroupAll`.

**Pseudo-code: the regrouping loop and the overlap stage.**

```
regroup(node, κ, dir, laws, items):                   -- SkipSt.run; flatten.rs FlattenScratch::regroup
  records := walk views with demands                  -- baseRecsR; enumerate (spine(dir) for a fold)
  entries := distinct views in order of entry         -- SkipSt.init, SkipSt.order
  heap := (size(view), entry) for each entry          -- viewSize; BinaryHeap<(u128, usize)>
  views := 0; work := 0                               -- BSt counters; MAX_REGROUP_VIEWS, MAX_REGROUP_WORK
  while heap not empty:
    w := pop the largest size, latest entry on a tie  -- SkipSt.next
    if w already regrouped: continue                  -- never fires: regroupRec_shrink
    mark w regrouped                                  -- SkipSt.mark
    cands := f-members holding a class of w, by node id   -- groupsOfEngineAt; Members::containing (by_contains)
    work += use-list lengths; if work > MAX_REGROUP_WORK: truncate; stop
    for (g, grp) in cands:                            -- SkipSt.groupStep
      work += |grp|; if work > MAX_REGROUP_WORK: truncate; stop
      for raw in fits(κ, dir, w, g, grp):             -- fitsR: sub-multiset | subset | run | prefix | suffix, ≥ 2 entries, not all of w, g ∉ grp
        t := normalize(κ, laws, raw)                  -- normalize; nary_canon::normalize
        if t is not a node, or a count overflows: count flatten_overflowed; continue   -- Ix.wide, saturated_size
        assert t not regrouped                        -- addTarget_spec: regroupRec_shrink
        if t is new: push (size(t), t)                -- SkipSt.addTarget
        if some record of t is unconditional: continue        -- RecR.uncond
        for r in srcRecs(records of w):               -- srcRecs: the first unconditional record alone, else all
          d := (t, leaves of r with g added where they hold a class of grp, needs of r less grp plus g, kept if t holds them)
                                                      -- deriveRec, addG, needsAfter
          if signature(d) already at t: continue      -- RecSig.same; sigs
          views += 1; if views > MAX_REGROUP_VIEWS: truncate; stop
          add d to t                                  -- SkipSt.addRec
  if κ = set and |items| > 0:                         -- SkipSt.overlapAll; the overlap stage, idempotence only
    for w in the loop's views, in entry order:        -- st₀.order; entries[0..n_loop]
      cands := f-members holding a class of w, by node id   -- groupsOfEngineAt
      work += use-list lengths; if work > MAX_REGROUP_WORK: truncate; stop
      for (g, grp) in cands:                          -- SkipSt.overlapGroupStep
        work += |grp|; if work > MAX_REGROUP_WORK: truncate; stop
        cs := classes of grp, sorted, distinct        -- groupClasses
        if g ∈ cs or |cs| < 2 or cs ⊄ w: continue     -- overlapDrops
        base := |w| + (g ∉ w ? 1 : 0); if base < |items|: continue
        k := base - |items|; if k ≥ |cs| or (k = 0 and g ∈ w): continue
        for D in the k-element sublists of cs, in sublists order:   -- dropSets; next_colex
          work += 1; if work > MAX_REGROUP_WORK: truncate; stop
          t := normalize(κ, laws, (w less D) ++ [g])  -- overlapFits; normalize
          if t is not a node, or a count overflows: count flatten_overflowed; continue
          if t is new: enter t (no heap: the stage regroups nothing)  -- SkipSt.addTargetO
          if some record of t is unconditional: continue
          for r in srcRecs(the loop's records of w):  -- st₀.recs w; records with index < n_loop
            d := (t, leaves of r with g added where they hold a class of grp, needs of r less grp plus g, kept if t holds them)
            if signature(d) already at t: continue
            views += 1; if views > MAX_REGROUP_VIEWS: truncate; stop
            add d to t
  keep the records needing at most |items| classes    -- withinLimit; Demand::needs
```

The model's `regroupSkipG` has no bounds and `BSt.run` adds them at the same places; the
engine also caps the takeable closure at 4,096 classes (`takeableRCap`) and skips regrouping
altogether when the decomposition has no item and the laws cannot drop a class
(`laws_drop`, `canDrop`). The overlap stage (`SkipSt.overlapAll`, `BSt.overlapAll`,
`RegroupOverlapDefs.lean`) runs after the loop, only when the loop is not truncated, and
derives from the loop's records alone, so an overlap view is one step from a view of the
loop (Section 4.6, "Overlap views under idempotence").

The proof turns on one relation. `Cov c b` (`EMatch/Flatten/RegroupSkip.lean:369`) says the
record `c` **covers** `b`: same view, each leaf of `c` has a leaf of `b` with the same opened
class, flag and classes, and every class `c` needs, `b` needs. A covering record passes the
demand rule whenever the covered one does (`Cov.accepts`, `Cov.acceptsL`, `:404`, `:416`) and
needs no more classes (`Cov.length`, `:427`). Each skip drops only covered records: an
unconditional record covers every record of its view (`cov_uncond`, `:479`), equal signatures
cover each other (`cov_of_same`, `:490`), and regrouping two records the same way preserves
the cover (`Cov.derive`, `:471`).

**`regroupSkipG_iff`** (`EMatch/Flatten/RegroupSkip.lean:1222`):

```lean
theorem regroupSkipG_iff {ctx : Ctx} {dir : Dir} {laws : Laws} {base : List RecR}
    (hb : BaseGood ctx.κ base) {gs : List (C × List (C × Nat))}
    (hgs : ∀ gg ∈ gs, gg ∈ groupsOf ctx) (hgs' : CandSup ctx dir gs)
    {F : Nat} (hF : ∀ r ∈ base, viewSize r.1 ≤ F) {limit : Nat} {w : List (C × Nat)}
    {taken : List C} :
    (∃ r ∈ withinLimit limit (regroupSkipG ctx dir laws gs base), r.1 = w ∧
        ∀ l ∈ r.alt, l.okE ctx.κ taken) ↔
      ∃ r ∈ withinLimit limit (regroupLevels ctx dir laws F base), r.1 = w ∧
        ∀ l ∈ r.alt, l.okE ctx.κ taken
```

**Reading.** The theorem is at the level of records, for any laws, kind, fold direction and
candidate order. Its hypotheses are properties of the engine's inputs, each discharged by a
lemma: well-formed walk records (`BaseGood`: positive counts, distinct classes for multisets
and sets, no class needed twice) by `baseGood_baseRecsR`; candidate groups that are filed
`f`-members (`hgs`) by `groupsOfEngine_sub`; a candidate list that holds every member with a
fit (`CandSup`) by `candSup_of_sup` from `groupsOfEngine_sup`; and a bound on the walk
views' sizes (`hF`) by `viewSize_le_regroupFuel`. The conclusion: for any view, the engine's
loop with its three skips keeps a record within the item limit that passes the engine's
demand rule exactly when the full enumeration does, so the skips lose no match and admit
none. `regroupSkipG_iffL` is the same statement under laws. Outside: the bounds
(`regroupBounded_query_exact`) and the sizes saturating at `u64::MAX`, which the engine
counts in `flatten_overflowed`.

*Proof.* `regroupRec_shrink` (`:259`) shows that a regrouping strictly shrinks a view under
any laws, so the full enumeration is exactly the set of records reachable from the walk's
records (`mem_regroupLevels_iff_reach`, `:345`), and a target is never a view already
regrouped (`addTarget_spec`; the engine asserts it in debug builds). The loop invariant
`SkipInv` (`:1008`) says that every record is reachable and every regrouped view is
**closed**: each regrouping of each of its records is
covered by a record of the target; a skipped record is covered at the moment it is skipped.
`run_finished` (`:1093`) shows the loop ends with every view regrouped, and
`regroupSkipG_spec` (`:1179`) concludes by induction on the chain that every record kept is
reachable and every reachable record is covered by a kept one.

`atomSat_regroupSkip_iff` (`:1355`) lifts this to atoms: an atom holds under
`Enumerator.regroupSkip` exactly when it holds under `Enumerator.regroup`. `regroupSkip_spec`
(`:1328`) discharges `Enumerator.Spec`, so the plan theorems of Section 4.4 apply
(`regroupSkip_plan_sound`, `regroupSkip_plan_complete`, `:1372`, `:1380`).
**`regroupSkip_match_iff`** (`:1410`) is `regroup_match_iff` with `Enumerator.regroupSkip`
on the left, word for word on the right:

```lean
theorem regroupSkip_match_iff {c : FCtx} {dir : Sym → Dir} {σ : Binding} {a : RAtom}
    {κ : FlatKind} (hκ : a.shape.flatKind = some κ) (hlaws : c.laws a.op = Laws.free) :
    AtomSatG (Enumerator.regroupSkip dir) c σ a ↔ ...
```

**Reading.** With the engine's loop in place of the full enumeration, an n-ary atom holds
exactly when `regroup_match_iff`'s chain condition holds: the engine's loop meets the
specification `regroup_match_iff` states. The laws version is `regroupSkip_match_iff_laws`.

**Adequacy.**

- The engine computes a view's size as a `u128` sum of counts read as `u64`
  (`saturated_size`, `flatten.rs`). A count past `u64::MAX` is read as `u64::MAX`; such a
  count is counted in `flatten_overflowed`, and a fit whose normalized
  view holds one is skipped as a fit whose normalization overflows the width (`Ix.wide`).
  With the counter zero every size is exact, so a regrouped view is strictly smaller than its
  source (`regroupRec_shrink`), which is what `regroupBounded_query_exact` assumes. No
  configured width is past 64 bits, so the case is unreachable.
- The engine counts `MAX_REGROUP_VIEWS` after the skips, and `BSt.run`
  (`RegroupBounds.lean`) counts at the same places; with the three counters zero the bounded
  run is this loop (`regroupBounded_exact`).
- The conformance generators use `regroupLevels` (`STATUS.md`): the engine's loop
  emits the same `check-eq` sets in another order, which changes the sampled `check-neq`
  candidates.

**The candidates and the bounds.**

```lean
theorem regroupAllSkipAt_eq (ctx : Ctx) (dir : Dir) (laws : Laws) (base : List RecR) :
    regroupAllSkipAt ctx dir laws base = regroupAllSkip ctx dir laws base

theorem regroupBounded_query_exact {c : FCtx} {dir : Sym → Dir} {sig : Sym → Kind}
    {as : List RAtom} (r : Nat) (hw : QueryFWF c sig as) (B : Bounds) (ix : Ix)
    (hz : (runB B ix dir c (planF as ∅ r) EEnv.empty).2 = 0) :
    (∀ env ∈ (runB B ix dir c (planF as ∅ r) EEnv.empty).1,
        ∀ a ∈ as, AtomSatG (Enumerator.regroupSkip dir) c env.σ a) ∧
      ∀ σ', (∀ a ∈ as, AtomSatG (Enumerator.regroupSkip dir) c σ' a) →
        ∃ env ∈ (runB B ix dir c (planF as ∅ r) EEnv.empty).1, Extends env.σ σ'
```

**Reading.** `regroupAllSkipAt_eq` has no hypothesis: the loop that reads each view's
candidates from the use lists `by_contains` of its classes, as the engine does (`isCand`,
`groupsOfEngineAt`, `SkipSt.runAt`, `regroupAllSkipAt`), ends with the same records as the
loop over every filed `f`-member (`regroupAllSkip`; `regroupView_filter_cand`,
`runAt_eq_run`), because a
member holding no class of the view has no fit for any kind (`isCand_of_fitsR`,
`fitsR_nil_of_not_cand`). `CandSup ctx dir gs` (`RegroupSkipDefs.lean`) asks of the
candidate list only the members with a fit in some view (`CandSupAt` per view), which
`groupsOfEngineAt_candSupAt` discharges for the engine's candidates.
`regroupBounded_query_exact` runs the flattened plan with the
engine's bounds `B` and multiplicity width `ix` and sums three counters over its `Flatten`
evaluations: `flatten_regroup_truncated`, `flatten_skipped` and `flatten_overflowed`. When
the sum is zero (`hz`), the bindings emitted are exactly those of the unbounded engine loop,
which `regroupSkip_match_iff` characterizes. The counters are engine outputs, so `hz` is a
condition a run can check on itself; the design note assigns it to tier 1. With a counter
nonzero, only soundness holds (`regroupBounded_plan_sound`): every emitted binding is a
match, and some matches may be missing.

**Hypotheses of the flattened-matching theorems, classified.**

| Hypothesis | Theorem | Class | Source |
|---|---|---|---|
| `hκ : a.shape.flatKind = some κ` | `regroup_match_iff`, `regroupSkipO_match_iff_laws` | derived | the atom's shape, from the resolver's flattening of the pattern |
| `hlaws : c.laws a.op = Laws.free` | `regroup_match_iff`, `regroupSkip_match_iff` | derived | the operator declaration; `regroup_match_iff_laws` and `regroupSkipO_match_iff_laws` drop it |
| `BaseGood`, `hgs`, `CandSup`, `hF` | `regroupSkipG_iff` | derived | `baseGood_baseRecsR`, `groupsOfEngine_sub`, `candSup_of_sup`, `viewSize_le_regroupFuel` |
| `hw : QueryFWF c sig as` | `flatten_plan_*`, `regroupBounded_query_exact` | assumed | the resolver and the index, as `AtomsWF` in Section 3 |
| `hz`: `flatten_regroup_truncated`, `flatten_skipped`, `flatten_overflowed` sum to zero | `regroupBounded_query_exact`, `regroupBoundedO_query_exact` | derived | the engine's own counters; tier 1 of the design note |
| `SeqShaped ctx` | `rawNodeD_left_iff`, `regroup_views_sound_left` | derived | the operator declaration: every `f`-member of a sequence operator is a sequence node |
| `MembersTwoClassesL`, `NodeTwoClassesL` | `demand_engine_complete_aci` (through `twoClassesL_of_members`) | assumed | the collapse invariant of `add` and rebuild on set nodes; `aci1.egg` records it |
| `ConsistentAC`, `ConsistentACI`, `ConsistentL` | the `regroup_views_sound_*` theorems | assumed | the reading of a congruence-closed store: each filed `f`-member denotes its class; for a fold, in any magma, so cyclic classes are covered (`consistentL_cyclic_satisfiable`) |
| a normal form reached only by inserting the unit | `regroup_match_iff_laws` | limit | `regroup_insert_unit_lost`; `flatten_regroup_laws_insert.egg` |
| a view with two overlap groups, a kept member in a rest variable | `regroupSkipO_match_iff_laws` | limit | not formed by the stage; no theorem, documented in Section 4.6 and Section 9 |
| opening or regrouping off a fold's spine | `otLeft_sound`, `regroup_views_sound_left` | limit | `fold_open_off_spine_unsound`, `regroup_off_spine_unsound` |
| the walk's bounds `MAX_VIEWS`, `MAX_WORK`, `MAX_ELEMS` | `views_complete` | limit | the model enumerates without bound; a skipped node is counted in `flatten_skipped`, which `hz` reads |

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

`Infer` (`CC/Defs.lean:225`) lists the inference steps:

```lean
inductive Infer (L : Laws n) : State n → State n → Prop
  | mint {st : State n} {N : Monomial n} {d : Fin n} :
      (∀ x ∈ N, st.Child x) → st.Fresh d → Infer L st (st.addNode N d)
  | joinMerge {st : State n} {M : Monomial n} {c : Fin n} {N : Monomial n} {d : Fin n} :
      (M, c) ∈ st.nodes → (N, d) ∈ st.nodes → E L st.eqs M N → Infer L st (st.merge c d)
  | retire {st : State n} {M : Monomial n} {c : Fin n} :
      (M, c) ∈ st.nodes → Infer L st (st.retire M c)
  | unretire {st : State n} {M : Monomial n} {c : Fin n} :
      (M, c) ∈ st.retired → Infer L st (st.unretire M c)
  | setRhs {st : State n} (rhs' : Fin n → Monomial n) :
      Infer L st { st with rhs := rhs' }
```

**Reading.** **mint** adds any monomial whose children already occur as children of nodes
(`State.Child`) as a node in a fresh class: the engine's `materialize` on a hash-cons miss.
The monomial need not be a reduct of a node; the (B) loop materializes the normal forms of
both reducts of an lcm that is no node. **joinMerge** merges two nodes whose monomials are
equal in `E L st.eqs`, the theory generated by the state's own classes (`State.eqs`, `:201`:
two nodes of one class) together with congruence, the law instances and cancellation. The
premise is a derivation from the state, not an assumption about the asserted equalities `S`:
a chain of rule, law and same-class steps in either direction (`Infer.joinMerge_of_steps`)
and the cancel-close of two present nodes (`Infer.cancelMerge`) are instances. **retire**
retires a node; **unretire** re-activates a retired node (the engine's `materialize` and
recanonization paths clearing `FLAG_AC_COLLAPSED`); **setRhs** overwrites the stored
right-hand sides. These three change neither the nodes nor `find`. The engine's
re-activation is `unretire` followed by `setRhs (st.refreshRhs M c)`
(`unretire_refresh_reachable`), and `unretire_refresh_I5` shows the pair keeps I5.

**The engine's merges as `Infer` runs** (`CC/EngineSteps.lean`). `Materialize st N st' c` is
`materialize`: a hash-cons hit on a node `(N, c)` or a mint in a fresh class `c`.
`Normalize L inv st` is the normalization of a pair side before it is materialized:
rewriting by the state's rules and removing `{x, inv x}` pairs (`group_cancel_pairs`). Four
theorems state that the state after each merge source of `cc_round` is reached from the
state before by `Infer` steps:

```lean
theorem superpose_infer (hinv : L.HasInv inv) (h₁ : r₁ ∈ st.rules) (h₂ : r₂ ∈ st.rules)
    (hN₁ : Normalize L inv st (criticalPair L r₁ r₂).1 N₁)
    (hN₂ : Normalize L inv st (criticalPair L r₁ r₂).2 N₂)
    (hm₁ : Materialize st N₁ st₁ c₁) (hm₂ : Materialize st₁ N₂ st₂ c₂) :
    Reachable L st (st₂.merge c₁ c₂)
theorem axiomPair_infer (hinv : L.HasInv inv) (hp : AxiomPair L inv k st P₁ P₂)
    (hN₁ : Normalize L inv st P₁ N₁) (hN₂ : Normalize L inv st P₂ N₂)
    (hm₁ : Materialize st N₁ st₁ c₁) (hm₂ : Materialize st₁ N₂ st₂ c₂) :
    Reachable L st (st₂.merge c₁ c₂)
theorem cancelClose_infer (hc : L.cancellative) (hinv : L.HasInv inv)
    (hp : CancelPair st P₁ P₂)
    (hN₁ : Normalize L inv st P₁ N₁) (hN₂ : Normalize L inv st P₂ N₂)
    (hm₁ : Materialize st N₁ st₁ c₁) (hm₂ : Materialize st₁ N₂ st₂ c₂) :
    Reachable L st (st₂.merge c₁ c₂)
theorem inverseRepair_infer (hinv : L.HasInv inv) (hM : (M, g) ∈ st.nodes)
    (hcancel : ReflTransGen (InvCancel inv) M M') (hm : Materialize st M' st' c) :
    Reachable L st (st'.merge c g)
```

**Reading.** `superpose_infer` is the (B) step: two rules, the two reducts of the lcm of
their left-hand sides, each normalized, materialized and merged; the lcm is not required to
be a node, and the left-hand sides are not required to overlap. `axiomPair_infer` is the
per-rule axiom pair: `AxiomPair` lists the pairs `cc_round` builds, `(clamp(B ⊎ {a}), B)`
for idempotence, `(clamp(B ⊎ a^(k−m)), A − a^m)` for a nilpotent order `k`, and the two
group-law pairs `(clamp(B ⊎ {y}), A − {a})` and `(clamp(B ⊎ {x}), A − {y})`.
`cancelClose_infer` is the cancellation closure: `CancelPair` lists C1 (`(A − C, B − C)`
with `C = A ∩ B`), C2 (the cancel-closed disjoint join of two rules) and the per-constant
closure of an emptied side (`(M ⊎ {g}, {g})` for a child class `g`). `inverseRepair_infer`
is `inverse_cancel_repair`: a node merged with its monomial after removing `{x, inv x}`
pairs, a law step rather than a rewrite. The hypotheses are the shape of the step and, for
a law, that the law set has the instance used (`HasInv`, `HasNil`, `HasIdem`); an operator
without an inverse takes `inv := fun _ => none`, for which `Laws.hasInv_none` discharges
`HasInv`. No hypothesis mentions I2. `superpose_example` is a concrete run: on `exSt`
(`Fin 7`, nodes `{x, y}` and `{p}` in class `3`, `{y, z}` and `{q}` in class `4`, so rules
`{x, y} → {p}` and `{y, z} → {q}`), `exSt_criticalPair` computes the pair `({z, p}, {x, q})`
by `decide`, and minting both in classes `5` and `6` and merging them is `Reachable`.
Outside: that a run of `cc_round` is a sequence of these steps in the order the engine
takes them (the theorems cover one merge source each, from the state the step reads), the
degenerate results of `materialize` (an empty monomial resolved to the unit, a singleton to
its class), and the merges recanonicalization performs through `find` on children.

The invariants (`CC/Defs.lean:244-266`, `CC/Assemble.lean:94`):

- **I0**: each class's `rhs` is a node of the class. `I0Active` requires, of each class that
  holds an active node, that its `rhs` be an active node of the class:

  ```lean
  def I0Active (st : State n) : Prop :=
    ∀ M c, (M, c) ∈ st.active →
      ∃ c', (st.rhs (st.find c), c') ∈ st.active ∧ st.find c' = st.find c
  ```

  `I0ActiveAll` (`Assemble.lean:100`) quantifies over every class of `Fin n`; no state with
  a leaf constant satisfies it (`witness_not_all`, Section 5.9).
- **I2**: nodes of one class are theory-equal. This is the soundness invariant.
- **I3**: a retired node rewrites in at least one step to a node of its class.
- **I5**: each class's `rhs` is the `degLex`-least active node of the class.

`RoundFixed` (`CC/Defs.lean:298`) is the fixpoint condition, stated as the three checks of the
engine's `cc_round`: the (A′) normalize pass (`nf_present`), the reducibility pass
(`lhs_reduced`: a node whose monomial contains another rule's left-hand side is rewritten,
merged and retired with `FLAG_AC_COLLAPSED`), and the (B) superposition loop over
overlapping pairs with neither left-hand side containing the other (`cp_joinable`):

```lean
structure RoundFixed (L : Laws n) (st : State n) : Prop where
  nf_present : ∀ M c N, (M, c) ∈ st.active →
    Relation.ReflTransGen (Rw L st.rules) M N → (∀ P, ¬ Rw L st.rules N P) →
    ∃ c', (N, c') ∈ st.active ∧ st.find c' = st.find c
  lhs_reduced : ∀ r₁ r₂, r₁ ∈ st.rules → r₂ ∈ st.rules → r₁ ≠ r₂ → ¬ r₂.1 ≤ r₁.1
  cp_joinable : ∀ r₁ r₂, r₁ ∈ st.rules → r₂ ∈ st.rules → r₁ ≠ r₂ → Overlap r₁.1 r₂.1 →
    ¬ r₁.1 ≤ r₂.1 → ¬ r₂.1 ≤ r₁.1 →
    Joinable (Rw L st.rules) (criticalPair L r₁ r₂).1 (criticalPair L r₁ r₂).2
```

`RoundFixed.cp_joinable_all` recovers joinability for every overlapping pair of distinct
rules, since a containing pair does not exist by `lhs_reduced`; without `lhs_reduced`, an
unrestricted `cp_joinable` would assert joinability of the containing pairs, which the engine
never superposes. `RoundFixed` is a
hypothesis about the final state; no theorem derives it from an engine run.

**Pseudo-code: one AC completion round.**

```
round(st, L):                                         -- Infer* over one round; egraph.rs cc_round
  rules := { (M, rhs(find c)) | (M, c) active, M ≫ rhs(find c) }   -- State.rules; completion_node_ids, class_rhs_into, monomial_cmp_key
  dedup rules by (op, left-hand side), keep the lowest node id            -- hcc; cc_round "Dedup"
  -- (A') normalize every active node and merge its normal form in
  for (M, c) in active:                                -- RoundFixed.nf_present
    N := normal form of M under rules, clamped by L   -- Rw L rules, L.clamp; normalize_ms
    c' := materialize(N)                              -- Infer.mint or hash-cons hit; 11.2
    if find c' ≠ find c: merge(c', c)                 -- Infer.joinMerge; do_merge
  -- reducibility pass with collapse
  for (M, c) in active, for (A, a) in rules, A ⊊ M:   -- RoundFixed.lhs_reduced
    red := clamp((M − A) + a); merge(materialize(red), c)   -- Infer.mint, joinMerge; (A') above
    retire (M, c)                                     -- Infer.retire, I3 "merge before mark"; set_cc_collapsed
  -- (B) superposition of overlapping, non-containing pairs
  for (A, a), (B, b) in rules, A ≠ B, both irreducible:    -- RoundFixed.cp_joinable
    if disjoint(A, B) or A ≤ B or B ≤ A: skip         -- Overlap, ¬ r₁.1 ≤ r₂.1; cc_round partner filter
    AB := lcm(A, B)                                   -- criticalPair; multiset_lcm_into
    c1 := nf(clamp((AB − A) + a)); c2 := nf(clamp((AB − B) + b))
    if find c1 ≠ find c2: merge(materialize(c1), materialize(c2))   -- superpose_infer
  axiom pairs and cancel-closure per rule             -- axiomPair_infer, cancelClose_infer; 11.4
  return "changed" iff a merge, a mint or a reactivation happened
```

The engine's (B) loop finds partners through the use lists of the rule's children rather
than over all pairs, restricts intermediate rounds to pairs with a touched endpoint, and
meters the round against `completion_work_budget`; the model has no budget and enumerates
every pair.

### 5.2 Soundness

**`completion_sound`** (`CC/Main.lean:44`):

```lean
theorem completion_sound {L : Laws n} {S : Set (Monomial n × Monomial n)}
    {st₀ st : State n} (hreach : Reachable L st₀ st) (h₀ : I2 L S st₀) : I2 L S st
```

**Reading.** One hypothesis on the start state, `h₀ : I2`: the initial classes are
theory-equal, which holds of a state whose classes come from asserted equations and
congruence. `hreach` says the final state is reached by steps of `Infer`. The (A′) merge,
the reducibility pass, the (B) superposition, the axiom pairs, the cancellation closure and
the inverse repair are `Infer` runs by the theorems of Section 5.1 (`superpose_infer`,
`axiomPair_infer`, `cancelClose_infer`, `inverseRepair_infer`). The conclusion is I2 of the final
state: two nodes in one class spell theory-equal monomials, so no merge is unsound. Lattice
merges (`lattice_merge_sound`, under `FlatSound`), the inverse rules R1 to R5
(`inv_rules_sound`) and the spine-restricted `a_round` (`aRound_sound`) extend the result to
the engine's other merge sources. Outside: the merges recanonicalization performs through
`find` on children, which the model treats as already done, and termination.

*Proof.* Induction on the run (`soundness`, `CC/Lemmas.lean:285`), one case per step
(`Infer_I2`, `:265`). A mint is alone in a fresh class. A join-merge chains I2 through the
merged pair (`merge_I2`, `:180`); its derivation in `E L st.eqs` is a derivation in
`E L S` because every equality the state asserts is one under I2 (`E_eqs_sound`, `:211`,
induction on the derivation). Retire, unretire and `setRhs` change neither the nodes nor
`find`. I4 is preserved because a mint's children already occur as children (`Infer_I4`,
`:541`).

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

**Reading.** The theorem is about one final state `st` and says nothing about how it is
reached. The table below gives each hypothesis, who supplies it, and the check the runtime
design note proposes (tier 1: every run, one pass over the nodes; tier 2: in CI, by a proved
Lean checker on a dump of the final state). The engine-side hypotheses are I5 (`h5₀`,
`hrun`, `ha`), `h0`, `hcanon`, `hcc` and `hfix : RoundFixed`; the input supplies `hS`;
the law declaration supplies `hlaw` and `hnf_ax`, discharged in `CC/Laws/` for every law set
the model names; the law part of `hcp` (`AxiomCP`) is derived from the fixed round and the
per-law conditions on the rules for those law sets (`axiomCP_of_laws`, Section 5.6); no
engine fact supplies `hcancel`, which Section 5.7 replaces by lattice closure in the bundles.
The conclusion is completeness at the fixpoint: two theory-equal active nodes are in one class.
Outside: retired nodes (in a class with their reduct by I3, not by this theorem), leaf
constants (Section 5.9), the number of rounds, and any run that stopped on a budget.

`h0` constrains only the classes that hold an active node, and `hcc` only the active
nodes; the statement over every class of `Fin n` is the corollary
`completion_complete_at_convergence_of_all` (`CC/Main.lean:125`). The theorem keeps `hcp` as
stated; the bundles `CompleteHyps` and `CompleteAtoms` take instead
`hcp_ax : AxiomCP L st.rules` (`CC/Assemble.lean`), and `hcp_of_fixed` rebuilds `hcp` from
`RoundFixed` and `AxiomCP`: `ruleRuleCP_of_fixed` lifts `RoundFixed.cp_joinable_all` to
plain rewriting (each plain reduct reaches its clamp in at most one law step,
`clamp_rtg_RwAx`, and a clamped step embeds, `Rw_rtg_embed`). The law theorems of
`CC/Laws/Main.lean` discharge their rule-rule condition `RuleRuleCP` the same way. For a law
set `LawSpec` names, `CompleteHyps.ofLaws` and `CompleteAtoms.ofLaws` build the bundles
from the per-law conditions `LawSpec.Conds` in place of `hcp_ax`, which `axiomCP_of_laws`
derives (Section 5.6).

| Hypothesis | Meaning | Class | Source | Runtime check |
|---|---|---|---|---|
| `h5₀`, `hrun`, `ha` | minimal-monomial maintenance from a good initial state, agreeing with `st` at the end | assumed | equivalent to assuming I5 (see below); `reachable_I5` is the engine content | tier 1, as I5; `check_min_monomial_invariant` exists as a debug check |
| `h0` | each class holding an active node has an active node as `rhs` | assumed | `class_rhs_into` | tier 1 |
| `hcanon` | stored right-hand sides are clamp-normal | assumed | the output of `nary_canon` | tier 1 |
| `hfix` | the round is a fixpoint (`RoundFixed`) | assumed | the confirmation round of `cc_round` at convergence | tier 2 (`nf_present`, `lhs_reduced`, `cp_joinable`) |
| `hlaw`, `hnf_ax` | law instances decrease `degLex`; clamp outputs are law-normal | derived | discharged for every `NFLaw` instance in `CC/Laws/` | once per signature |
| `hcp`, rule-rule part | every critical pair of two rules is joinable under plain rewriting | derived | `ruleRuleCP_of_fixed`, `hcp_of_fixed` from `hfix` | none beyond `hfix` |
| `hcp`, law part (`AxiomCP`) | every critical pair involving a law instance is joinable | derived for the law sets `LawSpec` names; assumed for an abstract law set | `axiomCP_of_laws` from `hfix` and the per-law conditions `LawSpec.Conds` on left-hand sides (`hu`, `hlhs`, `hax`, `hmatch`), which `CC/Laws/` states; `Laws/InvRulesMain.lean` derives the inverse ones from the fixpoints of R1 to R5 (`LawSpec.conds_inverse_of_fixed`, `conds_combined_of_fixed`); a hypothesis `hcp_ax` for an abstract law set | the per-law conditions, one pass over the rules |
| `hcc` | two active nodes with the same monomial share a class | assumed | hash-consing | tier 1; `debug_check_congruent_dup_invariant` exists as a debug check |
| `hS` | every asserted pair is two active nodes of one class | assumed | the input | none |
| `hcancel` | joinability cancels a common summand | limit | not an engine fact (`hcancel_not_derivable`, Section 5.7); `CompleteHyps` takes `hlat` (lattice closure) in its place, which `latticeClosed_of_engineFixed` derives from the fixpoint of `lattice_round` | tier 1, as lattice closure |

*Proof* (`CC/Assemble.lean:184-212`):

1. I5 holds of `st` (`reachable_I5`, `CC/Slot.lean:260`).
2. Each stored `rhs` is normal for `Rw L`: a step from it would go strictly down, and
   `nf_present` would put the normal form in the class, contradicting I5
   (`rhs_normal`, `Assemble.lean:113`). This step needs `h0` only at the two classes of the
   conclusion, which is why the weakened `I0Active` suffices.
3. Plain rewriting by the rules and law instances is confluent: Newman's lemma on a
   well-founded relation, with local confluence from `hcp` through the critical-pair lemma
   (`RwAx_confluent`, `Assemble.lean:41`; `newman`, `CC/Lemmas.lean:296`;
   `critical_pair_lemma`, `:270`).
4. Theory-equal monomials are joinable, by induction on `E` (`E_joinable_RwAx`,
   `Assemble.lean:53`). The `cancel` case is exactly `hcancel`.
5. Both nodes rewrite to their classes' right-hand sides, which are normal. Confluence makes
   the two right-hand sides equal. I0 gives a node with that monomial in each class, and
   `hcc` merges them.

The proof works with plain rewriting over rules and law instances, not with clamped rewriting
over rules alone: the `congr` case of the induction builds monomials that are not
clamp-normal, and those are not joinable under clamped rewriting (header of
`Assemble.lean`). `stub_counterexample` (`CC/Proofs/CriticalPairModulo.lean:202`) refutes the
formulation over clamped rewriting.

**Adequacy.**

- The minimal-monomial hypotheses `h5₀`, `hrun`, `ha` are equivalent to assuming I5:
  `OpsStar` is a reflexive transitive closure never linked to the inference run, so with
  `ss₀ = ss` the triple holds whenever some `SlotState` satisfies I5 and agrees with `st`.
  The engine content is that maintaining the minimal monomial preserves I5 (`reachable_I5`,
  Section 5.5). `AtomsWitness.witness_complete` (Section 5.9) discharges the triple with
  `ss₀ = ss` and the reflexive run, which confirms the reduction.
- The rule-rule part of `hcp` is derived from `RoundFixed` (`hcp_of_fixed`). The engine skips disjoint and containing pairs in its critical-pair loop
  (`egraph/src/egraph.rs`, `cc_round`): a disjoint pair is outside `Overlap` and is handled
  inside `critical_pair_lemma`; a containing pair does not exist at the fixpoint because the
  reducibility pass retired the containing node (`lhs_reduced`). The fixture
  `egraph/tests/egg/cc_containment_chain.egg` exercises two containing pairs that join only
  through that pass. `AxiomCP` is derived for every law set `LawSpec` names
  (`axiomCP_of_laws`): `CC/Laws/` reduces it, law by law, to conditions on the stored
  left-hand sides (`hu`, `hlhs`, `hax`, `hmatch`), `Laws/InvRulesMain.lean` derives the
  inverse ones from the fixpoints of R1 to R5, and the case analysis on the law set
  assembles them. For an abstract law set it stays a hypothesis of the bundles. The
  reducibility pass itself is the composition mint, joinMerge, retire of `Infer`, so
  soundness covers it without a further inference step.

**The critical pairs with a law instance.**

```lean
def AxiomCP (L : Laws n) (R : Rules n) : Prop := ...

theorem hcp_of_fixed {L : Laws n} {st : State n} (hfix : RoundFixed L st)
    (hax : AxiomCP L st.rules) :
    ∀ r₁ r₂, r₁ ∈ st.rules ∪ L.axRules → r₂ ∈ st.rules ∪ L.axRules → r₁ ≠ r₂ →
      Overlap r₁.1 r₂.1 →
      Joinable (Rw (plain n) (st.rules ∪ L.axRules))
        (criticalPair (plain n) r₁ r₂).1 (criticalPair (plain n) r₁ r₂).2
```

**Reading.** `AxiomCP L R` is the joinability of every critical pair in which at least one
side is a law instance (`L.axRules`). `hcp_of_fixed` says the fixed round supplies the rest:
with `RoundFixed` and `AxiomCP`, every overlapping pair of rules and law instances is
joinable under plain rewriting, which is the `hcp` above. For plain AC `AxiomCP` is vacuous
(`AxiomCP.of_no_ax`); for the law sets `LawSpec` names, `axiomCP_of_laws` (Section 5.6)
derives it from the fixed round and the per-law conditions. Outside: a law set the
development has no instance for, where `AxiomCP` stays a hypothesis.

### 5.4 Confluence and termination

`confluent_modulo` (`CC/Main.lean:30`) states that clamped rewriting is confluent when rules
and law instances are oriented, clamp produces law-normal forms, and every critical pair of
rules and law instances joins under plain rewriting. `run_stabilizes` (`CC/Main.lean:23`)
states that nodes and partition are eventually constant along any run; its proof uses only
that `Fin n` is finite and that a mint needs a fresh class, so it does not bound the engine's
rounds.

```lean
theorem kapur_termination (l : ℕ → Monomial n) (alive : ℕ → ℕ → Prop)
    (hself : ∀ i, alive i i)
    (hirr : ∀ i j, i < j → alive i j → ¬ l i ≤ l j)
    (hrem : ∀ i k, i < k → alive i (k - 1) → ¬ alive i k → l k ≤ l i ∧ l k ≠ l i) :
    False
```

**Reading.** `kapur_termination` (`CC/Lemmas.lean:492`) is about an abstract sequence of
left-hand sides `l i`, one per inference, with `alive i j` meaning rule `i` is still active
at time `j`. The hypotheses are the discipline of a reduced basis: a rule is alive when it is
added (`hself`), an added rule's left-hand side is not reducible by any rule alive at that
time (`hirr`), and a rule is retired only by a later rule whose left-hand side is strictly contained
in it (`hrem`, the collapse). The conclusion is `False`: no infinite such sequence exists, by
Dickson's lemma, so completion that keeps its basis reduced terminates. The theorem is not
connected to `Infer`: it says what the reducibility pass buys, not that `cc_round` performs
it. Outside: a bound on the number of rounds, the node and work budgets, and termination
with `a_round` interleaved. The engine's own evidence that collapse is needed is the
divergence of the no-collapse form on committed reproducers (design note
`06-ac-congruence-closure.md`, Section 6b).

### 5.5 The minimal monomial

The engine stores each class's minimal monomial and refreshes it when a member shrinks.
`CC/Slot.lean` models the operations that maintain it (`SlotState`).

```lean
theorem reachable_I5 {st₀ st : SlotState n} (h₀ : I5 st₀) (hrun : OpsStar st₀ st) : I5 st
```

**Reading.** `SlotState` is the per-class stored minimal monomial for one operator, together
with each class's active set. `Op` lists the engine's operations: mint,
merge with the two minima folded (`fold_min_monomial`), shrink with refresh
(`refresh_min_monomial`), retire when a smaller classmate exists, and un-retire with refresh
(`unretire`). From a good initial state (`h₀`) any run of these operations keeps I5. The
hypothesis is the operations' preconditions (a shrink goes strictly down, a merge joins
distinct classes); the engine supplies them. The proof is one case per operation (`op_I5`,
`:251`). `shrinkNoRefresh_breaks_I5` (`:290`) is a state in which a shrink without the refresh
breaks I5. Outside: that every engine step is one of the
operations, which is argued in prose, and the order keys, which `CC/MinMonoKey.lean` adds.

```lean
theorem unretire_refresh_I5 {st : State n} (h5 : I5 st) (M : Monomial n) (c : Fin n) :
    I5 { st.unretire M c with rhs := st.refreshRhs M c }

theorem unretireNoRefresh_breaks_I5 :
    I5 unretireBefore ∧ ¬ I5 (unretireBefore.unretireNoRefresh 5 {3, 1, 1})
```

**Reading.** The first theorem is on the completion state: clearing a node's collapsed flag
and then refreshing the class's right-hand side with the node's monomial (`refreshRhs`: the
class takes `M` when `M` is below its stored right-hand side) keeps I5, with no hypothesis
beyond I5 before. The second is a concrete state in which the same un-retire without the
refresh breaks I5: the stored minimal monomial stays on a node the next round collapses. It
is the state of `ac_reactivate_min_monomial.egg`, reduced from case 129 of the
`conform-cc-cert` corpus, in which `materialize` returns a collapsed node that is the normal
form of the class's own minimal monomial. The engine refreshes after clearing the flag in
both places.

**Pseudo-code: materialization, reactivation and the refresh.**

```
materialize(N):                                       -- cc_round, local `materialize`
  if N is {x}: return find x                          -- addNF, Normal::Single; add
  if N is empty and the operator has a unit u: return find u     -- addNF, Normal::Unit
  id := hash-cons lookup of the node f(N)             -- hcc
  if id is fresh:
    register node f(N) in a fresh class d             -- Infer.mint, SlotState.mint; register_if_fresh
    return d
  if id carries FLAG_AC_COLLAPSED and no current rule reduces N:   -- RoundFixed.nf_present
    clear the flag                                    -- Infer.unretire, SlotState.unretire
    rhs(find id) := min(rhs(find id), N)              -- State.refreshRhs; refresh_min_monomial
    count a change of the round                       -- "reactivation counts as a change"
  return find id
```

The engine runs the same refresh when recanonicalization changes a collapsed node's
monomial, in `recanonize_parent` and in the absorbed-uses sweep of `rebuild_congruence`, and
it clears the flag. After each congruence rebuild of the completion loop,
`unretire_irreducible_collapsed` does the same for every collapsed node that no current rule
of its operator reduces and that holds no inverse pair: a merge can reorient the rule that
collapsed it. The model states all three as `unretire` followed by `refreshRhs`
(`unretire_refresh_reachable`). Debug builds then check that every collapsed node is
reducible by a current rule or a law of its operator, or is a copy of an active node of its
class (`check_no_irreducible_collapsed`).

The engine orders monomials by per-class order keys, not by representative id
(`CC/MinMonoKey.lean`). At a merge every node's keyed monomial stays or shrinks
(`rename_key_le`, `survivor_key_le`), so each recanonicalization is a no-op or a shrink
(`merge_recanon_op`, `:201`). `keyed_reachable_I5` (`:211`) restates `reachable_I5`; the
content is in `merge_recanon_op`. `idOrder_grow_breaks_I5` (`:250`) shows that under the id
order a node grows past its classmate and I5 fails.

### 5.6 Laws and the inverse rules

`CC/Laws/Main.lean` instantiates the completeness theorem for each law set. The law
hypotheses `hlaw` and `hnf_ax` are discharged, and `hcp` is reduced to `RuleRuleCP`, which
the fixed round supplies (`ruleRuleCP_of_fixed`), and conditions on left-hand sides. For
`:inverse`, the reduction leaves four conditions, which the inverse rules R1 to R5
establish (below): `InvMatching`, `InvUnitFree`, `InverseAxiomCP` and
`NilpotentInverseCP`. The law sets are the five single laws and compositions `identity`,
`nilpotent`, `idempotent`, `inverse`, `combined` (identity, nilpotent, inverse) and the two
other compositions the engine accepts, `identityInverse` (identity, inverse) and
`idempotentIdentity` (identity, idempotent), all in `CC/Laws/Combined.lean` as normal-form
law sets.

```lean
theorem completion_complete_identity (u : Fin n) (cancel : Prop)
    {S : Set (Monomial n × Monomial n)} {st : State n} {ss₀ ss : SlotState n}
    (h5₀ : SlotState.I5 ss₀) (hrun : SlotState.OpsStar ss₀ ss) (ha : SlotState.Agrees st ss)
    (h0 : I0Active st) (hcanon : ∀ c, (Laws.identity u cancel).clamp (st.rhs c) = st.rhs c)
    (hfix : RoundFixed (Laws.identity u cancel) st)
    (hu : ∀ A B, (A, B) ∈ st.rules → u ∉ A)
    (hcc : ...) (hS : ...) (hcancel : cancel → ...)
    {M N : Monomial n} {c d : Fin n} (hM : (M, c) ∈ st.active) (hN : (N, d) ∈ st.active)
    (hMN : E (Laws.identity u cancel) S M N) : st.find c = st.find d
```

**Reading.** The seven law theorems (`completion_complete_identity`, `_nilpotent`,
`_idempotent`, `_inverse`, `_combined`, `_identityInverse`, `_idempotentIdentity`,
`CC/Laws/Main.lean`) are
`completion_complete_at_convergence` with the law hypotheses discharged and `hcp` reduced to
conditions on the stored rules, which the engine's clamp establishes: no left-hand side
holds the unit (`hu`); under `:nilpotent k` every count is below `k` (`hlhs`) and each rule's
pair with the clamp axiom joins (`hax`); under `:idempotent` every left-hand side is
duplicate-free; under `:inverse` the inverse map is injective and involutive
(`InvMatching`), left-hand sides hold no inverse pair (`InvNormal`), the rule-inverse pairs
join (`InverseAxiomCP`), and for the compositions with an inverse the unit is no inverse
(`InvUnitFree`) and, with a nilpotent order, the nilpotent-inverse pairs join
(`NilpotentInverseCP`). The `_engine` forms
(`completion_complete_inverse_engine`, `completion_complete_combined_engine`,
`completion_complete_identityInverse_engine`, `CC/Laws/InvRulesMain.lean`, `:350`, `:380`,
`:435`) derive the inverse conditions from the
fixpoints of the engine's rules R1 to R5 (`RoundFixedInv`, `RoundFixedInvUnit`,
`RoundFixedInvNil`; `invMatching_of_fixed`, `invUnitFree_of_fixed`,
`inverseAxiomCP_of_fixed`, `nilpotentInverseCP_of_fixed`) and the inverse nodes present
(`InvNodes`), and need I3. Every form takes `hcancel`; for a cancellative operator the
bundles use the lattice theorems of Section 5.7 instead. Outside: a law the development has
no instance for.

The engine applies the five inverse rules R1 to R5 in `inverse_law_repair`
(`egraph/src/egraph.rs:3361`). `CC/Laws/InvRules.lean` models them as inference steps;
`inv_rules_sound` (`:379`) extends soundness to them and requires a cancellative operator.

**Pseudo-code: axiom pairs and the per-law steps.**

```
axiom_pairs(rule A → B, L):                           -- AxiomCP, reduced per law in CC/Laws/
  if L idempotent: for a ∈ A: join(B + {a}, A)               -- hax (idempotent)
  if L nilpotent of order k: for a ∈ A with count m:
    join(B + a^(k−m), A without a)                          -- hax (nilpotent)
  if L has an inverse g:
    for a ∈ A with g(a) in class y: join(B + {y}, A − {a})   -- InverseAxiomCP, RoundFixedInv.r3_left
    for y ∈ A the class of g(x):    join(B + {x}, A − {y})   -- RoundFixedInv.r3_right
  if L cancellative:
    C := A ∩ B; join(A − C, B − C)                           -- CancelPair.c1, cancelClose_infer
    for every other rule A' → B': cancel-close (A + A', B + B')   -- (C2), disjoint superposition
inverse_rules(st):                                    -- inverse_law_repair
  R1: g(a) ~ g(c)  ⇒ merge(a, c);  g(g(x)) ⇒ merge(g(g(x)), x)   -- RoundFixedInv.r1_inj, r1_inv
  R2: g(x) ~ unit ⇒ merge(x, unit);  x ~ unit ⇒ merge(g(x), unit) -- RoundFixedInvUnit
  R3: the two rule-inverse pairs above, materialized and merged  -- r3_left, r3_right
  R4: g(x) in class y ⇒ merge(materialize(x^(k−1)), y)           -- RoundFixedInvNil.r4
  R5: g(x) in class y ≠ x ⇒ merge(materialize(y^(k−1)), x)       -- RoundFixedInvNil.r5
```

Each `join(P, Q)` normalizes both sides and merges their classes. The model states the
fixpoints (`RoundFixedInv`, `RoundFixedInvUnit`, `RoundFixedInvNil`) and derives the four
inverse conditions from them; the engine generates the pairs for touched rules in
intermediate rounds and for every rule in the full round.

**Adequacy.** The three `_engine` theorems take `hcancel`, `hcc`, `hS`, the minimal-monomial
hypotheses, `I3` and conditions on left-hand sides, and with the cancellative operator
`inv_rules_sound` requires, `hcancel` is the hypothesis Section 5.7 shows the engine does not
establish; the `_atoms` forms of Section 5.9 and the bundles take lattice closure in its
place.

**`AxiomCP` from the per-law conditions** (`CC/Laws/AxiomCP.lean`). `LawSpec n` enumerates
the law sets the model names, with their parameters: `plain`, `identity u cancel`,
`nilpotent k hk cancel`, `idempotent cancel`, `inverse inv cancel`,
`combined u k hk inv cancel hu`, `identityInverse u inv cancel hu` and
`idempotentIdentity u cancel`; `LawSpec.laws` is the `Laws` of each, and `LawSpec.Conds R`
the conjunction of the per-law conditions above on the rule set `R` (`IdentityConds`: no
left-hand side holds the unit; `NilpotentConds` and `IdempotentConds`: `hlhs` and `hax`;
`InverseConds`: `InvMatching`, `InvNormal` left-hand sides, `InverseAxiomCP`;
`CombinedConds`: the three together with `NilpotentInverseCP`; `IdentityInverseConds` and
`IdempotentIdentityConds`: the conditions of the two laws composed).

```lean
theorem axiomCP_of_laws (sp : LawSpec n) {st : State n} (hfix : RoundFixed sp.laws st)
    (hc : sp.Conds st.rules) : AxiomCP sp.laws st.rules

theorem LawSpec.hcp (sp : LawSpec n) {R : Rules n} (hor : Oriented R)
    (hRR : RuleRuleCP sp.laws R) (hc : sp.Conds R) : HCP sp.laws R

theorem CompleteHyps.ofLaws (sp : LawSpec n) ... (hfix : RoundFixed sp.laws st)
    (hc : sp.Conds st.rules) ... : CompleteHyps sp.laws S st

theorem CompleteAtoms.ofLaws (sp : LawSpec n) ... (hfix : RoundFixedA sp.laws st A u)
    (hc : sp.Conds (st.withAtoms A u).rules) ... : CompleteAtoms sp.laws S st A u
```

**Reading.** For every law set `LawSpec` names, a `RoundFixed` state whose rules satisfy the
law's conditions joins every critical pair that involves a law instance. The proof is one
case per law set: the fixed round gives the rule-rule pairs (`ruleRuleCP_of_fixed`), the
theorem of `CC/Laws/CriticalPairs.lean` for that law (`hcp_identity`, `hcp_nilpotent`,
`hcp_idempotent`, `hcp_inverse`, `hcp_combined`, which handles the pairwise interactions of
the combined laws: unit against nilpotent, unit against inverse, nilpotent against inverse;
`hcp_identityInverse`, the same without the nilpotent cases; `hcp_idempotentIdentity`, where
the unit generator and an idempotent generator never overlap)
gives the whole `HCP`, and `AxiomCP` is its law part (`AxiomCP.of_hcp`); for plain AC every
pair is a rule-rule pair. `LawSpec.hlaw` and `LawSpec.hnf_ax` discharge the two law
hypotheses the same way. `CompleteHyps.ofLaws` (`CC/Bridge/Modulo.lean`) and
`CompleteAtoms.ofLaws` (`CC/AtomsEngine.lean`) build the bundles from the engine-side
hypotheses and `LawSpec.Conds` in place of `hcp_ax`, `hlaw` and `hnf_ax`; the existing
fields and theorems are unchanged, and `AtomsWitness.witness_complete` goes through
`CompleteAtoms.ofLaws` at `LawSpec.plain`. The inverse conditions are what the fixpoints of
R1 to R5 establish: `LawSpec.conds_inverse_of_fixed`, `conds_identityInverse_of_fixed` and
`conds_combined_of_fixed` assemble `Conds` from `RoundFixedInv`, `RoundFixedInvUnit`,
`RoundFixedInvNil`, `InvNodes`, `I3` and `Converged`, as the `_engine` theorems do.

The engine accepts, on an AC operator, the tag sets plain, `:identity`, `:idempotent`,
`:idempotent :identity`, `:identity :nilpotent k`, `:identity :inverse` and
`:identity :nilpotent k :inverse` (`egraph/src/sortcheck.rs`: `:nilpotent` and `:inverse`
require `:identity`; `:idempotent` excludes `:nilpotent`, `:inverse` and `:cancellative`).
Every accepted tag set has a `Laws` instance and a `LawSpec` case: plain, `:identity`,
`:idempotent`, `:idempotent :identity` (`idempotentIdentity`), `:identity :nilpotent k`
(`LawSpec.identityNilpotent`, which is `combined` with the empty inverse: its inverse
conditions are vacuous), `:identity :inverse` (`identityInverse`) and
`:identity :nilpotent k :inverse` (`combined`); `nilpotent` and `inverse` alone are the
model's law sets with no engine tag set. The two compositions with an inverse are normal-form
law sets under `InvUnitFree`, which R2 supplies (`invUnitFree_of_fixed`); the composition
with the idempotent law leaves out the idempotent generator at the unit, `{u, u} → {u}`,
which is not an instance of the composite normal form and which `{u} → ∅` derives. Outside:
the conditions `hlhs` and `hax` of the nilpotent and idempotent laws and `hu` of the identity
law, which are stated on the rules and not derived from a fixpoint structure as the inverse
ones are.

### 5.7 The lattice round

Kapur's inferences alone do not establish `hcancel`. On the fixture `cancel_lattice.egg`
the inferences alone converge without the equation `C5 = c1c3²`, which needs `c1c4² = c0²` and two copies of
`c4 = c0c3`. The engine therefore runs `lattice_round` at the completion fixpoint: classes
whose count vectors differ by a member of the lattice spanned by the equations are merged.

`CC/Lattice.lean` formalizes the argument. A monomial's count vector is `vec M : Fin n → ℤ`.
`E_mem_lattice` (`:125`) shows theory-equal monomials differ by a lattice vector, for every
law set. `E_of_mem_lattice` and `E_iff_mem_lattice` (`:213`, `:218`) give the converse when the
theory is closed under cancellation (`CancelClosed`, from `cancelClosed_of_cancellative` or
`cancelClosed_of_nil`). `combined_E_iff` (`:272`) identifies, for the identity, nilpotent and
inverse laws, the lattice with the one spanned by the vectors `lattice_round` builds.
`stateLattice_eq_closure` (`:336`) shows the model's lattice is the span of the engine's
vectors (`engineRows`; `nodeEqs`: a class equals its node's monomial; `classEqs`:
classmates), and `engine_merge_E` (`:393`) shows each such merge is a theory consequence
under `FlatSound` (`:447`). `lattice_merge_sound` (`:500`) shows a lattice merge is a theory
consequence and preserves I2.

```lean
def LatticeClosed (L : Laws n) (st : State n) : Prop :=
  ∀ M c N d, (M, c) ∈ st.active → (N, d) ∈ st.active →
    vec M - vec N ∈ stateLattice L st → st.find c = st.find d

theorem latticeClosed_of_engineFixed {L : Laws n} {st : State n} (h : EngineFixed L st) :
    LatticeClosed L st

theorem completion_complete_cancellative_engine {L : Laws n} ...
    (h5₀ : ...) (hrun : ...) (ha : ...) (h0 : I0Active st) (hcanon : ...) (hfix : RoundFixed L st)
    (hlaw : ...) (hnf_ax : ...) (hcp : ...) (hcc : ...) (hS : ...)
    (hlat : L.cancellative → LatticeClosed L st)
    {M N : Monomial n} {c d : Fin n} (hM : (M, c) ∈ st.active) (hN : (N, d) ∈ st.active)
    (hMN : E L S M N) : st.find c = st.find d
```

**Reading.** `LatticeClosed` says that two active nodes whose count vectors differ by a
member of the lattice spanned by the state's equations are in one class. `EngineFixed` is
the fixpoint of `lattice_round` as the engine computes it, over the vectors it builds (one
per node, one per pair of classmates); `latticeClosed_of_engineFixed` (`:531`) says that
fixpoint gives `LatticeClosed`, with no further hypothesis.
`completion_complete_cancellative_engine` (`:565`) is the completeness theorem with
`hcancel` replaced by `hlat`: for a cancellative operator the conclusion comes from lattice
closure alone (`complete_of_latticeClosed`), and otherwise `hcancel` is vacuous. The engine
supplies `hlat` by running `lattice_round` whenever a full round finds nothing and reopening
completion after each of its merges. The soundness of those merges is
`lattice_merge_sound`, under `FlatSound` (every node and classmate equation holds in the
theory), which no theorem derives from the engine's steps. Outside: the echelon form and
coset representatives the engine computes, modelled as lattice membership only.

```lean
theorem hcancel_not_derivable :
    (cancelAC 4).cancellative ∧ RoundFixed (cancelAC 4) cexState ∧ I0Active cexState ∧
      I5 cexState ∧ ... ∧ LatticeClosed (cancelAC 4) cexState ∧ EngineFixed (cancelAC 4) cexState ∧
      ... ∧
      ¬ (∀ M N X : Monomial 4,
        Joinable (Rw (plain 4) (cexState.rules ∪ (cancelAC 4).axRules)) (M + X) (N + X) →
        Joinable (Rw (plain 4) (cexState.rules ∪ (cancelAC 4).axRules)) M N)
```

**Reading.** A concrete four-class cancellative state (`:725`) that satisfies every
hypothesis of the completeness theorem, is lattice-closed and is a fixpoint of
`lattice_round`, and in which `hcancel` fails: two sums with a common summand are joinable
while the summands' remainders rewrite to distinct normal forms. The reason is the
quantifier: `hcancel` ranges over every monomial, lattice closure over the nodes present. So
`hcancel` is not an engine fact; lattice closure is the right hypothesis, and it suffices.

**Adequacy.** The lattice is that of the extended theory, which reads each class id as the
term its node holds (`nodeEqs`, `classEqs`); that reading agrees with the core theory only
under `FlatSound`, which is not shown invariant under `Infer`. In the cancellative branch of
`completion_complete_cancellative_engine`, the proof uses only `LatticeClosed` and `hS`. The
variant with leaf constants, `completion_complete_cancellative_engine_atoms`, is in
Section 5.9.

**Pseudo-code: the completion loop, the confirmation round and the lattice round.**

```
rebuild():                                            -- EnginePhase; egraph.rs rebuild
  full := true                                        -- round 0 inspects every pair
  loop:
    rebuild_congruence()                              -- EnginePhase.cong; rebuild_congruence
    if node growth or work past its budget: outcome := abortedGrowthLimit | abortedWorkLimit; return
    if a width error: outcome := abortedOverflow; return      -- CompletionOutcome
    if the lazy goal is met: outcome := goalMet; return
    changed := cc_round(full) | a_round() | canon_repair_round()   -- Completion.step; 11.1
    if changed: full := false; continue              -- incremental rounds while progress
    if not full: full := true; continue              -- confirm with a full round
    if lattice_round(): full := false; continue      -- EngineFixed, LatticeClosed; lattice_round
    outcome := converged                              -- CompletionRun.converged: K.step S' = none
    return
```

`Converged` is reported only after a full round over every pair, with its reducibility pass,
finds nothing and `lattice_round` merges nothing. The model's `Completion.step` abstracts
the whole pass as one step function, so the incremental rounds and the touched delta are not
modelled, and the fixpoint `K.step S' = none` is the full round's verdict.

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

**Adequacy.** Recanonicalization by rebuild, the one-element collapse in `add`, and
termination of `a_round` interleaved with AC rounds are not modelled.

**Documented limit: completion modulo associativity alone.** `ARound/` has no completeness
theorem. `a_round` closes one gap (two spellings of a merged class inside other sequence
nodes) and does not chase critical pairs. The design note (`06-ac-congruence-closure.md`,
Section 14) states why none is sought: ground completion modulo associativity alone is
completion of a string rewriting system, a presentation of a finitely presented monoid, and
the word problem for such monoids is undecidable (Markov, Post). So the development proves
soundness of the step (`aRound_sound`, `aRoundH_sound`), uniqueness and reachability of the
least spelling (`isLeastSpelling_unique`, `firstRule_complete`) and termination of one round
over a finite node set (`aRoundH_wf`), and the runtime design note establishes, for `:assoc`
operators, matching completeness relative to the classes present and nothing about
completion.

`CC/Countermodel.lean` gives the semantic side of `E`. `E_sound` (`:58`) states that
theory-equal monomials have equal value in every commutative-monoid model of the asserted
pairs and laws (cancellative if the operator is). `not_E_of_separates` (`:73`) follows: a
model that separates two monomials certifies that they are not theory-equal. The generator
`semper-conform-cc-cert` emits `check-neq` only on pairs such a model separates, so a failing
`check-neq` there is an engine unsoundness.

### 5.9 Leaf constants

**Problem.** In `(union (+ a b) c)` the classes `a`, `b` and `c` hold no `+`-node and occur
in monomials only as summands, yet the equation relates the monomial `{a, b}` to the class
`c`. The engine identifies the one-element monomial `{x}` with the class `x` everywhere:
`nary_canon::normalize` returns `Normal::Single(x)` for a single child of count 1 and `add`
returns `x`'s class without building a node; recanonicalization that leaves a stored node
with one child records the pair (node, child) as a merge (`degeneracy_pair`); and
`class_rhs_into` gives an atomic class the right-hand side `{find c}`, which no stored node
spells. The empty monomial is identified the same way with the class of the operator's unit
(`Normal::Unit`).

**Definitions** (`CC/Atoms.lean`). `A : Set (Fin n)` is a set of atomic classes (in the
engine, every class referenced as a child) and `u : Option (Fin n)` the unit class.

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
`RoundFixedA.materialized` (`:201`): a stored active node whose monomial is an implicit
node's, such as a one-element node `({x}, c)` the engine keeps until the degeneracy merge, is
in the implicit node's class at a fixed round (the `degeneracy_pair` merge, derived).
`RoundFixedA.congr` (`:220`) concludes, because no two implicit nodes share a monomial
(`atomNodes_func`, `:73`).

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

**Reading.** The theorem of Section 5.3 read on the completion view `st.withAtoms A u`,
which adds `{x}` as an active node of each atomic class `x ∈ A` and the empty monomial as a
node of the unit `u`. The engine-side hypotheses are stated on the view: `h0` says an atomic class has `{x}` as
right-hand side (`class_rhs_into`), `hfix` adds the one-element collapse to the fixed round,
`hS` lets an asserted equation relate a node to a constant, and `hcp` and `hcancel` range
over the view's rules, which include `M → {x}`. `hcc` is on the stored nodes only, and
`RoundFixedA.congr` lifts it. The conclusion covers a stored node, an atomic class and the
unit alike: any two of them that are theory-equal are in one class. The proof applies
`completion_complete_at_convergence` to the view, with `hfix.roundFixed` and
`hfix.congr hcc`. `CompleteAtoms` (`:277`) packages the hypotheses with `hlat` in place of
`hcancel` and `AxiomCP` in place of the law part of `hcp`, which `CompleteAtoms.ofLaws`
derives from the per-law conditions for the law sets `LawSpec` names (Section 5.6); its
corollaries name the cases:
`nodes` (two stored nodes), `atom_class` (`:317`, a node theory-equal to `{x}` is in `x`'s
class), `atoms`, `unit_class` and `materialized`. Outside: a class that holds an `f`-node and
another operator's node and is no child, which the engine marks atomic and the model's store
does not see.

| Hypothesis | Stated on | Class | Source | Runtime check |
|---|---|---|---|---|
| `h5₀`, `hrun`, `ha` | the view | assumed | equivalent to assuming I5 of the view | tier 1, as I5 |
| `h0` | the view | assumed | an atomic class's `rhs` is `{x}` (`class_rhs_into`) | tier 1, "a class with none is a leaf whose normal form is `{c}`" |
| `hcanon` | the stored `rhs` | assumed | the output of `nary_canon` | tier 1 |
| `hfix` (`RoundFixedA`) | the view, plus the collapse | assumed; the collapse derived at `A := atomicOf st` | the confirmation round; `atomCollapse_of_addFixed` derives the collapse from `AddFixed`, a hypothesis on the normalize pass | tier 2, as `nf_present` and `cp_joinable` |
| `hcp` | the view's rules, which include `M → {x}` | rule-rule part derived from `RoundFixedA`; law part derived for the law sets `LawSpec` names, assumed for an abstract law set | `hcp_of_fixed` at `hfix.roundFixed`; `CompleteAtoms.ofLaws` takes `LawSpec.Conds` on the view's rules and `axiomCP_of_laws` supplies `hcp_ax` | tier 2, the per-law conditions over the view's rules |
| `hcc` | the stored active nodes | assumed | hash-consing | tier 1 |
| `hS` | the view: an asserted pair may relate a node to a constant | assumed | the input | none |
| `hcancel` | the view's rules | limit | not an engine fact (Section 5.7); `CompleteAtoms` takes `hlat : L.cancellative → LatticeClosed L (st.withAtoms A u)` in its place | tier 1, as lattice closure |
| `A` | a parameter; the `_atomic` corollaries take `atomicOf st` (`CC/AtomicOf.lean`), the set the `atomic` bit defines on the store of one operator | derived for the model's store, assumed for the bit | a child of a stored node (`add_use`) or a class with no `f`-node (`register_if_fresh`); a class holding an `f`-node and another operator's node, never a child, is outside the model's store | tier 1, "the bit is set iff `atomicOf`"; the five `atomic_bit_*.egg` fixtures probe the transitions |

`CC/AtomsEngine.lean` restates the engine-level theorems on the view:
`completion_complete_cancellative_engine_atoms` (`:62`, `LatticeClosed` of the view in place
of `hcancel`), `completion_complete_inverse_engine_atoms` (`:85`),
`completion_complete_combined_engine_atoms` (`:112`, the unit as the implicit node
`(∅, u)`) and `completion_complete_identityInverse_engine_atoms` (`:157`). `I3_withAtoms`
(`:37`) carries the retirement invariant to the view, and
`invNodes_withAtoms` (`:50`) derives the one-element nodes the inverse rules R1 to R5 are
stated on from the implicit nodes, when every class a `g`-node touches is atomic.

**The bit and `add`** (`CC/AtomicOf.lean`). The engine keeps one `atomic` bit per class, set
and never cleared: `add_use` (`containers/src/eclasses.rs`) sets it on every child of a
fresh node, `register_if_fresh` (`egraph.rs`) on the class of a fresh node whose operator has
no completion column, and `fold_min_monomial` ORs the two bits at a merge.

```lean
def State.HoldsNode (st : State n) (c : Fin n) : Prop := ∃ p ∈ st.nodes, st.find p.2 = st.find c
def State.IsChild (st : State n) (c : Fin n) : Prop :=
  ∃ p ∈ st.nodes, ∃ x ∈ p.1, st.find x = st.find c
def atomicOf (st : State n) : Set (Fin n) := {c | st.IsChild c ∨ ¬ st.HoldsNode c}

def AtomCollapse (L : Laws n) (st : State n) (A : Set (Fin n)) (u : Option (Fin n)) : Prop :=
  ∀ M c N x, (M, c) ∈ (st.withAtoms A u).active → (N, x) ∈ atomNodes A u →
    ReflTransGen (Rw L (st.withAtoms A u).rules) M N →
    (∀ P, ¬ Rw L (st.withAtoms A u).rules N P) → st.find x = st.find c

def AddFixed (L : Laws n) (A : Set (Fin n)) (u : Option (Fin n)) (st : State n) : Prop :=
  ∀ st', ¬ AddStep L A u st st'

theorem completion_complete_atomic {L : Laws n} ... {u : Option (Fin n)} ...
    (hfix : RoundFixed L (st.withAtoms (atomicOf st) u)) (hadd : AddFixed L (atomicOf st) u st)
    ... (hMN : E L S M N) : st.find c = st.find d
```

**Reading.** `atomicOf st` is the engine's `atomic` bit as the store of one operator shows
it: a child of a stored node, active or retired (a retired node keeps its uses), or a class
with no `f`-node. A class that holds both an `f`-node and another operator's node and is no
child is atomic in the engine and not in `atomicOf st`; the parametric theorems cover it
with any `A ⊇ atomicOf st`. `child_mem_atomicOf` is the tier 1 check "no `f`-node has a
non-atomic `f`-child", by definition. `addNF st u N` is `add` on a degenerate normal form:
`some (find x)` for `{x}` (`Normal::Single`), `u.map find` for `∅` (`Normal::Unit`), `none`
when a node is built. `AddStep L A u` is the normalize step with `add` so modelled: an
active node of the view whose normal form `addNF` sends to a class is merged into it
(`AddStep.find_changed`: the step is not idle under an idempotent `find`). At the fixpoint
`AddFixed` the collapse holds (`atomCollapse_of_addFixed`), and `roundFixedA_of_addFixed`
gives `RoundFixedA` from `RoundFixed` of the view. `completion_complete_atomic` restates
`completion_complete_atoms` at `A := atomicOf st` with `RoundFixed` of the view and
`AddFixed` in place of `RoundFixedA`: the collapse is derived. `CompleteAtomic L S st u` is
`CompleteAtoms` at that `A`, with the corollaries `child_class` and `leaf_class`;
`Final/Store.lean` has `saturation_modulo_complete_store_atomic`, and the witnesses
discharge it: `witness_atomicOf : atomicOf wst = wA` (by `fin_cases` and `decide`),
`witness_complete_atomic`, `witness_saturation_modulo_complete_atomic`. Assumed: `AddFixed`,
a hypothesis on the normalize pass of the same kind as `RoundFixed`, and that the bit the
engine keeps equals `atomicOf` on every class the store shows; the five fixtures
`atomic_bit_*.egg` probe the bit's transitions against the bounded oracle.

**Pseudo-code: the one-element collapse in `add`.**

```
add_step(st, L, A, u):                                -- AddStep.collapse; nary_canon::normalize, add
  for (M, c) active in the view st.withAtoms A u:
    N := normal form of M under the view's rules      -- Rw L (withAtoms).rules
    match addNF(N):                                   -- addNF
      {x}  ⇒ x' := find x                             -- Normal::Single(x) => find(x)
      ∅    ⇒ x' := find u                             -- Normal::Unit
      else ⇒ continue                                 -- a node is built, 11.2
    if find c ≠ x': merge(c, x')                      -- AddStep → st.merge c x'
  fixpoint when no step applies                       -- AddFixed
```

The engine performs the collapse inside `add` (a degenerate normal form returns the class and
builds no node) and at rebuild (`degeneracy_pair` merges a stored node left with one child
into that child); the model states the fixpoint `AddFixed` and derives `AtomCollapse` from it.

**Non-vacuity.** `CC/AtomsWitness.lean` takes the program

```
(union (+ a b) c)
(let t (+ a b d))
(let u (+ c d))
```

over plain AC at its completion fixpoint: classes `a, b, c, d = 0, …, 3` are leaf constants,
the stored nodes are `{a, b}` in `c`'s class and `{a, b, d}`, `{c, d}` in class 4, and every
atom's right-hand side is its one-element monomial. The node `{a, b, d}` is retired, as the
engine's reducibility pass leaves it (its left-hand side contains `{a, b}`; with it active
the state would hold a containing pair, which `lhs_reduced` rejects). The view has one rule.

```lean
theorem witness_complete : CompleteAtoms (Laws.plainAC 5) wS wst wA none
```

**Reading.** A concrete state (five classes, plain AC, no unit) satisfies every hypothesis
of `CompleteAtoms` at once, with the asserted equation `{a, b} = {c}` between a stored node
and a leaf constant; the parametric theorems alone do not show the hypotheses jointly
satisfiable. The bundle is built through `CompleteAtoms.ofLaws` at `LawSpec.plain`, whose
per-law conditions are empty. `witness_I3` checks that the retired node rewrites to a node of its class.
`witness_not_all` shows that `I0ActiveAll` fails on the stored state, so a completeness
theorem over `I0ActiveAll` applies to no state with a leaf constant. The
witness also establishes the reduction of the minimal-monomial triple to I5: it takes
`ss₀ = ss` and the reflexive run. What it does not establish is a non-trivial merge: with
`{a, b, d}` retired, the only active node theory-equal to `{c, d}` is itself.

**Adequacy.** The witness is plain AC: it does not exercise the unit, the laws, `hcancel`
(vacuous for a non-cancellative operator) or a non-trivial minimal-monomial history
(`ss₀ = ss`). Its closing `example` derives `wst.find 2 = wst.find 2`, which holds by
reflexivity; it shows that the corollaries apply, not that they derive a merge the state
lacks. A witness with two active, mutually irreducible, theory-equal nodes needs a
superposition (two rules whose left-hand sides overlap without containment) and is not
written. No theorem relates `AddStep` to `Infer`, whose `mint` step builds a node in a fresh
class. The docstring of `CC/Atoms.lean` (`:53`) names `completion_complete_atom_class`,
which does not exist; the theorem is `CompleteAtoms.atom_class`.

## 6. Rounds and saturation

### 6.1 Rounds

A **round** (`Round`, `EMatch/Engine/Rounds/Round.lean:40`) is one transition of the
semi-naive loop as the matcher sees it: the index snapshot of round r-1 (`before`), the
snapshot of round r after its actions and rebuild (`after`), and the engine's logs between
the two index builds (the added ids, the recorded unions, the subsumed ids, the touched log,
and the merge-membership delta). A node is new (`isNew`) when it is in the touched log or the
merge delta.

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

Each field is an assumption about an engine operation: a fresh id is logged at registration
(`register_if_fresh`); recanonicalization logs an id when its stored children change
(`egraph/src/caches.rs:541-547`); a merge pushes the absorbed class's members when tracking
is on (`merge_in_classes`); the union-find only merges; rebuild precedes the index build, so
children are canonical; hash-cons collisions merge, so equal nodes share a class.
Section 6.4 notes the one partial derivation (`dedup`).

### 6.2 The delta

**`delta_complete`** (`EMatch/Engine/Rounds/Delta.lean:41`):

```lean
theorem delta_complete {R : Round} (hwf : R.WF) (htr : R.tracking = true)
    {atoms : List QAtom} {σ' : Binding}
    (hafter : Matches R.after atoms σ') (hbefore : ¬ Matches R.before atoms σ') :
    ∃ (k : Nat) (ak : RAtom), atoms[k]? = some (.scan ak) ∧
      ∃ id, σ'.node ak.node = some id ∧ R.isNew id = true
```

**Reading.** `hwf : Round.WF` is what rebuild guarantees (Section 6.1), assumptions about
`register_if_fresh`, `recanonize_node`, `merge_in_classes` and the hash-cons. `htr` says
merge tracking is on, which `saturate_rules_semi` ensures. The conclusion is the cross-round
half of semi-naive completeness: a binding that matches after the round and not before
binds some scanning atom to a node the round logged as new, so some variant finds it. The
proof is by contraposition: a present node that is not new existed before with the same
stored node and representative (`Round.stable_of_not_new`, `Round.lean:134`), a shallow
pattern reads the graph only through the node itself (`matchN_shallow_iff`,
`AtomDelta.lean:31`), and `Eq` atoms do not read the graph, so each atom satisfied after is
satisfied before. Two counter-models below show that tracking and the absence of globals
are both needed. Outside: rules with `Eq` atoms against a global, which the engine routes
naive, and `:flatten` rules, which match naive every round (`needs_naive_match`).

**`semi_naive_round_complete`** (`EMatch/Engine/Rounds/Complete.lean:30`) combines
`delta_complete` with `variants_cover_new`:

```lean
theorem semi_naive_round_complete {R : Round} (hwf : R.WF) (htr : R.tracking = true)
    {sig : Sym → Kind} {atoms : List QAtom} {ap : APlan}
    (hwf₀ : AtomsWF R.before sig atoms) (hwf₁ : AtomsWF R.after sig atoms)
    (h : SchedA atoms ∅ ∅ ap) {σ' : Binding}
    (hnew : σ' ∈ runNaive R.after ap) (hold : σ' ∉ runNaive R.before ap) :
    ∃ (k : Nat) (ak : RAtom), atoms[k]? = some (.scan ak) ∧
      σ' ∈ runVariant R.after R.isNew k ap
```

**Reading.** With the round well formed and tracked, the query well formed on both snapshots
and a static plan, every naive match of the new snapshot that is not a naive match of the
old one is emitted by some variant `k` on the new snapshot, namely the one of its first new
atom. This is the theorem the saturation invariant uses for a tracked rule;
`MatcherOK.round_complete` is the same statement on a matcher, so the adaptive scheduler is
covered too. `semi_naive_complete` extends it to a chain of rounds: a naive match of the
final snapshot is a match of the first one or is emitted by a variant of some round.
Outside: the routing decision itself (which rules run tracked), which `route` in Section 6.4
models as a parameter.

Two counter-models show the hypotheses are needed. `delta_incomplete_untracked`
(`Rounds/Counter.lean:184`) is a well-formed round without tracking in which a new match has
no new scanning node: a merge whose survivor is the id the parent already stores. That is
why the merge-membership delta exists. `delta_incomplete_global` (`:98`) is a well-formed
tracked round in which a rule constrains a class variable to a global's class; the absorbed
class's members enter the delta, but no atom scans them. The engine routes such rules to
naive matching (`needs_naive_match`).

**Pseudo-code: semi-naive rounds, variants and routing.**

```
round r (r ≥ 1):                                      -- Round, ActRound; saturate.rs saturate_rules_semi
  new(id) := id ∈ touched ∨ id ∈ mergeDelta           -- Round.isNew; touched log, merge_in_classes
  resp := spelling_epoch moved and completion off     -- route; respelled
  for rule in rules:
    if naive(rule) or (resp and rule builds an n-ary term):      -- route naive resp
      run rule on the whole index                     -- runNaive; needs_naive_match, VariantIndex::naive
    else for k in scanning atoms of rule:             -- variants_cover_new
      run variant k: atom k in the delta, atoms < k in full minus delta, atoms > k in full   -- variantMode k
  apply every emitted binding's actions               -- ActRound, Fired; apply.rs
  rebuild()                                           -- 11.3, 11.6
```

`naive(rule)` is the engine's static routing (`needs_naive_match`: `:flatten` rules, rules
with a global, `Eq` against a global); the model takes it as a free parameter.

### 6.3 Actions and their consequences

A rule (`Rule`, `EMatch/Engine/Saturate/Actions.lean:117`) is a list of query atoms, an
annotated plan, and a list of actions: `insert t`, `union a b`, or `subsume x`. A rewrite
`L => R` is `[union (var root) R]`, plus `subsume root` under `:subsume`.

`Den G σ t c` (`Actions.lean:62`) states that the right-hand-side term `t` is present in `G`
under `σ` with value `c`: a variable denotes its bound class, an application the class of a
stored node whose children are literally the values of its subterms.

```lean
def ActFired (G : Graph) (σ : Binding) : Action → Prop
  | .insert t => ∃ c, Den G σ t c
  | .union a b => ∃ c, Den G σ a c ∧ Den G σ b c
  | .subsume _ => True

def Fired (G : Graph) (σ : Binding) (rule : Rule) : Prop :=
  ∀ act ∈ rule.actions, ActFired G σ act
```

For a rewrite, `Fired` says `R` is present in the class of the matched root.

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

**`inv_step`** (`Saturate/Invariant.lean:85`) carries `InvLag` from round r-1 to round r. A
match on `A.R.before = prev.R.after` either holds before the previous round, so the
previous invariant fired it and `fired_transport'` (`Saturate/Transport.lean:342`) keeps it
fired across a round without subsumption, or is new, so a naive-routed rule emits it
directly, a tracked rule emits it from a variant (`semi_naive_round_complete`), and the
round's actions fire it (`fired_after_actions`, `ActRound.lean:51`).

```lean
theorem inv_step {sig : Sym → Kind} {naive : Rule → Bool} {rules : List Rule}
    {prev A : ActRound} (hlink : A.R.before = prev.R.after)
    (hprev : prev.R.WF) (htr : prev.R.tracking = true)
    (hA : A.R.WF) (hAf : A.R.PersistFixed) (hsub : A.R.subsumed = ∅)
    (hatoms₀ : RulesWF sig prev.R.before rules) (hatoms₁ : RulesWF sig prev.R.after rules)
    (hmatch : MatchersOK rules) {resp : Bool} (hresp : ¬ prev.R.Persist → resp = true)
    (hemit : EmitsRound (route naive resp) prev.R A rules)
    (hinv : InvLagL prev rules) : InvLagL A rules
```

**Reading.** Two consecutive rounds. The hypotheses on the engine: both rounds well formed,
tracking on, the fixed-arity nodes of round `A` persisting literally (`PersistFixed`), no
subsumption, the rules' atoms well formed, each rule's matcher correct (`hmatch`, a theorem
for the adaptive scheduler), and the routing: if the previous rebuild is not literal
(`¬ prev.R.Persist`: a unit drop, a clamp or a collapse happened), the flag `resp` is set and
`route naive resp` sends the rules that build an n-ary term to the naive matcher. `hemit`
says every binding the routed matcher emits on the previous snapshot is applied in round
`A`. The conclusion carries the guarded invariant `InvLagL` one round forward. The routing
hypothesis is what the engine's `respelled` re-match implements through `spelling_epoch`.

`fired_transport` needs `Round.Persist` (`Transport.lean:45`): every non-subsumed node of
`before` survives in `after` with the same operator and its children mapped through the new
`find`. It also needs no subsumption, because a `:subsume` can remove from the index a node a
consequence is built of (`tests/egg/subsume.egg`). `Persist` is not a per-round
hypothesis. `recanonize_node` maps the children of a tuple, pair or
sequence node through `find` and nothing else; `Round.PersistFixed` states it for the tuple
and pair nodes (`isVariadic` is true of a sequence; `LiteralSeq`, `Fidelity/RecanonComplete.lean`,
states the sequence case) and every round assumes it; for a multiset or set node it also drops the unit's class and clamps the
counts, and a result of one element or none merges the node's class with a leaf
(`degeneracy_pair`). The invariant is therefore guarded (`InvLagL`): a rule whose actions
build an n-ary term (`Rule.buildsNary`) is fired at a round only if that round's rebuild
persisted every node literally (`Round.Persist`), and a rule that builds none is transported
through the fixed-arity nodes alone (`fired_transport_fixed'`). The guard is discharged at
the fixpoint, where a round that changed nothing is literal (`Round.persist_of_unchanged`),
and across the chain by the routing of `AChain` (`route naive resp`, `resp = true`), which
re-emits every old match: the engine's `respelled` re-match (`saturate.rs`), which fires
after a rebuild applied a law to a stored node (`VarCanon::law_applied`, counted in
`spelling_epoch`).

**`saturation_complete`** (`Saturate/Invariant.lean:231`):

```lean
theorem saturation_complete {sig : Sym → Kind} {naive : Rule → Bool} {rules : List Rule}
    (A₀ : ActRound) (As : List ActRound) (hmatch : MatchersOK rules)
    (h₀ : RulesWF sig A₀.R.before rules) (hok : ∀ A ∈ A₀ :: As, RoundOK sig rules A)
    (hemit₀ : EmitsAll A₀ rules) (hchain : AChain naive rules A₀ As)
    {A : ActRound} (hA : A ∈ A₀ :: As) (hfix : A.R.Unchanged) :
    Saturate.Inv A.R.before rules ∧ Saturate.Inv A.R.after rules
```

**Reading.** A run is round 0 (`A₀`, naive) and a list of later rounds (`As`). The engine
supplies: correct matchers (`hmatch`), well-formed rule atoms (`h₀`), per-round `RoundOK`
(`WF`, tracking, `PersistFixed`, no subsumption, well-formed atoms), every naive binding of
round 0 applied (`hemit₀`, `EmitsAll`), and the chain `AChain`: each round linked to the
previous, with every binding of the routed matcher (`route naive resp`) applied and the
routing widened to the rules that build an n-ary term after a non-literal rebuild.
`hfix : Unchanged` (`Round.Unchanged`, `:177`) says round `A` changed neither the node set
nor `find`; the engine's stop test gives it
(`engine_stop_unchanged`). The conclusion is the saturation invariant at `A`: every match of
every rule on the fixpoint snapshot is fired, its right-hand side present and its unions
merged. The static routing `naive` is a free parameter, so every routing the engine uses is
covered. Outside: `:subsume`, literal `Den` (the store forms of Section 6.5 lift both),
guards and literals in queries, and a run stopped by a budget, about which the theorem says
nothing.

**Hypotheses of `saturation_complete`, classified.**

| Hypothesis | Meaning | Class | Source |
|---|---|---|---|
| `hmatch : MatchersOK rules` | each rule's matcher emits exactly `Matches ∧ ModeOk` | derived | `matcherOK_engine` for the adaptive scheduler, `matcherOK_static_engine` for the plan `schedule_with_stats` builds (Section 3.4) |
| `h₀ : RulesWF` | the rules' atoms are well formed on the first snapshot | assumed | the resolver; the design note checks it once per rule at compilation |
| `hok`: `Round.WF` | the round facts of Section 6.1 | assumed | `register_if_fresh`, `recanonize_node`, `merge_in_classes`, the hash-cons; `dedup` is derived for a modelled sequence store (`dedup_of_inv`) |
| `hok`: `tracking = true` | merge tracking on | assumed | `saturate_rules_semi` turns it on for every entry point |
| `hok`: `PersistFixed` | the tuple and pair nodes persist literally | assumed | `recanonize_node` maps their children through `find` and nothing else |
| `hok`: `subsumed = ∅` | no subsumption | limit of this form | `tests/egg/subsume.egg`; the store form `saturation_complete_store` allows `:subsume` |
| `hemit₀`, `hchain` | every naive or variant binding is applied, under the routing `route naive resp` | assumed | the matcher and `apply.rs`; the routing is the `respelled` re-match through `spelling_epoch` |
| `hfix : Unchanged` | round `A` changes neither the node set nor `find` | derived | `engine_stop_unchanged` from the stop test, in `saturation_complete_engine` and the `_engine` forms |
| tracking, no globals, literal persistence | the hypotheses the counter-models need | limit | `delta_incomplete_untracked`, `delta_incomplete_global`, `denN_persist_fails` |

*Proof.* `invLag_chain` (`:153`) by induction with `inv_step`. At an unchanged round, `Den`,
`Fired` and `Matches` read the graph only through node membership and `find`, so the
one-round lag closes (`inv_of_unchanged`, `:219`).

**Adequacy.** The emission hypotheses state that the engine's matcher emits at least the
model's naive and variant sets on the frozen index and applies every one. The plan theorems
of Section 3 characterise the model's runs, not the Rust join. The engine skips an action
whose right-hand side has no value (`apply.rs:1346`). Budget exits stop the loop without a
fixpoint, and the theorem says nothing about them. `WF.dedup` is derived for a modelled
sequence store (`dedup_of_inv`, `Rounds/SeqSplice.lean:234`), but no theorem builds a
`Round.WF` from it.

### 6.5 The fidelity variants

`Fidelity/` closes several of these gaps, one at a time, for the saturation theorem:

- `Fidelity/Index.lean`: the index is the store filtered by the skip predicates of
  `egraph/src/index.rs:521-537`. `matches_index_iff` (`Fidelity/Index.lean:89`) states that
  matching the index is matching the store at unskipped nodes.
- `Fidelity/Subsume.lean`: `saturation_complete_store` (`:238`) allows `:subsume`. Matches
  are read on the index and consequences on the store.
- `Fidelity/Normalize.lean`, `NormalizeSat.lean`: `saturation_complete_N` (`:186`) reads
  right-hand sides as the normal forms `add` builds (`DenN`).
- `Fidelity/Recanon.lean`: `StorePersistN` states recanonicalization as the laws apply it
  (statement below). It is the per-round store hypothesis of `saturation_complete_N` and the
  final theorems (`RoundOKN.store`). `DenN.persist_fixed` carries the right-hand sides
  without n-ary application across it; `denN_persist_fails` shows that `DenN.persist` does
  not extend to n-ary ones. Hence the routing of `SChainN` (Section 6.4).
- `Fidelity/RecanonComplete.lean`: the completion-on case, where the engine does not
  re-match (statements below). `DenE` reads a right-hand side modulo the theory of its
  operator on the store (`EqAC`, `EqACI`, `EqA`: the equivalence the normalization steps
  generate); `DenE.persist` carries it across any rebuild meeting `StorePersistE`
  (`StorePersistN` with the sequence nodes literal) with no routing. `saturation_complete_E`
  is the fixpoint theorem on `SChainE`, the chain with any routing per round, and
  `saturation_complete_closed` adds `TheoryClosed`, the store reading of the completion
  completeness theorem, under which every value `add` builds for a right-hand side is in the
  match root's class (`denE_denN_eq`). `Final/Closed.lean` derives `TheoryClosed` from the
  completion state through the correspondence (`theoryClosed_of_complete`), and
  `saturation_complete_closed_of_complete` takes the completion hypotheses in its place. `PersistFails.sa_not_closed` and
  `PersistFails.completed` place the counter-model: its after-store is not closed under the
  theory; its completion is, and reaches the instance.
- `Fidelity/Sound.lean`: `denN_sound` (`:123`) states that what the actions build denotes the
  right-hand side in every model of the graph and the operator laws. Round-level soundness
  with rebuild's merges is open.
- `Fidelity/StopTest.lean`: `engine_stop_unchanged` derives `Unchanged` from the engine's
  stop test. The rebuild is modelled (statements below), and
  `saturation_complete_engine` and its variants take the stop test in place of `Unchanged`.

**Statements of the fidelity layer.**

```lean
structure StorePersistN (L : Sym → OpLaws) (Sb Sa : Store) : Prop extends StoreWF Sb Sa where
  fixed : LiteralFixed Sb Sa
  mset : ∀ id f m, (id, ⟨f, .mset m⟩) ∈ Sb.nodes → NFMset Sa L f (m.map Sa.find) (Sa.find id)
  set : ∀ id f s, (id, ⟨f, .set s⟩) ∈ Sb.nodes → NFSet Sa L f (s.image Sa.find) (Sa.find id)

theorem denN_persist_fails :
    ∃ (L : Sym → OpLaws) (Sb Sa : Store) (σ : Binding) (t : Pat) (c : C),
      StorePersistN L Sb Sa ∧ DenN Sb.graph L σ t c ∧ ¬ DenN Sa.graph L σ t (Sa.find c)
```

**Reading.** `StorePersistN` states what one rebuild does to the store, as `recanonize_node`
applies the laws: a tuple or pair node survives with its children mapped through the new
`find` and nothing else (`LiteralFixed`; the sequence nodes, which `recanonize_node` treats
the same way, are stated by `StorePersistE.seq`, `LiteralSeq`); a multiset node survives as the normal form
of its mapped children under the unit drop and the nilpotent clamp (`RStep`), or collapses to
a leaf when one element or none is left (`NFMset`, the `degeneracy_pair` merge); a set node
likewise under the unit drop (`RSetStep`, `NFSet`). Rebuild supplies it. `denN_persist_fails`
is the counter-model that justifies the routing: a store, a round meeting `StorePersistN`,
and a right-hand side `t` with an n-ary application (`f{x}` built through two splices) that
has a value before a round in which a nested class merges into the unit and only another
value after it, with the node holding the match untouched. A fired instance of a rule that
builds an n-ary term therefore need not stay fired across a rebuild that applied a law, and
`SChainN` routes such rules naive after a non-literal rebuild instead.

**Pseudo-code: rebuild and recanonicalization under the laws, with the spelling-change rule.**

```
recanonicalize(Sb) → Sa:                              -- StorePersistN; rebuild_congruence, recanonize_node
  for (id, f(children)) in Sb.nodes:
    if f is a tuple, pair or sequence:                -- LiteralFixed (tuple, pair); LiteralSeq (sequence, StorePersistE)
      store f(children mapped through find)           -- recanonize_node (fixed arity)
    if f is a multiset:                               -- NFMset
      m := children mapped through find
      repeat: drop the unit's class; drop k copies under :nilpotent k   -- RStep.unit, RStep.nil
      if m = {x}: merge(id, x); if m = ∅: merge(id, unit)   -- Final; degeneracy_pair
      else store f(m), hash-cons, merge on collision  -- WF.dedup
    if f is a set: the same with the unit drop only   -- RSetStep.unit, NFSet
  inverse pairs x, g(x) in one multiset: a merge the round records   -- canon_repair_round
  if any law step applied, or a degenerate collapse happened:
    spelling_epoch += 1                               -- VarCanon::law_applied; spelling_epoch
next round:
  resp := (completion off) and (spelling_epoch moved since the last cut)   -- route naive resp; saturate.rs respelled
  rules that build an n-ary term match naive this round when resp     -- Rule.buildsNary
```

The model states what the store looks like after the rebuild (`StorePersistN`) and takes the
routing as a hypothesis of the chain (`SChainN`); the engine's `touched` log, the
merge-membership delta and the order of the worklist are summarized by `Round.WF`. With
completion on, the engine does not re-match and completion joins the two spellings:
`saturation_complete_closed` (`Fidelity/RecanonComplete.lean`) takes the store's closure
under the theory (`TheoryClosed`) in place of the routing, and
`saturation_complete_closed_of_complete` (`Final/Closed.lean`) derives the closure from the
completion state (statements below).

```lean
theorem inv_step_N {sig : Sym → Kind} {naive : Rule → Bool} {rules : List Rule}
    {prev A : SActRoundN L} (hlink : A.Sb = prev.Sa)
    (hprev : prev.R.WF) (htr : prev.R.tracking = true) (hAp : StorePersistN L A.Sb A.Sa)
    (hatoms₀ : RulesWF sig prev.R.before rules) (hatoms₁ : RulesWF sig prev.R.after rules)
    (hmatch : MatchersOK rules) {resp : Bool} (hresp : ¬ Literal prev.Sb prev.Sa → resp = true)
    (hemit : EmitsRoundN (route naive resp) prev.R A rules)
    (hinv : InvLagN prev rules) : InvLagN A rules
```

**Reading.** `inv_step` on the store: matches read on the index, consequences read on the
store as the normal forms `add` builds (`DenN`), `:subsume` allowed, and the literal
persistence of the previous round (`Literal prev.Sb prev.Sa`) deciding the routing. The
engine supplies `StorePersistN` by its rebuild and `resp` by `spelling_epoch`. Its chain
form is `invLag_chain_N`, and `saturation_complete_N` is the fixpoint theorem on it.

```lean
def EqAC (G : Graph) (L : Sym → OpLaws) (f : Sym) : Multiset C → Multiset C → Prop :=
  Relation.EqvGen (ACStep G L f)

theorem DenE.persist (h : StorePersistE L Sb Sa) {σ : Binding} {t : Pat} {c : C}
    (hd : DenE Sb.graph L σ t c) : DenE Sa.graph L σ t (Sa.find c)

structure TheoryClosed (S : Store) (L : Sym → OpLaws) : Prop where
  mset : ∀ f c c', EqAC S.graph L f {S.find c} {S.find c'} → S.find c = S.find c'
  set : ∀ f c c', EqACI S.graph L f {S.find c} {S.find c'} → S.find c = S.find c'
  seq : ∀ f c c', EqA S.graph L f [S.find c] [S.find c'] → S.find c = S.find c'
  node : ∀ id₁ id₂ n, (id₁, n) ∈ S.nodes → (id₂, n) ∈ S.nodes → S.find id₁ = S.find id₂
  pair : ∀ id₁ id₂ f a b, (id₁, ⟨f, .spair a b⟩) ∈ S.nodes → (id₂, ⟨f, .spair b a⟩) ∈ S.nodes →
    S.find id₁ = S.find id₂

theorem saturation_complete_closed {sig : Sym → Kind} {rules : List Rule}
    (A₀ : SActRoundN L) (As : List (SActRoundN L)) (hmatch : MatchersOK rules)
    (h₀ : RulesWF sig A₀.R.before rules) (hok : ∀ A ∈ A₀ :: As, RoundOKE sig rules A)
    (hemit₀ : EmitsAllN A₀ rules) (hchain : SChainE rules A₀ As)
    {A : SActRoundN L} (hA : A ∈ A₀ :: As) (hfix : A.Unchanged) (hcl : TheoryClosed A.Sa L) :
    ∀ rule ∈ rules, ∀ σ, Matches A.Sa.index rule.atoms σ →
      FiredE A.Sa.graph L σ rule ∧
      ∀ a b, Action.union a b ∈ rule.actions →
        ∀ c₁ c₂, DenN A.Sa.graph L σ a c₁ → DenN A.Sa.graph L σ b c₂ → c₁ = c₂

structure TheoryClosedRest (S : Store) (L : Sym → OpLaws) (f : Sym) : Prop where
  mset : ∀ g, g ≠ f → ClosedAC S L g
  set : ∀ g, ClosedACI S L g
  seq : ∀ g, ClosedA S L g

structure LawsRead (S : Store) (L : Sym → OpLaws) (f : Sym) (st : State n) (Lc : Laws n) : Prop where
  unit : ∀ u, (L f).unit = some u →
    ∃ c, ((0 : Monomial n), c) ∈ st.nodes ∧ clsId (st.find c) = S.find u
  nil : ∀ r, (L f).nilpotent = some r → 2 ≤ r ∧ Lc.HasNil r
  inv : ∀ g, (L f).invOp = some g → ∀ id x, (id, ⟨g, .tuple [x]⟩) ∈ S.nodes →
    ∃ x' y', HoldsAtom st x x' ∧ HoldsAtom st (S.find id) y' ∧ Lc.lawRel ({x', y'} : Monomial n) 0

def SummandsAtomic (st : State n) (N : Finset (Monomial n × Fin n)) : Prop :=
  ∀ p ∈ N, ∀ y ∈ p.1, HoldsAtom st (clsId (st.find y)) y

theorem theoryClosed_of_complete (hcomp : CompleteHyps Lc St st) (h2 : I2 Lc St st)
    (h3 : I3 Lc st) (hk : S.graph.KeysNodup) (hN : Stored st N) (hs : SubRep S.graph st f N ι)
    (hcov : FCover S.graph f N ι) (hsum : SummandsAtomic st N) (hlaws : LawsRead S L f st Lc)
    (hdedup : ∀ id₁ id₂ nd, (id₁, nd) ∈ S.nodes → (id₂, nd) ∈ S.nodes → S.find id₁ = S.find id₂)
    (hsorted : PairsSorted S) (hrest : TheoryClosedRest S L f) : TheoryClosed S L

theorem saturation_complete_closed_of_complete {sig : Sym → Kind} {rules : List Rule}
    {L : Sym → OpLaws} (A₀ : SActRoundN L) (As : List (SActRoundN L)) (hmatch : MatchersOK rules)
    (h₀ : RulesWF sig A₀.R.before rules) (hok : ∀ A ∈ A₀ :: As, RoundOKE sig rules A)
    (hemit₀ : EmitsAllN A₀ rules) (hchain : SChainE rules A₀ As)
    {A : SActRoundN L} (hA : A ∈ A₀ :: As) (hfix : A.Unchanged)
    {Lc : Laws n} {St : Set (Monomial n × Monomial n)} {st : State n}
    (hcomp : CompleteHyps Lc St st) (h2 : I2 Lc St st) (h3 : I3 Lc st)
    (hk : A.Sa.graph.KeysNodup) {f : Sym} {N : Finset (Monomial n × Fin n)}
    {ι : Monomial n × Fin n → NodeId} (hN : Stored st N) (hs : SubRep A.Sa.graph st f N ι)
    (hcov : FCover A.Sa.graph f N ι) (hsum : SummandsAtomic st N)
    (hlaws : LawsRead A.Sa L f st Lc) (hsorted : PairsSorted A.Sa)
    (hrest : TheoryClosedRest A.Sa L f) :
    ∀ rule ∈ rules, ∀ σ, Matches A.Sa.index rule.atoms σ →
      FiredE A.Sa.graph L σ rule ∧
      ∀ a b, Action.union a b ∈ rule.actions →
        ∀ c₁ c₂, DenN A.Sa.graph L σ a c₁ → DenN A.Sa.graph L σ b c₂ → c₁ = c₂
```

**Reading.** `EqAC` is the equational theory of the AC operator `f` modulo the store, on
child multisets: the equivalence generated by the normalization steps `add` applies (a
splice through a class holding an `f`-node, the unit drop, the nilpotent clamp, the inverse
cancellation). `DenE` is `DenN` with the chain of steps replaced by this equivalence: the
match root's class holds a stored node (or is the leaf) whose spelling is equal in the theory
to the spelling built from the match. `DenE.persist` says such a right-hand side stays
present modulo the theory across a rebuild, whatever laws it applied and through however
many nested splices the old chain went: `ACStep.mapE` reads a splice through a node the
rebuild recanonicalized as a splice through its normal form (`NFMset`), joined to the mapped
children by the recanonicalization steps. `SChainE` is the chain with any routing per
round; with completion on the engine's routing is `route naive false = naive`.
`saturation_complete_E` concludes `InvE`: every match on the index at the fixpoint is fired
modulo the theory. `TheoryClosed` is the completion fixpoint read on the store: two classes
equal modulo the laws and the store's equations are one class (`ac_equal_same_class`,
`CompleteAtoms.same_class`), and the hash-cons identifies equal contents. Under it
`denE_denN_eq` says a right-hand side present modulo the theory has every value `add` would
build (`DenN`) in that class, and `saturation_complete_closed` says that at the fixpoint
every union a rule asks for holds between any values of its two sides: a re-match would
merge nothing. The conclusion is `FiredE`, not `FiredN`: the new spelling need not be stored
as a node, since completion materializes the normal form of the old node (`nf_present`), not
every spelling. `theoryClosed_of_complete` (`Final/Closed.lean`) derives `TheoryClosed` from
the completion state of one AC operator `f`: the store holds the nodes of a set `N` of stored
nodes of the state, active or retired, under `ι` (`SubRep` on the store, `Stored`) and no
other `f`-node (`FCover`); the class of each summand holds the summand's one-element monomial
(`SummandsAtomic`, which the completion view supplies for the atomic classes,
`summandsAtomic_withAtoms`); the laws the store reads for `f` agree with the state's
(`LawsRead`: the unit's class holds the empty node, the nilpotent order is at least two and a
law instance on every atom, an inverse pair is a law instance on the two atoms its classes
hold); `I2` and `I3` relate a retired node to an active one of its class
(`node_equal_active`). The proof is the inverse of `ACStep.mapE`. A store class is read as
the monomial of a node of the state in that class (`readClass`, `0` for a class holding
none), a child multiset as the sum of the readings (`readMset`), and one normalization step
on the store is an `=_E`-equality of the readings (`ACStep.readE`): a splice through the node
of `p` reads as `p.1` against its summands, a unit drop as the empty node, a nilpotent clamp
and an inverse cancellation as the law instances. A chain between two singletons is then an
`=_E`-equality between two nodes of the state (`EqAC.readE`), each `=_E`-equal to an active
node of its class, and `ac_equal_same_class` puts the two classes together. A class holding
no node ends no chain but the trivial one: its count is invariant modulo the nilpotent
order, which is `0` or at least `2` (`ACStep.count_mod`, `eq_of_chain_not_noded`). The
`node` field is the hash-cons dedup (`StoreWF.dedup`) and the `pair` field follows from it on
sorted pairs (`PairsSorted`). What is not derived is the remainder `TheoryClosedRest`: the
closure under the theory of every other AC operator (`ClosedAC`; one completion state per
operator derives each) and under the ACI and A theories of every operator (`ClosedACI`,
`ClosedA`), which the completion state does not model; `closedAC_of_absent`,
`closedACI_of_absent` and `closedA_of_absent` discharge it for an operator with no stored
node of the kind and no law. `saturation_complete_closed_of_complete` is
`saturation_complete_closed` with these hypotheses in place of `TheoryClosed`, and its
`_atoms` form takes `CompleteAtoms`, with `I2`, `I3` and the laws read on the completion view
and the summands in the atomic set. `witness_theoryClosed` and
`witness_saturation_complete_closed` (`Final/Witness.lean`) prove every hypothesis on the run
of Section 7.7. The counter-model of `denN_persist_fails` fits:
`PersistFails.sa_not_closed` shows its after-store is not closed under the theory
(`f{p, q} = e` makes `d` and `e'` equal), and `PersistFails.completed` exhibits its
completion, closed and meeting `StorePersistE`, in which `f{x}` has the value `Sc.find e'`
and no other. Fixture: `egraph/tests/egg/semi_recanon_completion_on.egg`.

```lean
inductive CompletionOutcome where
  | disabled | converged (rounds : Nat) | abortedGrowthLimit (addedNodes limit : Nat)
  | abortedWorkLimit (work limit : Nat) | abortedOverflow | goalMet (rounds : Nat)

inductive CompletionRun (K : Completion) : Store → Store → CompletionOutcome → Prop
  | converged {S S' : Store} (n : Nat) :
      K.Steps S S' → K.step S' = none → CompletionRun K S S' (.converged n)
  | stopped {S S' : Store} (o : CompletionOutcome) :
      o.isConverged = false → K.Steps S S' → CompletionRun K S S' o

theorem EnginePhase.rebuild_idle {K : Completion} {Sb Sa : Store} (E : EnginePhase K Sb Sa)
    (hm : E.mints = 0) (hg : E.merges = 0) (hs : E.subs = 0) : Sa = E.mid

def EnginePhase.Stop {K : Completion} {Sb Sa : Store} (E : EnginePhase K Sb Sa) : Prop :=
  E.changes = 0 ∧ E.mid.stamp = Sb.stamp

theorem engine_stop_unchanged {K : Completion} (A : SActRound) (E : EnginePhase K A.Sb A.Sa)
    (h : E.Stop) : A.Unchanged
```

**Reading.** `Completion` is the completion pass as a step function of the store: one
inference, or `none` when a full round finds nothing. `CompletionRun` is a run of it that
either converges (ends at a store with no step, `CompletionRun.converged_fixed`) or stops
with another outcome; the six outcomes (`disabled`, `converged`, `abortedGrowthLimit`,
`abortedWorkLimit`, `abortedOverflow`, `goalMet`) are those `rebuild` reports. `EnginePhase` is a
round as the engine runs it: the action phase with its counts of mints, merges and
subsumes, the snapshot it matched on being a completion fixpoint (`before_fixed`, which a
converged previous rebuild gives and an aborted one does not), congruence closure that is
idle without mints or merges (`cong_idle`), then the completion run. `rebuild_idle` is a
theorem (`CompletionRun.idle`): after an action phase that minted, merged and subsumed
nothing, the rebuild changes nothing. `Stop` is the engine's test: no action reported a
change and the size stamp (node count, class count) did not move; `engine_stop_unchanged`
says it implies `Unchanged`. A round after an aborted rebuild matches on a store that is not
a fixpoint, and the theorem does not apply to it. That is why the runtime check asks for
`Converged` and why a budget stop reports no completeness.

**Pseudo-code: the stop test.**

```
stop?(round):                                         -- EnginePhase.Stop; saturate.rs
  stamp₀ := (node count, class count) at the index build      -- Sb.stamp; size_stamp
  changes := sum of the actions' reported changes (counts a fresh subsume)   -- EnginePhase.changes
  stamp₁ := (node count, class count) after the actions       -- E.mid.stamp
  return changes = 0 ∧ stamp₁ = stamp₀                -- engine_stop_unchanged ⇒ Unchanged
```

The theorem needs the snapshot the round matched on to be a completion fixpoint
(`before_fixed`), which only a `converged` rebuild gives; a budget stop in the previous
rebuild leaves `Unchanged` underived, and the loop reports no fixpoint.

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

There is one `f`-multiset node per active node of the state, its children the
representatives of the summand classes and its class the representative of its CC class.
Class ids are `0` to `n - 1`, and node ids are offset by `n`. The bridge theorems need only
half of `Enumerates`: `Within st A` (`Represents.lean:69`) says every node of `A` is an
active node of `st`. `ac_equal_same_class_graph`, `matches_closed_under_theory` and the
engine-match theorems of `CC/Bridge/Modulo.lean` are stated with `Within`, because an enumeration of the stored active nodes is `Within` the completion view
of Section 5.9 but does not enumerate it.

### 7.2 Statement

**`saturation_modulo_complete`** (`Final/Main.lean:225`):

```lean
theorem saturation_modulo_complete {sig : Sym → Kind} {naive : Rule → Bool} {rules : List Rule}
    (A₀ : ActRound) (As : List ActRound) (hmatch : MatchersOK rules)
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

**Reading.** The hypotheses are those of `saturation_complete` (the run, the matchers, the
routing, the fixpoint round) plus a completion state `st` with `CompleteHyps`
(`CC/Bridge/Modulo.lean:36`: the hypotheses of Section 5.3 with `hcancel` replaced by
`hlat : L.cancellative → LatticeClosed L st`, so that
`ac_equal_same_class` goes through `completion_complete_cancellative_engine`), an
enumeration `act` of its active nodes, and `hG`: the fixpoint snapshot is the graph read
off `st`. The side conditions restrict the rule to one pattern with head `f`. The
conclusion, for two theory-equal active nodes `p`, `p'` and a match rooted at `p'`: the
instance is fired, the root class is `p`'s class, and the pattern matches at that class. So
at the fixpoint every rule has fired on every instance modulo the theory, at the class level.
The weakest point is `hG`: no engine index satisfies it (Section 7.5), and the store form of
Section 7.7 replaces it by `SubRep`. Outside: a term absent from the graph, matched through
its class only (`per_node_form_fails`), and the two-item match lost when its two children
classes merge (`proofs/repro/ac_collapse.egg`).

**`saturation_modulo_complete_atoms`** (`Final/Main.lean:255`) is the same statement for a
completion state with leaf constants:

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

**Reading.** The rounds hypotheses, elided, are those of `saturation_modulo_complete`.
`CompleteAtoms L S st X u` (Section 5.9) replaces `CompleteHyps`, so the theory `E L S` may
relate a node to a constant (`a + b = c`), while `act` and the graph are the stored nodes
only and the conclusion is about stored nodes `p`, `p'`. The proof instantiates
`saturation_modulo_complete_within` (`:119`) at the view `st.withAtoms X u`, with
`CompleteHyps.ofAtoms` (`CC/Bridge/Modulo.lean:60`) and `Enumerates.within_withAtoms`
(`:86`); the graph of the view is the graph of the stored state by definition
(`represents_withAtoms`, `:77`). The restriction of `hG` and the vacuity of literal `Den` for
most rule sets (Section 7.5) apply unchanged; `saturation_modulo_complete_store_atoms`
removes both.

### 7.3 Hypotheses

| Hypothesis | Meaning | Class | Source |
|---|---|---|---|
| `A₀`, `As` | the rounds, with their applied bindings and action facts | assumed | `apply.rs` and rebuild; `Den` is literal in this form (Section 6.3), `DenN` in the store form |
| `hmatch` | each rule's matcher emits exactly the matches its index settings admit (`MatchersOK`, Section 3.4) | derived | `matcherOK_engine` for the adaptive scheduler, `matcherOK_static_engine` (`scheduleEngine_schedA`) for the plan `schedule_with_stats` builds; any other static plan reduces to `SchedA` (`matcherOK_static`) |
| `h₀`, `hok` | rule atoms well formed; per round: `WF`, tracking, `PersistFixed`, no subsumption | assumed | the fixed-arity nodes persist literally in every rebuild; n-ary nodes are not constrained here, the routing of `AChain` covers a non-literal rebuild |
| `hemit₀`, `hchain` | every naive or variant binding is applied | assumed | the engine's matcher and `apply.rs` |
| `hfix` | round `A` changes nothing | derived in the `_engine` forms | `engine_stop_unchanged` derives it from the stop test; this form takes it as stated |
| `hcomp` | completion has converged (`CompleteHyps`; `CompleteAtoms` in the leaf-constant form) | assumed, with the derived and limit parts of Section 5.3 | includes `hlat` (lattice closure, in place of `hcancel`) and `hcp_ax` (`AxiomCP`), which `CompleteHyps.ofLaws` and `CompleteAtoms.ofLaws` derive from the per-law conditions for the law sets `LawSpec` names |
| `henum` | `act` is the set of stored active nodes | definitional | |
| `hG` | the fixpoint snapshot is the represented graph | limit of this form | no engine index satisfies it (Section 7.5); `SubRep` on the index replaces it in `saturation_modulo_complete_store_atoms` (Section 7.7) |
| `rule.atoms = ...`, `P.head = some f` | the rule's query is one pattern with head `f` | side condition | no `Eq` atoms, no globals |

The runtime design note checks `h₀` once per rule at compilation (`hmatch` is a theorem for
both schedulers and needs no check), assigns `hfix` to tier 2 (the stop test), and replaces the history
hypotheses `hok`, `hemit₀` and `hchain` by one naive matching round at the final state, which
checks the conclusion of `saturation_complete` directly. It has no check for `hG`, which no
engine state satisfies (Section 7.5).

### 7.4 Proof

The proof is that of `saturation_modulo_complete_sub` (`Final/Main.lean:89`), which takes
`SubRep A.R.after st f act ι` in place of `hG`; `saturation_modulo_complete_within` (`:119`)
applies it with `represents_subRep`, and `saturation_modulo_complete` applies that with
`henum.within`. Three independent parts:

1. **Fired.** `saturation_complete` gives `Saturate.Inv A.R.after rules`, which applied to the
   match is the first conjunct.
2. **The root.** `matches_at_sub` (`:67`) applies `backOk` to the atoms: it finds a node of
   `A.R.after` under the id `ι p'` with `MatchN` at it, and `KeysNodup` identifies that node
   with the represented node `mkNode st f p'`. On the represented graph, `matches_at_active`
   (`Final/Main.lean:36`) finds an active `q` with `σ.node r = some (nodeId q)` and `MatchN`
   at `mkNode st f q`, and injectivity of `nodeId` gives `q = p'`.
3. **The theory.** `ac_equal_same_class_sub` (`CC/Bridge/Sub.lean`) gives
   `find (ι p') = find (ι p)`, by `completion_complete_at_convergence`, and
   `matches_closed_under_theory_sub` lifts the node match at `p'` to a class match at `p`'s
   class through `MatchC.app`. On the represented graph `ac_equal_same_class_graph`
   (`CC/Bridge/Modulo.lean:101`) gives `find (nodeId p') = find (nodeId p)` and
   `matches_closed_under_theory` (`:144`) lifts the match.

The theory enters only through "theory-equal active nodes share a class". Lifting a node
match to a class match is one constructor. Neither `NoCollapse` nor `matches_transport`
appears in the proof: `saturation_complete` never transports a match across a merge, because
it case-splits on whether the match existed before the round.

### 7.5 What the theorem does not say

**The represented graph holds only active `f`-nodes.** `represents` contains one `f`-multiset
node per active node and nothing else: summand classes have no nodes, other operators are
absent, and retired nodes are dropped. The engine's index holds leaf nodes, other operators,
and retired `FLAG_AC_COLLAPSED` nodes, which the index does not skip (`index.rs:521-537`). So
`hG` restricts `saturation_modulo_complete` to an index that contains only active
`f`-multiset nodes, and no engine index satisfies it. The leaf-constant form keeps this
restriction: `represents st f act` has no node for a leaf constant either, so the leaf
constants enter `saturation_modulo_complete_atoms` only through the theory `E L S`. A rule
whose pattern names a constant, such as `(rewrite (+ a b) c)` with `a`, `b`, `c` nullary
operators, has no match on this graph, because `.plain a []` matches only a stored node of
operator `a`; the theorem covers such a rule only in the empty sense. The store form of
Section 7.7 replaces `hG` by `SubRep A.Sa.index st f act ι`: the represented graph is a part
of the index, which may hold leaf nodes, other operators, the nodes the right-hand sides
build and retired nodes. `saturation_modulo_complete_sub` does the same for the literal form.

**The hypotheses of the literal forms are contradictory for many rules.** `Fired` requires
every application in the right-hand side to be a stored node of `A.R.after` (through `Den`),
and under `hG` the only stored nodes are `f`-multiset nodes with literal children. If a rule
has a match at the fixpoint and its right-hand side builds any other node, for example
`(rewrite (f x y) (g x))`, `saturation_complete` derives `Fired` for that match, `Fired`
cannot hold, and the theorem holds vacuously for that rule set. The literal theorems have
content for rules whose right-hand sides are variables or literal `f`-terms the store holds
as written; the hypotheses are joint, so one such rule with a match makes the theorem vacuous
for every rule of the set, and a rule set whose right-hand sides use a second operator or a
constant is the common case. `saturation_modulo_complete_atoms` adds one more case: a
right-hand side that names a leaf constant, or that is a one-element `f`-term `(f x)`, needs
a stored node the graph does not have, because the implicit nodes of the view are not nodes
of `represents`. The docstrings of both theorems state the restriction (limit 3).
`AtomsWitness.witness_complete` establishes `CompleteAtoms` for one state and constructs no
rounds, so the literal forms have no witness of joint satisfiability with `hG`. The store
form reads right-hand sides as the normal forms `add` builds (`DenN`, `FiredN`) and has one:
`witness_saturation_modulo_complete` (`Final/Witness.lean`) applies it to two concrete rounds
of a rule whose right-hand side is a node of another operator, with every hypothesis proved
(Section 7.7).

**The literal forms use the least faithful layer.** They use literal `Den`, no subsumption,
the graph read as the index, and `Unchanged` assumed. Section 6.5 lists the theorems that
remove each restriction, and Section 7.7 composes them with the bridge; the literal forms
stay as the simplest statement of the argument.

**Two limits are stated in the docstring.** A theory-equal term absent from the graph has no
node and is matched through its class only. The per-node form, "a binding at `p` yields one
at `p'`", is false: `per_node_form_fails` (`CC/Bridge/Modulo.lean:251`) gives a state with
nodes `f{0, 1, 2}` and `f{0, 3}` in one class, where `f{x, y, z}` matches the first and cannot
match the second. That witness does not establish `CompleteHyps` for its state. The second
limit is that maximum partition loses a two-item match when its two children classes merge
(`proofs/repro/ac_collapse.egg`). The proof does not need a hypothesis about it.

### 7.6 The matching-side theorem

**`saturation_modulo_sound`** (`Final/Main.lean:288`):

```lean
theorem saturation_modulo_sound {sig : Sym → Kind} {rules : List Rule}
    {L : Laws n} {S : Set (Monomial n × Monomial n)} {st : State n}
    {act : Finset (Monomial n × Fin n)} (hcomp : CompleteHyps L S st)
    (henum : Enumerates st act) {f : Sym} {G : Graph} (hG : G = represents st f act)
    (hwf : RulesWF sig G rules) (hmatch : MatchersOK rules) :
    ∀ rule ∈ rules, ∀ (P : Pat) (r : Var), rule.atoms = (atoms P r).map QAtom.scan →
      P.head = some f →
      ∀ σ ∈ rule.matcher.naive G,
        Matches G rule.atoms σ ∧
        ∃ p' ∈ act, σ.node r = some (nodeId p') ∧
          σ.cls r = some (G.find (nodeId p')) ∧
          MatchN G P (mkNode st f p') σ ∧
          ∀ p ∈ act, E L S p.1 p'.1 → MatchC G P (G.find (nodeId p)) σ
```

**Reading.** One matching run on the represented graph, no rounds. Every binding the rule's
matcher emits naively is a match, is rooted at some active node `p'`, and is a class-level
match at every `p` theory-equal to `p'`. `STATUS.md` calls it the converse of the
completeness theorem; it is the soundness of the matcher composed with the bridge. Outside:
soundness of the actions, because `Fired` asks only that a consequence is present, and a
hash-cons hit or a completion-minted node can also account for it.

### 7.7 The final theorem over the store

The final theorem is stated on the store model of `Fidelity/` (Section 6.5),
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
    (A₀ : SActRoundN ops) (As : List (SActRoundN ops)) (hmatch : MatchersOK rules)
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

**Reading.** The final theorem in its strongest form. The rounds are store rounds with
normalized right-hand sides (`SActRoundN`), with `RoundOKN` (`WF`, tracking, `StorePersistN`,
well-formed atoms) per round, `EmitsAllN` at round 0, the chain `SChainN` with its routing,
and the fixpoint `Unchanged`. Matches are read on the index, consequences on the store as
normal forms, and `:subsume` is allowed. The completion state enters through
`CompleteAtoms`, `Within` (`act` holds active nodes of `st`) and `SubRep`; the other nodes of
the index may be leaf constants, other operators, right-hand-side nodes and retired nodes.
The conclusion, for a match rooted at `p'`: the instance is fired in the store as normal
forms (`FiredN`), its root binds `p`'s class, the pattern matches at that class on the
index, and the matched node is the represented node of `p'`. `_store`
(`saturation_modulo_complete_store`) is the form with `CompleteHyps`,
`saturation_modulo_complete_store_engine` takes the engine's stop test in place of
`Unchanged`, `_store_atomic` takes `CompleteAtomic`, and
`saturation_modulo_complete_store_cover` adds `FCover` (every `f`-node of the index is the
node of some `p ∈ act`) and concludes for every match, whatever its root. The proof is that
of Section 7.4 with `saturation_complete_N` in place of `saturation_complete`;
`matches_at_sub` identifies the matched node through `KeysNodup`. Outside: the relation
between `st` and the rounds. A match rooted at a retired node is covered by the retired form
below. The completion settings in which the engine does not re-match
after a spelling change are covered at the store level by `saturation_complete_closed`
(Section 6.5), which takes the store's closure under the theory (`TheoryClosed`) in place of
the routing of `SChainN`; `saturation_complete_closed_of_complete` derives the closure from
the completion state, up to the remainder `TheoryClosedRest` (Section 9).

**`saturation_modulo_complete_store_retired`** (`Final/Store.lean`). The
engine keeps a collapsed node (`FLAG_AC_COLLAPSED`, retired in the model) in the index and
matchable, so `FCover` over `act` fails on every run in which completion collapsed a node
(`not_cover`, below). `SubRepR G st f act ret ι` (`CC/Bridge/Sub.lean`) extends the
correspondence to a set `ret` of stored nodes, the retired ones, each in `G` under `ι` with
the children of `mkNode` and its class in `st`; `Stored st ret` says they are nodes of
`st`. With `FCover` over `act ∪ ret`, the theorem concludes for every match of the index:

```lean
theorem saturation_modulo_complete_store_retired ...
    (hcomp : CompleteHyps L S st) (h2 : I2 L S st) (h3 : I3 L st)
    (hw : Within st act) (hret : Stored st ret)
    (hs : SubRepR A.Sa.index st f act ret ι) (hcov : FCover A.Sa.index f (act ∪ ret) ι) :
    ∀ rule ∈ rules, ∀ (P : Pat) (r : Var), rule.atoms = (atoms P r).map QAtom.scan →
      P.head = some f →
      ∀ σ, Matches A.Sa.index rule.atoms σ →
        FiredN A.Sa.graph ops σ rule ∧
        ∃ p' ∈ act ∪ ret, σ.node r = some (ι p') ∧ MatchN A.Sa.index P (mkNode st f p') σ ∧
          ∃ q ∈ st.active, E L S p'.1 q.1 ∧ st.find q.2 = st.find p'.2 ∧
            σ.cls r = some (clsId (st.find q.2)) ∧
            MatchC A.Sa.index P (clsId (st.find q.2)) σ ∧
            ∀ p ∈ act, E L S p.1 p'.1 →
              σ.cls r = some (A.Sa.find (ι p)) ∧ MatchC A.Sa.index P (A.Sa.find (ι p)) σ
```

**Reading.** For every match: the instance is fired, the root is the node of some `p'`,
active or retired, where the pattern matches, and there is an active node `q` of `st`, in
`p'`'s class and `=_E`-equal to it, whose class the root binds and at which the pattern
matches at the class level; every active `p ∈ act` `=_E`-equal to `p'` gives the same
class, read in the index as `A.Sa.find (ι p)`. For an active `p'`, `q` is `p'` itself. For a
retired `p'`, `node_reduces_active` (`CC/Bridge/Sub.lean`) gives `q`: `I3` rewrites a retired
node to a node of its class, smaller under `≫`, so well-founded induction on `→_R`
(`Rw_wf`) reaches an active one, and `I2` (`rules_sound`, `Rw_rtg_sound`) makes the rewrite
an `=_E`-equality (`node_equal_active`). `I2` and `I3` are hypotheses beside
`CompleteHyps`; the leaf-constant form `saturation_modulo_complete_store_retired_atoms`
takes them on the completion view, whose rules include `M → {x}` for an atomic class and
whose `q` may be an implicit node of a leaf constant. Matching on a retired node is sound
in the engine because the node is still a member of its class, so a match rooted at it is a
match at that class, and completeness is unaffected because every match it yields is
yielded, at the class level, by the active node it rewrites to; what it costs is time: the
extra matches build nodes `=_E`-equal to the ones the active match builds, which completion
or hash-consing joins. The match count is not measured.

**The witness.** `Final/Witness.lean` takes the completion state of `CC/AtomsWitness.lean`
(the program `(union (+ a b) c)`, `t = a + b + d`, `u = c + d`) and adds the rules
`(rewrite (+ x y) (g x y))` with `g` a plain binary operator and
`(rewrite (+ x y z) k)` with `k` a constant. The store holds the four leaf constants, the
three `+`-nodes `{a, b}`, `{a, b, d}`, `{c, d}`, and after round 0 the four `g`-nodes
`g(a, b)`, `g(b, a)`, `g(c, d)`, `g(d, c)` and the `k`-node in the class of `{a, b, d}`;
round 1 matches on the result, builds nothing new and is the fixpoint. Every hypothesis is
proved by hand and `decide`, no `native_decide`.

```lean
theorem witness_saturation_modulo_complete :
    ∀ r ∈ rules, ∀ (P : Pat) (root : Var), r.atoms = (atoms P root).map QAtom.scan →
      P.head = some 0 →
      ∀ p ∈ act, ∀ p' ∈ act, E (Laws.plainAC 5) wS p.1 p'.1 →
      ∀ σ, Matches A₁.Sa.index r.atoms σ → σ.node root = some (ι p') →
        FiredN A₁.Sa.graph ops σ r ∧
        σ.cls root = some (A₁.Sa.find (ι p)) ∧
        MatchC A₁.Sa.index P (A₁.Sa.find (ι p)) σ ∧
        MatchN A₁.Sa.index P (mkNode wst 0 p') σ

theorem not_cover : ¬ FCover A₁.Sa.index 0 act ι

theorem witness_fires_retired :
    FiredN A₁.Sa.graph ops σabd rule₂ ∧
      σabd.cls 3 = some (A₁.Sa.find (ι p₃)) ∧
      MatchC A₁.Sa.index pat₂ (A₁.Sa.find (ι p₃)) σabd ∧
      MatchN A₁.Sa.index pat₂ (mkNode wst 0 p₂) σabd
```

**Reading.** `witness_saturation_modulo_complete` is `saturation_modulo_complete_store_atoms`
applied to this run with every hypothesis proved: the hypotheses of the final theorem are
jointly satisfiable on a run whose right-hand side builds a node of another operator, which
the literal forms could not show. `witness_fires_modulo` reads the conclusion at the match
`x ↦ c, y ↦ d` rooted at `{c, d}`. The node `{a, b, d}` is retired in
the completion state (Section 5.9), so `act` holds `{a, b}` and `{c, d}` only, and the
theorem says nothing about a match rooted at `{a, b, d}`; its class is that of `{c, d}` by
the store's union-find (`retired_class`), not by the theorem. `not_cover` records the limit
of the covering form: the collapsed node stays in the index and is matchable, so `FCover`
over `act` fails, and `saturation_modulo_complete_store_cover` has no witness on any run in
which completion collapsed a node. `witness_saturation_modulo_complete_retired` is
`saturation_modulo_complete_store_retired_atoms` on the same run, with `ret = {p₂}`
(`{a, b, d}`), `Stored`, `SubRepR` and `FCover` over `act ∪ ret` proved (`hyp_ret`,
`hyp_subR`, `hyp_coverR`), `I2` on the completion view (`witness_I2`: `{a, b}` with `c`,
`{a, b, d}` with `{c, d}`) and `I3` (`witness_I3`). The second rewrite matches `{a, b, d}`
only (`match_cases₂`: three distinct elements, which no two-element node holds), and
`witness_fires_retired` reads the conclusion at the match `x ↦ a, y ↦ b, z ↦ d` rooted at
it: the instance is fired (`k` is in the root's class), the root binds the class of the
active `{c, d}`, `=_E`-equal to `{a, b, d}` under `a + b = c` (`E_abd_cd`), the rewrite
matches at that class, and it matches at the represented node of `{a, b, d}`. Both rules
are routed naive in both rounds, so the semi-naive branch of `SChainN` is not exercised; the
matches are characterized on the concrete graphs (`match_cases`, `match_cases₂`), not by
running the plan. `witness_atomicOf`, `witness_complete_atomic` and
`witness_saturation_modulo_complete_atomic` repeat the witness with `A := atomicOf wst`.

**What remains.** `SubRep`, `CompleteAtoms` and the round facts are hypotheses: no theorem
relates the completion state to the rounds or to the engine's rebuild, so the theorem says
nothing about a run whose index does not hold the active nodes of a converged state. The
minimal-monomial hypotheses stay in `CompleteAtoms`; `hcp` is reduced to `AxiomCP`, which
the per-law conditions discharge for the law sets `LawSpec` names (`CompleteAtoms.ofLaws`),
and `hcancel` is replaced by lattice closure. The engine's completion settings, which do not
re-match, reach every instance at the class level: `saturation_complete_closed` takes the
store's closure under the theory (`TheoryClosed`) in place of the routing of `SChainN`, and
`saturation_complete_closed_of_complete` derives the closure from `CompleteHyps`, `I2`, `I3`
and the correspondence on the store, leaving the other operators and the ACI and A theories
as the remainder `TheoryClosedRest`. The covering
form over `act` alone excludes any index holding a collapsed `f`-node; the retired form takes
`I2`, `I3` and `SubRepR` as further hypotheses and covers it. Section 9 lists each of these
as a gap.

**Hypotheses of `saturation_modulo_complete_store_atoms`, classified.** The rounds
hypotheses are those of `saturation_complete` on the store (the table of Section 6.4, with
`StorePersistN` in place of `PersistFixed` and `:subsume` allowed); the completion
hypotheses are those of `CompleteAtoms` (the table of Section 5.9). The bridge adds:

| Hypothesis | Meaning | Class | Source |
|---|---|---|---|
| `hw : Within st act` | every node of `act` is an active node of `st` | definitional | `act` is chosen as the active nodes |
| `hs : SubRep A.Sa.index st f act ι` | each `p ∈ act` is stored in the index under `ι p` with the children of `mkNode st f p`, in the class `st` gives it | assumed | the correspondence between the engine's index and the completion state of the model; no theorem relates the two (Section 9) |
| `hfix : A.Unchanged` | the round changes nothing | derived | `engine_stop_unchanged`, in `saturation_modulo_complete_store_engine` |
| `FCover` (the `_cover` form) | every `f`-node of the index is the node of some `p ∈ act` | limit | fails on every run in which completion collapsed a node (`not_cover`); the `_retired` form takes `SubRepR`, `I2`, `I3` instead |
| `TheoryClosed` (`saturation_complete_closed`, completion on) | the store is closed under the theory | derived | `theoryClosed_of_complete`, from `CompleteHyps`, `I2`, `I3`, `SubRep` and `FCover` on the store, `SummandsAtomic`, `LawsRead`, the dedup and `PairsSorted`, in `saturation_complete_closed_of_complete` (Section 6.5) |
| `TheoryClosedRest` (`saturation_complete_closed_of_complete`) | the other AC operators and the ACI and A theories are closed | assumed | one completion state per AC operator; the ACI and A theories have no completion state (Section 9) |
| a theory-equal term absent from the graph; a two-item match whose children classes merge | | limit | `per_node_form_fails`; `proofs/repro/ac_collapse.egg` (`NoCollapse`) |

## 8. Conformance and mirror tests, and the fixtures

No theorem connects a Lean model to the Rust code. The tests below compare the executable
models with the engine on generated or recorded inputs; each compares one model definition
with one engine function. The counts are those of the committed corpora and of the last run
on record.

| Test | Compares | Against the model definition | Count |
|---|---|---|---|
| `conform.rs` (`egraph/tests/`) | the `check-eq` and `check-neq` results of every `.egg` file under `tests/egg/conform*`, run under both evaluation strategies and both atom-scheduling settings | `semper-conform`: `run (compile P)` (`EMatch/Ref.lean`) over `enumerateX`, `enumerateL` and the regrouped views (`regroupLevels`, `regroupLevelsCapped`, `runERO`); `semper-conform-flatten`: the flattened plan `planF` with `runER`; `semper-conform-cc`: the bounded closure of `CC/BoundedOracle.lean` (`run_sound`); `semper-conform-rounds`: the fired-instance invariant `Saturate.Inv` on the engine's own dumps; `semper-conform-cc-cert`: `not_E_of_separates` | 1,000 committed files: 200 `conform` and 200 `conform-flatten` (the 400 samples of the matching models, seed 1 and seed 2), 200 `conform-cc`, 200 `conform-rounds`, 200 `conform-cc-cert`; the Lean workflow regenerates all but `conform-rounds` and fails on a difference |
| `flatten_differential.rs` | the matches of `run_query` under `:flatten`, projected onto the pattern's variables and the root, as multisets, against a brute-force Rust reference that enumerates every opened, regrouped and overlap view of a node read back through the public accessors | the view definitions of Section 4.1 (`Views`, `RegroupsTo`, the overlap views), transcribed independently of the engine's enumerator | four tests (`flattened_matches_reference`, `_laws`, `untagged_matches_stored_children`, `_laws`), 60 seeded programs each, every pattern, both scheduling settings |
| the fold mirror | the conformance oracle `runER` run with the fold directions of the case (`Conform/Flatten/Oracle.lean`, `FCase.dirOf`) against the engine's `:flatten` matching on fold patterns; bindings compared as the number of distinct `Tag` nodes | `rawOptD`, `enumerateR` with `Dir.left` and `Dir.right` (`FoldEnum.lean`, `FoldRegroup.lean`) | 800 samples (the 400 committed `conform` and `conform-flatten` samples and 400 more of seed 3 of the `:flatten` generator), 230 with a fold in the pattern; every check holds and the binding counts agree; the comparison test is not committed |
| the atom-choice mirror, `atom_choice_agrees_with_the_model_on_the_rounds_corpus` (`ematch.rs`) | at every phase-B decision of the `conform-rounds` corpus run naive and semi-naive under runtime scheduling, the atom `choose_atom` takes against the one a Rust transliteration of `chooseEngine` takes from the same bindings and bucket lengths | `chooseEngine` (`EMatch/Engine/Choose.lean`) | 200 files, 4945 decisions, 1591 with several candidates, all agree; two mutations of the transliteration are caught (30 and 808 disagreements) |
| the static-plan mirror, `static_plan_agrees_with_the_model_on_the_rounds_corpus` (`schedule.rs`) | every plan `schedule_inner` builds while the `conform-rounds` corpus runs naive and semi-naive, against the steps a Rust transliteration of `scheduleEngine` (`model::schedule`) emits from the engine's prices: atom order, binding kind per variable, join lookups | `scheduleEngine` (`EMatch/Engine/Schedule.lean`), `engineJoinLookups` | 200 files, 2999 plans; 2679 compared (1185 with several atoms, 4071 picks), all agree; 320 outside the model, each for a rule with a `(= x g)` atom; three mutations caught (608, 17 and 458 disagreements), a fourth by `eager_chain_agrees_with_the_model` |
| the cursor mirror, `cursor_agrees_with_the_recursive_executor_on_the_rounds_corpus` and `cursor_frames_agree_with_the_lean_model_on_random_residuals` (`ematch.rs`) | every static plan `run_query_into` runs while the `conform-rounds` corpus runs naive, against the match multiset `MatchIterator` yields on the same plan and index (`mirror_cursor`); and the engine's cursor on random multiset and set nodes against a Rust transliteration of the Lean frame (`scan`, `findStep`, `findLoop`, `postYield`, `drive` over the AC and ACI stores) | `drive_eq_enum`, `acFrame_eq_decomposeAC`, `aciFrame_eq_decomposeACI` (`EMatch/Engine/Cursor.lean`); the frame stack has no model | 200 files, 1427 plans, 770 with a match, all agree; 720 random patterns compared, all agree, the model's lists without repeat; the corpus mirror found three defects of the cursor (Section 3.9) |
| the certified completion states (`semper-conform-cc-cert`, `tests/egg/conform-cc-cert/`) | the engine's `check-neq` under eager completion against pairs a concrete countermodel separates, with the certificate in the preceding comment; `check-eq` against the bounded oracle | `not_E_of_separates`, `E_sound` (`CC/Countermodel.lean`); `run_sound` (`CC/BoundedOracle.lean`) | 200 committed programs, seed 1, run by `conform.rs`; a failing `check-neq` is an engine unsoundness, a failing `check-eq` a completeness gap |
| the soundness waves | the certified generator's programs with their `dump-egraph` line, run through the engine by the soundness runner, which reads the dumped final state and checks every certified `check-neq` | `not_E_of_separates` on the dumped state | 10,200 programs over the waves run; every fixture named `ac_collapsed_recanon.egg`, `cancel_lattice.egg`, `cancel_crit_pair.egg`, `cancel_lattice_lazy.egg`, `nilpotent_group_lattice.egg` and `ac_reactivate_min_monomial.egg` is a reduction of a program of this generator |

The regrouping counters are checked the same way: every regrouping the engine runs on the
`conform` and `conform-flatten` samples has the counters of the model's run on a node of the
case (an instrumented engine against an executable mirror of `BSt.run`, not committed); on
`c1_0052.egg` both stop at `MAX_REGROUP_VIEWS` (16,385 records). The generators use
`regroupLevels` rather than the engine's loop, which emits the same `check-eq` sets in another
order and so changes the sampled `check-neq` candidates; they run the overlap stage
(`runERO`, `overlapStage` in `Conform.regroupedRecs`), and eight of the 400 matching samples
carry overlap matches (`conform/c1_0081.egg`, `c1_0101.egg`, `c1_0152.egg`, `c1_0181.egg`,
`conform-flatten/f2_0026.egg`, `f2_0112.egg`, `f2_0118.egg`, `f2_0135.egg`).

**Fixtures, by the theorem or invariant each probes.** A fixture without a path is in
`egraph/tests/egg/`; `egg_tests.rs` runs them.

The minimal monomial (I5: `reachable_I5`, `keyed_reachable_I5`, `unretire_refresh_I5`):

- `ac_min_slot_refresh.egg`, `proofs/repro/min-slot-gap.egg`: the refresh when recanonicalization shrinks a node (`shrinkNoRefresh_breaks_I5`).
- `ac_minmono_grow_wa.egg`, `ac_minmono_grow_aw.egg`, `ac_key_survivor_lowered.egg`: the per-class order keys (`idOrder_grow_breaks_I5`).
- `ac_reactivate_min_monomial.egg` (reduced from `conform-cc-cert/cs1_0129.egg`): the refresh after re-activating a collapsed node (`unretireNoRefresh_breaks_I5`).
- `ac_collapsed_recanon.egg`: clearing the collapsed flag when a node becomes irreducible (`Infer.unretire`, `RoundFixed.nf_present`).

The fixed round and the reduced basis (`RoundFixed`, `hcp_of_fixed`, `kapur_termination`):

- `cc_containment_chain.egg`: two containing pairs that join only through the reducibility pass (`lhs_reduced`).
- `conform-cc/cc1_0143.egg`: a disjoint partner reached through the use lists under the clamp, which the superposition loop skips.

Lattice closure (`LatticeClosed`, `latticeClosed_of_engineFixed`, `hcancel_not_derivable`):

- `cancel_lattice.egg`, `cancel_crit_pair.egg`, `cancel_lattice_lazy.egg`, `nilpotent_group_lattice.egg`: equalities that need several copies of an equation.

The inverse rules R1 to R5 (`completion_complete_inverse_engine`, `inv_rules_sound`):

- `proofs/repro/inv-into-unit.egg`, `proofs/repro/unit-inverse.egg`, `proofs/repro/rule-inverse-cp.egg`, `proofs/repro/z3-inverse.egg`: the four consequences pair cancellation inside one monomial misses.

The A-only round (`rewrite_left_sound`, `rewrite_right_sound`, `aRound_sound`):

- `ac_fold_completion_spine.egg`: a fold's spelling rewritten on its spine only.

Leaf constants and the `atomic` bit (`atomicOf`, `atomCollapse_of_addFixed`):

- `atomic_bit_child_before_and_after_node.egg`, `atomic_bit_inverse_after_splice.egg`, `atomic_bit_last_node_collapses.egg`, `atomic_bit_leaf_gains_node.egg`, `atomic_bit_merge_spliced_side.egg`: the bit's five transitions against the bounded oracle.

Outcomes and budgets (`CompletionRun`, `CompletionOutcome`):

- `ac_lazy_budget_inconclusive.egg`: a `check-neq` reported inconclusive after a budget stop.

Maximum partition (`MatchN`, `NoCollapse`):

- `proofs/repro/ac_collapse.egg`: a two-item match lost when its two children classes merge, a documented limit.

The demand rule (`demand_engine_complete_ac`, `demand_engine_complete_aci`, `nonInertEng_eq`):

- `proofs/repro/demand-gap.egg`, `flatten_demand_refold.egg`: a match whose unsatisfied leaf opened a class an item takes (`acceptsFix`).
- `flatten_laws_nilpotent.egg`, `flatten_laws_inverse.egg`, `flatten_laws_inverse_leaf.egg`, `flatten_laws_identity.egg`, `flatten_laws_assoc_unit.egg`: leaves that are not inert under the laws (`nonInertB`).
- `proofs/repro/aci-overaccept.egg`: a redundant set match the rule admits, a documented over-acceptance.
- `aci1.egg`: the collapse invariant on set nodes (`twoClassesL_of_members`).

Folds (`otLeft_sound`, `otRight_sound`, `rawNodeD_left_iff`):

- `flatten_fold_spine.egg`: a fold opened on its spine only.

Regrouping (`regroup_match_iff`, `regroup_match_iff_laws`, `regroupSkipO_match_iff_laws`, `regroupBounded_query_exact`):

- `flatten_regroup_nested_needs.egg`: the item limit on the final record only (`regroup_nested_matches`).
- `flatten_regroup_laws_drop_need.egg`: needed classes the laws drop (`regroup_drop_need_unit`, `_nilpotent`, `_inverse`, `_leaf`).
- `flatten_regroup_laws_no_item.egg`: an item-less pattern regrouped when the laws can drop a class (`mem_base_of_reach`).
- `flatten_regroup_laws_insert.egg`: a normal form reached only by insertion, the documented limit (`regroup_insert_unit_lost`).
- `flatten_regroup_laws_idem.egg`: the overlap view a set group keeps beside its class (`regroup_idem_overlap_found`).
- `conform/c1_0101.egg`: a pattern with one item more than the node has children binds the node's own class (`S{s, A, B} = s`).
- `c1_0052.egg`: a node past `MAX_REGROUP_VIEWS` in both the engine and the model's bounded run.

Semi-naive rounds (`delta_complete`, `semi_naive_round_complete`, `Round.WF`):

- `semi_merge_membership_delta.egg`: the merge-membership delta (`delta_incomplete_untracked`).
- `semi_eq_global_local.egg`, `proofs/repro/semi-eq-global-local.egg`: naive routing of a rule with an equality to a global (`delta_incomplete_global`).
- `seq_hashcons_miss_min.egg`, `rounds_r1_0581.egg`: splicing with canonical children (`raw_breaks_dedup`, `dedup_of_inv`).
- `semi_naive_atomic_semi.egg`, `semi_naive_minmono.egg`: the build-time spelling of an AC right-hand side, outside `saturation_complete`, covered by `spelling_epoch`.

Recanonicalization under the laws (`StorePersistN`, `denN_persist_fails`, `saturation_complete_closed`):

- `semi_recanon_unit_drop.egg`, `semi_recanon_idem_collapse.egg`, `semi_recanon_inverse_cancel.egg`, `semi_recanon_pending_collapse.egg`: the `respelled` re-match with completion off.
- `semi_recanon_completion_on.egg`: the same counter-model with completion on, joined at the fixpoint (`PersistFails.completed`).

The stop test and transport (`engine_stop_unchanged`, `fired_transport`):

- `stop_self_union_mints.egg`, `stop_assoc_flatten_mints.egg`: a union that mints nodes and reports zero changes (`Phase.stamp_ne`).
- `tests/egg/subsume.egg`: a `:subsume` that removes a node a consequence is built of, why `fired_transport` needs no subsumption.

## 9. Remaining gaps

Each entry names the gap, what closes it, and the check that shows it closed. The first five
are the hypotheses of the final theorem that state a correspondence between the engine and
the model (the class "assumed" of the tables above); the others are missing fixtures, missing
models, and the limits that stay by design.

1. **`SubRep` (the correspondence).** `saturation_modulo_complete_store_atoms` takes
   `SubRep A.Sa.index st f act ι`: the active `f`-nodes of the completion state are stored in
   the index under `ι` with the children `mkNode` gives them and in the classes `st` gives
   them. No theorem relates the completion state to the rounds or to the engine's rebuild, so
   the theorem says nothing about a run whose index does not hold the active nodes of a
   converged state. Closes it: a model of the rebuild's completion pass on the store
   (`Fidelity/StopTest.lean` has `CompletionRun` as a step function) whose converged store
   satisfies `SubRep` against a `State` read off it, or the tier 2 checker, which reads a dump
   of the final state into `State` and decides `SubRep` against the index. Acceptance: a
   theorem `subRep_of_converged` on the modelled rebuild, or the checker run over the
   committed corpora with no failure.
2. **The remainder of `TheoryClosed`.** With completion on the engine does not re-match
   after a spelling change, and `saturation_complete_closed` reaches every instance at the
   class level under `TheoryClosed`, the store's closure under the theory.
   `theoryClosed_of_complete` (`Final/Closed.lean`) derives it from `CompleteHyps`, `I2`, `I3`
   and the correspondence on the store (`SubRep`, `FCover`, `SummandsAtomic`, `LawsRead`) for
   the AC operator of the completion state, and `saturation_complete_closed_of_complete`
   takes those hypotheses in its place. What stays a hypothesis is `TheoryClosedRest`: the
   closure under the theory of every other AC operator, and under the ACI and A theories of
   every operator, which `CC/` does not model (`ClosedACI`, `ClosedA`). Closes it: one
   completion state per AC operator in `saturation_complete_closed_of_complete` (a family in
   place of the single state), and a set-node correspondence for the ACI operators under
   which `ACIStep` reads in a completion state with the idempotent law; the A theory has no
   completion theorem (gap 10). Acceptance: `TheoryClosedRest` reduced to its `seq` field.
3. **The count-threshold conditions.** `axiomCP_of_laws` derives `AxiomCP` for every tag
   set the engine accepts from the fixed round and the per-law conditions `LawSpec.Conds`
   (Section 5.6), and `CompleteHyps.ofLaws`, `CompleteAtoms.ofLaws` take those conditions in
   place of `hcp_ax`. What remains: the conditions `hlhs` and `hax` of the nilpotent and
   idempotent laws (counts below the threshold on every left-hand side; the engine's axiom
   pairs joinable) and `hu` of the identity law are stated on the rules and derived from no
   fixpoint structure, where the inverse conditions are derived from `RoundFixedInv`,
   `RoundFixedInvUnit` and `RoundFixedInvNil`. Closes it: a fixpoint structure for the axiom
   pairs of the count-threshold laws (the per-rule pairs of `cc_round`, stated as
   `RoundFixedInv.r3_left` is) with a theorem deriving `hax` from it. Acceptance:
   `LawSpec.conds_nilpotent_of_fixed` and `conds_idempotent_of_fixed`, audited in
   `CC/Laws/Check.lean`.
4. **The minimal-monomial history and the round facts.** The triple `h5₀`, `hrun`, `ha` is
   equivalent to assuming I5 of the final state (`OpsStar` is never linked to the inference
   run; `witness_complete` discharges it with `ss₀ = ss`). The round facts `Round.WF`,
   `ActRound` and `StorePersistN` are assumptions about `register_if_fresh`, `recanonize_node`,
   `merge_in_classes`, the hash-cons and `apply.rs`. Closes it: for I5, either `I5 st` in the
   statements in place of the triple, or `OpsStar` linked to `Reachable` by a theorem that
   every `Infer` step is an `Op`; for the round facts, the tier 1 and tier 2 checks of the
   design note (I5 by `check_min_monomial_invariant`, congruence by
   `debug_check_congruent_dup_invariant`, both existing as debug checks; the others design).
   Acceptance: `completion_complete_at_convergence` with `h5 : I5 st` as its only
   minimal-monomial hypothesis, and the tier 1 checker of the design note returning
   `Complete` on every committed corpus.
5. **The resolver's variable discipline.** `AtomsWF` and `EnvAtomsWF` (well-kinded atoms,
   distinct node variables, linear rest variables, every `Eq` operand bound by a scanning
   atom, a class variable no multiplicity or rest variable, no `exact 0` annotation) are
   supplied by `resolve.rs` and derived only for the atoms of a single pattern
   (`atoms_atomsWF`). Closes it: a transcription of the resolver's checks as a decision
   procedure on `List QAtom` with a theorem that it returns true exactly when `AtomsWF` and
   `EnvAtomsWF` hold, and a mirror test against `resolve.rs` on the corpora. Acceptance: the
   theorem and a mirror test with zero disagreements on the five corpora.
6. **The overlap-truncation fixture.** No fixture exercises a truncation inside the overlap
   stage: with the default bounds a family of overlap views past `MAX_REGROUP_VIEWS` needs a
   set of about fifty children, on which the set decomposition of a five-item pattern
   enumerates `48 · 47 · 46 · 45 · 44` partial assignments per node before the stage is
   reached (hours in a debug build). The bounds are settable from a test (`FlattenBounds`,
   `MatchPool::set_flatten_bounds`, `flatten_bounds.rs`), and the Lean bounds model takes
   them as values (`Bounds` in `RegroupBoundsDefs.lean`). Closes it: a test that lowers the
   bounds over a set node with overlap views. Acceptance: the test asserts
   `flatten_regroup_truncated > 0` and that every reported match is an overlap view, as
   `regroupBoundedO_plan_sound` states.
7. **The cursor matcher's frame stack.** `EMatch/Engine/Cursor.lean` models the AC and ACI
   decomposition frames of `MatchIterator` with their termination and the equality of their
   yields with the executor's decompositions (Section 3.9). The stack above them
   (`next_match`, `backtrack`, the join and sliding-window frames) has no model, so the
   equality of `run_query_iter`'s match multiset with `run_query`'s for a whole plan is checked
   on the rounds corpus and not proved. Closes it: the stack as a step function on a list of
   frames, with the theorem that its yields over a plan are `run`'s by induction on the plan.
   Acceptance: `cursor_matches_eq_run` in `EMatch/Engine/Cursor.lean`, audited in
   `Engine/Check.lean`.
8. **Unit insertion under completion off (documented limit).** With `zero ∋ add{B, D}` the
   view `add{A, C}` of `add{add{A, B}, add{C, D}}` is reached only by inserting the unit and
   regrouping; a chain opens and contracts and never inserts, and insertions have no bound
   (`regroup_insert_unit_lost`, `flatten_regroup_laws_insert.egg`). Nothing closes it in the
   matcher; `(set-option :completion eager)` proves the equality instead. Acceptance: none
   sought; the fixture records the loss and the theorem states it.
9. **The two limits of the overlap stage.** The stage forms neither a view with two overlap
   groups (`{A, C, sab, scd}` of `S{A, B, C, D}`) nor a kept member in a rest variable.
   Closes it: a second overlap step in `RegroupChainO` and a stage that iterates once more,
   counted against the same budgets, with `regroupSkipO_match_iff_laws` restated. Acceptance:
   a fixture with two overlap groups whose `check-eq` holds, and the restated theorem.
   The stage also has a cost the fixtures expose: on a set operator matched by a pattern
   with a rest variable, every node matches with an item bound to one of its own sub-nodes,
   so a right-hand side that grows the set fires many more instances per round
   (`ac_lazy_budget_inconclusive.egg` reaches its budget stop in milliseconds at a 200-node
   budget and in minutes at the default). Whether overlap views should be formed for
   patterns with a rest variable is a design decision to take with the model: restricting
   them is one condition in the stage and the same condition on `overlapStage`, with the
   characterization restated under it. Acceptance: the decision recorded here, the
   conformance samples agreeing, and the fixture at its default budget under a minute.
10. **Completion modulo associativity alone.** `ARound/` has no completeness theorem and none
    is sought: ground completion modulo associativity alone is completion of a string
    rewriting system, a presentation of a finitely presented monoid, whose word problem is
    undecidable (Markov, Post). `a_round` closes one gap (two spellings of a merged class
    inside other sequence nodes) and chases no critical pairs; the development proves
    soundness of the step (`aRound_sound`, `aRoundH_sound`), uniqueness and reachability of
    the least spelling (`isLeastSpelling_unique`, `firstRule_complete`) and termination of
    one round over a finite node set (`aRoundH_wf`). For `:assoc` operators the runtime
    checks establish matching completeness relative to the classes present and nothing about
    completion. Acceptance: none.
11. **The runtime completeness checks.** The design note assigns each hypothesis to a tier;
    of its tier 1 checks two exist in the engine as debug checks (`check_min_monomial_invariant`
    for I5, `debug_check_congruent_dup_invariant` for `hcc`), and the atomic bit, `hcanon`,
    `I0Active`, lattice closure, the `Converged` outcome and the three flatten counters have
    no checker; tier 2 (a proved Lean checker over `dump-egraph` output) is design. Closes it:
    the tier 1 checker behind `:check-complete`, the static checks of `hlaw`, `hnf_ax` and
    `RulesWF`, and the tier 2 checker with its correctness theorems. Acceptance: the note's
    Section 7: each fixture of its tier 1 table fails the corresponding check when its fix is
    reverted, the full suite passes with the option on, and CI runs the tier 2 checker over
    the committed corpora.
12. **Docstrings in the Lean sources that cite drifted lines or renamed files.**
    `Rounds/Round.lean:65-67` and `Rounds/Counter.lean:21-22` say tracking is off in
    `saturate_semi` (`saturate_rules_semi` turns it on for every entry point,
    `egraph/src/saturate.rs:946-950`); `InverseAxiomCP` (`CC/Laws/CriticalPairs.lean:146-149`)
    and `completion_complete_inverse` (`CC/Laws/Main.lean:96-101`) say the engine generates no
    rule-inverse pairs, citing `egraph.rs:3068`, which is inside `a_round` (the engine
    generates them, `egraph/src/egraph.rs:3799-3829`); `Final/Main.lean:131-132` equates
    `Unchanged` with `changes == 0`, which `Fidelity/StopTest.lean` shows insufficient;
    `Flatten/RegroupFits.lean:17-19` says the chain theorems are proved for AC only
    (`Flatten/RegroupChain.lean` proves them for every kind); `CC/Atoms.lean:53` names
    `completion_complete_atom_class` (the theorem is `CompleteAtoms.atom_class`);
    `EMatch/Flatten/RegroupSkip.lean:10` names `regroupSkip_iff` (the theorem is
    `regroupSkipG_iff`); `CC/MinMonoKey.lean:11`, `:215` cite `grow_wa.egg` (the fixture is
    `ac_minmono_grow_wa.egg`); `Fidelity/StopTest.lean:14` cites `s11_self_union.egg` and
    `s11_assoc.egg` (the fixtures are `stop_self_union_mints.egg` and
    `stop_assoc_flatten_mints.egg`); the citations `egraph.rs:4291-4305`
    (`EMatch/Env/Exec.lean:39`) and `apply.rs:1401-1411` (`EMatch/Env/Snapshot.lean:46`) point
    at unrelated code; `spec-flatten.md` (`EMatch/Flatten/Views.lean:6`, `Laws.lean:12`,
    `Main.lean:10`) and `doc/goal-canonical-flatten-views.md` (`egraph/src/nary_canon.rs:4`,
    `seq_collect.rs:252`) are not in the repository. Closes it: one pass over the docstrings
    replacing line numbers by function names. Acceptance: no docstring cites a Rust line
    number, and every fixture a docstring names exists.

Outside the model by design, and not listed as gaps: the engine's `Comm` atom joins through
`by_contains` as AC does (`egraph/src/schedule.rs:749`), where the model's `byContains`
ignores pairs and adds a `decomposeComm` step with no Rust counterpart; guards, literals and
globals have per-step theorems only (Section 3.8); `Flatten/` feeds nothing above it, so
`:flatten` and sequence rules across rounds are not modelled; `ARound/` uses its own state,
not `State`, and joint termination with AC rounds is not proved; emitted lists are compared
as sets (`Nodup` is not modelled beyond single steps); the build-time spelling of an AC
right-hand side (`flatten_mset_children`, which reads each argument class's `atomic` bit and
minimal monomial) is outside `saturation_complete` and covered by `spelling_epoch`; the
galloping cursor is verified separately in Verus (`containers-verus`).

## 10. Constraints on the engine, with their evidence

Each entry is a rule the engine keeps, the failure without it, and the evidence for it: the
counter-model theorem, the fixture, or both. "Completeness" means a theory-equal pair left in two classes or a match left unfired;
"soundness" means a merge of two terms the theory keeps apart.

**Must refresh the stored minimal monomial when recanonicalization shrinks a node.**
Otherwise the stored minimal monomial is no longer the class's least active monomial, the
orientation check drops the class's rule, and a theory-equal pair stays in two classes (I5
fails; completeness). Evidence: counter-model `shrinkNoRefresh_breaks_I5`
(`CC/Slot.lean:327`), the reproducer `proofs/repro/min-slot-gap.egg`, fixture
`ac_min_slot_refresh.egg`. The engine's refresh is `refresh_min_monomial`; `reachable_I5`
proves the operations with it keep I5.

**Must order monomials by a per-class key that a merge only lowers, not by representative
id.** Otherwise a merge that keeps the larger id renames a child upward, a stored node grows
past its classmate, and the class's rule is mis-oriented or lost (completeness). Evidence:
counter-model `idOrder_grow_breaks_I5` (`CC/MinMonoKey.lean:250`), fixtures
`ac_minmono_grow_wa.egg`, `ac_minmono_grow_aw.egg`, `ac_key_survivor_lowered.egg`.
`keyed_reachable_I5` proves that under the keys each recanonicalization is a
no-op or a shrink (`merge_recanon_op`).

**Must refresh the minimal monomial after re-activating a collapsed node.** Otherwise the
stored minimal monomial stays on a node the next round collapses, I5 fails and the class's
rule is lost (completeness). Evidence: counter-model `unretireNoRefresh_breaks_I5`
(`CC/Slot.lean:364`), fixture `ac_reactivate_min_monomial.egg` (reduced from
`conform-cc-cert/cs1_0129.egg`, located by `check_min_monomial_invariant`).
`unretire_refresh_I5` proves the refreshed re-activation keeps I5.

**Must clear the collapsed flag when a node becomes irreducible, at materialization and at
recanonicalization.** Otherwise a node that has become a normal form is never a superposition
source and its consequences are not generated (completeness; `RoundFixed.nf_present` asks
the normal form to be an active node). Evidence: fixture `ac_collapsed_recanon.egg` (reduced
from `conform-cc-cert` seed 1004, case 655, in which `C5 = C5·C5` is derived after
`C2 = C3` only with the flag cleared). The model's step is `Infer.unretire`; the condition
that no current rule reduces the node is the engine's, and `RoundFixed.nf_present` is what
needs it.

**Must merge a node's normal form into its class before flagging the node collapsed.**
Otherwise a retired node's reduct is in no class with it and the equality it carried is lost
(I3 fails; `completion_complete_at_convergence` and `nodes_reduce_all` in
`CC/Laws/InvRulesMain.lean` need I3). Evidence: no reproducer, because `cc_round` calls
`do_merge` before `set_cc_collapsed`; the rule is recorded in
`06-ac-congruence-closure.md`, Section 9c, so that a refactoring keeps the order. `witness_I3` checks I3 on the atoms witness.

**Must keep the active rules a reduced basis: retire every rule whose left-hand side
contains another's.** Otherwise reducible rules become superposition sources, breed rules
that contain the same left-hand side, and the run diverges; the termination argument
(`kapur_termination`, Dickson's lemma over a reduced antichain) does not apply, and a
diverging run never reaches the state at which completeness holds. Evidence: the divergence
of the no-collapse form on committed reproducers (`06-ac-congruence-closure.md`, Section 6b),
fixture `cc_containment_chain.egg` (two containing pairs that join only through the
reducibility pass). `RoundFixed.lhs_reduced` states the pass's result.

**Must include the reducibility pass and the superposition of every non-containing
overlapping pair in the confirmation round, and skip disjoint and containing pairs only.**
Otherwise the reported fixpoint is not `RoundFixed`, `hcp_of_fixed` does not apply, and
completeness at convergence is not established. A disjoint pair has a critical pair that
joins by one step of each rule, and a containing pair is retired by the reducibility pass;
skipping any other pair loses a critical pair. Evidence: `RoundFixed` with `lhs_reduced` and
`cp_joinable` over non-containing pairs, `ruleRuleCP_of_fixed`; `conform-cc/cc1_0143.egg`,
on which the use lists yield a disjoint partner under the clamp, which the loop skips rather
than rejects with a `debug_assert`.

**Must close a cancellative operator with `lattice_round` at the completion fixpoint, and
not rely on the cancel inferences.** Otherwise theory-equal pairs whose derivation needs
several copies of an equation stay in two classes (completeness), and the hypothesis
`hcancel` is not an engine fact. Evidence: fixture `cancel_lattice.egg` (the inferences alone
converge without `C5 = c1c3²`, which needs `c1c4² = c0²` and two copies of `c4 = c0c3`),
`cancel_crit_pair.egg`, `cancel_lattice_lazy.egg`, `nilpotent_group_lattice.egg`;
counter-model `hcancel_not_derivable`
(`CC/Lattice.lean:725`). `completion_complete_cancellative_engine` takes lattice closure in
place of `hcancel`, and `latticeClosed_of_engineFixed` gives it from the step's fixpoint.

**Must apply the inverse rules R1 to R5 at rebuild and generate the rule-inverse critical
pairs.** Otherwise the four conditions the inverse completeness theorem needs
(`InvMatching`, `InvUnitFree`, `InverseAxiomCP`, `NilpotentInverseCP`) fail, and
consequences such as `d + neg(a) = c` from `a + c = d` are missed (completeness). Evidence:
counter-models `invGen_cp_not_joinable` (`CC/Laws/Inverse.lean:512`) and
`combined_counterexample` (`CC/Laws/Combined.lean:160`), the four reproducers
`proofs/repro/inv-into-unit.egg`, `unit-inverse.egg`, `rule-inverse-cp.egg`,
`z3-inverse.egg`. `completion_complete_inverse_engine` derives the four
conditions from the rules' fixpoints (`invMatching_of_fixed` and the three others).

**Must rewrite a fold's spelling in `a_round` only at a prefix of a left fold and a suffix
of a right fold.** Otherwise the rewrite spells a different term and merges two terms the
fold keeps apart (`(X - A) - B = (X - C) - D` from `A - B = C - D`; soundness). Evidence:
counter-models `left_off_spine_unsound`, `right_off_spine_unsound`
(`CC/ARound/Basic.lean:390`, `:420`), fixture `ac_fold_completion_spine.egg`.
`rewrite_left_sound` and `rewrite_right_sound` prove the spine rewrite sound in
every magma, and `aRound_sound` that it keeps I2.

**Must open and regroup a fold's views on its spine only.** Otherwise a `:flatten` view
spells a different term and a rewrite on it merges unequal terms (soundness). Evidence:
counter-models `fold_open_off_spine_unsound` (`Flatten/Fold.lean:219`) and
`regroup_off_spine_unsound` (`Flatten/RegroupSound.lean:527`), fixture
`flatten_fold_spine.egg` (its `(check-neq (Sub (A) (Sub (B) (C))) (Tri (A) (B) (C)))` fails
with "terms are equal" when a view opens off the spine). `otLeft_sound`, `otRight_sound`,
`regroup_views_sound_left` and `regroup_views_sound_right` prove the spine views sound in
every magma.

**Must keep a `:flatten` match whose unsatisfied leaf opened a class an item takes.**
Otherwise the demand rule rejects a match that lives on no less-opened view, because
closing the leaf coalesces the opened class with the taken one into an entry of count two,
which no unannotated item takes (completeness of flattened matching). Evidence: the eval
counter-model in `Flatten/FixCheck.lean:39-64`, reproducer `proofs/repro/demand-gap.egg`,
fixture `flatten_demand_refold.egg`.
`demand_fix_complete_ac` proves the corrected rule complete up to refolding.

**Must keep a `:flatten` match whose unsatisfied leaf is not inert under the laws.**
Otherwise a leaf that contributes only through the unit drop, the nilpotent clamp or an
inverse cancellation is rejected although the refolded view is smaller or is no node
(completeness under `:identity`, `:nilpotent` and `:inverse`). Evidence: the five eval
counter-models in `Flatten/LawsCheck.lean`, fixtures `flatten_laws_nilpotent.egg`,
`flatten_laws_inverse.egg`, `flatten_laws_inverse_leaf.egg`, `flatten_laws_identity.egg`,
`flatten_laws_assoc_unit.egg`.
`demand_laws_complete_ac` proves the rule complete under any laws, and `nonInertEng_eq` that
the engine's flag is the model's.

**Must keep every leaf of the walk under an identity, and flag a leaf that gains a class
the normalization drops.** Otherwise the walk prunes a leaf that a later regrouping makes
non-inert, and the match on the regrouped view is lost (completeness). Evidence: fixture
`flatten_regroup_laws_drop_need.egg` (fourth case, a leaf of the walk), theorem
`regroup_drop_need_leaf` (`Flatten/RegroupLaws.lean`), `mayNonInert_of_canDrop` and
`prune_engine`; the engine's `may_be_non_inert` keeps every leaf under an `:identity`.

**Must make a regrouped record need only the classes its normalized view still holds.**
Otherwise a record needs the group's class after the laws dropped it (the unit, a count
clamped to zero, a cancelled inverse), no item can take it, and the match is lost
(completeness under laws). Evidence: fixture `flatten_regroup_laws_drop_need.egg`
(`(add x y)` binds `x = C, y = D` in `add{A, B, C, D}` with `zero ∋ add{A, B}`), theorems
`regroup_drop_need_unit`, `regroup_drop_need_nilpotent`, `regroup_drop_need_inverse`,
`reach_needs_held` (`Flatten/RegroupLaws.lean`); the engine and the model compute the
needed classes the same way (`needsAfter`).

**Must regroup an item-less n-ary pattern when the laws can drop a class.** Otherwise
`(f ..r)` misses the view `{C, D}` of `add{A, B, C, D}` with `zero ∋ add{A, B}`, a record that
needs no class and that only a law can produce (completeness). Evidence: fixture
`flatten_regroup_laws_no_item.egg`, theorem `mem_base_of_reach` (`Flatten/RegroupBounds.lean`,
a laws-free operator produces no such record, so laws-free operators need not regroup for
it), the engine's `laws_drop` and the model's `canDrop`.

**Must apply the item limit to the final records only, never at each regrouping.**
Otherwise a chain through a record that needs more classes than the pattern has items is
cut, although a later regrouping absorbs the needed classes, and the match through the
nested group is lost (completeness). Evidence: `regroup_nested_matches`
(`Flatten/RegroupNested.lean:81`: `{a, b, c, d, h, k}` through `{h, k, G1, G2}`, which needs
two classes, to `{h, k, G3}`), fixture `flatten_regroup_nested_needs.egg`.
`regroup_match_iff` bounds the final record only (`r.2.2.length ≤
a.elems.length`), and the cost is not measurable (`07-rules-and-pattern-matching.md`, §7.5).

**Must count a saturated view size, a truncation and a skipped node as a loss of
exactness.** Otherwise a count read as `u64::MAX` can make a regrouped view appear no
smaller than its source and let the skip of a regrouped target fire, and a truncated or
skipped node silently loses matches; in both cases the match set is no longer
`regroupSkip_match_iff`'s, and nothing reports it. Evidence: `saturated_size`
counts a count past `u64::MAX` in `flatten_overflowed`, with a unit test; the hypothesis `hz` of `regroupBounded_query_exact` (the three counters zero), and the model's
`Ix.wide`. The design note assigns the three counters to tier 1.

**Must never store a set node whose normal form is one class, and merge a stored one into
that class at rebuild.** Otherwise a raw view collapses to a single class after the unit
drop, `TwoClassesL` fails, and the demand rule for sets loses a match (completeness of
`:flatten` matching on ACI operators). Evidence: fixture `aci1.egg` (`z = And{x, s}`,
`n = And{x, z}`, `s ∪ Tru` merges `z` and then `n` with `x`), theorem `twoClassesL_of_members`
(`Flatten/EngineComplete.lean:314`). `demand_engine_complete_aci` takes
the invariant as a hypothesis.

**Must collapse a one-element normal form into its class, and keep the `atomic` bit equal
to "a child of a stored node, or a class with no node of the operator".** Otherwise a node
theory-equal to a leaf constant `{x}` stays out of `x`'s class, or a class is spliced where
its rule should rewrite (completeness on graphs with leaf constants). Evidence:
`AtomCollapse` derived from `AddFixed` (`atomCollapse_of_addFixed`, `CC/AtomicOf.lean`),
`atomicOf`, the five fixtures `atomic_bit_child_before_and_after_node.egg`,
`atomic_bit_inverse_after_splice.egg`, `atomic_bit_last_node_collapses.egg`,
`atomic_bit_leaf_gains_node.egg`, `atomic_bit_merge_spliced_side.egg`; `witness_atomicOf` checks the bit on the atoms witness.

**Must track merge members in the delta (`merge_in_classes`) under semi-naive matching.**
Otherwise a merge whose survivor is the id the parent already stores recanonicalizes no node,
a new match has no new scanning node, and no variant emits it (completeness of saturation).
Evidence: counter-model `delta_incomplete_untracked` (`Rounds/Counter.lean:184`), fixture
`semi_merge_membership_delta.egg`; `saturate_rules_semi` turns tracking on for every entry
point.

**Must route a rule that constrains a class variable to a global's class to the naive
matcher.** Otherwise the absorbed class's members enter the delta but no atom scans them,
and the new match is never emitted (completeness). Evidence: counter-model
`delta_incomplete_global` (`Rounds/Counter.lean:98`), fixture `semi_eq_global_local.egg`,
the engine's `needs_naive_match`.

**Must re-match the rules that build an n-ary term in full after a rebuild applied a law to
a stored node or changed a build-time spelling, when completion is off.** Otherwise a fired
instance whose right-hand side is built through a node the unit drop, the clamp or a
collapse rewrote is no longer present, no delta records the change, and the fixpoint is
reached with an unfired match (completeness). Evidence: counter-model `denN_persist_fails`
(`Fidelity/Recanon.lean:410`), fixtures `semi_recanon_unit_drop.egg`,
`semi_recanon_idem_collapse.egg`, `semi_recanon_inverse_cancel.egg`,
`semi_recanon_pending_collapse.egg`, `semi_naive_atomic_semi.egg`, `semi_naive_minmono.egg`,
the engine's `VarCanon::law_applied` counted in `spelling_epoch`, and the `respelled`
re-match. The chains `AChain` and `SChainN` take the routing as a hypothesis. With
completion on no re-match is needed: the old node and the new spelling are equal in the
theory and the completion fixpoint joins them (`saturation_complete_closed`,
`Fidelity/RecanonComplete.lean`; fixture `semi_recanon_completion_on.egg`).

**Must splice a same-operator child with its canonical children.** Otherwise `add` builds a
sequence node from the stale stored children of the spliced child, two nodes of equal
content end in two classes, `Round.WF.dedup` fails, and congruence misses an equality.
Evidence: counter-model `raw_breaks_dedup` (`Rounds/SeqSplice.lean:292`), fixtures
`seq_hashcons_miss_min.egg`, `rounds_r1_0581.egg`; `dedup_of_inv` derives `dedup` for the
store that splices canonical children.

**Must stop saturation only when no action reported a change and the size stamp did not
move.** Otherwise a union that minted nodes and reported zero changes stops the loop before
the fixpoint, with matches unfired (completeness). Evidence: fixtures
`stop_self_union_mints.egg`, `stop_assoc_flatten_mints.egg`, the engine's `size_stamp`;
`engine_stop_unchanged` (`Fidelity/StopTest.lean`) proves the test implies `Unchanged` and
`Phase.stamp_ne` the converse.

**Must report completeness only on a `Converged` outcome, never on a budget stop.**
Otherwise the round matches on a store that is not a completion fixpoint, `before_fixed`
fails, `rebuild_idle` does not apply, and the saturation theorems say nothing. Evidence:
`CompletionRun` and `CompletionOutcome` (`Fidelity/StopTest.lean`),
fixture `ac_lazy_budget_inconclusive.egg` (a `check-neq` reported inconclusive after a budget
stop). The runtime design note asks for `Converged` before any check.

**Must keep a collapsed node a member of its class, reducible by the rules to an active
node of that class.** A collapsed node stays in the index and is matchable, so `FCover`
over the active nodes fails on it and `saturation_modulo_complete_store_cover` has no
witness on such a run (`not_cover`, `Final/Witness.lean:666`). The match it yields is
covered by `saturation_modulo_complete_store_retired` because the retired node is still a
member of its class (`SubRepR`) and rewrites to an active node of it (I3, `I2`): its root
binds that node's class, so the match is sound, and the active node yields the same match
at the class level, so completeness is unaffected. What the engine pays is time: the match
rooted at the collapsed node builds nodes `=_E`-equal to the ones the active match builds,
which completion or hash-consing joins. Evidence: `witness_fires_retired`
(`Final/Witness.lean`).

**Must run the eager pass after the last scanning atom, to its fixpoint, before the plan
ends.** Otherwise an equality that the last join frees is never checked or copied: the plan
emits bindings that violate it (soundness of matching; `SchedA.done` asks that no unused atom
be free), and a variable bound only through that equality is never bound, so the rule's
actions read an unset variable. A single sweep is not enough: `(= a b)` passed over before
`(= b c)` is free only on the next sweep. Evidence: the `done` case of `schedLoop_schedA`
through `eagerFix_fixed` (`EMatch/Engine/Schedule.lean`); the mutation of the transliteration
that runs the eager pass before the first pick only disagrees with the engine on 458 of 2679
corpus plans, and the one that sweeps once leaves `(= a b)` unlowered in
`eager_chain_agrees_with_the_model` (`schedule.rs`). The engine's loop runs `lower_eager`
at the top of every iteration, including the one that finds no candidate.

**Must not expect regrouping to find a normal form reached only by insertion.** With
`zero ∋ add{B, D}`, `add{A, C}` equals `add{add{A, B}, add{C, D}}`, but a chain of
regroupings opens and contracts and never inserts, and insertions have no bound; the match
is lost by design, and `(set-option :completion eager)` proves the equality instead.
Evidence: `regroup_insert_unit_lost` (`Flatten/RegroupLaws.lean:1363`), fixture
`flatten_regroup_laws_insert.egg`. A documented limit of the regrouping guarantee, not a
defect.

**Must keep a set group beside its class only as many members as the pattern asks for.**
`S{A, B, C}` equals `S{A, C, sab}` by idempotence, and regrouping alone never forms that
view (`regroup_idem_overlap_loop_lost`, `Flatten/RegroupLaws.lean`): `(S x y z)` missed
`x = sab, y = A, z = C` (completeness relative to the classes present). Keeping every subset
of the members would multiply the views by up to `2^|group|`; the engine's overlap stage
keeps exactly `|items| - 1 - (|view| - |group|)` of them, one family of `C(|group|, k)`
views per group, and counts each raw fit and each record against `MAX_REGROUP_WORK` and
`MAX_REGROUP_VIEWS`, so a large family truncates the node and the run reports it instead of
enumerating `2^|group|` views. Evidence: `regroup_idem_overlap_found`,
`regroupSkipO_match_iff_laws`, `regroupBoundedO_query_exact`
(`Flatten/RegroupOverlap.lean`, `RegroupOverlapBounds.lean`), the fixture
`flatten_regroup_laws_idem.egg` (the match the stage forms), the regenerated conformance
samples (Section 8). Cost: nothing for an operator without idempotence, since the stage is
guarded by the kind; for a set operator one more read of the use lists per view of the loop
and the binomial families, both bounded.

**Must not seek a completeness theorem for completion modulo associativity alone.** The
problem is completion of a string rewriting system, and the word problem for finitely
presented monoids is undecidable (Markov, Post), so no algorithm decides every equality
associativity entails; `a_round` closes one gap and chases no critical pairs. Evidence:
`06-ac-congruence-closure.md`, Section 14; `ARound/` has soundness (`aRound_sound`,
`aRoundH_sound`), the least spelling (`isLeastSpelling_unique`, `firstRule_complete`) and
termination of one round (`aRoundH_wf`), and no completeness theorem; the runtime design
note establishes matching completeness relative to the classes present for `:assoc`
operators and nothing about completion.
