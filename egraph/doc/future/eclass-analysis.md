# E-Class Analysis with Verified Abstract Domains

**Status**: design for future work; nothing in this document is
implemented. This document lists the integration options for attaching
abstract values to e-classes and states which one I propose and why. It is
not a specification of the abstract domains themselves: those live in
`abstract-domains/doc/` and the reduced-product protocol in
`abstract-domains/doc/reduced-product.md`.

## 1. Goal

Attach to every e-class of an interpreted sort an abstract value that
over-approximates the set of concrete values the class can take in any model
of the asserted equalities. Bool classes carry a Boolean value, Int classes
carry ℤ domains (interval, congruence, a nonzero flag), and bit-vector
classes carry machine-word domains of the matching width.

Four events change these values:

- **make**: a node `f(c1, …, cn)` enters a class; its forward transfer
  evaluates `f` on the children's values.
- **merge**: two classes become one; both values describe the same concrete
  value, so the new value is their **meet** in set order, followed by a
  reduction among the domains.
- **child refinement**: a child's value shrinks; every parent node's forward
  transfer runs again.
- **parent refinement**: a class's value shrinks; each of its nodes runs a
  backward transfer that refines its children.

A merge whose meet is empty proves that the asserted equalities have no
model. A class whose value becomes a singleton can be merged with the
constant, and a Boolean class whose value becomes `true` or `false` can be
merged with that literal.

**Order convention.** This document orders values by set inclusion of their
concretizations, so a merge takes the meet. Egglog and
[lattice-functions.md](lattice-functions.md) order values by information
and call the same operation a join. The two descriptions agree; only the
names of the operations swap.

## 2. Relation to Verasco

The e-graph plays the role of Verasco's symbolic-equality domain
(Jourdan et al., POPL 2015, §6.4), with congruence closure and any number
of terms per class instead of one equation per variable. Verasco's
numerical domains query that domain through `get_eq_expr` and answer
interval queries through `get_itv` (§7). Here the same two directions
exist:

- the e-graph tells a value domain which nodes a class contains, which
  drives forward and backward transfers;
- a value domain tells the e-graph facts about a class, and, unlike in
  Verasco, those facts can come back as equalities (constants, decided
  conditions, decided `ite` branches).

Verasco's example (§6.4) is the case this design must handle:
`t2 = (t1 > 0) ? (y < z) : 0` and `t2 = true` imply `t1 > 0` and `y < z`.
That inference is the backward transfer of `ite` described in §6.

## 3. Requirements

1. **Soundness.** For every model `M` of the asserted equalities and every
   class `c`, `M(c)` is in the concretization of `c`'s value. Each transfer
   and each merge preserves this invariant.
2. **Rollback.** `pop` restores every value to its state at the matching
   `push`, together with the classes themselves.
3. **Change detection by equality.** Each domain has one representation per
   set, so the engine decides "did the value change" with `==`, and only a
   strict change schedules further work.
4. **Termination.** Values only shrink, but descending chains can be
   infinite (Int: `x = x + 1` shrinks `[0, ∞)` to `[1, ∞)`, then `[2, ∞)`,
   and so on) or exponentially long (bv64: 2^64 steps). Propagation needs a
   budget; the budget may cost precision but never soundness.
5. **Semi-naive completeness.** A value change that creates no node and
   merges no class must still reach the next semi-naive round, as
   [lattice-functions.md](lattice-functions.md) already requires for its
   tables.
6. **Verified core.** Domains, transfers, meets and reductions are verified
   in `abstract-domains`; the storage is verified in the class layer. User
   extensions carry the same trust as rewrite rules and nothing more.

## 4. Storage

**Proposed: a handle in `ClassData`, values in per-sort pools.**
`ClassData` already stores `min_row: Option<usize>`, an offset into
`min_pool`, a semi-persistent pool that is marked and restored with the
sparse set, and `MergeInfo` already returns `absorbed_min_row` so that
`EGraph` combines the two pool entries. The analysis follows the same pattern:

```rust
pub struct ClassData<L, T> {
    pub use_list: L,
    pub min_row: Option<usize>,
    pub abs: Option<AbsRef>,   // (sort tag, offset into that sort's pool); None: no analysis
    pub atomic: bool,
    ...
}
```

On a merge, `MergeInfo` returns `absorbed_abs`; `EGraph` computes the meet
and the reduction, writes the survivor's pool entry with a tracked write, and
records the class as changed if the value changed. The `containers` crate
stores opaque pool entries and does not depend on `abstract-domains`.

| Option | Rollback | Merge | Cost | Verdict |
|---|---|---|---|---|
| Value inline in `ClassData` | free | free | every class pays for the largest value (about 100 bytes for a u128 product, 1 byte for a Boolean); `IBig` is not `Copy`; swap-remove copies the value | **rejected** |
| Separate map from class to value | a second mark and restore that must stay in step with the union-find | the map must be re-keyed when the representative changes | one extra lookup per access | **rejected**: it can disagree with the union-find after a merge |
| Handle in `ClassData`, per-sort pools | the handle rolls back with the class, the pools with the same mark | same shape as `absorbed_min_row` | one field per class | **proposed** |
| A lattice-function table `(function abs (S) Dom :merge …)` keyed by the class | provided by the table design in [lattice-functions.md](lattice-functions.md) | a merge must also merge the two keys' entries, which the table design does not cover | a table lookup per access | **postponed**: revisit if the lattice table is built first and its key canonicalization can absorb class merges |

`IBig` bounds do not fit a `Copy` pool. Two ways out: saturating `i128`
bounds, where a bound that does not fit becomes infinite (sound, because it
rounds outward), or an append-only `IBig` side arena whose entries the pool
references. I propose saturating `i128` for the first version and measuring
how often a bound saturates on the benchmark set before deciding on the
arena.

## 5. Choosing domains per sort

Domains apply only to sorts with a concrete interpretation. Today the
concrete sorts come from the `LitModel` (`IBig`, `bool`, `i64`, `u64`, and
others), and user sorts such as `(sort Expr)` are uninterpreted. Three
options:

**Option A: domains belong to the literal model.** Each `LitSortDesc`
declares its domains, and analysis runs on classes of literal sorts only.
No new syntax. A user who wraps `IBig` in a constructor (`(Num IBig)`) gets
no analysis on the wrapping sort.

**Option B: user sorts declare an interpretation and a domain set.**

```lisp
(sort Bool :interp bool         :domains (bool))
(sort Int  :interp int          :domains (interval congruence nonzero))
(sort BV32 :interp (bitvec 32)  :domains (ubounds sbounds congruence bits))
(sort Expr)                                       ; uninterpreted: no analysis
```

`:interp` names the concrete carrier and fixes the `Semantics` the transfers
use; sortcheck rejects `:domains` on a sort without `:interp`.

**Option C: domain sets as named profiles.**
`(analysis int-default (interval congruence nonzero))` and
`(sort Int :interp int :analysis int-default)`, so benchmarks can switch a
whole configuration by name.

**Proposed: B, with defaults.** B is the only option that covers SMT-style
user sorts. Each `:interp` carrier has a default domain set, and
`:domains ()` disables the analysis for one sort. C is sugar over B and can
come later.

**Implementation of a domain set.** The per-sort fact record (`Facts<W>`,
`FactsZ`) always contains every field, and `:domains` is a bit mask. A
disabled field stays at top and its reduction steps are skipped. This avoids
one compiled type per subset of domains, and every mask is sound because top
is always a sound value.

**Bit-vector widths.** SMT-LIB allows any width, while the verified `Word`
covers u8 to u128. Options: a const-generic `Bits<const N: u32>(u128)`
implementing `Word` with modulus 2^N (all widths from 1 to 128, top above
128); a width stored in each value (this breaks `W::modulus()` as a static
spec function); or native widths only, with top for every other width.
I propose `Bits<N>`.

## 6. Propagation rules

Each function symbol needs a way to say how values flow through it. I
propose three tiers, ordered by where their soundness comes from.

**Tier 1: interpreted symbols, verified transfers.**

```lisp
(function bvadd (BV32 BV32) BV32 :interp bvadd)
(function ite   (Bool Int Int) Int :interp ite)
(function lt    (Int Int) Bool    :interp <)
```

`:interp` maps the symbol to a library operator with a verified forward
transfer and a verified backward transfer. The engine runs the forward
transfer when a child's value changes and the backward transfer when the
node's class changes. The user does not choose triggers. Signedness is a
property of the operator (`bvslt` against `bvult`), as in SMT-LIB.

The `ite` rules, for a class with value `R` containing `ite(c, t, e)`:

| Known | Conclusion |
|---|---|
| `meet(R, val(e))` is empty | `c` is true; `val(t) := val(t) ⊓ R` |
| `meet(R, val(t))` is empty | `c` is false; `val(e) := val(e) ⊓ R` |
| both are empty | conflict |
| `c` already known true | `val(t) := val(t) ⊓ R` |
| otherwise | nothing |

Soundness needs only that an empty meet implies disjoint concretizations,
which every domain's meet contract already states. How often the rule
fires depends on how often the meet detects an empty intersection, and any
component of a reduced product can detect it (an even value against an odd
branch decides `c` even when the intervals overlap).

**Tier 2: defined symbols, no new mechanism.**

```lisp
(function clamp (Int Int Int) Int)
(rewrite (clamp x lo hi) (ite (lt x lo) lo (ite (lt hi x) hi x)))
```

Once the rewrite fires, the `clamp` node and the `ite` node share a class,
and the tier 1 transfers of `ite` and `lt` propagate through the merge in
both directions. Soundness comes from the definition and the verified
transfers. This is the main difference from a classical abstract
interpreter: a definition becomes propagation without a transfer function
written for `clamp`.

**Tier 3: custom facts, trusted like rewrite rules.**

```lisp
(function hash (BV32) BV32 :range (0 1023))                ; unconditional fact on results
(rule ((= r (scale x)) (within x 0 9))                     ; abstract test in the body
      ((refine r (interval 0 99))))                        ; abstract fact in the head
```

`:range` is shorthand for a guard-free rule. A rule body can test abstract
facts next to ordinary patterns and the existing primitive guards, and a
rule head can `refine` a class. `refine` goes through the same meet,
reduction and conflict path as a merge. The user is responsible for the
head being true, exactly as for the right-hand side of a rewrite.

**Triggers for tier 3 come from semi-naive evaluation.** A rule fires again
only when a class it matched or tested changed its value in the previous
round. This covers "fire when a particular child moves" without per-rule
trigger annotations, provided value changes enter the touched log
(requirement 5).

**Alternatives considered.**

| Alternative | Why it loses |
|---|---|
| Per-symbol transfer expressions in an annotation language (`:forward (+ (itv a) (itv b))`) | duplicates the verified library in an unverified language; tier 2 covers definable symbols |
| User-chosen triggers per child (`:on (child 0)`) | semi-naive deltas already restrict firing to changed inputs; explicit triggers add a way to miss an update |
| Only literal-model primitives get transfers (no `:interp` on user symbols) | leaves SMT-style user signatures without propagation |

## 7. Scheduling and termination

Rebuild processes three queues: merges (meet and reduce), forward work
(parents of changed classes), and backward work (nodes of changed classes).
Each class has a budget of strict changes per `run` iteration; when the
budget is spent, the class stops scheduling further work until the next
iteration. Because every step keeps a sound value, the budget affects
precision only.

The reduction inside a value (§2 of `reduced-product.md`) has its own small
budget and the property that it never changes the concretization, so its
budget also affects precision only.

**Open: budget scope.** One budget per class per iteration, one global
budget per rebuild, or both. This interacts with semi-naive scheduling and
needs measurement on the benchmark set before a decision.

## 8. Merges derived from abstract values

**The rule: equal singletons, not equal abstract values.** The analysis may
merge two classes only when their values prove that the classes are equal in
every model. With non-relational values, this holds exactly when both values
concretize to the same single value. Equal abstract values are not enough:
`x ∈ [0, 10]` and `y ∈ [0, 10]` hold for `x = 1, y = 2`, so merging `x` and
`y` would assert an equality that some models violate. The same applies to
every domain in this design: two classes with congruence value `odd`, or two
bit-vector classes with the same known bits and some unknown bits, are not
equal.

| Values of classes `a` and `b` | What follows in every model | Action |
|---|---|---|
| `γ(a) = γ(b) = {k}` | `a = k = b` | merge both with the constant `k` |
| equal values, not singletons | nothing | none |
| `meet(a, b) = ⊥` | `a ≠ b` | record the disequality; merging them later is a conflict |
| overlapping, not singletons | nothing | none |

**Sources of derived merges.** Every derived merge reduces to "this class has
a singleton value" or to an equality the e-graph already accepts:

1. **Constant.** A class whose value is a singleton `{k}` is merged with the
   literal node for `k`. Two classes with the same singleton then share a
   class through the literal, so no pairwise comparison of values is
   needed. This is constant folding by analysis: the value became a
   singleton through meets and transfers, not through evaluating a ground
   term.
2. **Decided Boolean.** A Boolean class whose `Bool4` value is `True` or
   `False` is a singleton and is merged with `true` or `false`. This is case
   1 for the Boolean sort.
3. **Decided `ite`.** A class containing `ite(c, t, e)` whose condition class
   is decided is merged with `t` or `e`. This follows from case 2 and the
   congruence rule for `ite(true, t, e) = t`, so it needs no separate
   argument. The condition can be decided by the backward `ite` rule of §6,
   which is where the value of the `ite` class itself decides a branch.
4. **Inverse of an interpreted operator.** Some operators let a singleton
   value prove an equality between other classes. If the class of `sub(a, b)`
   has value `{0}`, then `a = b`; this holds over ℤ and modulo 2^N, because
   `a - b ≡ 0 (mod 2^N)` implies `a = b` for N-bit values. The same holds
   for `xor(a, b) = {0}` and for `eq(a, b) = {true}`. These are tier 1
   facts of the operator, stated next to its transfers and verified with
   them.
5. **Guarded rewrites.** A rewrite whose guard reads abstract facts,
   `(rewrite (Div x x) 1 :when ((nonzero x)))`, merges classes when the
   guard becomes true. The merge is as sound as the rewrite under its
   condition, and the guard is sound because it reads a verified value. This
   is the case the stripped Herbie analysis needs
   ([herbie.deviations.md](../../../doc/benchmarks/ledgers/herbie.deviations.md)
   §1: 12 rewrites guarded by `non-zero`).

**Disequalities.** An empty meet between two classes proves `a ≠ b` in every
model. The analysis does not merge anything on this basis. It can answer
`(check (!= a b))`, feed guards that test disequality, and turn a later merge
of `a` and `b` into a conflict. Disequality is the only fact the analysis
derives from non-singleton values.

**When the merges happen.** Derived merges are queued during propagation and
applied as one batch after it, never during it, because a merge changes the
classes that propagation is iterating over. A `run` iteration then repeats:
rebuild for congruence, propagate values within the budget of §7, apply the
queued derived merges, and rebuild again. A derived merge is an ordinary
merge for semi-naive evaluation: it enters the touched log as class growth.
A guarded rewrite whose guard becomes true through a value change, with no
node created and no class merged, must re-fire in the next round; this is
requirement 5.

**Soundness.** Every value over-approximates the class in every model
(requirement 1). A singleton value therefore fixes the class to one value in
every model, and the derived equality holds in every model. A derived merge
adds no constraint that the asserted equalities did not already imply.

**What case 1 needs from the literal model.** Merging with `k` needs a
literal node for `k` in the class's sort. `IBig` and `bool` literals exist
today. Bit-vector widths other than the `MachineModel`'s `u64` and `i64` have
no literal sort yet, which ties case 1 for bit-vectors to the width decision
of §5.

**Explanations.** With proof logging enabled, each derived merge needs a
`Justification`. Two options:

- **Dependency tracking.** Each value records the merges and nodes it
  depends on, and the justification lists them. Exact, but it costs memory
  on every refinement.
- **Trusted analysis step.** A new justification kind, `Analysis`, states
  that a verified transfer or meet produced the equality, without a
  derivation. Cheap, and the trust is limited to the verified library, but
  `explain` cannot reconstruct the reason.

**Open**: which one, and whether the second is acceptable for the proof
certificates the engine produces.

**Beyond singletons.** Equalities between classes whose values are not
singletons need relational information. Labeled union-find (§11) records
`y = x + c` as a labeled edge instead of a merge, and turns two different
labels between the same classes into constants. It is postponed for the
reasons in §11.

## 9. What stays outside this design

- The domains, transfers and reduction protocol: `abstract-domains`.
- Relational domains (linear inequalities, octagons): out of scope; the
  e-graph is the relational component.
- Lattice-valued functions as user tables: [lattice-functions.md](lattice-functions.md).
  §11 compares the two and proposes an order.

## 10. Acceptance criteria

- One sort (`Int` with intervals) runs through declaration, make, merge,
  backward `ite`, conflict, push and pop, with no new `admit`, `assume` or
  trusted contract in the class layer.
- A regression shows a value-only change reaching the next semi-naive round.
- A regression shows `x = x + 1` over `Int` terminating within the budget
  with a sound value.
- Naive and semi-naive evaluation reach the same values on generated finite
  traces.
- Benchmarks report the cost of the analysis per merge and per rebuild
  against the same programs without `:domains`.

## 11. Related work

Four lines of work cover parts of this design. None covers all of it.

**Coward, Constantinides and Drane, "Abstract Interpretation on E-Graphs"
(extended abstract, arXiv:2203.09191, 2022).** Implements interval
arithmetic over reals as an egg e-class analysis. Its contribution is the
merge rule this design uses: the nodes of a class are equal in every model,
so the class value is the meet of the node values, `⟦c⟧ = ⊓ₙ ⟦n⟧`. On their
examples, rewrites that remove repeated variables tighten bounds by 31% to
93% of the interval width (their Table 1, x, y ∈ [1, 2]). The analysis
propagates only from children to parents, uses one domain, has no backward
transfer, no reduction between domains, and no equality derived back into the
e-graph. Termination is not addressed beyond the observation that values only
narrow.

**Zhang et al., "Better Together: Unifying Datalog and Equality Saturation"
(egglog, PLDI 2023).** Replaces egg's single built-in analysis with
lattice-valued functions: tables whose collisions are resolved by a `:merge`
expression. An analysis is a set of ordinary rules over such tables, so a
program can have any number of analyses and propagate in any direction. A
class union makes table entries collide, and `:merge` combines them, which
gives the meet on merge without a dedicated mechanism. The cost is that every
transfer in every direction is a user rule, `:merge` is not restricted to a
lattice operation, and nothing relates two analyses except further rules: the
Herbie benchmark's `lo` and `hi` are separate tables. Our counterpart is
specified in [lattice-functions.md](lattice-functions.md); §12 compares the
two.

**Jourdan et al., "A Formally-Verified C Static Analyzer" (Verasco, POPL
2015).** Supplies the protocol between domains: domains exchange facts
through channels instead of pairwise reduced products (§7 of the paper), and
the symbolic-equality domain (§6.4) plays the role the e-graph plays here.
§2 of this document describes the correspondence. Verasco's symbolic domain
holds one equation per variable and its equalities never come back from the
numerical domains; the e-graph holds whole classes and receives derived
equalities.

**Lesbre, Lemerre, Ait-El-Hara and Bobot, "Relational Abstractions Based on
Labeled Union-Find" (PLDI 2025).** Extends the union-find itself: parent edges
carry labels from a group (`y = x + c`, `y = a·x + b`, `y = (x xor c) rot n`,
signedness casts), `find` composes labels along the path, and a relational
class holds values related by invertible functions. Non-relational values are
stored once at the root and transported along labels by a group action; this
requires the action to be exact, which holds for intervals and congruences
under constant offsets but not for known bits under addition. Two different
labels between the same classes are a conflict that yields constants or
unsatisfiability. The paper reports implementations in the Colibri2 SMT
solver and the Codex C analyzer, and Colibri2 needed a propagation limit
against slow convergence, the problem of §7.

This design does not include labeled edges. **Labeled union-find is
postponed, not rejected.** It would remove the `x = x + 1` descending chain
of requirement 4 (merging `c` with `c + 1` closes a cycle with label `+1`,
which must be the identity, so the merge is an immediate conflict over ℤ) and
store one value for the classes `x`, `x + 1`, `x + 2` instead of three. Its
cost is in the verified `UnionFind` and `EClasses` layer and in proof
logging, because a labeled edge is not an equality. Revisit if measurements
on the benchmark set show that offset chains dominate the propagation budget
of §7.

## 12. Class analysis and lattice functions

The two features overlap on the most common analysis. The Herbie benchmark
strips 32 forms because the engine has no `:merge`
([herbie.deviations.md](../../../doc/benchmarks/ledgers/herbie.deviations.md)
§1): `lo` and `hi` tables over `BigRat`, a `non-zero` relation, 15 rules
that propagate the interval through the operators, and 12 rewrites guarded by
`non-zero`. Without them, the check `(Div (Mul x 3) x) = 3` fails. That
analysis is an interval domain with a nonzero flag, which is the Int fact
record of this design over rationals instead of integers.

| | Class analysis (this document) | Lattice functions ([lattice-functions.md](lattice-functions.md)) |
|---|---|---|
| Keyed by | the e-class | any argument tuple |
| Value | a reduced product of verified domains | one value of one declared lattice |
| Transfers | verified library (tier 1), definitions (tier 2), trusted rules (tier 3) | user rules only |
| Backward propagation | verified, for interpreted symbols | user rules |
| Derived equalities | constants, decided conditions, `ite` branches | rules may `union` |
| Covers | numeric facts about terms of interpreted sorts | any monotone table: costs, shortest paths, points-to, types |

**Order: class analysis first, then lattice functions on the same
infrastructure.** Class analysis gives the Herbie analysis without its 15
rules, with backward propagation and verified transfers, once a rational
interval domain exists (`IntervalZ` covers ℤ only). Lattice functions remain
necessary for egglog programs whose tables are not facts about one term's
value, such as `(function path (i64 i64) i64 :merge (min old new))` in the
egglog paper, and for translating egglog benchmarks without rewriting their
analyses. Both features need the same two extensions: semi-persistent value
pools that roll back with `mark` and `restore`, and a touched-log entry for a
value change that creates no node and merges no class. Building those once
for class analysis leaves lattice functions as a declaration form, a table
index, and the `:merge` restriction to verified domains that
[lattice-functions.md](lattice-functions.md) already requires.

## 13. Further directions

These directions extend the design without changing §4 to §8. Each states
what it adds, what it costs, and what would decide it.

### 13.1 Downward iteration, and the constraint-propagation literature

A class is a conjunction: every node in it is a true statement about the
same value. Classical abstract interpretation joins at control-flow merges
and iterates upward from bottom; its iterates are sound only at the
fixpoint, which is why it needs widening. Here the iteration starts at top
and only takes meets, so every iterate is sound, which is what lets §7 stop
on a budget and lose only precision.

Forward transfer from children followed by backward transfer to children,
over a DAG with shared subterms, is the HC4 algorithm of interval constraint
programming (Benhamou, Goualard, Granvilliers and Puget, "Revising Hull and
Box Consistency", ICLP 1999): HC4-revise evaluates a constraint's expression
tree bottom-up, then projects the result top-down. A class with several
nodes is a shared subexpression with several defining equations, a case HC4
handles by running revise per constraint until no domain changes. That
literature has the scheduling heuristics this design will need: propagate a
change only when it shrinks a domain by more than a threshold, and order the
queue by depth. It also documents the slow convergence §7 bounds by a
budget.

### 13.2 Cycle acceleration

`x = x + 1` over ℤ descends `[0, ∞)`, `[1, ∞)`, `[2, ∞)` one step per
iteration and never reaches the empty set within a budget, although the
equation has no solution in ℤ; modulo 2^N it has none either, for N ≥ 1.
Labeled union-find (§11) removes the chain by turning the merge into a
labeled edge, at a cost in the verified class layer.

**Proposed instead, for a first version: acceleration on the propagation
cycle.** Acceleration applies when the cycle is, syntactically, a chain of
nodes that add or subtract constants, so that following it from a class
back to itself composes to `x ↦ x + d` with `d` a known constant. The
class's values then satisfy `x = x + d`. Over ℤ with `d ≠ 0`, and modulo 2^N
with `d ≢ 0 (mod 2^N)`, that equation has no solution, so the limit of the
descending sequence is the empty set and the class is bottom in one step.
Bottom is a conflict: the asserted equalities have no model. A value that
merely shrinks by a constant on each traversal is not enough to accelerate,
because the shrink can come from other nodes of the cycle's classes. This
is acceleration in the sense of Gonnord and Halbwachs ("Combining Widening
and Acceleration in Linear Relation Analysis", SAS 2006), applied to a
descending sequence. It needs no change to the union-find; its cost is
detecting such cycles when the propagation queue revisits a class. Revisit labeled union-find if
offset chains that acceleration cannot recognize dominate the budget on the
benchmark set.

### 13.3 Relational precision by term synthesis

The domains are non-relational, but the e-graph is not. A node `sub(a, b)`
in its own class has a value, and an interval on that class is a zone
constraint between `a` and `b`; an AC sum `add(a, b, c)` with a value is a
linear constraint over the three. The analysis therefore gains relational
precision whenever such terms exist, without a relational domain.

**Proposed: create them on purpose.** Where a comparison `lt(a, b)` or an
equality between sums occurs, add the node `sub(a, b)` (or the difference
of the two sums) to the graph. Its class value starts at the forward
transfer and is refined by every path that reaches it, which is the
relational information a zone domain would track. The cost is nodes:
bound it by synthesizing only for comparisons that the analysis has not
already decided, and only for operands of one sort. What would decide it:
the number of comparisons decided with and without synthesis, on the
benchmark set of §13.6.

### 13.4 Transfers for flat A, AC and ACI nodes

A flat AC node holds a multiset of children with multiplicities. Its forward
transfer folds the domain's binary operator over the children, with
`k · x` for a child of multiplicity `k` computed by the domain's
multiplication by a constant rather than by `k` additions. Its backward
transfer refines each child by the class value minus the sum of the other
children: computed naively, that is O(n²) per node; with prefix and suffix
folds it is O(n), and n is unbounded for flat nodes. An ACI node uses the
idempotent operator and needs no multiplicities. An A node folds its children
in order. Associativity makes every grouping of that fold equal on concrete
values, but an abstract operator need not be associative, so groupings can
give different values; each is sound, and their meet is too.

AC completion creates nodes, and every new node is one more component of its
class, so completion also tightens values. The interaction runs both ways:
a value that becomes a singleton turns into a literal (§8), which completion
then treats as a constant.

### 13.5 Facts as conflicts and as costs

Two uses of the values follow from §8 without new machinery.

- **Conflicts.** An empty meet proves that the asserted equalities have no
  model. A front end that asserts assumptions, as the CBMC e-graph dumps do,
  learns that its assumptions are infeasible; an SMT-style front end learns
  that its input is unsatisfiable.
- **Costs.** A cost model can read a class's value. A bit-width cost derived
  from an interval is how hardware datapath optimization extracts narrower
  operators (Coward, Constantinides and Drane, §11). The cost-model
  interface reads per-node data today; reading a class value needs one more
  accessor, and the value is fixed during extraction, so the cost stays a
  function of the selection.

### 13.6 Measuring before building

The synthetic benchmarks of `abstract-domains/bench/synth` (proposed in a
separate change) already run this design's propagation outside the e-graph:
classes and nodes from CBMC e-graph dumps, forward and backward transfers
with the crate's `Facts<W>` and `ExecTnum`, a per-class change budget, and
an answer key from sampled and enumerated models. Their first results, over
107 dumps and 233,408 classes, name work this design depends on:

| Finding | Measured | Consequence for this design |
|---|---|---|
| `Compare` on `Facts<W>` answers `Top` | 0 of 144 planted comparisons decided | §6's `ite` rule decides nothing until the comparison transfers land |
| `ExecTnum::bw_and` keeps unknown bits under a known zero | 72 of 174 known-bits points found; 332 of 335 with the eBPF `and` | a precise `and` belongs in the verified tnum before `bits` joins `Facts<W>` |
| reduction between interval and tnum | tnum excess 2.71 bits unreduced, 0.64 reduced | the reduction of §1 is worth its cost on these graphs |

Once the analysis exists in the e-graph, the same benchmarks run through it
and give a differential check against the harness, which is the way to
settle the open budget question of §7 and the term synthesis of §13.3.

### 13.7 Class analysis and lattice functions: how they differ, how they coexist

§12 orders the two features. This section states how they differ in kind,
and how a program uses both.

**What each feature is.** A lattice function is egglog's mechanism and the
subject of [lattice-functions.md](lattice-functions.md): a table from argument
tuples to values of a declared lattice, whose rows are written by rules and
whose colliding rows are combined by `:merge`. The class analysis of this
document attaches one value to each e-class of an interpreted sort, computed
by verified transfers named in the operators' signatures.

| | Lattice function | Class analysis |
|---|---|---|
| Keyed by | any argument tuple: `(path a b)`, `(lo e)` | one e-class |
| Value | one value of one declared lattice | the reduced product of the sort's domains (§5) |
| Who writes the transfers | the user, one rule per operator and direction | the library: `:interp` maps an operator to verified forward and backward transfers (§6) |
| On a class merge | colliding rows are combined by `:merge`, an expression that egglog does not check to be a lattice operation | meet, then reduction between the domains; an empty meet is a conflict (§1) |
| Several analyses | separate tables (Herbie's `lo` and `hi`), related only by further rules | components of one product, related by verified reduction channels |
| Equalities back into the e-graph | only through a rule that writes `union` | singletons become constants, decided conditions and `ite` branches merge (§8) |
| Trust | the rules are trusted, as rewrites are | transfers, meets and reductions are verified; tier 3 facts are trusted (§6) |
| Covers | any monotone table: costs, shortest paths, points-to sets, types | the set of concrete values a term of an interpreted sort can take |

The difference is one of kind. Abstract interpretation assigns each
operator a fixed abstract semantics and runs it over the program; the class
analysis is that, with the e-graph's classes as the program's terms, which
is why it needs no rules and can be verified once for every program. A
lattice function is a monotone Datalog table: more general, because its key
is any tuple and its lattice any lattice, and less specific, because every
transfer is a rule the user writes and checks.

**Each one alone.** Herbie's analysis (§12) is an interval and a nonzero
flag on every `Math` term: the class analysis expresses it with no rules,
and adds backward propagation and verified transfers. A shortest-path
table `(function path (Node Node) i64 :merge (min old new))` relates two
classes: the class analysis cannot express it, because its value describes
one term's concrete value and not a relation between terms.

**Both in one program.** Three connections make the features compose:

- a rule body can test a class fact (§6, tier 3) and write a lattice table,
  so a table can be seeded from the analysis: a cost table whose entry for a
  node reads the bit-width that the node's interval implies;
- a lattice function whose value sort is a verified domain takes that
  domain's join or meet as its `:merge`, the restriction
  [lattice-functions.md](lattice-functions.md) already requires, so such a
  table is sound by the domain's proofs rather than by trust in `:merge`;
- both store values in the semi-persistent value pools and record a
  value-only change in the touched log (§12), so a change in either reaches
  the next semi-naive round and rolls back with `pop`.

**What stays distinct.** Only the class analysis derives equalities back
into the e-graph (§8), because only its values are verified
over-approximations of a single term. Only lattice functions are keyed by
tuples. A program therefore uses the class analysis for facts about values
of interpreted sorts, and lattice functions for relations over tuples of
classes and for egglog programs whose tables are not facts about one term.
