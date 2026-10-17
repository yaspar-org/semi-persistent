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
`(prove (!= a b))`, feed guards that test disequality, and turn a later merge
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
