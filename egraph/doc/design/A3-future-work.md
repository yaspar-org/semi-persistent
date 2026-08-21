# Future Work

[← Developer Guide](A2-developer-guide.md) · [Table of Contents](00-table-of-contents.md) · [Ch 1: Node Storage →](01-node-storage.md)


This chapter covers features that are designed but not yet implemented. Full design
documents are in `doc/future/`. Implemented features are described in the main design
flow; AC congruence completeness, for example, is its own chapter
([AC Congruence Completeness](ac-congruence-completeness.md), with the engine-level
companion [AC Completion spec](ac-completion-spec.md)) and is covered by
[Ch 14: Soundness and Completeness](14-soundness.md). What remains for AC completion is
listed below.

## Maintained specifications

- [AC completion limits and validation](../future/ac-completion-limitations.md)
- [AU correctness and validation](../future/au-correctness-and-validation.md)
- [AU proof certificates](../future/au-proof-certificates.md)
- [Associative AU and other solver features](../future/au-associative-operators.md)
- [Lattice-valued functions](../future/lattice-functions.md)
- [Verified query compiler](../future/verified-query-compiler.md)
- [Partial weighted Max-SAT extraction](../future/max-sat-extraction.md)
- [Runtime performance validation](../future/performance-validation.md)
- [Variables and binders](../future/alpha-equivalence.md)
- [Stratified negation](../future/stratified-negation.md)

## AC Completion: remaining work

The algorithm is implemented, including multiple AC/ACI symbols and the semantic-property
facets: the per-op `min_monomial` pool (per-class rows, one column per completion op),
both MSet and Set partitions driven by the round, identity (unit-drop at build AND
recanonize, `CanonMode`), idempotent and nilpotent count clamps, the per-rule *axiom*
critical pairs (Kapur Lemmas 4.1(ii), 4.2(ii)/4.5) that clamping alone cannot derive, the
empty-monomial RHS for identity classes (Kapur's `f({}) = e`), the `:cancellative` §5
cancel-closure, and `:inverse` pair-level cancellation (which implies cancelative). See
`ac-completion-spec.md` §3 (the Kapur-correspondence table) and
`ac-algebraic-properties.md` (the storage and property-tag design). **Full Abelian-group
completion (§5.4, Gaussian elimination) is unsupported** (see
`../future/ac-completion-limitations.md`). Two pieces remain: scoping and verification.

**Enable by default (scoping).** Completion is off by default. On a sweep of stress
graphs, behavior ranged from quick convergence to explosive work. Those
observations do not establish that a generated basis is canonical, minimal, or
intrinsically necessary. The shipped backstop is the per-egraph
node-growth budget (`set_completion_node_budget`), checked inside the round's
apply loops and after progress; exceeding it reports
`CompletionOutcome::AbortedGrowthLimit`, drains plain congruence, and makes no
completion claim. Equalities already merged retain the transition-level
soundness argument described in Chapter 14 and focused tests, not an
end-to-end verified theorem. The lazy mode
(`--lazy-ac-eqs`, `ac-congruence-completeness.md` §13) covers the on-demand direction:
completion runs only inside a failing check, in a mark/complete/restore transaction,
with goal-directed rule/completion alternation as its second phase. Its recorded
refinements: share one transaction across consecutive checks, poll the goal
inside the completion loop, and stop growth inside a round rather than waiting
for its end. A degree bound on materialized monomials remains the other
scoping option. These early-stop policies trade completeness for bounded
execution. Their intended trustworthy polarity is to omit derivations rather
than admit unjustified ones; proving that polarity for every production
transition remains part of the verification work below.

**Verification.** The concrete obligations are listed in
[the design doc §12](ac-congruence-completeness.md) and
[the limitations specification](../future/ac-completion-limitations.md).
They include a precise finite-pool semantics, refinement of every Rust
normalization/materialization/merge step to that semantics, strict descent or
finite-work arguments for each loop, critical-pair coverage for each supported
algebra, and a theorem connecting a reported full-round fixpoint to the desired
closure property. The current Verus proofs cover container and e-class
invariants, not those end-to-end completion theorems.

Verus is a plausible tool for refinement and invariant preservation over the
shipping Rust. Lean or Coq may be useful for the abstract rewriting,
well-quasi-order, and confluence results. That tool split is a proposal, not an
established proof result or a requirement: whichever formalization is chosen
must state and prove the interface theorem between the abstract model and the
executable implementation.

### Variables and Binders via Parameterized Edge Labels

Standard e-graphs share structurally identical subterms, while variables and
binders make identity context-dependent. A direct de Bruijn implementation can
need shifted representations at different binder depths and thereby reduce
sharing. That is a risk of the naive representation, not a theorem that every
de Bruijn or explicit-substitution implementation destroys sharing.

The proposed direction is to parameterize the e-graph over an edge-label
algebra that encodes binding information on edges rather than in variables.
The `PortAlgebra` trait is a design, not an implemented trait. Three
binder-aware candidate families are under consideration; their merge and
symmetry laws are not yet known to fit one sufficient interface.

| Variant | Edge label | UF witness | Use case |
|---------|-----------|------------|----------|
| Classic | `()` | `()` | No binders (default) |
| Director | partial-injection matrix | contraction matrix | Positional ports, compact encoding |
| Thinning | subset/order-preserving injection | thinning composition | Minimal scope tracking, cheap weakening |
| Slotted | slot renaming map | slot renaming | Named slots, symmetry tracking |

#### Classic (default)

The current engine carries no binder label because the proposed
parameterization is not wired in. This establishes the current layout, not a
zero-cost claim about a future generic `PortAlgebra` implementation.

#### Directors

Based on director strings (Kennaway & Sleep 1988, Sinot 2005). Each
edge carries a partial injection from child ports to parent ports,
encoded as a matrix of bits. A single shared `Var` e-class with arity
1 represents all variable occurrences; which variable a `Var` node
represents is determined entirely by the parent edge's annotation.

#### Thinnings

Based on the co-de-Bruijn / thinning representation (a thinning is an
order-preserving injection from a subterm's used variables into the
ambient scope; McBride 2018, "Everybody's Got To Be Somewhere"). Each
edge carries the thinning that embeds the child's used-variable set into
the parent's scope, so a subterm can record the variables it uses and weakening
is a thinning composition. This can avoid unused ambient binders and improve
sharing; minimality and cross-context sharing are proof obligations, not
established properties of an implementation.

#### Slotted

Based on slotted e-graphs (Schneider et al., PLDI 2025). Each edge
carries a bijective renaming from child slots to parent slots. Classes
carry slot sets and symmetry groups.

The candidates share the use of labeled e-class references and composable
union-find witnesses. They do not yet share one proved merge law. Slotted
e-graphs additionally track class symmetries, thinnings require
order-preserving embeddings, and director contractions use positional
matrices. A simple set intersection is therefore a proposed special case, not
a unifying correctness theorem.

The parameterization affects two edge types in the e-graph:

1. E-node → child e-class edges. Each child pointer carries an edge
   label encoding the variable routing from parent to child.
2. Union-find edges. Each UF entry carries a witness that maps the
   absorbed class's port interface to the survivor's.

See `doc/future/alpha-equivalence.md` for the detailed Director/Slotted
proposal, the missing symmetry/canonical-key obligations, and the relationship
to the less-developed thinning candidate.

### Lattice-Valued Functions

The proposed lattice functions would resolve functional-dependency collisions
by a domain join rather than by e-class union. Selected abstract-domain joins
already have Verus proofs, but the table, declaration surface, and engine
integration do not exist. Their storage must restore the join history, and a
strict value increase must enter the semi-naive delta even when no node or
class changes. The full semantics, storage invariant, integration steps, and
translated-benchmark acceptance criteria are in
[the lattice-functions specification](../future/lattice-functions.md).

### Verified Query Compiler

A verified plan validator can exclude read-before-bind, cleanup, missing-atom,
and guard-order defects at rule installation. An independent pattern-level
matcher then supplies a semantic oracle, with a compiler-refinement theorem as
the final stage. See
[the verified-query-compiler specification](../future/verified-query-compiler.md).

### Cost-Based Extraction via Partial Weighted Max-SAT

The current fixpoint extractor remains the default for additive owned-tree
cost. Partial weighted Max-SAT or pseudo-Boolean extraction extends the
objective to edge costs, hard exclusions, lexicographic optimization, and
shared-DAG cost. It requires an explicit acyclicity encoding, deterministic
decoding, a solver trait, and independent optimum checks. The complete design
and acceptance criteria are in
[the Max-SAT extraction specification](../future/max-sat-extraction.md).

### Stratified Negation

The engine's generational structure can provide a checkpoint boundary for
stratified negation, but `mark()` itself is only a rollback token. Negative
indexing, SCC-aware dependency analysis, and retaining and querying a frozen
lower-stratum relation/equality view have implementation and memory costs.
A proposed stratum boundary is a
generation boundary: stratum k runs to fixpoint producing generation
G_k, and stratum k+1 treats G_k as its negative database. Since G_k
is a fully rebuilt, congruence-closed snapshot that is frozen for the
duration of stratum k+1, the absence of a fact in G_k is a stable
truth.

The implementation requires:
- A static stratification check on the dependency graph (no cycle
  through a negative edge)
- Negative literals as post-filters in the join engine (applied after
  the positive leapfrog completes, never contributing iterators)
- A variable safety check (every variable in a negative literal must
  be bound by some positive literal)

See [`../future/stratified-negation.md`](../future/stratified-negation.md)
for the full design including interaction with e-class merging.

## Anti-Unification: remaining work

Anti-unification is implemented and documented in
[Ch 19: Anti-Unification](19-anti-unification.md). The remaining work
(structural factoring for unequal-length associative (Seq) operators, PUCT and prior
processors, non-injective ACI matching, golden traces, and JSON export) is
collected in
[the associative-operator specification](../future/au-associative-operators.md).
The target theorem, production refinements, universal bound/transport lemmas,
formalizer validation, and delegation calibration are in
[AU correctness and validation](../future/au-correctness-and-validation.md);
independently checkable projection proofs are in
[AU proof certificates](../future/au-proof-certificates.md). The value-guided AND
selectors listed here previously are delivered: `uct_and` and `lct_and` are
selectable via `and_selector` alongside `round_robin`, with `lct_and` the
default.

## Runtime performance validation

Unresolved performance work and evidence-triggered revival conditions are
collected in
[the runtime validation specification](../future/performance-validation.md).
Machine-sensitive measurements use Criterion confidence intervals; the
retained cross-engine campaign remains qualified by its recorded host state.

---
[← Developer Guide](A2-developer-guide.md) · [Table of Contents](00-table-of-contents.md) · [Ch 1: Node Storage →](01-node-storage.md)
