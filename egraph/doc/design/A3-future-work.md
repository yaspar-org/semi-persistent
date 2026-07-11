# Future Work

[← Developer Guide](A2-developer-guide.md) · [Table of Contents](00-table-of-contents.md) · [Ch 1: Node Storage →](01-node-storage.md)


This chapter covers features that are designed but not yet implemented. Full design
documents are in `doc/future/`. Implemented features are described in the main design
flow; AC congruence completeness, for example, is its own chapter
([AC Congruence Completeness](ac-congruence-completeness.md), with the engine-level
companion [AC Completion spec](ac-completion-spec.md)) and is covered by
[Ch 14: Soundness and Completeness](14-soundness.md). What remains for AC completion is
listed below.

## AC Completion: remaining work

The algorithm is implemented (see the chapters above). Two pieces remain — scoping and
verification; the formerly-third piece (multi-AC/ACI + semantic properties) landed in the
2026-07 series and is summarized in a done-note below for the record.

**Enable by default (scoping).** Completion is off by default pending a termination
guard. On a sweep of stress graphs it converges on all but one pathological instance,
whose AC equation set has a genuinely large canonical basis (the growth is
input-specific, not size-specific; AC spec §3.3). Enabling it generally wants one of: a
per-`rebuild` growth guard that disables completion and falls back to plain congruence,
on-demand completion scoped to the sub-graph a query needs, or a degree bound on
materialized monomials. All three trade completeness for termination, and the fallback
is sound (it derives fewer equalities, never wrong ones; see Ch 14 on the trustworthy
polarity).

**Multiple AC symbols — DONE (2026-07, multi-AC/ACI series + conformance fixes).**
The per-op `min_monomial` pool landed (per-class rows, one column per completion op), the
round drives both the MSet and Set partitions, and the Kapur §4 semantic properties are in:
identity (unit-drop at build AND recanonize, `CanonMode`), idempotent and nilpotent count
clamps, and the per-rule *axiom* critical pairs (Lemmas 4.1(ii), 4.2(ii)/4.5) that clamping
alone cannot derive. A rule whose class is the op's identity has the **empty monomial** as
RHS (Kapur's `f({}) = e`). `:cancellative`/`:inverse` are rejected until their facets exist.
See `ac-completion-spec.md` §3 (the Kapur-correspondence table) and
`ac-algebraic-properties.md` (the storage and property-tag design). The cancelative facet
(Kapur §5.1–5.3) and gate-level `:inverse` pair cancellation landed 2026-07-10; **full
Abelian-group completion (§5.4, Gaussian elimination) is postponed indefinitely**
(operator decision 2026-07-10, recorded in `future/ac-completion-review-debt.md` §3).

**Verification.** The two halves have different proof character
(see [the design doc §12](ac-congruence-completeness.md) for the sketch), so:

- Soundness → Verus, on the real Rust `rebuild`. It is an invariant-preservation
  proof (every rule and merge stays `⊆ ACCC(S)`), which suits Verus's imperative
  reasoning and reuses this workspace's `vstd::multiset` + union-find modeling. It
  certifies the shipping code never asserts a false AC equality.
- Completeness → Lean (or Coq), on the abstract model. It requires Newman's Lemma,
  a Dickson well-quasi-order, and the critical-pair lemma, abstract-rewriting
  metatheory that Verus's trigger-based quantifier automation handles poorly. Lean
  `mathlib` has the well-founded recursion / `Multiset` / order theory; Coq has
  direct precedent (Contejean's RTA 2004 certified AC matching in Coq; CoLoR
  formalizes termination / Dickson).
- Why split: all-Verus would push the confluence metatheory into a tool poorly
  suited to it; all-Lean would prove soundness about an idealized model, not the
  real Rust, losing the main benefit. The split proves soundness on the running
  code and completeness in a tool that supports the metatheory.

### Variables and Binders via Parameterized Edge Labels

Standard e-graphs share structurally identical subterms, but
variables and binders break this property. A variable's identity
depends on its binding context, so the same structural subterm under
different binders gets different representations. De Bruijn indices
make each variable carry its distance to its binder, which is
context-dependent and destroys sharing.

The solution is to parameterize the e-graph over an edge label type
that encodes binding information on edges rather than in variables.
The design introduces a `PortAlgebra` trait that abstracts over the
edge representation. Three binder-aware instantiations are under
consideration (plus the trivial Classic default); the choice between
them is open.

| Variant | Edge label | UF witness | Use case |
|---------|-----------|------------|----------|
| Classic | `()` | `()` | No binders (default) |
| Director | partial-injection matrix | contraction matrix | Positional ports, compact encoding |
| Thinning | subset/order-preserving injection | thinning composition | Minimal scope tracking, cheap weakening |
| Slotted | slot renaming map | slot renaming | Named slots, symmetry tracking |

#### Classic (default)

Edges carry no label. This is the current behavior: no binder
support, maximum performance.

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
the parent's scope, so a subterm records exactly the variables it uses
and weakening is a thinning composition. This makes scope minimal by
construction (no unused binders are carried) and sharing maximal (two
occurrences that use the same variables share regardless of ambient
scope), at the cost of computing thinning composites on merge.

#### Slotted

Based on slotted e-graphs (Schneider et al., PLDI 2025). Each edge
carries a bijective renaming from child slots to parent slots. Classes
carry slot sets and symmetry groups.

All binder-aware variants share the same fundamental insight: on
merge, the class's port interface shrinks to the intersection of the
two sides. Ports that appear in one representation but not the other
are redundant. The contraction witness is stored in the union-find to
map the wider representation to the narrower one.

The parameterization affects two edge types in the e-graph:

1. E-node → child e-class edges. Each child pointer carries an edge
   label encoding the variable routing from parent to child.
2. Union-find edges. Each UF entry carries a witness that maps the
   absorbed class's port interface to the survivor's.

See `doc/future/alpha-equivalence.md` for the full unified design
including the `PortAlgebra` trait, composition rules, merge semantics,
and interaction with AC/ACI canonization.

### Cost-Based Extraction via Partial Weighted Max-SAT

The current extractor uses a simple bottom-up fixpoint: each
operator costs 1, and the cheapest term is found by iterating over
all e-nodes until costs stabilize. This handles the common case
(smallest AST) but cannot express richer extraction objectives.

A more powerful approach encodes extraction as partial weighted
Max-SAT. Each e-node becomes a boolean variable ("is this node
selected?"). Hard clauses enforce structural consistency: exactly one
node is selected per e-class, and selecting a node forces selection
of one node in each child class. Soft clauses encode cost
preferences with weights.

This formulation naturally supports:
- Per-operator cost weights (not just uniform cost 1)
- Constructor preference (prefer certain operators over others)
- DAG extraction (shared subterms counted once, not per-occurrence)
- Extraction with sort constraints
- Multi-objective extraction (Pareto-optimal trade-offs)

The Max-SAT encoding can be solved by off-the-shelf solvers (e.g.,
RC2, Open-WBO) or by a specialized branch-and-bound algorithm that
exploits the tree structure of the e-graph.

See `design_future/sp-optimal-term-extraction.md` for the cost
model and encoding details.

### Stratified Negation

the engine's generational structure provides the right semantics for
stratified negation at no additional cost. A stratum boundary is a
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

See `design_future/sp-stratified-negation.md` for the full
design including interaction with e-class merging.

---
[← Developer Guide](A2-developer-guide.md) · [Table of Contents](00-table-of-contents.md) · [Ch 1: Node Storage →](01-node-storage.md)
