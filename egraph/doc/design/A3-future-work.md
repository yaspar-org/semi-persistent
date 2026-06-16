# Future Work and Recently Completed Features

[← Developer Guide](A2-developer-guide.md) · [Table of Contents](00-table-of-contents.md) · [Ch 1: Node Storage →](01-node-storage.md)


This chapter covers planned features that are designed but not yet
implemented, plus one recently completed feature whose design
document predates the implementation. Full design documents are in
`doc/future/`.

## Planned

### AC Congruence Completeness via Critical Pairs

The problem and the fix are fully analyzed in
[AC Congruence Completeness](ac-congruence-completeness.md). This entry records
**where we stand and what remains.**

**Where we stand.** AC handling is **sound** and **complete for matching against
explicit nodes** (flattened multisets; candidate narrowing over the four indices
+ leapfrog; `DecomposeAC` recursive multiset split with multiplicity tracking and
`rest`-variables). It is **not AC-congruence-complete**: `rebuild` only
re-canonicalizes AC nodes (substitutes equal *atoms*), so sub-sum equalities are
missed — e.g. `+(a,b)=c` and `+(b,d)=e` (sharing `b`) entail `+(c,d)=+(a,e)`,
which we never derive. Our rebuild is Kapur's ground AC-CC (FSCD 2021) **minus**
its completion steps: we have Algo-1 steps 1–2 (union-find + node
re-canonicalization), we lack steps 3–4 (superposition + inter-reduction).

**What remains — implementation.** Add to `rebuild()`, per AC op, to fixpoint:
1. **Inter-reduction** (substitute a contained known sum `+A=a` into `+M`, i.e.
   replace the sub-multiset `A` with the class `a`) — reuses `DecomposeAC` + `rest`
   to compute the residual, `by_contains` to find the super-multiset candidates.
2. **lcm superposition** (overlapping `+A=a`, `+B=b` → materialize `+AB`, reduce
   both ways, merge) — reuses `⋃ by_contains` for overlap candidates.
   *Not* sub-multiset containment (a strict, incomplete special case).
Termination: Dickson's Lemma (Kapur Thm 6). Cost: quadratic in #AC-equations
(Conchon et al. §7.3). We can skip Kapur's monomial ordering — the union-find is
our canonical layer.

**What remains — verification.** The two halves have different proof character
(see [the design doc §12](ac-congruence-completeness.md) for the sketch), so:

- Soundness → Verus, on the real Rust `rebuild`. It is an invariant-preservation
  proof (every rule/merge stays `⊆ ACCC(S)`), which suits Verus's imperative
  reasoning and reuses this workspace's `vstd::multiset` + union-find modeling. It
  certifies the *shipping* code never asserts a false AC equality. Provable today
  on the current recanonize-only rebuild; extend the invariant when the
  substitution steps land.
- Completeness → Lean (or Coq), on the abstract model. It requires Newman's Lemma,
  a Dickson well-quasi-order, and the critical-pair lemma — abstract-rewriting
  metatheory that Verus's trigger-based quantifier automation handles poorly. Lean
  `mathlib` has the well-founded recursion / `Multiset` / order theory; Coq has
  direct precedent (Contejean's RTA 2004 certified AC matching in Coq; CoLoR
  formalizes termination / Dickson).
- Why split: all-Verus would push the confluence metatheory into a tool poorly
  suited to it; all-Lean would prove soundness about an *idealized* model, not the
  real Rust, losing the main benefit. The split proves soundness on the running
  code and completeness in a tool that supports the metatheory.

Staging: (1) Verus soundness invariant on today's rebuild; (2) extend it as
inter-reduction/superposition land; (3) Lean abstract completeness theorem,
parameterized to transfer to the implementation by refinement.

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
edge representation, with three concrete instantiations:

| Variant | Edge label | UF witness | Use case |
|---------|-----------|------------|----------|
| Classic | `()` | `()` | No binders (default) |
| Director | partial-injection matrix | contraction matrix | Positional ports, compact encoding |
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
