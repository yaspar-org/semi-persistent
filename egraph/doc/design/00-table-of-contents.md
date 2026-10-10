# Semi-Persistent E-Graph — Design Documents

[Table of Contents](00-table-of-contents.md) · [Overview: Why A Semi-Persistent EGraph →](A0-overview.md)

The foundational data structures (dense IDs, semi-persistent vectors, containers) are documented in the `semi-persistent-containers` crate documentation.

## Overview and Guides

- **[Overview: Why A Semi-Persistent Egraph?](A0-overview.md)**
  Intellectual lineage (egg, egglog, semi-persistence, AC
  canonization). Core capabilities: sparse snapshot memory with backend-specific
  mark/restore costs, native
  A/C/AC/ACI, leapfrog triejoin, proof extraction. Variables and
  binders are future work. Architecture and key design decisions.

- **[Language Guide](A1-language-guide.md)**
  Surface syntax, sorts, operators, algebraic attributes, rewrite
  rules, variadic matching, push/pop, saturation, compilation pipeline.

- **[Developer Guide: Extending the Literal Model](A2-developer-guide.md)**
  The `LitModel` trait, defining new builtin sorts and operations,
  how builtins are lifted into the e-graph, deferred interning,
  soundness guarantees.

- **[Future Work](A3-future-work.md)**
  Index of maintained future specifications: variables and binders,
  lattice-valued functions, a verified query compiler, partial weighted
  Max-SAT extraction, stratified negation, AU correctness/certificates, runtime
  validation, and the remaining AC-completion limits. Implemented algorithms
  stay in the numbered design chapters.

## Part I: Storage and the E-Graph

1. **[Node Representation and Storage](01-node-storage.md)**
   `FixedArityNode`, `VariableArityNode`, `LitNode`. Pool-allocated
   children for variable-arity. `NodeStore` with typed routing table.
   `NodeRef` enum for dispatch. History bit for proof logging.

2. **[E-Classes and Union-Find](02-classes-and-union-find.md)**
   `UnionFind` with path halving and union-by-rank.
   `EClasses`: circular use-lists for parent tracking, splice on merge.
   `MergeInfo` for worklist-driven rebuild. Proof-justified union.
   Merge survivor policy (`--union-by`) on the verified class-size and
   use-list counters.

3. **[Hash-Consing Caches](03-hash-consing-caches.md)**
   `FixedArityCache` (arity 0–3, commutative), `VariableArityCache`
   (A/AC/ACI with pool), `LitCache`. Partitioned by arity for cache
   locality. Re-canonization during rebuild. Collision detection.

4. **[The E-Graph](04-egraph.md)**
   `EGraph<Cfg, L, TRACK, PROOFS>`. Rebuild algorithm: worklist-driven,
   re-canonize parents, detect congruence collisions. `add`, `merge`,
   `find`. Push/pop via mark/restore across all sub-containers.

## Part II: Algebra

5. **[Algebraic Operators and Canonization](05-algebraic-operators.md)**
   Start here for what is new: one canonical form, flattening at match time, AC
   congruence closure, and extraction that chooses the grouping, each with its
   guarantee and a pointer to the detail. `PlainCanon`, `CCanon` (sort pair),
   `OrderedCanon` (A sequences), `MSetCanon` (sorted multiset, merge
   multiplicities), `SetCanon` (sorted set, deduplicate). The `VarCanon` trait.
   The algebraic properties of AC operators: representation, canonization, and
   the per-op pool.

6. **[AC Congruence Closure](06-ac-congruence-closure.md)**
   Part I explains why flattening AC nodes into canonical multisets erases the
   intermediate sub-sum subterms and breaks congruence completeness
   while the implemented matcher targets a narrower, sound maximum-partition
   e-matching relation; finite tests support matcher soundness, while a theorem
   and matcher completeness remain open. Part II gives the implemented repair,
   Kapur-style
   inter-reduction and lcm-superposition critical pairs over the existing
   `DecomposeAC`/`by_contains` machinery. Its soundness, termination, and
   completeness claims are conditional on the obligations stated in that
   chapter; they are not machine-checked theorems about the Rust code.
   §13 specifies the three completion modes
   (plain, eager, lazy: the goal-directed transaction at failing checks) and
   §14 the A-only inter-reduction round with its undecidability boundary.
   The verification plan lives in Future Work. Part III describes the
   incrementally maintained `min_monomial` candidate, its read-time orientation
   guard, and the diagnostic that can detect a nonminimal candidate; traces over
   concrete nodes the binding-restore invariant the
   `(f (add x ..r1) (add x ..r2))` matcher join must maintain; and checks the code clause-by-clause against the algorithm, explaining
   the sources of per-round growth without treating an observed basis as
   canonical or proving that every emitted node is necessary.

## Part III: Rules

7. **[Rules and Pattern Matching](07-rules-and-pattern-matching.md)**
   The surface language and parser, sortcheck and resolution, query
   compilation and scheduling, and pattern-matching execution. Matching over
   A, AC, ACI, and C operators, with maximum-partition semantics and
   `:flatten` views. Sequence patterns in the relational matcher, and rule
   application and right-hand-side evaluation.

8. **[Indexes and Leapfrog Triejoin](08-indexes-and-leapfrog.md)**
   `IndexStore` and its four `DenseSpanMap` families, rebuilt each round.
   `LeapfrogJoin`, the worst-case optimal multi-way intersection. Index
   selectivity, adaptive atom scheduling, and delta suffixes.

9. **[Saturation: the Interpreter, Naive and Semi-Naive Evaluation](09-saturation.md)**
   The `Interpreter`, command execution, the saturation loop, and push/pop
   scoping. Semi-naive evaluation: the `touched` log, delta indexes, and the
   k-variant delta decomposition.

10. **[Extensible Literal Model](10-literal-model.md)**
    `LitModel` trait: `sorts`, `ops`, `parse`, `is_truthy`.
    `BignumModel`, `MachineModel`, `AllModel`. `LitValStore` with
    `intern`/`try_lookup`. Ordinary term/rule sortchecking does not intern;
    declaration registration mutates registries and may build an AC identity.
    LHS matching is read-only. RHS application interns on demand.

## Part IV: Results and Guarantees

11. **[Extraction](11-extraction.md)**
    Additive extraction with content-ordered tie-breaking and the canonical
    `dump-egraph` export. Extraction under cost models: selection as
    constraints, flat nodes and the ladder of rungs, polarity, certificates.
    The backends, the Rust and Roto APIs, and criteria in ASP and MiniZinc.

12. **[Anti-Unification](12-anti-unification.md)**
    Exact memoized solver and Monte-Carlo graph search over the AND/OR
    graph of e-class-pair subproblems. Cycle contexts over SCC
    reachability, `(size, variant_mass)` ranking, AC/ACI matching via
    min-cost transportation, semi-persistent `SearchSession`
    mark/restore, `(antiunify)` / `(checkau)` commands.

13. **[Correctness Claims and Boundaries](13-soundness.md)**
    The two correctness properties over both sources of derived equalities,
    literal evaluation and congruence closure, and across operator kinds
    (plain, C, A, AC, ACI). Soundness: no false equality is asserted.
    Plain congruence closure is the default; opt-in AC/ACI completion attempts a
    stronger fixpoint but may stop at a resource limit. What is machine-checked,
    tested, argued conditionally, and still open.

14. **[Proof Logging](14-proof-logging.md)**
    Copy-on-first-re-canonization via history bit. `Justification`
    includes rewrite, congruence, user axiom, five AC-specific inference kinds,
    a companion-solver assumption, and a non-proof filler. Dual parent pointers
    (`parent` + `parent_proof`). Two LCA algorithms: naive
    walk-up for single queries, Euler-tour BFC for batch extraction and
    `--dump-proofs`. `ProofBuf` for path extraction. `PROOFS` const generic.

---

## Lexicon

Canonical terms; other phrasings defer to these.

- **multiplicity variant**: the variant of a rule covering a child at
  multiplicity 2 or more. Pattern elements bind distinct children
  (§7.5), so the base rule cannot match a repeated child.
- **class-growth delta**: the touched-log entries recording the absorbed
  class's members on a merge, so class growth that recanonicalizes
  nothing still reaches the next semi-naive round (§9.2).
- **survivor policy**: the `--union-by {rank,size,uses,sum}` choice of
  which class survives a merge (chapter 2).
- **eager completion** (`--derive-ac-eqs`) and **lazy completion**
  (`--lazy-ac-eqs`): the two opt-in AC completion modes; plain is the
  default (Chapter 6 §13).
- **campaign**: one timed measurement pass of the whole comparison set
  at one commit; a **run** is a single timed invocation.
- **native encoding / native column / native dual**: the program style
  using native algebraic operators, its slot in a results table, and
  the translated counterpart file of a rules-encoding benchmark.
- **class key**: the repr-set key naming a class's `ClassData`; "live"
  is its state adjective.
- **spelling**: one of a class's `Seq` nodes, the A-only analogue of an
  AC monomial (Chapter 6 §14).
- **W-invariants** (W1-W7): defined and proved in
  `containers-verus/src/eclasses.rs`; every citation points there.

---

## See Also

- `semi-persistent-containers` crate: dense IDs, semi-persistent vectors, and container types
- `semi-persistent-traversals` crate: stack-safe tree traversal algorithms

---
[Table of Contents](00-table-of-contents.md) · [Overview: Why Semi-Persistent →](A0-overview.md)
