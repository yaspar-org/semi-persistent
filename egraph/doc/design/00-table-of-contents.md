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

- **[AC Congruence Completeness](ac-congruence-completeness.md)**
- **[Algebraic Properties of AC Operators](ac-algebraic-properties.md)**
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
  The verification plan lives in Future Work.

- **[AC Completion: `min_monomial`, a matcher invariant, and implementation correspondence](ac-completion-spec.md)**
  A focused companion to the above (does not restate it). Describes the
  incrementally maintained `min_monomial` candidate, its read-time orientation
  guard, and the diagnostic that can detect a nonminimal candidate; traces over
  concrete nodes the binding-restore invariant the
  `(f (add x ..r1) (add x ..r2))` matcher join must maintain; and checks the code clause-by-clause against the algorithm, explaining
  the sources of per-round growth without treating an observed basis as
  canonical or proving that every emitted node is necessary.

## Part I: E-Graph Core

1. **[Node Representation and Storage](01-node-storage.md)**
   `FixedArityNode`, `VariableArityNode`, `LitNode`. Pool-allocated
   children for variable-arity. `NodeStore` with typed routing table.
   `NodeRef` enum for dispatch. History bit for proof logging.

2. **[E-Classes and Union-Find](02-classes-and-union-find.md)**
   `UnionFind` with path compression and union-by-rank.
   `EClasses`: circular use-lists for parent tracking, splice on merge.
   `MergeInfo` for worklist-driven rebuild. Proof-justified union.
   Merge survivor policy (`--union-by`) on the verified class-size and
   use-list counters.

3. **[Hash-Consing Caches](03-hash-consing-caches.md)**
   `FixedArityCache` (arity 0–3, commutative), `VariableArityCache`
   (A/AC/ACI with pool), `LitCache`. Partitioned by arity for cache
   locality. Re-canonization during rebuild. Collision detection.

4. **[Canonization Algorithms](04-canonization.md)**
   `PlainCanon`, `CCanon` (sort pair), `OrderedCanon` (A sequences),
   `MSetCanon` (sorted multiset, merge multiplicities),
   `SetCanon` (sorted set, deduplicate). The `VarCanon` trait.

5. **[The E-Graph](05-egraph.md)**
   `EGraph<Cfg, L, TRACK, PROOFS>`. Rebuild algorithm: worklist-driven,
   re-canonize parents, detect congruence collisions. `add`, `merge`,
   `find`. Push/pop via mark/restore across all sub-containers.

## Part II: Matching Engine

6. **[Index Construction](06-index.md)**
   `IndexStore`: `by_op`, `by_repr`, `by_child_pos`, `by_contains`.
   Built from scratch each saturation iteration. Each family is a verified
   `DenseSpanMap`: a flat value pool plus a dense-keyed span table, read
   through a leapfrog-compatible cursor.

7. **[Leapfrog Triejoin](07-leapfrog.md)**
   `LeapfrogJoin` over sorted iterators. Worst-case optimal multi-way
   intersection. Seek-based advancement.

8. **[Query Compilation and Scheduling](08-query-compilation.md)**
   Atoms → execution plan. Cost-based variable ordering. Eager pass
   for bound nodes. E-class–aware re-join for `ExtractChild` results.
   `LitBind` deferred to cost-based selection.

9. **[Pattern Matching Execution](09-pattern-matching.md)**
   Flattened-atom execution with static plans or dynamic per-binding
   middle-out scheduling. Push-style continuations use depth-first control
   flow; a separate pull iterator executes static plans. Subsequence, subset,
   and sub-multiset matching. Maximum partition semantics for AC and
   multiplicity constraints with interval intersection.

## Part III: Language and Compilation

10. **[Surface Language and Parser](10-surface-language.md)**
    Unified `(op children...)` syntax. `SurfacePattern` with
    prefix/suffix rest vars. `RhsTerm` with comprehensions.
    No bracket dispatch: operator kind resolved later.

11. **[Sortchecking and Resolution](11-sortcheck-and-resolution.md)**
    Three-phase pipeline: parse → sortcheck → interpret.
    `flatten_surface`: op-kind validation, atom classification.
    `resolve`: string names → dense typed ids. `MatchShape`.
    `CTerm`/`CCommand` for the interpreter.

12. **[Rule Application and RHS Evaluation](12-rule-application.md)**
    `RhsOp`/`RhsArg` tree. `FetchNode`, `Lit`, `App`, splices,
    comprehensions. `apply_action`: union, insert, subsume.
    Primitive op evaluation via `LitModel`.

## Part IV: Literal Model

13. **[Extensible Literal Model](13-literal-model.md)**
    `LitModel` trait: `sorts`, `ops`, `parse`, `is_truthy`.
    `BignumModel`, `MachineModel`, `AllModel`. `LitValStore` with
    `intern`/`try_lookup`. Ordinary term/rule sortchecking does not intern;
    declaration registration mutates registries and may build an AC identity.
    LHS matching is read-only. RHS application interns on demand.

## Part V: Soundness, Completeness, Proof Extraction, Term Extraction

14. **[Correctness Claims and Boundaries](14-soundness.md)**
    The two correctness properties over both sources of derived equalities,
    literal evaluation and congruence closure, and across operator kinds
    (plain, C, A, AC, ACI). Soundness: no false equality is asserted.
    Plain congruence closure is the default; opt-in AC/ACI completion attempts a
    stronger fixpoint but may stop at a resource limit. What is machine-checked,
    tested, argued conditionally, and still open.

15. **[Proof Logging](15-proof-logging.md)**
    Copy-on-first-re-canonization via history bit. `Justification`
    includes rewrite, congruence, user axiom, five AC-specific inference kinds,
    and a non-proof filler. Dual parent pointers
    (`parent` + `parent_proof`). Two LCA algorithms: naive
    walk-up for single queries, Euler-tour BFC for batch extraction and
    `--dump-proofs`. `ProofBuf` for path extraction. `PROOFS` const generic.

16. **[Term Extraction](16-extraction.md)**
    Additive owned-tree cost model. `extract_best` by repeated relaxation over
    all nodes to a fixed point.
    `reconstruct` for pretty-printing.

## Part VI: Interpreter and Saturation

17. **[Interpreter and Saturation Loop](17-interpreter.md)**
    `Interpreter` executes `CCommand` sequence. `saturate`:
    rebuild → index → schedule → match → apply. Push/pop scoping.
    `GlobalCtx` for let-bound names.

## Part VII: Incremental Saturation

18. **[Semi-Naive Evaluation](18-semi-naive-evaluation.md)**
    `saturate_semi`: match only what changed each round via the
    k-variant delta decomposition. `touched` log on the e-graph
    (created, recanonicalized, and absorbed-class members: the
    class-growth delta) + `IndexStore::build_delta`; `VariantIndex`
    three-way mode (delta / full∖delta / full) realized on `Step::Join`
    via the `Difference` cursor combinator. Root-binding and
    global-element rules use a full-index match each round. Per-atom,
    per-flavor scheduling. Selectable via `--use-semi-naive`; default
    remains naive. The driver never switches wholesale to naive, but
    individual rules use full-index matching when delta coverage is unsafe.

## Part VIII: Anti-Unification

19. **[Anti-Unification](19-anti-unification.md)**
    Exact memoized solver and Monte-Carlo graph search over the AND/OR
    graph of e-class-pair subproblems. Cycle contexts over SCC
    reachability, `(size, variant_mass)` ranking, AC/ACI matching via
    min-cost transportation, semi-persistent `SearchSession`
    mark/restore, `(antiunify)` / `(checkau)` commands.

20. **[Index Selectivity and Delta Suffixes](20-index-selectivity-and-delta-suffixes.md)**
    Size-biased per-path selectivity, per-binding operator restriction,
    static/runtime/automatic atom scheduling, sampled cross-index selectivity,
    semi-naive mode composition, and deferred watermark suffixes.

---

## Lexicon

Canonical terms; other phrasings defer to these.

- **multiplicity variant**: the variant of a rule covering a child at
  multiplicity 2 or more. Pattern elements bind distinct children
  (chapter 9), so the base rule cannot match a repeated child.
- **class-growth delta**: the touched-log entries recording the absorbed
  class's members on a merge, so class growth that recanonicalizes
  nothing still reaches the next semi-naive round (chapter 18).
- **survivor policy**: the `--union-by {rank,size,uses,sum}` choice of
  which class survives a merge (chapter 2).
- **eager completion** (`--derive-ac-eqs`) and **lazy completion**
  (`--lazy-ac-eqs`): the two opt-in AC completion modes; plain is the
  default (AC doc §13).
- **campaign**: one timed measurement pass of the whole comparison set
  at one commit; a **run** is a single timed invocation.
- **native encoding / native column / native dual**: the program style
  using native algebraic operators, its slot in a results table, and
  the translated counterpart file of a rules-encoding benchmark.
- **class key**: the repr-set key naming a class's `ClassData`; "live"
  is its state adjective.
- **spelling**: one of a class's `Seq` nodes, the A-only analogue of an
  AC monomial (AC doc §14).
- **W-invariants** (W1-W7): defined and proved in
  `containers-verus/src/eclasses.rs`; every citation points there.

---

## See Also

- `semi-persistent-containers` crate: dense IDs, semi-persistent vectors, and container types
- `semi-persistent-traversals` crate: stack-safe tree traversal algorithms

---
[Table of Contents](00-table-of-contents.md) · [Overview: Why Semi-Persistent →](A0-overview.md)
