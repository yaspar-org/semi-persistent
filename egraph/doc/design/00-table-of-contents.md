# Semi-Persistent E-Graph — Design Documents

[Table of Contents](00-table-of-contents.md) · [Overview: Why A Semi-Persistent EGraph →](A0-overview.md)

The foundational data structures (dense IDs, semi-persistent vectors, containers) are documented in the `semi-persistent-containers` crate documentation.

## Overview and Guides

- **[Overview: Why A Semi-Persistent Egraph?](A0-overview.md)**
  Intellectual lineage (egg, egglog, semi-persistence, AC
  canonization). Core capabilities: O(1) snapshots, native
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
  Planned features as standalone designs: variables and binders; cost-based extraction
  via partial weighted Max-SAT; stratified negation. Plus the remaining work on AC
  completion (enable-by-default scoping, multiple AC symbols, verification); the
  implemented algorithm itself is in the AC chapter and Ch 14.

- **[AC Congruence Completeness](ac-congruence-completeness.md)**
  Part I explains why flattening AC nodes into canonical multisets erases the 
  intermediate sub-sum subterms and breaks congruence completeness
  (even though matching stays complete), and why `rest`-variable
  matching doesn't restore completeness. Part II gives the fix — Kapur-style
  inter-reduction and lcm-superposition critical pairs — and shows it can reuse
  our existing `DecomposeAC`/`by_contains` machinery, with a correctness/termination
  argument and a proof sketch. Status and verification plan live in Future Work.

- **[AC Completion: `min_monomial`, the matcher bug, and a code-compliance review](ac-completion-spec.md)**
  A focused companion to the above (does not restate it). Defines `min_monomial`, the leximin AC
  representative of a class, with its exact properties and how it yields the tightest
  closure; traces the `(f (add x ..r1) (add x ..r2))` matcher bug over concrete nodes
  (cause and fix); and checks the code clause-by-clause against the algorithm, explaining
  the observed per-round growth as the genuine basis size on a dense, deeply-merged graph
  (not a bug, and not an artifact of approximate `min_monomial`).

## Part I: E-Graph Core

1. **[Node Representation and Storage](01-node-storage.md)**
   `FixedArityNode`, `VariableArityNode`, `LitNode`. Pool-allocated
   children for variable-arity. `NodeStore` with typed routing table.
   `NodeRef` enum for dispatch. History bit for proof logging.

2. **[E-Classes and Union-Find](02-classes-and-union-find.md)**
   `UnionFind` with path compression and union-by-rank.
   `EClasses`: circular use-lists for parent tracking, splice on merge.
   `MergeInfo` for worklist-driven rebuild. Proof-justified union.

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
   Built from scratch each saturation iteration. `SortedVec` with
   leapfrog-compatible cursor.

7. **[Leapfrog Triejoin](07-leapfrog.md)**
   `LeapfrogJoin` over sorted iterators. Worst-case optimal multi-way
   intersection. Seek-based advancement.

8. **[Query Compilation and Scheduling](08-query-compilation.md)**
   Atoms → execution plan. Cost-based variable ordering. Eager pass
   for bound nodes. E-class–aware re-join for `ExtractChild` results.
   `LitBind` deferred to cost-based selection.

9. **[Pattern Matching Execution](09-pattern-matching.md)**
   DFS backtracking engine. `Step` variants: `Join`, `ExtractChild`,
   `ExpandA`, `DecomposeAC`, `DecomposeACI`. Subsequence, subset, and
   sub-multiset matching. Maximum partition semantics for AC.
   Multiplicity constraints with interval intersection.

## Part III: Language and Compilation

10. **[Surface Language and Parser](10-surface-language.md)**
    Unified `(op children...)` syntax. `SurfacePattern` with
    prefix/suffix rest vars. `RhsTerm` with comprehensions.
    No bracket dispatch — operator kind resolved later.

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
    `intern`/`try_lookup`. Deferred interning: sortcheck never mutates.
    LHS matching is read-only. RHS application interns on demand.

## Part V: Soundness, Completeness, Proof Extraction, Term Extraction

14. **[Soundness and Completeness](14-soundness.md)**
    The two correctness properties over both sources of derived equalities,
    literal evaluation and congruence closure, and across operator kinds
    (plain, C, A, AC, ACI). Soundness: no false equality is asserted.
    Completeness: every entailed equality between materialized terms is decided,
    requiring the AC completion pass for AC/ACI. What is proved, argued, assumed.

15. **[Proof Logging](15-proof-logging.md)**
    Copy-on-first-re-canonization via history bit. `Justification`
    enum: `Rewrite`, `Congruence`, `Axiom`. Dual parent pointers
    (`parent_fast` + `parent_proof`). Two LCA algorithms: naive
    walk-up for single queries, Euler-tour BFC for batch extraction.
    `ProofBuf` for path extraction. `PROOFS` const generic.

16. **[Term Extraction](16-extraction.md)**
    Bottom-up cost model. `extract_best` via BFS over e-classes.
    `reconstruct` for pretty-printing.

## Part VI: Interpreter and Saturation

17. **[Interpreter and Saturation Loop](17-interpreter.md)**
    `Interpreter` executes `CCommand` sequence. `saturate`:
    rebuild → index → schedule → match → apply. Push/pop scoping.
    `GlobalCtx` for let-bound names.

## Part VII: Incremental Saturation

18. **[Semi-Naive Evaluation](18-semi-naive-evaluation.md)**
    `saturate_semi`: match only what changed each round via the
    k-variant delta decomposition. `touched` log on the e-graph +
    `IndexStore::build_delta`; `VariantIndex` three-way mode
    (delta / full∖delta / full) realized on `Step::Join` via the
    `Difference` cursor combinator. Per-atom, per-flavor scheduling.
    Selectable via `SaturationStrategy` / `--strategy semi-naive`;
    default remains naive, with no automatic fallback.

---

## See Also

- `semi-persistent-containers` crate — dense IDs, semi-persistent vectors, and container types
- `semi-persistent-traversals` crate — stack-safe tree traversal algorithms

---
[Table of Contents](00-table-of-contents.md) · [Overview: Why Semi-Persistent →](A0-overview.md)
