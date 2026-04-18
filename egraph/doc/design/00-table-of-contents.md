# Semi-Persistent E-Graph — Design Documents

[Table of Contents](00-table-of-contents.md) · [Overview: Why A Semi-Persistent EGraph →](A0-overview.md)

The foundational data structures (dense IDs, semi-persistent vectors, containers) are documented in the `semi-persistent-containers` crate documentation.

## Overview and Guides

- **[Overview: Why A Semi-Persistent Egraph?](A0-overview.md)**
  Intellectual lineage (egg, egglog, semi-persistence, AC
  canonization, director strings). Core capabilities: O(1)
  snapshots, native A/C/AC/ACI, leapfrog triejoin, proof
  extraction, variables and binders via director bitmatrices.
  Architecture and key design decisions.

- **[Language Guide](A1-language-guide.md)**
  Surface syntax, sorts, operators, algebraic attributes, rewrite
  rules, variadic matching, push/pop, saturation, compilation pipeline.

- **[Developer Guide: Extending the Literal Model](A2-developer-guide.md)**
  The `LitModel` trait, defining new builtin sorts and operations,
  how builtins are lifted into the e-graph, deferred interning,
  soundness guarantees.

- **[Future Work and Recently Completed Features](A3-future-work.md)**
  Implemented: globals in patterns. Planned: variables and binders
  (parameterized edge labels),
  cost-based extraction via partial weighted Max-SAT, stratified
  negation.

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
   `ACCanon` (sorted multiset, merge multiplicities),
   `ACICanon` (sorted set, deduplicate). The `VarCanon` trait.

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

## Part IV: Literal Model and Soundness

13. **[Extensible Literal Model](13-literal-model.md)**
    `LitModel` trait: `sorts`, `ops`, `parse`, `is_truthy`.
    `BignumModel`, `MachineModel`, `AllModel`. `LitValStore` with
    `intern`/`try_lookup`. Deferred interning: sortcheck never mutates.
    LHS matching is read-only. RHS application interns on demand.

14. **[Soundness of Primitive Operations](14-soundness.md)**
    Why literal ops must be congruence-compatible. The `@`-prefixed
    auto-lift ops. Sort architecture: concrete vs user sorts.
    No implicit bridging.

## Part V: Proofs and Extraction

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

---

## See Also

- `semi-persistent-containers` crate — dense IDs, semi-persistent vectors, and container types
- `semi-persistent-traversals` crate — stack-safe tree traversal algorithms

---
[Table of Contents](00-table-of-contents.md) · [Overview: Why Semi-Persistent →](A0-overview.md)
