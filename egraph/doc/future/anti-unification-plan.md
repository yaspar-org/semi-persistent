# Anti-Unification Implementation Plan

## Delivered / Deferred (status after milestone 1)

**Delivered**: snapshot + SCC reachability; search-space layer with cycle contexts
(both `CycleMode`s); per-kind action generation (ordered, SPair, AC matrices, ACI,
literals); hash-consed term pool with variant projection; syntactic seed; exact
solver (unbounded matrix enumeration — the oracle is exact); MCGS with UCT selection,
round-robin AND allocation, greedy rollout, path backpropagation with idempotent
value recomputation and result composition; `anti_unify()` public API; `au_demo`
example. Results are ranked by `(size, variant_mass)` lexicographically — a
deliberate extension: at equal size the candidate with more backbone wins.

**Deferred**: PUCT and prior processors (§A.6); `uct_and`/`lct_and` AND selectors;
lazy-AC chain states (§3.4.4 — MCGS truncates at `A_max`, exact enumerates all);
semi-persistent containers, whole-search mark/restore, `SearchSession`/`SearchToken`
(§4.7); interpreter commands (§6); completion counter and exploitation-ratio
reporting (§3.3.7–3.3.8); golden traces; fixture-corpus end-to-end runs.

Implementation plan for `doc/future/anti-unification-mcgs.md` (the design). One commit per
phase; each commit leaves the tree fully green (`cargo build`, `cargo test`, `cargo fmt`,
`cargo clippy`). The Python reference implementation lives in
`~/projects/SocratesCompass/symbolic-au/` and answers behavioral questions the design
leaves open.

## Decisions taken up front

- **Borrowed e-graph, owned side tables.** The snapshot holds `&EGraph` for node-level
  reads (op, children, flags) and owns only the derived tables the e-graph does not
  index: per-class members grouped by operator, best size/term per class, SCC
  reachability. All stored ids are canonized once at snapshot build (`find_const`);
  the search never touches the union-find afterwards.
- **`AuClassId`** (`define_id31!`) is the dense class index used by every table, context,
  and bitset. Minted only by the snapshot's representative-to-dense map, so
  non-canonical or cross-version ids cannot enter search state.
- **Contexts are interned** as sorted `AuClassId` vectors behind `CtxId`; the node-cache
  key `(l, r, ctxL, ctxR)` is 4 copyable ids.
- Milestone scope per the design: equal-length Seq zip only; equal-total AC matrices
  only (unequal totals fall back to the syntactic seed); lazy-AC chain states for
  `T(M,N) > A_max`; no learned priors (uniform/ranked/votes/full_dist processors, no
  model integration).

## Phases

1. **Snapshot + reachability** (`au/egraph_api.rs`) — dense class table, members grouped
   by op (excluding `FLAG_SUBSUMED`), best-term fixpoint (A.2), Tarjan SCC + one bitset
   per SCC (§2.4). Error: `NoFiniteRepresentative`.
2. **Search-space layer** (`au/space.rs`) — context interner, `OrArena`/`AndArena`,
   node/edge caches, `CycleMode`, child-context derivation (§2.3).
3. **Action generation** (`au/actions.rs`) — per-kind dispatch (§3.4): positional zip,
   SPair orientations, AC matching-count matrices (greedy-first order, `A_max` bound,
   lazy chain states), ACI bijections, literal value match. Cached per `(l, r)`,
   cycle-filtered per node. Appendix B pinned as a unit test.
4. **Terms + results** (`au/terms.rs`, `au/results.rs`) — hash-consed term pool with
   canonical AC child order, sizes (Variants cost 0), variant projection, syntactic
   seed (A.3), best-result table (strict improvement, write-once exact flag).
5. **Exact solver** (`au/exact.rs`) — `eager_with_memo` (§3.2), memo
   `Empty/Visiting/Solved` indexed by `OrId`, publishes exact flags.
6. **MCGS** (`au/stats.rs`, `au/mcgs.rs`, `au/policy.rs`) — statistics overlay
   (edge visits, idempotent Q recomputation, reverse parent links), greedy rollout
   (A.4), UCT/PUCT selection (§3.3.4), AND selectors (§3.3.5), prior processors (A.6),
   completion counter (§3.3.7). Oracle-equality tests vs phase 5.
7. **Session + commands** (`au/session.rs`, interpreter) — whole-search
   `mark()`/`restore(token)` (§4.7), `(anti-unify …)` / `(check-au …)` commands (§6),
   fixture-corpus conformance runs, mark/restore property tests.

## Test gates per phase

- P1: reachability on a known cyclic graph; best-size on AC multiplicities.
- P2: context derivation at a cycle; node-cache sharing on acyclic regions (empty ctx).
- P3: Appendix B (6 actions), repeated-children single matrix, greedy counterexample
  (§3.4.4) reachable, SPair dedup when a=b.
- P4: seed/projection round-trip; strict-improvement monotonicity.
- P5: exact sizes on hand-built small graphs; termination under both cycle modes.
- P6: MCGS-to-completion == exact size on small instances; every intermediate result
  valid (both projections in root classes) and ≥ oracle optimum.
- P7: end-to-end .egg scripts over the tests/au_reference_fixtures.rs corpus;
  mark/restore state equality property test.
