# Semi-Persistent: A Semi-Persistent E-Graph Engine

[← Table of Contents](00-table-of-contents.md) · [Language Guide →](A1-language-guide.md)


## Why a New E-Graph?

E-graphs have a long history in automated reasoning, but their
modern revival began with egg (Willsey et al., POPL 2021), which
made equality saturation practical through rebuilding and e-class
analyses. egglog (Zhang et al., PLDI 2023) took the next step by
unifying Datalog and equality saturation into a single fixpoint
framework, introducing the key insight that pattern matching over
e-graphs is a relational join, and demonstrating the use of
worst-case-optimal leapfrog triejoin (Veldhuizen, ICDT 2014) for
e-matching.

These systems occupy distinct points in the design space without
bridging them. egg lacks backtracking, Datalog integration, and
relational pattern matching. egglog has no semi-persistent structure
and limited support for associative-commutative-idempotent (ACI)
operators. Soufflé is a high-performance Datalog engine but lacks
native e-graph support.

The engine synthesizes ideas from several lines of work into a single
coherent execution engine:

- Semi-persistent data structures (Conchon and Filliâtre, 2008)
  provide memory-cheap snapshots (a sparse diff, not a copy). For `b`
  fork-history links, `k` replayed entries, `r` regrown cells, `p`
  surviving-parent entries, and `w` materialized bitmap words, vector restore
  is O(b+k+r+p) with inline capture and O(b+k+r+p+w) with parallel capture.
  This vector bound excludes higher-level transient cache repair. The protocol
  enables backtracking and supplies change boundaries for semi-naive
  evaluation. Future stratified negation also needs a queryable frozen
  relation/equality view; the rollback token is not such a view.
- Matching modulo AC via canonization, inspired by the AC(X)
  decision procedure in Alt-Ergo (Conchon, Iguernlala, and Mebsout;
  Iguernlala, 2013), handles associative, commutative, and
  idempotent properties structurally rather than through rewrite
  rules.
- Relational e-matching uses leapfrog triejoin, as introduced by
  egglog, for worst-case-optimal multiway intersection. AC decomposition
  remains a separate branching stage and does not inherit that whole-algorithm
  bound.
- Variables and binders are future work (no binder support today). The
  planned approach parameterizes the e-graph over an edge-label algebra,
  with several candidate representations under consideration; see
  [Future Work](A3-future-work.md).

The contribution is making the implemented mechanisms coexist in a single
engine. Semi-persistence provides rollback frames; pattern matching treats the
e-graph's round snapshot as indexed relations; and a separate round-local
`touched` log defines the conservative delta used by semi-naive evaluation.
Rollback generations and semi-naive rounds are therefore related mechanisms,
not the same boundary. Datalog relation declarations and frozen stratum views
remain future work.

## Core Capabilities

### Semi-persistent backtracking

The entire e-graph state (nodes, e-classes, union-find, hash-cons
caches, literal store, registries) can be snapshotted with `(push)`
and restored with `(pop)`. A snapshot is a single frame push across all
containers; its *memory* cost is only the cells subsequently modified
(a sparse diff), never a copy of the e-graph: that is the decisive
saving. The push also resets capture state: inline storage clears the slots
named by the prior frame's diff, and parallel storage clears every
materialized bitmap word. Restore replays diffs, regrows popped cells, and
reconstructs the surviving parent frame's capture state; its exact complexity
is the backend-specific bound above, not O(1) and not solely O(k).
Each semi-persistent vector achieves this by recording only the first
write to each cell per generation (a diff-log protocol).

### Constant-work structural operations

Cached-head/tail singly linked lists for e-class use-lists make splice a
constant number of pointer/header updates; tracked first-write capture can
still grow a diff-log backing vector. Sparse sets with swap-and-pop give O(1)
membership and removal and amortized O(1) insertion for the set of canonical
representatives. The compressed union-find uses
path compression on the fast path while maintaining an uncompressed
proof path in a parallel array, so proof extraction does not sacrifice
find performance.

### Sound and extensible builtin operations

Primitive operations on machine-word types (i64, u64, f64) are checked
by default: overflow, division by zero, and lossy conversions panic
rather than silently producing wrong results. Wrapping and saturating
variants (`wrapping_add`, `saturating_mul`, etc.) require explicit
opt-in, so constant-folding rules are sound to execute by default and
the engine never derives false equalities from silent wraparound.
Arbitrary-precision types are also available: IBig (integers), UBig
(unsigned), and RBig (rationals) cannot overflow their numeric range, though
their `num-bigint`/`num-rational` representations can allocate as magnitude
grows. The `LitModel` trait makes the set of
concrete sorts and operations pluggable; users can define new builtin
types by implementing a single trait. Beyond numeric and string
types, the LitModel is also the extension point for abstract domains
(intervals, sets, tristate numbers for bitvector analysis, and so on)
and other value types used in lattice-valued merge operations.

### Native A/C/AC/ACI theories

Associative, commutative, and idempotent properties are handled
structurally through canonical representations rather than rewrite
rules. AC nodes store sorted multisets; ACI nodes store sorted sets
with deduplication; A nodes store sequences. Handling these properties
structurally avoids the combinatorial e-graph growth caused by the corresponding
rewrite encodings. Pattern matching dispatches
automatically based on the operator's registered kind.

**Caveat (AC congruence completeness):** the structural canonization
gives maximum-partition matching that is supported as sound by the
implementation argument and finite regression tests, not by a verified
matcher theorem. It avoids rewrite-encoding growth, but on its own it does
*not* provide full AC congruence closure: recanonicalizing
an AC node substitutes equal *atoms*, never equal *sub-sums*, so given
`+(a,b) = c` and `+(b,d) = e`, the entailed equality `+(c,d) = +(a,e)`
(via the shared `b`) is not discovered by canonization alone. The
missing steps, Kapur-style superposition and rule inter-reduction
(FSCD 2021 / LMCS 2023, including the semantic-property facets:
identity, idempotent, nilpotent, cancelative, inverse-pair), are
implemented in the completion pass, which runs in one of three modes:
**plain** (the default: canonization and congruence only, because rare
inputs can make completion extremely expensive and the implementation has no
general end-to-end termination theorem), **eager**
(`--derive-ac-eqs`: every rebuild attempts completion; only a `Converged`
outcome reports that one full implementation round made no change), and **lazy**
(`--lazy-ac-eqs`: a failing equality check runs goal-directed
completion inside a semi-persistent transaction and the restore
discards everything it minted). `--union-by` selects the merge
survivor policy on the verified per-class counters. See
[AC Congruence Completeness](ac-congruence-completeness.md) §13 for
the modes and [Future Work](A3-future-work.md) for the verification
plan.

### Relational pattern matching via leapfrog triejoin

Patterns compile to flat relational atoms. Their relational intersections use
worst-case-optimal leapfrog triejoin over four sorted index families
(`by_op`, `by_child_pos`, `by_repr`, `by_contains`). A cost-based
scheduler orders atoms from estimated selectivity in the default `Static`
mode. Optional `Runtime` scheduling chooses the next schedulable atom from live
bucket lengths for each partial binding, so it can execute middle-out and choose
different orders for sibling bindings. The production push matcher explores
the resulting lowered steps with depth-first continuation execution; that
control flow is not top-down pattern traversal.

### Maximal partition matching for AC/ACI

Multiset matching avoids multiplicity sub-count and residual-submultiset
enumeration: a selected element consumes its whole available multiplicity.
A bound scalar variable is found by a linear scan of the `d` distinct residual
entries, while an unbound scalar branches over those entries. With `k`
unbound scalar variables, the candidate assignment tree is at most `d^k`
before constraint and distinctness pruning; work per branch still includes
residual scans. The exponent is therefore pattern arity rather than numerical
multiplicity. This describes the shipped maximum-partition relation, which is
narrower than classical AC matching.

### Proof extraction

A dual-parent-pointer union-find maintains both a path-compressed
fast path and an uncompressed proof path. The proof path records
the justification for every merge (rewrite, congruence, or axiom).
Proof extraction walks the proof forest via LCA to find the shortest
chain connecting two nodes. A history bit on each e-node supports
copy-on-first-re-canonization, so the original node structure is
preserved for proof reconstruction.

### Datalog-style rules

Rules with multiple LHS patterns and multiple RHS actions express
Datalog-style reasoning. The saturation loop repeats rebuild, index, schedule,
match, and apply. It reports saturation when a full round produces no change;
an iteration limit or goal can stop a run earlier.

### Variables and binders (planned)

Binders are not supported today. The planned approach attaches a binding
annotation to each parent-to-child edge rather than to variables, so that
all occurrences of a variable can share one e-class and structural sharing
survives. The edge-label representation is parameterized; the candidate
encodings and the trade-offs between them are in
[Future Work](A3-future-work.md) and `doc/future/alpha-equivalence.md`.

## Architecture

The project is organized in layers, each building on the one below:

```
┌──────────────────────────────────────────────────┐
│  Interpreter: execute commands, drive saturation │
├──────────────────────────────────────────────────┤
│  Compilation: parse → sortcheck → resolve        │
├──────────────────────────────────────────────────┤
│  Matching: schedule → leapfrog join → apply      │
├──────────────────────────────────────────────────┤
│  E-Graph: nodes, classes, union-find, caches     │
├──────────────────────────────────────────────────┤
│  Containers: semi-persistent Vec, Map, SparseSet │
├──────────────────────────────────────────────────┤
│  Foundations: DenseId, Tagged, bit-packing       │
└──────────────────────────────────────────────────┘
```

The foundation layer provides 31-bit dense identifiers with a stolen
tag bit for inline capture tracking, enabling semi-persistent
containers with zero auxiliary storage per cell. The container layer
builds semi-persistent vectors (sparse-diff snapshots with backend-specific
capture-state rebuild costs), maps,
append-only vectors, sparse sets, and intrusive linked-list arenas.
The e-graph layer composes these containers into node storage,
e-classes with circular use-lists, a dual-array union-find, and
partitioned hash-cons caches. The matching layer builds sorted
indexes from scratch each iteration and executes relational queries
via leapfrog triejoin. The compilation layer parses a uniform
S-expression surface syntax, sort-checks and resolves patterns into
dense typed variable ids, and schedules query plans. The interpreter
drives the saturation loop and manages push/pop scoping.

## Key Design Decisions

### Bulk-rebuilt sorted indexes

Indexes are rebuilt from scratch each saturation iteration rather
than maintained incrementally. The current implementation uses sorted vectors,
whose contiguous layout is a good fit for full-index iteration and binary
search. Any current performance comparison with an arena-backed B+ tree must
come from the maintained Criterion benchmarks at the revision being evaluated;
this design chapter does not preserve a fixed ratio from an older run.

### Shrink at mark, not restore

Capacity reclamation happens during `mark()` (before the frame push),
not during `restore()`. Reclaiming at mark avoids costly reallocations
in tight exploratory loops; the vector naturally "learns" the right
capacity by ratcheting across branches.

### Source-of-truth vs derived state

The e-graph cleanly separates source-of-truth containers (node store,
union-find, literal store) from derived containers (hash-cons caches,
indexes). Source-of-truth containers participate in the diff-log
protocol. Derived containers are rebuilt from source-of-truth after
restore.

### Compile-time elision and retained state

The `TRACK` and `PROOFS` const generics eliminate work guarded by those
constants: disabled tracking performs no diff capture, and disabled proof
logging allocates no proof/history vectors or records proof edges. The generic
types still contain empty diff/frame/fork fields, proof/history `Option` fields
set to `None`, and general runtime guards. The claim is therefore that
feature-specific execution is erased while empty-state fields remain, not that
the complete type has zero or minimum layout or no general check overhead.

## Detailed Design

The chapters that follow describe each layer in detail:

- **Foundations** (dense ids, semi-persistent vectors and containers): documented in the `semi-persistent-containers` crate
- Chapters 1–5: E-graph core (nodes, classes, union-find, caches, canonization, rebuild)
- Chapters 6-9: Matching engine (indexes, leapfrog join, scheduling, pattern execution)
- Chapters 10-12: Language and compilation (surface syntax, sortcheck, rule application)
- Chapters 13-14: Literal model and soundness
- Chapters 15-16: Proofs and extraction
- Chapter 17: Interpreter and saturation loop
- Chapter 18: Semi-naive evaluation (`saturate_semi`: match only what changed each round, via the `touched` log, delta indexes, and the k-variant delta decomposition)
- Chapter 19: Anti-unification (exact memoized solver and Monte-Carlo graph search over the AND/OR graph of e-class-pair subproblems)
- Chapter 20: Index selectivity and adaptive matching (size-biased fan-outs,
  per-binding operator restriction and atom scheduling, sampled selectivity,
  and deferred watermark delta suffixes)
- [ac-algebraic-properties.md](ac-algebraic-properties.md) and [ac-congruence-completeness.md](ac-congruence-completeness.md): why multiset canonization breaks congruence completeness, and the Kapur-style completion that repairs it
- [ac-completion-spec.md](ac-completion-spec.md): the maintained
  `min_monomial` candidate, diagnostics, and a clause-by-clause implementation
  correspondence

## References

- Willsey, M., Nandi, C., Wang, Y.R., Flatt, O., Tatlock, Z., and
  Panchekha, P. "egg: Fast and Extensible Equality Saturation."
  POPL 2021. https://dl.acm.org/doi/10.1145/3434304

- Zhang, Y., Wang, Y.R., Flatt, O., Cao, D., Zucker, P., Roesner,
  E., Willsey, M., and Tatlock, Z. "Better Together: Unifying
  Datalog and Equality Saturation." PLDI 2023.
  https://dl.acm.org/doi/10.1145/3591239

- Veldhuizen, T.L. "Leapfrog Triejoin: A Simple, Worst-Case Optimal
  Join Algorithm." ICDT 2014. https://arxiv.org/abs/1210.0481

- Conchon, S. and Filliâtre, J.-C. "Semi-persistent Data
  Structures." ESOP 2008.

- Iguernlala, M. "Strengthening the Heart of an SMT-Solver: Design
  and Implementation of Efficient Decision Procedures." PhD thesis,
  Université Paris-Sud, 2013. (AC(X) canonized rewriting in Alt-Ergo.)

- Conchon, S., Iguernlala, M., and Mebsout, A. "Canonized Rewriting
  and Ground AC Completion Modulo Shostak Theories." 2012.
  https://arxiv.org/abs/1207.3262

- Schneider, R., Rossel, M., Shaikhha, A., Goens, A., and Steuwer,
  M. "Slotted E-Graphs: First-Class Support for (Bound) Variables
  in E-Graphs." PLDI 2025.
  https://dl.acm.org/doi/10.1145/3729326

---
[← Table of Contents](00-table-of-contents.md) · [Language Guide →](A1-language-guide.md)
