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
  provide memory-cheap snapshots (a sparse diff, not a copy) and O(k)
  restore, enabling backtracking and stratification through the same
  generational mechanism.
- Matching modulo AC via canonization, inspired by the AC(X)
  decision procedure in Alt-Ergo (Conchon, Iguernlala, and Mebsout;
  Iguernlala, 2013), handles associative, commutative, and
  idempotent properties structurally rather than through rewrite
  rules.
- Relational e-matching via leapfrog triejoin, as introduced by
  egglog, provides worst-case-optimal pattern matching.
- Parameterized edge labels for variables and binders. The e-graph
  is parameterized over a `PortAlgebra` trait that abstracts the edge
  representation. Two binder-aware instantiations are supported:
  directors (positional ports with partial-injection matrices,
  inspired by Sinot, Fernández, and Mackie 2005) and slotted
  e-graphs (named slots with renaming maps, Schneider et al. PLDI
  2025). The default instantiation carries no labels (classic
  e-graph, no binder support).

The contribution of The project is making all these mechanisms coexist in
a single engine. Semi-persistence is the unifying mechanism: the
e-graph's hash-cons is a functional database, pattern matching is a
relational join, and generations serve as both undo checkpoints and
stratum boundaries.

## Core Capabilities

### Semi-persistent backtracking

The entire e-graph state (nodes, e-classes, union-find, hash-cons
caches, literal store, registries) can be snapshotted with `(push)`
and restored with `(pop)`. A snapshot is a single frame push across all
containers; its *memory* cost is only the cells subsequently modified
(a sparse diff), never a copy of the e-graph — that is the decisive
saving. (The push also resets each container's per-cell capture flags,
which is sublinear, not a copy; see the containers design docs.) Restore
is O(k), where k is the number of cells modified since the snapshot, not
the total size of the e-graph.
Each semi-persistent vector achieves this by recording only the first
write to each cell per generation (a diff-log protocol).

### O(1) algorithms where possible

Circular intrusive linked lists for e-class use-lists give O(1)
splice on merge, with no allocation and no traversal. Sparse sets
with swap-and-pop give O(1) membership test, insert, and delete for
the set of canonical representatives. The compressed union-find uses
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
(unsigned), and RBig (rationals) cannot overflow, though they consume
more memory; values that exceed their inline 128-bit representation
spill to a heap-allocated box. The `LitModel` trait makes the set of
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
structurally prevents the combinatorial e-graph bloat that occurs when
they are encoded as rewrite rules. Pattern matching dispatches
automatically based on the operator's registered kind.

**Caveat (AC congruence completeness):** the structural canonization
gives correct matching and prevents the exponential blowup, but it
does *not* provide full AC congruence closure. Rebuild re-canonicalizes
AC nodes but generates no AC critical pairs: given `+(a,b) = c` and
`+(b,d) = e`, the entailed equality `+(c,d) = +(a,e)` (via the shared
`b`) is not discovered. Our rebuild is Kapur's ground AC-CC algorithm
minus its completion steps (we have the union-find and node
re-canonicalization; we lack superposition and rule inter-reduction).
Closing the gap means adding those steps — a known extension (Kapur,
FSCD 2021). See
[AC Congruence Completeness](ac-congruence-completeness.md) for the full
problem/fix analysis and [Future Work](A3-future-work.md) for status.

### Relational pattern matching via leapfrog triejoin

Patterns compile to flat relational atoms joined by a
worst-case-optimal leapfrog triejoin over four sorted index families
(`by_op`, `by_child_pos`, `by_repr`, `by_contains`). A cost-based
scheduler orders variables by estimated selectivity each iteration.
The execution engine is a lazy DFS stack machine with static dispatch.

### Maximal partition matching for AC/ACI

Multiset matching avoids the exponential blowup of multiplicity
sub-count enumeration. Each concrete element's total count is bound
in O(1) and removed from the residual pool. Combinatorial branching
is restricted to the distribution of unique residual elements among
unbound variables.

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
Datalog-style reasoning. The saturation loop (rebuild, index, schedule,
match, apply) runs rules to fixpoint.

### Variables and binders (planned)

Director bitmatrices attached to e-graph edges encode variable routing
without making variables context-dependent. All variable occurrences
share a single anonymous `Var` e-class; binding context is carried
by the parent edge's bitmatrix annotation. The bitmatrix is packed
into a u64 inline with the child e-class id (covering arities up to
7 × 9), with a spill path for larger arities. This encoding avoids
the cascading index shifts of de Bruijn representations and the
permutation group complexity of slotted e-graphs.

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
builds semi-persistent vectors (sparse-diff snapshots, O(k) restore), maps,
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
than maintained incrementally. Benchmarks at 10M elements show
sorted-Vec iteration is 13× faster than arena-backed B+Trees. Since
the join phase iterates the full index repeatedly for every rule,
iteration speed dominates.

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

### Compile-time elision

The `TRACK` and `PROOFS` const generics eliminate semi-persistence
and proof-logging overhead at compile time when not needed. A
non-backtracking, non-proof-logging configuration pays zero cost for
these features.

## Detailed Design

The chapters that follow describe each layer in detail:

- **Foundations** (dense ids, semi-persistent vectors and containers) — documented in the `semi-persistent-containers` crate
- Chapters 1–5: E-graph core (nodes, classes, union-find, caches, canonization, rebuild)
- Chapters 6-9: Matching engine (indexes, leapfrog join, scheduling, pattern execution)
- Chapters 10-12: Language and compilation (surface syntax, sortcheck, rule application)
- Chapters 13-14: Literal model and soundness
- Chapters 15-16: Proofs and extraction
- Chapter 17: Interpreter and saturation loop

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

- Sinot, F.-R., Fernández, M., and Mackie, I. "Lambda-Calculus with
  Director Strings." APAL, 2005.

- Kennaway, R. and Sleep, R. "Director Strings as Combinators."
  ACM TOPLAS, 1988.

- Schneider, R., Rossel, M., Shaikhha, A., Goens, A., and Steuwer,
  M. "Slotted E-Graphs: First-Class Support for (Bound) Variables
  in E-Graphs." PLDI 2025.
  https://dl.acm.org/doi/10.1145/3729326

---
[← Table of Contents](00-table-of-contents.md) · [Language Guide →](A1-language-guide.md)
