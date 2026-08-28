# Changelog

## [Unreleased]

## [0.3.0] - 2026-08-28

### Added

- Added the Semper book, with executable examples covering the language,
  algebraic canonization, saturation, anti-unification, and policy repair.

### Changed

- Made malformed algebraic declarations and rule right-hand sides fail during
  resolution instead of relying on unchecked representation invariants.
- Clarified that anti-unification optimality is relative to the equalities
  materialized in the selected e-graph completion mode.
- Aligned every workspace package and internal published dependency at
  version `0.3.0`.

### Fixed

- Honored `:assoc-left` and `:assoc-right` flattening directions during both
  source-term construction and rewrite right-hand-side construction.
- Rejected algebraic operators whose argument and result sorts make variadic
  singleton collapse unsound, as well as conflicting associativity tags.
- Added lexically scoped right-hand-side comprehension locals without mutating
  query match shapes or runtime match rows.
- Enforced collection element sorts, fixed right-hand-side arity, and
  literal-producing comprehension filters.
- Rebuilt before every `run :until` observation, including the final
  observation after exhausting the rule-round budget.

## [0.2.0] - 2026-08-25

### Added

- Published `semi-persistent-containers-verus`, the executable
  Verus-verified container layer used by the e-graph.
- Added canonical license, conduct, contribution, and security documents to
  every workspace package, with a CI gate for package metadata and source
  headers.
- Added Exact and Monte Carlo graph search for e-graph anti-unification,
  including explicit cycle policies and rewrite-aware semantic diffing.
- Added native associative, commutative, and idempotent canonization across
  construction, matching, and anti-unification.
- Added plain, eager, and goal-directed lazy AC congruence-closure modes.
- Added deterministic batch proof-path export using an Euler-tour LCA index.

### Changed

- Switched `semi-persistent-egraph` to the verified container implementation;
  the independent Rust implementation remains available as a differential and
  performance reference.
- Reworked AC matching around maximum partitions so its exponential factor is
  in pattern variables and distinct children rather than child multiplicity.
- Made pool-backed variadic recursion-scheme nodes traversable and deduplicated
  by their child sequences.
- Aligned every workspace package and internal published dependency at
  version `0.2.0`.

### Verification

- Added differential, property, layout, and regression coverage between the
  verified and reference container implementations.
- Added Verus proofs for the container protocol and selected
  anti-unification objective and lower-bound lemmas. The exact scope and
  remaining obligations are maintained in [`doc/claims.md`](doc/claims.md).
