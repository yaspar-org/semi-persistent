# Semi-Persistent E-Graph

A semi-persistent equality saturation engine in Rust: memory-cheap snapshots (a sparse diff rather than a full copy) and O(k) restore across all core data structures.

Three contributions:

1. **Pervasive semi-persistence**: every data structure is built from a single semi-persistent vector primitive with a diff-log protocol. Mark/restore composes automatically across the union-find, node stores, hash-cons caches, and registries. Enables embedding equality saturation inside backtracking search (SAT, SMT, constraint propagation).

2. **Native A/AC/ACI theories with leapfrog matching**: associative, commutative, and idempotent operators are handled structurally through canonical representations (sorted multisets for AC, sorted sets for ACI, sequences for A), not rewrite rules. Pattern matching extends leapfrog triejoin with maximum partition semantics: branching is over distinct elements, not multiplicities, avoiding exponential blowup.

The engine is compared against egglog on a ten-benchmark intersection set
(`comparison/`): rules encoding at parity on solver-dominated workloads,
native AC 2.4-2.8x faster, in the current campaign
(`comparison/final/final-r3-tables.md`).

3. **Proof logging with compile-time opt-out**: a dual-parent-pointer union-find with copy-on-first-re-canonization preserves original node structure for proof reconstruction. Euler-tour LCA enables O(n) preprocessing, O(1)-per-query batch extraction. A `const PROOFS: bool` generic eliminates all proof machinery at compile time when not needed.

Both semi-persistence (`const TRACK: bool`) and proof logging (`const PROOFS: bool`) are compile-time opt-out with zero residual overhead when disabled.

## Workspace

| Crate | Description |
|-------|-------------|
| [`semi-persistent`](semi-persistent/) | CLI front-end and integration surface for the engine. |
| [`containers-verus`](containers-verus/) | The engine's semi-persistent container layer, Verus-verified: `Vec`, `Map`, `SparseSet`, `ListArena`, circular lists, union-find, the e-class aggregate, `DenseSpanMap`. Snapshots cost only the changed cells (a sparse diff, not a copy); O(k) restore. `egraph` consumes this crate as `semi-persistent-containers`. |
| [`containers`](containers/) | The unverified reference implementation of the container layer, kept as the differential-conformance oracle and performance baseline (`containers-conformance`). ([design docs](containers/doc/design/00-table-of-contents.md)) |
| [`egraph`](egraph/) | Equality saturation engine: e-graphs, e-matching, rewrite scheduling, term extraction, proofs. ([design docs](egraph/doc/design/00-table-of-contents.md)) |
| [`traversals`](traversals/) | Arena-based recursion schemes. Stack-safe folds, unfolds, transforms, zippers. Includes `traversals-derive` proc-macro. ([tutorial](traversals/TUTORIAL.md)) |
| [`abstract-domains`](abstract-domains/) | Verified bitvector abstract domains (Tnums, Anums, Unums, Intervals, reduced products). 754 Verus proofs, 0 admits. Built separately from the default workflow. |

## Building

```bash
# Build all crates (except Verus-only ones)
cargo build

# Run all tests. containers-verus builds as a dependency of egraph; the
# excludes skip its own test suites and abstract-domains', which run under
# the Verus toolchain below.
cargo test --workspace --exclude semi-persistent-abstract-domains --exclude semi-persistent-containers-verus

# Verify the proof-carrying crates (Verus toolchain)
cd abstract-domains && cargo verus verify
cd containers-verus && cargo verus verify
```

## Design Principles

- **Correctness first**: proofs and tests before optimization.
- **Zero-overhead abstractions**: pool indices, not heap allocations, on hot paths. `Copy` over `Clone` for all pool-index and bitfield types.
- **Semi-persistence as the unifying mechanism**: the same generational protocol that yields memory-cheap snapshots also supplies stratum boundaries for stratified negation and rollback for exploratory search.

## Security

See [CONTRIBUTING](CONTRIBUTING.md#security-issue-notifications) for more information.

## License

This project is licensed under the Apache-2.0 License.
