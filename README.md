# Semi-Persistent E-Graph

A semi-persistent equality saturation engine in Rust: memory-cheap snapshots
through sparse diffs rather than full copies.

Four contributions:

1. **Composable semi-persistence**: source-of-truth containers are built from
   the semi-persistent vector and its diff-log protocol. Transient hash-cons
   indexes and matching caches are reconstructed from that state after restore.
   Snapshot memory is sparse. `mark()` and restore also rebuild capture state:
   for fork-history links `b`, replayed entries `k`, regrown cells `r`,
   surviving-parent entries `p`, and materialized bitmap words `w`, vector
   restore is O(b+k+r+p) with inline flags and O(b+k+r+p+w) with parallel
   flags. This excludes caller-owned payload costs and higher-level transient
   cache repair.

2. **Native A/AC/ACI theories with leapfrog matching**: associative,
   commutative, and idempotent operators use sorted multisets, sets, and
   sequences rather than rewrite encodings. Maximum-partition AC matching
   avoids enumerating multiplicity sub-counts and residual sub-multisets. With
   `k` unbound scalar pattern variables and `d` distinct children it still
   branches O(d^k), exponential in pattern arity but independent of the
   numerical multiplicities.

3. **Proof logging with batch export**: a dual-parent-pointer union-find with
   copy-on-first-recanonization preserves original node structure. The
   `--proofs --dump-proofs FILE` mode builds one Euler-tour LCA index in O(n),
   performs O(1) LCA queries, and writes one deterministic proof-path record per
   e-node. These records are not yet independently replay-checked certificates.

4. **Anti-unification over the shared e-graph**: exact branch-and-bound and
   Monte-Carlo graph search operate over everything saturation has proved
   equal, so differently written rewrites can become shared structure.
   Exact-solver optimality, bounds, transport, and delegation have finite
   oracle/property evidence. The Verus crate proves objective and positional
   lower-bound lemmas; it does not yet prove `D = OPT` or refine the Rust
   AC/ACI solver. ([chapter 19](egraph/doc/design/19-anti-unification.md))

`TRACK=false` and `PROOFS=false` eliminate work guarded by those const
generics. The generic structs still retain empty diff/frame/fork fields and
`None` proof-column options, plus general runtime guards, so this is execution
elision with retained empty-state fields, not a zero-layout-overhead or
minimum-layout claim.

AC completion has three modes. Plain congruence closure is the default.
`--derive-ac-eqs` enables eager completion during rebuild;
`--lazy-ac-eqs` runs goal-directed completion on demand after a plain equality
check fails, then restores the transaction. A negative lazy check reports that
the implemented bounded search did not derive equality; it is not a proved
semantic disequality result.

The latest retained egglog comparison covers seventeen benchmarks (the
ten-benchmark ranked intersection plus seven second-pass additions,
`doc/benchmarks/`). Campaign
[`final-r6`](doc/benchmarks/records/campaigns/final-r6-tables.md) measured a
source snapshot based on `8f041483`, before the subsequent engine, container,
traversal, and AU changes on this branch. Its reported geometric means are
1.19x/1.11x for the rules encoding and 2.56x/2.69x over the eleven native
translations; its `acgen` rows are 0.12x/0.05x for explicit rules and
100x/111x for native AC. These are historical measurements of the recorded
binaries, not current-implementation performance claims. The campaign retains
all 750 process-wall samples and exact binary hashes, but ran under substantial
background load and did not compute bootstrap confidence intervals. Release
performance claims require a same-revision Criterion rerun with retained
bootstrap confidence intervals.

## Workspace

| Crate | Description |
|-------|-------------|
| [`semi-persistent`](semi-persistent/) | Umbrella crate re-exporting `containers`, `egraph`, and `traversals`; the `semi-persistent` CLI binary ships from the `egraph` crate. |
| [`containers-verus`](containers-verus/) | The engine's semi-persistent container layer, Verus-verified: `Vec`, `Map`, `SparseSet`, `ListArena`, circular lists, union-find, the e-class aggregate, `DenseSpanMap`. Snapshots use sparse diffs rather than copies; mark/restore also maintain backend-specific capture state. `egraph` consumes this crate as `semi-persistent-containers`. |
| [`containers`](containers/) | The unverified reference implementation of the container layer, kept as the differential-conformance oracle and performance baseline (`containers-conformance`). ([design docs](containers/doc/design/00-table-of-contents.md)) |
| [`egraph`](egraph/) | Equality saturation engine: e-graphs, e-matching, rewrite scheduling, term extraction, proofs. ([design docs](egraph/doc/design/00-table-of-contents.md)) |
| [`traversals`](traversals/) | Arena-based recursion schemes. Stack-safe folds, unfolds, transforms, zippers. Includes `traversals-derive` proc-macro. ([tutorial](traversals/TUTORIAL.md)) |
| [`abstract-domains`](abstract-domains/) | Verified bitvector abstract domains (Tnums, Anums, Unums, Intervals, reduced products). The ordinary Verus run reports 994 verified conditions and 0 errors at the enabled `u8`/`u16`/`u32`/`u64` widths; a CI source gate rejects project-local `admit()`/`assume()`. The pinned `vstd` dependency remains part of the trust boundary. Its executable Rust mirror participates in workspace builds and tests; proof checking runs separately under Verus. |

The live headline-claim inventory, with proved, measured, and argued statements
kept separate, is [`doc/claims.md`](doc/claims.md). It includes retractions and
the proof roadmap for claims not yet established.
[`doc/artifact.md`](doc/artifact.md) gives reproduction commands.
[`doc/paper/draft.md`](doc/paper/draft.md) is the future-paper draft; the
already-published short paper is retained unchanged as a historical artifact.

## Documentation

Design chapters live beside their crates:
[`egraph/doc/design/`](egraph/doc/design/00-table-of-contents.md),
[`containers-verus/doc/design/`](containers-verus/doc/design/00-table-of-contents.md),
[`containers/doc/design/`](containers/doc/design/00-table-of-contents.md).
Cross-cutting claims and reproduction instructions are under [`doc/`](doc/).
The egglog comparison and its public methodology live in
[`doc/benchmarks/`](doc/benchmarks/README.md). Future feature specifications
remain beside the crates they extend.

## Building

```bash
# Build every workspace crate with stable Rust.
# Verus proof items erase under rustc.
cargo build --workspace

# Run the default runtime, property, and documentation tests.
cargo test --workspace

# Cover optional features, examples, benches, and feature-gated binaries.
cargo build --workspace --all-targets --all-features
cargo test --workspace --all-features

# Verify the proof-carrying crates with the pinned Verus toolchain.
(cd abstract-domains && cargo verus verify)
(cd containers-verus && cargo verus verify)
(cd containers-verus && cargo verus verify --features literal-types)
(cd au-verus && cargo verus verify)
```

## Design Principles

- **Correctness first**: proofs and tests before optimization.
- **Compact indexed storage**: use typed dense IDs, spans, and reusable arenas
  on measured hot paths. Allocation and code-generation claims are
  path-specific rather than inferred from an abstraction.
- **Semi-persistence as the unifying mechanism**: the generational protocol
  yields memory-cheap rollback and change boundaries for semi-naive evaluation.
  Future stratified negation additionally needs a queryable frozen relation and
  equality view; a rollback token alone is not such a snapshot.

## Security

See [CONTRIBUTING](CONTRIBUTING.md#security-issue-notifications) for more information.

## License

This project is licensed under the Apache-2.0 License.
