# semi-persistent-containers (reference implementation)

The unverified reference implementation of the semi-persistent containers.
The e-graph engine does not link this crate: `egraph/Cargo.toml` aliases
`semi-persistent-containers` to `semi-persistent-containers-verus`, the
verified implementation, and that crate's containers are what the engine
runs on.

This crate serves two roles:

- **Conformance oracle.** `containers-conformance/` runs differential tests
  of the verified containers against these, method by method.
- **Performance baseline.** The production-vs-verus comparisons in
  [`containers-conformance/BASELINE.md`](../containers-conformance/BASELINE.md)
  measure against the implementations here.

The `union_find` and `eclasses` modules preserve the hand-written production
algorithms removed by the verified-container adoption in commit `cb1a5fe`
(the reachable pre-adoption tree is its parent, `df5b7fe`). Moving them here
removes dead alternate implementations from `egraph` without discarding them.
Their justification payload is generic rather than tied to the engine's rule
enum, and they use the current count and index APIs plus the current
directed-rank saturation contract. Proof-buffer scratch fields are public, as
they are in the verified crate, because the e-graph's deep explanation pass
borrows them across the crate boundary. The union, proof-forest, class-ring,
use-list, and restore algorithms remain the former production ones.
`containers-conformance/tests/egraph_reference_differential.rs` compares them
with the verified kernel over randomized traces and proof reconstruction.

The design documentation under `doc/design/` describes the data structures;
the proofs about their verified counterparts live in
`containers-verus/doc/design/`.

## License

Apache-2.0.
