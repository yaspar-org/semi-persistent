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

The design documentation under `doc/design/` describes the data structures;
the proofs about their verified counterparts live in
`containers-verus/doc/design/`.

## License

Apache-2.0.
