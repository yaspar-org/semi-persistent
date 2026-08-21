<!--
Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
SPDX-License-Identifier: Apache-2.0
-->
# E-Graph Class-Layer Integration

The e-graph uses the verified class kernel directly:

- `egraph::EClasses` aliases `containers-verus::EClasses`;
- `egraph::UnionFind` aliases `containers-verus::UnionFind`; and
- `egraph::ProofBuf` aliases the verified proof buffer.

There is no state-copying adapter. The engine supplies its
`Justification<G>` type and compile-time `TRACK`/`PROOFS` choices.

## Surface

The kernel provides:

- sequential singleton creation;
- `find` and read-only `find_const`;
- heuristic and directed union;
- justified union and proof-forest rerooting;
- class member and use-list rings;
- class size, atomicity, minimum-width, and per-operator minimum monomials;
- class merge and use-list splice;
- proof explanation into `ProofBuf`; and
- compositional `mark`/`restore`.

Operationally fallible forms return `ContainerError`; panic-shaped compatibility
wrappers preserve the engine's internal invariant checks.

## Invariants

`EClasses::wf()` contains W1 through W7, listed in the `eclasses.rs` module
header:

- row/key/ring agreement;
- representative and union-find agreement;
- class-member partitioning;
- use-list ownership and parent validity;
- archived-state agreement for outstanding marks;
- proof-column lockstep when `PROOFS = true`; and
- cached class-size agreement.

Every verified mutator preserves these clauses. Aggregate restore validates the
component tokens before mutating any column and then restores all columns in
lockstep.

## Proof Boundary

The ring, key, use-list, archive, size, and union-find storage transitions are
verified.

Proof-forest path reversal and LCA walking remain trusted executable glue over
verified columns. An end-to-end proof would add proof-forest acyclicity and show
that rerooting preserves it. This limitation is documented in the trust ledger
and must not be described as a verified explanation algorithm.

## Engine-Specific Policies

The engine computes directed-merge survivors from class size or use-list size
and passes that choice to the kernel. Completion metadata uses the per-class
minimum-monomial columns. These policies are engine logic; the kernel proves
that applying a valid choice preserves its representation invariants.

With `TRACK = false`, tracking branches and writes are removed by constant
specialization, while empty archive/fork fields remain in the generic
structure. With `PROOFS = false`, proof recording and history work are removed;
the option fields remain `None`.

## Conformance Scope

`containers-conformance` compares the verified kernel with the retained
unverified reference on finite traces and selected layouts. This is regression
evidence, not a universal equivalence theorem. The public protocol and known
semantic differences are in
[`containers-conformance/BASELINE.md`](../../../containers-conformance/BASELINE.md).

Machine-specific performance comparisons belong in the Criterion benches
listed by that protocol, not in this design chapter.
