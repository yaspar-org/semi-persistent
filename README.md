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

4. **Anti-unification over the shared e-graph**: Exact, Monte-Carlo graph
   search, and both hybrid paths share an explicit side- or ordered-pair cycle
   policy. Pair-mode Exact uses bounded relaxation over the finite ordered-pair
   graph; the side modes solve their filtered contextual graphs. All modes
   operate over everything saturation has proved equal, so differently written
   rewrites can become shared structure. Optimality, bounds, transport, and
   delegation have finite oracle/property evidence. The Verus crate proves
   objective and positional lower-bound lemmas; it does not yet prove
   `D* = OPT` or refine the Rust AC/ACI solver.
   ([chapter 19](egraph/doc/design/19-anti-unification.md))

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

The latest retained egglog comparison is historical evidence, not a benchmark
of the `0.2.0` implementation. It covers seventeen benchmarks (the
ten-benchmark ranked intersection plus seven second-pass additions,
`doc/benchmarks/`). Campaign
[`final-r6`](doc/benchmarks/records/campaigns/final-r6-tables.md) measured a
source snapshot based on `8f041483`, before the later engine, container,
traversal, and AU changes included in `0.2.0`. Its reported geometric means are
1.19x/1.11x for the rules encoding and 2.56x/2.69x over the eleven native
translations; its `acgen` rows are 0.12x/0.05x for explicit rules and
100x/111x for native AC. These are historical measurements of the recorded
binaries, not current-implementation performance claims. The campaign retains
all 750 process-wall samples and exact binary hashes, but ran under substantial
background load and did not compute bootstrap confidence intervals. Release
performance claims require a same-revision Criterion rerun that retains
bootstrap confidence intervals.

## Example: Catching an Autoformalization Divergence

A most-specific anti-unifier is the dual of a most-general unifier. Give the
engine two first-order formalizations of the same sentence and Exact search
computes their most-specific anti-unifier under the selected e-graph theory and
cycle policy: a shared backbone with `Variants` nodes at the remaining
differences. Declared algebraic laws are handled during canonization, and
rewrite rules can add domain-specific equalities before the diff.

Consider this policy:

> A cross-region replication request is permitted only if the source bucket
> has versioning enabled and the destination bucket lies in an approved region.
> If the object is tagged confidential, the destination and source accounts
> must be the same and server-side encryption with a customer-managed key must
> be in effect. Objects up to the multipart threshold are copied directly;
> larger objects require a multipart copy.

The complete signature is below. `Formula` is the symbolic formula sort;
`Lit` embeds the engine's concrete `bool` literal sort, whose values are
`true` and `false`. `And` and `Or` are variadic ACI operators with
`(Lit true)` and `(Lit false)` as their respective neutral elements, and `Eq`
is commutative. These declarations add only the stated algebraic laws; other
Boolean laws would require explicit rewrites.

```lisp
(sort Formula)
(sort Int)
(sort Bucket)
(sort Object)
(sort Region)
(sort Account)

(function Lit (bool) Formula)
(function And (Formula) Formula :assoc-comm-idem :identity (Lit true))
(function Or (Formula) Formula :assoc-comm-idem :identity (Lit false))
(function Implies (Formula Formula) Formula)
(function Ite (Formula Formula Formula) Formula)
(function Eq (Account Account) Formula :comm)
(function Lt (Int Int) Formula)
(function Lte (Int Int) Formula)

(function src () Bucket)
(function dst () Bucket)
(function obj () Object)
(function regionOf (Bucket) Region)
(function accountOf (Bucket) Account)
(function sizeOf (Object) Int)
(function multipartThreshold () Int)

(function permit () Formula)
(function sseCmk () Formula)
(function directCopy () Formula)
(function multipartCopy () Formula)
(function versioningOn (Bucket) Formula)
(function approvedRegion (Region) Formula)
(function usEast1 (Region) Formula)
(function euWest1 (Region) Formula)
(function taggedConfidential (Object) Formula)
```

This is a ground first-order instance for one request: `src`, `dst`, and `obj`
are nullary constants in the signature.

Two independently produced formalizations use that signature:

```lisp
; Encoding A
(let formulaA
  (Implies (permit)
    (And
      (versioningOn (src))
      (approvedRegion (regionOf (dst)))
      (Implies
        (taggedConfidential (obj))
        (And
          (Eq (accountOf (dst)) (accountOf (src)))
          (sseCmk)))
      (Ite
        (Lte (sizeOf (obj)) (multipartThreshold))
        (directCopy)
        (multipartCopy)))))

; Encoding B
(let formulaB
  (Implies (permit)
    (And
      (Ite
        (Lt (sizeOf (obj)) (multipartThreshold))
        (directCopy)
        (multipartCopy))
      (Implies
        (taggedConfidential (obj))
        (Or
          (Eq (accountOf (src)) (accountOf (dst)))
          (sseCmk)))
      (Or
        (usEast1 (regionOf (dst)))
        (euWest1 (regionOf (dst))))
      (versioningOn (src)))))

(antiunify formulaA formulaB :algorithm exact)
```

They have five syntactic differences: reordered conjuncts, swapped `Eq`
arguments, an expansion of `approvedRegion`, `And` changed to `Or`, and `Lte`
changed to `Lt`. Exact search prints:

```lisp
(anti-unify :size 42 :cr 0.5862 :completion exact
  (Implies
    permit
    (And
      (Implies
        (taggedConfidential obj)
        (And
          (Or
            (Eq (accountOf dst) (accountOf src))
            (Variants (Lit false) sseCmk))
          (Variants sseCmk (Lit true))))
      (Ite
        (Variants
          (Lte (sizeOf obj) multipartThreshold)
          (Lt (sizeOf obj) multipartThreshold))
        directCopy
        multipartCopy)
      (versioningOn src)
      (Variants
        (approvedRegion (regionOf dst))
        (Or (usEast1 (regionOf dst)) (euWest1 (regionOf dst)))))))
```

Two syntactic differences are absent. ACI canonization absorbs the conjunct
reordering, while commutative canonization gives both `Eq` applications the
same argument order. The `Ite` also shows that the common copy branches remain
in the backbone and only its condition is variant. The confidential clause
uses both declared identities: projecting left turns
`Or(Eq, (Lit false))` into `Eq` and keeps the required `sseCmk` conjunct;
projecting right keeps `Or(Eq, sseCmk)` and turns the second conjunct into
`(Lit true)`.

Identity padding also preserves the surrounding ACI structure when a
formalization drops one conjunct or disjunct:

```lisp
(let conjunctionFull
  (And
    (versioningOn (src))
    (approvedRegion (regionOf (dst)))))
(let conjunctionDropped
  (versioningOn (src)))
(antiunify conjunctionFull conjunctionDropped :algorithm exact)

(let disjunctionFull
  (Or
    (usEast1 (regionOf (dst)))
    (euWest1 (regionOf (dst)))))
(let disjunctionDropped
  (usEast1 (regionOf (dst))))
(antiunify disjunctionFull disjunctionDropped :algorithm exact)
```

Exact search aligns the missing terms with the appropriate neutral values:

```lisp
(anti-unify :size 8 :cr 1.0000 :completion exact
  (And
    (versioningOn src)
    (Variants (approvedRegion (regionOf dst)) (Lit true))))

(anti-unify :size 9 :cr 0.8571 :completion exact
  (Or
    (usEast1 (regionOf dst))
    (Variants (euWest1 (regionOf dst)) (Lit false))))
```

The first `Variants` means that one version requires the approved-region
conjunct while the other is trivially true there. The second means that one
version admits the `euWest1` disjunct while the other contributes only false.

Now add the domain equality that defines the approved regions and rerun the
diff:

```lisp
(rewrite
  (approvedRegion r)
  (Or (usEast1 r) (euWest1 r)))
(run 3)
(antiunify formulaA formulaB :algorithm exact)
```

The region difference is absorbed and compression improves from `0.5862` to
`0.4000`:

```lisp
(anti-unify :size 35 :cr 0.4000 :completion exact
  (Implies
    permit
    (And
      (Implies
        (taggedConfidential obj)
        (And
          (Or
            (Eq (accountOf dst) (accountOf src))
            (Variants (Lit false) sseCmk))
          (Variants sseCmk (Lit true))))
      (Ite
        (Variants
          (Lte (sizeOf obj) multipartThreshold)
          (Lt (sizeOf obj) multipartThreshold))
        directCopy
        multipartCopy)
      (versioningOn src)
      (approvedRegion (regionOf dst)))))
```

Exactly two policy divergences remain:

- Encoding B accepts same-account replication **or** SSE-CMK where the policy
  requires both. It therefore admits confidential cross-account replication.
- Encoding B uses a strict threshold, so an object exactly at
  `multipartThreshold` takes the multipart path instead of the direct path.

The same query with `:algorithm uct :playouts 3000` returns the same size-35
term. The full executable input, including result bounds that make the example
self-checking, is
[`egraph/examples/au_policy_divergence.egg`](egraph/examples/au_policy_divergence.egg):

```bash
cargo run --release -p semi-persistent-egraph -- \
  egraph/examples/au_policy_divergence.egg
```

## Workspace

| Crate | Description |
|-------|-------------|
| [`semi-persistent`](semi-persistent/) | Published facade re-exporting the verified containers, e-graph library, and recursion schemes. The `semi-persistent` CLI binary is provided by the e-graph package. |
| [`containers-verus`](containers-verus/) | Production container layer used by the e-graph. Verus verifies the sparse-diff mark/restore protocol and its `Vec`, append-only vector, map, sparse set, list and circular-list arenas, union-find, e-class aggregate, dense span map, B+tree, and sorted cursors. The e-graph aliases this package as `semi-persistent-containers`. ([proof design](containers-verus/doc/design/00-table-of-contents.md)) |
| [`containers`](containers/) | Independent ordinary-Rust implementation of the container layer, retained as the semantic differential oracle and performance reference rather than the engine backend. ([design docs](containers/doc/design/00-table-of-contents.md)) |
| [`containers-conformance`](containers-conformance/) | Non-published differential, property, layout, and Criterion harness comparing the verified and ordinary-Rust container implementations over their documented shared surface. |
| [`egraph`](egraph/) | Equality-saturation engine with native A/AC/ACI canonization, eager and lazy AC completion, dynamically scheduled e-matching, extraction, proof logging, and Exact/MCGS/hybrid anti-unification. ([design docs](egraph/doc/design/00-table-of-contents.md)) |
| [`traversals`](traversals/) | Arena-based, stack-safe recursion schemes with pooled variadics, optional structural deduplication, marks/restores, folds, unfolds, transforms, and zippers. ([tutorial](traversals/TUTORIAL.md)) |
| [`traversals-derive`](traversals/derive/) | Proc-macro companion generating typed arenas, allocators, smart constructors, and traversal plumbing for recursion-scheme families. |
| [`abstract-domains`](abstract-domains/) | Verus-verified bitvector Tnums, Anums, Unums, intervals, and reduced products at `u8`/`u16`/`u32`/`u64`; the executable mirror participates in ordinary workspace tests. The current proof gate reports 994 verified conditions and 0 errors. |
| [`au-verus`](au-verus/) | Machine-checked positional AU objective, recurrence, representation, and lower-bound lemmas. It is an abstract proof model, not yet a refinement proof for the production cyclic AC/ACI solver. |

The live headline-claim inventory, with proved, measured, and argued statements
kept separate, is [`doc/claims.md`](doc/claims.md). It includes retractions and
the proof roadmap for claims not yet established.
[`doc/artifact.md`](doc/artifact.md) gives reproduction commands.
[`doc/paper/draft.md`](doc/paper/draft.md) is the future-paper draft; the
already-published short paper is retained unchanged as a historical artifact.

## Documentation

[**The Semper Book**](doc/book/) is the user-facing guide, extracted from the
design documentation and organized around using anti-unification to diagnose
formalization problems. Build it with `bash doc/book/build.sh` (needs
[mdBook](https://rust-lang.github.io/mdBook/)); every program it shows is a file
in this repository that the test suite executes.

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
