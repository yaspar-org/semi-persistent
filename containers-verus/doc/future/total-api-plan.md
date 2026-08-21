# Total Public API

## Goal

No safe Rust caller should be able to invoke a public operation whose memory
safety or functional result depends on a Verus `requires` clause. Verus erases
preconditions, so an unverified caller cannot be expected to establish one.

The preferred public shapes are:

- a total operation with unconditional postconditions;
- `Result<_, ContainerError>` for operational refusal;
- an explicit panic/refusal check for programmer-contract violations; or
- a crate-private verified core called by a total public wrapper.

## Enforcement

`containers-verus/tools/check_partial_api.py` scans public executable
functions. CI rejects any new public `requires` occurrence not listed in
`partial-api-allowlist.txt`, and the allowlist may only shrink.

The allowlist is a boundary inventory, not a proof that listed functions are
safe for arbitrary callers. Each entry must belong to one of the classes below.

## Current Boundary Classes

### Runtime-Rechecked Layout Operations

`NodeLayout` operations retain Verus preconditions so verified tree code can
consume precise contracts. Their executable bodies mirror those preconditions
with release-mode refusal checks before any unchecked index operation.

This is memory-safe for unverified callers, but the signatures remain partial
in the verifier. A future cleanup may split the public layout metadata from a
crate-private operations trait, or replace preconditions with conditional
postconditions where that remains useful.

### Inaccessible Store Receivers

`DiffStore` methods carry preconditions, but external safe Rust cannot obtain a
store value because constructors and aggregate access are crate-private. This
is compiler-enforced. Making the trait itself crate-private would simplify the
surface further if no external type-level use requires it.

### Type-Law Assumptions

Some preconditions express laws with no executable decision procedure:

- `obeys_key_model::<K>()`;
- `Tagged` representation laws; and
- erased ghost-parameter contracts.

These are trust-boundary items, not runtime input checks. The key-model
assumption has a separate elimination design in
[key-model-tcb.md](key-model-tcb.md).

### Component-Boundary Preconditions

The direct component APIs still expose obligations that their aggregate
callers prove:

- circular-list splice requires distinct rings;
- sparse-set restore requires an archived well-formed snapshot.

These are the main callable partial operations still to eliminate.

## Remaining Design Work

### Circular Lists

Provide one of:

1. an O(1) executable ring-identity witness checked by a total splice wrapper;
2. a `Result`-returning API that refuses same-ring inputs; or
3. crate-private splice primitives exposed only through `EClasses`, where
   distinctness is already a theorem.

The selected design must not add a ring walk to every splice.

### Sparse-Set Restore

Archive the snapshot permutation/well-formedness fact in the container's own
invariant, then make token validity sufficient for a total `try_restore`.
Alternatively, keep the primitive crate-private and expose restore only through
an aggregate that already archives the fact.

### Layout Surface

Separate metadata needed by external generic code from unsafe-to-misuse node
operations. The target is either:

- public constants and associated types plus crate-private operations; or
- public total operations with explicit refusal and requires-free conditional
  contracts.

Do not weaken the existing release guards around unchecked indexing.

### Keyed Maps

Eliminate `obeys_key_model` assumptions by moving verified maps to an index
whose correctness does not depend on vstd's uninterpreted `HashMap` key model.
Canonical key wrappers are already available; the remaining work is the
verified index and consumer integration.

## Performance Requirements

Total wrappers on hot paths must be measured with Criterion. Report the
estimate, confidence interval, benchmark configuration, and target
architecture. A fixed ratio from one wall-clock run is not acceptance
evidence.

Batch APIs should discharge a bound once when that avoids repeated checks. A
reservation witness is justified only when a real caller cannot batch and
Criterion identifies per-element checking as material.

## Acceptance Criteria

The goal is complete when:

1. the allowlist contains only non-runtime-testable type laws or entries whose
   receivers are compiler-inaccessible;
2. no public safe operation can reach unchecked indexing without a release
   guard;
3. direct circular-list and sparse-set callers need no erased precondition;
4. misuse tests cover every refusal path;
5. Verus verification, Rust tests, and the partial-API CI gate pass; and
6. any hot-path API change has Criterion evidence.

The allowlist and generated API documentation are the current status sources;
this file specifies the target and acceptance conditions only.
