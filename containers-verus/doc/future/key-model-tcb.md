# Eliminating the Hash-Key Model Assumption

## Goal

Remove `obeys_key_model::<K>()` from the trusted basis of verified maps.
Property tests remain useful, but they cannot prove this universal foreign-code
contract.

The trust inventory is maintained in
[the trust-boundary chapter](../design/02-trust-boundary.md).

## 1. Why the Assumption Exists

`SpMap<K, V>` uses `std::HashMap`. vstd models that type only under
`obeys_key_model::<K>()`, an uninterpreted predicate whose intended laws are:

1. executable hashing is deterministic;
2. executable equality identifies exactly one representation identity; and
3. cloning preserves that identity.

The second law is stronger than ordinary `Eq`. An equality class containing two
different representations does not satisfy it.

| Key type | Key-model status |
|---|---|
| `BigInt`, `BigUint` | Assumed; normalized structural representations make the assumption credible but still trusted |
| `OrderedFloat<f64>` | Does not satisfy the identity law: NaN payloads and signed zeros can compare equal |
| `BigRational` | Does not satisfy the identity law: raw non-reduced ratios can compare equal |
| `CanonicalF64` | Canonical bit representation; equality is representation identity |
| `BitsF64` | Raw-bit identity |
| `CanonicalRational` | Reduced numerator/positive-denominator representation |

The canonical wrappers make their own equality classes singleton by
construction. They do not remove vstd's uninterpreted `HashMap` premise; an
axiom is still needed to connect the executable implementations to that
predicate.

## 2. Current Containment

Key-model assumptions are centralized in `external_specs.rs`.
`declare_key_model_assumption!` requires:

- an `axiom_key_model_` name;
- a written justification;
- a value generator; and
- a representation observable used by generated property tests.

CI rejects assumptions outside the designated module or outside that naming
discipline.

Runtime tests cover every falsifiable part:

- repeated and cloned values hash identically;
- alternate construction paths that compare equal have the same observable
  representation;
- clones preserve representation;
- known `OrderedFloat` and raw-rational counterexamples remain excluded; and
- canonical wrappers agree with their documented identity.

This is finite evidence only. It cannot establish the universal key-model law.

## 3. Required Architecture

Eliminating the assumption requires both parts below.

### Canonical Keys at the Boundary

Every verified-map key must have a local canonical encoding:

- exact floats use `BitsF64`;
- compatibility float identity may use `CanonicalF64`;
- rationals use `CanonicalRational`;
- dense ids use their integer newtype representation;
- composite keys use canonical components and structural encoding.

Conversion from a foreign value can be unverified without invalidating the map
theorem: a faulty conversion can choose the wrong canonical key, but it cannot
make two distinct canonical values violate the map's internal equality model.

### A Verified Index Independent of `std::HashMap`

`SpMap` must stop relying on vstd's conditional `HashMap` model. Candidate
backends are:

1. a verified hash table whose executable equality, hashing, and probing refine
   a local canonical-key specification; or
2. a verified ordered index over canonical encodings, such as a map variant of
   the B+ tree.

The ordered option has simpler trust accounting but O(log n) lookup. The hash
option preserves expected O(1) lookup but requires substantially more proof.
Choose using representative Criterion workloads after both designs have
executable prototypes.

## 4. Float Semantics Are Separate

`CanonicalF64` folds all NaNs and folds `-0.0` onto `+0.0` to match the
e-graph's current `OrderedFloat` identity. That compatibility is not a semantic
endorsement.

Using one term identity for signed zero is hazardous when constant folding
distinguishes `1.0 / +0.0` from `1.0 / -0.0`. NaN equality and min/max semantics
also require an explicit theory decision.

The semantic target is:

1. key literals by `BitsF64`;
2. express any desired equivalence as operator-scoped rewrites; and
3. test division, negation, equality, min, max, signed zero, infinities, and NaN
   payloads as one model change.

This change must not be bundled with the map-backend replacement. The backend
can preserve current identity first; float semantics can then change with an
isolated behavioral test surface.

## 5. Composite Key Coverage

The e-graph uses more than literal keys. A complete verified index must support:

| Key shape | Representative use |
|---|---|
| `String` | sort, operator, rule, and axiom registries |
| dense-id newtypes | class, operator, context, OR-state, and term maps |
| literal enum | literal interning |
| `Vec<Id>` | AU structural indexes |
| tuples of ids | AU actions and pair indexes |
| `(TermOp, Vec<TermId>)` | term structural interning |

Canonical container encodings should compose:

- ids from their integer representation;
- tuples from canonical components;
- vectors from length plus canonical elements; and
- strings from exact bytes.

This avoids adding a new ad hoc trust statement for every map instantiation.

## 6. Acceptance Criteria

The key-model trust item is removed only when:

1. verified maps no longer require `obeys_key_model`;
2. all map keys cross through documented canonical encodings;
3. the replacement index proves lookup, insertion, overwrite, and
   semi-persistent restore against its abstract map;
4. literal identity tests cover the float/rational edge cases above;
5. differential and property tests cover all composite key shapes;
6. representative lookup, insertion, and restore workloads have Criterion
   estimates and confidence intervals; and
7. the corresponding axioms and allowlist entries are deleted.

Until then, the centralized assumptions and property tests are an explicit
trust boundary, not verified theorems.
