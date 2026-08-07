# Shrinking the key-model TCB after the migration

*Status: future work, still open after the consumer swap. Owner: whoever
migrates `LitValStore`.
Context: trust ledger group D
([02-trust-boundary.md](../design/02-trust-boundary.md) §3.5); the
Phase 9 review that withdrew the BigRational/OrderedFloat axioms as false.*

## The problem, precisely

`SpMap<K, V>` sits on `std::HashMap`, whose vstd model is conditioned on
`obeys_key_model::<K>()` — an **`uninterp` spec fn with no introduction
rule other than axioms**. Its prose meaning (vstd `std_specs/hash.rs`):

1. `Hash` is deterministic;
2. two keys are **identical iff** the executable `==` considers them equal;
3. `clone()` produces a result identical to its input.

Requirement (2) is the sharp one: `==` equivalence classes must be
singletons up to value identity. Determinism is NOT sufficient. This is
why two of the migration's original literal-type axioms were withdrawn
(and replaced by canonical wrappers whose axioms hold by construction):

| type | verdict | reason |
|---|---|---|
| `BigInt` / `BigUint` | axiom kept (credible) | exec `eq` is structural (sign + digit vector) over the crate's normalization invariant |
| `OrderedFloat<f64>` | **axiom withdrawn — false** | all NaN payloads (and ±0.0) share one `==` class across distinct bit patterns |
| `BigRational` | **axiom withdrawn — false** | `Ratio::new_raw` makes non-reduced values reachable; `eq` is mathematical (`2/4 == 1/2` across distinct representations) |
| `CanonicalF64` (crate-local) | axiom holds by construction | only constructor canonicalizes (one NaN encoding, +0.0); `==` is derived bit identity |
| `CanonicalRational` (crate-local) | axiom holds by construction | reduced positive-denominator pair via `Ratio::new` only; derived structural eq over normalized `BigInt`s |

The violations are pinned by regression tests
(`tests/compat_map.rs::key_model_violations`): if a crate upgrade changes
the semantics, those tests fail and the exclusion gets re-reviewed.

Beyond group D, the default crate's assumed-fact inventory is four
one-line contracts: `ContainerId::eq`'s equality reflection, the two
shrink helpers' data preservation, and `clone_key_exact`'s clone identity.
This document is about driving the *key-model* part to zero and keeping
the rest honest.

## Why we cannot just verify the contracts

- `obeys_key_model` is `uninterp`: nothing can *prove* it, by
  construction. vstd's own axioms for `u8`…`i128` are `admit()`-backed,
  and even `StringHashMap` *assumes* it for `String`. vstd's doc comment
  says a proof path is planned but does not exist.
- The requirements are about the executable bodies of foreign `Hash`/
  `Eq`/`Clone` impls. Foreign crates are never compiled under Verus, so
  the verifier has no model of that code. Any interaction bottoms out in
  at least one trusted statement about foreign exec behavior.
- Defining the key type locally does not escape either: derived `Hash`
  goes through std's `Hasher` machinery, which vstd models with its own
  assumed specs (`builds_valid_hashers` is also `uninterp`).

## The endgame: eliminate the assumption (Option A)

Make the verified property independent of foreign code:

1. **Canonical key types at the boundary.** Crate-local types whose
   `Eq`/`Hash` we write and verify ourselves, with conversion at the
   client boundary:
   - floats → `CanonicalF64(u64)`: the NaN-canonicalized, ±0.0-normalized
     bit pattern (what `OrderedFloat::hash` already computes — we make it
     the *identity*, not just the hash);
   - rationals → `CanonicalRational { numer: BigInt, denom: BigInt }`,
     reduced, denom > 0 as a CONSTRUCTOR invariant (not a type invariant —
     both fields are `BigInt`; `Ratio::new` normalizes the sign onto the
     numerator) — compare/hash structurally;
   - big integers → keep keying by `BigInt` short-term (credible axiom),
     or a limb-vector newtype long-term.

   The foreign→canonical conversion is unverified, but it exits the TCB:
   a buggy conversion mis-keys that client's value (garbage-in,
   garbage-out at their boundary) — it can no longer make the *container's*
   theorems false. That soundness/correctness separation is the point.

2. **A verified index for `SpMap`.** Even with canonical keys,
   `std::HashMap` still demands `obeys_key_model::<CanonicalKey>()` —
   vstd's whole HashMap model is conditioned on it. Two exits:
   - hand-verified hash table over canonical keys (the crate's fully
     verified `BPlusTreeSet` shows the proof machinery is in-house); or
   - a verified ordered index over the canonical encoding (the B+tree
     itself, if the interning workload tolerates O(log n) — measure
     against the rebuild-vs-incremental data before assuming it doesn't).

   With both steps, `obeys_key_model` axioms, `clone_key_exact`, and
   `values_equal` all become deletable: the trusted surface drops to
   ContainerId + capacity introspection + the panic primitive.

Cost: a verified-map project plus per-intern conversion. Decide once a
`LitValStore` migration measures real literal-interning traffic; the consumer
swap did not include it.

## Until then: fuzz the contracts (Option B — done)

Every assumed contract gets a **property-based test of the assumed fact
itself** — not an end-to-end oracle. The distinction matters: an
SpMap-vs-HashMap oracle uses the same `Eq`/`Hash` on both sides, so it
can never detect an identity/`==` mismatch. What CAN be falsified at
runtime, per contract:

| assumed contract | falsifiable observable | test (exists today?) |
|---|---|---|
| `obeys_key_model` req (1): hash determinism | same value hashes equal across calls/clones | ✅ `literal_keys::bigint_key_model_hash_determinism` |
| req (2): `==` ⟹ identity | values built via different construction paths that compare `==` must agree on every representation observable (byte encoding, sign, Debug, hash) | ✅ `literal_keys::bigint_key_model_eq_is_identity` (arithmetic detours, shift round-trips, decimal round-trips) |
| req (3): clone identity | clone agrees on every representation observable | ✅ `literal_keys::bigint_key_model_clone_identity` |
| withdrawn-type violations stay real | the known violating pairs still compare `==` | ✅ `key_model_violations::*` |
| `clone_key_exact` ensures | same as req (3), for every K a consumer uses | ✅ per-type via the generated tests + `canonical_key_model` proptest |
| `shrink_vec_capacity` / `shrink_aov_capacity` ensures | element sequence unchanged across a shrink at random lengths/capacities/policies | ✅ `shrink_preserves_vec_contents` / `shrink_preserves_aov_contents` |
| `ContainerId::eq` reflection + `new` distinctness | already fuzzed | ✅ `external_body_contract_fuzz.rs` |

Status update (all landed with the verified crate, ahead of schedule):

1. ✅ **Canonical key wrappers** (`src/canonical_keys.rs`): `CanonicalF64`
   (canonical-NaN/zero-normalized bits; `==` is bit identity with no
   foreign-code dependence) and `CanonicalRational` (reduced,
   positive-denominator `BigInt` pair) — the Option A step 1 boundary
   types. Proptest requirement fuzz + SpMap oracle in
   `tests/compat_map.rs::canonical_key_model`; axioms in
   `external_specs.rs` with per-type credibility arguments.
2. ✅ **Requirement-level fuzz for the foreign axioms**
   (`literal_keys::*_key_model_*`) and proptest coverage for the
   canonical types.
3. ✅ **Shrink-helper contract fuzz**
   (`shrink_preserves_vec_contents` / `shrink_preserves_aov_contents`):
   the last contract-carrying `ensures` without a runtime test.
4. ✅ **`declare_key_model_assumption!` macro** (`external_specs.rs`):
   compile-time-checked `axiom_key_model_` prefix, mandatory
   justification, generated requirement fuzz (determinism, clone
   identity, `==`-iff-representation-identity over caller-supplied
   generator + observable). Demonstrated end-to-end in
   `tests/key_model_macro.rs`. CI grep convention: every
   `axiom_key_model_*` in the workspace must come from this macro.

5. ✅ **CI enforcement** (`.github/workflows/verus.yml`): the
   literal-types verify sweep, the compat-all+literal-types test matrix,
   and the axiom-discipline gate — any `obeys_key_model` axiom outside
   the audited `external_specs.rs` without the `axiom_key_model_` prefix
   fails CI.

Remaining work item (NOT done by the consumer swap):

1. **Consumer conversion**: `NiraLitVal::Rat` interning keys by
   `CanonicalRational` (convert at the LitValStore boundary), model f64
   literals by `CanonicalF64`.

## Honest limits of Option B

- Fuzzing samples; it cannot establish req (2) universally (it
  quantifies over all values), and a hasher-state-dependent violation
  could hide from any fixed test. Option B is a tripwire, not a proof.
- For *unverified* cargo callers, `requires` erases; nothing forces
  anything. At best `SpMap::new` could run a sampled smoke check in
  debug builds.
- The endgame that actually removes the assumption is Option A. Option B
  keeps us honest until the traffic data says whether Option A's verified
  index is worth building.


## Float term identity: the fold is parity, not the endgame (review 2026-07-26)

Requirement (2) and hash-consing are two different questions that
canonicalization answers at once — which is why `CanonicalF64`'s fold is
seductive and why it must not be mistaken for a semantic decision. For the
key model alone, **bit-exact keying is strictly easier to justify**:
`BitsF64(u64)` (now in `canonical_keys.rs`) is injective by construction,
no fold, no dependence on float semantics. The fold in `CanonicalF64`
exists for exactly one reason: it reproduces production's `OrderedFloat`
intern behavior, pinned pair-for-pair by
`float_key_semantics::canonical_f64_matches_ordered_float`.

**The fold inherits a live model-layer hazard** (pre-existing in
production, NOT introduced by the migration): with ±0.0 interned as one
term, congruence + constant folding over `model.rs`'s `f64::/` merges
`+inf ≡ -inf` (`1.0/0.0` vs `1.0/-0.0` from two representatives of the
same class), and `f64::neg(0.0) ≡ 0.0`. Adjacent issues in the same
operator table: `f64::==` on two NaNs folds to `true` (IEEE: false), and
`f64::min`/`max` follow the total order rather than IEEE minNum/maxNum.

Sequencing (deliberate, so behavioral diffs have one candidate cause):

1. **Container switch (done): keep the fold.** Key by `CanonicalF64`;
   behavior identical to production; the fold is pinned by
   `canonical_f64_fold_is_pinned` so it cannot drift silently.
2. **Separate change (model semantics): switch to `BitsF64`** and express
   any identification actually wanted (e.g. `-0.0 → 0.0` where the theory
   says so) as rewrite rules scoped to specific operators — visible,
   reviewable, per-operator. Fix `f64::==`/`min`/`max` IEEE semantics in
   the same change, with its own tests.

## Axiom inventory for the consumer conversion: nine key types, not one (review 2026-07-26)

Group D as landed covers the literal types only. Counting `Map<K, V>`
instantiations across the e-graph, the consumer switch needs
`obeys_key_model` for roughly nine distinct key shapes (vstd axiomatizes
only primitives and `Box`es):

| key type | site | credibility |
|---|---|---|
| `String` | registry sorts/ops/rules/axioms (4 maps) | byte-exact eq — solid; any Unicode normalization is a parse-time decision, never in the key |
| `Cfg::O`, `A::Class`, `A::Or`, `A::Context`, `A::Term` | unit_node, inverse_op, AU maps | `define_id*!` newtypes over u32/u64 — solid |
| the literal enum | LitValStore | only as good as its payloads (hence the canonical wrappers) |
| `Vec<A::Class>` | au/space.rs index | structural over a solid element |
| `(A::Class, A::Class)`, 4-tuples | au/actions.rs, au/space.rs | structural over solid components |
| `(TermOp<O,V>, Vec<A::Term>)` | au/terms.rs by_structure | structural over a consumer enum |

Consequence 1 — **the literal enum is the key**, so canonicalization lives
in the variant payloads (`Rat(CanonicalRational)`, `F64(CanonicalF64)` then
`F64(BitsF64)`), not at the LitValStore boundary as earlier drafts said.

Consequence 2 — **`define_id7/15/31/63!` should generate the axiom for the
id type it defines.** The argument is airtight (newtype over a primitive,
derived structural Eq/Hash, and the macro's impls are already verified);
generating it makes five of the nine rows uniform and free instead of
hand-written.

Consequence 3 — **composite keys want compositional axioms**, mirroring
vstd's own `Box<K>` form (`obeys_key_model::<K>() ==>
obeys_key_model::<Box<K>>()`): one conditional axiom for `Vec<K>`, one per
tuple arity over its components, one for `String`. A handful of trusted
statements instead of an axiom count that grows with every new map — the
difference between a bounded TCB and one that scales with the consumer.
These land in `external_specs.rs` when the consumer conversion happens, budgeted, not
discovered mid-switch.
