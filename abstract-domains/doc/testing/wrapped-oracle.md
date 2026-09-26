# Wrapped Interval oracle and integration tests

## Current interface

The partner refactor at 6d9f949 introduces `AbstractValue<D> { Bot, NonBot(D) }`.
`Wrapped<T>` now has only Top and Arc; its values are nonempty. The independent
reference keeps Empty/Full/Arc. Harness adapters map Empty to AbstractValue::Bot
and Full/Arc to AbstractValue::NonBot(Wrapped::Top/Arc).

The harness matches Bot to false for membership and leaves Bot unchanged under
normalization. For NonBot it invokes the actual production contains/normalize.
These lifting helpers are test code, not a claimed production generic lifted API.
The explicit Clone implementations for Copy endpoints/payloads preserve equality.

## Run

```sh
cargo test -p semi-persistent-abstract-domains
cargo verus verify --manifest-path abstract-domains/Cargo.toml
```

Alternatively run `cargo verus verify` from abstract-domains.

## Coverage

- 13 independent oracle self-tests: widths 1–4 exhaustive representations and
  62,140 canonical pairs; split-intersection rejection; selected 8-bit arithmetic
  reference; sparse u32 reference checks. These are not production arithmetic tests.
- 13 production test functions: two exhaustive u8/i8 suites jointly testing
  original/normalized membership, exact canonical output and idempotence; ten
  type-specific boundary suites checking wrappers, normalization and Clone;
  one u32 integration test using the prepared callback checker.
- Production u8/i8 checks enumerate all endpoint pairs plus Bot/Top and all 256
  bit patterns. Wider tests sample extrema, sign boundaries, endpoints and neighbors.
- Full-circle arcs normalize to Top; equal endpoints remain singletons. Bot is
  distinct from NonBot(Top). Raw Arc construction still permits noncanonical
  full circles until normalize is called.

Regrouping previous tests into type-specific shared harnesses changes test counts
without dropping membership, normalization or Clone coverage. Current full run:
58 passed (32 existing + 13 oracle + 13 production), one ignored doctest.
Verus: 1016 verified, 0 errors. The new wrapper Clone contract is included.

## Limits

Canonical output and idempotence are runtime-tested; normalize's universal
contract proves exact membership preservation. contains proves correspondence to
has. Wide-width sampling is not exhaustive. No production generic map/and_then,
lifted join, meet, arithmetic, conversions or reduced product is implemented here.
A shared Bot variant alone does not detect contradictions between nonempty product
components. No new proof escapes or dependencies are added.

Small-width reference results cannot be treated as u32 results: Arc(0,15) is Full
for four bits but not u32. Future operation tests must match actual width semantics.
Do not discard either component of a split intersection. Algebraic properties
must be assessed individually because Wrapped is not a standard lattice.
