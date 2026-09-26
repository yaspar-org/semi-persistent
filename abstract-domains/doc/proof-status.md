# Abstract Domains Proof Status

Last refreshed: 2026-09-23.

## Current result

```text
cargo verus verify
1016 verified, 0 errors
```

The project source contains no executable `admit()` or `assume()` calls. CI
enforces that policy with a source scan and runs ordinary Verus verification.
The pinned `vstd` dependency contains admitted specifications; global
`--no-cheating` fails while compiling `vstd` before reaching this crate. Those
dependency specifications, Verus, and the solver remain part of the trust
boundary.

Enabled executable widths:

- `d8` (`u8`)
- `d16` (`u16`)
- `d32` (`u32`)
- `d64` (`u64`)

The `d128` macro invocation remains disabled because its bitvector obligations
exceed the current solver capacity. Do not describe `u128` as an enabled or
verified executable instance of the existing d* domains. The separate
Wrapped<u128>/Wrapped<i128> membership implementations described below do verify.

The separate Rust mirror suite contains 32 tests:

```text
cargo test -p semi-persistent-abstract-domains --test fuzz
```

Those tests mirror the Verus definitions and provide randomized/exhaustive
finite evidence. They are not an independent proof that a separate executable
implementation corresponds to the verified definitions.

## Layer status

| Layer | Contents | Status |
| --- | --- | --- |
| L1 | bit primitives and infinite-bitstring natural operations | proved |
| L2 | Tnum, Anum, Unum, and division theory | proved |
| L3 | chopped bounded-width domains | every stated contract verifies; containment covers the explicit operation inventory in `design.md`, not every defined operation |
| L4 | `ExecTnum`, `ExecAnum`, `ExecUnum`, `Interval`, `ReducedProduct` at four enabled widths | every method verifies its stated contract; containment scope is listed below |

All enabled L4 results are proved well formed where their contracts say so.
The current **universal containment** contracts are:

| Type | Operations with universal containment contracts |
| --- | --- |
| `ExecTnum` | `bw_or`, `bw_and`, `bw_xor`, `add`, `join`, `meet` |
| `ExecAnum` | `add`, `div_const` |
| `ExecUnum` | `top`, `add`, `from_interval`, `mul` |
| `Interval` | `add`, `meet`, `join`, `div_const` |
| `ReducedProduct` | `reduce`, `add` |

The `ExecUnum` proofs use native/spec bridge lemmas, the L3 `ChoppedUnum`
soundness theorems, explicit overflow-to-top cases, and interval-to-Unum range
lemmas. `ReducedProduct::add` composes the four component containment
postconditions and then applies the proved containment of `reduce`.

Other executable methods currently prove well-formedness only. In particular,
this includes Tnum multiplication, shifts, negation and subtraction, most
Unum conversions/arithmetic helpers, and ReducedProduct bitwise operations,
subtraction, multiplication, division, shifts, joins, meets, and negation.
Their implementations and finite mirror tests are evidence, but not universal
containment theorems. Adding those postconditions and proofs is the remaining
L4 soundness work.


## Wrapped membership and normalization

`AbstractValue<D>` provides Bot/NonBot; `Wrapped<T>` has only nonempty Top/Arc.
For u8/u16/u32/u64/u128 and i8/i16/i32/i64/i128, contains verifies
`result == self.has(x)` and normalize verifies universal exact membership
preservation. Explicit Clone implementations for Wrapped<T> (T: Copy) and
AbstractValue<D> (D: Copy) verify equality with the original.

The production harness has 13 test functions: exhaustive u8/i8 membership and
normalization, boundary/wrapper/Clone suites for ten types, and a u32 adapter.
Together with 13 oracle self-tests and 32 existing tests, 58 tests pass; one
doctest is ignored. Tests were regrouped; former counts are not comparable
one-for-one. Canonicality and idempotence are tested, not separate formal contracts.
Raw Arc construction can be noncanonical until normalize is called. Test-only
wrapper lifting does not establish a generic production lifted API or product
consistency. Join/meet, arithmetic and conversions remain future work.
