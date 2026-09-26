# Abstract Domains Proof Status

Last refreshed: 2026-09-24.

## Current result

```text
cargo verus verify
1030 verified, 0 errors
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
verified executable instance.

The separate Rust mirror suite contains 47 tests:

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
| L4 | `StridedInterval` at four enabled widths | representation, normalization, and join (Weeks 4-5 of Task 1); not yet in `ReducedProduct` |

All enabled L4 results are proved well formed where their contracts say so.
The current **universal containment** contracts are:

| Type | Operations with universal containment contracts |
| --- | --- |
| `ExecTnum` | `bw_or`, `bw_and`, `bw_xor`, `add`, `join`, `meet` |
| `ExecAnum` | `add`, `div_const` |
| `ExecUnum` | `top`, `add`, `from_interval`, `mul` |
| `Interval` | `add`, `meet`, `join`, `div_const` |
| `ReducedProduct` | `reduce`, `add` |
| `StridedInterval` | `join` (sound, not exact in the mismatched-stride case -- see below) |

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

`StridedInterval`: `wf`, `bottom`/`top`/`singleton` produce wf values with
the concretization the project-wide semantics require (`top_has`,
`singleton_exact`), and `normalize` preserves concretization exactly
(`self.has(x) == r.has(x)`, not just "no values lost"). `join` has a
universal containment contract (`self.has(x) ==> r.has(x)` and
`t.has(x) ==> r.has(x)`), but it is intentionally not tight: it is exact
when both operands share a nonzero stride and residue class, or are two
distinct singletons, and otherwise falls back to `top()` rather than
guessing. Tightening the mismatched-stride case needs gcd, which is
Yuting's shared helper and hasn't landed yet -- SI-W5-01's acceptance
criterion is soundness ("join contains both operands"), not precision, so
this is not a gap to close before the general meet/CRT work in Week 6-7.
Meet, arithmetic transfers, and `ReducedProduct` integration are still
open (Weeks 6-7 per the Task 1 plan).
