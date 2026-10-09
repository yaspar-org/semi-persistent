# Abstract Domains Proof Status

Last refreshed: 2026-10-01.

## Current result

`cargo verus verify` reports 0 errors; CI runs it on every pull request. This
file does not record the number of verified items, because every change to the
crate moves it.

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
| L4 | `ExecTnum`, `ExecAnum`, `ExecUnum`, `Interval` at four enabled widths | every method verifies its stated contract; containment scope is listed below |

All enabled L4 results are proved well formed where their contracts say so.
The current **universal containment** contracts are:

| Type | Operations with universal containment contracts |
| --- | --- |
| `ExecTnum` | `bw_or`, `bw_and`, `bw_xor`, `add`, `join`, `meet` |
| `ExecAnum` | `add`, `div_const` |
| `ExecUnum` | `top`, `add`, `from_interval`, `mul` |
| `Interval` | `add`, `meet`, `join`, `div_const` |

The `ExecUnum` proofs use native/spec bridge lemmas, the L3 `ChoppedUnum`
soundness theorems, explicit overflow-to-top cases, and interval-to-Unum range
lemmas. #123 removed `ReducedProduct`, whose `reduce` and `add` carried
containment theorems; `reduce::Product` replaces it.

Other executable methods currently prove well-formedness only. In particular,
this includes Tnum multiplication, shifts, negation and subtraction, most
and Unum conversions/arithmetic helpers.
Their implementations and finite mirror tests are evidence, but not universal
containment theorems. Adding those postconditions and proofs is the remaining
L4 soundness work.

## Sign over mathematical integers

`Sign` is the seven nonempty sign sets over `int`; `BotOr<Sign>` supplies the
eighth, empty state. Its representation is canonical, and `leq`, `join`, and
`meet` are exact with respect to `gamma`. `Arith<Euclid>` and `Arith<Trunc>`
prove universal containment for negation, addition, and subtraction; `Mul` is
also proved for both integer semantics. The Sign domain exports bounds through
`FactsZ` and its `Refine` implementation proves that it preserves every jointly
represented value and never grows the Sign component.

`DivRem<Euclid>` and `DivRem<Trunc>` have exact zero classification and
universally proved containment contracts. Truncated division and remainder use
the dividend-sign rule; Euclidean remainder is `Zero` for a zero dividend and
`NonNeg` otherwise; Euclidean division handles both positive and negative
divisors. These transfers return the tight result expressible in the seven-state
Sign abstraction. The Sign runtime suite checks all 7-by-7 abstract category
pairs against concrete values from `[-12, 12]`, including exact quotient and
remainder sign categories, lattice exactness, flags, and FactsZ refinement
no-growth.
