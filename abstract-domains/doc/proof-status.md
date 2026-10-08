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
| `IntervalZ` | `add`, `neg`, `sub`, `mul`, `meet`, `join`, Cousot `widen`, `narrow`, `refine`, `DivRem<Euclid>`, `DivRem<Trunc>` |

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

## IntervalZ

`IntervalZ` is the bottomless unbounded interval from `doc/domain-traits.md`:
`Lo` is `NegInf | Fin(IBig)`, `Hi` is `Fin(IBig) | PosInf`, fields are private,
and `lo <= hi` when both are finite. Emptiness is `BotOr::Bot`. `IBig` is the
trusted `num-bigint` wrapper in the ledger; it is not a verified type.

`widen` is Cousot widening: an unstable bound jumps to infinity. Division is
`DivRem<Euclid>` and `DivRem<Trunc>`. A divisor that contains 0 is split at
zero. The Euclidean quotient of a finite negative by `+∞` is `-1`; the
truncated quotient is `0`. `DivZero` is exact in both directions (`Never`
excludes 0, `Always` is `{0}`). Remainder is the corner hull `x - q * y` when
the quotient is one integer, and otherwise `0 <= r < |y|`, cut by `|r| <= |x|`
where that bound holds (truncation keeps the dividend's sign). `Mul` is the endpoint product, with `0 * ±∞ = 0`.
`narrow` and `refine` return `BotOr`. `meet_chain_sound` states that a
concrete value in the start interval and in every fact survives the chain.
`IBig` is trusted, so its operations are not part of the verified crate.
`cargo test -p semi-persistent-abstract-domains --test interval_z` checks Euclidean `-7/2 = -4`, truncated `-7/2 = -3`, a negative divided by `+∞`, singleton remainders, and `narrow`.
