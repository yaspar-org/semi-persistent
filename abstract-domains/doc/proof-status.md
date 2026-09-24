# Abstract Domains Proof Status

Last refreshed: 2026-09-23.

## Current result

The historical crate-wide figure below is the L1–L4 machine domains and does
**not** include IntervalZ. IntervalZ is reported separately in its section.

```text
cargo verus verify
994 verified, 0 errors
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
| `IntervalZ` | `add`, `neg`, `sub`, `mul`, `meet`, `join`, `div` (value + alarm), `widen`, `narrow`, `refine` |
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

## IntervalZ (Task 1 §3.2)

`abstract-domains/src/interval_z.rs` is the unbounded-integer interval domain
from the practicum:

```text
Bound     = NegInf | Fin(IBig) | PosInf
IntervalZ = { empty, lo, hi }
values    = every int z with lo <= z <= hi
```

Finite endpoints are `IBig` (`num_bigint::BigInt`, spec view `int`). Nothing
wraps: addition, subtraction and multiplication are exact on endpoints,
including past `i64`. A product is the min/max of the four extended endpoint
products. Division splits a divisor that contains 0 at zero, takes the four
Euclidean endpoint quotients on each side, and joins; `IBig::div_euclid` is
specified as Verus `int` `/`. UBig is `wf_ubig` (`lo >= 0`) on the same type.
RBig is `IntervalR`, the same bounds with open/closed endpoints.

`widen` jumps an unstable endpoint to `±∞`. It is not monotone. A meet chain
either stabilises (fuel unchanged) or spends one unit of fuel per strict
meet; fuel 0 keeps the current value.

Contracts stated, with no project-local `admit()`/`assume()`:

- explicit bottom; disjoint meet is bottom
- lattice laws of §3.5 for meet/join, plus monotonicity of `meet`, `join`,
  `add`, `neg`, `sub`, `mul` and `div`
- containment of `add`, `neg`, `sub`, `mul`, `meet`, `join`
- `div` value containment for every nonzero concrete divisor, and alarm
  membership (`NoError` ⟂ `DefiniteError`, join is `MaybeError`)
- `narrow` refines its first argument and stays above the meet
- `meet_chain` refines the start and is unchanged at fuel 0
- `within`, `nonzero`, `nonneg` and `fits_u8` refuse to license bottom

```text
cargo verus verify -p semi-persistent-abstract-domains -- --verify-only-module ibig --verify-only-module interval_z --rlimit 50
168 verified, 0 errors
```

`cargo test -p semi-persistent-abstract-domains --test interval_z` (22 tests)
covers the executable transfers, the `[-8,-1]/[-4,-2]` quotients, fuel
exhaustion, UBig and open endpoints.
