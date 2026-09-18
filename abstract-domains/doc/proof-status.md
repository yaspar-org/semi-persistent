# Abstract Domains Proof Status

Last refreshed: 2026-09-17.

## Current result

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
Bound     = NegInf | Fin(i64) | PosInf
IntervalZ = { empty, lo, hi }
values    = every int z with lo <= z <= hi
```

Finite endpoints are `i64` (an executable stand-in for IBig). Membership and
every containment contract are over mathematical `int`, so nothing wraps.
Endpoint overflow widens to ±∞, or to `top` if a lower bound would otherwise
become `PosInf` (which would look empty). Stopping at `top` is always sound.
That widening is not monotone; `meet` is monotone and is the operation the
e-graph iterates.

Proved:

- explicit bottom; disjoint meet is bottom
- lattice laws of §3.5 for meet/join (idempotent, commutative, associative,
  units, zeros), plus `meet` monotone
- containment of `add`, `neg`, `sub`, `mul`, `meet`, `join`
- `div` value containment for every nonzero concrete divisor, and alarm
  membership for the zero cases (`NoError` ⟂ `DefiniteError`, join is
  `MaybeError`)
- `widen` extensive and over-approximates join; `narrow` refines
- refinement budget: budget 0 keeps the current value (sound); positive
  budget takes the meet
- guards `within` and `nonzero` refuse to license bottom

`cargo verus verify -- --verify-only-module interval_z` reports 86 verified,
0 errors. No project-local `admit()`/`assume()`.
