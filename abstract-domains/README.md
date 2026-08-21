# abstract-domains: Proved Abstract Domain Library

A formally verified implementation of bitvector abstract domains,
written in [Verus](https://github.com/verus-lang/verus) (verified Rust).

## What this is

This crate provides **tristate numbers (Tnums)**, **additive tristate numbers (Anums)**,
**intervals**, **Unums (horizontally composable additive tristate numbers)**, and their
**reduced product TAIU** -- abstract domains for reasoning about bitvector arithmetic
with bitwise uncertainty.

The ordinary verification run reports **994 verified conditions and 0
errors**. A CI source gate rejects executable `admit()` and `assume()` calls in
this crate. The pinned `vstd` dependency contains admitted specifications and
is part of the trust boundary; a global `--no-cheating` run therefore fails in
`vstd` before project verification. A separate 32-test Rust mirror suite
provides randomized and exhaustive finite evidence; it mirrors the Verus
definitions rather than constituting a second formal verification.

## Architecture

```
Layer 4: exec_tnum.rs / domains.rs  -- Executable u8/u16/u32/u64 implementations
Layer 3: chopped.rs                 -- Bounded-width simulation
Layer 2: tnum.rs / anum.rs / unum.rs / div.rs -- Unbounded theory with soundness proofs
Layer 1: nats.rs / bools.rs         -- Natural numbers as infinite bitstrings
         tbit.rs                    -- Single-bit abstract domain (Tb)
```

### Layer 1: Infinite bitstrings (bools.rs, nats.rs)

Natural numbers are modeled as infinite boolean strings via `hd` (mod 2) and `tl` (div 2).
All bitwise operations (AND, OR, XOR, AND-NOT) are defined as pointwise `mapd` over bits.
Addition is defined recursively via a full adder with carry.

### Layer 2: Abstract domains (tbit.rs, tnum.rs, anum.rs, unum.rs, div.rs)

**Tnum** `Tn{v, m}`: each bit is independently 0, 1, or unknown (X).
- Membership: `has(n) <==> (n & ~m) == v`
- Precise for: bitwise ops, shifts
- Imprecise for: arithmetic (carry propagation destroys information)

**Anum** `An{v, m}`: a known base value plus bitwise uncertainty.
- Represents: `{v + d | d & ~m == 0}` (v plus any subset of m bits)
- Addition keeps the base sum exact while soundly widening offset uncertainty

**Unum** `Un{base, walls, extent}`: a known base plus independently bounded
bit fields.
- Single-field case: `{base + d | 0 <= d <= extent}`
- Multi-field case: each field offset ranges over `[0, field_extent]`
- Addition is proved sound; exactness for all accepted encodings is neither
  claimed nor true
- Key formula: `cout = (x1 & x2) | ((x1 | x2) & ~(x1 + x2))`

**Division**: long division by iterated subtraction, dual of multiplication.
Both constant-divisor and general Tnum/Tnum division are proved sound.

### Layer 3: Bounded simulation (`chopped.rs`)

`ChoppedTnum`, `ChoppedAnum`, and `ChoppedUnum` pair an unbounded domain with
a bit width. Explicit bounded containment theorems cover ChoppedTnum
add/mul/shifts/join/meet, ChoppedAnum add/division by constant, and
ChoppedUnum add/mul, subject to their stated fit and no-overflow preconditions.
The ChoppedTnum bitwise helpers currently expose invariant/width preservation,
while its `div` and `neg` spec functions have no Layer-3 containment theorem.

### Layer 4: Executable domains (exec_tnum.rs, domains.rs)

Native Rust implementations on u8/u16/u32/u64 (`u128` is disabled because its
bitvector obligations exceed current solver capacity):

- **ETn**: Executable Tnum. Well-formedness (`v & m == 0`) proved via `by(bit_vector)`.
- **EAn**: Executable Anum. Exact base arithmetic.
- **EUn**: Executable Unum. Proved-sound addition via the carry-out formula,
  widening to top when represented bounds or result ranges wrap.
- **Interval**: `[lo, hi]` bounds tracking.
- **ReducedProduct (TAIU)**: Tnum x Anum x Interval x Unum.

The **reduced product** propagates information across domains:
- Interval bounds clear impossible high bits in Tnum and Anum
- Tnum/Anum/Unum min/max tighten the interval
- Unum is rebuilt from tightened interval after bitwise ops
- Unum is threaded directly through arithmetic operations. It retains the
  proved unbounded field formula when fixed-width bounds do not wrap and
  widens to top otherwise.

Every executable method verifies its stated contract. Universal containment
theorems currently cover `ExecTnum` bitwise/add/join/meet,
`ExecAnum` add/division by constant, `ExecUnum` top/add/from-interval/multiply,
`Interval` add/meet/join/division by constant, and `ReducedProduct`
reduce/add. Other Layer 4 methods currently prove well-formedness only; see
[the proof-status inventory](doc/proof-status.md).

## Key theorems

| Theorem | File | What it says |
|---------|------|-------------|
| `Tnum::add_bitwise_eq` | tnum.rs | Non-recursive addition formula = recursive |
| `TBit::add_carry_decomp` | tbit.rs | The carry compensation property |
| `tn_ext` | tnum.rs | Two inv Tnums with same membership are equal |
| `Tnum::div_sound` | div.rs | General Tnum/Tnum division is sound |
| `Anum::div_const_sound` | anum.rs | Anum division by constant with exact base quotient |
| `Unum::add_sound` | unum.rs | Multi-field unbounded Unum addition is sound |
| `Unum::mul_sound` | unum.rs | Unbounded Unum multiplication is sound |
| `carry_out_c_overflow` | unum.rs | Carry-out bit = low-bits overflow |
| `Unum::add_bounded_sound` | unum.rs | Chopped addition is sound under its no-overflow preconditions |
| `Unum::to_anum_sound` | unum.rs | Single-field (`walls == 0`) Unum-to-Anum conversion is sound |

## Prerequisites

- [Verus](https://github.com/verus-lang/verus) for formal verification
- [cargo-verus](https://github.com/verus-lang/verus) (`cargo install cargo-verus`)
- Rust toolchain (see `rust-toolchain.toml`)

## Running

```bash
# Verify all project obligations
cargo verus verify

# Verify only the Unum module
cargo verus verify -- --verify-only-module unum

# Per-module timing breakdown
cargo verus verify -- --time-expanded

# Run the 32-test Rust mirror suite
cargo test --test fuzz --release

# Run demo
cargo run --features bin
```

## Verification status

- 994 Verus conditions, 0 errors
- no project-local `admit()`/`assume()` calls (CI source gate)
- pinned `vstd` admitted specifications remain in the trust boundary
- 32 Rust mirror tests, all passing
- 4 enabled bit-widths: u8, u16, u32, u64

## Design documents

- [Unum design](doc/unum-design.md): representation, proved containment
  scope, precision counterexample, conversions, and reduced-product use.
- [Abstract domains design](doc/design.md): overall architecture and proof methodology.
- [Interval soundness](doc/interval-soundness.md): the contracts implemented
  by the current unsigned interval component.
- [Interval extensions](doc/future/interval-extensions.md): interval division
  with alarms, abstract comparisons and narrowing, wrapped intervals, and
  strided intervals.
