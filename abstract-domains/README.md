# abstract-domains: Proved Abstract Domain Library

A formally verified implementation of bitvector abstract domains,
written in [Verus](https://github.com/verus-lang/verus) (verified Rust).

## What this is

This crate provides **tristate numbers (Tnums)**, **additive tristate numbers (Anums)**,
**intervals**, **Unums (horizontally composable additive tristate numbers)**, and their
**reduced product TAIU** -- abstract domains for reasoning about bitvector arithmetic
with bitwise uncertainty.

Every operation is verified in two ways:
1. **Formal proofs** (Verus): 754 verified lemmas, 0 admits, proving soundness of the
   abstract domain theory on unbounded natural numbers.
2. **Fuzz tests**: 29 randomized tests, 1M iterations each, checking that the executable
   u64 implementations match the expected concrete semantics.

## Architecture

```
Layer 4: exec_tnum.rs / domains.rs  -- Executable u8/u16/u32/u64/u128 implementations
Layer 3: reg.rs                     -- Bounded register simulation (TnR)
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
- Precise for: addition (base adds exactly, no carry blowup)

**Unum** `Un{v, x}`: a known base value plus a contiguous range.
- Represents: `{v + d | 0 <= d <= x}` (single-field case)
- Multi-field: partitions bits into fields, each a contiguous range [0, max]
- Precise for: addition (fields merge correctly via carry-out detection)
- Key formula: `cout = (x1 & x2) | ((x1 | x2) & ~(x1 + x2))`

**Division**: long division by iterated subtraction, dual of multiplication.
Both constant-divisor and general Tnum/Tnum division are proved sound.

### Layer 3: Bounded simulation (reg.rs)

`TnR{tn, w}` wraps a Tnum with a bit-width. Proves that all operations on
w-bit values produce w-bit results, and that bounded operations simulate
unbounded operations via `chop(_, w)`.

### Layer 4: Executable domains (exec_tnum.rs, domains.rs)

Native Rust implementations on u8/u16/u32/u64/u128:

- **ETn**: Executable Tnum. Well-formedness (`v & m == 0`) proved via `by(bit_vector)`.
- **EAn**: Executable Anum. Exact base arithmetic.
- **EUn**: Executable Unum. Precise addition via carry-out formula.
- **Interval**: `[lo, hi]` bounds tracking.
- **TAI**: Reduced product of Tnum x Anum x Interval x Unum.

The **reduced product** propagates information across domains:
- Interval bounds clear impossible high bits in Tnum and Anum
- Tnum/Anum/Unum min/max tighten the interval
- Unum is rebuilt from tightened interval after bitwise ops
- Unum is threaded directly through arithmetic ops (precise addition)

## Key theorems

| Theorem | File | What it says |
|---------|------|-------------|
| `plus_bv_eq` | tnum.rs | Non-recursive addition formula = recursive |
| `plus_c_carry_decomp` | tbit.rs | The carry compensation property |
| `tn_ext` | tnum.rs | Two inv Tnums with same membership are equal |
| `div_tn_sound` | div.rs | General Tnum/Tnum division is sound |
| `div_const_an_sound` | anum.rs | Anum division by constant with exact base quotient |
| `plus_sound` | unum.rs | Single-field Unum addition is sound |
| `plus_precise` | unum.rs | Single-field Unum addition is precise (no extraneous values) |
| `cout_c_overflow` | unum.rs | Carry-out register = low-bits overflow |
| `plus2_sound` | unum.rs | Two-field Unum addition with boundary preservation |
| `to_an_sound` | unum.rs | Unum to Anum conversion is sound |

## Prerequisites

- [Verus](https://github.com/verus-lang/verus) for formal verification
- [cargo-verus](https://github.com/verus-lang/verus) (`cargo install cargo-verus`)
- Rust toolchain (see `rust-toolchain.toml`)

## Running

```bash
# Verify all proofs (754 lemmas)
cargo verus verify

# Verify only the Unum module (fast, ~5s)
verus --crate-type lib src/lib.rs --verify-module unum

# Run fuzz tests (29 tests, ~12s)
cargo test --test fuzz --release

# Run demo
cargo run --features bin
```

## Verification status

- 754 Verus proofs, 0 admits, 0 errors
- 29 fuzz tests, all passing
- 5 bit-widths: u8, u16, u32, u64, u128
- 4-bit exhaustive: 0 unsound / 1,183,744 Unum addition pairs

## Design documents

- [Unum design](doc/unum-design.md): full explanation of Unums, the carry-out
  formula bug and fix, incomparability with Tnums, TAIU reduced product, and
  proof strategy.
- [Abstract domains design](doc/design.md): overall architecture and proof methodology.
