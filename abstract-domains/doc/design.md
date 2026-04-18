# Semi-Persistent Abstract Domains

A proved abstract domains library for bitvector arithmetic. 880 verified obligations,
13 admits remaining (all in Layer 4 soundness contracts), 30 soundness fuzz tests.

## Background

Tristate numbers (Tnums) were introduced in the Linux kernel's eBPF verifier
to track which bits of a register are known (0 or 1) versus unknown. The
verifier uses Tnums to prove safety properties (bounds checks, alignment,
absence of undefined behavior) before loading BPF programs into the kernel.
The original C implementation did not come with formal proofs of correctness.

We first implemented Tnums in Rust back in 2024 and, using Kani, proved soundness
of all abstract bitwise operations and all abstract arithmetic operations except
multiplication and division. This gave us confidence in the algorithms, but the
proofs were not compositional; each operation was verified independently by exhaustive
bitblasting, with no shared proof infrastructure or inductive reasoning.
Critically, we did not have a proof for the mul and div algorithm, and
neither did the original authors.

Ernie Cohen then developed a layered formalization approach that avoids
bitblasting entirely. The approach models bitvectors as infinite sequences
of booleans obtained by repeated mod-2 / div-2 on natural numbers. Tnum
operations are formalized as recursive functions over these infinite bit
sequences, and soundness is established through four refinement layers:

1. **Layer 1**: Bitwise and arithmetic operations on natural numbers, modeled
   as infinite bitstrings via mod-2/div-2.
2. **Layer 2**: Abstract domain types (Tnum, Anum) defined as recursive
   functions over these bitstrings, with soundness proofs for every operation.
3. **Layer 3**: Bounded-width simulation, proving that chopping the infinite
   bitstring to *w* bits preserves soundness.
4. **Layer 4**: Machine-word implementations on native integer types, proved
   to compute the same results as the chopped versions.

We implemented this layered model in Verus (verified Rust) and used a combination
of LLMs (Claude Opus 4.6 1m, Claude Sonnet 4.6 1m, DeepSeek v3.2) together with
brute-force Python simulation to discover the missing inductive invariant needed
to complete the Layer 2 proofs: the *carry compensation property*. We then
continued through Layers 3 and 4, added novel Anum division with exact base
quotients, fleshed out the _Unum abstract domain_ that Ernie imagined, an extension
of Anums that can track hard boundaries between slices of a bitvector, and prevents
uncertainty from propagating beyond boundaries. We built a reduced product of the
domains with a soundness proof of the reduction.

In parallel, we developed the same types and algorithms in Lean 4. Both the
Verus and Lean formalizations got stuck at different points, and progress in
each path unlocked the other. Lemma statements and inductive invariants
discovered in one prover were transferred to the other, and both reached
completion.

## How Soundness Is Formalized

An abstract domain is sound if every concrete result of an operation is
contained in the abstract result. For a binary operation ⊕ on domain D,
soundness means:

```
∀ x y. a.has(x) ∧ b.has(y) ⟹ (a ⊕ b).has(x ⊕_concrete y)
```

Each domain defines `has` differently, so the soundness statement takes a
different form for each. The four domains form a progression, each improving
on the previous:

| Domain | Strength | Weakness |
|--------|----------|----------|
| Tnum | Precise for bitwise ops | Carry destroys info on add |
| Anum | Exact base on add | Still loses carry info in offset |
| Unum | Precise for add (no carry loss) | No bitwise precision |
| Interval | Precise for add, div | No bit-level info |

The reduced product combines all four, using each where it excels.


## The Four Domains

### Tnum: per-bit known/unknown tracking

A Tnum `{val, mask}` satisfies `has(n) ⟺ (n & ~mask) == val`: the bits of
`n` outside the mask equal `val`. Soundness of addition:

```
∀ x y. self.has(x) ∧ t.has(y) ⟹ self.add(t).has(nat_add(x, y))
```

The proof works by induction on the bitstring length. At each bit position,
`TBit::add_carry_sound` establishes that the single-bit abstract addition
contains the concrete carry and result. The inductive step threads the carry
through the recursion.

For bitwise operations (or, and, xor), soundness is simpler: `has_equiv`
reduces membership to a per-bit property, and each bit is handled
independently.

**The problem with Tnums**: carry destroys lower-bound information.
`1 + u = uu`. The carry from adding 1 to an unknown bit makes *two* bits
unknown. Range grows exponentially instead of linearly. Addition is not even
associative in precision: `(1+1)+u = 1u` (range 2), but `1+(1+u) = uuu`
(range 8).

### Anum: base + offset with exact base arithmetic

An Anum `{base, span}` satisfies `has(x) ⟺ x ≥ base ∧ Tnum(0, span).has(x - base)`:
the value is at least `base`, and the offset `x - base` has only bits within
`span`. Soundness of addition:

```
∀ x y. self.has(x) ∧ a.has(y) ⟹ self.add(a).has(nat_add(x, y))
```

The proof decomposes: if `x = base₁ + δ₁` and `y = base₂ + δ₂`, then
`x + y = (base₁ + base₂) + (δ₁ + δ₂)`. The base `base₁ + base₂` is exact
(no approximation). The offset `δ₁ + δ₂` is handled by Tnum addition
soundness on `Tnum(0, span₁)` and `Tnum(0, span₂)`.

For Anum division by constant `d`, soundness says:

```
∀ x. self.has(x) ⟹ self.div_const(d).has(x / d)
```

The proof uses monotonicity of integer division: since `base ≤ x ≤ base + span`,
we get `base/d ≤ x/d ≤ (base+span)/d`. The result Anum has base `base/d`
(exact) and a span covering the range.

**Improvement over Tnum**: the base adds exactly, so precision loss only
affects the offset. But the offset still suffers from carry expansion.

### Unum: horizontally composable additive tristate numbers

A Unum `{base, walls, extent}` partitions the bits into fields. Within each
field, the offset from `base` ranges over a contiguous interval `[0, max]`.
Since each field is a contiguous range, addition within a field is precise
(like interval addition). Since the fields are at different bit positions,
they don't interfere (horizontal compositionality).

The `walls` register marks field boundaries (1 = start of new field).
The `extent` register stores each field's maximum in the corresponding bits.

Addition:
```
result.base   = base₁ + base₂
result.extent = extent₁ + extent₂
result.walls  = (walls₁ & walls₂) & ~(carry_out << 1)
```

A boundary survives only if both inputs have it AND no carry from the extent
sum crossed it. The carry-out formula `cout = (a & b) | ((a | b) & ~(a + b))`
correctly handles carry propagation chains of arbitrary length.

Soundness:
```
∀ x y. self.has(x) ∧ t.has(y) ⟹ self.add(t).has(nat_add(x, y))
```

The proof tracks a 5-bit state machine `(cd, br, cx, b1, b2)` with invariant
`cd + br ≤ cx + b1 + b2`. At surviving boundaries, all credits are zero,
forcing all debts to zero.

Multiplication uses bilinear expansion:
```
result = {base: base₁*base₂, walls: 0, extent: base₁*extent₂ + base₂*extent₁ + extent₁*extent₂}
```

**Improvement over Anum**: precise addition with no carry loss at all. The
offset is a contiguous range, not a bit-pattern set.

See `unum-design.md` for the full Unum specification, algorithm details,
worked examples, and the invariant discovery process.

### Interval: simple lo/hi bounds

An Interval `{lo, hi}` satisfies `has(x) ⟺ lo ≤ x ≤ hi`. Precise for
addition (when no overflow) and division. No bit-level information.

### ReducedProduct: combining all four

The reduced product combines all four domains:
```
ReducedProduct.has(x) ⟺ tnum.has(x) ∧ anum.has(x) ∧ interval.has(x) ∧ unum.has(x)
```

Each operation uses the best domain for that operation. After each operation,
`reduce()` cross-propagates information:

1. Tighten interval from Tnum/Anum/Unum min/max bounds.
2. Clear impossible high bits in Tnum/Anum using interval upper bound.
3. Rebuild Unum from tightened interval.

Soundness of `reduce`: narrowing never removes a value present in all
components. Soundness of operations: compose the four component soundness
proofs, then apply reduce soundness.


## How We Found the Missing Invariant

The missing piece was `add_bitwise_eq`: proving that the non-recursive Tnum
addition formula (5 nat-level operations, used by the Linux kernel) produces
the same result as the recursive formula (bit-by-bit via `TBit::add_carry`).
This lemma is also the foundation of the multiplication proof, since the
shift-add multiplication loop calls the non-recursive formula at each step.
Without it, neither addition nor multiplication could be proved sound. The
This proof was unexpectedly difficult to establish from first principles.

We had to simulate both the Layer 1 abstractions (nat-level operations) and
Layer 2 abstractions (recursive Tnum operations) in lockstep, comparing every
intermediate value at every recursion level, to discover the relational
invariant connecting the two formulations. The Python scripts used in this
process are preserved in `scripts/`.

**Phase 1: Brute-force simulation.** We wrote Python scripts that
exhaustively enumerated all 3-4 bit Tnum additions and compared the
non-recursive formula against the recursive one at every bit position. The
simulation confirmed they always agree, but didn't tell us *why*.

**Phase 2: Searching for per-bit invariants.** A tracing script dumped every
intermediate value at each recursion level. We then tested candidate
invariants across all cases. This found three necessary conditions:

- `carry_u <= cm` (the ub carry is bounded by the m-carry)
- `cm == 0 ==> carry_u == 0` (when m-carry is known, ub carry is zero)
- `cm == 1 ==> mask_i == 1` (uncertain carry means mask absorbs it)

These were necessary but not sufficient.

**Phase 3: The failed direct approach.** We tried proving structural equality
directly. The SMT solver couldn't close the gap because `TBit::add_carry` has
~15 nested `let` bindings and Z3 can't evaluate it structurally.

**Phase 4: Extensionality pivot.** We proved `tn_ext` (Tnum extensionality):
two inv Tnums with the same `has` set are structurally equal. This reduced
structural equality to `has`-equivalence.

**Phase 5: The tail decomposition wall.** To prove `has`-equivalence
inductively, we needed the tail of the non-recursive formula to equal the
non-recursive formula applied to tails. When the carry bit `c1.m == T`, the
two formulas use *different* carries, yet simulation shows the results match.

**Phase 6: Finding the compensation.** Another Python script checked: when
`c1.m == T`, what are `cm1` and `ub_carry`? The output showed they're never
both 0 and never both 1. Exactly one is always 1. So the non-recursive
formula puts the extra 1 in the ub carry, the recursive formula puts it in
the lbm carry, and the totals are identical.

**Phase 7: The algebraic proof.** Why does `cm1 XOR ub_carry == T` when
`c1.m == T`? Tracing through the `TBit::add_carry` formula:

- `c1.m = maskc = ubc XOR cv1`
- When `c1.m == T` and `cv1 == T`: from the inv constraints, `cv1 == T`
  means ≥2 of `{sv, tv, cv}` are 1, each forcing the corresponding `m` to 0,
  which forces `cm1 == ubc1`. Contradiction with `c1.m == T`.
- Therefore `cv1 == F` when `c1.m == T`.
- So `c1.m = ubc = cm1 XOR ub_carry`. Since `c1.m == T`: `cm1 XOR ub_carry == T`. QED.

We added this as one line to `add_carry_decomp`:
```
&&& (c1.m.b() ==> (cm1.b() != (rv0.b() && rm0.b())))
```

The solver proved it instantly. Everything else followed mechanically.


## Architecture

```
Layer 1: bools.rs + nats.rs        — Natural number algorithms on infinite bitstrings
Layer 2: tbit.rs + tnum.rs         — Recursive abstract domain operations + soundness
         anum.rs + unum.rs + div.rs
Layer 3: chopped.rs                — Bounded (w-bit) simulation via chop
Layer 4: exec_tnum.rs + domains.rs — Machine-word execution on u8/u16/u32/u64/u128
```

### Layer 1: Natural numbers as infinite bitstrings (`bools.rs`, `nats.rs`)

A natural number is an infinite boolean string accessed via `lsb(n) = n % 2`
(least significant bit) and `shr1(n) = n / 2` (right shift by one). All
bitwise operations are defined as pointwise maps via `mapd(a, b, f)`, and
addition is a recursive full adder `nat_add_carry(a, b, carry)`. The main
definitions include `bit(n, i)`, `bw_or`, `bw_and`, `bw_xor`, `bw_and_not`,
`nat_add`, `chop`, `exp`, `all_ones`, `nat_mul_acc`, and `twos_comp`.

Key lemmas:
- `eq_from_bits`: bitwise equality implies structural equality
- `mapd_hd_tl`: bitwise ops decompose through head/tail
- `nat_add_carry_correct`: recursive addition equals arithmetic addition
- `chop_is_mod`: chopping equals modular arithmetic
- `chop_nat_add`, `chop_nat_mul`: chopping distributes over add/mul

**50 proof fns, 1018 lines. All proved.**

### Layer 2: Abstract domains with soundness proofs

This layer defines the abstract domain types and proves soundness of every
operation over infinite bitstrings.

**TBit** (`tbit.rs`): The single-bit abstract domain. All operations proved
sound with empty proof bodies; Z3 handles the boolean case analysis directly.
The critical `add_carry_decomp` establishes the carry compensation property.
*14 proof fns, 273 lines.*

**Tnum** (`tnum.rs`): Tristate numbers on unbounded naturals. Membership
defined recursively and proved equivalent to the bitwise form via `has_equiv`.
The hardest theorem, `add_bitwise_eq`, is proved through the chain
`add_carry_decomp` → `add_bitwise_inv` → `add_bitwise_eq` → `tn_ext`.
*32 proof fns, 1142 lines.*

**Anum** (`anum.rs`): Additive tristate numbers. Addition is exact on the
base value. Novel `div_const` gives exact base quotient for division by
constant. Tnum multiplication uses Anum as internal accumulator (`tnum_mul`).
*19 proof fns, 561 lines.*

**Unum** (`unum.rs`): Horizontally composable additive tristate numbers.
Precise addition via bitfield partitioning. Bilinear multiplication.
Membership via borrow-tracking subtraction. Core invariant `cd + br ≤ cx + b1 + b2`
discovered through exhaustive state-machine enumeration.
*26 proof fns, 789 lines.*

**Div** (`div.rs`): Tnum division and subtraction. Long division by iterated
subtraction; both constant-divisor and general Tnum÷Tnum proved sound.
*12 proof fns, 660 lines.*

**All proved. No admits.**

### Layer 3: Bounded register simulation (`chopped.rs`)

`ChoppedTnum{tnum, w}`, `ChoppedAnum{anum, w}`, `ChoppedUnum{unum, w}` wrap
L2 types with a bit-width. This layer proves that bounded operations simulate
unbounded operations via `chop(_, w)`. All bounded operations are proved
sound.

- ChoppedTnum: add, mul, bitwise (or, and, xor), shift (lsh, rsh), join, meet
- ChoppedAnum: add, div_const
- ChoppedUnum: add, mul

**16 proof fns, 330 lines. All proved. No admits.**

### Layer 4: Executable machine-word domains (`domains.rs`, `exec_tnum.rs`)

Native Rust implementations on u8, u16, u32, u64, u128 via macro generation.
Five domain types: ExecTnum, ExecAnum, ExecUnum, Interval, ReducedProduct.

The **value bridge** connects native wrapping arithmetic to spec chopping:
- `bridge_add(a, b)`: `wrapping_add(a,b) as nat == chop(nat_add(a,b), W)`
- `bridge_mul(a, b)`: `wrapping_mul(a,b) as nat == chop(prod(a,b), W)`

The **bitwise bridge** connects native bitwise ops to spec bitwise ops:
- `bit_is_native_bit(n, i)`: `bit(n as nat, i) == ((n >> i) & 1 == 1)`
- `native_xor(a, b)`: `(a ^ b) as nat == bw_xor(a as nat, b as nat)`
- `native_or(a, b)`: `(a | b) as nat == bw_or(a as nat, b as nat)`
- `native_and(a, b)`: `(a & b) as nat == bw_and(a as nat, b as nat)`

Interval is fully proved (add, meet, join, div_const). All other domain
operations have soundness `ensures` clauses with `admit()` placeholders,
to be eliminated one at a time using the bridge lemmas + L3 soundness.

**10 proof fns in domains.rs (×5 widths), 3 in exec_tnum.rs. 13 admits remaining.**

See `proof-status.md` for the detailed scoreboard.


## Verification Status

880 Verus verified obligations, 1 error (exp_128 rlimit), 13 admits.
30 fuzz tests passing. 5 bit-widths: u8, u16, u32, u64, u128.

| File | Lines | Proof fns | Status |
|------|-------|-----------|--------|
| bools.rs | 48 | 1 | ✅ all proved |
| tbit.rs | 273 | 14 | ✅ all proved |
| nats.rs | 1018 | 50 | ✅ all proved (exp_128 rlimit) |
| tnum.rs | 1142 | 32 | ✅ all proved |
| anum.rs | 561 | 19 | ✅ all proved |
| unum.rs | 789 | 26 | ✅ all proved |
| div.rs | 660 | 12 | ✅ all proved |
| chopped.rs | 330 | 16 | ✅ all proved |
| domains.rs | 726 | 10 ×5 | 13 admits |
| exec_tnum.rs | 749 | 3 | ✅ all proved |
| fuzz.rs | 936 | — | 30 tests pass |


## Summary

| Component | Status |
|---|---|
| Layer 1 (nats) | Complete |
| Layer 2 (tnum) | 0 axioms, fully proved |
| Layer 2 (anum) | Complete + novel div_const |
| Layer 2 (unum) | Complete (add + mul) |
| Layer 3 (chopped) | 0 axioms, fully proved |
| Layer 4 (exec) | 13 admits (WIP) |
| Division | Proved (constant + general) |
| Anum division | Proved (novel exact-base quotient) |
| Unum domain | Proved (precise add + bilinear mul) |
| Reduced product | 4-domain (Tnum×Anum×Interval×Unum) |
| Multi-width | u8, u16, u32, u64, u128 |
| Fuzz tests | 30 tests |
