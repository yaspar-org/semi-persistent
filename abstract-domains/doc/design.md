# Semi-Persistent Abstract Domains

A proved abstract domains library for bitvector arithmetic. The ordinary Verus
run has 994 verified conditions and 0 errors, and a CI source gate rejects
project-local `admit()`/`assume()` calls. The pinned `vstd` dependency remains
inside the trust boundary. A separate 32-test Rust mirror suite supplies finite
randomized/exhaustive evidence.

## Background

Tristate numbers (Tnums) were introduced in the Linux kernel's eBPF verifier
to track which bits of a register are known (0 or 1) versus unknown. The
verifier uses Tnums to prove safety properties (bounds checks, alignment,
absence of undefined behavior) before loading BPF programs into the kernel.
The original C implementation did not come with formal proofs of correctness.

Finite-width bitblasting can establish individual operation instances, but it
does not provide compositional proofs or a shared inductive model. In particular,
multiplication and division require reasoning that scales independently of the
chosen machine width.

Ernie Cohen then developed a layered formalization approach that avoids
bitblasting entirely. The approach models bitvectors as infinite sequences
of booleans obtained by repeated mod-2 / div-2 on natural numbers. Tnum
operations are formalized as recursive functions over these infinite bit
sequences, and soundness is established through four refinement layers:

1. **Layer 1**: Bitwise and arithmetic operations on natural numbers, modeled
   as infinite bitstrings via mod-2/div-2.
2. **Layer 2**: Abstract domain types (Tnum, Anum) defined as recursive
   functions over these bitstrings, with soundness proofs for every operation.
3. **Layer 3**: Bounded-width simulation. Explicit containment theorems connect
   selected operations to their chopped results; other definitions currently
   have only invariant/width preservation or no Layer-3 theorem.
4. **Layer 4**: Machine-word implementations on native integer types. Every
   method verifies its written contract; selected operations have universal
   containment refinements to the chopped theory, while others currently prove
   only well-formedness.

The Verus formalization implements all four layers. Its central inductive fact is
the *carry compensation property*, which connects recursive bit-level addition
to the closed-form Tnum operation. The library also covers Anum division with
exact base quotients, Unum field boundaries that stop uncertainty propagating
across slices, and a reduced product with a proof that reduction preserves every
represented concrete value.

## How Soundness Is Formalized

An abstract domain is sound if every concrete result of an operation is
contained in the abstract result. For a binary operation ⊕ on domain D,
soundness means:

```
∀ x y. a.has(x) ∧ b.has(y) ⟹ (a ⊕ b).has(x ⊕_concrete y)
```

Each domain defines `has` differently, so the soundness statement takes a
different form for each. The domains are complementary rather than a total
precision ordering:

| Domain | Strength | Weakness |
|--------|----------|----------|
| Tnum | Bitwise-aware transfer functions | Carry destroys info on add |
| Anum | Exact base on add | Still loses carry info in offset |
| Unum | Field-sensitive arithmetic bounds | No native bitwise transfer |
| Interval | Exact non-wrapping add and positive constant division | No bit-level info |

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
Fields at different bit positions can retain independent bounds. The
executable representation has no canonical-form invariant, however, so these
facts do not imply that every abstract addition is exact.

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

**Difference from Anum**: each Unum field denotes a contiguous offset range,
whereas an Anum span denotes independently selectable offset bits. The
verified theorem for Unum addition is containment, not exactness. Exactness is
false for some encodings accepted or produced by the executable API; see
`unum-design.md`.

See `unum-design.md` for the full Unum specification, algorithm details, worked
examples, and proof invariant.

### Interval: simple lo/hi bounds

An Interval `{lo, hi}` satisfies `has(x) ⟺ lo ≤ x ≤ hi`. Its executable
addition is exact when endpoint arithmetic does not overflow and otherwise
widens to top. Positive constant division is exact for unsigned,
non-wrapping intervals. No interval-by-interval division is implemented.

### ReducedProduct: combining all four

The reduced product combines all four domains:
```
ReducedProduct.has(x) ⟺ tnum.has(x) ∧ anum.has(x) ∧ interval.has(x) ∧ unum.has(x)
```

Each operation constructs the available component results. After each
operation, `reduce()` cross-propagates information:

1. Tighten interval from Tnum/Anum/Unum min/max bounds.
2. Clear impossible high bits in Tnum/Anum using interval upper bound.
3. Rebuild Unum from tightened interval.

`reduce` has a universal containment theorem: narrowing never removes a value
present in all components. `ReducedProduct::add` composes all four component
containment proofs and then applies reduce containment. The other executable
ReducedProduct methods currently guarantee well-formed results but do not yet
carry universal containment postconditions; their intended composition is not
a proved Layer 4 theorem until those contracts are added.

The exact contracts implemented by the interval component are listed in
[`interval-soundness.md`](interval-soundness.md). General division and alarms,
abstract comparisons and narrowing, wrapped intervals, and strided intervals
are maintained as future designs in
[`future/interval-extensions.md`](future/interval-extensions.md).


## Carry Compensation Invariant

The missing piece was `add_bitwise_eq`: proving that the non-recursive Tnum
addition formula (5 nat-level operations, used by the Linux kernel) produces
the same result as the recursive formula (bit-by-bit via `TBit::add_carry`).
This lemma is also the foundation of the multiplication proof, since the
shift-add multiplication loop calls the non-recursive formula at each step.
Without it, neither addition nor multiplication has a compositional soundness
proof.

Three per-bit relations connect the recursive and non-recursive forms:

- `carry_u <= cm` (the ub carry is bounded by the m-carry)
- `cm == 0 ==> carry_u == 0` (when m-carry is known, ub carry is zero)
- `cm == 1 ==> mask_i == 1` (uncertain carry means mask absorbs it)

`tn_ext` reduces structural equality of invariant Tnums to equality of their
`has` sets. The inductive tail step then has one exceptional case: when
`c1.m == T`, the two formulas route a carry differently. Carry compensation
states that exactly one of `cm1` and `ub_carry` is set, so the non-recursive
formula places the extra one in the upper-bound carry while the recursive
formula places it in the lower-bound-mask carry. The totals remain equal.

Algebraically, `cm1 XOR ub_carry == T` follows from `c1.m == T`:

- `c1.m = maskc = ubc XOR cv1`
- When `c1.m == T` and `cv1 == T`: from the inv constraints, `cv1 == T`
  means ≥2 of `{sv, tv, cv}` are 1, each forcing the corresponding `m` to 0,
  which forces `cm1 == ubc1`. Contradiction with `c1.m == T`.
- Therefore `cv1 == F` when `c1.m == T`.
- So `c1.m = ubc = cm1 XOR ub_carry`. Since `c1.m == T`: `cm1 XOR ub_carry == T`. QED.

The corresponding clause in `TBit::add_carry_carry_decomp` is:
```
&&& (c1.m.b() ==> (cm1.b() != (rv0.b() && rm0.b())))
```

Together with the three relations above, this clause discharges the recursive
tail step and lifts the addition result into the multiplication proof.


## Architecture

```
Layer 1: bools.rs + nats.rs        — Natural number algorithms on infinite bitstrings
Layer 2: tbit.rs + tnum.rs         — Recursive abstract domain operations + soundness
         anum.rs + unum.rs + div.rs
Layer 3: chopped.rs                — Bounded (w-bit) simulation via chop
Layer 4: exec_tnum.rs + domains.rs — Machine-word execution on u8/u16/u32/u64
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

These lemmas are machine-checked with no admits.

### Layer 2: Abstract domains with soundness proofs

This layer defines the abstract domain types and proves the operation
contracts inventoried below over infinite bitstrings.

**TBit** (`tbit.rs`): The single-bit abstract domain. All operations proved
sound with empty proof bodies; Z3 handles the boolean case analysis directly.
The critical `add_carry_carry_decomp` establishes the carry compensation
property.

**Tnum** (`tnum.rs`): Tristate numbers on unbounded naturals. Membership
defined recursively and proved equivalent to the bitwise form via `has_equiv`.
The hardest theorem, `add_bitwise_eq`, uses
`add_carry_carry_decomp` in the tail-decomposition argument, together with
`add_bitwise_inv`, `add_bitwise_eq`, and `tn_ext`.

**Anum** (`anum.rs`): Additive tristate numbers. Addition is exact on the
base value. `div_const` gives an exact base quotient for division by
constant. Tnum multiplication uses Anum as internal accumulator (`tnum_mul`).

**Unum** (`unum.rs`): Horizontally composable additive tristate numbers.
The unbounded addition formula and multiplication's bilinear bound have
containment proofs. No exactness or associativity theorem is present.
Membership uses borrow-tracking subtraction, and the core addition proof
maintains `cd + br ≤ cx + b1 + b2`.

**Div** (`div.rs`): Tnum division and subtraction. Long division by iterated
subtraction; both constant-divisor and general Tnum÷Tnum proved sound.

All contracts described in this Layer-2 inventory verify without admits.

### Layer 3: Bounded register simulation (`chopped.rs`)

`ChoppedTnum{tnum, w}`, `ChoppedAnum{anum, w}`, `ChoppedUnum{unum, w}` wrap
L2 types with a bit-width. The current explicit bounded containment contracts
are:

- ChoppedTnum: add, mul, shifts (lsh, rsh), join, meet
- ChoppedAnum: add and div_const, under their stated fit/divisor preconditions
- ChoppedUnum: add and mul, under their stated no-overflow/fit preconditions

ChoppedTnum bitwise `or_inv`, `and_inv`, and `xor_inv` expose
invariant/width-preservation postconditions and call the Layer-2 soundness
lemmas internally, but they do not state a Layer-3 containment postcondition.
The `div` and `neg` spec functions currently have no corresponding Layer-3
soundness theorem. All contracts that are stated in this layer verify without
project-local admits.

### Layer 4: Executable machine-word domains (`domains.rs`, `exec_tnum.rs`)

Native Rust implementations on u8, u16, u32, and u64 via macro generation.
The u128 instantiation is disabled because its bitvector obligations exceed
current solver capacity. Five domain types are enabled at each active width:
ExecTnum, ExecAnum, ExecUnum, Interval, and ReducedProduct.

The **value bridge** connects native wrapping arithmetic to spec chopping:
- `bridge_add(a, b)`: `wrapping_add(a,b) as nat == chop(nat_add(a,b), W)`
- `bridge_mul(a, b)`: `wrapping_mul(a,b) as nat == chop(prod(a,b), W)`

The **bitwise bridge** connects native bitwise ops to spec bitwise ops:
- `bit_is_native_bit(n, i)`: `bit(n as nat, i) == ((n >> i) & 1 == 1)`
- `native_xor(a, b)`: `(a ^ b) as nat == bw_xor(a as nat, b as nat)`
- `native_or(a, b)`: `(a | b) as nat == bw_or(a as nat, b as nat)`
- `native_and(a, b)`: `(a & b) as nat == bw_and(a as nat, b as nat)`

Every L4 method verifies its stated contract. Universal containment is
currently proved for:

- `ExecTnum::{bw_or,bw_and,bw_xor,add,join,meet}`;
- `ExecAnum::{add,div_const}`;
- `ExecUnum::{top,add,from_interval,mul}`;
- `Interval::{add,meet,join,div_const}`; and
- `ReducedProduct::{reduce,add}`.

Other executable operations currently prove well-formedness only. L2/L3
soundness and finite mirror tests do not by themselves establish the missing
L4 refinement theorem.

See `proof-status.md` for the detailed scoreboard.


## Verification Status

The current verification and test counts are recorded in
[`proof-status.md`](proof-status.md), together with the commands used to
regenerate them. The source contains no executable `admit()` or `assume()`.


## Summary

| Component | Status |
|---|---|
| Layer 1 (nats) | Stated contracts verified |
| Layer 2 (tnum) | Stated contracts verified without admits |
| Layer 2 (anum) | Stated contracts verified, including `div_const` |
| Layer 2 (unum) | Add/mul containment and supporting contracts verified |
| Layer 3 (chopped) | Stated bounded-simulation contracts verified |
| Layer 4 (exec) | All stated contracts proved at u8/u16/u32/u64; universal containment only for the explicit inventory above |
| Division | Tnum constant and general containment proved |
| Anum division | Positive constant-divisor containment proved |
| Unum domain | Sound unbounded/bounded add and mul; no general exactness theorem |
| Reduced product | 4-domain (Tnum×Anum×Interval×Unum) |
| Multi-width | u8, u16, u32, u64 (`u128` disabled) |
| Rust mirror tests | See `proof-status.md` for the regenerated count |
