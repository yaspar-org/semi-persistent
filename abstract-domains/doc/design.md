# Semi-Persistent Abstract Domains

A proved abstract domains library for bitvector arithmetic. `cargo verus
verify` reports 0 errors, and a CI source gate rejects
project-local `admit()`/`assume()` calls. The pinned `vstd` dependency remains
inside the trust boundary. A separate Rust mirror suite supplies finite
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

The other Anum operations come in three kinds. `lshi`, `neg` and `join` are
native: `lshi` shifts base and span together; `neg` reflects through `2^w`
(`Anum::reflect`, base `2^w - (base + span)`, same span, since `span - δ` is a
bit subset of `span` when `δ` is); `join` takes the lower base and covers the
join of both offset Tnums above it (`Anum::cover`: a member of a Tnum is a bit
subset of `val | mask`). Bitwise ops, `rshi` and `meet` go through Tnum, as
`from_tnum(op(to_tnum a, to_tnum b))`, since an Anum has no better
representation for them. `mul` is the bounded `Anum::mul_anum`: the partial
products of one operand's Tnum by each bit of the other are summed in an Anum
accumulator. At width `w`, `lshi`, `neg`, `add` (and so `mul`) widen to top
when a bound would wrap.

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

### Combining the domains

These domains are combined through `reduce::Product` and the per-sort fact
records, described in [`reduced-product.md`](reduced-product.md). #123 removed
the earlier `ReducedProduct`, which combined exactly Tnum, Anum, Interval and
Unum with a reduction written by hand for those four. Tnum, Anum and Unum join
`Product` once they implement `Domain` with a `BotOr` bottom and `Refine`.

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
Layer 4: exec_tnum.rs + exec_anum.rs + exec_unum.rs — Machine-word execution, generic over the width
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
constant. `Anum::mul_anum` multiplies Tnums into an Anum by shift-and-add
with an Anum accumulator; it is the model of Anum `mul`. Tnum multiplication
uses pair-join (`Tnum::pair_mul`, `pair_mul.rs`), which is more precise.

**Unum** (`unum.rs`): Horizontally composable additive tristate numbers.
The unbounded addition formula and multiplication's bilinear bound have
containment proofs. No exactness or associativity theorem is present.
Membership uses borrow-tracking subtraction, and the core addition proof
maintains `cd + br ≤ cx + b1 + b2`.

**Div** (`div.rs`): Tnum division and subtraction. Long division by iterated
subtraction. `div1_div_mod` proves that the spec long division `div1` computes
`n / d` and `n % d` for every `n` below `2^w`, so `div_const_sound_div` and
`div_sound_div` state that the quotient and remainder Tnums contain `/` and `%`
of every such member (constant divisor and general Tnum÷Tnum). Negation and
subtraction (`neg_sound`, `sub_sound_all`) are proved for every member.

All contracts described in this Layer-2 inventory verify without admits.

### Layer 3: Bounded register simulation (`chopped.rs`)

`ChoppedTnum{tnum, w}`, `ChoppedAnum{anum, w}`, `ChoppedUnum{unum, w}` wrap
L2 types with a bit-width. The current explicit bounded containment contracts
are:

- ChoppedTnum: add, sub, neg, mul, bitwise (or, and, xor,
  and_not, not), shifts (lsh, rsh, lshi, rshi), join, meet
- ChoppedAnum: add, add_w (top on overflow), sub, div_const, from_tnum and
  to_tnum, under their stated fit/divisor preconditions; lshi, neg, join; bitwise
  (and, or, xor, not) and rshi through Tnum; mul (`mul_step`, the bounded
  `Anum::mul_step_anum`)
- ChoppedUnum: add and mul, under their stated no-overflow/fit preconditions

The `div` spec function currently has no corresponding Layer-3 soundness
theorem. All contracts that are stated in this layer verify without
project-local admits.

### Layer 4: Executable machine-word domains (`exec_tnum.rs`, `exec_anum.rs`, `exec_unum.rs`)

Each executable domain is written once, generic over the width:
`impl<W: BitWord> ExecTnum<W>`, `ExecAnum<W>` and `ExecUnum<W>`, with
`Interval<W>` (`interval.rs`) over `W: Word`. `domains.rs` names them at u8,
u16, u32 and u64 (`d8` .. `d64`). No per-width proof remains in domain code:
the bridges are the `BitWord` lemmas of `bitword.rs` (`lemma_and`, `lemma_or`,
`lemma_xor`, `mul_wrap`, `shl_wrap`, and the generic `lemma_add`,
`lemma_sub`, `lemma_neg`, `lemma_not`, `lemma_and_not`, `lemma_shr`,
`lemma_low_bit`), and bound checks use `Word::checked_add` and
`checked_mul`. ExecTnum's well-formedness is `to_tn().inv()`, taken from the
Layer-3 inv lemmas. Containment is stated on the word view: `W::from_int` for
wrapping add, sub and neg, `and`/`or`/`xor`/`not` for the bitwise operations,
and `chop` of the nat result for shifts and products.

Every L4 method verifies its stated contract. Universal containment is
currently proved for:

- `ExecTnum::{constant,top,bw_or,bw_and,bw_xor,bw_not,bw_and_not,add,sub,neg,
  mul,divrem_g,divrem,rsh,lsh,rshi,lshi,join,meet}`, each derived from its
  Layer-3 theorem through `lemma_ct()`;
- `ExecAnum::{constant,top,add,sub,div_const,from_etn,to_etn,neg,lshi,join,
  bw_and,bw_or,bw_xor,bw_not,rshi,meet,mul,mul_precise}`, the same way;
- `ExecUnum::{constant,top,add,from_interval,mul}`;
- every `Interval<W>` operation (`interval.rs`);
- generic `Congruence<W>` exact refinement/meet, least-upper-bound join,
  join-based widen, and unsigned add/sub/neg.


Most `ExecTnum` operations, and `ExecAnum::{top,add,neg,lshi,join,bw_and,
bw_or,bw_xor,bw_not,rshi,mul,to_etn,from_etn}`, also ensure, as a clause
separate from containment, that their result equals the Layer-3 spec
(`r.to_tn() == ct.op().tnum`, `r.to_an() == ca.op().anum`). This
lets composite operations chain them (`neg` and `sub` through `bw_not` and
`add`; the `mul` loop invariant through `add` and `join`), and it pins
precision: a less precise `add` would still be sound but would break these
proofs. `meet` does not export it: it normalizes, and equals the spec only when
the operands share a member; neither does `ExecAnum::meet`, which is built on
it. `ExecAnum::mul` follows `ChoppedAnum::mul_step` with the exec `add`, so its
loop invariant is the spec equality. It is often top, because the bounds of the
partial products sum past 2^W. `ExecAnum::mul_precise` trades time for
precision: it also computes pair-join on the two Tnums, meets it with `mul`, and
keeps whichever of `mul` and the meet has fewer span bits (the meet alone can be
looser than `mul`, since reading an Anum as a Tnum carries the base into the
span). At u8 with bases and spans below 16, results average 151.7 values,
against 196.5 for `mul`. It has containment but no spec equality. `ExecTnum::mul` is pair-join multiplication
(`ChoppedTnum::mul`, `Tnum::pair_mul`): starting from the exact product of the
known bits, each unknown bit keeps both sums with `join(acc, acc + c)`. See
`future/tnum-mul-div-precision.md`.

Congruence uses private canonical finite-word classes and external `BotOr` for
empty intersections. Its meet delegates positive-modulus inputs to the shared
CRT helper. The first two members characterize stride divisibility, which
proves the GCD join is below every common upper bound. Addition uses proved
extreme members to preserve `gcd(s1, s2)` when all sums or differences lie
in one wrapping segment. Only mixed wrapping includes the machine modulus.
Subtraction is direct; negation subtracts from zero and preserves the stride
when zero is absent. Runtime arithmetic uses `W: Word`, including u128.
Contracts prove containment and constant exactness, not general optimality.
Full mixed-wrap splitting remains a precision follow-up. Signed transfer instances,
multiplication, and division are deferred.

Other executable operations currently prove well-formedness only. L2/L3
soundness and finite mirror tests do not by themselves establish the missing
L4 refinement theorem.

See `proof-status.md` for the detailed scoreboard.


## Verification Status

The current verification scope and test coverage are recorded in
[`proof-status.md`](proof-status.md), together with the commands used to
check them. The source contains no executable `admit()` or `assume()`.


## Summary

| Component | Status |
|---|---|
| Layer 1 (nats) | Stated contracts verified |
| Layer 2 (tnum) | Stated contracts verified without admits |
| Layer 2 (anum) | Stated contracts verified, including `div_const` |
| Layer 2 (unum) | Add/mul containment and supporting contracts verified |
| Layer 3 (chopped) | Stated bounded-simulation contracts verified |
| Layer 4 (exec) | All stated contracts proved for every `W: BitWord`; universal containment only for the explicit inventory above |
| Division | Tnum constant and general containment proved |
| Anum division | Positive constant-divisor containment proved |
| Unum domain | Sound unbounded/bounded add and mul; no general exactness theorem |
| Congruence | Generic `Domain` and `Arith<Unsigned<W>>`; exact meet/refinement and LUB join |
| Reduced product | 4-domain (Tnum×Anum×Interval×Unum) |
| Multi-width | `ExecTnum`, `ExecAnum`, `ExecUnum` generic over `W: BitWord`, named at u8, u16, u32, u64; `Congruence<W>`: u8, u16, u32, u64, u128 |
| Rust mirror tests | See `proof-status.md` for coverage and commands |
