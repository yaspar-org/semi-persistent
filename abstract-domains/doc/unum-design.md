# Unums: Horizontally Composable Additive Tristate Numbers

## The problem

In symbolic execution we track abstract values, each representing a set of
possible concrete bitvector values. When we apply an operation (like addition)
to two abstract values, the result must be *sound*: it must contain every
possible concrete outcome. Beyond soundness, we want *precision*: the result
shouldn't contain extraneous values that can't actually arise.

For low-level code we are particularly interested in registers (bitvectors of
fixed width). We want our abstraction to use linear space and to support both
bitwise and arithmetic operations. The three existing domains each fall short
in a different way.

### Tnums: precise for bitwise, terrible for arithmetic

A Tnum represents a set by marking each bit as 0, 1, or u (unknown).
Represented as `(v, m)` where `v` has the known-1 bits and `m` has the
unknown bits. A concrete value `n` is in the set iff `n & ~m == v`.

Example (8-bit): `Tn(v=00100, m=01011)` means bit 2 is definitely 1, bits
3-7 are definitely 0, and bits 0, 1, 3 are unknown. The set is
{4, 5, 6, 7, 12, 13, 14, 15}.

Tnums are precise for bitwise operations (AND, OR, XOR); the abstract result
contains exactly the concrete outcomes, nothing more. But they are terrible
for arithmetic:

- Carry destroys lower-bound information. `1 + u = uu`. The carry from
  adding 1 to an unknown bit makes *two* bits unknown. We went from knowing
  the value is in {1, 2} (range 2) to {0, 1, 2, 3} (range 4).

- This compounds exponentially. `1 + u = uu`, `1 + uu = uuu`, and so on.
  62 sequential increments of an unknown bit produce 63 unknown bits. The
  range grows exponentially instead of linearly.

- Addition is not associative. `(1+1)+u = 10+u = 1u` (range 2), but
  `1+(1+u) = 1+uu = uuu` (range 8). The order of operations changes the
  precision of the result.

- Bounds information is lost. Converting the interval [7, 8] (size 2) to
  a Tnum gives `1uuu` (size 8), because the bit patterns 0111 and 1000 differ
  in every position.

### Intervals: precise for arithmetic, no bit-level information

An interval `[lo, hi]` is precise for addition: `[a,b] + [c,d] = [a+c, b+d]`.
But it carries no bit-level information at all. If a register packs two
independent counters (one in the low bits, one in the high bits), an interval
can't track them independently. Uncertainty in the high counter destroys
information about the low counter.

### Anums: better arithmetic, still imprecise

An Anum `(v, m)` represents the set `{v + d | d & ~m == 0}`. The base `v` is
the minimum value, and `m` describes which bits of the *offset from v* can be
set. This is strictly better than Tnums for arithmetic because the bases add
exactly:

```
(v1, m1) + (v2, m2) = (v1 + v2,  (m1 + m2) | m1 | m2)
```

The `| m1 | m2` term is the Tnum-style carry expansion, but it only applies
to the uncertainty part, not the base. Every consistent Tnum is an Anum, and
Anums are at least as precise.

But Anums still have the carry problem in the uncertainty part. When `v = 0`,
an Anum is exactly a Tnum, and the `m1 + m2 | m1 | m2` formula still loses
precision through carries.

### What we actually want

A domain that:

1. Generalizes both Tnums and intervals.
2. Is *precise* for addition (no extraneous values).
3. Is *horizontally compositional* (packing two independent counters into one
   register doesn't destroy information about either).
4. Uses linear space (a few machine words).

No known linear-size domain combination achieves all of these. Unums are the
attempt.


## The core idea: bitfield partitioning

### Why intervals are precise but Tnums aren't

An interval `[0, 5]` represents {0, 1, 2, 3, 4, 5}, a *contiguous range*.
Adding two contiguous ranges gives a contiguous range: `[0,5] + [0,3] = [0,8]`.
No gaps, no extraneous values.

A Tnum like `(0, 0b101)` represents {0, 1, 4, 5}. Bits 0 and 2 are
independently unknown. This is *not* contiguous. It has gaps (2 and 3 are
missing). When you add two such sets, the gaps interact with carries in
complicated ways, and you lose precision.

### The Unum insight

Partition the bits into fields. Within each field, represent a contiguous
range from 0 to some maximum. Since each field is a contiguous range,
addition within a field is precise (like interval addition). Since the fields
are at different bit positions, they don't interfere with each other
(horizontal compositionality).

### Concrete example

Using 8 bits. We want to represent "a counter in bits [0:3] that's between 0
and 10, plus a counter in bits [4:7] that's between 0 and 12."

As a Unum with `v = 0`:

- Field 1: bits [0:3], max = 10 (`1010`), MSB = 1
- Field 2: bits [4:7], max = 12 (`1100`), MSB = 1

The set is `{f1 + (f2 << 4) | 0 <= f1 <= 10, 0 <= f2 <= 12}`.

A Tnum can't represent this; it would have to say all 8 bits are unknown
(range 0-255). An interval would say [0, 202], which includes all the gaps
between valid field combinations. The Unum captures the structure exactly.


## Representation

A Unum is `(v, w, x)` where:

- `v` = the base (minimum) value.
- `w` = bitfield boundary markers. A 1-bit marks the start ("leader") of a
  new bitfield. A 0-bit means "continuation of the previous field" ("follower").
- `x` = the maximum value for each bitfield, stored in the corresponding
  bit positions.

The encoding from the spec:

```
w = 1:0, 0:(w0-1), 1:0, 0:(w1-1), ...
x = max0:w0, max1:w1, ...
```

So `w` has a 1 at the start of each field, followed by (width - 1) zeros.
And `x` stores each field's max value in the corresponding bit positions.

Well-formedness constraint: If a field has width 1, its max can be 0 or 1.
If a field has width > 1, the leading bit of its max (the MSB within the
field) must be 1, i.e., `1 << (width - 1) <= max`. This ensures the field
width is tight: you can't waste bits on a max that doesn't need them.

Three quantities fall out of the representation that are useful for analysis:

- `kz = w & ~x`: the known-zero bits (leader positions where max = 0, i.e.,
  width-1 fields that are always 0).
- `ld = w & x`: the leader positions of nonzero bitfields.
- `f = ~w`: the follower positions (non-leading bits of nonzero bitfields).

The representation subsumes the other domains:

- A Tnum with no known-1 bits is a special case where each bit is its own
  width-1 bitfield with max 0 or 1. Converting: set `w = all 1s`, `x = m`.
- An interval `[lo, hi]` is a single bitfield spanning all bits with
  `v = lo`, `x = hi - lo`.
- Converting to Anum: see "Conversions" section below (not just `An(v, x)`).
- Converting to interval: `[v, v + x]`.


## Addition algorithm

The central claim: Unum addition is precise and associative.

Given `u1 = (v1, w1, x1)` and `u2 = (v2, w2, x2)`:

```
result.v  = v1 + v2
result.x  = x1 + x2
result.w  = (w1 & w2) & ~(cout << 1)
            where cout = (x1 & x2) | ((x1 | x2) & ~(x1 + x2))
```

### Why `x` is just the sum

Each field's max represents the range of uncertainty. When you add two Unums,
the total uncertainty is the sum of the individual uncertainties. Since `x`
stores the per-field maxes in their bit positions, and the fields may overlap
or merge, the total `x` is just `x1 + x2`.

### Why `w` uses the carry-out formula

A boundary (leader bit) in the result survives only if:

1. Both inputs have a boundary at that position (`w1 & w2`), AND
2. No carry from the `x1 + x2` addition crossed that boundary.

A carry crosses boundary at bit `i` when the sum of the x-bits in the field
below bit `i` overflows that field, i.e., there is a carry-out of bit `i-1`.

The standard carry-out formula for addition `s = a + b` is:

```
cout = (a & b) | ((a | b) & ~s)
```

where `cout[i]` is 1 iff there is a carry out of bit `i` (equivalently, a
carry into bit `i+1`). Shifting left by 1 converts carry-out-of-`i` to
carry-into-`i+1`:

```
carry_in = cout << 1
```

Bit 0 of `carry_in` is always 0 (no carry into the lowest bit), so the
boundary at bit 0 is always preserved when both inputs have one. The final
formula:

```
w = (w1 & w2) & ~carry_in
```

This is a fixed sequence of bitwise operations plus one addition, regardless
of register width.

### The spec's original formula was wrong

The original spec proposed:

```
w = w1 & w2 & ((~x12 & ~x1 & ~x2) | (x12 & (~x1 | ~x2)))
```

This attempts per-bit carry detection but fails because it does not account
for carry *propagation*. It checks whether bit `i` of `x1` and `x2` would
generate a carry at that position, but ignores carries arriving from lower
bits. For example, with 4-bit Unums:

```
u1 = (v=0, w=0101, x=1010): fields [0:2] max=2, [2:4] max=2
     set = {0, 1, 2, 4, 5, 6, 8, 9, 10}
u2 = (v=0, w=1101, x=0010): field [0:2] max=2
     set = {0, 1, 2}
```

The sum of the [0:2] fields has max 2+2=4, which overflows 2 bits and should
destroy the boundary at bit 2. But the spec's formula keeps it, producing
`{0, 4, 8, 12}` instead of the correct `{0, 1, ..., 12}`.

The carry-out formula correctly detects this: `cout[1]` is 1 (carry out of
bit 1), so `carry_in[2]` is 1, destroying the boundary at bit 2.

Verification: Exhaustive testing over all 1,183,744 pairs of valid 4-bit
Unums confirms the carry-out formula is sound (zero failures). The spec's
formula fails on 745,472 pairs (63%).

### Worked example: aligned fields

```
U1: one field, bits [0:3], max = 5    (w1 = 0001, x1 = 0101)
U2: one field, bits [0:3], max = 3    (w2 = 0001, x2 = 0011)
```

U1 represents {0, 1, 2, 3, 4, 5}. U2 represents {0, 1, 2, 3}.

```
x12  = 0101 + 0011 = 1000
cout = (0101 & 0011) | ((0101 | 0011) & ~1000)
     = 0001 | (0111 & 0111)
     = 0001 | 0111 = 0111
carry_in = 0111 << 1 = 1110
w = (0001 & 0001) & ~1110 = 0001 & 0001 = 0001
```

The boundary at bit 0 survives (no carry into bit 0). Result: one field
[0:4] with max = 8. Set = {0, 1, ..., 8}. Precise.

### Worked example: carry destroys boundary

```
U1: fields [0:2] max=2, [2:4] max=2   (w1 = 0101, x1 = 1010)
U2: field  [0:2] max=2                (w2 = 1101, x2 = 0010)
```

```
x12  = 1010 + 0010 = 1100
cout = (1010 & 0010) | ((1010 | 0010) & ~1100)
     = 0010 | (1010 & 0011)
     = 0010 | 0010 = 0010
carry_in = 0010 << 1 = 0100
w_cand = 0101 & 1101 = 0101
w = 0101 & ~0100 = 0001
```

The boundary at bit 2 is destroyed by the carry from the lower field
(2 + 2 = 4 overflows 2 bits). Result: one field [0:4] with max = 12.
Set = {0, 1, ..., 12}. Sound.

### Worked example: misaligned fields

```
U1: field at bits [0:3], max = 5     (w1 = 0001, x1 = 0101)
U2: field at bits [2:5], max = 3     (w2 = 0100, x2 = 1100)
```

```
w1 & w2 = 0001 & 0100 = 0000
```

No bit position has a boundary in both inputs, so all boundaries are
destroyed. The result is one big field with `x12 = 0101 + 1100 = 10001`.
This is correct: U2's max of 3 at offset 2 contributes `3 << 2 = 12`, and
`5 + 12 = 17 = 10001`.


## Membership test

To test whether a concrete value `y` is in the Unum `(v, w, x)`:

1. Compute `d = y - v` (the offset from the base).
2. For each bitfield (determined by `w`), extract the corresponding bits of
   `d` and check that they are <= the corresponding bits of `x`.

The spec describes an O(1) formulation: complement `d`, add it to `x`, and
check that no `w` bit changed or carried out. This works because if
`d_field <= max_field`, then `~d_field + max_field` won't carry out of the
field. If `d_field > max_field`, it will.


## Conversions

Converting a Unum to an Anum requires care. The naive conversion `EAn(v, x)`
is wrong because a Unum field with max = 10 (`1010`) represents the contiguous
range {0, 1, ..., 10}, while `EAn(v=0, m=1010)` represents only {0, 2, 8, 10},
the bit-pattern subsets of `m`. The Anum's per-bit independence is fundamentally
different from the Unum's per-field contiguous range. The fix is to widen `x`
to `ones(len(x))`, the smallest value of the form `2^k - 1` that is >= `x`.
This is proved sound for the single-field case (`w = 0`) in `to_an_sound_single`.
Converting to a Tnum goes through the Anum conversion, then `EAn.to_etn()`.

In the other direction, an Anum converts to a Unum by treating each bit of `m`
as its own width-1 bitfield: `EUn(v, w=all_ones, x=m)`. An interval converts
to a single bitfield spanning all bits: `EUn(lo, w=1, x=hi-lo)`.


## Bounded registers and overflow

For bounded registers (u8, u16, u32, u64, u128), if `x1 + x2` overflows the
register width, the result wraps and the stored max is wrong. The
implementation must detect this and fall back to top:

```
if x1 + x2 overflows:
    return EUn::top()
```

Verified: all overflow cases are correctly handled by the top fallback in the
4-bit exhaustive test.


## Chain of reasoning and failure modes

Working backwards from what we want:

```
We want: precise addition of abstract bitvector sets
  |  requires
Each abstract value = base + sum of independent contiguous ranges
  |  requires
Ranges are at non-overlapping bit positions (bitfields)
  |  requires
Bitfield boundaries are tracked (the w register)
  |  requires
Addition correctly merges fields when carries cross boundaries
  |  requires
The w formula correctly detects carries at boundary positions
  |  requires
cout = (x1 & x2) | ((x1 | x2) & ~(x1 + x2)) is the standard carry-out
  |  verified
Exhaustive 4-bit test: 0 unsound / 1,183,744 pairs
```

### Precondition 1: Each bitfield independently represents [0, max]

This is the fundamental invariant. A field with max = 5 in bits [0:2]
represents exactly {0, 1, 2, 3, 4, 5}. Not a Tnum-style set with gaps.

How it can fail: If we somehow get a field where the "max" doesn't bound a
contiguous range. The representation enforces this by construction: a field
with max M at offset i represents `{d << i | 0 <= d <= M}`.

### Precondition 2: Fields don't interfere (no carry leakage)

If field 1 is bits [0:3] with max 10, and field 2 is bits [4:7] with max 12,
then a value in field 1 (up to 10) can't produce a carry into bit 4. Since
10 < 16 = 2^4, this holds.

How it can fail: If a field's max is large enough that adding it to the
base could carry into the next field. But the max is stored in the field's own
bits, so it's bounded by 2^width - 1. A value in [0, max] where
max < 2^width can't carry out of the field.

But after addition, `x12 = x1 + x2` might overflow a field! If both fields
have max = 10, then x12 = 20 = `10100`, which overflows 4 bits. This is
exactly where the `w` formula comes in: the carry out of bit 3 destroys the
boundary at bit 4, merging the fields.

### Precondition 3: The `w` formula correctly detects carries

The carry-out formula `cout = (a & b) | ((a | b) & ~(a + b))` is a standard
result in digital logic. At each bit position `i`:

- `a[i] & b[i]`: both bits are 1, so a carry is generated regardless of
  carry-in.
- `(a[i] | b[i]) & ~s[i]`: at least one bit is 1, and the sum bit is 0,
  which means a carry-in was consumed and a carry-out was produced.

This correctly captures carry propagation chains of arbitrary length.

### Precondition 4: Merged fields have correct maxes

When a boundary at bit i is destroyed, the fields on either side merge. The
merged field's max is whatever `x12` has in those bit positions. Since
`x12 = x1 + x2` and the carry propagated through, the merged field's max is
the correct sum of the sub-field maxes.

### Precondition 5: Bounded register overflow

For bounded registers, if `x1 + x2` overflows the entire word, `x12` wraps
and the stored max is wrong. The implementation detects this and returns top.


## Relationship to TI (Tnum x Interval)

The Linux eBPF verifier uses TI: track both a Tnum and an interval, and
reduce with respect to both after each operation. For example,
`(u0u, [1, 4])` represents {1, 4}.

The spec notes an apparent paradox: this set, represented additively, has
uncertainty {0, 3}, which is not a contiguous range and thus not representable
as a Unum. So TI can represent some sets that Unums cannot.

But the spec argues this doesn't matter in practice: such sets can only arise
through bitwise operations (not pure addition). The set {1, 4} requires
setting a specific bit to 0 with a bitwise AND, e.g., `(uu + 1) & ~2`. Since
Unums are not designed to be precise for bitwise operations, the conversion
path is: use Unums for arithmetic, convert to TI for bitwise operations,
convert back.

This conversion is guaranteed to be at least as precise as using TI alone,
because Unums are at least as precise as Anums for addition, and Anums are at
least as precise as Tnums.


## Unums vs Tnums: incomparable domains

Unums and Tnums are not ordered by precision; they are incomparable.
Each can represent sets the other cannot:

Unum > Tnum for contiguous ranges. A Unum field with max=5 represents
{0,1,2,3,4,5} exactly. A Tnum needs `(0, 0b111)` = {0,...,7}, adding 6 and 7.

Tnum > Unum for non-contiguous sets. `Tn(0, 0b100)` = {0, 4} exactly.
No Unum can represent {0, 4} without including {1, 2, 3}.

Anum >= Tnum for addition (strictly better; every Tnum is an Anum).
Unum >= Anum for addition (strictly better; every Anum is a Unum with
per-bit fields, and Unums are precise).
Tnum >= Unum for bitwise ops (Tnums are precise, Unums lose information).

This means the optimal strategy is a reduced product of all four domains:
use each domain where it excels, and cross-reduce to propagate information.


## TAIU: the reduced product Tnum x Anum x Interval x Unum

The implementation extends the existing TAI reduced product to TAIU by adding
a Unum component. Each operation uses the best domain:

| Operation | Tnum | Anum | Interval | Unum |
|-----------|------|------|----------|------|
| AND/OR/XOR | precise | top | top | top |
| plus | imprecise | good | precise | precise |
| sub | imprecise | good | top | good |
| neg | imprecise | top | top | good |
| mul | imprecise | top | top | good |
| div_const | top | good | precise | top |
| shift | precise | top | top | top |

After each operation, `reduce()` cross-propagates:
1. Tighten interval from Tnum, Anum, and Unum min/max bounds.
2. Tighten Tnum from interval (clear impossible high bits).
3. Tighten Anum from interval.
4. Rebuild Unum from tightened interval.

The Unum is rebuilt from the interval after reduction rather than preserved
across bitwise operations, because bitwise ops destroy the bitfield structure.
For arithmetic sequences (the Unum's strength), the Unum is threaded through
directly via `EUn::plus`/`sub`/`neg`, preserving the precise bitfield
partitioning across chains of additions.


## Operations not yet specified

The spec leaves one area explicitly open:

- Bitwise operations. Unums are not precise for bitwise operations. The
  spec suggests investigating how to propagate bitwise operations through
  constant addition/subtraction (to account for the base `v`), but this is
  future work.


## Multiplication algorithm

### The algorithm: bilinear expansion

Given `u1 = (v1, w1, x1)` and `u2 = (v2, w2, x2)`, the product is:

```
result = (v1*v2, w=0, x = v1*x2 + v2*x1 + x1*x2)
```

`w=0` means a single field spanning all bits (no boundaries). The result
represents the set `{v1*v2 + d | 0 <= d <= v1*x2 + v2*x1 + x1*x2}`.

### Why it is sound

Any concrete pair `c1 ∈ u1`, `c2 ∈ u2` can be written as:

```
c1 = v1 + d1,   0 <= d1 <= x1
c2 = v2 + d2,   0 <= d2 <= x2
```

The bound `d_i <= x_i` holds for any Unum regardless of its field structure:
each field's borrow-tracking subtraction never underflows, so the total
offset is bounded by the total max. This is `d_allowed_leq_general`.

Expanding the product:

```
c1 * c2 = (v1 + d1) * (v2 + d2)
        = v1*v2  +  v1*d2  +  v2*d1  +  d1*d2
```

The uncertainty above the base `v1*v2` is `v1*d2 + v2*d1 + d1*d2`. Since
`d1 <= x1` and `d2 <= x2`:

```
v1*d2 <= v1*x2
v2*d1 <= v2*x1
d1*d2 <= x1*x2
```

Summing: `v1*d2 + v2*d1 + d1*d2 <= v1*x2 + v2*x1 + x1*x2 = result.x`.

So `c1*c2 - v1*v2 <= result.x`, which is exactly `result.has(c1*c2)` for a
single-field Unum.

### Why it is better than Anum multiplication

Anum multiplication (shift-and-add) produces `An{v=v1*v2, m=ones_mask(range)}`
where `ones_mask` rounds the range up to the nearest `2^k - 1`. The Unum
keeps the exact range `v1*x2 + v2*x1 + x1*x2` without rounding. For example,
if the range is 100, Anum rounds to 127; the Unum keeps 100.

The Unum result is also a single-field Unum, so it integrates cleanly with
subsequent Unum additions: the precise bitfield structure is preserved.

### Overflow handling

If any of `v1*v2`, `v1*x2`, `v2*x1`, `x1*x2`, or their sum overflows the
register width, the result falls back to `top()`. This is detected using
overflow-checked multiplication and addition.

### Formal proof

The soundness theorem `mul_sound` is proved in Verus with zero admits:

```
forall c1 c2: u1.has(c1) && u2.has(c2) ==> u1.mul_un(u2).has(prod(c1, c2))
```

The proof required four new lemmas:

| Lemma | What it proves |
|-------|---------------|
| `d_allowed_leq_general` | `d_allowed(w,x,d,F,true) => d <= x` for any `w` |
| `d_allowed_leq_general_c` | Same with arbitrary borrow (inductive helper) |
| `d_allowed_leq_converse` | `d <= x => d_allowed(0,x,d,F,true)` |
| `d_allowed_leq_converse_borrow` | `d+1 <= x => d_allowed(0,x,d,T,false)` |

`d_allowed_leq_general` generalizes the existing `d_allowed_leq` (which only
handled `w=0`) to arbitrary field structure. It is needed to extract `d1 <= x1`
and `d2 <= x2` from the input membership predicates.

`d_allowed_leq_converse` is the reverse direction: given `d <= x`, construct
a witness that `d_allowed(0, x, d, F, true)` holds. This closes the proof by
showing the result Unum (which has `w=0`) contains the computed uncertainty.

Both are proved by induction on the bitstring, tracking the borrow bit through
the subtraction `x - d` one bit at a time.

### How the lemmas were found

The proof goal was `mul_sound`. Working backwards:

1. The result has `w=0`, so `has(n)` reduces to `n >= v` and
   `d_allowed(0, x, d, F, true)`. The existing `d_allowed_leq` proved the
   forward direction. We needed the **converse** to close the proof —
   hence `d_allowed_leq_converse`.

2. To bound the uncertainty, we needed `d1 <= x1` and `d2 <= x2` from the
   input membership predicates. But `d_allowed_leq` only worked for `w=0`.
   The inputs can have any `w`, so we needed `d_allowed_leq_general`.

3. `d_allowed_leq_general_c` was the borrow-carrying helper to make
   `d_allowed_leq_general` inductive (same pattern as `d_allowed_leq`).

4. The bilinear inequality `v1*d2 + v2*d1 + d1*d2 <= v1*x2 + v2*x1 + x1*x2`
   followed directly from `lemma_mul_upper_bound` in Verus's arithmetic library.

### Fuzz testing

`fuzz_eun_mul` tests soundness at 64-bit width: 1,000,000 pairs × 8 concrete
samples each = 8,000,000 checks, all passing.


## Formal proof

### The soundness theorem

The central theorem, proved in Verus with zero admits:

```
forall c1 c2: u1.has(c1) && u2.has(c2) ==> u1.plus_un(u2).has(c1 + c2)
```

where `has` is defined recursively on the bitstring with borrow tracking,
and `plus_un` computes `v = v1 + v2`, `x = x1 + x2`,
`w = (w1 & w2) & ~lsh(cout_c(x1, x2))`.

### The membership predicate: d_allowed with borrow tracking

Membership checking works like hardware subtraction. For each bitfield, we
subtract d from x one bit at a time, tracking a borrow bit. At each field
boundary (leader bit), we check that the previous field's subtraction didn't
underflow. If it did, d exceeded x in that field, and the value is rejected.

Formally, the predicate `d_allowed(w, x, d, borrow, first)` recurses on
the bitstring. There are two base cases: if `w`, `x`, and `d` are all zero,
the value is accepted iff the borrow is zero (no outstanding debt); if `w`
and `x` are zero but `d` is nonzero, the value is rejected (d has bits but
no field capacity left). In the recursive case:

1. If this is a leader bit (`w[0]=1`) and not the first bit and the borrow
   is nonzero, the previous field overflowed; return false.
2. Compute the subtraction `x[0] - d[0] - borrow`. If negative, set the
   new borrow to 1.
3. Recurse on the tails with `first=false`.

### The invariant: cd + br <= cx + b1 + b2

The core inductive proof tracks five bits of state at each bit position:

- `b1`: borrow in x1 - d1 (membership check for input u1)
- `b2`: borrow in x2 - d2 (membership check for input u2)
- `cd`: carry in d1 + d2 (concrete value addition)
- `cx`: carry in x1 + x2 (max value addition / carry-out)
- `br`: borrow in x12 - (d1+d2) (membership check for result)

The invariant is:

```
cd + br <= cx + b1 + b2
```

Interpretation: the total "debt" (carry in the d-sum plus the result borrow)
is bounded by the total "credit" (carry in the x-sum plus the input borrows).

At a surviving boundary (`w_result[i] = 1`), we know:
- `cx = 0` (no carry crossed this boundary, otherwise it would be destroyed)
- `b1 = 0` and `b2 = 0` (both input fields were ok, otherwise their
  `d_allowed` would have returned false at this leader)

The invariant then gives `cd + br <= 0`, forcing `cd = 0` and `br = 0`.
The result borrow is zero, so the leader check passes.

### How we discovered the invariant

We used brute-force simulation to enumerate the state machine.

Step 1: enumerate reachable states. Starting from `(0,0,0,0,0)`, we
applied all possible bit combinations `(x1h, d1h, x2h, d2h)` in `{0,1}^4`
and computed the transition. This produced 20 reachable states out of 32
possible.

Step 2: search for linear invariants. We tested all inequalities of the
form `a*b1 + b*b2 + c*cd + d*cx + e*br <= k` for coefficients in `{-1,0,1}`
and `k` in `{0,1,2}`. For each candidate, we checked:
1. Does it hold for all 20 reachable states?
2. Is it preserved by all transitions (from states satisfying the invariant)?
3. Does it imply `br = 0` when `cx = 0, b1 = 0, b2 = 0`?

Exactly one invariant passed all three checks: `-b1 - b2 + cd - cx + br <= 0`,
equivalently `cd + br <= cx + b1 + b2`.

Step 3: verify preservation. We checked all 512 transitions (32 states x
16 bit combinations) and confirmed zero violations.

### Proof structure

The proof consists of 13 key lemmas, all verified with zero admits (Verus reports 20 total verified obligations including internal assertions):

| Lemma | What it proves |
|-------|---------------|
| `plus_sound` | The top-level soundness theorem |
| `d_allowed_plus` | Reduces to `d_allowed_plus_c` with initial state (all carries/borrows zero) |
| `d_allowed_plus_c` | Core induction: invariant + recursion + connection |
| `connect_ih` | Links IH on tails to full result via monotonicity |
| `inv_step` | Invariant `cd+br <= cx+b1+b2` preserved per bit (Z3 case analysis on 5 booleans) |
| `tw_leq_wtail` | `tl(w) <= w_tail` bitwise (the monotonicity bridge) |
| `tw_eq` | `tl(w) = (tl(w1)&tl(w2)) & ~co` (bitwise decomposition via `bit_tl`) |
| `nbr_implies_no_leader` | `nbr=T => tl(w)[0]=0` (boundary destroyed when result borrow is set) |
| `d_allowed_first_equiv` | `d_allowed(w,x,d,br,true) => d_allowed(w,x,d,br,false)` when `br=F` or `hd(w)=F` |
| `d_allowed_mono` | Fewer boundaries => easier to satisfy (induction on bitstring) |
| `d_allowed_leq` | `d_allowed(0,x,d,br,_) => d+br<=x` (single-field: borrow-tracking subtraction) |
| `to_an_sound_single` | `Un{w=0}.has(n) => Un{w=0}.to_an().has(n)` (single-field Unum->Anum) |
| `cout_c_overflow` | `bit(cout_nat(a,b), i) <==> chop(a,i+1) + chop(b,i+1) >= 2^(i+1)` |

### The tl(w) vs w_tail mismatch

The hardest part of the proof was connecting the inductive hypothesis (which
operates on tails) to the full result. The issue:

- `tl(w) = (tl(w1) & tl(w2)) & ~cout_c(x1, x2, cx)` (the actual tail)
- `w_tail = (tl(w1) & tl(w2)) & ~lsh(cout_c(tl(x1), tl(x2), ncx))` (what the IH gives)

These differ at bit 0: `tl(w)` uses `~ncx` while `w_tail` uses `~F`.
When `ncx = T`, `tl(w)` has bit 0 cleared (boundary destroyed) while
`w_tail` might have it set.

The solution uses three lemmas:
1. Monotonicity (`d_allowed_mono`): `tl(w) <= w_tail` bitwise, so
   `d_allowed(w_tail,...) => d_allowed(tl(w),...)`.
2. No-leader (`nbr_implies_no_leader`): when `nbr = T`, `tl(w)[0] = 0`
   (either `ncx = T` destroys the boundary, or `nb1/nb2 = T` means the
   input's `d_allowed` would have failed at this leader).
3. First-equiv (`d_allowed_first_equiv`): `d_allowed(w,x,d,br,true) =>
   d_allowed(w,x,d,br,false)` when `br = F` or `hd(w) = F`.


## Implementation status

The full crate verifies with 768 proofs and zero admits. The general
multi-field addition soundness theorem is proved without any axioms or
assumptions. Multiplication soundness is proved via bilinear expansion.
Exhaustive 4-bit testing confirms zero unsound cases across 1,183,744 pairs,
and 30 fuzz tests at 64-bit width all pass (16 Unum-specific plus 14 for the
existing domains). The executable implementation lives in `abstract-domains/src/domains.rs`
as `EUn`, with the corrected carry-out `w` formula, `ones_mask`-based
`to_ean`, carry-aware `to_etn`, and bilinear `mul`. It is integrated into the
TAIU reduced product (Tnum x Anum x Interval x Unum).
