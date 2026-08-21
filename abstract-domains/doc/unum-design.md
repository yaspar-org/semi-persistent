# Unums: Horizontally Composable Additive Tristate Numbers

This chapter describes the implemented Unum representation and separates its
proved containment properties from precision properties that remain open.

## Motivation

The executable reduced product combines four complementary abstractions:

- Tnums track independent known and unknown bits.
- Anums track a base plus independently selectable offset bits.
- Intervals track a contiguous unsigned range.
- Unums track a base plus independently bounded bit-field offsets.

Tnums preserve bit-level structure but often widen around carries. Intervals
handle monotone unsigned arithmetic well but cannot retain independent packed
fields. Unums retain selected field boundaries across addition when no extent
carry crosses those boundaries.

These domains are not totally ordered by precision. For example, a Tnum can
represent `{0,4}` exactly, while a single-field Unum containing both endpoints
also contains `1`, `2`, and `3`. A Unum can represent independent contiguous
field ranges that neither one Tnum nor one interval represents exactly.

## Representation

An unbounded Unum is:

```text
Unum { base, walls, extent }
```

Membership is defined by `Unum::has` and the recursive
`field_admits(walls, extent, offset, borrow, first)` predicate. A represented
value has the form `base + offset`. At every wall after the first bit,
borrow-tracking checks that the offset for the preceding field did not exceed
that field's extent.

`walls` marks field starts. Bit zero is treated as an implicit start by the
`first` parameter, so both zero and one at `walls[0]` are accepted. With
`walls == 0`, membership is exactly:

```text
base <= value <= base + extent
```

The executable `ExecUnum` deliberately has no `wf` predicate. Arbitrary
`base`, `walls`, and `extent` words therefore have defined membership
semantics; the API does not enforce a unique or tight encoding. Documentation
must not assume that all executable values satisfy a hidden canonical-form
invariant.

## Addition

For unbounded naturals, addition computes:

```text
result.base   = base1 + base2
result.extent = extent1 + extent2
cout = (extent1 & extent2) | ((extent1 | extent2) & ~(extent1 + extent2))
result.walls  = (walls1 & walls2) & ~(cout << 1)
```

A wall survives only when both operands have it and no carry from the extent
sum crosses it. `Unum::carry_out_formula` proves that the broadword expression
equals the recursive carry register. `carry_out_c_overflow` relates each carry
bit to overflow of the corresponding low-bit prefixes.

`Unum::add_sound` proves:

```text
u1.has(x) && u2.has(y) ==> u1.add(u2).has(x + y)
```

The core induction maintains:

```text
concrete_carry + result_borrow
    <= extent_carry + left_borrow + right_borrow
```

At a surviving wall, the extent carry and both input borrows are zero, forcing
the result borrow to zero.

### Precision scope

There is no `plus_precise` theorem and no theorem that abstract addition is
associative. More importantly, exactness is false for all accepted encodings.
At four bits, consider:

```text
zero = Unum { base: 0, walls: 0b0000, extent: 0b0000 }
gaps = Unum { base: 0, walls: 0b1111, extent: 0b0010 }
```

`zero` denotes `{0}` and `gaps` denotes `{0,2}`. Their sum formula intersects
the wall masks, producing `walls = 0` and `extent = 2`, which denotes
`{0,1,2}`. This is a sound widening, not an exact sum.

The executable `from_interval([0,0])` can produce the `zero` encoding above,
so this is not merely an unreachable struct literal. Exactness under a
specified canonical subset may be a useful future theorem, but that subset
and its preservation obligations are not currently formalized.

The Rust mirror suite samples commuted and reassociated additions, but its
current structural-property tests establish containment of sampled concrete
sums only. They do not prove equality of abstract results.

## Fixed-Width Addition

`ExecUnum::add` is generated for `u8`, `u16`, `u32`, and `u64`. It uses the
field formula only when the bases, extents, represented upper bounds, and
their sum do not wrap. Otherwise it returns `top`.

Its Verus postcondition universally quantifies over machine values:

```text
self.has(x) && other.has(y)
    ==> result.has(x.wrapping_add(y))
```

The proof connects the native operations to `ChoppedUnum` and the unbounded
containment theorem. This is a soundness result; overflow-to-top and
noncanonical wall masks prevent an unconditional fixed-width precision claim.

## Multiplication

Unbounded multiplication uses a single-field bilinear bound:

```text
result.base = base1 * base2
result.walls = 0
result.extent =
    base1 * extent2 + base2 * extent1 + extent1 * extent2
```

For represented values `base1 + d1` and `base2 + d2`, membership gives
`d1 <= extent1` and `d2 <= extent2`. Expanding the concrete product bounds
its offset from `base1 * base2` by `result.extent`.
`Unum::mul_sound` proves the resulting containment.

`ExecUnum::mul` checks every represented-bound product and sum used by this
construction. If any check fails it returns `top`; otherwise its universal
postcondition contains every wrapping product represented by the operands.
The result has one field and is generally an overapproximation, not an exact
product set.

## Conversions

The implemented conversions have different proof status:

- `ExecUnum::from_interval` creates one field and has a universal containment
  postcondition.
- `ExecUnum::from_ean` gives every bit its own field. It has mirror-test
  coverage but no Layer-4 containment postcondition.
- `ExecUnum::to_ean` widens the whole extent to the next all-ones mask. It has
  mirror-test coverage but no Layer-4 containment postcondition.
- `ExecUnum::to_etn` goes through that Anum and guarantees only Tnum
  well-formedness at Layer 4.
- The unbounded `Unum::to_anum_sound` theorem applies only when `walls == 0`.

Consequently, conversion soundness must not be generalized beyond this
inventory until the missing executable postconditions are added.

## Reduced Product

`ReducedProduct` contains a Tnum, Anum, Interval, and Unum. Addition computes
all four component transfers and then calls `reduce`; this entire operation
has a universal containment theorem.

Bitwise operations preserve only the Tnum result and set the other components
to top before reduction. Other arithmetic operations call available component
implementations, but most currently guarantee only well-formed results at
Layer 4. The exact operation inventory is maintained in
[`proof-status.md`](proof-status.md).

`reduce` narrows interval bounds from all components, narrows Tnum and Anum
using the resulting upper bound, and rebuilds the Unum from the interval. Its
universal theorem says that no value in the input product intersection is
removed. Rebuilding from an interval can discard field structure, so reduction
is not a precision-preservation theorem for any individual component.

## Established and Open Claims

Machine-checked:

- carry-out formula equivalence and prefix-overflow characterization;
- unbounded addition and multiplication containment;
- chopped add/mul containment under their explicit no-overflow conditions;
- executable `top`, `add`, `from_interval`, and `mul` containment at the four
  enabled widths; and
- reduced-product `reduce` and `add` containment.

Not machine-checked:

- exactness of addition on a defined canonical representation subset;
- abstract associativity or commutativity as structural equality;
- Layer-4 containment for the remaining conversions and Unum operations; and
- any claim that TAIU is an optimal reduced product.

The current verification counts and mirror-test command are recorded in
[`proof-status.md`](proof-status.md).
