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

`ExecUnum::add` is proved once for every `W: BitWord`. It uses the
field formula only when the bases, extents, represented upper bounds, and
their sum do not wrap. Otherwise it returns `top`.

Its Verus postcondition universally quantifies over machine values:

```text
self.has(x) && other.has(y)
    ==> result.has(W::from_int(x.view() + y.view()))
```

The proof connects the word operations to `ChoppedUnum` and the unbounded
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
- `ExecUnum::from_ean` gives every bit its own field. Its containment
  postcondition follows from `Unum::submask_admitted`: an offset whose bits are
  bits of the extent is admitted whatever the walls.
- `ExecUnum::to_ean` widens the whole extent to the next all-ones mask. Its
  containment postcondition follows from `Unum::to_anum_sound`, which holds for
  any walls, since every admitted offset is at most the extent.
- `ExecUnum::to_etn` is `ExecAnum::to_etn` of that Anum, and inherits its
  containment postcondition.

## Negation and Subtraction

`ExecUnum::neg` maps `v + d` to `(-v - x) + (x - d)`. Within each field the
complement `x_f - d_f` stays in `[0, x_f]`, and the subtraction `x - d` borrows
at the same bits as `d`'s admission, so `Unum::complement_admitted` proves that
`x - d` is admitted with the same walls and extent. The result keeps the walls
when `0 < v` and `v + x < 2^W`; it is `{0}` for `{0}`, and top when the range
wraps or holds 0 with something else. `ExecUnum::sub` adds the negation; both
have universal containment postconditions.

## Reduced Product

Unum would combine with other domains through `reduce::Product` and the fact
record `Facts<W>` (see [`reduced-product.md`](reduced-product.md)), but it does
not implement `Domain` or `Refine` yet. The hand-written `ReducedProduct` of
Tnum, Anum, Interval and Unum, whose `reduce` rebuilt the Unum from the
interval, was removed in #123.

`ExecUnum` cannot implement `Canonical` as it stands: several encodings denote
the same set. At 4 bits, `walls = 0b0001` and `walls = 0b0101`, both with
`extent = 0b0011`, denote `{0, 1, 2, 3}`; the second splits off a field whose
maximum is 0. So `==` on two values does not decide equality of their sets,
and a Unum cannot be a field of a stored fact record until a canonical form is
defined and a `normalize` is proved to reach it.

## Established and Open Claims

Machine-checked:

- carry-out formula equivalence and prefix-overflow characterization;
- unbounded addition and multiplication containment;
- chopped add/mul containment under their explicit no-overflow conditions;
  and
- executable containment for every `ExecUnum` operation (`constant`, `top`,
  `add`, `neg`, `sub`, `mul`, `from_interval`, `from_ean`, `to_ean`,
  `to_etn`), proved once for every `W: BitWord`.

Not machine-checked:

- a canonical form for Unums, and a `normalize` that reaches it;
- exactness of addition on a defined canonical representation subset;
- abstract associativity or commutativity as structural equality;
- the precision of `add`, measured as the share of sampled results that are
  the smallest Unum containing the concrete sums; and
- any claim that TAIU is an optimal reduced product.

The current verification counts and mirror-test command are recorded in
[`proof-status.md`](proof-status.md).
