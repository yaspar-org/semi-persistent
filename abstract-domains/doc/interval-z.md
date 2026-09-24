# IntervalZ

Unbounded integer intervals, in [src/ibig.rs](../src/ibig.rs) and
[src/interval_z.rs](../src/interval_z.rs). Shifts and bitwise transfers stay
on the machine-word `Interval`.

Each section below states the representation or the operation, how the
executable code computes it, and what Verus proves. The run that checks all
of those contracts is at the end.

```text
Bound     = NegInf | Fin(IBig) | PosInf
IntervalZ = { empty, lo: Bound, hi: Bound }
values    = every integer z with lo <= z <= hi
```

`empty` has no values. A well-formed nonempty interval has `lo <= hi`, a
lower bound other than `+∞`, and an upper bound other than `−∞`. `refines`
(`⊑`) means every concrete value on the left is a concrete value on the
right. `eq_abs` identifies two empty intervals, and two nonempty intervals
whose endpoints have equal `view`s.

## 1. Integers (`IBig`)

`IBig` is the finite endpoint. The payload is `num_bigint::BigInt`. The spec
view is mathematical `int`, so endpoint arithmetic does not wrap, including
past `i64`.

| Operation | Implementation | Verified |
| --- | --- | --- |
| `from_i64`, `zero`, `clone_ibig` | `BigInt` constructors | `view()` is that integer, and the value is `from_int` of its view |
| `add`, `mul`, `neg` | `BigInt` `+`, `*`, unary `-` | `view()` is `+`, `*`, `-` on `int` |
| `div_euclid` | truncating `BigInt` `/` and `%`; if the remainder is negative, step the quotient so the remainder is nonnegative | nonzero divisor; `view()` is Verus `int /` (same quotient as Rust `div_euclid`) |
| `le`, `lt`, `eq_int`, `is_zero`, `is_neg`, `is_pos` | `BigInt` order and `Sign` | the `bool` matches the comparison on `view()` |

`IBig` is `external_body`. The proofs trust each `ensures` above and two
broadcast axioms: `from_int(n).view() == n`, and every value equals
`from_int` of its view.

## 2. Endpoints (`Bound`)

`le`, `eq_bound`, `min`, and `max` follow `bound_le` and `bound_eq`. `−∞`
is `<=` every bound, every bound is `<= +∞`, and two `Fin` values compare
by `view()`.

`bound_le` is reflexive, total, and antisymmetric: equal `Fin` views are the
same `Bound`, by the surjectivity axiom. `min` and `max` commute.

Interval add, neg, mul, and div call these endpoint operations, then wrap
the resulting bounds.

| Operation | Implementation | Verified |
| --- | --- | --- |
| `add` | `Fin + Fin` is the exact sum. A `−∞` summand yields `−∞`, and a `+∞` summand yields `+∞`. The two opposite pairs are fixed first: `−∞ + +∞ = −∞`, `+∞ + −∞ = +∞` | result equals `add_bound_spec` |
| `neg` | `−∞` and `+∞` swap. `Fin(n)` becomes `Fin(−n)` | result equals `neg_bound_spec` |
| `ext_mul` | `Fin * Fin` is the exact product. `0 * ±∞ = 0`. A positive finite endpoint keeps the sign of an infinity; a negative one flips it. Same-sign infinities yield `+∞`; opposite infinities yield `−∞` | result equals `ext_mul_spec` |
| `ext_div` | a zero `Fin` divisor returns `None`. A finite dividend over `±∞` is `0`. `±∞ / ±∞` uses the sign rule above. `Fin / Fin` is the Euclidean quotient | result equals `ext_div_spec` |

## 3. Intervals

`bottom` is `empty` with dummy endpoints `Fin(0)`. `top` is `[−∞, +∞]`.
`constant(n)` is the singleton `[n, n]`.

`range(lo, hi)` returns that interval when `lo <= hi`, the lower bound is
not `+∞`, and the upper bound is not `−∞`. Otherwise it returns bottom.
`arith(lo, hi)` uses the same test and returns top on failure. Products and
quotients are built with `arith`, so an unordered corner set becomes top,
which still contains every integer.

| Operation | Implementation | Verified |
| --- | --- | --- |
| `bottom` | `empty = true` | well-formed, equals `bottom_spec`, and `has` is false for every integer |
| `top` | `[−∞, +∞]` | well-formed, equals `top_spec`, and `has` is true for every integer |
| `constant` | both endpoints `Fin(n)` | well-formed, nonempty, and contains `n` |
| `range` | keep the bounds when they are ordered; otherwise bottom | well-formed, and the postcondition in the paragraph above |
| `arith` | the same test; failure is top | well-formed, equals `arith_spec` |
| `contains` | compare the integer with both endpoints; false on bottom | matches `has` |

## 4. Lattice

`meet` takes the max of the lower bounds and the min of the upper bounds.
If either argument is empty, or the resulting bounds are crossed, or the
lower bound is `+∞`, or the upper bound is `−∞`, the result is bottom.

`join` takes the min of the lower bounds and the max of the upper bounds.
An empty argument is dropped. Joining two nonempty intervals is their convex
hull.

| Operation | Verified |
| --- | --- |
| `meet` | well-formed; equals `meet_spec` up to `eq_abs`; `has` is exactly the intersection |
| `join` | well-formed; equals `join_spec` up to `eq_abs`; every value of either argument is in the result |

Lattice laws, included in the verification count:

| Theorem | Statement |
| --- | --- |
| `meet_comm`, `meet_idempotent`, `meet_assoc`, `meet_top`, `meet_bottom` | laws of `meet_spec` |
| `join_comm`, `join_idempotent`, `join_assoc`, `join_top`, `join_bottom` | laws of `join_spec` |
| `meet_monotone` | `a ⊑ b` implies `a ⊓ c ⊑ b ⊓ c` |
| `join_monotone` | `a ⊑ b` implies `a ⊔ c ⊑ b ⊔ c` |

## 5. Arithmetic

An empty argument makes `add`, `neg`, `sub`, and `mul` return bottom.
Otherwise the result is `arith` of the endpoint formula.

| Operation | Implementation | Verified |
| --- | --- | --- |
| `add` | `arith(lo + lo, hi + hi)` | equals `add_spec`; every concrete `x + y` is in the result |
| `neg` | `arith(−hi, −lo)` | equals `neg_spec`; every concrete `−x` is in the result |
| `sub` | `add` of `neg` on the subtrahend | equals `sub_spec`; every concrete `x − y` is in the result |
| `mul` | min and max of the four `ext_mul` corners, then `arith` | equals `mul_spec`; every concrete product is in the result, including unbounded endpoints and `0 * ±∞` |

Monotonicity has the same shape for each of these: if `a ⊑ b` and the other
operand stays fixed, the result on `a` refines the result on `b`. For `neg`
there is only one argument. `sub` is `add` after `neg`, and its proof is
that composition.

## 6. Division and alarms

`Alarm` is the set of possible error bits, not a severity.

| Alarm | Concrete error bit | |
| --- | --- | --- |
| `NoError` | `{false}` | the divisor contains no zero |
| `DefiniteError` | `{true}` | the divisor is exactly `{0}` |
| `MaybeError` | `{false, true}` | the divisor contains zero and some other integer |

`join` of `NoError` and `DefiniteError` is `MaybeError`. That fact is proved
(`alarm_join_safe_and_definite_is_maybe`), and `Alarm::join` matches
`join_spec` and contains every error bit of either argument.

`div_one` is division by an interval that is not split. It takes the min and
max of the four `ext_div` corners when every corner is `Some`. Any `None`
(a zero endpoint) makes `div_one` return top. Verified: the result equals
`div_one_spec`, and if the divisor contains no zero then every concrete
Euclidean quotient is in the result.

`div(a, d)` then classifies the divisor:

1. Either argument is empty: bottom, `NoError`.
2. `d` is the singleton `{0}`: bottom, `DefiniteError`.
3. `d` contains `0`: meet `d` with `(−∞, −1]` and with `[1, +∞)`, run `div_one` on each side, and join the quotients. Alarm `MaybeError`.
4. Otherwise: `div_one(a, d)`, alarm `NoError`.

Example of step 4: `[-8, -1] / [-4, -2] = [1, 4]`, because
`(-1).div_euclid(-4) == 1`.

Verified for `div`: the value equals `div_spec` up to `eq_abs`, the alarm
equals `div_spec`, every quotient by a nonzero concrete divisor is in the
value, and `y == 0` is an element of the alarm exactly when a concrete pair
has that error bit.

`div_monotone`: if the dividend gets tighter and the divisor stays fixed,
the quotient gets tighter. A divisor that contains zero is split into the
two rays; each ray excludes zero, so each side uses the `div_one`
monotonicity lemma, and the two joins are chained.

## 7. Widen, narrow, and fuel

These are the iteration operators. Widen grows, narrow shrinks, and `refine`
spends fuel on a descending meet.

| Operation | Implementation | Verified |
| --- | --- | --- |
| `widen` | if the right lower bound moved down, the result lower bound is `−∞`; if the right upper bound moved up, the result upper bound is `+∞`. An empty argument is ignored | equals `widen_spec` up to `eq_abs`; both arguments refine the result, and so does their join |
| `narrow` | an infinite endpoint is replaced by the other argument's endpoint; a crossed result is bottom | equals `narrow_spec` up to `eq_abs`; the result refines the first argument, and `meet` refines the result |
| `refine` | fuel `0` keeps the value and returns fuel `0`. A meet that changes the value spends `1`. A meet that leaves the value unchanged spends nothing | the pair matches `refine_value` and `refine_fuel`; the value refines the start |

`meet_chain_sound` iterates that rule along a sequence of facts. The result
is well-formed and refines the start. Fuel `0` returns the start unchanged.
Stopping early is sound for the same reason: the current value still refines
the start.

`widen` is proved sound for the three refinement facts in the table. It has
no monotonicity theorem: sending an unstable endpoint to `±∞` is not
monotone. `narrow` is proved for the two facts in the table and has no
monotonicity theorem.

## 8. Guards

A guard returns true only when every concrete value satisfies the predicate.
Bottom returns false, so bottom does not license the guard.

| Operation | Implementation | Verified |
| --- | --- | --- |
| `within(lo, hi)` | both endpoints lie inside `[lo, hi]` | a true result means every concrete value is inside that `i64` range |
| `nonzero` | the interval does not contain `0` | a true result means no concrete value is `0` |
| `nonneg` | the lower bound is `>= 0`, which accepts `[0, +∞)` | a true result means every concrete value is `>= 0` |
| `fits_u8` | `within(0, 255)` | a true result means every concrete value is in `0..=255` |

## 9. UBig and `IntervalR`

UBig is the same `IntervalZ`. `wf_ubig` is `wf` together with `empty` or
`lo >= 0`. `check_ubig` is that test, and it is proved equal to `wf_ubig`.
Bottom passes. A negative lower bound fails.

`IntervalR` is the same bounds with `lo_closed` and `hi_closed`. Infinities
are never closed: `new` forces a `−∞` lower bound open and a `+∞` upper
bound open. A crossed pair, a `+∞` lower bound, a `−∞` upper bound, or a
shared endpoint that is open on either side becomes bottom. Otherwise the
interval keeps the adjusted flags.

| Operation | Implementation | Verified |
| --- | --- | --- |
| `IntervalR::bottom` | `empty`, closed dummy endpoints `Fin(0)` | well-formed, equals `interval_r_bottom`, and contains no integer |
| `IntervalR::new` | adjust the closed flags, then the test in the paragraph above | well-formed, equals `interval_r_new_spec` |
| `contains_int` | an open finite endpoint uses a strict inequality | matches `has_int` |
| `meet` | the tighter lower bound and the tighter upper bound; a shared endpoint stays closed only when both sides include it | well-formed; every integer that belongs to both arguments belongs to the meet |

## 10. Verification result

Checked on 2026-09-23 with Verus `0.2026.08.02.b677dd5` and
`vstd = 0.0.0-2026-08-02-0125`:

```text
cargo verus verify -p semi-persistent-abstract-domains -- --verify-only-module ibig --verify-only-module interval_z --rlimit 50
168 verified, 0 errors
```

```text
cargo test -p semi-persistent-abstract-domains --test interval_z --offline
22 passed, 0 failed
```

The 168 is this pair of modules. The crate-wide 994 does not include them.
Neither module contains `admit()` or `assume()`. Ordinary `cargo test`
erases proofs; the 168 is the Verus run. Pinned `vstd` lemmas, the `IBig`
axioms, and the `external_body` ensures are the trust boundary.

[tests/interval_z.rs](../tests/interval_z.rs) checks the executable side of
the contracts above, in the same order: bottom and top, meet and join and
their lattice laws, containment of add, neg, sub, and mul, alarm join,
division alarms and `nonzero`, `within` and `nonneg`, widen to infinity and
narrow, fuel exhaustion and a stable meet that spends nothing, a sum past
`i64` that stays finite, `div_euclid` against `i64`, UBig's nonnegative
lower bound, an open `IntervalR` endpoint excluding that integer, and the
unbounded cases `[1, +∞) * [2, 3] = [2, +∞)`,
`[−∞, −1] * [2, 3] = [−∞, −2]`, and `[2, 10] / [1, +∞) = [0, 10]` with
`NoError`.
