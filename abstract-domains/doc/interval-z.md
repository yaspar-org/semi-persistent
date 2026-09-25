# IntervalZ

Unbounded integer intervals, in [src/ibig.rs](../src/ibig.rs) and [src/interval_z.rs](../src/interval_z.rs).

```text
Bound     = NegInf | Fin(IBig) | PosInf
IntervalZ = { empty, lo: Bound, hi: Bound }
values    = every integer z with lo <= z <= hi
```

`empty` has no values. A well-formed nonempty interval has `lo <= hi`. 

## 1. Integers (`IBig`)

`IBig` is the finite endpoint. The payload is `num_bigint::BigInt`. The spec view is mathematical `int`, so endpoint arithmetic does not wrap.

## 2. Endpoints (`Bound`)

`le`, `eq_bound`, `min`, and `max` follow `bound_le` and `bound_eq`.

Interval add, neg, mul, and div call these endpoint operations.


| Operation | Implementation                                                                                                                                                                                     | Verified                       |
| --------- | -------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | ------------------------------ |
| `add`     | `Fin + Fin` is the exact sum. A `−∞` summand yields `−∞`, and a `+∞` summand yields `+∞`. The two opposite pairs are fixed first: `−∞ + +∞ = −∞`, `+∞ + −∞ = +∞`                                   | result equals `add_bound_spec` |
| `neg`     | `−∞` and `+∞` swap. `Fin(n)` becomes `Fin(−n)`                                                                                                                                                     | result equals `neg_bound_spec` |
| `ext_mul` | `Fin * Fin` is the exact product. `0 * ±∞ = 0`. A positive finite endpoint keeps the sign of an infinity; a negative one flips it. Same-sign infinities yield `+∞`; opposite infinities yield `−∞` | result equals `ext_mul_spec`   |
| `ext_div` | a zero `Fin` divisor returns `None`. A finite dividend over `±∞` is `0`. `±∞ / ±∞` uses the sign rule above. `Fin / Fin` is the Euclidean quotient                                                 | result equals `ext_div_spec`   |


## 3. Intervals

`bottom` is `empty` with dummy endpoints `Fin(0)`. `top` is `[−∞, +∞]`. `constant(n)` is the singleton `[n, n]`.


| Operation  | Implementation                                           | Verified                                                                |
| ---------- | -------------------------------------------------------- | ----------------------------------------------------------------------- |
| `bottom`   | `empty = true`                                           | well-formed, equals `bottom_spec`, and `has` is false for every integer |
| `top`      | `[−∞, +∞]`                                               | well-formed, equals `top_spec`, and `has` is true for every integer     |
| `constant` | both endpoints `Fin(n)`                                  | well-formed, nonempty, and contains `n`                                 |
| `range`    | keep the bounds when they are ordered; otherwise bottom  | well-formed, and the postcondition in the paragraph above               |
| `arith`    | the same test; failure is top                            | well-formed, equals `arith_spec`                                        |
| `contains` | compare the integer with both endpoints; false on bottom | matches `has`                                                           |


## 4. Lattice


| Operation | Verified                                                                                        |
| --------- | ----------------------------------------------------------------------------------------------- |
| `meet`    | well-formed; equals `meet_spec` up to `eq_abs`; `has` is exactly the intersection               |
| `join`    | well-formed; equals `join_spec` up to `eq_abs`; every value of either argument is in the result |


Lattice laws, included in the verification count:


| Theorem                                                                 | Statement                       |
| ----------------------------------------------------------------------- | ------------------------------- |
| `meet_comm`, `meet_idempotent`, `meet_assoc`, `meet_top`, `meet_bottom` | laws of `meet_spec`             |
| `join_comm`, `join_idempotent`, `join_assoc`, `join_top`, `join_bottom` | laws of `join_spec`             |
| `meet_monotone`                                                         | `a ⊑ b` implies `a ⊓ c ⊑ b ⊓ c` |
| `join_monotone`                                                         | `a ⊑ b` implies `a ⊔ c ⊑ b ⊔ c` |


## 5. Arithmetic


| Operation | Implementation                                          | Verified                                                                                               |
| --------- | ------------------------------------------------------- | ------------------------------------------------------------------------------------------------------ |
| `add`     | `arith(lo + lo, hi + hi)`                               | equals `add_spec`; every concrete `x + y` is in the result                                             |
| `neg`     | `arith(−hi, −lo)`                                       | equals `neg_spec`; every concrete `−x` is in the result                                                |
| `sub`     | `add` of `neg` on the subtrahend                        | equals `sub_spec`; every concrete `x − y` is in the result                                             |
| `mul`     | min and max of the four `ext_mul` corners, then `arith` | equals `mul_spec`; every concrete product is in the result, including unbounded endpoints and `0 * ±∞` |


Monotonicity has the same shape for each of these: if `a ⊑ b` and the other operand stays fixed, the result on `a` refines the result on `b`.

## 6. Division and alarms

`Alarm` is the set of possible error bits, not a severity.


| Alarm           | Concrete error bit |                                                  |
| --------------- | ------------------ | ------------------------------------------------ |
| `NoError`       | `{false}`          | the divisor contains no zero                     |
| `DefiniteError` | `{true}`           | the divisor is exactly `{0}`                     |
| `MaybeError`    | `{false, true}`    | the divisor contains zero and some other integer |


`div_one` is division by an interval that is not split. It takes the min and max of the four `ext_div` corners when every corner is `Some`. Any `None` (a zero endpoint) makes `div_one` return top. Verified: the result equals `div_one_spec`, and if the divisor contains no zero then every concrete Euclidean quotient is in the result.

`div(a, d)` then classifies the divisor:

1. Either argument is empty: bottom, `NoError`.
2. `d` is the singleton `{0}`: bottom, `DefiniteError`.
3. `d` contains `0`: meet `d` with `(−∞, −1]` and with `[1, +∞)`, run `div_one` on each side, and join the quotients. Alarm `MaybeError`.
4. Otherwise: `div_one(a, d)`, alarm `NoError`.

Verified for `div`: the value equals `div_spec` up to `eq_abs`, the alarm equals `div_spec`, every quotient by a nonzero concrete divisor is in the value, and `y == 0` is an element of the alarm exactly when a concrete pair has that error bit.

## 7. Widen, narrow, and fuel


| Operation | Implementation                                                                                                                                 | Verified                                                                                                  |
| --------- | ---------------------------------------------------------------------------------------------------------------------------------------------- | --------------------------------------------------------------------------------------------------------- |
| `widen`   | loop over the four endpoints of both arguments and keep the least lower bound and greatest upper bound. An empty argument is ignored           | equals the convex hull (`join`); both arguments refine the result, and so does their join                 |
| `narrow`  | an infinite endpoint is replaced by the other argument's endpoint; a crossed result is bottom                                                  | equals `narrow_spec` up to `eq_abs`; the result refines the first argument, and `meet` refines the result |
| `refine`  | fuel `0` keeps the value and returns fuel `0`. A meet that changes the value spends `1`. A meet that leaves the value unchanged spends nothing | the pair matches `refine_value` and `refine_fuel`; the value refines the start                            |


## 8. Guards


| Operation        | Implementation                                     | Verified                                                            |
| ---------------- | -------------------------------------------------- | ------------------------------------------------------------------- |
| `within(lo, hi)` | both endpoints lie inside `[lo, hi]`               | a true result means every concrete value is inside that `i64` range |
| `nonzero`        | the interval does not contain `0`                  | a true result means no concrete value is `0`                        |
| `nonneg`         | the lower bound is `>= 0`, which accepts `[0, +∞)` | a true result means every concrete value is `>= 0`                  |
| `fits_u8`        | `within(0, 255)`                                   | a true result means every concrete value is in `0..=255`            |


## 9. Verification result

Checked on 2026-09-23 with Verus `0.2026.08.02.b677dd5` and `vstd = 0.0.0-2026-08-02-0125`:

```text
cargo verus verify -p semi-persistent-abstract-domains -- --verify-only-module ibig --verify-only-module interval_z --rlimit 50
173 verified, 0 errors
```

```text
cargo test -p semi-persistent-abstract-domains --test interval_z --offline
22 passed, 0 failed
```

