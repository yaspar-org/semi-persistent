# IntervalZ

Unbounded integer intervals, in [src/ibig.rs](../src/ibig.rs) and [src/interval_z.rs](../src/interval_z.rs). The shape is the shared domain interface in [domain-traits.md](domain-traits.md).

```text
Lo        = NegInf | Fin(IBig)
Hi        = Fin(IBig) | PosInf
IntervalZ = { lo: Lo, hi: Hi }     private fields, lo <= hi when both are finite
values    = every integer z with lo <= z <= hi
empty     = BotOr::Bot, outside the type
```

There is no `empty` flag. A well-formed value is nonempty, and each set has one representation.

## Integers (`IBig`)

`IBig` is a trusted wrapper around `num_bigint::BigInt`. Its spec view is mathematical `int`. The trusted items, including `sub`, `mul`, `div_euclid`, and `div_trunc`, are listed in the ledger in [domain-traits.md](domain-traits.md). `div_euclid` is Verus `int` `/` (nonnegative remainder). `div_trunc` divides toward zero. This module is not verified code.

## Domain

`Domain` provides `top` (`[-∞, +∞]`), `leq`, `join`, `meet -> BotOr`, and Cousot `widen`. An unstable bound jumps to `±∞`, so the chain `[0,0]`, `[0,1]`, `[0,2]`, … reaches `+∞` in one step. `meet` of disjoint intervals is `Bot`. Contracts are soundness against `gamma`, with explicit `#[trigger]`s. `lemma_canonical` says equal concretizations are equal values.

## Arithmetic

`Arith<Euclid>` and `Arith<Trunc>` share `add`, `sub`, and `neg`, which are exact on the endpoints. Addition of an infinite bound is that infinity. `Mul<Euclid>` and `Mul<Trunc>` take the four endpoint products. `0 * ±∞ = 0`. Comparing those products borrows them and copies only the smaller or the larger one.

## Division

`DivRem<Euclid>::div` and `DivRem<Trunc>::div` return `(BotOr<IntervalZ>, DivZero)`.

| `DivZero` | When                                       | Quotient           |
| --------- | ------------------------------------------ | ------------------ |
| `Always`  | the divisor is `{0}`                       | `Bot`              |
| `Never`   | the divisor excludes 0                     | endpoint quotients |
| `Maybe`   | the divisor contains 0 and another integer | split, then join   |

Both directions are proved: `Never` if and only if 0 is absent, and `Always` if and only if every concrete divisor is 0. `div_nonzero` is private and requires that the divisor exclude 0.

A divisor that contains 0 is split into `(-∞, -1]` and `[1, +∞)`. Each side is divided separately and the results are joined. A wholly negative divisor is negated, divided, and the quotient is negated.

Endpoint quotients when the divisor is positive:

- a negative lower bound is divided by the smaller positive endpoint;
- a nonnegative lower bound is divided by the larger one, and `+∞` contributes `0`;
- a nonnegative upper bound is divided by the smaller positive endpoint;
- a negative upper bound is divided by the larger one. Euclidean `+∞` contributes `-1`. Truncation contributes `0`.

So `[-8, -1] / [1, +∞)` is `[-∞, -1]` for Euclidean division, not an interval that contains `0`. Truncation of `-7 / 2` is `-3`; the Euclidean quotient is `-4`.

When the quotient of two finite intervals is a single integer, the remainder is `x - q * y` at the four corners, so a singleton division is exact: Euclidean `10 % 3 = 1` and `-7 % 2 = 1`, while truncation gives `-7 % 2 = -1`. Otherwise the remainder is the magnitude bound: Euclidean `0 <= r < |y|`, and truncation keeps the sign of the dividend. A finite dividend also cuts this by `|r| <= |x|` (Euclidean only when the dividend is nonnegative, since a negative Euclidean remainder can exceed `|x|`). When every `|y| <= |x|`, truncation uses `|r| <= (|x| - 1) / 2`, so truncated `[-5, -5] % [-5, 1]` is `[-2, 0]`. `DivZero` is the same flag as for the quotient.

`narrow` replaces an infinite endpoint of the first interval by the same endpoint of the second, and returns `Bot` if the bounds cross. Every concrete value that lies in both intervals survives, and every surviving value was already in the first interval. `refine(fact, budget)` is one `meet` when `budget > 0`, and it leaves the interval unchanged when `budget == 0`. The result contains a concrete value exactly when that value satisfies both intervals and fuel was spent. `meet_chain` repeats that step. Its soundness proof says a value in the start value and in every fact is still present, including when fuel runs out before the facts do.
