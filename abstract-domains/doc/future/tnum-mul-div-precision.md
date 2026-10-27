# Precision-optimized Tnum multiplication and division

This is a proposal for new `ExecTnum::mul` and `ExecTnum::div` algorithms, with the
Layer-2 specs, Layer-3 statements, and simulation arguments that connect them. It is not
a status page: `proof-status.md` records what is proved. Every number below was measured
by the brute-force harness described in the next section; none is inferred.

## Measurement

The harness takes two Tnums, enumerates every concrete pair of members, computes the
concrete results, and lifts them back into the best Tnum: the AND and the OR of all
results. It then runs each algorithm in W-bit registers, checks soundness against every
concrete result, and reports how many unknown bits the algorithm's result has beyond the
best Tnum. At W = 8 it runs every pair (43.0M for multiplication, 41.4M with a nonzero
divisor minimum for division). At W = 16 it samples 2M to 3M pairs with at most 14
unknown bits in total, so that the best Tnum stays enumerable. The unbounded layer uses
`num-bigint` `BigUint`.

The difference between the exact set and the best Tnum is the loss of the
representation; the difference between the best Tnum and an algorithm's result is the
loss of the algorithm. Only the second can be recovered inside the Tnum domain.

## Multiplication: pair-join

**Where the precision goes.** Split the product by the unknown bits of each operand:

    x * y = x.v * y.v + sum_l v_l * (x.v << l) + sum_k u_k * (y << k)   (mod 2^W)

where `v_l` ranges over the unknown bits of `y` and `u_k` over those of `x`. Each term is
one of two values, `{0, c}`. `Anum::mul_step_rc` (the loop of the current
`ExecTnum::mul`) adds each term as the Tnum `(0, c)`, which has 2^popcount(c) members.
That is where most of its loss comes from.

**Algorithm.** Start from the exact product of the known parts, then, for each unknown
bit, keep both values of its term:

    acc := (x.v * y.v, 0)
    for each unknown bit l of y:  acc := join(acc, acc + (x.v << l, 0))
    for each unknown bit k of x:  acc := join(acc, acc + (y << k))

The new partial sum is either `acc` or `acc + c`, and the join holds both. The cost is one
Tnum addition and one join per unknown bit.

**Layer 2.** Two recursions with an accumulator, peeling the lowest bit as `mul_step`
does:

- `pj_const(s, ym, acc)`: if `ym == 0` return `acc`; otherwise recurse on
  `(2s, tl(ym), acc')`, where `acc' = join(acc, acc.add(Tn(s, 0)))` when `hd(ym)` is set.
- `pj_tnum(y, xm, acc)`: the same over the unknown bits of `x`, with the step
  `join(acc, acc.add(y))` and the recursion on `y.lsh()`.
- `pair_mul(X, Y) = pj_tnum(Y, X.m, pj_const(X.v, Y.m, Tn(X.v * Y.v, 0)))`.

Soundness, with `submask(d, m)` meaning the bits of `d` are among those of `m`:

1. `acc.has(z) && submask(d, ym) ==> pj_const(s, ym, acc).has(z + s * d)`, by induction
   on `ym`, splitting `d = hd(d) + 2 tl(d)`; each step uses `add_sound` and `join_sound`.
2. `acc.has(z) && y.has(w) && submask(d, xm) ==> pj_tnum(y, xm, acc).has(z + w * d)`, the
   same induction, with `lsh_sound` carrying `y.has(w)` to `y.lsh().has(2w)`.
3. The theorem: write `x = X.v + dx` and `y = Y.v + dy` with `dx`, `dy` submasks; then
   `x * y = X.v * Y.v + X.v * dy + y * dx`, covered by lemma 1 then lemma 2.

The decomposition `X.has(x) ==> x = X.v + dx` follows from `has_equiv`. The steps
`s * d == s * hd(d) + 2 s * tl(d)` need `by(nonlinear_arith)`.

**Layer 3.** `ChoppedTnum::pair_mul = pair_mul(..).chop_tn(w)`, as `ChoppedTnum::mul` is
stated today. The harness checks that the W-bit loop equals chop of the unbounded
`pair_mul` on every u8 pair and on every sampled u16 pair (0 mismatches).

**Layer 4.** The exec loop runs over the W bit positions of each mask and keeps the
invariant `acc.to_tn() == chop(acc_spec, W)`. Each step needs:
- `chop_add_bitwise` and `add_bitwise_eq`, which exist;
- `chop_lsh_tn`, which exists;
- `chop(join(a, b)) == join(chop(a), chop(b))`, a new bitwise lemma.

**Measured.**

| algorithm | u8: optimal | u8: bits lost | u16: optimal | u16: bits lost |
| --- | --- | --- | --- | --- |
| `mul_step_rc` (current) | 90.0% | 0.129 | 58.1% | 0.831 |
| pair-join | **97.2%** | **0.029** | **89.8%** | **0.120** |
| pair-join, both operand orders, meet | 97.6% | 0.025 | 91.8% | 0.093 |

The representation loss at u8 is 1.73 bits (exact set 4.36, best Tnum 6.09, mean log2
size). Both operand orders gain 0.4 points at u8 and 2 points at u16, at twice the cost;
the single order is the proposal, and the meet is an option.

**Rejected alternatives, with their numbers** (Python prototypes, 12,000 to 24,000
sampled pairs): the meet of the Anum and Tnum accumulators gains at most 0.25 points over
`mul_step_rc`, because the two lose precision on the same inputs; a numeric bound on the
uncertain part with NAF recoding gains 0 to 5.5 points; enumerating the members of an
operand with at most k unknown bits reaches 97% at u16 for k = 6, but costs 2^k
multiplications and was rejected as enumeration.

## Division: bounded, guarded long division

**The current spec.** `Tnum::div(t, w)` (`div.rs`) is long division from the top bit, with
three branches on the shifted remainder `r1`: subtract, keep, or, when the comparison
depends on the concrete values, `join(r1, r1 - d)` with a quotient bit `x`. Subtraction
is two's complement at `w + 1` bits, and the remainder is never chopped.

**What the harness shows about it.**
- The unbounded remainder exceeds W bits in 75.7% of u8 pairs. The extra bits come from
  the uncertain branch, where `r1 - d` wraps for the members with `r1 < d`; they are
  always unknown bits, never known-1.
- A W-bit loop running the same algorithm equals chop of the unbounded state after every
  step, on every u8 pair and every sampled u16 pair, and the quotients are identical.
  The width question therefore has no consequence for soundness; it only concerns how the
  simulation is stated.
- The quotient is already close to the best Tnum (0.069 bits lost at u8). The remainder
  is not (0.92 bits lost at u8).

**Algorithm.** Three refinements, each sound because every concrete remainder is below
the divisor and below the prefix of the dividend consumed so far:

1. **Remainder bound.** After step j, chop the remainder to `min(j, k)` bits, with
   `k = bit_width(d.max())`. Every concrete remainder is below `d.max() < 2^k`, and after j
   steps it is at most the j-bit prefix of the dividend, so below `2^j`.
2. **Guarded branches.** In the uncertain branch, restrict each side to the members its
   guard admits: the kept side to `[0, d.max() - 1]`, and the subtracted side to
   `[0, min(r1.max() - d.min(), d.max() - 1)]`, each by a meet with the Tnum of the range.
3. **Final range meets.** Meet the quotient with the Tnum of
   `[n.min() / d.max(), n.max() / d.min()]` and the remainder with that of
   `[0, min(n.max(), d.max() - 1)]`.

**Measured** (remainder; the quotient moves from 94.2% to 94.6% optimal at u8).

| variant | u8: optimal | u8: bits lost | u16: optimal | u16: bits lost |
| --- | --- | --- | --- | --- |
| current | 45.1% | 0.924 | 43.0% | 1.075 |
| 1. remainder bound | 66.3% | 0.489 | 62.9% | 0.590 |
| 1 + 2 + 3 | **79.1%** | **0.279** | **74.0%** | **0.389** |

The representation loss of the remainder at u8 is 1.57 bits (exact set 3.87, best Tnum
5.44): larger than what the algorithm still loses. Remainder sets are close to ranges
such as `[0, d - 1]`, which a Tnum represents poorly, and the best Anum is only 0.1 bits
smaller. Recovering that loss is a reduced-product question (Interval, Unum), not a Tnum
algorithm question; it has not been measured.

**Layer 2.** `div` becomes width-free: the iteration count is a parameter, the
subtraction width is `k + 1`, derived from the divisor, and the remainder after each step
is chopped to `min(j, k)` bits. With the prefix bound, the shifted remainder `r1` has at
most W bits on every u8 pair (Python model, W = 3 to 5, every pair), so the Layer-2 state
of a division of W-bit inputs is itself a W-bit value.

Soundness extends `div_loop_sound` with two facts per step: the concrete remainder is
below `dv <= d.max() < 2^k`, and it is at most `nv >> i`, the prefix consumed so far
(a new invariant, maintained because `2 (nv >> i) + bit(nv, i - 1) == nv >> (i - 1)` and
subtraction only decreases it). Each chop is then `chop_sound` plus `chop_id`. The
guarded meets need a Tnum-of-range spec with its soundness lemma
(`lo <= x <= hi ==> range_tn(lo, hi).has(x)`) and `meet_sound`, which exists.

The remainder bound alone (refinement 1 with k, without the prefix term) is proved on the
local branch `div-remainder-bound` (commit 65a366b): `div_k(t, w, k)` with `div_k_sound`
for any `k` with `t.max() < 2^k`; `div` is `div_k` with `k = w`, and the whole crate
verifies (0 errors).

**Layer 3.** Because the Layer-2 state of a division of W-bit inputs fits W bits, Layer 3
is Layer 2 restricted to inputs below 2^W, with no chop. `div_sound_div` already relates
the result to `/` and `%`.

**Layer 4.** The exec loop runs W steps in W-bit registers and computes `k` with one
leading-zero count. Its state equals the Layer-2 state exactly. The one lemma beyond
equality of the arithmetic is that subtraction at W bits, chopped to `min(j, k) <= W`
bits, equals subtraction at `k + 1` bits chopped the same way, which follows from
`chop_add_bitwise`.

## Prerequisites shared by both

- **`chop` of `join`**, a new bitwise lemma, used by both simulations.
- **Tnum of a range** at Layer 2 (`range_tn(lo, hi)`: the common prefix of `lo` and `hi`,
  unknown below it), with its soundness lemma, and its exec counterpart, which needs
  `bit_width`.
- **The exec layer as `impl<W: Word>`.** These algorithms are best written once over the
  `Word` trait rather than in the `abstract_domain!` macro, with the bit-level bridges as
  `Word` lemmas. Under the macro every `by(bit_vector)` query is re-verified per width
  (d64 takes 10 times the SMT time of d8 on #108's head), and d128 stays disabled.

## Work plan

1. Prove the division prefix bound, and with it the exact Layer-2/exec correspondence.
2. Add `range_tn`, its soundness lemma, and the guarded and final meets to `div`.
3. Write `ExecTnum::div` and `ExecTnum::rem` against the Layer-2 spec.
4. Write `pair_mul` at Layer 2 with lemmas 1 to 3, then its Layer-3 statement.
5. Replace the loop of `ExecTnum::mul` with pair-join and prove the simulation.
6. Measure Interval and Unum on the same u8 space to size the reduced-product gain.

Steps 1 to 3 and 4 to 5 are independent. The harness is not in the repository yet: it
reruns every table above in under two minutes at u8, and would belong under `tests/` or
`bench/` if this proposal is adopted.
