# Interval Domain: Soundness Contracts, Division, and Alarm Lattice

Design doc for `feature/interval-div-by-zero`.
Worktree: `semi-persistent-div-by-zero`

Legend: `[ ]` todo · `[x]` done · `[~]` in progress

---

## Motivation

The `Interval` type in `domains.rs` currently has two gaps:

1. **No soundness specifications.** Every method ensures `r.wf()` (well-formedness)
   but never states the soundness contract: that concrete results of represented
   values are contained in the abstract result. The Tnum and Anum layers have
   full `has`/`contains` specs with Verus proofs; Interval has none.

2. **Missing operations.** The TAI reduced product hardcodes `Interval::top()`
   for bitwise ops, sub, mul, neg, shifts. These are sound (⊤ contains
   everything) but the soundness obligation is implicit — there is no
   `Interval::bw_or` method with an ensures clause that a caller or future
   maintainer can rely on.

3. **No interval ÷ interval.** Only `div_const` exists. General division
   requires handling division by zero, which motivates the alarm lattice.

## Design

### 1. Containment predicate

```
pub open spec fn contains(self, x: $uint) -> bool { self.lo <= x && x <= self.hi }
```

Added to `Interval`. All soundness ensures clauses are stated in terms of this.

### 2. Soundness ensures on every operation

Each operation gets an ensures clause of the form:

```
ensures
    r.wf(),
    // soundness: every concrete result is contained
    forall |x, y| self.contains(x) && t.contains(y) ==> r.contains(conc_op(x, y))
```

For operations that return `top()`, soundness is trivially discharged since
`top().contains(x)` holds for all `x`. The point is making the contract
*explicit* so that:
- Future refinements (e.g., precise `bw_and` with constant) must satisfy the same spec.
- The reduced product's soundness can be composed from component soundness.

### 3. Stub methods for unsupported operations

New methods on `Interval`, all returning `top()` with soundness ensures:

| Method     | Returns   | Soundness                                    |
|------------|-----------|----------------------------------------------|
| `bw_or`    | `top()`   | trivial (⊤ contains everything)              |
| `bw_and`   | `top()`   | trivial                                      |
| `bw_xor`   | `top()`   | trivial                                      |
| `bw_not`   | `top()`   | trivial                                      |
| `sub`      | `top()`   | trivial                                      |
| `mul`      | `top()`   | trivial                                      |
| `neg`      | `top()`   | trivial                                      |
| `rsh`      | precise   | `[lo>>1, hi>>1]` — monotone, easy proof      |
| `lsh`      | precise   | overflow check like `plus`                   |
| `div`      | split+alarm | see §4 below                               |

The TAI methods are then updated to call `self.iv.bw_or(&t.iv)` etc. instead
of inlining `Interval::top()`. This makes the TAI a uniform reduced product
where each component contributes its own transfer function.

### 4. Alarm lattice and interval division

#### 4.1 The Alarm type

```
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Alarm { None, Maybe, Definite }
```

Lattice order: `None ⊑ Maybe ⊑ Definite`.

- `join(None, None) = None`
- `join(_, Definite) = Definite`
- `join(None, Maybe) = Maybe`
- `join(Maybe, Maybe) = Maybe`

This is the Astrée-style error flag (Cousot, Cousot, Feret, Mauborgne, Miné,
Rival — ENS). It cleanly separates "what value do we get" from "could this
crash", and composes with any numeric domain.

#### 4.2 Interval division: `[a,b] ÷ [c,d]`

Three cases for the divisor `[c,d]`:

1. **0 ∉ [c,d]** (i.e., `c > 0`): Normal division.
   Result = `[a/d, b/c]`, alarm = `None`.
   (For unsigned intervals where `c > 0`, this is straightforward.)

2. **[c,d] = [0,0]**: Every concrete divisor is zero.
   Result = `top()`, alarm = `Definite`.

3. **0 ∈ [c,d]** with `d > 0` (i.e., `c == 0, d > 0`): Split around zero.
   Exclude zero from divisor: effective divisor is `[1, d]`.
   Result = `[a/d, b/1]` = `[a/d, b]`, alarm = `Maybe`.
   (Sound because we over-approximate: any `x/y` with `y ∈ [1,d]` lands in
   `[a/d, b]`.)

Note: We work with *unsigned* integers, so the divisor interval `[c,d]` has
`c >= 0` always. The only question is whether `c == 0`.

#### 4.3 Return type

`div` returns `(Interval, Alarm)`. The alarm propagates through TAI as a
separate component. For all other operations, alarm is `None`.

### 5. TAI integration

TAI gains an `alarm: Alarm` field. The `reduce` method preserves it.
`TAI::div` computes the interval division and propagates the alarm.
All other TAI operations set `alarm: Alarm::None`.

### 6. Fuzz tests

The fuzz test file (`abstract-domains/tests/fuzz.rs`) currently tests ETn (all ops),
EAn (plus, div_const), and Interval (plus only). We add:

- `Interval::contains` — used by all interval fuzz tests
- `fuzz_iv_sub`, `fuzz_iv_mul` — verify `top()` contains results (trivial but confirms wiring)
- `fuzz_iv_rsh`, `fuzz_iv_lsh` — verify precise results
- `fuzz_iv_div_const` — verify existing div_const soundness
- `fuzz_iv_div` — verify interval÷interval soundness (skip div-by-zero samples, verify alarm flag)
- `fuzz_iv_bw_or`, `fuzz_iv_bw_and`, `fuzz_iv_bw_xor` — verify top() containment

### 7. Alternative interval representations (future work)

Two well-studied alternatives to classical `[lo, hi]` intervals exist for
machine-integer analysis. Neither is needed immediately because the TAI
reduced product compensates for the interval's weaknesses, but they inform
future design decisions.

#### 7.1 Wrapped intervals

Navas, Schachte, Søndergaard, Stuckey (APLAS 2012, TOPLAS 2015). Allow
`lo > hi` to mean the wrapped region `[lo, MAX] ∪ [0, hi]`. Signedness-
agnostic: treats integers as bit-strings, only distinguishing signed vs
unsigned for operations that differ. Avoids the `top()` fallback on overflow
that our current `plus` uses. Every operation needs wrap-around case splits,
increasing implementation and proof complexity.

#### 7.2 Strided intervals

Balakrishnan & Reps (CC 2004, PhD thesis 2007). Triples `(stride, lo, hi)`
representing `{i : lo ≤ i ≤ hi ∧ i ≡ lo (mod stride)}`. Captures alignment
and regular spacing — e.g., `4[0, 252]` means `{0, 4, 8, ..., 252}`. Meet
requires solving modular congruence systems (CRT). Formally verified in Coq
as part of the Verasco/CompCert project (IRISA).

#### 7.3 Why TAI already covers most of this

The Tnum component natively handles power-of-2 strides (the common case for
alignment) and wrapping arithmetic. The Anum tracks additive offsets. The
`reduce` step transfers Tnum/Anum precision back to the interval. The only
gap is non-power-of-2 strides, which are rare in practice. Wrapped intervals
would help the interval component specifically on overflow, but the Tnum
already carries information through wraps and `reduce` recovers it.

### 8. Abstract booleans and comparison operators

#### 8.1 Motivation

The TAI domain currently has no way to express the result of a comparison.
The demo uses ad-hoc `assume_lt` / `assume_ge` functions that manually
narrow intervals, but there is no abstract boolean type and no abstract
comparison operations. This means:

- Branch conditions can't be analyzed abstractly
- The result of `x < y` can't be represented as an abstract value
- Backward narrowing from branch conditions is ad-hoc

#### 8.2 The ABool lattice

```
         Top (may be true or false)
        /   \
    True     False
        \   /
        Bot (unreachable)
```

```rust
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum ABool { Bot, True, False, Top }
```

Concrete containment: `ABool::contains(self, b: bool)`:
- `Bot` contains nothing
- `True` contains only `true`
- `False` contains only `false`
- `Top` contains both

Lattice operations:
- `join(True, False) = Top`, `join(x, Bot) = x`, etc.
- `meet(True, False) = Bot`, `meet(x, Top) = x`, etc.
- `not(True) = False`, `not(False) = True`, `not(Top) = Top`, `not(Bot) = Bot`
- `and(True, True) = True`, `and(False, _) = False`, `and(True, Top) = Top`, etc.
- `or(True, _) = True`, `or(False, False) = False`, `or(False, Top) = Top`, etc.

#### 8.3 Abstract comparison operations on TAI

Each comparison returns `ABool`:

| Operation      | Semantics                          | Precision source          |
|----------------|------------------------------------|---------------------------|
| `TAI::cmp_eq`  | Could `x == y`?                    | Interval overlap + Tnum   |
| `TAI::cmp_ne`  | Could `x != y`?                    | Interval disjoint + Tnum  |
| `TAI::cmp_lt`  | Could `x < y`?                     | Interval bounds           |
| `TAI::cmp_le`  | Could `x <= y`?                    | Interval bounds           |
| `TAI::cmp_gt`  | Could `x > y`?                     | Interval bounds           |
| `TAI::cmp_ge`  | Could `x >= y`?                    | Interval bounds           |

The key insight: interval bounds give us definite answers in many cases:
- If `self.max_val() < t.min_val()` then `cmp_lt` returns `True` (definitely less)
- If `self.min_val() >= t.max_val()` then `cmp_lt` returns `False` (definitely not less)
- Otherwise `Top` (could go either way)

For equality, Tnum adds precision: if the known bits of `self` and `t`
conflict (i.e., there exists a bit position where both Tnums have known
but different values), then equality is impossible → `False`.

#### 8.4 Backward narrowing (assume)

Given `cmp_lt(x, y) = True` (branch taken), we can narrow:
- `x.iv.hi = min(x.iv.hi, y.iv.hi - 1)` (x must be less than y's max)
- `y.iv.lo = max(y.iv.lo, x.iv.lo + 1)` (y must be greater than x's min)

This replaces the ad-hoc `assume_lt` / `assume_ge` in demo.rs with
principled abstract operations.

#### 8.5 Soundness contract

```
ensures
    forall |x, y| self.contains(x) && t.contains(y) ==> result.contains(x < y)
```

Where `result.contains(b)` means the abstract boolean includes the concrete
boolean `b`.

---

## Tasks

### Phase 1: Interval soundness contracts and stubs

- [x] 1.1 Add `Interval::contains` spec
- [x] 1.2 Add soundness ensures to `Interval::constant`, `top`, `plus`, `meet`, `join`, `div_const`
- [x] 1.3 Add `Interval::bw_or`, `bw_and`, `bw_xor`, `bw_not` — return `top()`, soundness ensures
- [x] 1.4 Add `Interval::sub`, `mul`, `neg` — return `top()`, soundness ensures
- [x] 1.5 Add `Interval::rsh` — precise `[lo>>1, hi>>1]`, soundness ensures
- [x] 1.6 Add `Interval::lsh` — with overflow to `top()`, soundness ensures
- [x] 1.7 Update TAI methods to call Interval methods instead of inlining `Interval::top()`

### Phase 2: Alarm lattice and division

- [x] 2.1 Add `Alarm` enum with `join` and `meet`
- [x] 2.2 Add `Interval::div` returning `(Interval, Alarm)`
- [x] 2.3 Add `alarm: Alarm` field to TAI
- [x] 2.4 Add `TAI::div` wiring interval div + alarm propagation
- [x] 2.5 Update `TAI::reduce`, `join`, `meet` to propagate alarm

### Phase 3: Fuzz tests

- [x] 3.1 Add `Interval::contains` to fuzz test mirror
- [x] 3.2 Add fuzz tests for all Interval ops (bw_or/and/xor, sub, mul, rsh, lsh, neg)
- [x] 3.3 Add fuzz test for `Interval::div_const`
- [x] 3.4 Add fuzz test for `Interval::div` with alarm verification

### Phase 4: Abstract booleans and comparisons

- [x] 4.1 Add `ABool` enum with `contains`, `join`, `meet`, `not`, `and`, `or`
- [x] 4.2 Add `TAI::cmp_lt`, `cmp_le`, `cmp_gt`, `cmp_ge`, `cmp_eq`, `cmp_ne` returning `ABool`
- [x] 4.3 Add `TAI::assume_ult` / `assume_uge` for backward narrowing from comparisons
- [x] 4.4 Add fuzz tests for all comparison operations
- [x] 4.5 Refactor demo.rs `assume_lt` / `assume_ge` to use new abstract comparisons
