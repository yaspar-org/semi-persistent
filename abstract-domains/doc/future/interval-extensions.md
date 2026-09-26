# Interval Domain Extensions

[Current interval contracts](../interval-soundness.md) |
[Proof status](../proof-status.md)

The shipping interval component is a non-wrapping unsigned range with a
canonical bottom and proved `add`, `join`, `meet`, and positive-constant
division contracts. This document specifies extensions that are not
implemented on the current branch. Nothing here is evidence that the
corresponding operation exists or verifies.

## 1. Transfer Functions, Division, and Alarms

### Current state

`Interval::div` returns a value interval and the shared `DivAlarm`, with proved
nonzero quotient containment and alarm membership. `ReducedProduct::div`
propagates both results through the reduced product and proves that reduction
preserves every quotient for a represented nonzero divisor.

### Gap

The interval component has explicit, proved bitwise transfers, but they
deliberately return `top` for non-bottom operands and therefore contribute no
bitwise precision. Subtraction, multiplication, negation, and both one-bit
shifts have proved endpoint transfers; operations conservatively return `top`
when their results cross the unsigned wrap boundary.

### Task

The division and alarm composition task is complete. The remaining interval
transfer opportunity is to replace conservative bitwise `top` results with
proved endpoint bounds when those bounds improve precision.

The interval division transfer uses the following cases for unsigned dividend
`[a,b]` and divisor `[c,d]`:

- `c > 0`: return `[a / d, b / c]` with no-error;
- `c = 0 < d`: return `[a / d, b]` with maybe-error; and
- `c = d = 0`: return `bottom` with definite-error.

The alarm domain uses concretization rather than severity:

```text
NoError       = {false}
DefiniteError = {true}
MaybeError    = {false, true}
```

Thus `NoError` and `DefiniteError` are incomparable and their proved join is
`MaybeError`. Reduced-product division propagates the alarm according to this
concretization. Alarm-bearing control-flow joins remain future client-level
work.

### Acceptance criteria

- Every new executable transfer has a universal containment postcondition and
  a well-formed result postcondition.
- Division proves both value containment for every nonzero concrete divisor
  and correct alarm membership for zero and nonzero divisors.
- Joining a safe and a definitely failing path yields maybe-error, not
  definite-error.
- Exhaustive small-width tests cover endpoint, wrap, zero-only, and mixed-zero
  divisor intervals in addition to the Verus proofs.
- Ordinary Verus verification passes, the project-local no-admit source gate
  stays green, and any dependency axioms remain explicit in the trust boundary.

## 2. Abstract Booleans and Backward Narrowing

### Current state

The reduced product has no abstract boolean result type, comparison transfer
functions, or branch-assumption API. Interval overlap and conflicting known
Tnum bits are therefore not exposed as reusable comparison facts.

### Gap

Clients cannot represent the result of `eq`, `ne`, or unsigned order
comparisons, and a taken branch cannot soundly narrow its operands through a
specified operation.

### Task

Introduce the four-point boolean domain
`{Bottom, True, False, Top}` with an explicit concretization and proved
`join`, `meet`, `not`, `and`, and `or`. Add reduced-product comparisons:

- interval disjointness and singleton equality for `eq`/`ne`;
- conflicting known Tnum bits as an additional proof of inequality; and
- interval endpoint reasoning for unsigned `<`, `<=`, `>`, and `>=`.

Add backward transfer functions for true and false branches. For a true
unsigned `x < y` branch, narrow with checked forms of
`x.hi <= y.hi - 1` and `y.lo >= x.lo + 1`, detect an infeasible branch, and run
the ordinary reduced-product reduction afterward. Represent infeasibility with
the explicit bottom; do not encode it as an ordinary nonempty interval.

### Acceptance criteria

- Comparison results contain every concrete comparison of represented inputs.
- Backward transfer retains every concrete input pair satisfying the assumed
  branch and rejects only pairs that violate it.
- Boundary cases at zero and the machine maximum cannot underflow or overflow.
- Exhaustive small-width tests compare forward and backward results with
  concrete enumeration.
- Reduced-product soundness composes from the boolean, interval, Tnum, Anum,
  and Unum contracts without an admit.

## 3. Wrapped Intervals

### Current state

Endpoint wrap causes the ordinary interval transfer to widen to `top`. Tnum and
Anum components can retain some information across wrap, but the interval
component itself cannot represent `[lo, MAX] union [0, hi]`.

### Gap

Programs dominated by modular arithmetic may lose useful interval precision at
the first wrap. It is not known whether a wrapped interval component improves
the existing reduced product enough to justify its larger proof and runtime
surface.

### Task

Prototype a separate wrapped-interval type with explicit empty and full states
so endpoint equality and `lo > hi` are unambiguous. Specify its concretization
over machine integers and prove canonicalization, join, meet, arithmetic, and
conversion to and from the existing interval and Tnum components.

Measure it against the current reduced product on wrap-heavy workloads before
replacing the ordinary interval component.

### Acceptance criteria

- Every representation has one explicit concretization, including empty and
  full.
- Transfer functions are proved sound for modular machine arithmetic.
- Conversion and reduction preserve represented concrete values.
- Criterion measurements report precision and runtime separately; adoption
  requires a maintained workload with a material precision benefit.
- The ordinary interval implementation remains available until equivalence or
  a migration boundary is proved.

## 4. Strided Intervals

### Current state

Tnum captures power-of-two alignment, but the reduced product has no direct
representation for non-power-of-two congruence classes such as values equal to
`1 mod 3` within a range.

### Gap

It is unknown whether non-power-of-two stride information is useful for target
consumers, and meet requires a checked modular-congruence construction rather
than endpoint arithmetic alone.

### Task

Specify a canonical strided interval `(stride, lo, hi)` with explicit singleton,
empty, and full conventions. Prove membership, normalization, join, meet, and
the arithmetic operations selected by a motivating consumer. The meet proof
must either construct the compatible congruence with gcd/CRT lemmas or return
empty when none exists.

Define reductions with Tnum, Anum, and the ordinary interval without claiming
that either component subsumes the other.

### Acceptance criteria

- Well-formedness implies a nonambiguous finite concretization.
- Join contains both operands; meet denotes their exact intersection whenever
  the chosen representation can express it and a sound over-approximation
  otherwise.
- GCD/CRT helper lemmas verify without trusted arithmetic shortcuts.
- Exhaustive small-width enumeration checks every lattice and transfer
  operation.
- A production integration requires a demonstrated precision benefit and
  Criterion evidence for its runtime and memory cost.
