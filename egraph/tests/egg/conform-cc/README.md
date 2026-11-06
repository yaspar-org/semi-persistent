# AC-congruence closure conformance fixtures

`cc1_0000.egg` .. `cc1_0199.egg` are cases 0..199 of seed 1 of `semper-conform-cc`
(`proofs/lean/Conform/CC`). Each declares one AC operator, optionally with a unit,
an inverse, a nilpotent order, idempotence or cancellativity, asserts equations
between its terms under `(set-option :completion eager)`, and checks the result.

The oracle is a bounded closure of the equational theory: every monomial of total
count at most B (B from 3 to 5), closed under the asserted equations, congruence,
the law instances and cancellation, to a fixpoint. `CC/BoundedOracle.lean` proves
it sound for the theory (`run_sound`, `run_sound_nf`), so a failing `check-eq` is a
completeness gap of the engine. A `check-neq` is emitted only for pairs the closure
separates at B and at B+2: a derivation can pass through monomials above the bound.
Associativity without commutativity is excluded (its completion cannot be complete).

The cases are biased toward the completeness gaps the proofs found: overlapping
left-hand sides, a node that shrinks or grows when a later equation lands, inverse
nodes merged with each other, with the unit and with their argument, nilpotent
orders 2 and 3 with inverses, and cancellative operators. On seed 1, 2,000 cases
agree with the engine after the order-key fix; before it, 12 did not.

`tests/conform.rs` scans this directory. Regenerate, and the Lean workflow does
the same and fails when a committed file differs:

    cd proofs/lean
    lake exe semper-conform-cc 1 200 ../../egraph/tests/egg/conform-cc
