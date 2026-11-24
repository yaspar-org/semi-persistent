# Certified AC-congruence closure conformance fixtures

`cs1_0000.egg` .. `cs1_0199.egg` are cases 0..199 of seed 1 of `semper-conform-cc-cert`
(`proofs/lean/Conform/CC/Cert.lean`), written with `--fixture`, which omits the
`dump-egraph` line the soundness runner reads. Each declares one AC operator with laws
from identity, nilpotent order, inverse, idempotence and cancellativity, asserts
equations under `(set-option :completion eager)`, and checks two kinds of pairs.

- A `check-neq` is emitted only for a pair that a concrete countermodel separates: a
  commutative monoid (natural-number vectors or `ZMod k` vectors) and a valuation of the
  classes under which every asserted equation and every law instance holds, cancellative
  when the operator is, and the two sides differ. The certificate precedes the check
  (`;; CERT ...`). `SemperProofs/CC/Countermodel.lean` proves such a pair is not
  theory-equal (`not_E_of_separates`), so a failing `check-neq` is an unsoundness of the
  engine.
- A `check-eq` pair is equal in the bounded closure of the theory
  (`SemperProofs/CC/BoundedOracle.lean`, `run_sound`), so a failing `check-eq` is a
  completeness gap of the engine.

Every program from this generator that revealed an engine bug is also a hand-registered
fixture in `tests/egg` (`cancel_lattice.egg`, `cancel_crit_pair.egg`,
`cancel_lattice_lazy.egg`, `nilpotent_group_lattice.egg`, `ac_collapsed_recanon.egg`), so
no regression depends on the generator's output.

`tests/conform.rs` scans this directory. Regenerate, and the Lean workflow does the same
and fails when a committed file differs:

    cd proofs/lean
    lake exe semper-conform-cc-cert 1 200 ../../egraph/tests/egg/conform-cc-cert --fixture
