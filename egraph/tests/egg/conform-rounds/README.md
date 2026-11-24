# Multi-round conformance fixtures

`r1_0000.egg` .. `r1_0199.egg` are cases 0..199 of seed 1 of `semper-conform-rounds`
(`proofs/lean/Conform/Rounds`). Each builds a small e-graph, declares two to four rules
whose heads build terms (`union`, inserts, `rewrite`, occasionally `:subsume`), runs
`(run k)` with `k` in 2..5, and checks the final state.

- Fired checks: every match of every rule on the snapshot of round `k` (the naive run's
  dump after `(run k-1)`), computed by the reference interpreter of the Lean model, has
  its consequence in the final state: the model's `Saturate.InvLag`, which is
  `Saturate.Inv` when the run saturated.
- State checks: the classes of the naive final state (a member per class equal to the
  class's term, distinct classes not equal), which every evaluation mode must reach.

`tests/conform.rs` runs every file under naive and semi-naive evaluation and both
atom-scheduling modes. Regenerate (the engine is needed: the oracle reads its dumps):

    cd proofs/lean
    lake exe semper-conform-rounds 1 200 ../../egraph/tests/egg/conform-rounds \
      --engine ../../target/release/semi-persistent
