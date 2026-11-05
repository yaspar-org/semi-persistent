# Conformance fixtures from the Lean e-matching model

Every `.egg` file here was written by `semper-conform`, the conformance generator
of the Lean development (`proofs/lean/Conform/`, Lake executable `semper-conform`).
A file builds a small e-graph, applies one rule whose right-hand side tags the
bound variables, and checks the matches the model's reference interpreter computes
(`run (compile P)` of `SemperProofs/EMatch/Ref.lean`, through `enumerateX` /
`enumerateL` views when the rule is `:flatten`) as `check-eq`, and a sample of the
candidates it rejects as `check-neq`.

The files are the first 200 cases of seed 1 on which the model and the engine agree
(`c1_0000.egg` .. `c1_0199.egg`). `conform.rs` scans this directory and runs each
file under both evaluation strategies and both atom-scheduling modes; a file needs
no registration.

Regenerate, from `proofs/lean`:

    lake build semper-conform
    lake exe semper-conform 1 200 ../../egraph/tests/egg/conform

The same seed gives byte-identical files. The Lean workflow
(`.github/workflows/lean.yml`) regenerates the sample and fails when a committed
file differs, so the fixtures stay pinned to the model's executable definitions:
after a change to the model or the generator, regenerate and commit the diff.
