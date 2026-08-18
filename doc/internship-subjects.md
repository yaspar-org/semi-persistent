# Internship subjects

Three self-contained projects on the semi-persistent e-graph engine. Each
names its objective as an acceptance test, the workspace pieces it builds on,
and staged milestones so a partial completion is still a deliverable. The
engine background is `egraph/doc/design/` (start at the overview and the
table of contents); the verification background is `containers-verus/README.md`
and its design chapters.

## 1. Lattice functions on verified abstract domains

Objective: lattice-valued functions, `(function f (Args) Ret :merge ...)`,
where a functional-dependency collision resolves by a lattice join instead of
a class union. Acceptance: the nine egglog perf-suite programs gated on this
feature pair pass, including the seven that share one 6658-line header
(`tests/header/luminal-header.egg`, translated once), and herbie's stripped
interval analysis becomes translatable.

Three layers. Domains: reuse and extend the `abstract-domains` crate's
verified lattices; a `:merge` is a join in a declared domain, not an
arbitrary expression, which is what makes the verification tractable.
Verified storage: extend the verified class layer (`containers-verus`
EClasses, or a sibling table keyed like it) with lattice-valued payload;
the well-formedness clause follows the W7 pattern in
`containers-verus/src/eclasses.rs`: the stored value equals the join of the
ghost write history, at every method boundary and per archived frame, so
mark/restore carries accuracy through the existing payload-rollback proofs.
Engine integration: a lattice write is a semi-naive delta event (design
chapter 18 explains why a change that creates no node must still reach the
delta), the proof representation of a join is decided up front (a join is
not a union), and `run-schedule` (`seq`/`saturate`/`repeat`) desugars to the
existing run loop.

Milestones: one verified domain wired end to end with restore fixtures; the
well-formedness clause verified at 0 errors; semi-naive integration with a
delta-completeness fixture; run-schedule; the luminal header and the nine
programs, timed under the campaign protocol. Estimated 8-12 person-weeks.

## 2. A verified query compiler

Objective: verify the pipeline from a resolved query to an executable match
plan, so plan-level matcher defects are excluded by construction. The two
historical defect classes to design against: a backtracking step clearing
variables it did not bind, and a literal atom compiled without an index
lookup so its rule never fires.

Staged. Stage 1, a verified plan validator: a Verus-checked pass over
compiled plans asserting the plan invariants (every variable bound before
read, cleanup clears exactly what the step bound, every atom reachable,
literal atoms carry a lookup, guards scheduled after their binders), run at
rule install. Stage 2, a verified reference matcher: an executable
pattern-level semantics (match sets defined against the e-graph model,
partition semantics for AC per design chapter 9) proved sound against the
spec, used as the differential oracle for the optimized engines; this kills
the failure mode where every engine agrees on one shared mistake. Stage 3,
stretch: prove plan generation refines the reference semantics, making the
validator redundant.

Acceptance: the validator rejects plans seeded with each historical defect;
the oracle reproduces the egg-test corpus match sets; both verify at 0
errors. Estimated 8-12 person-weeks; stages 1 and 2 stand alone.

## 3. A Max-SAT term extractor

Objective: extraction as optimization. The e-graph reads as an AND/OR graph
(classes are OR nodes choosing one member, nodes are AND nodes requiring all
children); hard clauses encode the selection constraints, soft clauses carry
the cost model with weights on nodes and on edges; a partial weighted
Max-SAT solver (or a pseudo-Boolean solver for linear costs) finds the
optimum. The design sketch is in `egraph/doc/design/A3-future-work.md`.

Scope: the encoder, including the classic subtlety that the selected
sub-DAG must be acyclic (ordering variables or a solver-side acyclicity
constraint); solver integration behind a trait, with the current fixpoint
extractor remaining the default; model decoding with deterministic
tie-breaking; objectives the fixpoint extractor cannot express: DAG cost
(shared subterms counted once), per-operator weights, `:unextractable` as a
hard exclusion, lexicographic multi-objective.

Acceptance: equal costs against the fixpoint extractor on the corpus where
both apply; at least one benchmark exhibiting an objective only this
extractor expresses (the combinators program's cost asymmetry is the
natural exhibit); encode-plus-solve time measured against graph size.
Estimated 6-10 person-weeks. Context: `comparison/eqsolve.deviations.md`
records that extraction is not a bottleneck on the current corpus; the value
here is expressiveness, not speed.
