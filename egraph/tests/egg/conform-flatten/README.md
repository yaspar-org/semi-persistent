# `:flatten` conformance fixtures from the Lean e-matching model

Every `.egg` file here was written by `semper-conform-flatten`, the `:flatten`
conformance generator of the Lean development (`proofs/lean/Conform/Flatten/`,
Lake executable `semper-conform-flatten`). A file builds a small e-graph, applies
one rule whose right-hand side tags the bound variables, and checks the matches
the model computes as `check-eq`, and a sample of the candidates it rejects as
`check-neq`. A rule tagged `:flatten` is matched by the model's flattened plan
(`runER` of `SemperProofs/EMatch/Flatten/RegroupDefs.lean` over the plan of
`PlanDefs.lean`: the pattern's atoms, every n-ary atom flattened into its own
view register, with the views of the opening walk and their regrouped views,
accepted by the engine's demand rule); an untagged rule by the reference
interpreter, as in `../conform/`. A regrouped view replaces a group of a view's
entries by the class of an existing node over that group, and a matched record
needs at most one regrouped class per item (`regroup_plan_sound`, `regroup_plan_complete` in `Flatten/Regroup.lean`). A draw
whose regrouping passes the generator's budget (`regroupCap`) is redrawn.

The cases cover what the seed-1 fixtures (`../conform/`) leave out of `:flatten`:
n-ary applications nested in the pattern, laws on two operators of one pattern
(`Add` with `:identity`/`:nilpotent`/`:inverse` and `And` with `:identity`),
cyclic classes, several nodes of one operator in one class, sequences with
prefix and suffix rests, the folds `SubL` (`:assoc-left`) and `SubR`
(`:assoc-right`), whose views open only the fold's spine, and nodes with many raw views
(up to the generator's cap of 300 per node). The header of each file names its
family and the features it covers.

The files are the first 200 cases of seed 2 (`f2_0000.egg` .. `f2_0199.egg`).
`conform.rs` scans this directory and runs each file under both evaluation
strategies and both atom-scheduling modes; a file needs no registration.

Regenerate, from `proofs/lean`:

    lake build semper-conform-flatten
    lake exe semper-conform-flatten 2 200 ../../egraph/tests/egg/conform-flatten

The same seed gives byte-identical files. The Lean workflow
(`.github/workflows/lean.yml`) regenerates the sample and fails when a committed
file differs, so the fixtures stay pinned to the model's executable definitions:
after a change to the model or the generator, regenerate and commit the diff.
