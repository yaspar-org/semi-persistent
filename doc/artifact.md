<!--
Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
SPDX-License-Identifier: Apache-2.0
-->
# Reproducing headline evidence

One command per headline evidence family, and what it should print.
`doc/claims.md` says what is claimed and at what strength. A headline claim
with no command here has no repository-local mechanical check and is marked
accordingly.

Times are from one laptop and are given so a run that takes ten times longer
tells you something is wrong, not as a performance result.

## Prerequisites

```
rustup toolchain install stable            # the workspace
```

Verus is needed only for the proof crates. The pinned version is in
`containers-verus/.verus-version`, and all three verified crates pin the same
one (CI fails if they drift).

The egglog comparison needs egglog at the revision `egraph/benches/corpus.toml`
pins; the script clones and builds it, or `--keep-egglog <path>` reuses a
checkout and refuses to record a run if it is at the wrong revision.

## Core build and proof commands

```
cargo fmt --all -- --check
cargo clippy --workspace --all-targets -- -D warnings
cargo build --workspace
cargo test --workspace
cargo build --workspace --all-targets --all-features
cargo test --workspace --all-features
cargo deny check
(cd abstract-domains && cargo verus verify)                     # 994 verified, 0 errors
(cd containers-verus && cargo verus verify)                    # 1703 verified, 0 errors
(cd containers-verus && cargo verus verify --features literal-types) # 1703 verified, 0 errors
(cd au-verus && cargo verus verify)                             # 29 verified, 0 errors
```

The main CI workflow sets `RUSTFLAGS="-D warnings"` for its build and test
jobs; set it locally to match.
CI separately scans `abstract-domains/src`, `containers-verus/src`, and
`au-verus/src` for project-local `admit()`/`assume()` calls. Do not add
`--no-cheating` to the abstract-domain command while the pinned `vstd`
dependency contains admitted specifications: that command fails in `vstd`
before project verification. This dependency is part of the stated trust
boundary.

The legacy-container performance comparison is a Criterion report, not a CI
gate:

```bash
cargo bench -p containers-conformance --bench retained_containers_bench
```

Use its confidence intervals and record the host, revision, and registration
order with any cited result.

## The anti-unification claims

| claim | command |
| --- | --- |
| The solver agrees with `OPT` on enumerable fixtures | `cargo test -p semi-persistent-egraph --release --test au_oracle` |
| Bounds never overestimate | same file, `lb_pair_never_exceeds_the_true_optimum` |
| Edge-count sharing preserves the optimum | same file, `edge_count_sharing_agrees_with_the_unfolded_optimum` |
| The AC transport finds the best matching | same file, `ac_transport_agrees_with_exhaustive_member_matching` |
| The answer reads the class, not the representative | same file, `the_optimum_does_not_depend_on_merge_order` |
| Every flag preserves soundness | `cargo test -p semi-persistent-egraph --release --test au_differential` |
| Delegation pays when the misjudgement is shallow | `cargo test -p semi-persistent-egraph --release --test au_delegation` |
| Positional recurrence lower bound, machine-checked | `(cd au-verus && cargo verus verify)` |

The oracle tests skip fixtures whose term set is too large to enumerate, and
assert a floor on how many were checked, so they cannot pass by skipping
everything.

There is no reproduction command for `D* = OPT`, because no current theorem
states it. The missing proof steps are listed in `claims.md` section 4.

## Proof export

```bash
cargo run -p semi-persistent-egraph -- \
  egraph/tests/egg/constructor_cost.egg \
  --proofs --dump-proofs /tmp/all-proofs.txt
```

The output starts with `semi-persistent-proof-dump v1` and ends with aggregate
term/nontrivial/step counts. One deterministic proof-path record is written per
e-node. No independent replay checker currently turns this format into a
certificate.

## The measurements

Each prints a table. They are `#[ignore]` because they measure rather than
check, so they need `-- --ignored --nocapture`.

```
# Where each method wins, and that `dec` never leaves the exact solver's region
cargo test -p semi-persistent-egraph --release --test au_hardness \
  hardness_map -- --ignored --nocapture                          # ~1 min

# sat-decoy: the family where the rollout is wrong and exact does not scale.
# Exact times out twice at 60 s each.
cargo test -p semi-persistent-egraph --release --test au_corpus_bench \
  sat_decoy_ladder -- --ignored --nocapture                      # ~5 min

# The ablation at the scale where the configurations separate
cargo test -p semi-persistent-egraph --release --test au_corpus_bench \
  deep_ablation -- --ignored --nocapture                         # ~2 min

# Ground truth: the planted optimum is only the optimum once saturation has
# merged the guard orders. Run this before reading any cell of the study.
cargo test -p semi-persistent-egraph --release --test au_corpus_bench \
  sat_ite_planted_vs_exact_64 -- --ignored --nocapture           # ~3 min

# Where delegation pays, and the zero-gadget control
cargo test -p semi-persistent-egraph --release --test au_delegation \
  delegation_ladder -- --ignored --nocapture                       # ~1 min

# The auto-formalization corpus and the paraphrase operators
cargo test -p semi-persistent-egraph --release --test au_formalization \
  formalization_corpus -- --ignored --nocapture
cargo test -p semi-persistent-egraph --release --test au_formalization \
  paraphrase_operators -- --ignored --nocapture

# The formalizer pilot
cargo test -p semi-persistent-egraph --release --test au_formalizer_pilot \
  formalizer_pilot -- --ignored --nocapture
```

## The engine comparison

```
# Our engine alone under Criterion. No egglog needed.
cargo bench -p semi-persistent-egraph --bench corpus

# Both engines. Clones and builds egglog at the pinned revision.
python3 scripts/egglog-compare/compare.py --label repro --require-stats

# Reusing a checkout instead of cloning
python3 scripts/egglog-compare/compare.py --label repro --require-stats \
  --keep-egglog ~/tools/egglog
```

The runner writes every timed invocation to `repro-samples.csv`, aggregate
statistics to `repro-results.csv`, and a provenance record containing exact
binary SHA-256 hashes, source-tree state, commands, timestamps, machine/tool
metadata, and the protocol. The latest retained complete campaign,
`final-r6`, contains 750 timed samples and records its loaded-host
qualification, but measures a source snapshot based on `8f041483`. Later
implementation changes make it historical evidence rather than a current
performance result.

The corpus harness reports Criterion estimates and bootstrap confidence
intervals; it has no fixed wall-time verdict. For a same-host code comparison,
save a baseline with `--save-baseline NAME` and compare with
`--baseline NAME`. Retain both intervals, the revision, and host state with any
cited result.

The current cross-engine Python runner reports process medians and dispersion,
not Criterion bootstrap intervals. Before publishing a new cross-engine ratio,
move those process invocations under a Criterion harness, run both binaries
from one recorded source state, and retain Criterion's bootstrap confidence
intervals.

## What cannot be reproduced from here

The formalizer pilot's renderings were written by one system. Rerunning the
command reproduces the scoring, not the renderings, and an independent
formalizer's output would be a different measurement.
[`claims.md` section 5](claims.md#5-open-and-retracted-claims) states the
limitation.
