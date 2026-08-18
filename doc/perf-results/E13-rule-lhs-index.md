<!--
Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
SPDX-License-Identifier: Apache-2.0
-->
# E13: index AC rewrite rules by LHS class (C4): **accepted**

**Verdict: accepted. −30.4% on `accompl32` and −46.8% on `accompl64`, reproducing
within 0.4 points across three runs, confirmed standalone at −47.0% with an
identical checksum.** The largest single win of the campaign.

The three normalize loops (`normalize_ms_into`, `normalize_set_into`,
`normalize_nilpotent_into`) tested every rule in the table on every rewrite step.
They now consult an inverted index keyed by each rule's LHS-minimum class, and
test only the rules a class actually present in the host monomial could match.

## The plan's fix was the wrong half

C4 was framed as "the rule scan restarts from index 0 after every rewrite", with
the fix being to resume where the previous scan left off. Instrumentation says
that addresses less than a quarter of the cost, and is unsound besides.

Per-call decomposition on `accompl32`:

```
tests/call 188.4  =  restart-scans 43.6 (23%)  +  final failing scan 144.8 (77%)
```

**77% of all subset tests are the last scan**: the one that proves no rule
applies and ends the loop. No resume strategy removes that scan; it has to visit
every rule by definition. And resuming is not even correct for the other 23%: a
rewrite step replaces `lhs` with `rhs` in the host, and the added `rhs` elements
can make an *earlier* rule applicable, so a scan that resumes past that rule
returns a non-normal form.

What is left is C4's other half (index the rules by LHS content), which
addresses the 77% and the 23% together, because it shrinks every scan rather than
skipping some of them.

## The gate, and the premise

C4's gate was "count `multiset_subset` calls per rewrite step first; if the mean
rule count is under ~8, close it". Measured with a temporary probe in
`multiset.rs` driven by a `complsite`-shaped harness:

| workload | calls | mean \|rules\| | subset tests | tests/call | tests/rewrite |
|---|---|---|---|---|---|
| `accompl32` build |  5 789 | 144.8 |  1 090 690 | 188.4 | 197.4 |
| `accompl32` sat   |  2 423 | 154.9 |    507 430 | 209.4 | 179.7 |
| `accompl64` build | 11 965 | 296.3 |  4 577 666 | 382.6 | 403.4 |
| `accompl64` sat   |  5 015 | 314.9 |  2 119 510 | 422.6 | 365.4 |
| `accompl128` build| 24 317 | 599.4 | 18 746 242 | 770.9 | 815.2 |
| `accompl128` sat  | 10 199 | 634.9 |  8 658 358 | 848.9 | 736.8 |

Mean |rules| is 145-635 against a threshold of 8, and it scales linearly with
`pairs`, so the scan is the term that grows with problem size.

The complementary measurement is how much of that is skippable. Probing
`out.binary_search_by(|p| p.0.cmp(&g0)).is_err()` for `g0 = rule.lhs[0].0`:

| workload | tests whose LHS-minimum is absent from the host |
|---|---|
| `accompl32` | 1 020 904 / 1 090 690 = **93.6%** |
| `accompl64` | 4 428 904 / 4 577 666 = **96.8%** |
| `accompl128` | 18 439 528 / 18 746 242 = **98.4%** |

**The prune rate rises with table size**, which is what makes this an asymptotic
improvement rather than a constant factor: the bigger the problem, the larger the
fraction of the scan that was wasted.

The other half of why this is so lopsided is that **the monomials are tiny**:
mean 2.46 classes, max 5, essentially flat across all three sizes. A host with
2.5 classes cannot possibly match more than a handful of a 635-rule table, and
the old loop tested all 635.

## Where the time actually was

Before writing code, the time was attributed by call site, because completion has
two and they have very different amortization properties:

| workload | inter-reduction (A′) | critical-pair loop (B) |
|---|---|---|
| `accompl32`  | 0.090 ms (5.6%) | 0.973 ms (**60.8%**) |
| `accompl64`  | 0.303 ms (5.8%) | 3.413 ms (**65.7%**) |
| `accompl128` | 1.228 ms (6.4%) | 13.862 ms (**71.7%**) |

Two thirds of completion time is one loop, and its share grows with size. That
loop's rule table is **already hoisted outside it** (the `Bclose` hoist, perf doc
§2), so an index built alongside the table is amortized over thousands of
normalizations and costs nothing per call.

Inter-reduction is the opposite: it refills a *different* rule slice per target
(each target is normalized by every rule but its own), so an index there would be
rebuilt per target with nothing to amortize over, and it is 6% of the time.

Hence `NfRules`, which carries a rule slice plus an *optional* index: the
critical-pair loop passes `NfRules::indexed`, inter-reduction passes
`NfRules::linear`. Splitting this way rather than indexing both is the whole
reason the change is a win and not a wash.

## Design

`NfIndex` is a CSR table (`keys` ascending and distinct, `starts` the offsets,
`order` the rule positions grouped by key), so it is three allocations regardless
of table size, and `rebuild` reuses them across rounds.

Two properties matter:

**Soundness needs only a fixed LHS member as the key.** Containment implies every
LHS class is present in the host, so a probe over the host's classes reaches the
rule's bucket whichever member was chosen. A mutation keying on the LHS *maximum*
instead of the minimum passes every test, correctly: the minimum is chosen for
bucket balance, worth 1.8% (`accompl64` 2.507 ms vs 2.552 ms), because
completion's rules are minted in class-id order so their maxima cluster in the
recently-added range while their minima spread.

**The selected rule must be the same one the linear scan would pick**, not merely
*a* rule that applies. Which rule fires determines the normal form reached, so
candidates are gathered and then visited in ascending rule position. This is the
one property that would silently change behavior if wrong, so it has a dedicated
test and two mutations below.

## Numbers

`saturate_bench` against `E13-before` (= `bd968b7`), three runs:

| bench | run 1 | run 2 | run 3 | absolute after |
|---|---|---|---|---|
| `saturate/accompl32` | **−30.7%** | **−30.5%** | **−30.4%** | 1.041 ms (was 1.500) |
| `saturate/accompl64` | **−46.8%** | **−46.7%** | **−46.8%** | 2.576 ms (was 4.840) |
| `saturate/plain7/naive` | +0.2% | −0.2% | +1.6% | 13.2 ms |
| `saturate/plain7/semi` | +0.2% | −1.2% | +1.0% | 7.4 ms |
| `saturate/ac6/naive` | −0.2% | −0.4% | +0.4% | 2.36 ms |
| `saturate/ac6/semi` | −0.3% | −0.1% | −0.0% | 1.24 ms |
| `saturate/ac10/naive` | −0.5% | −0.3% | +1.3% | 77.8 ms |
| `saturate/ac10/semi` | +0.0% | −0.1% | −0.0% | 49.6 ms |

The two completion rows reproduce within 0.4 points across three runs, far
outside the ±1% rebuild band and outside the ±4-5% AC artifact band protocol item
7 warns about. Every other row is inside the noise: they run with no rules and
never enter completion, so the mechanism is provably absent, and the numbers agree.

Standalone confirmation, min of 200 reps:

| | baseline | indexed | |
|---|---|---|---|
| `accompl64` | 4.7423 ms | 2.5148 ms | **−47.0%** |

−47.0% standalone against −46.8% in criterion, checksum identical (127200), so
unlike E6 and E7, whose completion-row deltas were artifacts, this one is real on
both instruments.

Mechanism count per protocol item 5, `multiset_subset` calls during `saturate`:

| workload | before | after | |
|---|---|---|---|
| `accompl32`  |    507 430 |    99 888 | **−80.3%** |
| `accompl64`  |  2 119 510 |   347 120 | **−83.6%** |
| `accompl128` |  8 658 358 | 1 271 664 | **−85.3%** |

The reduction grows with size, matching the prune-rate table. It falls short of
the 93.6-98.4% ceiling because inter-reduction stays linear by design: the
residual is that 6% site, not a defect in the index.

## Correctness

`cargo test --workspace --release`: 81 test binaries, 0 failures. `cargo fmt
--all --check` and `cargo clippy --release --all-targets` clean.

Five tests added, the substantive one being an exhaustive comparison: every
multiplicity vector over 6 classes with counts 0..=2 (729 hosts), each normalized
both ways by all three normalizers (multiset, idempotent, nilpotent at orders 2
and 3), asserting the results are equal. The rule table is built so LHS-minima
repeat and disagree with position order, so the order-preservation property is
actually exercised rather than accidentally satisfied.

Mutation-checked:

| mutation | result |
|---|---|
| candidates returned in key order (drop the position sort) | **1 test fails** |
| probe only the host's first class | **1 test fails** |
| skip the confirming containment test | **1 test fails** |
| key on the LHS maximum instead of the minimum | **passes, correctly** |

The last one is not a coverage gap: any fixed LHS member is a sound key, so a
test that failed here would be asserting something untrue. It is a performance
choice, and it is measured above rather than tested.

## Reproduce

```bash
export MALLOC_MMAP_THRESHOLD_=65536
cd egraph
cargo bench --bench saturate_bench -- --save-baseline E13-before   # at bd968b7
# apply the change, then
cargo bench --bench saturate_bench -- --baseline E13-before
cargo run --release --example complsite
```

The instrumentation was temporary and is not retained. To recreate: count
`multiset_subset` entries in a thread-local, wrap the normalize loop body in an
`Instant`, tag calls by call site with a thread-local set from the two loops in
`egraph.rs`, and drive it from a `complsite`-shaped harness that reports the
`ac_completion` build phase and the `saturate` phase separately.
