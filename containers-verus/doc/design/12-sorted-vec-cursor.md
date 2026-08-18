<!--
Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
SPDX-License-Identifier: Apache-2.0
-->
# The Sorted-Vec Cursor: a Verified Galloping Seek

Every chapter before this one verifies a *container*. This one verifies an
*algorithm over a container the consumer already owns*: the galloping seek in
`egraph/src/index.rs::SortedVecCursor`, which is the cursor every leapfrog join in
the e-graph runs on. It is the first proof in this crate whose subject is not a
data structure but a piece of the query engine one level up, which is why it is
short: there is no representation invariant to establish, no arena, no
semi-persistence. There is one loop invariant, and everything follows from it.

## 1. Why this seek and not another

Leapfrog join is a sequence of `seek`s across sorted key lists. It has one
correctness requirement of its cursors, and it is not "seek is fast": it is that
**a seek must not step past a key that could have matched**. A cursor that
overshoots by one produces a join that silently returns fewer rows. Nothing
panics, no invariant trips, and the answer is wrong: the failure mode that
formal verification is actually for.

Production's `seek` is where that risk concentrates, because it is the only place
in the join layer doing non-trivial index arithmetic:

```rust
// egraph/src/index.rs, abridged
pub fn seek(&mut self, target: G) {
    if self.pos >= n || data[self.pos] >= target { return; }   // already satisfied
    let mut step = 1usize;
    let mut lo = self.pos;
    while lo + step < n && data[lo + step] < target {          // gallop
        lo += step;
        step *= 2;
    }
    let hi = (lo + step).min(n);
    self.pos = lo + 1 + data[lo + 1..hi].partition_point(|x| *x < target);
}
```

A doubling ladder, a clamp, and a bisection over a *computed* window: three
places for an off-by-one, and one (`lo + step`) for an overflow. The galloping
form exists for a measured reason: `doc/perf-results/E7-galloping-seek.md`
records 4-6% end-to-end and 70-97% on the seek itself, because 56-67% of AC-row
seeks advance by ≤1 against a remainder of 2^4.7..2^7.9, so `O(log d)` in the
distance advanced beats `O(log rem)` in the remainder. The optimization is
keeping its gain; this chapter is about it also being right.

## 2. What is proven

`src/sorted_vec_cursor.rs`, verified module `sorted_vec_cursor`: **14 facts, 0
errors, 0 `external_body`, 0 `admit`/`assume`.**

The model is the slice's ids projected to nats in slice order (`nat_model`), and
`cursor_wf` asks for two things: the model is strictly sorted, and `pos <= len`.
Strict sortedness is not a convenience: it is the representation invariant of the
`SortedVec` being cursored (`IndexStore::build_from` sorts and dedups each
bucket), and it is what lets this module reuse the B+tree's seek vocabulary
unchanged.

`seek`'s postcondition is the whole soundness story:

```rust
ensures
    self.cursor_wf(),
    self.model() == old(self).model(),
    ({ let ti = seek_target_idx(old(self).model(), target.id_nat());
       self.idx() == if old(self).idx() >= ti { old(self).idx() } else { ti } }),
```

`seek_target_idx` is **`bplus.rs`'s spec function, not a new one**: the count of
model keys strictly below the target. Both verified cursors on the leapfrog
surface land on the same spec, which is what makes them substitutable at the
`SortedCursor` boundary rather than merely similarly shaped:

| | seek contract |
|---|---|
| `BPlusCursor::seek` | `idx' == seek_target_idx(model, t)` |
| `SortedVecCursor::seek` | `idx' == max(idx, seek_target_idx(model, t))` |

The `max` is the algorithm, not proof slack. Production returns immediately when
the cursor already satisfies the target (24.7% and 30.6% of seeks on the `ac6`
and `plain7` semi-naive rows do not move at all, because the `Difference`
combinator seeks both sides to the same key), so a cursor positioned past the
target must stay put. Forward-only is what leapfrog needs, and it is what
makes monotonicity hold unconditionally rather than as a side condition.

Four named theorems turn that one postcondition into the four statements a reader
of the join code actually reasons with. They are corollaries, stated separately
because the postcondition is phrased as a *count*, and "lands on the first key ≥
t" / "skipped nothing" is exactly the step that should be proven once here rather
than re-derived at each call site:

| theorem | statement |
|---|---|
| `theorem_seek_lands_on_first_ge` | positioned ⟹ key ≥ t, and every earlier key < t; exhausted ⟹ no key reaches t |
| `theorem_seek_never_skips` | every index passed over held a key < t; and if t is present, the cursor stopped *on* it |
| `theorem_seek_is_monotone` | `pos` never decreases and stays ≤ `len` |
| `theorem_step_enumerates_tail` | stepping from any position yields the strictly increasing tail |

Plus what needs no theorem because Verus discharges it as a matter of course, and
which is the part a property test can only sample: **every slice index is in
bounds and no arithmetic overflows**, for every slice length and every target.

## 3. The one invariant that carries the gallop

```rust
while step < n - lo && data[lo + step].lt(target)
    invariant
        self.pos <= lo < n,
        model[lo as int] < t,        // <-- this one
        1 <= step <= lo + 1,
```

`model[lo] < t` is the load-bearing fact. It is what makes the bisection window
`lo+1 .. hi` sound rather than `lo .. hi`: index `lo` is *already known* to be
below the target, so excluding it cannot skip the answer. That also explains a
result from the production side: mutating the bisection to the closed window
`lo..hi` survives all 12,000 property-test cases and the full 596-test lib suite,
because it is a genuine equivalence, not a coverage gap. Here that is settled
rather than inferred: the mutation re-verifies clean (§5, M3′).

`1 <= step <= lo + 1` is the ladder bound. `step` starts at 1 with `lo >= 0`, and
each iteration advances `lo` by the old `step`, so `2·step <= lo' + 1`, which
with `lo < n` gives `step <= n` and discharges `step * 2`.

The bisection then carries the two halves of a split point and `a` is shown to
split the *whole* model, at which point `lemma_seek_target_idx_unique` (also
`bplus.rs`'s, unchanged) identifies it with `seek_target_idx`. The proof reuses
`lemma_seek_target_idx_split` the same way. Nothing about the seek vocabulary had
to be generalized to accept a second cursor, which is the useful part of the
result: the B+tree chapter's spec functions turned out to be about *sorted
sequences*, not about B+trees.

### One deliberate spelling difference from production

Production's ladder guard is `lo + step < n`; the verified one is the equivalent
`step < n - lo`, and `hi = (lo + step).min(n)` becomes the `if` computing the same
value. Both spellings are overflow-free (the invariant bounds `lo + step` by
`2n`, and a Rust slice length is at most `isize::MAX`, so `2n` fits), but that
argument needs the slice-length bound as an extra axiom, whereas `n - lo` is safe
from `lo < n` alone. The verified spelling is the one whose overflow-freedom comes
from the invariant rather than from a fact about slices. Same instruction count,
one less thing to trust.

## 4. Two frictions worth recording

**A loop body assumes only the invariants.** The exec comparisons (`IndexLike::lt`)
have `ensures` phrased in `lt_spec` (hence `as_nat`), while the model is phrased in
`id_nat`. `DenseId::lemma_as_nat_is_id_nat` bridges them, and calling it before
the loop is *not enough*: Verus gives the loop body only what the invariants say,
so `target.as_nat() == t` has to be an invariant clause itself. Three failed
proof attempts collapsed to that one line. (The same shape as `bplus_search`'s
need for `lemma_order_is_as_nat`: Verus will not unfold a default-bodied trait
spec method through a type parameter.)

**Spec and proof items cannot be `use`d at module top level.** `seek_target_idx`
and the two lemmas are erased entirely by the `verus!` macro in a plain cargo
build, so a top-level `use crate::bplus::seek_target_idx` fails to resolve there
even though it verifies fine. They are referenced by full path inside `verus!{}`,
which is what `bplus.rs` already does for the same reason.

## 5. Runtime tests, and what mutation testing says

`tests/sorted_vec_cursor_proptest.rs`: 10 tests, 12,000 generated cases. Under
plain `cargo test` the Verus contracts are **erased**, so this is the same
defense-in-depth posture as `bplus_contract_fuzz`: it catches an exec body
changed without re-running Verus, and it checks the verified cursor against the
*same* linear-scan oracle and the same generators as production's own
`mod seek_props`, which is what makes "the verified cursor models the production
one" a tested claim rather than an asserted one.

Both id widths are covered because production's are: `DenseId31` mirrors `ENodeId`
(31-bit), `DenseId63` mirrors `ENodeId64` (63-bit).

The mutation results are the interesting part, because they let the proof and the
tests be compared on the same seven mutations. Production's numbers are from
`egraph`'s suite; the verified column is whether Verus still reports 0 errors:

| mutation | production tests | verified module |
|---|---|---|
| M1 gallop guard `<` → `<=` | 36 fail | **rejected** |
| M2 halve the `hi` window | 57 fail | **rejected** |
| M3 bisect `lo..hi` instead of `lo+1..hi` | **survives** | **rejected** (invariant `lo+1 <= a`) |
| M3′ same, with the invariant relaxed to `lo <= a` | survives | **verifies clean** |
| M4 early-return `>=` → `>` | 16 fail | **rejected** |
| M5 `step *= 2` → `step += 1` | **survives** | **verifies clean** |
| M6 drop the `min(n)` clamp | 24 fail | **rejected** (slice-index precondition) |
| M7 drop the gallop's upper bound | 45 fail | **rejected** (precondition + overflow + `decreases`) |

Production counts are out of `egraph`'s 596 lib tests, re-measured after this
chapter's property tests were added; E7's table records the same mutations against
the smaller pre-proptest suite, which is why its numbers are lower.

Three rows are worth reading twice.

**M5 verifying clean is a confirmation, not a hole.** `step += 1` turns the gallop
into a linear scan: same answer, worse asymptotics. A soundness proof *should*
accept it, and the production suite surviving it is correct too. Two independent
methods agreeing that a mutation is perf-only is stronger evidence than either
alone.

**M3 and M3′ together are what a proof adds over a test.** The test suite survives
M3 and cannot tell you why. Verus rejects it against the invariant as written, and
then accepts it once the invariant is relaxed to match, which decides the open
question: `lo..hi` is genuinely equivalent, and the production code's survival was
a correct survival rather than a coverage gap. That is a fact about the algorithm
that 12,000 test cases could suggest and only the proof could settle.

**M6 and M7 are the guarantee that motivated this chapter.** Both are
out-of-bounds mutations, and both are rejected as *precondition failures on the
slice index*, not as a wrong answer discovered downstream. The property tests
catch them by sampling into the bad region; the proof catches them by not
admitting the region exists.

## 6. Delegation and the consumer boundary

`src/sorted_cursor.rs` holds the plain-Rust `SortedCursor` trait: the
consumer-facing trait-object boundary for leapfrog composition, deliberately
outside `verus!{}` (trust ledger group E, delegation glue). Both verified cursors
now impl it, each as a one-line delegation to verified inherent methods.

`SortedVecCursor`'s impl adds exactly one thing over `BPlusCursor`'s: an
`is_valid` guard in `key` and `step`. That is because the verified `key` takes
`idx() < model().len()` as a *precondition* rather than returning `Option`, since
production's does (`data[pos]`, which panics past the end); the guard is what
discharges it at the `Option`-returning trait boundary.

One asymmetry the trait cannot express, recorded at both impls: `BPlusCursor::seek`
is absolute and `SortedVecCursor::seek` is forward-only. Leapfrog only ever seeks
forward, so they agree on every call it makes, but a consumer seeking *backwards*
through the trait would see different behavior from the two, so the trait's
contract is written to license only the forward-only reading.

## 7. Status and scope

**Verified:** the cursor's full surface (`new`, `pos`, `is_valid`, `key`, `step`,
`seek`) with the four soundness theorems. 14 facts, no trusted items, no
`admit`/`assume`. Verified as part of `cargo verus verify`.

**Not claimed:** the `O(log d)` cost bound is not proven, only measured
(`doc/perf-results/E7-galloping-seek.md`): the same position as the B+tree's
per-seek node-visit count ([Chapter 10](10-bplus-tree.md) §3c). The proof
establishes that the gallop is *sound*, not that it is *fast*; if it were slow the
proof would still go through, which is exactly why the perf ledger is a separate
artifact from this one.

**In production:** `egraph` runs this cursor. `egraph/src/index.rs`
re-exports the `SortedVecCursor` type and `egraph/src/leapfrog.rs`
re-exports the `SortedCursor` trait; both are foreign to `egraph`, so this
crate supplies the only impl and the orphan rule forbids a second one. The
correspondence between the verified cursor and the engine's join algorithm
is therefore maintained *by compilation*, not just by the shared oracle of
§5; the oracle and generators remain as the runtime guard on the erased
build, where `requires`/`ensures` are gone.

§7a records the measured cost of the foreign-cursor indirection: seeks
substantially faster, end-to-end unchanged, which is why the design is
justified on soundness rather than speed.

## 7a. Cost of the foreign-cursor indirection, measured

Verification and performance pull in opposite directions often enough that "the
verified one is faster" deserves evidence rather than a claim. The numbers below
come from a **single binary** holding both algorithms, alternating which runs
first, over 9 reps at 1M keys (medians). A cross-binary criterion A/B was tried
first and discarded: a production-vs-production control run came back at ±0.2%,
which established that run-to-run noise was *not* the explanation and sent the
investigation to codegen instead.

| shape | prod (ns) | verified | Ord→raw compare only | `partition_point`→loop only |
|---|---|---|---|---|
| stride/1 | 7 770 | −48% | −28% | −43% |
| stride/16 | 60 930 | −65% | −9% | −71% |
| stride/256 | 206 751 | −77% | −33% | −80% |
| full sweep | 1 899 327 | −49% | −29% | −43% |

Two independent differences, separated by holding one fixed and varying the other:

1. **The bisection loop, which is the dominant factor.** Production called
   `data[lo+1..hi].partition_point(|x| *x < target)`. The verified version cannot:
   there is no way to state a loop invariant *through* std's `partition_point`, so
   the proof forced an explicit `while a < b` bisection. That hand-written loop
   compiles better than std's here: swapping only this, with the comparison held
   at production's, accounts for −43% to −80%.
2. **The comparison.** These ids steal the MSB as a capture tag, so `Ord::cmp`
   masks *both* operands (`(raw & MASK).cmp(&(other.raw & MASK))`). The verified
   code compares through `IndexLike::lt`, a bare `raw < raw`, sound because a
   `SortedVec` holds clean ids. Worth a few points to −33%.

A deterministic probe-count harness confirms the two do **identical work**:
byte-for-byte equal slice-load counts and equal final positions on every shape
above. The win is entirely codegen, not algorithm, which is also why it does not
contradict [E7](../../../doc/perf-results/E7-galloping-seek.md), whose
gallop-vs-binary-search comparison is about probe counts.

**End-to-end: unchanged.** `acsite` 1.94–1.97 ms both sides; `complsite`
2.415–2.435 ms verified vs 2.413–2.415 ms production, checksums identical
(17400, 127200). This is the ratio E7 already established: a 70-97% seek win
moved end-to-end 4-6%, because seek is a small share of saturation time, and a
2-3x win on a small share is still a small share. The swap is a soundness change
that happens not to cost anything, and it should be defended on that basis.
