// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! `ContainerId`: opaque per-container identity.
//!
//! Production code uses a process-global atomic counter so each `Vec`
//! instance gets a unique id; `restore` rejects a token whose `container_id`
//! doesn't match. Verus models this with an `external_body` wrapper around the
//! runtime `u64` plus a ghost `id: nat` projection. The exec equality test
//! `eq` is specified to reflect ghost-id equality exactly, which is all the
//! `restore` cross-container guard needs:
//!
//!   token.container_id.eq(self.id)  ⟺  token.container_id.id() == self.id.id()
//!
//! The container check only rejects *cross-container misuse* (a caller error),
//! so it is NOT on the correctness-critical path — restore's reconstruction
//! theorem stands without it. We therefore keep this encoding minimal: the
//! verified guarantee is the faithful reflection above (a matching id provably
//! means the exec check passed, so a token minted by another container is
//! provably rejected — the soundness-relevant direction).
//!
//! ## Uniqueness (migration plan 2.6): width, not a runtime check
//!
//! Foreign-token rejection is only as strong as id uniqueness, and a wrapping
//! counter would eventually hand two live containers the same id. Production's
//! counter is a plain `fetch_add` on an `AtomicU32`, so it wraps silently after
//! 2^32 containers. This crate widens the counter to `u64` — the same algorithm
//! over 4 billion times the range — and, by default, leaves the allocation path
//! otherwise identical to production's. Any *runtime* exhaustion guard is
//! opt-in via the `strict-id-exhaustion` feature, which makes exhaustion fatal
//! instead of wrapping. Debug builds assert unconditionally.
//!
//! ### Why the guard cannot be free (measured)
//!
//! An unconditional guard costs **+21.8%** on `micro/push_only_untracked`.
//! Bisected by instruction-shape probes on the exact loop the bench compiles
//! (write-up in `doc/design/11-layout-parity.md`), counting instructions in the
//! push loop and two markers: `lea` = length recomputed as `base + i`,
//! `shr $0x20` = per-iteration `u32`-fit test.
//!
//! | allocator body                                  | instrs | `lea` | `shr` | vs prod |
//! |-------------------------------------------------|--------|-------|-------|---------|
//! | production `fetch_add` on `AtomicU32`           | 54     | 0     | 0     | —       |
//! | `fetch_add`, `debug_assert!` only  (**default**)| 55     | 0     | 0     | +0.2%   |
//! | `fetch_add` + non-diverging early return        | 58     | 0     | 0     | ~parity |
//! | `fetch_add` + second atomic op (any form)       | 94     | 2     | 1     | +21.8%  |
//! | `fetch_add` + diverging panic                   | 94     | 2     | 1     | +21.8%  |
//! | `fetch_update` CAS loop, no guard at all        | 94     | 2     | 1     | +21.8%  |
//!
//! Three independent triggers, each sufficient on its own: a CAS loop, a
//! diverging (`-> !`) arm branched on the freshly minted id, or a *second*
//! atomic memory operation. Each splits the basic block in `Vec::with_store`,
//! which spills the partially-initialized `Vec` to memory and destroys the fact
//! that a fresh store's length is 0. Downstream, `push` then recomputes length
//! as `base + i` (two `lea` per iteration) instead of reusing the loop counter,
//! and `I::try_from_usize`'s overflow test degrades from a hoisted
//! loop-invariant `cmp` into a per-iteration `mov`/`shr $0x20`/`jne`.
//! `#[cold]`, `#[inline(never)]`, `extern "C"` (nounwind), `abort`-instead-of-
//! `panic`, and branchless `cmov` selects were all measured; none help. The
//! block split is the cost, and one atomic op is the entire budget.
//!
//! This is not a Verus artifact: adding the same diverging guard to
//! *production's* `token.rs` degrades production identically (70 → 86 instrs,
//! `lea=2`, `shr=1`). It is the inherent price of the check.
//!
//! It also only manifests when the push count is a **compile-time constant**,
//! as it is in the bench. With a runtime count — every real consumer, the
//! e-graph included — both sides measure parity even with the guard. That is
//! why the hand-timed harnesses read parity while criterion read +40%: they
//! compile different loops, and each was right about its own.
//!
//! Two rejected alternatives worth recording. An *absorbing poison band* (top
//! 2^32 reserved, counter clamped back on overflow) is sound but needs a second
//! atomic store to be absorbing — without the clamp a plain `fetch_add` climbs
//! through the band and wraps to live low ids — and the second store is exactly
//! what costs 21.8%. A *fail-closed* `eq` (`raw == other.raw && raw <
//! THRESHOLD`) measures at parity but is **unsound here**: `eq` is
//! `external_body` with `ensures b == (self.id() == other.id())`, so returning
//! `false` for `self.eq(self)` would make an assumed postcondition false.
//!
//! The allocation path is factored through `next_id_from` so unit tests can
//! park a counter at the boundary rather than iterating 2^64 times.
//!
//! Note: a fresh-id *generator* IS expressible in Verus if we later want
//! distinctness as a proved (not assumed) property — a `tracked` ghost
//! monotone counter threaded as a linear resource and advanced on each `new()`
//! (`ensures fresh > all prior`), no global mutable static required. Deferred
//! because the check is off the critical path. See
//! `doc/design/02-fork-history.md` §4(c).

use vstd::prelude::*;

verus! {

/// Opaque per-`Vec` identity. The runtime payload is a `u64` (production used
/// u32; widened for uniqueness headroom -- see the module doc, and note the
/// runtime no-wrap trap is opt-in via `strict-id-exhaustion`, not
/// unconditional); the ghost `id` is its abstract value, used in specs.
#[verifier::external_body]
#[derive(Clone, Copy)]
pub struct ContainerId {
    raw: u64,
}

impl ContainerId {
    /// Ghost projection: the abstract identity.
    pub uninterp spec fn id(self) -> nat;

    /// Exec equality, reflecting ghost-id equality exactly. This is the only
    /// observation `restore`/`is_valid_token` make on a `ContainerId`.
    #[verifier::external_body]
    #[inline(always)]
    pub fn eq(self, other: ContainerId) -> (b: bool)
        ensures b == (self.id() == other.id())
    {
        self.raw == other.raw
    }

    /// Mint a fresh id via atomic increment (see module doc for the exhaustion
    /// posture). `external_body`: the returned id's
    /// ghost value is unconstrained here — distinctness from a specific other
    /// container, when needed, is supplied by the caller as a hypothesis.
    /// Marked so each call site sees an opaque, independent id.
    #[verifier::external_body]
    pub fn new() -> ContainerId {
        ContainerId { raw: next_id_from(&NEXT) }
    }
}

} // verus!

// prod-parity: production derives `Debug` on `ContainerId` (`token.rs`); the
// consumer needs it transitively (tokens embed a `ContainerId`, and structs
// holding tokens derive `Debug`). Manual because the struct is `external_body`.
impl core::fmt::Debug for ContainerId {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_tuple("ContainerId").field(&self.raw).finish()
    }
}

/// One past the last id the allocator may hand out. `u64::MAX` is reserved so
/// the boundary can be observed without the counter having to actually wrap.
pub(crate) const ID_LIMIT: u64 = u64::MAX;

/// The process-global counter behind `ContainerId::new`.
///
/// Outside `verus!{}` deliberately. Declared inside the `external_body` `new`,
/// the `verus!` macro still walks the body and tries to annotate the `static`,
/// which warns "verus-related attribute has no effect because item is already
/// marked external" — the annotation is redundant, not wrong, but it is noise on
/// every build. Verus has no ghost view of a `static` either way; the id's
/// uniqueness rests on the `u64` width, not on proof (see `next_id_from`).
static NEXT: core::sync::atomic::AtomicU64 = core::sync::atomic::AtomicU64::new(1);

/// Allocation from a shared counter: returns the current value and advances it.
///
/// Deliberately production's algorithm — a single `fetch_add`, no CAS, no second
/// atomic op, no diverging arm — because each of those costs 21.8% on
/// constant-count push loops (module doc). Under `strict-id-exhaustion` the
/// unconditional trap is restored, paying that cost for a fatal-instead-of-
/// wrapping exhaustion. `debug_assert!` covers debug builds either way, so the
/// boundary is exercised by the test suite regardless of features.
///
/// Factored out of `ContainerId::new` so tests can park a counter at the
/// boundary rather than iterating 2^64 times (plan 2.5: forged-state /
/// exhaustion cases are in-module unit tests).
///
/// Outside `verus!{}`: this is the trusted allocator behind the `external_body`
/// `new` (trust group A). Its no-reuse property rests on the `u64` width, not on
/// proof: 2^64 allocations is ~584 thousand years at a million containers per
/// second.
fn next_id_from(counter: &core::sync::atomic::AtomicU64) -> u64 {
    use core::sync::atomic::Ordering;
    let prev = counter.fetch_add(1, Ordering::Relaxed);
    debug_assert!(
        prev < ID_LIMIT,
        "ContainerId allocator exhausted (2^64 ids): the counter has wrapped and \
         ids may now be reused, which would let one container accept another's token"
    );
    // `>=` rather than `==`: ID_LIMIT is a named boundary, and the guard should
    // stay correct if it is ever lowered below u64::MAX. clippy flags the
    // comparison as always-false only because the two happen to coincide today.
    #[cfg(feature = "strict-id-exhaustion")]
    #[allow(clippy::absurd_extreme_comparisons)]
    if prev >= ID_LIMIT {
        panic!("ContainerId allocator exhausted (2^64 ids): refusing to wrap and reuse ids");
    }
    prev
}

// Production-surface parity: derived equality on the raw counter value (the
// inherent `eq` is the verified spelling; this is the operator form).
impl PartialEq for ContainerId {
    #[inline(always)]
    fn eq(&self, other: &Self) -> bool {
        self.raw == other.raw
    }
}
impl Eq for ContainerId {}

#[cfg(test)]
mod tests {
    use core::sync::atomic::AtomicU64;

    /// The boundary is observable: allocating at the limit trips the guard
    /// (debug builds always; release builds under `strict-id-exhaustion`). The
    /// terminal-state-injection test from plan 2.5/2.6 — we park the counter at
    /// the boundary rather than iterating 2^64 times.
    ///
    /// `cfg`-gated on the guard being live: with the guard compiled out in a
    /// release test run, `next_id_from` wraps by design and there is nothing to
    /// observe.
    #[test]
    #[cfg(any(debug_assertions, feature = "strict-id-exhaustion"))]
    #[should_panic(expected = "ContainerId allocator exhausted")]
    fn exhausted_counter_traps_instead_of_wrapping() {
        let counter = AtomicU64::new(super::ID_LIMIT);
        let _ = super::next_id_from(&counter);
    }

    /// Every id below the limit is allocated normally; only the wrap is refused.
    #[test]
    fn last_valid_id_still_allocates() {
        let counter = AtomicU64::new(super::ID_LIMIT - 1);
        assert_eq!(super::next_id_from(&counter), super::ID_LIMIT - 1);
    }

    /// The limit is the full `u64` range: 4 billion times production's 2^32
    /// (`containers/src/token.rs` uses an `AtomicU32`), which is the actual
    /// uniqueness argument now that the runtime guard is opt-in.
    #[test]
    fn limit_is_full_u64_range() {
        assert_eq!(super::ID_LIMIT, u64::MAX);
        assert!(super::ID_LIMIT / u64::from(u32::MAX) > 4_000_000_000);
    }

    /// Sequential allocations are distinct and monotone.
    #[test]
    fn ids_distinct_and_monotone() {
        let counter = AtomicU64::new(1);
        let a = super::next_id_from(&counter);
        let b = super::next_id_from(&counter);
        let c = super::next_id_from(&counter);
        assert!(a < b && b < c);
    }
}
