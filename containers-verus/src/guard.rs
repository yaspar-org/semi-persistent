// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Runtime precondition guards for the public container API.
//!
//! The containers are verified: a Verus-checked caller PROVES every public
//! method's `requires` clause, so it never trips a guard. But the crate is also
//! usable from ordinary (unverified) Rust, where nothing forces the caller to
//! satisfy those preconditions, and the erased `requires` offers no runtime
//! protection. A few preconditions, if violated by such a caller, would not
//! fault cleanly: an index-type / fork-history counter would silently wrap
//! (`as u32` truncation) and corrupt the structure rather than panic.
//!
//! [`check_precondition`] closes that gap. It is `external_body` with
//! `requires cond`, so:
//!   - a verified caller discharges `cond` from the method's own `requires`;
//!     the runtime branch is provably dead for them (zero behavioral change);
//!   - an unverified caller who violates the precondition gets a descriptive
//!     panic at the call site instead of silent corruption.
//!
//! These guard the overflow / capacity preconditions only (the silent-wrap
//! hazards). Plain out-of-range index accesses (`get`/`set`/`pop`) already
//! panic via the inner `Vec`'s bounds check, so they need no extra guard.

use vstd::prelude::*;

verus! {

/// Trap a violated public-API precondition with a descriptive message.
///
/// `requires cond`: a verified caller proves this, so the body's check is dead
/// for them. `external_body` lets the body use the panic-formatting machinery
/// (which Verus does not model) and keeps the function opaque to the verifier.
#[verifier::external_body]
#[inline(always)]
pub fn check_precondition(cond: bool, msg: &str)
    requires
        cond,
{
    if !cond {
        panic!("containers-verus: precondition violated: {}", msg);
    }
}

/// Total refusal: diverges unconditionally, with NO `requires` — the total
/// shell's panic arm (total-API plan phases 4/5). Where `check_precondition`
/// serves verified callers (who prove `cond` and get a dead check),
/// `refuse` serves the total public surface: a function that has already
/// BRANCHED on its would-be precondition calls this in the violating arm, so
/// its signature carries no obligation and its panic is documented behavior,
/// matching production's panic-on-misuse parity. `external_body` only for
/// the unmodeled panic machinery; the `!` return means nothing is assumable
/// from it (there is no post-state).
#[verifier::external_body]
#[inline(never)]
pub fn refuse(msg: &str) -> !
{
    panic!("containers-verus: {}", msg);
}

} // verus!

/// The same trap, callable from inside `external_body` diagnostic code where
/// no proof context exists (so no `requires`). Outside `verus!{}` — never
/// visible to the verifier; used only by debug-build mirrors of spec-level
/// preconditions (e.g. `CircularList::splice`'s different-rings walk).
pub fn check_precondition_erased(cond: bool, msg: &str) {
    if !cond {
        panic!("containers-verus: precondition violated: {}", msg);
    }
}
