// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Acceptance criteria: index construction and index arithmetic are bounded by the id's
//! *payload* capacity, and crossing that bound is always observable.
//!
//! A `DenseId` is one bit narrower than the word carrying it — the MSB is the inline
//! capture flag — so there are two different ceilings in play, and every guard here is
//! about not confusing them:
//!
//! * `Self::MAX` (`0x7f` for a 7-bit id), the largest id that exists;
//! * the backing word's max (`0xff` for `u8`), which is not a capacity at all.
//!
//! Checking against the second admits a whole band of values that have no id, and
//! narrowing to the word *before* comparing is worse still: it wraps out-of-range inputs
//! back into range and reports success, so two distinct positions receive the same id.
//! That is the failure this file exists to rule out, because it is silent — no panic, no
//! `None`, just an index that quietly means something else.
//!
//! `define_id7!` is what makes this testable at all. Its ceiling is 128, so every
//! boundary below is reached with a literal; at 31 bits the same cases need four billion
//! allocations.

use semi_persistent_containers::{DenseId, IdFactory, IndexLike, define_id7, define_id15};

define_id7! { struct Tiny / StoredTiny, "t"; }
define_id15! { struct Small / StoredSmall, "s"; }

/// The regression: `try_from_usize` narrowed to the backing word before range-checking,
/// so inputs that wrapped back under the mask were accepted. `256 as u8` is `0`, which is
/// `<= 0x7f`, so a 7-bit id reported success and returned id 0 — aliasing position 256
/// onto position 0. Same shape at 15 bits with `65536 as u16`.
#[test]
fn try_from_usize_does_not_wrap_into_range() {
    // One past the ceiling: rejected before and after the fix (no wrap yet).
    assert_eq!(Tiny::try_from_usize(128), None);
    // A multiple of the backing word's range: this is the one that used to alias.
    for n in [256, 257, 384, 512, 1 << 20] {
        assert_eq!(
            Tiny::try_from_usize(n),
            None,
            "a 7-bit id must reject {n}, not narrow it into range"
        );
    }
    assert_eq!(Small::try_from_usize(1 << 15), None);
    for n in [1usize << 16, (1 << 16) + 1, 1 << 32] {
        assert_eq!(
            Small::try_from_usize(n),
            None,
            "a 15-bit id must reject {n}, not narrow it into range"
        );
    }
}

/// Accepting a value must return *that* value. This is the property the wrap violated:
/// it returned `Some`, so the caller had no way to learn the index had changed meaning.
#[test]
fn accepted_indices_round_trip_exactly() {
    for n in 0..=127usize {
        let id = Tiny::try_from_usize(n).expect("every index below the ceiling exists");
        assert_eq!(id.as_usize(), n);
        assert_eq!(DenseId::to_usize(id), n);
    }
    assert_eq!(Tiny::MAX.as_usize(), 127);
    assert_eq!(Tiny::MIN.as_usize(), 0);
}

/// `from_usize` is the infallible spelling, so out of range must panic. It used to cast
/// first and hand the already-wrapped value to an assertion that then passed.
#[test]
#[should_panic(expected = "exceeds range")]
fn from_usize_panics_instead_of_aliasing() {
    let _ = Tiny::from_usize(256);
}

/// `IdFactory` exhausts at the id's capacity, not the backing word's.
///
/// It guarded with `T::Index::try_from_usize`, i.e. against `u8`, so for a 7-bit id it
/// admitted 0..=255 and only reported exhaustion at 256. The 128 values in between passed
/// the guard and then panicked inside `from_usize` — from `try_alloc`, whose whole purpose
/// is to report exhaustion as `None`.
#[test]
fn factory_exhausts_at_the_id_capacity_not_the_word() {
    let mut f: IdFactory<Tiny> = IdFactory::new();
    for n in 0..128usize {
        assert_eq!(
            f.try_alloc().map(|id| id.as_usize()),
            Some(n),
            "the first 128 ids of a 7-bit space must all allocate"
        );
    }
    assert_eq!(f.count(), 128);
    // The 129th must be `None`, not a panic and not id 128 (which does not exist).
    assert_eq!(f.try_alloc(), None);
    assert_eq!(f.try_alloc(), None, "exhaustion is stable, not a one-shot");
    assert_eq!(f.count(), 128, "a refused allocation must not advance");
}

/// Arithmetic is bounded by `MAX`, not by the backing word. `0x40 + 0x40 == 0x80` does
/// not overflow a `u8` but is not a 7-bit id, and returning it would set the capture bit
/// — an index silently reinterpreted as a tag.
#[test]
fn checked_arithmetic_respects_the_payload_ceiling() {
    let half = Tiny::try_from_usize(0x40).unwrap();
    assert_eq!(
        half.checked_add(half),
        None,
        "0x80 fits the u8 but is not a 7-bit id"
    );
    assert_eq!(
        Tiny::MAX.checked_incr(),
        None,
        "incrementing the largest id has no result"
    );
    assert_eq!(Tiny::MIN.checked_decr(), None);

    let a = Tiny::try_from_usize(100).unwrap();
    let b = Tiny::try_from_usize(27).unwrap();
    assert_eq!(a.checked_add(b).map(|x| x.as_usize()), Some(127));
    assert_eq!(
        a.checked_add(Tiny::try_from_usize(28).unwrap()),
        None,
        "128 is one past the ceiling"
    );
    assert_eq!(a.checked_sub(b).map(|x| x.as_usize()), Some(73));
    assert_eq!(b.checked_sub(a), None, "no negative indices");

    // A stride into a flattened pool: the product overflows before either factor does.
    let stride = Tiny::try_from_usize(12).unwrap();
    assert_eq!(
        stride
            .checked_mul(Tiny::try_from_usize(10).unwrap())
            .map(|x| x.as_usize()),
        Some(120)
    );
    assert_eq!(stride.checked_mul(Tiny::try_from_usize(11).unwrap()), None);

    // A `std` collection length crossing into a narrow index.
    assert_eq!(
        Tiny::MIN.checked_add_usize(127).map(|x| x.as_usize()),
        Some(127)
    );
    assert_eq!(Tiny::MIN.checked_add_usize(128), None);
    assert_eq!(
        Tiny::MIN.checked_add_usize(usize::MAX),
        None,
        "a huge count must not overflow the intermediate either"
    );
    assert_eq!(a.checked_add_usize(usize::MAX), None);
}

/// The default bodies must agree with the inherent operations on the primitives, where
/// `MAX` genuinely is the word's max — including at `usize`, where the intermediate is
/// the same width as the result and `checked_add` is the only thing standing between the
/// sum and a wrap.
#[test]
fn primitive_impls_agree_with_inherent_checked_ops() {
    for (a, b) in [(0u8, 0u8), (1, 1), (200, 55), (200, 56), (255, 1), (0, 1)] {
        assert_eq!(IndexLike::checked_add(a, b), a.checked_add(b));
        assert_eq!(IndexLike::checked_sub(a, b), a.checked_sub(b));
        assert_eq!(IndexLike::checked_mul(a, b), a.checked_mul(b));
    }
    assert_eq!(IndexLike::checked_incr(u8::MAX), None);
    assert_eq!(IndexLike::checked_decr(0u8), None);

    assert_eq!(IndexLike::checked_add(u32::MAX, 1u32), None);
    assert_eq!(IndexLike::checked_incr(u32::MAX), None);
    assert_eq!(IndexLike::checked_mul(1u32 << 16, 1u32 << 16), None);

    assert_eq!(IndexLike::checked_add(u64::MAX, 1u64), None);
    assert_eq!(IndexLike::checked_incr(u64::MAX), None);

    assert_eq!(IndexLike::checked_add(usize::MAX, 1usize), None);
    assert_eq!(IndexLike::checked_incr(usize::MAX), None);
    assert_eq!(IndexLike::checked_add_usize(usize::MAX, 1), None);
    assert_eq!(IndexLike::checked_add_usize(1usize, usize::MAX), None);
}
