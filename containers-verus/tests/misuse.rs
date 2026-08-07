// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Misuse test suite (migration plan 2.5, public-API half).
//!
//! Every case here produces an invalid token through the PUBLIC API only
//! (forged-state cases — out-of-range frame indices, mixed-component compound
//! tokens, counter exhaustion — live as in-module `#[cfg(test)]` unit tests
//! next to the private state they corrupt). Each rejected restore must:
//!
//!   1. panic with the production-parity message, and
//!   2. panic BEFORE mutating anything (state logically unchanged after
//!      catch_unwind).
//!
//! These pin the runtime-hardening contract: erased `requires` clauses have
//! runtime mirrors that fire for unverified callers exactly where production's
//! asserts fire.

use semi_persistent_containers_verus::append_only_vec::AppendOnlyVec;
use semi_persistent_containers_verus::parallel_store::ParallelStore;
use semi_persistent_containers_verus::vec::{ShrinkPolicy, Vec as SpVec};

type V = SpVec<u32, u32, ParallelStore<u32, u32>, true>;

fn read_back(v: &V) -> Vec<u32> {
    (0..v.len() as usize).map(|i| v.get(i as u32)).collect()
}

// ---------------------------------------------------------------------------
// Foreign token: a token minted by container A must be rejected by B.
// ---------------------------------------------------------------------------

#[test]
#[should_panic(expected = "token belongs to a different container")]
fn foreign_token_panics() {
    let mut a = V::new();
    let mut b = V::new();
    a.push(1);
    b.push(2);
    let tok_a = a.mark(ShrinkPolicy::Never);
    b.restore(tok_a); // wrong container
}

#[test]
fn foreign_token_rejected_before_mutation() {
    let mut a = V::new();
    let mut b = V::new();
    for i in 0..10 {
        a.push(i);
        b.push(i + 100);
    }
    let tok_a = a.mark(ShrinkPolicy::Never);
    b.push(999);
    let before = (0..b.len() as usize)
        .map(|i| b.get(i as u32))
        .collect::<Vec<_>>();

    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        b.restore(tok_a);
    }));
    assert!(result.is_err(), "foreign restore must panic");
    let after = (0..b.len() as usize)
        .map(|i| b.get(i as u32))
        .collect::<Vec<_>>();
    assert_eq!(before, after, "rejected restore must not mutate state");
    // b remains fully usable.
    b.push(1000);
    assert_eq!(b.pop(), Some(1000));

    // And is_valid_token agrees without panicking.
    assert!(!b.is_valid_token(&tok_a));
    assert!(a.is_valid_token(&tok_a));
}

// ---------------------------------------------------------------------------
// Consumed token: restore(t) then restore(t) again — the frame is gone. THE
// consumed-token gap: genealogy alone would still call it on-path; the
// frame-liveness check must reject it.
// ---------------------------------------------------------------------------

#[test]
#[should_panic(expected = "token points beyond frame stack")]
fn consumed_token_panics() {
    let mut v = V::new();
    v.push(1);
    let tok = v.mark(ShrinkPolicy::Never);
    v.push(2);
    v.restore(tok); // consumes the frame
    v.restore(tok); // frame is gone
}

#[test]
fn consumed_token_reported_invalid_and_rejected_before_mutation() {
    let mut v = V::new();
    v.push(1);
    let tok = v.mark(ShrinkPolicy::Never);
    v.push(2);
    assert!(v.is_valid_token(&tok), "live token is restorable");
    v.restore(tok);
    // The consumed-token gap (design doc 08): the public is_valid_token must
    // now report NOT restorable (frame liveness), even though the branch
    // genealogy alone would still consider it on-path.
    assert!(
        !v.is_valid_token(&tok),
        "consumed token must report not-restorable"
    );

    let before = read_back(&v);
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        v.restore(tok);
    }));
    assert!(result.is_err(), "consumed restore must panic");
    assert_eq!(
        before,
        read_back(&v),
        "rejected restore must not mutate state"
    );
}

// ---------------------------------------------------------------------------
// Abandoned-future token: mark A, restore past it, mark again (new branch) —
// A's future was cut off; its token must be rejected by genealogy.
// ---------------------------------------------------------------------------

#[test]
#[should_panic(expected = "abandoned future")]
fn abandoned_future_token_panics() {
    let mut v = V::new();
    v.push(1);
    let base = v.mark(ShrinkPolicy::Never);
    v.push(2);
    let abandoned = v.mark(ShrinkPolicy::Never); // depth 2 on branch 0
    v.push(3);
    v.restore(base); // cut back to depth 0 -> new branch
    v.push(20);
    let _new_frame = v.mark(ShrinkPolicy::Never); // depth 1 on the NEW branch
    v.push(21);
    // `abandoned` names depth 2 of the OLD branch: genealogy must reject it
    // (its frame_idx=1 is within frames.len()=1? No: frames.len() is 1, so
    // frame_idx=1 fails liveness... push another frame so liveness passes and
    // genealogy is the deciding check).
    let _deeper = v.mark(ShrinkPolicy::Never); // frames.len()=2, frame_idx=1 live
    v.restore(abandoned);
}

#[test]
fn abandoned_future_reported_invalid() {
    let mut v = V::new();
    v.push(1);
    let base = v.mark(ShrinkPolicy::Never);
    v.push(2);
    let abandoned = v.mark(ShrinkPolicy::Never);
    v.push(3);
    v.restore(base);
    v.push(20);
    let _f1 = v.mark(ShrinkPolicy::Never);
    let _f2 = v.mark(ShrinkPolicy::Never); // make frame_idx=1 live again
    assert!(
        !v.is_valid_token(&abandoned),
        "abandoned-future token must report not-restorable"
    );
}

// ---------------------------------------------------------------------------
// TRACK=false: mark and restore are caller errors (production parity).
// ---------------------------------------------------------------------------

#[test]
#[should_panic(expected = "mark() called on untracked vec")]
fn untracked_mark_panics() {
    let mut v = SpVec::<u32, u32, ParallelStore<u32, u32>, false>::new();
    v.push(1);
    let _ = v.mark(ShrinkPolicy::Never);
}

#[test]
#[should_panic(expected = "mark() called on untracked AppendOnlyVec")]
fn untracked_append_only_mark_panics() {
    let mut v = AppendOnlyVec::<u32, false>::new();
    v.push(1);
    let _ = v.mark(ShrinkPolicy::Never);
}

/// TRACK=false restore: also a caller error. A token cannot be legitimately
/// obtained at TRACK=false (mark panics), so forge the call by transmuting
/// nothing — instead, get a token from a tracked vec and feed it to an
/// untracked one: the TRACK guard must fire FIRST (before the
/// container-identity check).
#[test]
#[should_panic(expected = "restore() called on untracked vec")]
fn untracked_restore_panics() {
    let mut tracked = V::new();
    tracked.push(1);
    let tok = tracked.mark(ShrinkPolicy::Never);
    let mut untracked = SpVec::<u32, u32, ParallelStore<u32, u32>, false>::new();
    untracked.push(1);
    untracked.restore(tok);
}

/// CircularList::splice same-ring misuse: the different-rings precondition is
/// spec-level; debug builds walk the ring and panic (release relies on caller
/// discipline — documented divergence). This test only asserts under
/// debug_assertions, which cargo test builds enable.
#[test]
#[cfg(debug_assertions)]
fn circular_splice_same_ring_panics_in_debug() {
    use semi_persistent_containers_verus::circular_list::CircularList;
    use semi_persistent_containers_verus::dense_id::DenseId31;
    let mut c = CircularList::<u32, DenseId31, true>::new();
    let a = c.add_singleton(1);
    let b = c.add_singleton(2);
    c.splice(a, b); // legal: different rings -> merged
    let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        c.splice(a, b); // now the SAME ring: debug guard must fire
    }));
    assert!(
        r.is_err(),
        "same-ring splice must panic under debug_assertions"
    );
}

#[test]
fn untracked_normal_ops_work() {
    // TRACK=false: everything except mark/restore behaves as a plain vec.
    let mut v = SpVec::<u32, u32, ParallelStore<u32, u32>, false>::new();
    for i in 0..100 {
        v.push(i);
    }
    v.set(50u32, 999);
    assert_eq!(v.get(50u32), 999);
    assert_eq!(v.pop(), Some(99));
    assert_eq!(v.len(), 99);
}

// ---------------------------------------------------------------------------
// AppendOnlyVec: same token discipline as Vec.
// ---------------------------------------------------------------------------

#[test]
#[should_panic(expected = "token belongs to a different container")]
fn aov_foreign_token_panics() {
    let mut a = AppendOnlyVec::<u32, true>::new();
    let mut b = AppendOnlyVec::<u32, true>::new();
    a.push(1);
    b.push(2);
    let tok_a = a.mark(ShrinkPolicy::Never);
    b.restore(tok_a);
}

#[test]
#[should_panic(expected = "token points beyond frame stack")]
fn aov_consumed_token_panics() {
    let mut v = AppendOnlyVec::<u32, true>::new();
    v.push(1);
    let tok = v.mark(ShrinkPolicy::Never);
    v.push(2);
    v.restore(tok);
    v.restore(tok);
}

#[test]
fn aov_consumed_token_reported_invalid() {
    let mut v = AppendOnlyVec::<u32, true>::new();
    v.push(1);
    let tok = v.mark(ShrinkPolicy::Never);
    assert!(v.is_valid_token(&tok));
    v.restore(tok);
    assert!(!v.is_valid_token(&tok));
}

// ---------------------------------------------------------------------------
// SpMap: token discipline through the composite wrapper.
// ---------------------------------------------------------------------------

#[test]
fn map_consumed_token_reported_invalid_and_state_preserved() {
    use semi_persistent_containers_verus::map::SpMap;
    let mut m = SpMap::<u32, u32, true>::new();
    m.insert(1, 10);
    let tok = m.mark(ShrinkPolicy::Never);
    m.insert(2, 20);
    assert!(m.is_valid_token(&tok));
    m.restore(tok);
    assert!(
        !m.is_valid_token(&tok),
        "consumed map token must be invalid"
    );

    let before_log = m.log_len();
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        m.restore(tok);
    }));
    assert!(result.is_err());
    assert_eq!(m.log_len(), before_log, "rejected restore must not mutate");
    assert_eq!(m.id_of(&1), Some(0));
}

// ---------------------------------------------------------------------------
// SparseSet: atomic compound restore — a token with a consumed component must
// be rejected BEFORE any of the three vecs is restored.
// ---------------------------------------------------------------------------

#[test]
fn sparse_set_atomic_restore_rejects_consumed_compound() {
    use semi_persistent_containers_verus::dense_id::DenseId31;
    use semi_persistent_containers_verus::sparse_set::SparseSet;

    // Privacy closeout: constructed via the public constructor (fields are
    // no longer visible outside the crate).
    let mut s = SparseSet::<u32, DenseId31, ParallelStore<u32, DenseId31>, true>::new();
    let id1 = s.add(100);
    let tok = s.mark(ShrinkPolicy::Never);
    let id2 = s.add(200);
    assert!(s.is_valid_token(&tok));
    s.restore(tok);
    assert!(
        !s.is_valid_token(&tok),
        "consumed compound token must be invalid"
    );

    // A second restore with the consumed compound token must be rejected
    // atomically: panic fires before ANY of dense/sparse/indices restores.
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        s.restore(tok);
    }));
    assert!(result.is_err(), "consumed compound restore must panic");
    // Set state intact and consistent: id1 present, id2 rolled back.
    assert!(s.contains(id1));
    assert!(!s.contains(id2));
    assert_eq!(s.get(id1), 100);
}
