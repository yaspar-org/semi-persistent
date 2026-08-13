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
fn foreign_token_refuses_as_err() {
    let mut a = V::new();
    let mut b = V::new();
    a.try_push(1).expect("push: within index word");
    b.try_push(2).expect("push: within index word");
    let tok_a = a
        .try_mark(ShrinkPolicy::Never)
        .expect("mark: depth bounded by this harness");
    let e = b.try_restore(tok_a).unwrap_err(); // wrong container
    assert_eq!(
        e,
        semi_persistent_containers_verus::error::ContainerError::InvalidToken,
        "was: panic(token belongs to a different container)"
    );
}

#[test]
fn foreign_token_rejected_before_mutation() {
    let mut a = V::new();
    let mut b = V::new();
    for i in 0..10 {
        a.try_push(i).expect("push: within index word");
        b.try_push(i + 100).expect("push: within index word");
    }
    let tok_a = a
        .try_mark(ShrinkPolicy::Never)
        .expect("mark: depth bounded by this harness");
    b.try_push(999).expect("push: within index word");
    let before = (0..b.len() as usize)
        .map(|i| b.get(i as u32))
        .collect::<Vec<_>>();

    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        b.try_restore(tok_a).expect("restore: own token");
    }));
    assert!(result.is_err(), "foreign restore must panic");
    let after = (0..b.len() as usize)
        .map(|i| b.get(i as u32))
        .collect::<Vec<_>>();
    assert_eq!(before, after, "rejected restore must not mutate state");
    // b remains fully usable.
    b.try_push(1000).expect("push: within index word");
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
fn consumed_token_refuses_as_err() {
    let mut v = V::new();
    v.try_push(1).expect("push: within index word");
    let tok = v
        .try_mark(ShrinkPolicy::Never)
        .expect("mark: depth bounded by this harness");
    v.try_push(2).expect("push: within index word");
    v.try_restore(tok).expect("first restore: live frame"); // consumes the frame
    let e = v.try_restore(tok).unwrap_err(); // frame is gone
    assert_eq!(
        e,
        semi_persistent_containers_verus::error::ContainerError::InvalidToken,
        "was: panic(token points beyond frame stack)"
    );
}

#[test]
fn consumed_token_reported_invalid_and_rejected_before_mutation() {
    let mut v = V::new();
    v.try_push(1).expect("push: within index word");
    let tok = v
        .try_mark(ShrinkPolicy::Never)
        .expect("mark: depth bounded by this harness");
    v.try_push(2).expect("push: within index word");
    assert!(v.is_valid_token(&tok), "live token is restorable");
    v.try_restore(tok).expect("restore: own token");
    // The consumed-token gap (design doc 08): the public is_valid_token must
    // now report NOT restorable (frame liveness), even though the branch
    // genealogy alone would still consider it on-path.
    assert!(
        !v.is_valid_token(&tok),
        "consumed token must report not-restorable"
    );

    let before = read_back(&v);
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        v.try_restore(tok).expect("restore: own token");
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
fn abandoned_future_token_refuses_as_err() {
    let mut v = V::new();
    v.try_push(1).expect("push: within index word");
    let base = v
        .try_mark(ShrinkPolicy::Never)
        .expect("mark: depth bounded by this harness");
    v.try_push(2).expect("push: within index word");
    let abandoned = v
        .try_mark(ShrinkPolicy::Never)
        .expect("mark: depth bounded by this harness"); // depth 2 on branch 0
    v.try_push(3).expect("push: within index word");
    v.try_restore(base).expect("restore: own token"); // cut back to depth 0 -> new branch
    v.try_push(20).expect("push: within index word");
    let _new_frame = v
        .try_mark(ShrinkPolicy::Never)
        .expect("mark: depth bounded by this harness"); // depth 1 on the NEW branch
    v.try_push(21).expect("push: within index word");
    // `abandoned` names depth 2 of the OLD branch: genealogy must reject it
    // (its frame_idx=1 is within frames.len()=1? No: frames.len() is 1, so
    // frame_idx=1 fails liveness... push another frame so liveness passes and
    // genealogy is the deciding check).
    let _deeper = v
        .try_mark(ShrinkPolicy::Never)
        .expect("mark: depth bounded by this harness"); // frames.len()=2, frame_idx=1 live
    assert_eq!(
        v.try_restore(abandoned).unwrap_err(),
        semi_persistent_containers_verus::error::ContainerError::InvalidToken,
        "was: panic — abandoned-branch future token, rejected by genealogy"
    );
}

#[test]
fn abandoned_future_reported_invalid() {
    let mut v = V::new();
    v.try_push(1).expect("push: within index word");
    let base = v
        .try_mark(ShrinkPolicy::Never)
        .expect("mark: depth bounded by this harness");
    v.try_push(2).expect("push: within index word");
    let abandoned = v
        .try_mark(ShrinkPolicy::Never)
        .expect("mark: depth bounded by this harness");
    v.try_push(3).expect("push: within index word");
    v.try_restore(base).expect("restore: own token");
    v.try_push(20).expect("push: within index word");
    let _f1 = v
        .try_mark(ShrinkPolicy::Never)
        .expect("mark: depth bounded by this harness");
    let _f2 = v
        .try_mark(ShrinkPolicy::Never)
        .expect("mark: depth bounded by this harness"); // make frame_idx=1 live again
    assert!(
        !v.is_valid_token(&abandoned),
        "abandoned-future token must report not-restorable"
    );
}

// ---------------------------------------------------------------------------
// TRACK=false: mark and restore are caller errors (production parity).
// ---------------------------------------------------------------------------

#[test]
fn untracked_mark_refuses_as_err() {
    let mut v = SpVec::<u32, u32, ParallelStore<u32, u32>, false>::new();
    v.try_push(1).expect("push: within index word");
    let e = v.try_mark(ShrinkPolicy::Never).unwrap_err();
    assert_eq!(
        e,
        semi_persistent_containers_verus::error::ContainerError::Untracked,
        "was: panic(mark() called on untracked vec)"
    );
}

#[test]
fn untracked_append_only_mark_refuses_as_err() {
    let mut v = AppendOnlyVec::<u32, usize, false>::new();
    v.try_push(1).expect("push: within index word");
    let e = v.try_mark(ShrinkPolicy::Never).unwrap_err();
    assert_eq!(
        e,
        semi_persistent_containers_verus::error::ContainerError::Untracked,
        "was: panic(mark() called on untracked AppendOnlyVec)"
    );
}

/// TRACK=false restore: also a caller error. A token cannot be legitimately
/// obtained at TRACK=false (mark panics), so forge the call by transmuting
/// nothing — instead, get a token from a tracked vec and feed it to an
/// untracked one: the TRACK guard must fire FIRST (before the
/// container-identity check).
#[test]
fn untracked_restore_refuses_as_err() {
    let mut tracked = V::new();
    tracked.try_push(1).expect("push: within index word");
    let tok = tracked
        .try_mark(ShrinkPolicy::Never)
        .expect("mark: depth bounded by this harness");
    let mut untracked = SpVec::<u32, u32, ParallelStore<u32, u32>, false>::new();
    untracked.try_push(1).expect("push: within index word");
    let e = untracked.try_restore(tok).unwrap_err();
    assert_eq!(
        e,
        semi_persistent_containers_verus::error::ContainerError::InvalidToken,
        "was: panic(restore() called on untracked vec); Untracked is folded into\n         InvalidToken here because is_restorable_spec includes the TRACK gate"
    );
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
    let a = c.try_add_singleton(1).expect("id range");
    let b = c.try_add_singleton(2).expect("id range");
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
        v.try_push(i).expect("push: within index word");
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
fn aov_foreign_token_refuses_as_err() {
    let mut a = AppendOnlyVec::<u32, usize, true>::new();
    let mut b = AppendOnlyVec::<u32, usize, true>::new();
    a.try_push(1).expect("push: within index word");
    b.try_push(2).expect("push: within index word");
    let tok_a = a
        .try_mark(ShrinkPolicy::Never)
        .expect("mark: depth bounded by this harness");
    assert_eq!(
        b.try_restore(tok_a).unwrap_err(),
        semi_persistent_containers_verus::error::ContainerError::InvalidToken,
        "was: panic(token belongs to a different container)"
    );
}

#[test]
fn aov_consumed_token_refuses_as_err() {
    let mut v = AppendOnlyVec::<u32, usize, true>::new();
    v.try_push(1).expect("push: within index word");
    let tok = v
        .try_mark(ShrinkPolicy::Never)
        .expect("mark: depth bounded by this harness");
    v.try_push(2).expect("push: within index word");
    v.try_restore(tok).expect("first restore: live frame");
    assert_eq!(
        v.try_restore(tok).unwrap_err(),
        semi_persistent_containers_verus::error::ContainerError::InvalidToken,
        "was: panic(token points beyond frame stack)"
    );
}

#[test]
fn aov_consumed_token_reported_invalid() {
    let mut v = AppendOnlyVec::<u32, usize, true>::new();
    v.try_push(1).expect("push: within index word");
    let tok = v
        .try_mark(ShrinkPolicy::Never)
        .expect("mark: depth bounded by this harness");
    assert!(v.is_valid_token(&tok));
    v.try_restore(tok).expect("restore: own token");
    assert!(!v.is_valid_token(&tok));
}

// ---------------------------------------------------------------------------
// SpMap: token discipline through the composite wrapper.
// ---------------------------------------------------------------------------

#[test]
fn map_consumed_token_reported_invalid_and_state_preserved() {
    use semi_persistent_containers_verus::map::SpMap;
    let mut m = SpMap::<u32, u32, usize, true>::new();
    m.try_insert(1, 10).expect("insert: within index word");
    let tok = m
        .try_mark(ShrinkPolicy::Never)
        .expect("mark: depth bounded by this harness");
    m.try_insert(2, 20).expect("insert: within index word");
    assert!(m.is_valid_token(&tok));
    m.try_restore(tok).expect("restore: own token");
    assert!(
        !m.is_valid_token(&tok),
        "consumed map token must be invalid"
    );

    let before_log = m.log_len();
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        m.try_restore(tok).expect("restore: own token");
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
    let id1 = s.try_add(100).expect("add: within id space");
    let tok = s
        .try_mark(ShrinkPolicy::Never)
        .expect("mark: depth bounded by this harness");
    let id2 = s.try_add(200).expect("add: within id space");
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

// ---------------------------------------------------------------------------
// Total shell (total-API plan phase 2): every refusal is an Err naming the
// failed precondition, the container is unchanged, and nothing panics.
// ---------------------------------------------------------------------------

#[test]
fn try_push_refuses_at_the_index_words_capacity() {
    use semi_persistent_containers_verus::error::ContainerError;
    type V = SpVec<u32, u8, ParallelStore<u32, u8>, false>;
    let mut v: V = V::new();
    // can_push holds while len + 1 < 256, i.e. through len == 254.
    let mut n = 0usize;
    while v.can_push() {
        v.try_push(7).unwrap();
        n += 1;
    }
    assert_eq!(n, 255, "push admits exactly max_nat - 1 elements");
    let e = v.try_push(8).unwrap_err();
    assert_eq!(e, ContainerError::CapacityExhausted);
    // Unchanged: still the same length, and a subsequent len() must not trap.
    assert_eq!(v.len(), u8::MAX);
}

#[test]
fn try_extend_is_all_or_nothing() {
    use semi_persistent_containers_verus::error::ContainerError;
    type V = SpVec<u32, u8, ParallelStore<u32, u8>, false>;
    let mut v: V = V::new();
    v.try_extend(&[1, 2, 3]).unwrap();
    assert_eq!(v.len(), 3);
    // 253 more would land exactly at 256 > 255 = cap: refused whole.
    let big: Vec<u32> = (0..253).collect();
    let e = v.try_extend(&big).unwrap_err();
    assert_eq!(e, ContainerError::CapacityExhausted);
    assert_eq!(v.len(), 3, "a refused batch appends nothing");
    // 252 more lands at 255 == cap: admitted.
    v.try_extend(&big[..252]).unwrap();
    assert_eq!(v.len(), u8::MAX);
}

#[test]
fn try_mark_names_the_failed_precondition() {
    use semi_persistent_containers_verus::error::ContainerError;
    // Untracked: refused as Untracked, not a panic (the partial mark panics).
    type U = SpVec<u32, u8, ParallelStore<u32, u8>, false>;
    let mut u: U = U::new();
    assert_eq!(
        u.try_mark(ShrinkPolicy::Never).unwrap_err(),
        ContainerError::Untracked
    );
    // Tracked and in range: succeeds and round-trips through try_restore.
    type T = SpVec<u32, u8, ParallelStore<u32, u8>, true>;
    let mut t: T = T::new();
    t.try_push(1).unwrap();
    let tok = t.try_mark(ShrinkPolicy::Never).unwrap();
    t.try_push(2).unwrap();
    t.try_restore(tok).unwrap();
    assert_eq!(t.len(), 1);
}

#[test]
fn try_restore_rejects_a_foreign_token_as_err() {
    use semi_persistent_containers_verus::error::ContainerError;
    type T = SpVec<u32, u8, ParallelStore<u32, u8>, true>;
    let mut a: T = T::new();
    let mut b: T = T::new();
    a.try_push(1).unwrap();
    b.try_push(9).unwrap();
    let tok_a = a.try_mark(ShrinkPolicy::Never).unwrap();
    assert_eq!(
        b.try_restore(tok_a).unwrap_err(),
        ContainerError::InvalidToken,
        "a foreign token is an Err on the total surface (the partial core panics)"
    );
    assert_eq!(b.len(), 1, "refused restore leaves the container unchanged");
    // Consumed token: valid once, then Err.
    a.try_restore(tok_a).unwrap();
    assert_eq!(
        a.try_restore(tok_a).unwrap_err(),
        ContainerError::InvalidToken
    );
}

#[test]
fn aov_total_shell_refuses_and_round_trips() {
    use semi_persistent_containers_verus::error::ContainerError;
    type A = AppendOnlyVec<String, u8, true>;
    let mut a: A = A::new();
    while a.can_push() {
        a.try_push(format!("x")).unwrap();
    }
    assert_eq!(
        a.try_push(format!("y")).unwrap_err(),
        ContainerError::CapacityExhausted
    );
    let tok = a.try_mark(ShrinkPolicy::Never).unwrap();
    assert_eq!(
        a.try_restore(tok).map_err(|e| e),
        Ok(()),
        "fresh token restores"
    );
    assert_eq!(
        a.try_restore(tok).unwrap_err(),
        ContainerError::InvalidToken,
        "consumed token refuses as Err"
    );
}
