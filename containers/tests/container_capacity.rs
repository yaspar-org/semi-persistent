// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Acceptance criteria: every container's index-width ceiling is *reached* by a test, and
//! crossing it is always observable — never an index that quietly means something else.
//!
//! `tests/index_arith.rs` pins the ceiling of the index *type*: `try_from_usize` rejects
//! out-of-range values instead of narrowing them into range. This file pins the ceiling of
//! the *containers built on it*, which is a separate claim: a container can hold a perfectly
//! well-behaved `IndexLike` and still lose the bound by computing a position before checking
//! it, or by checking the position it returns while leaving the length it will report
//! unrepresentable.
//!
//! `I = u8` is what makes any of this testable. Every boundary below is reached with 255 or
//! 256 pushes; at `u32` the same cases need four billion, which is why they were previously
//! reasoned about and not run.
//!
//! ## Two protocols, both deliberate, both pinned here
//!
//! The containers do not all refuse an overflowing insert at the same point, and the
//! difference is a design decision rather than an inconsistency:
//!
//! * [`AppendOnlyVec`] (and [`Map`], whose log is one) **refuses at push time**, guarding the
//!   *new length* rather than the returned index. Its doc states the reason: every later
//!   `len()` is then infallible by construction. It owns its length, so it can.
//! * [`Vec`] — and therefore [`SparseSet`], whose three arrays are `Vec`s — **accepts the
//!   overflowing element and traps at the next `len()` read**. This is the "overflow
//!   protocol" the verified port documents at `containers-verus/src/vec.rs`: `push` carries no
//!   runtime check because the verified `requires` obliges every *verified* caller to prove
//!   `len + 1 < I::max_nat()`, and the `len()`-read trap is the backstop for an unverified
//!   one. Adding a production-only assert would put a check on the hot path that the proof
//!   already discharges, and would diverge from the verified contract.
//!
//! What matters for soundness is the same in both cases and is what each test below actually
//! asserts: **no position is ever aliased onto another**. A trap at the next read is a
//! diagnosable stop; an index that wrapped is a wrong answer. So the tests check the full
//! distinctness and value-fidelity of everything stored right up to and including the
//! over-filled state, and only then that the trap fires.
//!
//! [`AppendOnlyVec`]: semi_persistent_containers::AppendOnlyVec
//! [`Map`]: semi_persistent_containers::Map
//! [`Vec`]: semi_persistent_containers::VecI
//! [`SparseSet`]: semi_persistent_containers::SparseSet

use semi_persistent_containers as c;
use semi_persistent_containers::IndexLike;

/// Live elements a container can hold under an `I = u8` index: positions `0..=254`.
///
/// One below the 256 values a `u8` has, because a *length* of 256 is the thing that must stay
/// representable, and 255 positions is the most that leaves room for. Every container below
/// lands on this same number, but by two different routes — refused at push time, or reached
/// and then trapped on the next length read — which is what the two sections separate.
const OWNED_LEN_CAP: usize = 255;

// ---------------------------------------------------------------------------
// AppendOnlyVec — refuses at push time
// ---------------------------------------------------------------------------

/// A full append-only vec is exactly full: every index is its own position, every element
/// reads back, and `len()` is readable at the ceiling rather than trapping there.
#[test]
fn append_only_vec_is_exact_at_its_ceiling() {
    let mut v: c::AppendOnlyVec<u32, u8, true> = c::AppendOnlyVec::new();
    for i in 0..OWNED_LEN_CAP {
        let at = v.push(i as u32);
        assert_eq!(
            at.as_usize(),
            i,
            "push must return its own position, not a narrowed one"
        );
    }
    assert_eq!(
        v.len().as_usize(),
        OWNED_LEN_CAP,
        "len() must be readable at the ceiling — that is what the push-time guard buys"
    );
    for i in 0..OWNED_LEN_CAP {
        let at: u8 = u8::try_from_usize(i).expect("in range by construction");
        assert_eq!(*v.get(at), i as u32, "element {i} read back as another");
    }
}

/// One past the ceiling is refused *at the push*, naming the index word.
///
/// The guard is on the successor length, so the refused push is the one whose index (255)
/// would still have fit: accepting it would leave a vec whose own `len()` is unrepresentable.
#[test]
#[should_panic(expected = "append-only vec is full for its index word")]
fn append_only_vec_refuses_the_push_that_would_break_len() {
    let mut v: c::AppendOnlyVec<u32, u8, true> = c::AppendOnlyVec::new();
    for i in 0..=OWNED_LEN_CAP {
        v.push(i as u32);
    }
}

/// Restoring below the ceiling makes room again: the cap is on the live length, not a
/// once-and-for-all budget. A cap that counted lifetime pushes instead would pass every test
/// above and still brick a long-running semi-persistent session.
#[test]
fn append_only_vec_capacity_is_reclaimed_by_restore() {
    let mut v: c::AppendOnlyVec<u32, u8, true> = c::AppendOnlyVec::new();
    for i in 0..100 {
        v.push(i);
    }
    let t = v.mark(c::ShrinkPolicy::Never);
    for i in 0..(OWNED_LEN_CAP - 100) {
        v.push(i as u32);
    }
    assert_eq!(v.len().as_usize(), OWNED_LEN_CAP);
    v.restore(t);
    assert_eq!(v.len().as_usize(), 100);
    // The freed positions are pushable again, all the way back to the ceiling.
    for i in 0..(OWNED_LEN_CAP - 100) {
        v.push(i as u32);
    }
    assert_eq!(v.len().as_usize(), OWNED_LEN_CAP);
}

// ---------------------------------------------------------------------------
// Map — inherits the append-only ceiling
// ---------------------------------------------------------------------------

/// The map's ceiling is its log's, and the hash index agrees with it at the boundary: every
/// key still resolves to its own log position when the log is full.
///
/// This is the assertion the width work actually needs, because `I` is the *value* type of
/// that index: a narrowing there would make `id_of` return a position belonging to a
/// different key, which no length check would ever notice.
#[test]
fn map_index_agrees_with_the_log_at_the_ceiling() {
    let mut m: c::Map<u32, u32, u8, true> = c::Map::new();
    for i in 0..OWNED_LEN_CAP {
        let id = m.insert(i as u32, (i as u32) * 7);
        assert_eq!(id.as_usize(), i, "insert must return its own log position");
    }
    assert_eq!(m.log_len().as_usize(), OWNED_LEN_CAP);
    for i in 0..OWNED_LEN_CAP {
        let k = i as u32;
        assert_eq!(
            m.id_of(&k).map(IndexLike::as_usize),
            Some(i),
            "key {k} resolved to the wrong log position at the ceiling"
        );
        assert_eq!(*m.get_by_key(&k).expect("present"), k * 7);
    }
}

#[test]
#[should_panic(expected = "append-only vec is full for its index word")]
fn map_refuses_the_insert_past_the_log_ceiling() {
    let mut m: c::Map<u32, u32, u8, true> = c::Map::new();
    for i in 0..=OWNED_LEN_CAP {
        m.insert(i as u32, 0);
    }
}

// ---------------------------------------------------------------------------
// Vec — accepts, then traps at the next len() read
// ---------------------------------------------------------------------------

/// Up to the ceiling, both stores are exact: `len()` is readable and every slot holds its
/// own value. `InlineStore` and `ParallelStore` are checked separately because they have
/// *separate* `len()` implementations, each with its own `try_from_usize`.
#[test]
fn vec_stores_are_exact_at_their_ceiling() {
    let mut vi: c::VecI<u32, u8, true> = c::VecI::new();
    let mut vp: c::VecP<u32, u8, true> = c::VecP::new();
    for i in 0..OWNED_LEN_CAP {
        vi.push(i as u32);
        vp.push(i as u32);
    }
    assert_eq!(vi.len().as_usize(), OWNED_LEN_CAP, "inline store len");
    assert_eq!(vp.len().as_usize(), OWNED_LEN_CAP, "parallel store len");
    for i in 0..OWNED_LEN_CAP {
        let at: u8 = u8::try_from_usize(i).expect("in range by construction");
        assert_eq!(vi.get(at), i as u32, "inline element {i}");
        assert_eq!(vp.get(at), i as u32, "parallel element {i}");
    }
}

/// The over-filled vec does not alias: the element pushed past the ceiling goes to its own
/// slot, and every earlier slot still reads back its own value.
///
/// This is the soundness half of the trap-at-read protocol. `push` accepted an element whose
/// *length* it cannot name in an `I`, which is why the next `len()` traps — but it did not
/// reuse an index to do it, and that is the difference between a stop and a wrong answer.
/// Read through raw slot indices rather than through `len()`, since reading `len()` is exactly
/// what is no longer allowed.
#[test]
fn vec_past_its_ceiling_does_not_alias_earlier_slots() {
    let mut v: c::VecI<u32, u8, true> = c::VecI::new();
    for i in 0..=OWNED_LEN_CAP {
        v.push(i as u32);
    }
    // Every slot including 255 — the over-filled element is *addressable*, it is only the
    // length 256 that is not, so it has its own slot and must not have taken anyone else's.
    for i in 0..=OWNED_LEN_CAP {
        let at: u8 = u8::try_from_usize(i).expect("slot 255 is still a u8; only 256 is not");
        assert_eq!(
            v.get(at),
            i as u32,
            "the over-filled push overwrote slot {i} instead of taking its own"
        );
    }
}

#[test]
#[should_panic(expected = "len overflow")]
fn vec_past_its_ceiling_traps_at_the_next_len_read() {
    let mut v: c::VecI<u32, u8, true> = c::VecI::new();
    for i in 0..=OWNED_LEN_CAP {
        v.push(i as u32);
    }
    let _ = v.len();
}

/// The parallel store traps too, and at its own `len()`. Asserted separately from the inline
/// one: the two stores duplicate the check, so a regression could remove either.
#[test]
#[should_panic(expected = "len overflow")]
fn parallel_store_vec_traps_at_the_next_len_read() {
    let mut v: c::VecP<u32, u8, true> = c::VecP::new();
    for i in 0..=OWNED_LEN_CAP {
        v.push(i as u32);
    }
    let _ = v.len();
}

// ---------------------------------------------------------------------------
// SparseSet — ids stay distinct through the boundary
// ---------------------------------------------------------------------------

/// A sparse set holding its ceiling of live elements: every id distinct, every id resolving
/// to its own value, `len()` readable.
///
/// Same count as the length-owning containers, reached by a different route. `add` derives
/// the new id from the dense length *before* pushing, so `add` itself only traps at the 257th
/// call — but the 256th leaves all three arrays 256 long, and `len`, `contains` and `get` all
/// read a length through `try_from_usize`. So the *usable* ceiling is 255, one below where
/// `add` refuses. That asymmetry is the reason this is a test and not a comment.
#[test]
fn sparse_set_is_exact_at_its_usable_ceiling() {
    let mut s: c::SparseSet<u32, u8, c::ParallelStore<u32, u8>, true> = c::SparseSet::new();
    let mut ids = Vec::new();
    for i in 0..OWNED_LEN_CAP {
        ids.push(s.add(i as u32));
    }
    let distinct: std::collections::BTreeSet<u8> = ids.iter().copied().collect();
    assert_eq!(
        distinct.len(),
        OWNED_LEN_CAP,
        "a full sparse set must have handed out {OWNED_LEN_CAP} distinct ids"
    );
    assert_eq!(s.len().as_usize(), OWNED_LEN_CAP);
    for (i, &id) in ids.iter().enumerate() {
        assert!(s.contains(id), "lost live id {id}");
        assert_eq!(s.get(id), i as u32, "id {id} resolves to the wrong element");
    }
}

/// One element past the usable ceiling: `add` accepts it and hands out a distinct id, and
/// *then* every read traps.
///
/// The order of the two assertions is the point. Distinctness is checked first, from the ids
/// alone with no container read, because that is the soundness property: an id reissued here
/// would silently merge two live elements, and no later trap would ever reveal it. The trap
/// is checked second, and only says that the over-filled state is a stop rather than a
/// usable-looking set. Neither assertion substitutes for the other.
#[test]
#[should_panic(expected = "len overflow")]
fn sparse_set_past_its_usable_ceiling_traps_rather_than_aliasing() {
    let mut s: c::SparseSet<u32, u8, c::ParallelStore<u32, u8>, true> = c::SparseSet::new();
    let mut ids = std::collections::BTreeSet::new();
    for i in 0..=OWNED_LEN_CAP {
        let id = s.add(i as u32);
        assert!(
            ids.insert(id),
            "id {id} reissued while still live (element {i})"
        );
    }
    assert_eq!(ids.len(), OWNED_LEN_CAP + 1, "256 adds must yield 256 ids");
    // Now the length is unrepresentable, so the set is a stop, not a set.
    let _ = s.contains(0);
}

/// Two past: `add` itself traps, on the dense length it reads before deriving the id.
#[test]
#[should_panic(expected = "len overflow")]
fn sparse_set_add_traps_once_the_dense_length_is_unrepresentable() {
    let mut s: c::SparseSet<u32, u8, c::ParallelStore<u32, u8>, true> = c::SparseSet::new();
    for i in 0..=(OWNED_LEN_CAP + 1) {
        s.add(i as u32);
    }
}

/// Removing frees the id for reuse, so the ceiling bounds the *live* set and not the number
/// of adds a session may ever perform. The recycled ids must be the freed ones — a full set
/// that answered with fresh ids instead would walk straight into the trap above.
#[test]
fn sparse_set_recycles_ids_at_the_ceiling_instead_of_trapping() {
    let mut s: c::SparseSet<u32, u8, c::ParallelStore<u32, u8>, true> = c::SparseSet::new();
    let mut ids = Vec::new();
    for i in 0..OWNED_LEN_CAP {
        ids.push(s.add(i as u32));
    }
    // Free three ids spread through the dense array, so the recycling is not just "the last".
    let freed: std::collections::BTreeSet<u8> =
        [ids[0], ids[OWNED_LEN_CAP / 2], ids[OWNED_LEN_CAP - 1]]
            .into_iter()
            .collect();
    for &id in &freed {
        s.remove(id);
    }
    assert_eq!(s.len().as_usize(), OWNED_LEN_CAP - freed.len());
    let mut reissued = std::collections::BTreeSet::new();
    for i in 0..freed.len() {
        let id = s.add(1000 + i as u32);
        assert!(
            freed.contains(&id),
            "a full set issued id {id}, which was never freed"
        );
        assert!(reissued.insert(id), "id {id} reissued twice");
    }
    assert_eq!(reissued, freed, "every freed id must come back");
    assert_eq!(s.len().as_usize(), OWNED_LEN_CAP, "back at the ceiling");
}
