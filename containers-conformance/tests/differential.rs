// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Differential trace harness (migration plan Phase 1.2).
//!
//! Runs identical randomized operation traces against the production
//! `semi-persistent-containers` crate and this crate, asserting identical
//! observable results at every step. Parity is defined over the RETAINED
//! COMMON BEHAVIORAL SURFACE (plan Phase 0): operations intentionally removed
//! (`get_mut`), bounds intentionally narrowed (Clone vectors), and 32-bit
//! targets are out of scope.
//!
//! Coverage grows with the parity phases:
//! - NOW (pre-parity API subset): Vec both stores (push/pop/set/get/len/
//!   mark/restore), AppendOnlyVec, SpMap vs Map (Copy keys, insert/id_of/
//!   contains_key/log_len/mark/restore), BPlusTreeSet (insert_general vs
//!   insert, cursor seek/step/key, mark/restore).
//! - Phase 5.3: SparseSet (needs the verus `new()` constructor; construction
//!   via struct literal would break at Phase 2.1 field privacy).
//! - Phase 5.4: ListArena (needs typed ids in verus).
//! - Phase 4/7: token-validity verdicts (`is_valid_token` — the verus meaning
//!   strengthens to "restorable now" in Phase 2.2, at which point the verdict
//!   comparison is scoped to tokens production also considers restorable).
//!
//! Determinism: a seeded xorshift generator; no proptest shrinking needed —
//! a failing trace replays exactly from its seed.

use containers_conformance::Rng;
use semi_persistent_containers as prod;
use semi_persistent_containers_verus as verus;

// ---------------------------------------------------------------------------
// Vec differential: production VecI/VecP vs verus Vec<_, _, InlineStore/
// ParallelStore, true>. Ops: push, pop, set, get, len, mark, restore.
// ---------------------------------------------------------------------------

fn vec_trace_inline(seed: u64, steps: usize) {
    type VInline = verus::vec::Vec<u32, u32, verus::inline_store::InlineStore<u32, u32>, true>;
    let mut p: prod::VecI<u32, u32, true> = prod::VecI::new();
    let mut v: VInline = VInline::new();

    let mut rng = Rng::new(seed);
    // (prod token, verus token) pairs; restore-to-ancestor invalidates suffix.
    let mut marks: Vec<(prod::VecToken, verus::vec::VecToken)> = Vec::new();
    let mut len: usize = 0;

    for step in 0..steps {
        match rng.below(100) {
            0..=39 => {
                let val = rng.next() as u32;
                p.push(val);
                v.push(val);
                len += 1;
            }
            40..=64 => {
                if len == 0 {
                    continue;
                }
                let idx = rng.below(len as u64) as u32;
                let val = rng.next() as u32;
                p.set(idx, val);
                v.set(idx, val);
            }
            65..=79 => {
                if len == 0 {
                    continue;
                }
                let idx = rng.below(len as u64) as u32;
                assert_eq!(p.get(idx), v.get(idx), "step {step}: get({idx}) diverged");
            }
            80..=86 => {
                let got_p = p.pop();
                let got_v = v.pop();
                assert_eq!(got_p, got_v, "step {step}: pop diverged");
                len = len.saturating_sub(1);
            }
            87..=93 => {
                if marks.len() >= 12 {
                    continue;
                }
                let tp = p.mark(prod::ShrinkPolicy::Never);
                let tv = v.mark(verus::vec::ShrinkPolicy::Never);
                marks.push((tp, tv));
            }
            _ => {
                if marks.is_empty() {
                    continue;
                }
                let idx = rng.below(marks.len() as u64) as usize;
                let (tp, tv) = marks[idx];
                p.restore(tp);
                v.restore(tv);
                marks.truncate(idx);
                len = p.len() as usize;
            }
        }
        assert_eq!(
            p.len() as usize,
            {
                let l: u32 = v.len();
                l as usize
            },
            "step {step}: len diverged"
        );
    }

    // Full-content sweep.
    for i in 0..len as u32 {
        assert_eq!(p.get(i), v.get(i), "final content diverged at {i}");
    }
}

#[test]
fn differential_vec_inline() {
    for seed in [1, 0xBEEF, 0xC0FFEE, 42, 7777] {
        vec_trace_inline(seed, 2000);
    }
}

fn vec_trace_parallel(seed: u64, steps: usize) {
    type VParallel =
        verus::vec::Vec<u32, u32, verus::parallel_store::ParallelStore<u32, u32>, true>;
    let mut p: prod::VecP<u32, u32, true> = prod::VecP::new();
    let mut v: VParallel = VParallel::new();

    let mut rng = Rng::new(seed);
    let mut marks: Vec<(prod::VecToken, verus::vec::VecToken)> = Vec::new();
    let mut len: usize = 0;

    for step in 0..steps {
        match rng.below(100) {
            0..=39 => {
                let val = rng.next() as u32;
                p.push(val);
                v.push(val);
                len += 1;
            }
            40..=64 => {
                if len == 0 {
                    continue;
                }
                let idx = rng.below(len as u64) as u32;
                let val = rng.next() as u32;
                p.set(idx, val);
                v.set(idx, val);
            }
            65..=79 => {
                if len == 0 {
                    continue;
                }
                let idx = rng.below(len as u64) as u32;
                assert_eq!(p.get(idx), v.get(idx), "step {step}: get({idx}) diverged");
            }
            80..=86 => {
                assert_eq!(p.pop(), v.pop(), "step {step}: pop diverged");
                len = len.saturating_sub(1);
            }
            87..=93 => {
                if marks.len() >= 12 {
                    continue;
                }
                marks.push((
                    p.mark(prod::ShrinkPolicy::Never),
                    v.mark(verus::vec::ShrinkPolicy::Never),
                ));
            }
            _ => {
                if marks.is_empty() {
                    continue;
                }
                let idx = rng.below(marks.len() as u64) as usize;
                let (tp, tv) = marks[idx];
                p.restore(tp);
                v.restore(tv);
                marks.truncate(idx);
                len = p.len() as usize;
            }
        }
    }

    for i in 0..len as u32 {
        assert_eq!(p.get(i), v.get(i), "final content diverged at {i}");
    }
}

#[test]
fn differential_vec_parallel() {
    for seed in [2, 0xFACE, 0xDECAF, 99, 31337] {
        vec_trace_parallel(seed, 2000);
    }
}

// ---------------------------------------------------------------------------
// AppendOnlyVec differential.
// ---------------------------------------------------------------------------

fn aov_trace(seed: u64, steps: usize) {
    let mut p: prod::AppendOnlyVec<u32, true> = prod::AppendOnlyVec::new();
    let mut v: verus::append_only_vec::AppendOnlyVec<u32, true> =
        verus::append_only_vec::AppendOnlyVec::new();

    let mut rng = Rng::new(seed);
    let mut marks: Vec<(prod::VecToken, verus::vec::VecToken)> = Vec::new();

    for step in 0..steps {
        match rng.below(100) {
            0..=49 => {
                let val = rng.next() as u32;
                let ip = p.push(val);
                let iv = v.push(val);
                assert_eq!(ip, iv, "step {step}: push index diverged");
            }
            50..=79 => {
                if p.is_empty() {
                    continue;
                }
                let idx = rng.below(p.len() as u64) as usize;
                assert_eq!(*p.get(idx), *v.get(idx), "step {step}: get diverged");
            }
            80..=89 => {
                if marks.len() >= 12 {
                    continue;
                }
                marks.push((
                    p.mark(prod::ShrinkPolicy::Never),
                    v.mark(verus::vec::ShrinkPolicy::Never),
                ));
            }
            _ => {
                if marks.is_empty() {
                    continue;
                }
                let idx = rng.below(marks.len() as u64) as usize;
                let (tp, tv) = marks[idx];
                p.restore(tp);
                v.restore(tv);
                marks.truncate(idx);
            }
        }
        assert_eq!(p.len(), v.len(), "step {step}: len diverged");
    }

    for i in 0..p.len() {
        assert_eq!(*p.get(i), *v.get(i), "final content diverged at {i}");
    }
}

#[test]
fn differential_append_only_vec() {
    for seed in [3, 0xABCD, 555, 2024, 0xFEED] {
        aov_trace(seed, 2000);
    }
}

// ---------------------------------------------------------------------------
// Map differential: production Map<u32, u32> vs verus SpMap<u32, u32> (Copy
// keys — the pre-Phase-5.1 common surface). insert / id_of / contains_key /
// log_len / mark / restore.
// ---------------------------------------------------------------------------

fn map_trace(seed: u64, steps: usize) {
    let mut p: prod::Map<u32, u32, true> = prod::Map::new();
    let mut v: verus::map::SpMap<u32, u32, true> = verus::map::SpMap::new();

    let mut rng = Rng::new(seed);
    let mut marks: Vec<(prod::MapToken, verus::map::MapToken)> = Vec::new();

    for step in 0..steps {
        match rng.below(100) {
            0..=44 => {
                // Small key space forces overwrite-shadow traffic.
                let key = rng.below(50) as u32;
                let val = rng.next() as u32;
                let ip = p.insert(key, val);
                let iv = v.insert(key, val);
                assert_eq!(ip, iv, "step {step}: insert log-index diverged");
            }
            45..=74 => {
                let key = rng.below(80) as u32;
                assert_eq!(
                    p.id_of(&key),
                    v.id_of(&key),
                    "step {step}: id_of({key}) diverged"
                );
                assert_eq!(
                    p.contains_key(&key),
                    v.contains_key(&key),
                    "step {step}: contains_key({key}) diverged"
                );
                assert_eq!(
                    p.get_by_key(&key),
                    v.get_by_key(&key),
                    "step {step}: get_by_key({key}) diverged"
                );
                assert_eq!(p.len(), v.len(), "step {step}: live-key len diverged");
            }
            75..=87 => {
                if marks.len() >= 12 {
                    continue;
                }
                marks.push((
                    p.mark(prod::ShrinkPolicy::Never),
                    v.mark(verus::vec::ShrinkPolicy::Never),
                ));
            }
            _ => {
                if marks.is_empty() {
                    continue;
                }
                let idx = rng.below(marks.len() as u64) as usize;
                let (tp, tv) = marks[idx];
                p.restore(tp);
                v.restore(tv);
                marks.truncate(idx);
            }
        }
        assert_eq!(p.log_len(), v.log_len(), "step {step}: log_len diverged");
    }

    // Content sweep over the key space.
    for key in 0..100u32 {
        assert_eq!(p.id_of(&key), v.id_of(&key), "final id_of({key}) diverged");
    }
}

#[test]
fn differential_map() {
    for seed in [4, 0x1234, 888, 4096, 0xB00] {
        map_trace(seed, 1500);
    }
}

// ---------------------------------------------------------------------------
// BPlusTreeSet differential: production insert/cursor vs verus
// insert_general/BPlusCursor. Uses the verified DenseId31 (the verus crate's
// witness id type) against a production define_id31 with matching layout.
// ---------------------------------------------------------------------------

prod::define_id31! {
    pub struct DiffId / StoredDiffId, "d";
}

fn bplus_trace(seed: u64, steps: usize) {
    use verus::dense_id::DenseId31;

    let mut p: prod::BPlusTreeSet<DiffId, prod::Layout64U32, prod::BinarySearch, true> =
        prod::BPlusTreeSet::new();
    let mut v: verus::bplus::BPlusTreeSet<
        DenseId31,
        verus::bplus_layout::Layout64U32,
        verus::bplus_search::BinarySearch,
        true,
    > = verus::bplus::BPlusTreeSet::new();

    let mut rng = Rng::new(seed);
    let mut marks: Vec<(prod::BPlusToken, verus::bplus::BPlusToken)> = Vec::new();

    for step in 0..steps {
        match rng.below(100) {
            0..=54 => {
                let raw = rng.below(10_000) as u32;
                let ip = p.insert(DiffId::new(raw));
                let iv = v.insert(DenseId31::new(raw));
                assert_eq!(ip, iv, "step {step}: insert({raw}) diverged");
            }
            55..=79 => {
                let raw = rng.below(10_000) as u32;
                let mut cp = p.cursor();
                cp.seek(DiffId::new(raw));
                let mut cv = verus::bplus::BPlusCursor::new(&v);
                cv.seek(DenseId31::new(raw));
                let got_p = cp.key().map(|k| k.raw());
                let got_v = cv.key().map(|k| k.index() as u32);
                assert_eq!(got_p, got_v, "step {step}: seek({raw}) diverged");
            }
            80..=89 => {
                if marks.len() >= 8 {
                    continue;
                }
                marks.push((
                    p.mark(prod::ShrinkPolicy::Never),
                    v.mark(verus::vec::ShrinkPolicy::Never),
                ));
            }
            _ => {
                if marks.is_empty() {
                    continue;
                }
                let idx = rng.below(marks.len() as u64) as usize;
                let (tp, tv) = marks[idx].clone();
                p.restore(tp);
                v.restore(tv);
                marks.truncate(idx);
            }
        }
        assert_eq!(p.len(), v.len(), "step {step}: len diverged");
    }

    // Full in-order sweep.
    let mut cp = p.cursor();
    cp.seek_first();
    let mut cv = verus::bplus::BPlusCursor::new(&v);
    cv.seek_first();
    loop {
        let kp = cp.key().map(|k| k.raw());
        let kv = cv.key().map(|k| k.index() as u32);
        assert_eq!(kp, kv, "final enumeration diverged");
        if kp.is_none() {
            break;
        }
        cp.step();
        cv.step();
    }
}

#[test]
fn differential_bplus() {
    for seed in [5, 0x5EED, 1234, 9999, 0xACE] {
        bplus_trace(seed, 1200);
    }
}

// ---------------------------------------------------------------------------
// String-keyed map differential (Phase 5.1: Clone keys). Exercises the
// registry shape: String keys, overwrite shadows, get_by_key/len/mark/restore.
// ---------------------------------------------------------------------------

fn map_string_trace(seed: u64, steps: usize) {
    let mut p: prod::Map<String, u32, true> = prod::Map::new();
    let mut v: verus::map::SpMap<String, u32, true> = verus::map::SpMap::new();

    let mut rng = Rng::new(seed);
    let mut marks: Vec<(prod::MapToken, verus::map::MapToken)> = Vec::new();

    for step in 0..steps {
        match rng.below(100) {
            0..=44 => {
                let key = format!("k{}", rng.below(40));
                let val = rng.next() as u32;
                let ip = p.insert(key.clone(), val);
                let iv = v.insert(key, val);
                assert_eq!(ip, iv, "step {step}: insert log-index diverged");
            }
            45..=74 => {
                let key = format!("k{}", rng.below(60));
                assert_eq!(
                    p.get_by_key(&key),
                    v.get_by_key(&key),
                    "step {step}: get_by_key({key}) diverged"
                );
                assert_eq!(p.len(), v.len(), "step {step}: live-key len diverged");
                assert_eq!(p.is_empty(), v.is_empty());
            }
            75..=87 => {
                if marks.len() >= 10 {
                    continue;
                }
                marks.push((
                    p.mark(prod::ShrinkPolicy::Never),
                    v.mark(verus::vec::ShrinkPolicy::Never),
                ));
            }
            _ => {
                if marks.is_empty() {
                    continue;
                }
                let idx = rng.below(marks.len() as u64) as usize;
                let (tp, tv) = marks[idx];
                p.restore(tp);
                v.restore(tv);
                marks.truncate(idx);
            }
        }
        assert_eq!(p.log_len(), v.log_len(), "step {step}: log_len diverged");
    }

    // Content sweep: iter yields the same log (insertion order incl. shadows).
    let pv: Vec<(String, u32)> = p.iter().cloned().collect();
    let vv: Vec<(String, u32)> = v.iter().cloned().collect();
    assert_eq!(pv, vv, "final log content diverged");
}

#[test]
fn differential_map_string_keys() {
    for seed in [6, 0xD1FF, 2468, 0xF00D, 777] {
        map_string_trace(seed, 1200);
    }
}

// ---------------------------------------------------------------------------
// SparseSet differential (Phase 5.3: constructors). add/remove/get/contains/
// len + mark/restore, ids pinned by the oracle-free direct comparison.
// ---------------------------------------------------------------------------

fn sparse_set_trace(seed: u64, steps: usize) {
    use prod::IndexLike as ProdIndexLike;

    let mut p = prod::SparseSet::<u32, u32, prod::ParallelStore<u32, u32>, true>::new();
    let mut v = verus::sparse_set::SparseSet::<
        u32,
        u32,
        verus::parallel_store::ParallelStore<u32, u32>,
        true,
    >::new();

    let mut rng = Rng::new(seed);
    let mut live_ids: Vec<u32> = Vec::new();
    let mut marks: Vec<(
        prod::SparseSetToken,
        verus::sparse_set::SparseSetToken,
        Vec<u32>,
    )> = Vec::new();

    for step in 0..steps {
        match rng.below(100) {
            0..=39 => {
                let val = rng.next() as u32;
                let ip = p.add(val);
                let iv = v.add(val);
                assert_eq!(ip, iv, "step {step}: add returned different ids");
                live_ids.push(ip);
            }
            40..=59 => {
                if live_ids.is_empty() {
                    continue;
                }
                let k = rng.below(live_ids.len() as u64) as usize;
                let id = live_ids.swap_remove(k);
                p.remove(id);
                v.remove(id);
            }
            60..=79 => {
                if live_ids.is_empty() {
                    continue;
                }
                let k = rng.below(live_ids.len() as u64) as usize;
                let id = live_ids[k];
                assert_eq!(
                    p.contains(id),
                    v.contains(id),
                    "step {step}: contains diverged"
                );
                assert_eq!(p.get(id), v.get(id), "step {step}: get diverged");
            }
            80..=89 => {
                if marks.len() >= 8 {
                    continue;
                }
                marks.push((
                    p.mark(prod::ShrinkPolicy::Never),
                    v.mark(verus::vec::ShrinkPolicy::Never),
                    live_ids.clone(),
                ));
            }
            _ => {
                if marks.is_empty() {
                    continue;
                }
                let idx = rng.below(marks.len() as u64) as usize;
                let (tp, tv, snap_ids) = marks[idx].clone();
                p.restore(tp);
                v.restore(tv);
                live_ids = snap_ids;
                marks.truncate(idx);
            }
        }
        assert_eq!(
            p.len().as_usize(),
            {
                let l: u32 = v.len();
                l as usize
            },
            "step {step}: len diverged"
        );
    }

    for &id in &live_ids {
        assert_eq!(
            p.contains(id),
            v.contains(id),
            "final contains diverged for {id}"
        );
        if p.contains(id) {
            assert_eq!(p.get(id), v.get(id), "final get diverged for {id}");
        }
    }
}

#[test]
fn differential_sparse_set() {
    for seed in [7, 0x5CA1, 4242, 0xBEAD, 616] {
        sparse_set_trace(seed, 1500);
    }
}

// ---------------------------------------------------------------------------
// Byte-accounting differential (Phase 9.2): capacity-based reporting matching
// production's formulas. `tracking_bytes` must agree EXACTLY: both sides push
// identical element sequences into std::Vecs of identically-sized elements
// ((T, I) diff entries, {saved_len: I, diff_start: usize} frames, (u32, u32)
// fork origins), and std::Vec's growth is deterministic. `total_bytes` differs
// by design in two places — the verus ContainerId is u64 (checked-allocation
// fix) vs production's u32, and the packed CaptureBits words vec grows
// word-at-a-time vs production's resize-at-prepare_mark — so it is checked at
// the formula level instead (struct size included, store capacity included).
// ---------------------------------------------------------------------------

fn bytes_trace(seed: u64, steps: usize) {
    type VParallel =
        verus::vec::Vec<u64, u32, verus::parallel_store::ParallelStore<u64, u32>, true>;
    let mut p: prod::VecP<u64, u32, true> = prod::VecP::new();
    let mut v: VParallel = VParallel::new();

    let mut rng = Rng::new(seed);
    let mut marks: Vec<(prod::VecToken, verus::vec::VecToken)> = Vec::new();
    let mut len: usize = 0;

    for step in 0..steps {
        match rng.below(100) {
            0..=44 => {
                let val = rng.next();
                p.push(val);
                v.push(val);
                len += 1;
            }
            45..=69 => {
                if len == 0 {
                    continue;
                }
                let idx = rng.below(len as u64) as u32;
                let val = rng.next();
                p.set(idx, val);
                v.set(idx, val);
            }
            70..=79 => {
                p.pop();
                v.pop();
                len = len.saturating_sub(1);
            }
            80..=89 => {
                if marks.len() >= 12 {
                    continue;
                }
                let tp = p.mark(prod::ShrinkPolicy::Never);
                let tv = v.mark(verus::vec::ShrinkPolicy::Never);
                marks.push((tp, tv));
            }
            _ => {
                if marks.is_empty() {
                    continue;
                }
                let idx = rng.below(marks.len() as u64) as usize;
                let (tp, tv) = marks[idx];
                p.restore(tp);
                v.restore(tv);
                marks.truncate(idx);
                len = p.len() as usize;
            }
        }

        // Tracking bytes agree exactly (same capacity-based formula over
        // identically-laid-out element types and identical growth histories).
        assert_eq!(
            p.tracking_bytes(),
            v.tracking_bytes(),
            "step {step}: tracking_bytes diverged"
        );

        // total_bytes formula checks (see the header comment for why exact
        // equality is out of scope): includes the struct itself and at least
        // the data-capacity term of the store on top of tracking.
        let vt = v.total_bytes();
        assert!(
            vt >= core::mem::size_of::<VParallel>()
                + v.tracking_bytes()
                + len * core::mem::size_of::<u64>(),
            "step {step}: total_bytes below struct + tracking + data floor"
        );
        let pt = p.total_bytes();
        assert!(
            pt >= core::mem::size_of::<prod::VecP<u64, u32, true>>()
                + p.tracking_bytes()
                + len * core::mem::size_of::<u64>(),
            "step {step}: production total_bytes below its own floor (harness bug)"
        );
    }
}

#[test]
fn differential_bytes() {
    for seed in [3, 0xB17E5, 909, 0xFEED, 21] {
        bytes_trace(seed, 2000);
    }
}

// ---------------------------------------------------------------------------
// Class-ring byte-accounting differential (the consumer swap).
//
// `tests/layout_parity.rs` asserts the two ring cells are the same 12 bytes;
// that is the *static* half of the memory claim. This is the dynamic half: over
// a randomized merge/mark/restore trace, the verified ring's retained history
// must cost exactly what the hand-rolled ring's did. Both log `(cell, u32)` per
// captured write — 16 bytes at 31-bit ids, not the 24 a `usize`-indexed store
// would spend — so `tracking_bytes()` has to agree EXACTLY, not approximately.
//
// It is a separate trace from `bytes_trace` because the shapes differ in the way
// that matters: a ring merge writes TWO cells per operation (survivor and
// absorbed), so the diff log grows twice as fast per op and first-write-wins
// dedup bites at a different point. A vec trace cannot exercise that.
// ---------------------------------------------------------------------------

fn class_ring_bytes_trace(seed: u64, steps: usize) {
    use containers_conformance::prod_class_ring::{self as pring, PNodeId};
    use verus::opt::DenseId as _;
    verus::define_id31! { pub struct VNodeId / SVNodeId, "n"; }

    const N: usize = 4_000;
    let mut p = pring::build::<true>(N);
    let mut v: verus::CircularList<verus::Opt<u32>, VNodeId, true> = verus::CircularList::new();
    for i in 0..N {
        v.add_singleton(verus::Opt::some(i as u32));
    }

    // Both sides start with identically-grown backing vectors, so tracking
    // starts at parity before a single mark.
    assert_eq!(
        p.tracking_bytes(),
        v.tracking_bytes(),
        "seed {seed}: tracking_bytes diverged before any mark"
    );

    let mut rng = Rng::new(seed);
    // Ring membership is not tracked here (the merge *result* is differential-
    // tested elsewhere); this trace is about allocation, so it only needs the
    // operation sequences to be identical on both sides.
    let mut marks: Vec<(prod::VecToken, verus::circular_list::CircularListToken)> = Vec::new();

    for step in 0..steps {
        match rng.below(100) {
            // Merge two distinct nodes. Splicing already-merged nodes is fine
            // (it splits, which is the same write pattern), so no bookkeeping is
            // needed to keep the two sides in step — only the ids must match.
            0..=74 => {
                let a = rng.below(N as u64) as usize;
                let b = rng.below(N as u64) as usize;
                if a == b {
                    continue;
                }
                pring::splice(&mut p, PNodeId::new(a as u32), PNodeId::new(b as u32));
                let (vs, vb) = (VNodeId::from_usize(a), VNodeId::from_usize(b));
                v.splice(vs, vb);
                let mut payload = v.payload_of(vb);
                payload.set_none();
                v.set_payload(vb, payload);
            }
            75..=89 => {
                if marks.len() >= 12 {
                    continue;
                }
                let tp = p.mark(prod::ShrinkPolicy::Never);
                let tv = v.mark(verus::vec::ShrinkPolicy::Never);
                marks.push((tp, tv));
            }
            _ => {
                if marks.is_empty() {
                    continue;
                }
                let idx = rng.below(marks.len() as u64) as usize;
                let (tp, tv) = marks[idx];
                p.restore(tp);
                v.restore(tv);
                marks.truncate(idx);
            }
        }

        // THE claim: identical retained-history cost at every step. Exact
        // equality is right here for the same reason as `bytes_trace` — both
        // sides push identical sequences into std::Vecs of identically-sized
        // elements ((cell, u32) diff entries, {saved_len: u32, diff_start:
        // usize} frames, (u32, u32) fork origins) and std::Vec's growth is
        // deterministic.
        assert_eq!(
            p.tracking_bytes(),
            v.tracking_bytes(),
            "seed {seed} step {step}: ring tracking_bytes diverged"
        );
    }

    // Whole-container footprint: same 12-byte cell, same capacity growth history,
    // same 16-byte diff entries, so the ONLY permitted difference is the struct
    // header — the verus ContainerId is u64 vs production's u32 (the
    // checked-allocation fix noted in `bytes_trace`'s header), which measures as
    // exactly 8 bytes on a ~52 KB container. The ghost `model`/`model_snapshots`
    // fields are erased and cost nothing at runtime, which this is also the check
    // for: a ghost field that accidentally materialized would blow this bound by
    // far more than 8 bytes.
    const HEADER_SLACK: usize = 8;
    let (pt, vt) = (p.total_bytes(), v.total_bytes());
    assert!(
        vt <= pt + HEADER_SLACK,
        "seed {seed}: verus ring total_bytes {vt} exceeds production's {pt} by more \
         than the {HEADER_SLACK}-byte ContainerId-width allowance"
    );
}

#[test]
fn differential_class_ring_bytes() {
    for seed in [11, 0xC1A55, 777, 0xDEFACE, 5] {
        class_ring_bytes_trace(seed, 1200);
    }
}
