// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! `VecT` (TrailStore, chronological capture) differential tests against a
//! `VecP` twin (ParallelStore, unique capture) and a plain-`Vec` oracle.
//!
//! The two disciplines must be observationally identical: the trail store
//! appends a diff entry on EVERY in-frame write (duplicates allowed, ghost
//! flags only) while the parallel store logs first-write-only behind a runtime
//! bitmap, and reconstruction is first-entry-wins for both. Every test drives
//! the same operations through both columns and compares the full contents at
//! every step, including after deep (multi-frame) restores.
use proptest::prelude::*;
use semi_persistent_containers_verus::{ShrinkPolicy, VecP, VecT, VecToken};

fn assert_twins_match(t: &VecT<u32, u32, true>, p: &VecP<u32, u32, true>, ctx: &str) {
    assert_eq!(t.len(), p.len(), "{ctx}: len mismatch");
    for i in 0..t.len() {
        assert_eq!(t.get(i), p.get(i), "{ctx}: content mismatch at {i}");
    }
}

/// Repeated writes to one slot inside one frame: the trail column logs every
/// write, the parallel column logs only the first; restore must agree (the
/// trail's later duplicates are inert under first-entry-wins).
#[test]
fn duplicate_writes_restore_to_first_capture() {
    let mut t = VecT::<u32, u32, true>::new();
    let mut p = VecP::<u32, u32, true>::new();
    for v in 0..8u32 {
        t.try_push(v).unwrap();
        p.try_push(v).unwrap();
    }
    let tk_t = t.try_mark(ShrinkPolicy::Never).unwrap();
    let tk_p = p.try_mark(ShrinkPolicy::Never).unwrap();
    // 100 writes to the same two slots: 200 trail entries, 2 parallel entries.
    for round in 0..100u32 {
        t.set(3u32, round * 7 + 1);
        p.set(3u32, round * 7 + 1);
        t.set(5u32, round * 11 + 2);
        p.set(5u32, round * 11 + 2);
    }
    assert_twins_match(&t, &p, "pre-restore");
    t.try_restore(tk_t).unwrap();
    p.try_restore(tk_p).unwrap();
    assert_twins_match(&t, &p, "post-restore");
    for i in 0..8u32 {
        assert_eq!(t.get(i), i, "restored value at {i}");
    }
}

/// Deep restore across nested frames with duplicate writes in every stratum.
#[test]
fn deep_restore_across_duplicated_strata() {
    let mut t = VecT::<u32, u32, true>::new();
    let mut p = VecP::<u32, u32, true>::new();
    for v in 0..16u32 {
        t.try_push(v * 10).unwrap();
        p.try_push(v * 10).unwrap();
    }
    let mut marks: Vec<(VecToken, VecToken, Vec<u32>)> = Vec::new();
    for depth in 0..6u32 {
        let tk_t = t.try_mark(ShrinkPolicy::Never).unwrap();
        let tk_p = p.try_mark(ShrinkPolicy::Never).unwrap();
        let snapshot: Vec<u32> = (0..t.len()).map(|i| t.get(i)).collect();
        marks.push((tk_t, tk_p, snapshot));
        for w in 0..10u32 {
            let idx = (depth * 3 + w) % 16;
            t.set(idx, depth * 1000 + w);
            p.set(idx, depth * 1000 + w);
            // Duplicate in the same frame.
            t.set(idx, depth * 1000 + w + 500_000);
            p.set(idx, depth * 1000 + w + 500_000);
        }
        assert_twins_match(&t, &p, "after frame writes");
    }
    // Restore straight past four levels to depth 1's mark.
    let (tk_t, tk_p, snapshot) = marks[1].clone();
    t.try_restore(tk_t).unwrap();
    p.try_restore(tk_p).unwrap();
    assert_twins_match(&t, &p, "deep restore");
    for (i, expected) in snapshot.iter().enumerate() {
        assert_eq!(t.get(i as u32), *expected, "deep-restored value at {i}");
    }
}

/// Pop into the marked region, push back over it, then restore: exercises the
/// pop-capture and reentered-slot flag inheritance under the ghost-flag store.
#[test]
fn pop_into_marked_region_and_restore() {
    let mut t = VecT::<u32, u32, true>::new();
    let mut p = VecP::<u32, u32, true>::new();
    for v in 0..10u32 {
        t.try_push(v).unwrap();
        p.try_push(v).unwrap();
    }
    let tk_t = t.try_mark(ShrinkPolicy::Never).unwrap();
    let tk_p = p.try_mark(ShrinkPolicy::Never).unwrap();
    // Pop below the mark, then rebuild over the popped region with new values,
    // writing each slot twice (trail duplicates).
    for _ in 0..6 {
        assert_eq!(t.pop(), p.pop(), "pop twin mismatch");
    }
    for v in 0..8u32 {
        t.try_push(100 + v).unwrap();
        p.try_push(100 + v).unwrap();
        let last_t = t.len() - 1;
        t.set(last_t, 200 + v);
        p.set(last_t, 200 + v);
    }
    assert_twins_match(&t, &p, "after pop/push churn");
    t.try_restore(tk_t).unwrap();
    p.try_restore(tk_p).unwrap();
    assert_twins_match(&t, &p, "post-restore");
    for i in 0..10u32 {
        assert_eq!(t.get(i), i, "restored value at {i}");
    }
}

#[derive(Clone, Debug)]
enum Op {
    Push(u32),
    Set(usize, u32),
    Pop,
    Mark,
    Restore(usize),
}

fn op_strategy() -> impl Strategy<Value = Op> {
    prop_oneof![
        35 => any::<u32>().prop_map(Op::Push),
        35 => (any::<usize>(), any::<u32>()).prop_map(|(i, v)| Op::Set(i, v)),
        10 => Just(Op::Pop),
        10 => Just(Op::Mark),
        10 => any::<usize>().prop_map(Op::Restore),
    ]
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(40))]

    /// Random twin run: VecT and VecP through identical operations, full
    /// contents compared after every operation, oracle checked at restores.
    #[test]
    fn trail_matches_parallel_twin(ops in proptest::collection::vec(op_strategy(), 1..400)) {
        let mut t = VecT::<u32, u32, true>::new();
        let mut p = VecP::<u32, u32, true>::new();
        let mut oracle: Vec<u32> = Vec::new();
        let mut snapshots: Vec<(VecToken, VecToken, Vec<u32>)> = Vec::new();

        for op in ops {
            match op {
                Op::Push(v) => {
                    t.try_push(v).expect("within capacity");
                    p.try_push(v).expect("within capacity");
                    oracle.push(v);
                }
                Op::Set(idx, v) => {
                    if oracle.is_empty() { continue; }
                    let idx = idx % oracle.len();
                    t.set(idx as u32, v);
                    p.set(idx as u32, v);
                    oracle[idx] = v;
                }
                Op::Pop => {
                    let got_t = t.pop();
                    let got_p = p.pop();
                    let expected = oracle.pop();
                    prop_assert_eq!(got_t, expected);
                    prop_assert_eq!(got_p, expected);
                }
                Op::Mark => {
                    if snapshots.len() >= 16 { continue; }
                    let tk_t = t.try_mark(ShrinkPolicy::Never).expect("depth in bounds");
                    let tk_p = p.try_mark(ShrinkPolicy::Never).expect("depth in bounds");
                    snapshots.push((tk_t, tk_p, oracle.clone()));
                }
                Op::Restore(idx) => {
                    if snapshots.is_empty() { continue; }
                    let idx = idx % snapshots.len();
                    let (tk_t, tk_p, snap) = snapshots[idx].clone();
                    t.try_restore(tk_t).expect("own live token");
                    p.try_restore(tk_p).expect("own live token");
                    oracle = snap;
                    snapshots.truncate(idx);
                }
            }
            prop_assert_eq!(t.len() as usize, oracle.len());
            prop_assert_eq!(p.len() as usize, oracle.len());
            for (i, expected) in oracle.iter().enumerate() {
                prop_assert_eq!(t.get(i as u32), *expected);
                prop_assert_eq!(p.get(i as u32), *expected);
            }
        }
    }
}

/// `VecD`: the runtime-selected store must be observationally identical to
/// the oracle for EVERY kind, through marks, deep restores, and duplicate
/// writes (the trail kind) — one op tape, four columns compared in lockstep.
#[test]
fn vecd_kinds_match_oracle() {
    use semi_persistent_containers_verus::{StoreKind, VecD};
    let kinds = [StoreKind::Inline, StoreKind::Parallel, StoreKind::Trail];
    let mut cols: Vec<VecD<u32, u32, true>> = kinds.iter().map(|&k| VecD::new_kind(k)).collect();
    let mut oracle: Vec<u32> = Vec::new();
    let mut snaps: Vec<(Vec<VecToken>, Vec<u32>)> = Vec::new();

    let mut seed = 0x9e3779b9u32;
    let mut rng = move || {
        seed ^= seed << 13;
        seed ^= seed >> 17;
        seed ^= seed << 5;
        seed
    };
    for step in 0..4000u32 {
        match rng() % 100 {
            0..=34 => {
                let v = rng();
                for c in cols.iter_mut() {
                    c.try_push(v).unwrap();
                }
                oracle.push(v);
            }
            35..=74 => {
                if oracle.is_empty() {
                    continue;
                }
                let i = (rng() as usize) % oracle.len();
                let v = rng();
                for c in cols.iter_mut() {
                    c.set(i as u32, v);
                }
                oracle[i] = v;
            }
            75..=84 => {
                let e = oracle.pop();
                for c in cols.iter_mut() {
                    assert_eq!(c.pop(), e, "pop mismatch at step {step}");
                }
            }
            85..=92 => {
                if snaps.len() >= 12 {
                    continue;
                }
                let toks = cols
                    .iter_mut()
                    .map(|c| c.try_mark(ShrinkPolicy::Never).unwrap())
                    .collect();
                snaps.push((toks, oracle.clone()));
            }
            _ => {
                if snaps.is_empty() {
                    continue;
                }
                let i = (rng() as usize) % snaps.len();
                let (toks, snap) = snaps[i].clone();
                for (c, t) in cols.iter_mut().zip(toks) {
                    c.try_restore(t).unwrap();
                }
                oracle = snap;
                snaps.truncate(i);
            }
        }
        for (k, c) in cols.iter().enumerate() {
            assert_eq!(
                c.len() as usize,
                oracle.len(),
                "len mismatch kind {k} step {step}"
            );
        }
    }
    for (i, expected) in oracle.iter().enumerate() {
        for (k, c) in cols.iter().enumerate() {
            assert_eq!(c.get(i as u32), *expected, "kind {k} final mismatch at {i}");
        }
    }
}
