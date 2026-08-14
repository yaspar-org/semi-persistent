// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Ported production compatibility test: `containers/tests/vec_proptest.rs`.
//!
//! Gated on `compat-core` + `compat-ids` (migration plan Phase 1.1): the test
//! target builds once Phase 4 (core API parity: `VecI`/`VecP` aliases, root
//! re-exports, `get`/`set` via `impl Into<I>`) and Phase 6 (`define_id31!`,
//! `IdFactory`) have landed. Assertions are unchanged from production.
use proptest::prelude::*;
use semi_persistent_containers_verus::{DenseId, IdFactory};
use semi_persistent_containers_verus::{ShrinkPolicy, VecToken};

semi_persistent_containers_verus::define_id31! {
    pub struct TestId / StoredTestId, "t";
}

#[derive(Clone, Debug)]
enum Op {
    Push(u32),
    Set(usize, u32),
    Get(usize),
    Pop,
    Mark,
    Restore(usize),
}

fn op_strategy() -> impl Strategy<Value = Op> {
    prop_oneof![
        40 => any::<u32>().prop_map(Op::Push),
        30 => (any::<usize>(), any::<u32>()).prop_map(|(i, v)| Op::Set(i, v)),
        20 => any::<usize>().prop_map(Op::Get),
        10 => Just(Op::Pop),
        15 => Just(Op::Mark),
        10 => any::<usize>().prop_map(Op::Restore),
    ]
}

fn run_ops(ops: Vec<Op>, mut v: semi_persistent_containers_verus::VecI<u32, u32, true>) {
    let mut oracle: Vec<u32> = Vec::new();
    let mut snapshots: Vec<(VecToken, Vec<u32>)> = Vec::new();

    for op in ops {
        match op {
            Op::Push(val) => {
                v.try_push(val).expect("compat: within capacity");
                oracle.push(val);
            }
            Op::Set(idx, val) => {
                if oracle.is_empty() {
                    continue;
                }
                let idx = idx % oracle.len();
                v.set(idx as u32, val);
                oracle[idx] = val;
            }
            Op::Get(idx) => {
                if oracle.is_empty() {
                    continue;
                }
                let idx = idx % oracle.len();
                assert_eq!(v.get(idx as u32), oracle[idx], "get mismatch at {idx}");
            }
            Op::Pop => {
                let got = v.pop();
                let expected = oracle.pop();
                assert_eq!(got, expected, "pop mismatch");
            }
            Op::Mark => {
                if snapshots.len() >= 20 {
                    continue;
                }
                let token = v
                    .try_mark(ShrinkPolicy::Never)
                    .expect("compat: depth in bounds");
                snapshots.push((token, oracle.clone()));
            }
            Op::Restore(idx) => {
                if snapshots.is_empty() {
                    continue;
                }
                let idx = idx % snapshots.len();
                let (token, snap) = snapshots[idx].clone();
                v.try_restore(token).expect("compat: own live token");
                oracle = snap;
                snapshots.truncate(idx);
            }
        }
    }

    // Final consistency check.
    let len = oracle.len();
    assert_eq!(v.len(), len as u32, "final len mismatch");
    for (i, expected) in oracle.iter().enumerate() {
        assert_eq!(v.get(i as u32), *expected, "final mismatch at {i}");
    }
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(20))]

    #[test]
    fn vec_inline_proptest(ops in proptest::collection::vec(op_strategy(), 1..500)) {
        run_ops(ops, semi_persistent_containers_verus::VecI::<u32, u32, true>::new());
    }
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(20))]

    #[test]
    fn vec_parallel_proptest(ops in proptest::collection::vec(op_strategy(), 1..500)) {
        let v = semi_persistent_containers_verus::VecP::<u32, u32, true>::new();
        let mut oracle: Vec<u32> = Vec::new();
        let mut snapshots: Vec<(VecToken, Vec<u32>)> = Vec::new();
        let mut v = v;

        for op in ops {
            match op {
                Op::Push(val) => {
                    v.try_push(val).expect("compat: within capacity");
                    oracle.push(val);
                }
                Op::Set(idx, val) => {
                    if oracle.is_empty() { continue; }
                    let idx = idx % oracle.len();
                    v.set(idx as u32, val);
                    oracle[idx] = val;
                }
                Op::Get(idx) => {
                    if oracle.is_empty() { continue; }
                    let idx = idx % oracle.len();
                    assert_eq!(v.get(idx as u32), oracle[idx]);
                }
                Op::Pop => {
                    assert_eq!(v.pop(), oracle.pop());
                }
                Op::Mark => {
                    if snapshots.len() >= 20 { continue; }
                    let token = v.try_mark(ShrinkPolicy::Never).expect("compat: depth in bounds");
                    snapshots.push((token, oracle.clone()));
                }
                Op::Restore(idx) => {
                    if snapshots.is_empty() { continue; }
                    let idx = idx % snapshots.len();
                    let (token, snap) = snapshots[idx].clone();
                    v.try_restore(token).expect("compat: own live token");
                    oracle = snap;
                    snapshots.truncate(idx);
                }
            }
        }

        let len = oracle.len();
        assert_eq!(v.len(), len as u32);
        for (i, expected) in oracle.iter().enumerate() {
            assert_eq!(v.get(i as u32), *expected);
        }
    }
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(20))]

    #[test]
    fn vec_dense_id_proptest(ops in proptest::collection::vec(op_strategy(), 1..500)) {
        // VecI storing TestId values, indexed by u32 (TestId::Index)
        let mut v = semi_persistent_containers_verus::VecI::<TestId, u32, true>::new();
        let mut oracle: Vec<TestId> = Vec::new();
        let mut snapshots: Vec<(VecToken, Vec<TestId>)> = Vec::new();
        let mut factory = IdFactory::<TestId>::new();

        for op in ops {
            match op {
                Op::Push(_) => {
                    if let Some(id) = factory.try_alloc() {
                        v.try_push(id).expect("compat: within capacity");
                        oracle.push(id);
                    }
                }
                Op::Set(idx, raw) => {
                    if oracle.is_empty() { continue; }
                    let idx = idx % oracle.len();
                    let val = TestId::from_usize(raw as usize % factory.count().max(1));
                    v.set(idx as u32, val);
                    oracle[idx] = val;
                }
                Op::Get(idx) => {
                    if oracle.is_empty() { continue; }
                    let idx = idx % oracle.len();
                    assert_eq!(v.get(idx as u32), oracle[idx]);
                }
                Op::Pop => {
                    assert_eq!(v.pop(), oracle.pop());
                }
                Op::Mark => {
                    if snapshots.len() >= 20 { continue; }
                    let token = v.try_mark(ShrinkPolicy::Never).expect("compat: depth in bounds");
                    snapshots.push((token, oracle.clone()));
                }
                Op::Restore(idx) => {
                    if snapshots.is_empty() { continue; }
                    let idx = idx % snapshots.len();
                    let (token, snap) = snapshots[idx].clone();
                    v.try_restore(token).expect("compat: own live token");
                    oracle = snap;
                    snapshots.truncate(idx);
                }
            }
        }

        let len = oracle.len();
        assert_eq!(v.len(), len as u32);
        for (i, expected) in oracle.iter().enumerate() {
            assert_eq!(v.get(i as u32), *expected);
        }
    }
}
