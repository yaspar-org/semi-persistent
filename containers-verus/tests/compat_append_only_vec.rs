// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Ported production compatibility test:
//! `containers/tests/append_only_vec_proptest.rs`. Gated on `compat-core`.
use proptest::prelude::*;
use semi_persistent_containers_verus::{AppendOnlyVec, ShrinkPolicy, VecToken};

#[derive(Clone, Debug)]
enum Op {
    Push(u32),
    Get(usize),
    Mark,
    Restore(usize),
}

fn op_strategy() -> impl Strategy<Value = Op> {
    prop_oneof![
        50 => any::<u32>().prop_map(Op::Push),
        30 => any::<usize>().prop_map(Op::Get),
        15 => Just(Op::Mark),
        10 => any::<usize>().prop_map(Op::Restore),
    ]
}

fn run_ops(ops: Vec<Op>) {
    let mut v = AppendOnlyVec::<u32>::new();
    let mut oracle: Vec<u32> = Vec::new();
    let mut snapshots: Vec<(VecToken, Vec<u32>)> = Vec::new();

    for op in ops {
        match op {
            Op::Push(val) => {
                v.try_push(val).expect("compat: within capacity");
                oracle.push(val);
            }
            Op::Get(idx) => {
                if oracle.is_empty() {
                    continue;
                }
                let idx = idx % oracle.len();
                assert_eq!(*v.get(idx), oracle[idx], "get mismatch at {idx}");
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

    assert_eq!(v.len(), oracle.len(), "final len mismatch");
    for (i, expected) in oracle.iter().enumerate() {
        assert_eq!(*v.get(i), *expected, "final mismatch at {i}");
    }
    // `iter` / `as_slice` compatibility.
    #[cfg(feature = "compat-composites")]
    {
        let collected: Vec<u32> = v.iter().copied().collect();
        assert_eq!(collected, oracle, "iter mismatch");
        assert_eq!(v.as_slice(), &oracle[..], "as_slice mismatch");
    }
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(50))]

    #[test]
    fn append_only_vec_proptest(ops in proptest::collection::vec(op_strategy(), 1..500)) {
        run_ops(ops);
    }
}
