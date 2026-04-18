// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
use proptest::prelude::*;
use semi_persistent_containers::{AppendOnlyVec, ShrinkPolicy, VecToken};

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
                v.push(val);
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
                let token = v.mark(ShrinkPolicy::Never);
                snapshots.push((token, oracle.clone()));
            }
            Op::Restore(idx) => {
                if snapshots.is_empty() {
                    continue;
                }
                let idx = idx % snapshots.len();
                let (token, snap) = snapshots[idx].clone();
                v.restore(token);
                oracle = snap;
                snapshots.truncate(idx);
            }
        }
    }

    assert_eq!(v.len(), oracle.len(), "final len mismatch");
    for (i, expected) in oracle.iter().enumerate() {
        assert_eq!(*v.get(i), *expected, "final mismatch at {i}");
    }
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(50))]

    #[test]
    fn append_only_vec_proptest(ops in proptest::collection::vec(op_strategy(), 1..500)) {
        run_ops(ops);
    }
}
