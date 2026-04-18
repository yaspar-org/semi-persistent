// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
use proptest::prelude::*;
use semi_persistent_containers::ShrinkPolicy;
use semi_persistent_containers::sparse_set::SparseSet;
use std::collections::HashMap;

#[derive(Clone, Debug)]
enum Op {
    Push(u32),
    Remove(usize),
    Get(usize),
    Mark,
    Restore(usize),
}

fn op_strategy() -> impl Strategy<Value = Op> {
    prop_oneof![
        40 => any::<u32>().prop_map(Op::Push),
        20 => any::<usize>().prop_map(Op::Remove),
        20 => any::<usize>().prop_map(Op::Get),
        15 => Just(Op::Mark),
        10 => any::<usize>().prop_map(Op::Restore),
    ]
}

use semi_persistent_containers::sparse_set::SparseSetToken;

fn run_ops(ops: Vec<Op>) {
    let mut ss = SparseSet::<u32, u32, semi_persistent_containers::ParallelStore<u32, u32>>::new();
    // oracle: id → value
    let mut oracle: HashMap<u32, u32> = HashMap::new();
    let mut snapshots: Vec<(SparseSetToken, HashMap<u32, u32>)> = Vec::new();

    for op in ops {
        match op {
            Op::Push(val) => {
                let id = ss.add(val);
                oracle.insert(id, val);
            }
            Op::Remove(raw) => {
                if oracle.is_empty() {
                    continue;
                }
                let ids: Vec<u32> = oracle.keys().copied().collect();
                let id = ids[raw % ids.len()];
                ss.remove(id);
                oracle.remove(&id);
            }
            Op::Get(raw) => {
                if oracle.is_empty() {
                    continue;
                }
                let ids: Vec<u32> = oracle.keys().copied().collect();
                let id = ids[raw % ids.len()];
                assert_eq!(
                    ss.get(id),
                    *oracle.get(&id).unwrap(),
                    "get mismatch for id {id}"
                );
            }
            Op::Mark => {
                if snapshots.len() >= 15 {
                    continue;
                }
                let token = ss.mark(ShrinkPolicy::Never);
                snapshots.push((token, oracle.clone()));
            }
            Op::Restore(idx) => {
                if snapshots.is_empty() {
                    continue;
                }
                let idx = idx % snapshots.len();
                let (token, snap) = snapshots[idx].clone();
                ss.restore(token);
                oracle = snap;
                snapshots.truncate(idx);
            }
        }

        // Invariant: oracle and sparse set agree on contents.
        assert_eq!(ss.len().as_usize(), oracle.len(), "len mismatch");
        for (&id, &val) in &oracle {
            assert!(ss.contains(id), "oracle has {id} but ss doesn't");
            assert_eq!(ss.get(id), val, "value mismatch for {id}");
        }
    }
}

use semi_persistent_containers::IndexLike;

proptest! {
    #![proptest_config(ProptestConfig::with_cases(20))]

    #[test]
    fn sparse_set_proptest(ops in proptest::collection::vec(op_strategy(), 1..500)) {
        run_ops(ops);
    }
}
