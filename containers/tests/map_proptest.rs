// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
use proptest::prelude::*;
use semi_persistent_containers::{Map, MapToken, ShrinkPolicy};

#[derive(Clone, Debug)]
enum Op {
    Insert(String, u32),
    GetByKey(String),
    Mark,
    Restore(usize),
}

fn op_strategy() -> impl Strategy<Value = Op> {
    let key = "[a-z]{1,4}";
    prop_oneof![
        50 => (key, any::<u32>()).prop_map(|(k, v)| Op::Insert(k, v)),
        30 => key.prop_map(Op::GetByKey),
        15 => Just(Op::Mark),
        10 => any::<usize>().prop_map(Op::Restore),
    ]
}

fn run_ops(ops: Vec<Op>) {
    let mut m = Map::<String, u32>::new();
    let mut oracle = std::collections::HashMap::<String, u32>::new();
    let mut snapshots: Vec<(MapToken, std::collections::HashMap<String, u32>)> = Vec::new();

    for op in ops {
        match op {
            Op::Insert(key, val) => {
                m.insert(key.clone(), val);
                oracle.insert(key, val);
            }
            Op::GetByKey(key) => {
                let got = m.get_by_key(&key).copied();
                let expected = oracle.get(&key).copied();
                assert_eq!(got, expected, "get mismatch for key {key:?}");
            }
            Op::Mark => {
                if snapshots.len() >= 20 {
                    continue;
                }
                let token = m.mark(ShrinkPolicy::Never);
                snapshots.push((token, oracle.clone()));
            }
            Op::Restore(idx) => {
                if snapshots.is_empty() {
                    continue;
                }
                let idx = idx % snapshots.len();
                let (token, snap) = snapshots[idx].clone();
                m.restore(token);
                oracle = snap;
                snapshots.truncate(idx);
            }
        }
    }

    // Final consistency: every oracle key is in the map with the right value.
    for (k, v) in &oracle {
        assert_eq!(m.get_by_key(k), Some(v), "final mismatch for key {k:?}");
    }
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(50))]

    #[test]
    fn map_proptest(ops in proptest::collection::vec(op_strategy(), 1..300)) {
        run_ops(ops);
    }
}
