// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Ported production compatibility test: `containers/tests/bplus_proptest.rs`.
//!
//! Exercises the production-shaped surface: `cursor()`, total `insert` on any
//! tree, token-only `restore` (Phase 7), 31-bit macro ids (Phase 6).
//! Gated on `compat-bplus` + `compat-ids` (Phase 8).
use proptest::prelude::*;
use semi_persistent_containers_verus::{
    BPlusToken, BPlusTreeSet, BinarySearch, Layout64U32, ShrinkPolicy,
};

semi_persistent_containers_verus::define_id31! {
    pub struct PropId / StoredPropId, "p";
}

type Tree = BPlusTreeSet<PropId, Layout64U32, BinarySearch, true>;

fn k(n: u32) -> PropId {
    PropId::new(n & 0x7FFF_FFFF)
}

/// Oracle: a sorted `Vec<PropId>` with no duplicates.
#[derive(Clone, Debug)]
struct Oracle(Vec<PropId>);

impl Oracle {
    fn new() -> Self {
        Self(Vec::new())
    }
    fn insert(&mut self, key: PropId) -> bool {
        match self.0.binary_search(&key) {
            Ok(_) => false,
            Err(pos) => {
                self.0.insert(pos, key);
                true
            }
        }
    }
    fn iter(&self) -> &[PropId] {
        &self.0
    }
    fn len(&self) -> usize {
        self.0.len()
    }
}

fn collect(tree: &Tree) -> Vec<PropId> {
    let mut c = tree.cursor();
    c.seek_first();
    std::iter::from_fn(|| {
        let k = c.key();
        c.step();
        k
    })
    .collect()
}

#[derive(Clone, Debug)]
enum Op {
    Insert(u32),
    SeekCheck(u32),
    Mark,
    Restore(usize),
}

fn op_strategy() -> impl Strategy<Value = Op> {
    prop_oneof![
        50 => (0..10000u32).prop_map(Op::Insert),
        20 => (0..10000u32).prop_map(Op::SeekCheck),
        15 => Just(Op::Mark),
        10 => any::<usize>().prop_map(Op::Restore),
    ]
}

fn run_ops(ops: Vec<Op>) {
    let mut tree = Tree::new();
    let mut oracle = Oracle::new();
    let mut snapshots: Vec<(BPlusToken, Oracle)> = Vec::new();

    for op in ops {
        match op {
            Op::Insert(key) => {
                let got = tree.insert(k(key));
                let expected = oracle.insert(k(key));
                assert_eq!(got, expected, "insert mismatch for key {key}");
            }
            Op::SeekCheck(key) => {
                let mut c = tree.cursor();
                c.seek(k(key));
                let got = c.key();
                // Oracle: first element >= key
                let expected = oracle.iter().iter().copied().find(|x| *x >= k(key));
                assert_eq!(got, expected, "seek mismatch for key {key}");
            }
            Op::Mark => {
                if snapshots.len() >= 10 {
                    continue;
                }
                let token = tree.mark(ShrinkPolicy::Never);
                snapshots.push((token, oracle.clone()));
            }
            Op::Restore(idx) => {
                if snapshots.is_empty() {
                    continue;
                }
                let idx = idx % snapshots.len();
                let (token, snap) = snapshots[idx].clone();
                tree.restore(token);
                oracle = snap;
                snapshots.truncate(idx);
            }
        }
    }

    let got = collect(&tree);
    assert_eq!(got, oracle.iter(), "final iteration mismatch");
    assert_eq!(tree.len(), oracle.len(), "final len mismatch");
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(50))]

    #[test]
    fn bplus_proptest(ops in proptest::collection::vec(op_strategy(), 1..500)) {
        run_ops(ops);
    }
}

// Production `from_sorted` parity (Phase 8.3): bulk build equals insert loop.
proptest! {
    #![proptest_config(ProptestConfig::with_cases(20))]

    #[test]
    fn from_sorted_equals_insert_loop(raw in proptest::collection::btree_set(0..100_000u32, 1..2000)) {
        let keys: Vec<PropId> = raw.iter().map(|&x| k(x)).collect();
        let bulk = Tree::from_sorted(&keys);
        let mut incremental = Tree::new();
        for &key in &keys {
            incremental.insert(key);
        }
        assert_eq!(bulk.len(), incremental.len());
        assert_eq!(collect(&bulk), collect(&incremental), "bulk vs incremental content");
    }
}
