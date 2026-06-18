// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Same shape as `bplus_proptest` but exercising the u64-backed tree.
//! Parameterized over `NodeLayout` so both 256- and 512-byte node variants
//! are validated against the sorted-vec oracle.
use proptest::prelude::*;
use semi_persistent_containers::{
    BPlusToken, BPlusTreeSet, BinarySearch, IndexLike, Layout256U64, Layout512U64, NodeLayout,
    ShrinkPolicy,
};

semi_persistent_containers::define_id63! {
    pub struct PropId64 / StoredPropId64, "p64";
}

fn k(n: u64) -> PropId64 {
    PropId64::new(n & 0x7FFF_FFFF_FFFF_FFFF)
}

#[derive(Clone, Debug)]
enum Op {
    Insert(u64),
    SeekCheck(u64),
    Mark,
    Restore(usize),
}

fn op_strategy() -> impl Strategy<Value = Op> {
    prop_oneof![
        50 => (0..10_000_000u64).prop_map(Op::Insert),
        20 => (0..10_000_000u64).prop_map(Op::SeekCheck),
        15 => Just(Op::Mark),
        10 => any::<usize>().prop_map(Op::Restore),
    ]
}

fn run_ops<L>(ops: Vec<Op>)
where
    L: NodeLayout<Word = u64>,
    L::ArenaIdx: IndexLike + Default,
    L::Node: Default,
{
    let mut tree: BPlusTreeSet<PropId64, L, BinarySearch, true> = BPlusTreeSet::new();
    let mut oracle: Vec<PropId64> = Vec::new();
    let mut snapshots: Vec<(BPlusToken, Vec<PropId64>)> = Vec::new();

    for op in ops {
        match op {
            Op::Insert(key) => {
                let kk = k(key);
                let got = tree.insert(kk);
                let expected = match oracle.binary_search(&kk) {
                    Ok(_) => false,
                    Err(pos) => {
                        oracle.insert(pos, kk);
                        true
                    }
                };
                assert_eq!(got, expected, "insert mismatch for key {key}");
            }
            Op::SeekCheck(key) => {
                let mut c = tree.cursor();
                c.seek(k(key));
                let got = c.key();
                let expected = oracle.iter().copied().find(|x| *x >= k(key));
                assert_eq!(got, expected, "seek mismatch for key {key}");
            }
            Op::Mark => {
                if snapshots.len() >= 10 {
                    continue;
                }
                snapshots.push((tree.mark(ShrinkPolicy::Never), oracle.clone()));
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

    let mut c = tree.cursor();
    c.seek_first();
    let got: Vec<PropId64> = std::iter::from_fn(|| {
        let k = c.key();
        c.step();
        k
    })
    .collect();
    assert_eq!(got, oracle, "final iteration mismatch");
    assert_eq!(tree.len(), oracle.len(), "final len mismatch");
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(50))]

    #[test]
    fn bplus64_proptest_layout256(ops in proptest::collection::vec(op_strategy(), 1..500)) {
        run_ops::<Layout256U64>(ops);
    }

    #[test]
    fn bplus64_proptest_layout512(ops in proptest::collection::vec(op_strategy(), 1..500)) {
        run_ops::<Layout512U64>(ops);
    }
}
