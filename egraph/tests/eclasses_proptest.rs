// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
use proptest::prelude::*;
use semi_persistent_egraph::classes::EClasses;
use semi_persistent_egraph::classes::EClassesToken;
use semi_persistent_egraph::containers::ShrinkPolicy;
use semi_persistent_egraph::id::{UseListId, UseNodeId};
use semi_persistent_egraph::{DenseId, ENodeId};
use std::collections::{HashMap, HashSet};

#[derive(Clone, Debug)]
enum Op {
    AddSingleton,
    Merge(usize, usize),
    IterClass(usize),
    Mark,
    Restore(usize),
}

fn op_strategy() -> impl Strategy<Value = Op> {
    prop_oneof![
        40 => Just(Op::AddSingleton),
        30 => (any::<usize>(), any::<usize>()).prop_map(|(a, b)| Op::Merge(a, b)),
        15 => any::<usize>().prop_map(Op::IterClass),
        10 => Just(Op::Mark),
        8 => any::<usize>().prop_map(Op::Restore),
    ]
}

/// Oracle: union-find via HashMap. Each node maps to its representative.
#[derive(Clone, Debug)]
struct Oracle {
    parent: HashMap<u32, u32>,
    next_id: u32,
}

impl Oracle {
    fn new() -> Self {
        Self {
            parent: HashMap::new(),
            next_id: 0,
        }
    }

    fn add(&mut self) -> u32 {
        let id = self.next_id;
        self.parent.insert(id, id);
        self.next_id += 1;
        id
    }

    fn find(&self, mut x: u32) -> u32 {
        while self.parent[&x] != x {
            x = self.parent[&x];
        }
        x
    }

    fn merge(&mut self, a: u32, b: u32) {
        let ra = self.find(a);
        let rb = self.find(b);
        if ra != rb {
            // Flatten: point everything in rb's class to ra
            let keys: Vec<u32> = self.parent.keys().copied().collect();
            for k in keys {
                if self.find(k) == rb {
                    self.parent.insert(k, ra);
                }
            }
        }
    }

    fn class_of(&self, x: u32) -> HashSet<u32> {
        let r = self.find(x);
        self.parent
            .keys()
            .filter(|&&k| self.find(k) == r)
            .copied()
            .collect()
    }

    #[allow(dead_code)]
    fn num_classes(&self) -> usize {
        let reprs: HashSet<u32> = self.parent.keys().map(|&k| self.find(k)).collect();
        reprs.len()
    }
}

fn run_ops(ops: Vec<Op>) {
    let mut ec = EClasses::<ENodeId, UseListId, UseNodeId, true, false>::new();
    let mut oracle = Oracle::new();
    let mut ids: Vec<u32> = Vec::new();
    let mut snapshots: Vec<(EClassesToken, Oracle, Vec<u32>)> = Vec::new();

    for op in ops {
        match op {
            Op::AddSingleton => {
                let raw = oracle.next_id;
                let id = ENodeId::from_usize(raw as usize);
                ec.add_singleton(id);
                oracle.add();
                ids.push(raw);
            }
            Op::Merge(a, b) => {
                if ids.len() < 2 {
                    continue;
                }
                let a_raw = ids[a % ids.len()];
                let b_raw = ids[b % ids.len()];
                if a_raw == b_raw {
                    continue;
                }
                // Find representatives in oracle
                let ra = oracle.find(a_raw);
                let rb = oracle.find(b_raw);
                if ra == rb {
                    continue;
                }
                ec.merge(
                    ENodeId::from_usize(ra as usize),
                    ENodeId::from_usize(rb as usize),
                );
                oracle.merge(ra, rb);
            }
            Op::IterClass(idx) => {
                if ids.is_empty() {
                    continue;
                }
                let raw = ids[idx % ids.len()];
                let expected = oracle.class_of(raw);
                let actual: HashSet<u32> = ec
                    .iter_class(ENodeId::from_usize(raw as usize))
                    .map(|e: ENodeId| e.raw())
                    .collect();
                assert_eq!(actual, expected, "class mismatch for node {raw}");
            }
            Op::Mark => {
                if snapshots.len() >= 15 {
                    continue;
                }
                let tok = ec.mark(ShrinkPolicy::Never);
                snapshots.push((tok, oracle.clone(), ids.clone()));
            }
            Op::Restore(idx) => {
                if snapshots.is_empty() {
                    continue;
                }
                let idx = idx % snapshots.len();
                let (tok, snap_oracle, snap_ids) = snapshots[idx].clone();
                ec.restore(tok);
                oracle = snap_oracle;
                ids = snap_ids;
                snapshots.truncate(idx);
            }
        }
    }

    // Final check: every node's class matches oracle.
    for &raw in &ids {
        let expected = oracle.class_of(raw);
        let actual: HashSet<u32> = ec
            .iter_class(ENodeId::from_usize(raw as usize))
            .map(|e: ENodeId| e.raw())
            .collect();
        assert_eq!(actual, expected, "final class mismatch for node {raw}");
    }
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(20))]

    #[test]
    fn eclasses_proptest(ops in proptest::collection::vec(op_strategy(), 1..500)) {
        run_ops(ops);
    }
}
