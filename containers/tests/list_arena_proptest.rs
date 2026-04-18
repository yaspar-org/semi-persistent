// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
use proptest::prelude::*;
use semi_persistent_containers::{ListArena, ListArenaToken, ShrinkPolicy};

semi_persistent_containers::define_id31! { pub struct TestElem / StoredTestElem, "e"; }
semi_persistent_containers::define_id31! { pub struct ListId / StoredListId, "l"; }
semi_persistent_containers::define_id31! { pub struct NodeId / StoredNodeId, "n"; }

type Arena = ListArena<TestElem, ListId, NodeId, true>;

/// Oracle: each list is a Vec<u32>, keyed by list index.
#[derive(Clone, Debug)]
struct Oracle {
    lists: Vec<Vec<u32>>,
}

impl Oracle {
    fn new() -> Self {
        Self { lists: Vec::new() }
    }
    fn new_list(&mut self) -> usize {
        let id = self.lists.len();
        self.lists.push(Vec::new());
        id
    }
    fn prepend(&mut self, list: usize, val: u32) {
        self.lists[list].insert(0, val);
    }
    fn iter(&self, list: usize) -> &[u32] {
        &self.lists[list]
    }
}

#[derive(Clone, Debug)]
enum Op {
    NewList,
    Prepend(usize, u32),
    CheckIter(usize),
    Mark,
    Restore(usize),
}

fn op_strategy() -> impl Strategy<Value = Op> {
    prop_oneof![
        15 => Just(Op::NewList),
        50 => (any::<usize>(), 0..1000u32).prop_map(|(l, v)| Op::Prepend(l, v)),
        20 => any::<usize>().prop_map(Op::CheckIter),
        10 => Just(Op::Mark),
        8 => any::<usize>().prop_map(Op::Restore),
    ]
}

fn collect(arena: &Arena, list: ListId) -> Vec<u32> {
    arena.iter(list).map(|e| e.raw()).collect()
}

fn run_ops(ops: Vec<Op>) {
    let mut arena = Arena::new();
    let mut oracle = Oracle::new();
    let mut list_ids: Vec<ListId> = Vec::new();
    let mut snapshots: Vec<(ListArenaToken, Oracle, Vec<ListId>)> = Vec::new();

    for op in ops {
        match op {
            Op::NewList => {
                let id = arena.new_list();
                list_ids.push(id);
                oracle.new_list();
            }
            Op::Prepend(l, val) => {
                if list_ids.is_empty() {
                    continue;
                }
                let l = l % list_ids.len();
                arena.prepend(list_ids[l], TestElem::new(val));
                oracle.prepend(l, val);
            }
            Op::CheckIter(l) => {
                if list_ids.is_empty() {
                    continue;
                }
                let l = l % list_ids.len();
                let got = collect(&arena, list_ids[l]);
                let expected = oracle.iter(l);
                assert_eq!(got, expected, "iter mismatch for list {l}");
            }
            Op::Mark => {
                if snapshots.len() >= 10 {
                    continue;
                }
                let token = arena.mark(ShrinkPolicy::Never);
                snapshots.push((token, oracle.clone(), list_ids.clone()));
            }
            Op::Restore(idx) => {
                if snapshots.is_empty() {
                    continue;
                }
                let idx = idx % snapshots.len();
                let (token, snap_oracle, snap_ids) = snapshots[idx].clone();
                arena.restore(token);
                oracle = snap_oracle;
                list_ids = snap_ids;
                snapshots.truncate(idx);
            }
        }
    }

    // Final consistency check.
    for (i, &lid) in list_ids.iter().enumerate() {
        let got = collect(&arena, lid);
        let expected = oracle.iter(i);
        assert_eq!(got, expected, "final mismatch for list {i}");
    }
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(50))]

    #[test]
    fn list_arena_proptest(ops in proptest::collection::vec(op_strategy(), 1..300)) {
        run_ops(ops);
    }
}
