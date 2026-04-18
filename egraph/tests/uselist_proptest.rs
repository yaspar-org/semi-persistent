// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
use proptest::prelude::*;
use semi_persistent_egraph::ENodeId;
use semi_persistent_egraph::classes::EClasses;
use semi_persistent_egraph::containers::ShrinkPolicy;
use semi_persistent_egraph::id::{UseListId, UseNodeId};
use std::collections::HashMap;

type EC = EClasses<ENodeId, UseListId, UseNodeId, true, false>;

#[derive(Clone, Debug)]
struct Oracle {
    parent: HashMap<ENodeId, ENodeId>,
    uses: HashMap<ENodeId, Vec<ENodeId>>,
}

impl Oracle {
    fn new() -> Self {
        Self {
            parent: HashMap::new(),
            uses: HashMap::new(),
        }
    }

    fn add(&mut self, id: ENodeId) {
        self.parent.insert(id, id);
        self.uses.insert(id, Vec::new());
    }

    fn find(&self, mut x: ENodeId) -> ENodeId {
        while self.parent[&x] != x {
            x = self.parent[&x];
        }
        x
    }

    fn merge_and_splice(&mut self, surv: ENodeId, abs: ENodeId) {
        self.parent.insert(abs, surv);
        let abs_list = self.uses.remove(&abs).unwrap_or_default();
        self.uses.get_mut(&surv).unwrap().extend(abs_list);
    }

    fn add_use(&mut self, repr: ENodeId, parent: ENodeId) {
        self.uses.get_mut(&repr).unwrap().push(parent);
    }

    fn get_uses(&self, repr: ENodeId) -> Vec<ENodeId> {
        self.uses.get(&repr).cloned().unwrap_or_default()
    }
}

fn do_merge(ec: &mut EC, oracle: &mut Oracle, a: ENodeId, b: ENodeId) {
    let ra = oracle.find(a);
    let rb = oracle.find(b);
    if ra == rb {
        assert!(ec.merge(a, b).is_none());
        return;
    }
    let ra_repr = ec.repr_id(ra).unwrap();
    let rb_repr = ec.repr_id(rb).unwrap();
    let ra_list = ec.use_list_id(ra_repr);
    let rb_list = ec.use_list_id(rb_repr);

    let m = ec.merge(a, b).unwrap();
    let (es, ea) = (m.survivor, m.absorbed);
    let surv_list = if es == ra { ra_list } else { rb_list };
    ec.splice_uses(surv_list, m.absorbed_uses);
    oracle.merge_and_splice(es, ea);
}

fn do_add_use(ec: &mut EC, oracle: &mut Oracle, child: ENodeId, parent: ENodeId) {
    let repr = oracle.find(child);
    let repr_idx = ec.repr_id(repr).unwrap();
    oracle.add_use(repr, parent);
    ec.add_use(repr_idx, parent);
}

fn check_all(ec: &EC, oracle: &Oracle, ids: &[ENodeId]) {
    for &node in ids {
        let repr = oracle.find(node);
        assert_eq!(repr, ec.find_const(node), "find mismatch for {:?}", node);
        if let Some(repr_idx) = ec.repr_id(repr) {
            let expected = oracle.get_uses(repr);
            let actual: Vec<ENodeId> = ec.iter_uses(repr_idx).collect();
            assert_eq!(actual, expected, "use-list mismatch for repr {:?}", repr);
        }
    }
}

/// Build a layered tree structure:
/// - Layer 0: `width` leaf nodes
/// - Layer 1..depth: `width` nodes, each with random parents in layer below
/// - Each node in layer k registers as a use of 1-3 random nodes in layer k-1
///
/// Then merge random pairs in layer 0 and verify use-lists propagate correctly.
fn run_layered(
    width: usize,
    depth: usize,
    uses_per_node: Vec<Vec<usize>>, // [layer][node] → indices into prev layer
    merges: Vec<(usize, usize)>,    // pairs of layer-0 indices to merge
    do_mark_restore: bool,
) {
    let mut ec = EC::new();
    let mut oracle = Oracle::new();
    let mut layers: Vec<Vec<ENodeId>> = Vec::new();
    let mut all_ids: Vec<ENodeId> = Vec::new();
    let mut next_raw = 0u32;

    // Build layers
    for layer_idx in 0..depth {
        let mut layer = Vec::new();
        for _ in 0..width {
            let id = ENodeId::new(next_raw);
            next_raw += 1;
            ec.add_singleton(id);
            oracle.add(id);
            all_ids.push(id);
            layer.push(id);
        }

        // Register uses: each node in this layer uses nodes from previous layer
        if layer_idx > 0 {
            let prev = &layers[layer_idx - 1];
            let layer_uses = if layer_idx - 1 < uses_per_node.len() {
                &uses_per_node[layer_idx - 1]
            } else {
                &vec![]
            };
            for (i, &node) in layer.iter().enumerate() {
                // Each node uses 1-3 children from previous layer
                let base = if i < layer_uses.len() {
                    layer_uses[i]
                } else {
                    i
                };
                // Use the node at `base % prev.len()` as child
                let child = prev[base % prev.len()];
                do_add_use(&mut ec, &mut oracle, child, node);
                // Second child (different)
                let child2 = prev[(base + 1) % prev.len()];
                do_add_use(&mut ec, &mut oracle, child2, node);
            }
        }

        layers.push(layer);
    }

    // Verify before merges
    check_all(&ec, &oracle, &all_ids);

    // Optionally mark
    let token = if do_mark_restore {
        Some(ec.mark(ShrinkPolicy::Never))
    } else {
        None
    };
    let snap_oracle = oracle.clone();

    // Merge pairs in layer 0
    let layer0 = &layers[0];
    for &(ai, bi) in &merges {
        let a = layer0[ai % layer0.len()];
        let b = layer0[bi % layer0.len()];
        do_merge(&mut ec, &mut oracle, a, b);
    }

    // Verify after merges
    check_all(&ec, &oracle, &all_ids);

    // Restore and verify
    if let Some(tok) = token {
        ec.restore(tok);
        oracle = snap_oracle;
        check_all(&ec, &oracle, &all_ids);
    }
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(100))]

    #[test]
    fn layered_small(
        uses in proptest::collection::vec(
            proptest::collection::vec(any::<usize>(), 20), 5
        ),
        merges in proptest::collection::vec(
            (any::<usize>(), any::<usize>()), 0..10
        ),
        do_restore in proptest::bool::ANY,
    ) {
        run_layered(20, 5, uses, merges, do_restore);
    }

    #[test]
    fn layered_medium(
        uses in proptest::collection::vec(
            proptest::collection::vec(any::<usize>(), 100), 5
        ),
        merges in proptest::collection::vec(
            (any::<usize>(), any::<usize>()), 0..50
        ),
        do_restore in proptest::bool::ANY,
    ) {
        run_layered(100, 5, uses, merges, do_restore);
    }

    #[test]
    fn layered_deep(
        uses in proptest::collection::vec(
            proptest::collection::vec(any::<usize>(), 50), 10
        ),
        merges in proptest::collection::vec(
            (any::<usize>(), any::<usize>()), 0..30
        ),
        do_restore in proptest::bool::ANY,
    ) {
        run_layered(50, 10, uses, merges, do_restore);
    }

    #[test]
    fn layered_wide(
        uses in proptest::collection::vec(
            proptest::collection::vec(any::<usize>(), 1000), 3
        ),
        merges in proptest::collection::vec(
            (any::<usize>(), any::<usize>()), 0..200
        ),
        do_restore in proptest::bool::ANY,
    ) {
        run_layered(1000, 3, uses, merges, do_restore);
    }
}
