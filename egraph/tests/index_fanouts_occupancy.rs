// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! `measure_fanouts` reads each family's occupied keys from the map's occupancy
//! list instead of scanning `0..len()` and skipping the empty buckets. The
//! statistics it produces feed the planner, so they have to be the ones the scan
//! produced, not merely close to them: `reference_fanouts` below *is* the scan,
//! and the index build's `FanOuts` must equal it exactly.
//!
//! Exactly is the right comparison, not a tolerance. Both passes accumulate
//! integer bucket sizes in `u128` and divide once at the end, so the visit order
//! cannot move a result; a difference would mean the two passes saw different
//! buckets, which is the failure this fences.
//!
//! The graph is built so the check has something to fail on: the `by_child_pos`
//! key space is several times its occupied keys (asserted, not assumed), the
//! buckets mix operators at the same key so the per-operator tally is live, and
//! merging classes leaves the key space with holes an ascending scan walks over.

use semi_persistent_egraph::EGraph;
use semi_persistent_egraph::config::EGraphConfig;
use semi_persistent_egraph::index::IndexStore;
use semi_persistent_egraph::literal::{NiraLitVal, NiraModel};
use semi_persistent_egraph::nodes::DefaultConfig;
use std::collections::HashMap;

type Cfg = DefaultConfig;
type EG = EGraph<Cfg, NiraLitVal, false, false>;
type O = <Cfg as EGraphConfig>::O;
/// The three fan-out statistics in one comparable shape: `by_repr`, then the
/// `(op, position)` and `op` keyed ones as vectors sorted by key, with each
/// operator as its dense id so the keys order.
type Stats = (f64, Vec<((usize, usize), f64)>, Vec<(usize, f64)>);

/// Leaves, two binary operators over every ordered pair of them, a unary
/// operator over the binary nodes, and a multiset operator so `by_contains` is
/// non-empty as well. Two merges then collapse classes, which both punches holes
/// in the `by_repr` and `by_child_pos` key spaces and puts more than one node in
/// a class.
fn nontrivial() -> EG {
    const LEAVES: usize = 12;
    let mut eg = EG::from_model(&NiraModel);
    let s = eg.intern_sort("E");
    let f = eg.register_op2("f", s, s, s);
    let h = eg.register_op2("h", s, s, s);
    let g = eg.register_op1("g", s, s);
    let add = eg.register_mset("add", s, s);

    let mut leaves = Vec::new();
    for i in 0..LEAVES {
        let op = eg.register_op0(&format!("a{i}"), s);
        leaves.push(eg.add(op, &[]));
    }
    for i in 0..LEAVES {
        for j in 0..LEAVES {
            let x = eg.add(f, &[leaves[i], leaves[j]]);
            // `h` over the same child pair puts two operators under one
            // `by_child_pos` key, which is the whole reason the tally is
            // per-operator.
            let y = eg.add(h, &[leaves[i], leaves[j]]);
            if (i + j) % 3 == 0 {
                eg.add(g, &[x]);
                eg.add(add, &[x, y]);
            }
        }
    }
    eg.rebuild();
    // Collapse two pairs of leaf classes: the surviving representatives keep
    // their buckets and the merged-away ids leave their keys empty.
    eg.merge(leaves[0], leaves[1]);
    eg.merge(leaves[4], leaves[9]);
    eg.rebuild();
    eg
}

/// The fan-out statistics as the key-space scan computed them: every key in
/// `0..len()`, empty buckets skipped. A transcription of the pass this change
/// replaced, kept independent of it — it reads the families through the public
/// accessors and takes each entry's operator from `round_op`.
fn reference_fanouts(ix: &IndexStore<Cfg>) -> Stats {
    let biased = |(sum, sq): (u128, u128)| -> f64 {
        if sum == 0 {
            1.0
        } else {
            sq as f64 / sum as f64
        }
    };
    let tally = |bucket: &[<Cfg as EGraphConfig>::G]| -> HashMap<O, u128> {
        let mut t: HashMap<O, u128> = HashMap::new();
        for &gid in bucket {
            *t.entry(ix.round_op(gid).expect("a full index fills its op table"))
                .or_insert(0) += 1;
        }
        t
    };

    let mut cp: HashMap<(usize, usize), (u128, u128)> = HashMap::new();
    for k in 0..ix.by_child_pos.len() {
        let bucket = ix.by_child_pos.get(k);
        if bucket.is_empty() {
            continue;
        }
        let pos = k / ix.child_pos_stride;
        for (o, c) in tally(bucket) {
            let e = cp.entry((o.to_usize(), pos)).or_insert((0, 0));
            e.0 += c;
            e.1 += c * c;
        }
    }
    let mut ct: HashMap<usize, (u128, u128)> = HashMap::new();
    for k in 0..ix.by_contains.len() {
        let bucket = ix.by_contains.get(k);
        if bucket.is_empty() {
            continue;
        }
        for (o, c) in tally(bucket) {
            let e = ct.entry(o.to_usize()).or_insert((0, 0));
            e.0 += c;
            e.1 += c * c;
        }
    }
    let (mut class_sum, mut class_sq) = (0u128, 0u128);
    for k in 0..ix.by_repr.len() {
        let c = ix.by_repr.get(k).len() as u128;
        class_sum += c;
        class_sq += c * c;
    }

    let mut cp: Vec<_> = cp.into_iter().map(|(k, v)| (k, biased(v))).collect();
    let mut ct: Vec<_> = ct.into_iter().map(|(k, v)| (k, biased(v))).collect();
    cp.sort_by_key(|&(k, _)| k);
    ct.sort_by_key(|&(k, _)| k);
    (biased((class_sum, class_sq)), cp, ct)
}

/// The recorded statistics in the same shape, so the two are comparable.
fn recorded(ix: &IndexStore<Cfg>) -> Stats {
    let mut cp: Vec<_> = ix
        .fanouts
        .by_child_pos
        .iter()
        .map(|(&(o, pos), &v)| ((o.to_usize(), pos), v))
        .collect();
    let mut ct: Vec<_> = ix
        .fanouts
        .by_contains
        .iter()
        .map(|(&o, &v)| (o.to_usize(), v))
        .collect();
    cp.sort_by_key(|&(k, _)| k);
    ct.sort_by_key(|&(k, _)| k);
    (ix.fanouts.by_repr, cp, ct)
}

#[test]
fn occupied_key_pass_matches_the_key_space_scan() {
    let eg = nontrivial();
    let ix = IndexStore::build(&eg);

    // The two passes must actually iterate different things, or agreeing proves
    // nothing: count the occupied keys the scan finds and compare to the key
    // space it walks.
    let occupied = (0..ix.by_child_pos.len())
        .filter(|&k| !ix.by_child_pos.get(k).is_empty())
        .count();
    assert!(
        ix.by_child_pos.len() > 4 * occupied && occupied > 0,
        "by_child_pos key space ({}) must be several times its {occupied} occupied keys, \
         or the scan and the occupancy list do the same work",
        ix.by_child_pos.len()
    );

    let (want_repr, want_cp, want_ct) = reference_fanouts(&ix);
    let (got_repr, got_cp, got_ct) = recorded(&ix);

    // Non-degenerate: several keyed statistics, more than one operator among
    // them, and classes that hold more than one node.
    assert!(want_cp.len() > 4, "by_child_pos statistics: {want_cp:?}");
    assert!(!want_ct.is_empty(), "by_contains statistics: {want_ct:?}");
    assert!(
        want_cp
            .iter()
            .map(|&((o, _), _)| o)
            .collect::<Vec<_>>()
            .windows(2)
            .any(|w| w[0] != w[1]),
        "the by_child_pos buckets must mix operators: {want_cp:?}"
    );
    assert!(want_repr > 1.0, "classes must hold more than one node each");

    assert_eq!(got_repr, want_repr, "by_repr fan-out");
    assert_eq!(got_cp, want_cp, "by_child_pos fan-outs");
    assert_eq!(got_ct, want_ct, "by_contains fan-outs");
}
