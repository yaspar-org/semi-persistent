// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Per-node control flags across recanonicalization, and the
//! `FLAG_CONGRUENT_DUP` invariant.
//!
//! Recanonicalization rewrites a node in place when a child's class merges. It used to
//! rebuild the node with `FixedArityNode::new`, whose flags start at zero, so any flag
//! on that node was silently cleared: a `(subsume t)` was undone by the next merge that
//! recanonicalized `t`, and `t` became matchable again. Both tests below force that
//! path, which needs the child's class to *lose* a merge — the surface language cannot
//! choose the survivor, so these drive the API directly.

use semi_persistent_egraph::EGraph;
use semi_persistent_egraph::literal::{NiraLitVal, NiraModel};
use semi_persistent_egraph::node_types::{FLAG_CONGRUENT_DUP, FLAG_SUBSUMED};
use semi_persistent_egraph::nodes::DefaultConfig;

type EG = EGraph<DefaultConfig, NiraLitVal, false, false>;

/// Grow `keep`'s class with `n` fresh singleton classes, so union-by-size makes it the
/// survivor of a later merge and the other side's stored child ids have to move.
fn pad_class(
    eg: &mut EG,
    sort: <DefaultConfig as semi_persistent_egraph::config::EGraphConfig>::S,
    keep: <DefaultConfig as semi_persistent_egraph::config::EGraphConfig>::G,
    n: usize,
    tag: &str,
) {
    for i in 0..n {
        let op = eg.register_op0(&format!("pad_{tag}_{i}"), sort);
        let id = eg.add(op, &[]);
        eg.merge(id, keep);
    }
}

#[test]
fn recanonize_preserves_subsumed_flag() {
    let mut eg = EG::from_model(&NiraModel);
    let e = eg.intern_sort("E");
    eg.register_op1("g", e, e);
    let a = eg.register_op0("a", e);
    let b = eg.register_op0("b", e);
    let g = eg.ops().id_by_name("g").unwrap();

    let ia = eg.add(a, &[]);
    let ib = eg.add(b, &[]);
    let ga = eg.add(g, &[ia]);
    pad_class(&mut eg, e, ib, 8, "s");
    eg.rebuild();

    eg.subsume(ga);
    assert_ne!(
        eg.node_flags(ga) & FLAG_SUBSUMED,
        0,
        "subsume sets the flag"
    );

    let before = eg.child_at(ga, 0);
    eg.merge(ia, ib);
    eg.rebuild();
    assert_ne!(
        eg.child_at(ga, 0),
        before,
        "the child's class must lose the merge, or the node is never recanonicalized \
         and the test proves nothing"
    );
    assert_ne!(
        eg.node_flags(ga) & FLAG_SUBSUMED,
        0,
        "recanonicalization must not clear FLAG_SUBSUMED"
    );
}

#[test]
fn recanonized_congruent_copy_is_flagged_once_per_group() {
    // `g(a)` and `g(b)` are distinct nodes until `a` and `b` merge. The merge makes
    // their canonical forms equal, the hash-cons collision merges their classes, and the
    // loser stays a member because the store never removes a node. Exactly one of the two
    // carries `FLAG_CONGRUENT_DUP` afterwards.
    let mut eg = EG::from_model(&NiraModel);
    let e = eg.intern_sort("E");
    eg.register_op1("g", e, e);
    let a = eg.register_op0("a", e);
    let b = eg.register_op0("b", e);
    let g = eg.ops().id_by_name("g").unwrap();

    let ia = eg.add(a, &[]);
    let ib = eg.add(b, &[]);
    let ga = eg.add(g, &[ia]);
    let gb = eg.add(g, &[ib]);
    pad_class(&mut eg, e, ib, 8, "d");
    eg.rebuild();
    assert_ne!(
        eg.find_const(ga),
        eg.find_const(gb),
        "distinct before the merge"
    );
    assert_eq!(eg.node_flags(ga) & FLAG_CONGRUENT_DUP, 0);
    assert_eq!(eg.node_flags(gb) & FLAG_CONGRUENT_DUP, 0);

    eg.merge(ia, ib);
    eg.rebuild();

    assert_eq!(
        eg.find_const(ga),
        eg.find_const(gb),
        "congruence merged them"
    );
    let fa = eg.node_flags(ga) & FLAG_CONGRUENT_DUP != 0;
    let fb = eg.node_flags(gb) & FLAG_CONGRUENT_DUP != 0;
    assert!(
        fa != fb,
        "exactly one of the two copies is flagged (ga {fa}, gb {fb}); flagging neither \
         leaves the duplicate visible, flagging both leaves the class with no member"
    );
    eg.debug_check_congruent_dup_invariant();
}
