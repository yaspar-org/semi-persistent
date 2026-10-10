// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Step 3 of `doc/goal-stable-extraction.md`: the greedy extractor breaks cost ties by
//! content, so one e-graph built in two node orders extracts one term.

use semi_persistent_egraph::EGraph;
use semi_persistent_egraph::extract::extract_best;
use semi_persistent_egraph::literal::{NiraLitVal, NiraModel};
use semi_persistent_egraph::nodes::DefaultConfig;
use semi_persistent_egraph::registry::{OpKind, OpMeta};

type EG = EGraph<DefaultConfig, NiraLitVal, false, false>;
type G = <DefaultConfig as semi_persistent_egraph::config::EGraphConfig>::G;
type O = <DefaultConfig as semi_persistent_egraph::config::EGraphConfig>::O;

/// The operators of the tests, registered in one fixed order.
struct Ops {
    a: O,
    b: O,
    c: O,
    f: O,
    g: O,
    k: O,
    plus: O,
}

fn graph(cost: u32) -> (EG, Ops) {
    let mut eg = EG::from_model(&NiraModel);
    let e = eg.intern_sort("E");
    let meta = OpMeta {
        cost,
        ..OpMeta::default()
    };
    let leaf = |eg: &mut EG, n: &str| {
        eg.register_kind_meta(n, e, OpKind::Normal { arg_sorts: vec![] }, meta)
    };
    let a = leaf(&mut eg, "a");
    let b = leaf(&mut eg, "b");
    let c = leaf(&mut eg, "c");
    let f = eg.register_kind_meta("f", e, OpKind::Normal { arg_sorts: vec![e] }, meta);
    let g = eg.register_kind_meta("g", e, OpKind::Normal { arg_sorts: vec![e] }, meta);
    let k = eg.register_kind_meta(
        "k",
        e,
        OpKind::Normal {
            arg_sorts: vec![e, e],
        },
        meta,
    );
    let plus = eg.register_kind_meta(
        "plus",
        e,
        OpKind::MSet {
            arg_sort: e,
            clamp: semi_persistent_egraph::registry::Clamp::None,
            identity: None,
            cancellative: false,
        },
        meta,
    );
    (
        eg,
        Ops {
            a,
            b,
            c,
            f,
            g,
            k,
            plus,
        },
    )
}

/// The tie at the root: `(f a)` and `(g b)` cost 2 each and are merged into one class
/// with `(k (a) (b))` (cost 3), so the root has two cheapest terms. Below it, the class
/// of `(plus b c)` is merged with `(f c)`: two terms of cost 3, a second tie. With `rev`
/// every group of nodes is added in the opposite order, so each tie's two nodes swap ids.
fn tied(rev: bool) -> (EG, G) {
    let (mut eg, o) = graph(1);
    let order = |n: usize| -> Vec<usize> {
        let v: Vec<usize> = (0..n).collect();
        if rev {
            v.into_iter().rev().collect()
        } else {
            v
        }
    };
    let mut leaf = [None; 3];
    for i in order(3) {
        leaf[i] = Some(eg.add([o.a, o.b, o.c][i], &[]));
    }
    let [Some(ia), Some(ib), Some(ic)] = leaf else {
        panic!("every leaf was built");
    };
    let mut root = Vec::new();
    for i in order(3) {
        root.push(match i {
            0 => eg.add(o.f, &[ia]),
            1 => eg.add(o.g, &[ib]),
            _ => eg.add(o.k, &[ia, ib]),
        });
    }
    for &n in &root[1..] {
        eg.merge(root[0], n);
    }
    let mut below = Vec::new();
    for i in order(2) {
        below.push(if i == 0 {
            eg.add(o.plus, &[ib, ic])
        } else {
            eg.add(o.f, &[ic])
        });
    }
    eg.merge(below[0], below[1]);
    eg.rebuild();
    let top = eg.add(o.k, &[root[0], below[0]]);
    eg.rebuild();
    (eg, top)
}

#[test]
fn one_egraph_in_two_node_orders_extracts_one_term() {
    let (x, rx) = tied(false);
    let (y, ry) = tied(true);
    let ids = |eg: &EG| -> Vec<String> {
        eg.node_ids()
            .map(|id| eg.node_op_name(id).to_string())
            .collect()
    };
    assert_ne!(
        ids(&x),
        ids(&y),
        "the two builds allocated in the same order"
    );
    let (tx, ty) = (
        extract_best(&x, rx).expect("extractable").to_string(),
        extract_best(&y, ry).expect("extractable").to_string(),
    );
    assert_eq!(tx, ty);
}

/// The tie-break is a function of content: among the two cheapest terms at the root,
/// the one with the smaller node colour wins, whichever was added first.
#[test]
fn the_tie_is_broken_by_colour_not_by_order() {
    for order in [[0usize, 1], [1, 0]] {
        let (mut eg, o) = graph(1);
        let (ia, ib) = (eg.add(o.a, &[]), eg.add(o.b, &[]));
        let mut root = None;
        for &i in &order {
            let n = if i == 0 {
                eg.add(o.f, &[ia])
            } else {
                eg.add(o.g, &[ib])
            };
            match root {
                None => root = Some(n),
                Some(r) => {
                    eg.merge(r, n);
                }
            }
        }
        eg.rebuild();
        let root = root.expect("a root");
        let t = extract_best(&eg, root).expect("extractable").to_string();
        let c = eg.canon_colours();
        let ci = c.class_of(eg.class_repr(root)).expect("the root's class");
        let (best, _) = c.members[ci]
            .iter()
            .zip(&c.node_colour[ci])
            .min_by_key(|(_, col)| **col)
            .expect("members");
        let want = if eg.node_op_name(*best) == "f" {
            "(f (a))"
        } else {
            "(g (b))"
        };
        assert_eq!(t, want, "order {order:?}");
    }
}

/// With every operator at cost 0, a class can reach itself at equal cost
/// (`x = {a, f(x)}`). The tie-break must not choose the cycle: height comes before
/// colour, so the leaf wins and extraction terminates.
#[test]
fn a_zero_cost_cycle_is_not_chosen() {
    let (mut eg, o) = graph(0);
    let ia = eg.add(o.a, &[]);
    let fa = eg.add(o.f, &[ia]);
    eg.merge(ia, fa);
    eg.rebuild();
    assert_eq!(
        extract_best(&eg, ia).expect("extractable").to_string(),
        "(a)"
    );
}

/// An AC node's children print in colour order, so `plus(b, c)` built either way prints
/// one text.
#[test]
fn ac_children_print_in_content_order() {
    let print = |first_c: bool| {
        let (mut eg, o) = graph(1);
        let (ib, ic) = if first_c {
            let ic = eg.add(o.c, &[]);
            (eg.add(o.b, &[]), ic)
        } else {
            let ib = eg.add(o.b, &[]);
            (ib, eg.add(o.c, &[]))
        };
        let p = eg.add(o.plus, &[ib, ic, ic]);
        eg.rebuild();
        extract_best(&eg, p).expect("extractable").to_string()
    };
    assert_eq!(print(true), print(false));
}
