// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Step 1 of `doc/goal-stable-extraction.md`: the content colouring
//! (`EGraph::canon_colours`) depends on the e-graph's content only.

use semi_persistent_egraph::canon_colour::{Colour, hash_bytes};
use semi_persistent_egraph::interpret::Interpreter;
use semi_persistent_egraph::model::{MachineLit, MachineModel};

type Cfg = semi_persistent_egraph::nodes::DefaultConfig;
type Interp = Interpreter<Cfg, MachineLit, MachineModel, true, false>;

const DECLS: &str = "(sort E)
(function a () E)
(function b () E)
(function c () E)
(function F (E) E)
(function K (E E) E)
(function Plus (E) E :assoc-comm)
(function And (E) E :assoc-comm-idem)
(function Cat (E) E :assoc)
";

fn build(body: &str) -> Interp {
    let src = format!("{DECLS}{body}");
    let cmds = semi_persistent_egraph::parser::parse_program_v2(&src).expect("parse");
    let mut it: Interp = Interpreter::new(MachineModel);
    let mut sg = semi_persistent_egraph::resolve::GlobalCtx::new();
    let checked =
        semi_persistent_egraph::sortcheck::sortcheck_program(cmds, &mut it.eg, &it.model, &mut sg)
            .expect("sortcheck");
    it.run_checked(&checked).expect("run");
    it.eg.rebuild();
    it
}

/// The multiset of class colours, sorted.
fn colours(it: &Interp) -> Vec<Colour> {
    let c = it.eg.canon_colours();
    assert!(
        c.converged,
        "the refinement did not converge within its bound"
    );
    let mut v = c.class_colour.clone();
    v.sort_unstable();
    v
}

/// The hash is `rapidhash_v3` with fixed seeds, which the crate keeps stable across
/// versions. A change here changes every exported name. The values were recorded from
/// rapidhash 4.5.1 on 2026-10-02.
#[test]
fn the_hash_is_pinned() {
    assert_eq!(hash_bytes(b"semper").hex(), GOLDEN_SEMPER);
    assert_eq!(hash_bytes(b"").hex(), GOLDEN_EMPTY);
}

const GOLDEN_SEMPER: &str = "7ff129168c0baca818b8034788847939";
const GOLDEN_EMPTY: &str = "c8e8d13696dc3b39befb03c3cc4c458d";

/// The same e-graph built in two node orders, so every id differs, colours the same.
#[test]
fn colours_do_not_depend_on_ids() {
    let terms = [
        "(F (a))",
        "(K (a) (b))",
        "(K (b) (a))",
        "(Plus (a) (b) (b))",
        "(And (a) (F (b)))",
        "(Cat (a) (b) (c))",
        "(F (F (c)))",
    ];
    let forward: String = terms
        .iter()
        .enumerate()
        .map(|(i, t)| format!("(let t{i} {t})\n"))
        .collect();
    let backward: String = terms
        .iter()
        .enumerate()
        .rev()
        .map(|(i, t)| format!("(let t{i} {t})\n"))
        .collect();
    let union = "(union t0 t6)\n";
    let (x, y) = (build(&(forward + union)), build(&(backward + union)));
    // The two builds allocate in opposite orders, so the test compares across ids.
    let first: Vec<String> =
        x.eg.node_ids()
            .map(|n| x.eg.node_op_name(n).to_string())
            .collect();
    let second: Vec<String> =
        y.eg.node_ids()
            .map(|n| y.eg.node_op_name(n).to_string())
            .collect();
    assert_ne!(first, second, "the two builds allocated in the same order");
    assert_eq!(colours(&x), colours(&y));
}

/// Child order counts for a plain operator, and not for an AC one.
#[test]
fn ac_order_is_ignored_and_plain_order_kept() {
    let plain = build("(let x (K (a) (b)))\n");
    let swapped = build("(let x (K (b) (a)))\n");
    assert_ne!(colours(&plain), colours(&swapped));
    let ac = build("(let x (Plus (a) (b)))\n");
    let ac_swapped = build("(let x (Plus (b) (a)))\n");
    assert_eq!(colours(&ac), colours(&ac_swapped));
    // `a` (assoc) keeps its order.
    let cat = build("(let x (Cat (a) (b)))\n");
    let cat_swapped = build("(let x (Cat (b) (a)))\n");
    assert_ne!(colours(&cat), colours(&cat_swapped));
}

/// A multiset child's multiplicity is content: `Plus(a, a)` is not `Plus(a)`.
#[test]
fn multiplicity_is_content() {
    let two = build("(let x (Plus (a) (a) (b)))\n");
    let one = build("(let x (Plus (a) (b)))\n");
    assert_ne!(colours(&two), colours(&one));
}

/// A cyclic class (`x = F(x)`) terminates within the bound, and distinct content gets
/// distinct colours.
#[test]
fn a_cycle_terminates() {
    let it = build("(let x (a))\n(union x (F x))\n(let y (b))\n");
    let c = it.eg.canon_colours();
    assert!(c.converged);
    assert!(c.rounds <= c.classes.len() + 1);
    assert_eq!(c.symmetric_groups(), 0);
}

/// Every node of one class has its own colour.
#[test]
fn members_of_a_class_are_told_apart() {
    let it = build("(let x (a))\n(union x (F (b)))\n(union x (K (b) (c)))\n");
    let c = it.eg.canon_colours();
    for cols in &c.node_colour {
        let mut v = cols.clone();
        v.sort_unstable();
        v.dedup();
        assert_eq!(
            v.len(),
            cols.len(),
            "two members of one class share a colour"
        );
    }
}
