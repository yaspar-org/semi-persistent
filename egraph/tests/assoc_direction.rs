// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Directional associative flattening through the two surface construction paths.

use semi_persistent_egraph::interpret::Interpreter;
use semi_persistent_egraph::model::{BignumLit, BignumModel};
use semi_persistent_egraph::nodes::DefaultConfig;
use semi_persistent_egraph::parser::parse_program_v2;
use semi_persistent_egraph::registry::AssocDir;
use semi_persistent_egraph::resolve::GlobalCtx;
use semi_persistent_egraph::sortcheck::sortcheck_program;

fn run(src: &str) {
    let surface = parse_program_v2(src).expect("program parses");
    let mut interp =
        Interpreter::<DefaultConfig, BignumLit, BignumModel, true, false>::new(BignumModel);
    let mut globals = GlobalCtx::new();
    let checked = sortcheck_program(surface, &mut interp.eg, &interp.model, &mut globals)
        .expect("program sort-checks");
    interp.run_checked(&checked).expect("program runs");
}

fn sortcheck_error(src: &str) -> String {
    let surface = parse_program_v2(src).expect("program parses");
    let mut interp =
        Interpreter::<DefaultConfig, BignumLit, BignumModel, true, false>::new(BignumModel);
    let mut globals = GlobalCtx::new();
    match sortcheck_program(surface, &mut interp.eg, &interp.model, &mut globals) {
        Ok(_) => panic!("program unexpectedly sort-checks"),
        Err(error) => error.to_string(),
    }
}

#[test]
fn conflicting_assoc_directions_are_rejected_independently_of_tag_order() {
    for tags in [
        ":assoc-left :assoc-right",
        ":assoc-right :assoc-left",
        ":assoc :assoc-left",
        ":assoc-left :assoc",
        ":assoc :assoc-right",
        ":assoc-right :assoc",
    ] {
        let error = sortcheck_error(&format!("(sort E)\n(function f (E) E {tags})"));
        assert!(
            error.contains(":assoc, :assoc-left, and :assoc-right are mutually exclusive"),
            "{tags}: {error}"
        );
    }
}

#[test]
fn directional_assoc_does_not_silently_become_ac() {
    for tags in [
        ":assoc-left :comm",
        ":comm :assoc-left",
        ":assoc-right :comm",
        ":comm :assoc-right",
    ] {
        let error = sortcheck_error(&format!("(sort E)\n(function f (E) E {tags})"));
        assert!(
            error.contains(":assoc-left/:assoc-right cannot be combined with :comm"),
            "{tags}: {error}"
        );
    }
}

#[test]
fn initial_term_construction_respects_assoc_direction() {
    run(r#"
(sort E)
(function L (E) E :assoc-left)
(function R (E) E :assoc-right)
(function A (E) E :assoc)
(function a () E)
(function b () E)
(function c () E)
(function d () E)

(let lflat (L (a) (b) (c) (d)))
(check (= lflat (L (L (L (a) (b)) (c)) (d))))
(check (!= lflat (L (a) (L (b) (c)) (d))))

(let rflat (R (a) (b) (c) (d)))
(check (= rflat (R (a) (R (b) (R (c) (d))))))
(check (!= rflat (R (R (a) (b)) (c) (d))))

(let aflat (A (a) (b) (c) (d)))
(check (= aflat (A (A (a) (b)) (c) (d))))
(check (= aflat (A (a) (A (b) (c)) (d))))
(check (= aflat (A (a) (b) (A (c) (d)))))
"#);
}

#[test]
fn rewrite_rhs_construction_respects_assoc_direction() {
    run(r#"
(sort E)
(function L (E) E :assoc-left)
(function R (E) E :assoc-right)
(function A (E) E :assoc)
(function a () E)
(function b () E)
(function c () E)

(function EmitLSpine () E)
(function EmitLGrouped () E)
(function EmitRSpine () E)
(function EmitRGrouped () E)
(function EmitAFromLeft () E)
(function EmitAFromRight () E)

(rewrite (EmitLSpine) (L (L (a) (b)) (c)))
(rewrite (EmitLGrouped) (L (a) (L (b) (c))))
(rewrite (EmitRSpine) (R (a) (R (b) (c))))
(rewrite (EmitRGrouped) (R (R (a) (b)) (c)))
(rewrite (EmitAFromLeft) (A (A (a) (b)) (c)))
(rewrite (EmitAFromRight) (A (a) (A (b) (c))))

(let ls (EmitLSpine))
(let lg (EmitLGrouped))
(let rs (EmitRSpine))
(let rg (EmitRGrouped))
(let al (EmitAFromLeft))
(let ar (EmitAFromRight))
(run 2)

(check (= ls (L (a) (b) (c))))
(check (!= lg (L (a) (b) (c))))
(check (= rs (R (a) (b) (c))))
(check (!= rg (R (a) (b) (c))))
(check (= al (A (a) (b) (c))))
(check (= ar (A (a) (b) (c))))
"#);
}

#[derive(Clone, Debug)]
enum Tree {
    Leaf(usize),
    App(Box<Tree>, Box<Tree>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum Normal {
    Leaf(usize),
    App(Vec<Normal>),
}

fn bracketings(leaves: &[usize]) -> Vec<Tree> {
    if let [leaf] = leaves {
        return vec![Tree::Leaf(*leaf)];
    }

    let mut out = Vec::new();
    for split in 1..leaves.len() {
        for left in bracketings(&leaves[..split]) {
            for right in bracketings(&leaves[split..]) {
                out.push(Tree::App(Box::new(left.clone()), Box::new(right)));
            }
        }
    }
    out
}

fn normalize(tree: &Tree, dir: AssocDir) -> Normal {
    match tree {
        Tree::Leaf(leaf) => Normal::Leaf(*leaf),
        Tree::App(left, right) => {
            let left = normalize(left, dir);
            let right = normalize(right, dir);
            let mut children = Vec::new();
            match dir {
                AssocDir::Left => {
                    if let Normal::App(nested) = left {
                        children.extend(nested);
                    } else {
                        children.push(left);
                    }
                    children.push(right);
                }
                AssocDir::Right => {
                    children.push(left);
                    if let Normal::App(nested) = right {
                        children.extend(nested);
                    } else {
                        children.push(right);
                    }
                }
                AssocDir::Both => {
                    for child in [left, right] {
                        if let Normal::App(nested) = child {
                            children.extend(nested);
                        } else {
                            children.push(child);
                        }
                    }
                }
            }
            Normal::App(children)
        }
    }
}

#[test]
fn construction_matches_the_directional_normal_form_oracle() {
    use semi_persistent_egraph::EGraph;
    use semi_persistent_egraph::id::{ENodeId, OpId};

    type EG = EGraph<DefaultConfig, BignumLit, false, false>;

    fn build(tree: &Tree, eg: &mut EG, op: OpId, leaves: &[ENodeId]) -> ENodeId {
        match tree {
            Tree::Leaf(leaf) => leaves[*leaf],
            Tree::App(left, right) => {
                let left = build(left, eg, op, leaves);
                let right = build(right, eg, op, leaves);
                eg.add(op, &[left, right])
            }
        }
    }

    let orders = [[0, 1, 2, 3, 4, 5], [1, 0, 2, 3, 4, 5], [5, 4, 3, 2, 1, 0]];

    for dir in [AssocDir::Left, AssocDir::Right, AssocDir::Both] {
        let mut eg = EG::from_model(&BignumModel);
        let sort = eg.intern_sort("E");
        let op = eg.register_a("f", sort, sort, dir);
        let leaves: Vec<_> = (0..6)
            .map(|i| {
                let leaf = eg.register_op0(&format!("x{i}"), sort);
                eg.add(leaf, &[])
            })
            .collect();

        let trees: Vec<_> = orders.iter().flat_map(|order| bracketings(order)).collect();
        let normals: Vec<_> = trees.iter().map(|tree| normalize(tree, dir)).collect();
        let built: Vec<_> = trees
            .iter()
            .map(|tree| build(tree, &mut eg, op, &leaves))
            .collect();

        for i in 0..trees.len() {
            for j in 0..trees.len() {
                assert_eq!(
                    built[i] == built[j],
                    normals[i] == normals[j],
                    "{dir:?} disagrees with the oracle:\nleft={:?}\nright={:?}\n\
                     left_nf={:?}\nright_nf={:?}",
                    trees[i],
                    trees[j],
                    normals[i],
                    normals[j],
                );
            }
        }
    }
}
