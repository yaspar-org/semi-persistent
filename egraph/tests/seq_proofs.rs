// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Step 5 of `doc/goal-sequence-patterns.md`: in proof mode, the unions a sequence
//! rule makes carry `Justification::Rewrite` with the rule's id, so `explain` of an
//! equality the rule made cites it.

use semi_persistent_egraph::interpret::Interpreter;
use semi_persistent_egraph::model::{MachineLit, MachineModel};
use semi_persistent_egraph::union_find::{Justification, ProofBuf};

type Cfg = semi_persistent_egraph::nodes::DefaultConfig;

fn cites_the_rule(program: &str, root_op: &str, marker_op: &str) {
    let cmds = semi_persistent_egraph::parser::parse_program_v2(program).expect("parse");
    let mut it: Interpreter<Cfg, MachineLit, MachineModel, false, true> =
        Interpreter::new(MachineModel);
    let mut sg = semi_persistent_egraph::resolve::GlobalCtx::new();
    let checked =
        semi_persistent_egraph::sortcheck::sortcheck_program(cmds, &mut it.eg, &it.model, &mut sg)
            .expect("sortcheck");
    it.run_checked(&checked).expect("run");
    let (_, _, e) = it.globals().get("e").expect("e");
    let eg = &it.eg;
    // The input's node, and the rewritten node (the one with the marker child).
    let has_marker = |n| {
        let mut m = false;
        eg.for_each_child(n, |k, _| {
            m |= eg
                .node_ids()
                .any(|x| eg.class_repr(x) == eg.class_repr(k) && eg.node_op_name(x) == marker_op);
        });
        m
    };
    let rewritten = eg
        .node_ids()
        .find(|&n| {
            eg.node_op_name(n) == root_op && eg.class_repr(n) == eg.class_repr(e) && has_marker(n)
        })
        .expect("the rule fired");
    let mut buf = ProofBuf::new();
    assert!(eg.explain(e, rewritten, &mut buf), "no explanation");
    let names: Vec<&str> = buf
        .steps
        .iter()
        .filter_map(|(_, _, j)| {
            if let Justification::Rewrite { rule_id } = j {
                Some(eg.rules().name(*rule_id))
            } else {
                None
            }
        })
        .collect();
    assert!(
        names.iter().any(|n| n.starts_with("collection_rule_")),
        "the explanation cites no sequence rule: {:?}",
        buf.steps
    );
}

/// Under an associative operator.
#[test]
fn a_sequence_rule_under_a_is_cited() {
    cites_the_rule(
        "(sort E)
(function a () E)
(function b () E)
(function F (E) E)
(function H (E) E)
(function Cat (E) E :assoc)
(let e (Cat a (F a) (F b) b))
(rewrite (Cat ..pre (..fs (F x)) ..suf) (Cat ..pre (H (Cat ..fs)) ..suf) :when ((>= (count fs) 2)))
(run 1)",
        "Cat",
        "H",
    );
}

/// Under an ACI operator.
#[test]
fn a_sequence_rule_under_aci_is_cited() {
    cites_the_rule(
        "(sort E)
(function a () E)
(function b () E)
(function F (E) E)
(function H (E) E)
(function And (E) E :assoc-comm-idem)
(let e (And a (F a) (F b)))
(rewrite (And (..fs (F x)) ..rest) (And (H (And ..fs)) ..rest) :when ((>= (count fs) 2)))
(run 1)",
        "And",
        "H",
    );
}
