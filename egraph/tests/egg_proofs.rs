// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Fixtures whose completion inferences run under `PROOFS = true`.
//!
//! The egg harness (`egg_tests.rs`) runs every fixture with proofs off, so a completion
//! step's `PROOFS` arm, which records the step's justification, is reached only here.
//! Each fixture below is run through the interpreter with proofs on, must end as its
//! header says (`ok`), and the pair its header names must be explained by a chain that
//! carries the step's own label.

use semi_persistent_egraph::interpret::Interpreter;
use semi_persistent_egraph::model::{MachineLit, MachineModel};
use semi_persistent_egraph::nodes::DefaultConfig;
use semi_persistent_egraph::union_find::{Justification, ProofBuf};

type Interp = Interpreter<DefaultConfig, MachineLit, MachineModel, true, true>;

/// Run `tests/egg/<file>` with proofs on; the run must succeed.
fn run(file: &str) -> Interp {
    let path = format!("tests/egg/{file}");
    let src = std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("cannot read {path}: {e}"));
    let cmds = semi_persistent_egraph::parser::parse_program_v2(&src).expect("parse");
    let mut interp = Interp::new(MachineModel);
    let mut globals = semi_persistent_egraph::resolve::GlobalCtx::new();
    let checked = semi_persistent_egraph::sortcheck::sortcheck_program(
        cmds,
        &mut interp.eg,
        &interp.model,
        &mut globals,
    )
    .expect("sortcheck");
    interp
        .run_checked(&checked)
        .unwrap_or_else(|e| panic!("{file}: expected ok, got: {e}"));
    interp
}

/// The class of the nullary operator `name`.
fn constant(interp: &mut Interp, name: &str) -> semi_persistent_egraph::id::ENodeId {
    let op = interp.eg.ops().id_by_name(name).expect(name);
    interp.eg.add(op, &[])
}

/// `a` and `b` are one class, and some step of their proof chain carries `label`.
fn assert_explained(
    interp: &mut Interp,
    a: semi_persistent_egraph::id::ENodeId,
    b: semi_persistent_egraph::id::ENodeId,
    label: impl Fn(&Justification<semi_persistent_egraph::id::ENodeId>) -> bool,
    what: &str,
) {
    assert_eq!(
        interp.eg.find(a),
        interp.eg.find(b),
        "{what}: classes differ"
    );
    let mut buf = ProofBuf::new();
    assert!(interp.eg.explain(a, b, &mut buf), "{what}: no proof path");
    assert!(
        buf.steps.iter().any(|(_, _, j)| label(j)),
        "{what}: label missing; chain labels: {:?}",
        buf.steps.iter().map(|(_, _, j)| j).collect::<Vec<_>>()
    );
}

/// `cancel_lattice.egg`: `c5 = c1c3²` follows only from the exact cancelative closure at
/// the fixpoint (`lattice_round`), whose merges are justified as `Cancellative`.
#[test]
fn cancel_lattice_under_proofs() {
    let mut interp = run("cancel_lattice.egg");
    let c1 = constant(&mut interp, "C1");
    let c3 = constant(&mut interp, "C3");
    let c5 = constant(&mut interp, "C5");
    let add = interp.eg.ops().id_by_name("Add").expect("Add");
    let c1c3c3 = interp.eg.add(add, &[c1, c3, c3]);
    interp.eg.rebuild();
    assert_explained(
        &mut interp,
        c5,
        c1c3c3,
        |j| matches!(j, Justification::Cancellative { .. }),
        "c5 = c1c3²",
    );
    // Separated by the model Z2 with c3 = c4 = 1 (the fixture's certificate).
    let c0 = constant(&mut interp, "C0");
    let c2 = constant(&mut interp, "C2");
    let c2c3 = interp.eg.add(add, &[c2, c3]);
    assert_ne!(
        interp.eg.find(c2c3),
        interp.eg.find(c0),
        "c2c3 = c0 is not entailed"
    );
}
