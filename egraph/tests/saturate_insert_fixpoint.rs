// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! An insert action whose node already exists is not a change: the loop must
//! report a fixpoint once a naive-routed insert rule only re-fires old matches.
use semi_persistent_egraph::interpret::Interpreter;
use semi_persistent_egraph::literal::{NiraLitVal, NiraModel};
use semi_persistent_egraph::nodes::Config64;

/// `((h x) (= x g))` is routed to naive matching (a global equality), so its
/// one match is re-emitted every round; its insert `(k x)` creates a node in
/// round 1 and hits the hash-cons afterwards. Before the fix every round
/// counted the hit as a change and `(run 10)` ran ten rounds without
/// saturating.
#[test]
fn insert_hit_is_not_a_change() {
    let program = "\
(datatype E (h E) (k E) (a))
(let g (a))
(let t (h (a)))
(rule ((h x) (= x g)) ((k x)))
(run 10)
";
    let cmds = semi_persistent_egraph::parser::parse_program_v2(program).expect("parses");
    let mut interp = Interpreter::<Config64, NiraLitVal, NiraModel, false, false>::new(NiraModel);
    let mut globals = semi_persistent_egraph::resolve::GlobalCtx::new();
    let checked = semi_persistent_egraph::sortcheck::sortcheck_program(
        cmds,
        &mut interp.eg,
        &interp.model,
        &mut globals,
    )
    .expect("sortchecks");
    interp.run_checked(&checked).expect("runs");
    let sat = interp.last_sat().expect("a run happened");
    assert!(sat.saturated, "the loop must report a fixpoint, ran {} rounds", sat.iterations);
    assert_eq!(sat.iterations, 2, "one round of changes, one unchanged round");
}
