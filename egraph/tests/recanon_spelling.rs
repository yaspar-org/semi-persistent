// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! A rebuild that applies a law to a stored n-ary node (a unit drop, a count clamp, a
//! degenerate arity) counts as a spelling change (`spelling_epoch`), so the next semi-naive
//! round matches the rules that build an AC term in full. A rebuild that only maps children
//! through `find` does not count. The Lean model asks exactly this of the engine: a round
//! whose rebuild is not literal routes those rules naive (`proofs/lean/SemperProofs/
//! Fidelity/NormalizeSat.lean`, `SChainN`), because a fired instance need not survive such
//! a rebuild (`Fidelity/Recanon.lean`, `denN_persist_fails`).

use semi_persistent_egraph::EGraph31;
use semi_persistent_egraph::literal::NiraLitVal;

type Eg = EGraph31<NiraLitVal, false, false>;

#[test]
fn unit_drop_bumps_spelling_epoch() {
    let mut eg = Eg::new();
    let sort = eg.intern_sort("E");
    let add = eg.register_mset("Add", sort, sort);
    let zero_op = eg.register_op0("Zero", sort);
    let a_op = eg.register_op0("A", sort);
    let b_op = eg.register_op0("B", sort);
    let e_op = eg.register_op0("E", sort);
    let zero = eg.add(zero_op, &[]);
    eg.set_unit_node(add, zero);
    let a = eg.add(a_op, &[]);
    let b = eg.add(b_op, &[]);
    let e = eg.add(e_op, &[]);
    let s = eg.add(add, &[a, b, e]);
    eg.rebuild();
    let before = eg.spelling_epoch();
    // `E` joins the unit's class: `Add{A,B,E}` recanonicalizes to `Add{A,B}`.
    eg.merge(e, zero);
    eg.rebuild();
    assert!(
        eg.spelling_epoch() > before,
        "a unit drop at recanonicalization must count as a spelling change"
    );
    let ab = eg.add(add, &[a, b]);
    assert_eq!(eg.find(ab), eg.find(s));
}

#[test]
fn literal_recanonicalization_keeps_spelling_epoch() {
    let mut eg = Eg::new();
    let sort = eg.intern_sort("E");
    let add = eg.register_mset("Add", sort, sort);
    let a_op = eg.register_op0("A", sort);
    let b_op = eg.register_op0("B", sort);
    let c_op = eg.register_op0("C", sort);
    let a = eg.add(a_op, &[]);
    let b = eg.add(b_op, &[]);
    let c = eg.add(c_op, &[]);
    let _s = eg.add(add, &[a, c]);
    eg.rebuild();
    let before = eg.spelling_epoch();
    // `C` joins `B`'s class: `Add{A,C}` becomes `Add{A,B}`, the image under `find`.
    eg.merge(c, b);
    eg.rebuild();
    assert_eq!(
        eg.spelling_epoch(),
        before,
        "a recanonicalization that only maps children through find is not a spelling change"
    );
}
