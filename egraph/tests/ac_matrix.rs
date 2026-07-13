// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! The AC-extension × harness-feature matrix: every semantic-property mechanism this
//! branch added (Kapur §4 axiom critical pairs, recanonize unit-drop, cancelative
//! closure, inverse-pair cancellation) exercised under all four `(TRACK, PROOFS)`
//! const-generic combinations, plus proof RECONSTRUCTION under `PROOFS = true` and
//! mark/restore round-trips under `TRACK = true`.
//!
//! The egg fixture harness runs `(TRACK = true, PROOFS = false)` and the proof suite
//! `(false, true)`, so without this file the new mechanisms were never compiled — let
//! alone asserted — under `(false, false)` and `(true, true)`, and no proof was ever
//! reconstructed across the new merge kinds (review-debt §2.1).

use semi_persistent_egraph::EGraph31;
use semi_persistent_egraph::containers::ShrinkPolicy;
use semi_persistent_egraph::id::AxiomId;
use semi_persistent_egraph::literal::NiraLitVal;
use semi_persistent_egraph::registry::{Clamp, OpKind};
use semi_persistent_egraph::union_find::{Justification, ProofBuf};

type Eg<const TRACK: bool, const PROOFS: bool> = EGraph31<NiraLitVal, TRACK, PROOFS>;

fn axiom(i: u16) -> Justification<semi_persistent_egraph::ENodeId> {
    Justification::Axiom {
        axiom_id: AxiomId::new(i),
    }
}

/// Assert a ≡ b, and under PROOFS also reconstruct the class-level proof chain.
fn assert_eq_class<const TRACK: bool, const PROOFS: bool>(
    eg: &mut Eg<TRACK, PROOFS>,
    a: semi_persistent_egraph::ENodeId,
    b: semi_persistent_egraph::ENodeId,
    what: &str,
) {
    assert_eq!(eg.find(a), eg.find(b), "{what}: classes differ");
    if PROOFS {
        let mut buf = ProofBuf::new();
        assert!(
            eg.explain(a, b, &mut buf),
            "{what}: explain found no proof path"
        );
        // Build-time canonization can make the two terms the SAME node (e.g.
        // `add(a, neg(a))` returns the unit node directly, like `xor(a,a) → e`): that is
        // definitional equality at the hash-cons level — no merge happened, and the empty
        // chain is correct reflexivity. A proof chain is required only across distinct nodes.
        assert!(
            a == b || !buf.steps.is_empty(),
            "{what}: distinct nodes in one class but proof reconstruction returned an \
             empty chain"
        );
    }
}

/// Under PROOFS, assert the class-level proof chain for `a ≡ b` contains at least one
/// step matching `pred` — the exact-label check that pins each completion inference to
/// its faithful justification variant (not a catch-all congruence/superposition label).
fn assert_proof_label<const TRACK: bool, const PROOFS: bool>(
    eg: &mut Eg<TRACK, PROOFS>,
    a: semi_persistent_egraph::ENodeId,
    b: semi_persistent_egraph::ENodeId,
    pred: impl Fn(&Justification<semi_persistent_egraph::ENodeId>) -> bool,
    what: &str,
) {
    if !PROOFS {
        return;
    }
    let mut buf = ProofBuf::new();
    assert!(eg.explain(a, b, &mut buf), "{what}: explain found no proof");
    assert!(
        buf.steps.iter().any(|(_, _, j)| pred(j)),
        "{what}: expected proof label missing; chain labels: {:?}",
        buf.steps.iter().map(|(_, _, j)| j).collect::<Vec<_>>()
    );
}

/// Kapur §4.2 nilpotent axiom critical pair: xor(a,b)=c ⟹ xor(a,c)=b.
fn nilpotent_axiom_cp<const TRACK: bool, const PROOFS: bool>() {
    let mut eg = Eg::<TRACK, PROOFS>::new();
    eg.set_cc(true);
    let s = eg.intern_sort("E");
    let e_op = eg.register_op0("e", s);
    let a_op = eg.register_op0("a", s);
    let b_op = eg.register_op0("b", s);
    let c_op = eg.register_op0("c", s);
    let xor = eg.register_kind(
        "xor",
        s,
        OpKind::MSet {
            arg_sort: s,
            clamp: Clamp::Nilpotent { order: 2 },
            identity: None,
            cancellative: false,
        },
    );
    let e = eg.add(e_op, &[]);
    eg.set_unit_node(xor, e);
    let a = eg.add(a_op, &[]);
    let b = eg.add(b_op, &[]);
    let c = eg.add(c_op, &[]);
    let x_ab = eg.add(xor, &[a, b]);
    eg.merge_justified(x_ab, c, axiom(0));
    eg.rebuild();
    let x_ac = eg.add(xor, &[a, c]);
    eg.rebuild();
    assert_eq_class(&mut eg, x_ac, b, "nilpotent axiom CP xor(a,c)=b");
    // The derived equality must be justified by the semantic-axiom CP label, not a
    // catch-all superposition/congruence.
    assert_proof_label(
        &mut eg,
        x_ac,
        b,
        |j| matches!(j, Justification::ACAxiomCP { .. }),
        "nilpotent axiom CP proof label",
    );
}

/// Recanonize unit-drop (late merge into the unit's class): add(a,b), b=0 ⟹ add(a,b)=a.
fn late_unit_merge<const TRACK: bool, const PROOFS: bool>() {
    let mut eg = Eg::<TRACK, PROOFS>::new();
    eg.set_cc(true);
    let s = eg.intern_sort("E");
    let zero_op = eg.register_op0("zero", s);
    let a_op = eg.register_op0("a", s);
    let b_op = eg.register_op0("b", s);
    let add = eg.register_kind(
        "add",
        s,
        OpKind::MSet {
            arg_sort: s,
            clamp: Clamp::None,
            identity: None,
            cancellative: false,
        },
    );
    let zero = eg.add(zero_op, &[]);
    eg.set_unit_node(add, zero);
    let a = eg.add(a_op, &[]);
    let b = eg.add(b_op, &[]);
    let s_ab = eg.add(add, &[a, b]);
    eg.merge_justified(b, zero, axiom(0));
    eg.rebuild();
    assert_eq_class(&mut eg, s_ab, a, "late unit merge add(a,b)=a");
}

/// Inverse-pair cancellation, build-time and via a late merge (completion round).
fn inverse_cancellation<const TRACK: bool, const PROOFS: bool>() {
    let mut eg = Eg::<TRACK, PROOFS>::new();
    eg.set_cc(true);
    let s = eg.intern_sort("E");
    let zero_op = eg.register_op0("zero", s);
    let a_op = eg.register_op0("a", s);
    let x_op = eg.register_op0("x", s);
    let neg = eg.register_op1("neg", s, s);
    let add = eg.register_kind(
        "add",
        s,
        OpKind::MSet {
            arg_sort: s,
            clamp: Clamp::None,
            identity: None,
            cancellative: true, // implied by :inverse at the surface; set explicitly here
        },
    );
    let zero = eg.add(zero_op, &[]);
    eg.set_unit_node(add, zero);
    eg.set_inverse_op(add, neg);
    let a = eg.add(a_op, &[]);
    let neg_a = eg.add(neg, &[a]);

    // Build-time: add(a, neg(a)) cancels to the unit as it is built.
    let t = eg.add(add, &[a, neg_a]);
    assert_eq_class(&mut eg, t, zero, "build-time inverse pair add(a,neg a)=0");

    // Late pair: add(a, x) with x merged into neg(a)'s class afterwards; the completion
    // round's (A′) pass cancels the now-formed pair.
    let x = eg.add(x_op, &[]);
    let t2 = eg.add(add, &[a, x]);
    eg.merge_justified(x, neg_a, axiom(1));
    eg.rebuild();
    assert_eq_class(
        &mut eg,
        t2,
        zero,
        "late inverse pair add(a,x)=0 after x=neg(a)",
    );
    // The completion-derived step must carry the group-law label.
    assert_proof_label(
        &mut eg,
        t2,
        zero,
        |j| matches!(j, Justification::InverseCancel { .. }),
        "late inverse pair proof label",
    );
}

/// Cancelative closure (Kapur §5.2 C1): add(a,c)=add(b,c) ⟹ a=b.
fn cancelative_close<const TRACK: bool, const PROOFS: bool>() {
    let mut eg = Eg::<TRACK, PROOFS>::new();
    eg.set_cc(true);
    let s = eg.intern_sort("E");
    let a_op = eg.register_op0("a", s);
    let b_op = eg.register_op0("b", s);
    let c_op = eg.register_op0("c", s);
    let mul = eg.register_kind(
        "mul",
        s,
        OpKind::MSet {
            arg_sort: s,
            clamp: Clamp::None,
            identity: None,
            cancellative: true,
        },
    );
    let a = eg.add(a_op, &[]);
    let b = eg.add(b_op, &[]);
    let c = eg.add(c_op, &[]);
    let ac = eg.add(mul, &[a, c]);
    let bc = eg.add(mul, &[b, c]);
    eg.merge_justified(ac, bc, axiom(0));
    eg.rebuild();
    assert_eq_class(&mut eg, a, b, "cancelative close a=b");
    // a=b is a §5.2 cancel-closure consequence; its proof step must say so.
    assert_proof_label(
        &mut eg,
        a,
        b,
        |j| matches!(j, Justification::Cancellative { .. }),
        "cancelative close proof label",
    );
}

/// TRACK-only: the new AC state (derived merges, unit map, inverse map) round-trips
/// through mark/restore — equalities hold inside the mark, are gone after restore, and
/// are re-derivable afterwards.
fn semi_persistence_round_trip<const PROOFS: bool>() {
    let mut eg = Eg::<true, PROOFS>::new();
    eg.set_cc(true);
    let s = eg.intern_sort("E");
    let zero_op = eg.register_op0("zero", s);
    let a_op = eg.register_op0("a", s);
    let b_op = eg.register_op0("b", s);
    let neg = eg.register_op1("neg", s, s);
    let add = eg.register_kind(
        "add",
        s,
        OpKind::MSet {
            arg_sort: s,
            clamp: Clamp::None,
            identity: None,
            cancellative: true,
        },
    );
    let zero = eg.add(zero_op, &[]);
    eg.set_unit_node(add, zero);
    eg.set_inverse_op(add, neg);
    let a = eg.add(a_op, &[]);
    let b = eg.add(b_op, &[]);
    let s_ab = eg.add(add, &[a, b]);

    let tok = eg.mark(ShrinkPolicy::Never);

    // Inside the mark: late unit merge + late inverse pair, both derived.
    eg.merge_justified(b, zero, axiom(0));
    eg.rebuild();
    assert_eq!(eg.find(s_ab), eg.find(a), "inside mark: add(a,b)=a");
    if PROOFS {
        // Proof reconstruction INSIDE the mark: tracking must not disturb the proof
        // forest for equalities derived under it.
        let mut buf = ProofBuf::new();
        assert!(
            eg.explain(s_ab, a, &mut buf) && !buf.steps.is_empty(),
            "inside mark: no proof chain for add(a,b)=a"
        );
    }

    eg.restore(tok);
    assert_ne!(
        eg.find(s_ab),
        eg.find(a),
        "after restore: the unit merge must be rolled back"
    );
    assert_ne!(
        eg.find(b),
        eg.find(zero),
        "after restore: b=0 must be rolled back"
    );
    if PROOFS {
        // The proof forest must roll back WITH the union-find: a stale justification
        // edge surviving the restore would let explain "prove" a retracted equality —
        // that would be a proof-logging soundness bug, not a completeness gap.
        let mut buf = ProofBuf::new();
        assert!(
            !eg.explain(s_ab, a, &mut buf),
            "after restore: explain still finds a path for the ROLLED-BACK add(a,b)=a"
        );
        let mut buf2 = ProofBuf::new();
        assert!(
            !eg.explain(b, zero, &mut buf2),
            "after restore: explain still finds a path for the ROLLED-BACK b=0"
        );
    }

    // Re-derivable after restore (the maps and node stores are intact).
    eg.merge_justified(b, zero, axiom(1));
    eg.rebuild();
    assert_eq!(eg.find(s_ab), eg.find(a), "re-derived after restore");
    if PROOFS {
        // And the re-derived equality gets a FRESH valid chain (not stale pre-restore
        // steps): reconstruction succeeds again after the roll-back + re-derivation.
        let mut buf = ProofBuf::new();
        assert!(
            eg.explain(s_ab, a, &mut buf) && !buf.steps.is_empty(),
            "re-derived after restore: no proof chain for add(a,b)=a"
        );
    }
}

/// Pairwise rule superposition (§4b): add(a,b)=c ∧ add(b,d)=e ⟹ add(c,d) = add(a,e).
fn superposition_label<const TRACK: bool, const PROOFS: bool>() {
    let mut eg = Eg::<TRACK, PROOFS>::new();
    eg.set_cc(true);
    let s = eg.intern_sort("E");
    let a_op = eg.register_op0("a", s);
    let b_op = eg.register_op0("b", s);
    let c_op = eg.register_op0("c", s);
    let d_op = eg.register_op0("d", s);
    let e_op = eg.register_op0("e", s);
    let add = eg.register_mset("add", s, s);
    let a = eg.add(a_op, &[]);
    let b = eg.add(b_op, &[]);
    let c = eg.add(c_op, &[]);
    let d = eg.add(d_op, &[]);
    let e = eg.add(e_op, &[]);
    let s_ab = eg.add(add, &[a, b]);
    let s_bd = eg.add(add, &[b, d]);
    eg.merge_justified(s_ab, c, axiom(0));
    eg.merge_justified(s_bd, e, axiom(1));
    eg.rebuild();
    let s_cd = eg.add(add, &[c, d]);
    let s_ae = eg.add(add, &[a, e]);
    eg.rebuild();
    assert_eq_class(&mut eg, s_cd, s_ae, "superposition add(c,d)=add(a,e)");
    assert_proof_label(
        &mut eg,
        s_cd,
        s_ae,
        |j| matches!(j, Justification::ACSuperposition { .. }),
        "superposition proof label",
    );
}

/// TRACK-only: `completion_outcome` reflects the current graph state and rolls back with
/// it. `Disabled` before opting in, `Converged` after a completed rebuild, and after a
/// `restore` the mark-time outcome is back (never a value from the discarded scope).
fn completion_outcome_semantics<const PROOFS: bool>() {
    use semi_persistent_egraph::CompletionOutcome;
    let mut eg = Eg::<true, PROOFS>::new();
    assert_eq!(eg.completion_outcome(), None, "no rebuild yet");

    let s = eg.intern_sort("E");
    let a_op = eg.register_op0("a", s);
    let b_op = eg.register_op0("b", s);
    let add = eg.register_mset("add", s, s);
    let a = eg.add(a_op, &[]);
    let b = eg.add(b_op, &[]);
    let s_ab = eg.add(add, &[a, b]);

    // cc off: rebuild records Disabled.
    eg.rebuild();
    assert_eq!(eg.completion_outcome(), Some(CompletionOutcome::Disabled));

    // mark() rebuilds first, so the token snapshots a Disabled-state graph.
    let tok = eg.mark(ShrinkPolicy::Never);

    // Inside the scope: enable completion and derive; outcome becomes Converged.
    eg.set_cc(true);
    eg.merge_justified(s_ab, a, axiom(0));
    eg.rebuild();
    assert!(
        matches!(
            eg.completion_outcome(),
            Some(CompletionOutcome::Converged { .. })
        ),
        "expected Converged inside the scope, got {:?}",
        eg.completion_outcome()
    );

    // Restore: the outcome must roll back to the mark-time value, not report the
    // discarded scope's Converged run.
    eg.restore(tok);
    assert_eq!(
        eg.completion_outcome(),
        Some(CompletionOutcome::Disabled),
        "restore must roll the outcome back with the graph"
    );
}

fn run_all<const TRACK: bool, const PROOFS: bool>() {
    nilpotent_axiom_cp::<TRACK, PROOFS>();
    late_unit_merge::<TRACK, PROOFS>();
    inverse_cancellation::<TRACK, PROOFS>();
    cancelative_close::<TRACK, PROOFS>();
    superposition_label::<TRACK, PROOFS>();
}

#[test]
fn matrix_track_off_proofs_off() {
    run_all::<false, false>();
}

#[test]
fn matrix_track_on_proofs_off() {
    run_all::<true, false>();
    semi_persistence_round_trip::<false>();
    completion_outcome_semantics::<false>();
}

#[test]
fn matrix_track_off_proofs_on() {
    run_all::<false, true>();
}

#[test]
fn matrix_track_on_proofs_on() {
    run_all::<true, true>();
    semi_persistence_round_trip::<true>();
    completion_outcome_semantics::<true>();
}
