// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! End-to-end acceptance tests: anti-unification on a Config64 e-graph.
//!
//! The AU subsystem instantiates its id family through `Cfg::Au`, so a
//! Config64 e-graph gets 63-bit AU arenas. These tests verify the production
//! path works at both widths and produces identical lexicographic results.

use semi_persistent_egraph::EGraph63;
use semi_persistent_egraph::au::egraph_api::AuSnapshot;
use semi_persistent_egraph::au::session::{AuAlgorithm, AuConfig, Completion, anti_unify};
use semi_persistent_egraph::literal::NiraLitVal;

type Eg64 = EGraph63<NiraLitVal, false, false>;
type Eg31 = semi_persistent_egraph::EGraph31<NiraLitVal, false, false>;

/// Exact and UCT on a Config64 e-graph with an AC operator and identity.
#[test]
fn config64_exact_and_uct_agree() {
    let mut eg = Eg64::new();
    let sort = eg.intern_sort("E");
    let a_op = eg.register_op0("a", sort);
    let b_op = eg.register_op0("b", sort);
    let c_op = eg.register_op0("c", sort);
    let d_op = eg.register_op0("d", sort);
    let and_op = eg.register_set("and", sort, sort);

    let a = eg.add(a_op, &[]);
    let b = eg.add(b_op, &[]);
    let c = eg.add(c_op, &[]);
    let d = eg.add(d_op, &[]);
    let and_abc = eg.add(and_op, &[a, b, c]);
    let and_bcd = eg.add(and_op, &[b, c, d]);
    eg.rebuild();

    let snap = AuSnapshot::new(&eg).unwrap();
    let exact = anti_unify(
        &snap,
        and_abc,
        and_bcd,
        &AuConfig {
            algorithm: AuAlgorithm::Exact,
            ..Default::default()
        },
    )
    .unwrap();
    let uct = anti_unify(
        &snap,
        and_abc,
        and_bcd,
        &AuConfig {
            algorithm: AuAlgorithm::Uct,
            playouts: 500,
            ..Default::default()
        },
    )
    .unwrap();

    assert_eq!(exact.completion, Completion::Exact);
    assert_eq!(
        uct.pool.quality(uct.term_id),
        exact.pool.quality(exact.term_id),
        "Config64 UCT must match the exact oracle"
    );
    // and(b, c, Variants(a,d)) = 5 nodes.
    assert_eq!(exact.size, 5);
}

/// Cycle filtering on Config64: X = f(X) merged; exact must terminate.
#[test]
fn config64_cycle_filtering_terminates() {
    let mut eg = Eg64::new();
    let sort = eg.intern_sort("E");
    let x_op = eg.register_op0("x", sort);
    let y_op = eg.register_op0("y", sort);
    let f_op = eg.register_op1("f", sort, sort);

    let x = eg.add(x_op, &[]);
    let fx = eg.add(f_op, &[x]);
    eg.merge(x, fx);
    let y = eg.add(y_op, &[]);
    let fy = eg.add(f_op, &[y]);
    eg.rebuild();

    let snap = AuSnapshot::new(&eg).unwrap();
    let result = anti_unify(
        &snap,
        x,
        fy,
        &AuConfig {
            algorithm: AuAlgorithm::Exact,
            ..Default::default()
        },
    )
    .unwrap();
    assert!(result.size > 0);
}

/// Identical lexicographic result at both widths on the same problem.
#[test]
fn widths_produce_identical_results() {
    fn quality_of_31() -> (u32, u32) {
        let mut eg = Eg31::new();
        let sort = eg.intern_sort("E");
        let a_op = eg.register_op0("a", sort);
        let b_op = eg.register_op0("b", sort);
        let c_op = eg.register_op0("c", sort);
        let f_op = eg.register_op2("f", sort, sort, sort);
        let plus = eg.register_mset("plus", sort, sort);

        let a = eg.add(a_op, &[]);
        let b = eg.add(b_op, &[]);
        let c = eg.add(c_op, &[]);
        let fab = eg.add(f_op, &[a, b]);
        let fcb = eg.add(f_op, &[c, b]);
        let l = eg.add(plus, &[fab, a, a]);
        let r = eg.add(plus, &[fcb, c, c]);
        eg.rebuild();

        let snap = AuSnapshot::new(&eg).unwrap();
        let result = anti_unify(
            &snap,
            l,
            r,
            &AuConfig {
                algorithm: AuAlgorithm::Exact,
                ..Default::default()
            },
        )
        .unwrap();
        result.pool.quality(result.term_id)
    }

    fn quality_of_64() -> (u32, u32) {
        let mut eg = Eg64::new();
        let sort = eg.intern_sort("E");
        let a_op = eg.register_op0("a", sort);
        let b_op = eg.register_op0("b", sort);
        let c_op = eg.register_op0("c", sort);
        let f_op = eg.register_op2("f", sort, sort, sort);
        let plus = eg.register_mset("plus", sort, sort);

        let a = eg.add(a_op, &[]);
        let b = eg.add(b_op, &[]);
        let c = eg.add(c_op, &[]);
        let fab = eg.add(f_op, &[a, b]);
        let fcb = eg.add(f_op, &[c, b]);
        let l = eg.add(plus, &[fab, a, a]);
        let r = eg.add(plus, &[fcb, c, c]);
        eg.rebuild();

        let snap = AuSnapshot::new(&eg).unwrap();
        let result = anti_unify(
            &snap,
            l,
            r,
            &AuConfig {
                algorithm: AuAlgorithm::Exact,
                ..Default::default()
            },
        )
        .unwrap();
        result.pool.quality(result.term_id)
    }

    assert_eq!(
        quality_of_31(),
        quality_of_64(),
        "Config31 and Config64 must produce identical lexicographic results"
    );
}

/// Session mark/restore on a Config64 e-graph: run UCT, mark, run more work,
/// restore, verify the pre-mark result is recovered and a re-run agrees.
#[test]
fn config64_session_mark_restore() {
    use semi_persistent_egraph::au::mcgs::McgsConfig;
    use semi_persistent_egraph::au::session::SearchSession;
    use semi_persistent_egraph::au::space::CycleMode;

    let mut eg = Eg64::new();
    let sort = eg.intern_sort("E");
    let a_op = eg.register_op0("a", sort);
    let b_op = eg.register_op0("b", sort);
    let c_op = eg.register_op0("c", sort);
    let and_op = eg.register_set("and", sort, sort);

    let a = eg.add(a_op, &[]);
    let b = eg.add(b_op, &[]);
    let c = eg.add(c_op, &[]);
    let l = eg.add(and_op, &[a, b]);
    let r = eg.add(and_op, &[b, c]);
    eg.rebuild();

    let snap = AuSnapshot::new(&eg).unwrap();
    let mut session = SearchSession::new(&snap, CycleMode::AncestorOnly);
    let config = McgsConfig {
        playouts: 100,
        ..Default::default()
    };

    // First search (includes AC transport descriptors on the stats entries).
    let (term1, completion1) = session.run_uct(l, r, &config).unwrap();
    let quality1 = session_quality(&session, term1);

    let token = session.mark();

    // More work on a different pair mutates every layer past the mark.
    let (_, _) = session.run_uct(a, c, &config).unwrap();

    // Restore: all layers (including the MCGS descriptor cache) roll back.
    session.restore(token);

    // Re-running the original pair on the restored session must agree.
    let (term2, completion2) = session.run_uct(l, r, &config).unwrap();
    let quality2 = session_quality(&session, term2);
    assert_eq!(
        quality1, quality2,
        "restored session must reproduce the result"
    );
    assert_eq!(completion1, completion2);
}

/// Descriptor-cache rollback: restoring past a search that created NON-EMPTY
/// transport descriptors must remove them, and a subsequent search on a
/// DIFFERENT AC pair (different transport shape, different classes) must
/// rebuild fresh descriptors. If stale descriptors survived the restore
/// (i.e. the transport_descs truncation were missing), the new pair's root
/// stats entry would read the old pair's descriptors by index and compose a
/// wrong anti-unifier, so the quality comparison against the exact oracle
/// fails.
#[test]
fn config64_descriptor_cache_rolls_back_and_rebuilds() {
    use semi_persistent_egraph::au::mcgs::McgsConfig;
    use semi_persistent_egraph::au::session::SearchSession;
    use semi_persistent_egraph::au::space::CycleMode;

    let mut eg = Eg64::new();
    let sort = eg.intern_sort("E");
    let a_op = eg.register_op0("a", sort);
    let b_op = eg.register_op0("b", sort);
    let c_op = eg.register_op0("c", sort);
    let p_op = eg.register_op0("p", sort);
    let q_op = eg.register_op0("q", sort);
    let s_op = eg.register_op0("s", sort);
    let t_op = eg.register_op0("t", sort);
    let and_op = eg.register_set("and", sort, sort);

    let a = eg.add(a_op, &[]);
    let b = eg.add(b_op, &[]);
    let c = eg.add(c_op, &[]);
    let p = eg.add(p_op, &[]);
    let q = eg.add(q_op, &[]);
    let s = eg.add(s_op, &[]);
    let t = eg.add(t_op, &[]);
    // First AC pair: 2-member monomials.
    let l1 = eg.add(and_op, &[a, b]);
    let r1 = eg.add(and_op, &[b, c]);
    // Second AC pair: 3-member monomials over disjoint classes.
    let l2 = eg.add(and_op, &[p, q, s]);
    let r2 = eg.add(and_op, &[q, s, t]);
    eg.rebuild();

    let snap = AuSnapshot::new(&eg).unwrap();
    let config = McgsConfig {
        playouts: 300,
        ..Default::default()
    };

    let mut session = SearchSession::new(&snap, CycleMode::AncestorOnly);

    // Mark the EMPTY session, then create non-empty descriptors.
    let token = session.mark();
    let (_, _) = session.run_uct(l1, r1, &config).unwrap();

    // Restore to empty: all descriptor lists created above must be removed.
    session.restore(token);

    // Search the second pair. Its root stats entry reuses index 0; stale
    // descriptors from the first pair would be read in its place.
    let (term, _) = session.run_uct(l2, r2, &config).unwrap();
    let session_result = session_quality(&session, term);

    // Reference: the exact oracle on the second pair.
    let exact = anti_unify(
        &snap,
        l2,
        r2,
        &AuConfig {
            algorithm: AuAlgorithm::Exact,
            ..Default::default()
        },
    )
    .unwrap();
    assert_eq!(
        session_result,
        exact.pool.quality(exact.term_id),
        "post-restore search must use fresh descriptors, not stale ones"
    );
    // and(q, s, Variants(p,t)) = 5 nodes.
    assert_eq!(session_result.0, 5);
}

fn session_quality<
    'e,
    Cfg: semi_persistent_egraph::config::EGraphConfig,
    L: semi_persistent_egraph::literal::LitVal,
    const T: bool,
    const P: bool,
>(
    session: &semi_persistent_egraph::au::session::SearchSession<'e, Cfg, L, T, P>,
    term: semi_persistent_egraph::au::session::TermOf<Cfg>,
) -> (u32, u32)
where
    semi_persistent_egraph::canon::MSetCanon:
        semi_persistent_egraph::canon::VarCanon<Cfg::G, Cfg::C>,
{
    session.pool_quality(term)
}
