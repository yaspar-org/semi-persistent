// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! The intersection-subtraction counterexample (§3.4.4 "greedy is ordering,
//! not pruning", exhibited fully).
//!
//! Heuristic under test: when anti-unifying AC multisets M and N, first remove
//! the common submultiset `I = M ∩ N` and pair each shared element with itself
//! (a "free" diagonal pair), then solve only the residuals `M − I` vs `N − I`.
//! This is the natural canonization-flavored shortcut: intersecting canonical
//! multisets is cheap and each self-pair AU(x,x) = best_term(x) looks locally
//! unbeatable.
//!
//! The counterexample: an operator-polymorphic class X (containing members
//! under two different head operators, created by a merge) is worth MORE used
//! crosswise against two operator-incompatible residuals than paired with
//! itself. Pairing X with X banks a locally optimal 3 but strands Y and Z,
//! whose AU degenerates to a bare Variants; the crossed matching pays 4 + 4
//! but factors an operator into the backbone on both children.
//!
//! The amplified family shows the gap grows linearly with the arity of the
//! leaf operators: intersection-first is worse by exactly (k − 1) at arity k,
//! so the heuristic is not merely off-by-one, it is unboundedly suboptimal.

use semi_persistent_egraph::EGraph31;
use semi_persistent_egraph::au::actions::{ActionCache, generate_actions};
use semi_persistent_egraph::au::egraph_api::AuSnapshot;
use semi_persistent_egraph::au::session::{AuAlgorithm, AuConfig, anti_unify};
use semi_persistent_egraph::literal::NiraLitVal;

type Eg = EGraph31<NiraLitVal, false, false>;

/// The minimal instance, with every intermediate quantity asserted.
///
///   X = {f(v,v), g(v,v)}   (merged: operator-polymorphic)
///   Y = {f(v,u)}
///   Z = {g(v,u)}
///   left  = acop{X, Y},  right = acop{X, Z}
#[test]
fn intersection_subtraction_is_suboptimal_minimal() {
    let mut eg = Eg::new();
    let sort = eg.intern_sort("E");
    let v_op = eg.register_op0("v", sort);
    let u_op = eg.register_op0("u", sort);
    let f = eg.register_op2("f", sort, sort, sort);
    let g = eg.register_op2("g", sort, sort, sort);
    let acop = eg.register_mset("acop", sort, sort);

    let v = eg.add(v_op, &[]);
    let u = eg.add(u_op, &[]);
    let x_f = eg.add(f, &[v, v]);
    let x_g = eg.add(g, &[v, v]);
    eg.merge(x_f, x_g); // X is polymorphic: f-member AND g-member
    let y = eg.add(f, &[v, u]);
    let z = eg.add(g, &[v, u]);
    let left = eg.add(acop, &[x_f, y]);
    let right = eg.add(acop, &[x_f, z]);
    eg.rebuild();

    let snap = AuSnapshot::new(&eg).unwrap();
    let exact = |l, r| {
        anti_unify(
            &snap,
            l,
            r,
            &AuConfig {
                algorithm: AuAlgorithm::Exact,
                ..Default::default()
            },
        )
        .unwrap()
        .size
    };

    // The building blocks of the two strategies.
    let au_xx = exact(x_f, x_f); // the "free" diagonal pair
    let au_yz = exact(y, z); // the stranded residual: no common operator
    let au_xz = exact(x_f, z); // crossed: factors through X's g-member
    let au_yx = exact(y, x_f); // crossed: factors through X's f-member

    assert_eq!(au_xx, 3, "AU(X,X) = best_term(X) = f(v,v), size 3");
    assert_eq!(
        au_yz, 6,
        "AU(Y,Z) = Variants(f(v,u), g(v,u)): no shared operator, all variant mass"
    );
    assert_eq!(au_xz, 4, "AU(X,Z) = g(v, Variants(v,u)) via X's g-member");
    assert_eq!(au_yx, 4, "AU(Y,X) = f(v, Variants(u,v)) via X's f-member");

    // Intersection-first total: 1 (acop) + AU(X,X) + AU(Y,Z) = 10.
    let intersection_first = 1 + au_xx + au_yz;
    assert_eq!(intersection_first, 10);

    // Crossed total: 1 (acop) + AU(X,Z) + AU(Y,X) = 9.
    let crossed = 1 + au_xz + au_yx;
    assert_eq!(crossed, 9);

    // The exact solver finds the crossed matching, beating intersection-first.
    let optimum = exact(left, right);
    assert_eq!(optimum, crossed);
    assert!(optimum < intersection_first);

    // Both matchings are present in the action set: the greedy diagonal is an
    // ordering heuristic, not a pruning rule (§3.4.4).
    let lc = snap.class_of(left).unwrap();
    let rc = snap.class_of(right).unwrap();
    let mut cache = ActionCache::new(usize::MAX);
    generate_actions(&snap, &mut cache, lc, rc);
    let actions = cache.get(lc, rc).unwrap();
    let x_class = snap.class_of(x_f).unwrap();
    let has_diagonal = actions.iter().any(|a| {
        a.pairs
            .iter()
            .any(|p| p.left == x_class && p.right == x_class)
    });
    let has_crossed = actions.iter().any(|a| {
        !a.pairs
            .iter()
            .any(|p| p.left == x_class && p.right == x_class)
    });
    assert!(has_diagonal, "the diagonal matching must remain reachable");
    assert!(has_crossed, "the crossed matching must remain reachable");
}

/// The amplified family: at leaf arity k, intersection-first loses by k − 1.
///
///   X_k = {f(v,…,v), g(v,…,v)}   (k copies of v; merged)
///   Y_k = {f(v,…,v,u)}           (k−1 copies of v, then u)
///   Z_k = {g(v,…,v,u)}
///
/// AU(Y_k, Z_k) is a bare Variants of two size-(k+1) terms: cost 2(k+1).
/// AU(X_k, Z_k) and AU(Y_k, X_k) factor the operator, pairing (v,v) k−1 times
/// and (v,u) once: cost 1 + (k−1) + 2 = k + 2 each.
/// Intersection-first: 1 + (k+1) + 2(k+1) = 3k + 4.
/// Crossed:            1 + 2(k + 2)       = 2k + 5.
/// Gap: (3k + 4) − (2k + 5) = k − 1: crossed wins for every k ≥ 2 and the
/// gap grows without bound in the arity.
#[test]
fn intersection_subtraction_gap_grows_with_arity() {
    for k in [2usize, 4, 6, 8] {
        let mut eg = Eg::new();
        let sort = eg.intern_sort("E");
        let v_op = eg.register_op0("v", sort);
        let u_op = eg.register_op0("u", sort);
        let sorts: Vec<_> = std::iter::repeat_n(sort, k).collect();
        let f = eg.register_opn("f", &sorts, sort);
        let g = eg.register_opn("g", &sorts, sort);
        let acop = eg.register_mset("acop", sort, sort);

        let v = eg.add(v_op, &[]);
        let u = eg.add(u_op, &[]);
        let all_v: Vec<_> = std::iter::repeat_n(v, k).collect();
        let mut v_then_u = all_v.clone();
        v_then_u[k - 1] = u;

        let x_f = eg.add(f, &all_v);
        let x_g = eg.add(g, &all_v);
        eg.merge(x_f, x_g);
        let y = eg.add(f, &v_then_u);
        let z = eg.add(g, &v_then_u);
        let left = eg.add(acop, &[x_f, y]);
        let right = eg.add(acop, &[x_f, z]);
        eg.rebuild();

        let snap = AuSnapshot::new(&eg).unwrap();
        let exact = |l, r| {
            anti_unify(
                &snap,
                l,
                r,
                &AuConfig {
                    algorithm: AuAlgorithm::Exact,
                    ..Default::default()
                },
            )
            .unwrap()
            .size
        };

        let k32 = k as u32;
        let intersection_first = 1 + (k32 + 1) + 2 * (k32 + 1); // 3k + 4
        let crossed = 1 + 2 * (k32 + 2); // 2k + 5

        let optimum = exact(left, right);
        assert!(
            crossed < intersection_first,
            "arity {k}: crossed must beat intersection-first"
        );
        assert_eq!(
            optimum, crossed,
            "arity {k}: exact must find the crossed matching"
        );
        assert_eq!(
            intersection_first - optimum,
            k32 - 1,
            "arity {k}: the gap is exactly k - 1"
        );
    }
}

/// Sanity floor for the heuristic's defenders: when the shared element is NOT
/// operator-polymorphic, intersection-first IS optimal. The counterexample
/// requires the polymorphism; this pins the boundary of the phenomenon.
#[test]
fn intersection_subtraction_is_optimal_without_polymorphism() {
    let mut eg = Eg::new();
    let sort = eg.intern_sort("E");
    let v_op = eg.register_op0("v", sort);
    let u_op = eg.register_op0("u", sort);
    let f = eg.register_op2("f", sort, sort, sort);
    let g = eg.register_op2("g", sort, sort, sort);
    let acop = eg.register_mset("acop", sort, sort);

    let v = eg.add(v_op, &[]);
    let u = eg.add(u_op, &[]);
    let x = eg.add(f, &[v, v]); // NOT merged with any g-member
    let y = eg.add(f, &[v, u]);
    let z = eg.add(g, &[v, u]);
    let left = eg.add(acop, &[x, y]);
    let right = eg.add(acop, &[x, z]);
    eg.rebuild();

    let snap = AuSnapshot::new(&eg).unwrap();
    let result = anti_unify(
        &snap,
        left,
        right,
        &AuConfig {
            algorithm: AuAlgorithm::Exact,
            ..Default::default()
        },
    )
    .unwrap();
    // Without a g-member on X, AU(X,Z) has no common operator (Variants, 6)
    // and the crossed total is 1 + 6 + 4 = 11; intersection-first stays 10.
    assert_eq!(result.size, 10);
}
