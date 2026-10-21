// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Exhaustive small-model checks for the mathematical-integer Sign domain.

use semi_persistent_abstract_domains::{
    facts_z::FactsZ,
    ibig::IBig,
    interval_z::{Hi, IntervalZ, Lo},
    lattice::{BotOr, Domain},
    reduce::Refine,
    semantics::{Euclid, Trunc},
    sign::{Sign, SignKind},
    transfer::{Arith, DivRem, Mul},
};

fn states() -> [SignKind; 7] {
    [
        SignKind::Neg,
        SignKind::Zero,
        SignKind::Pos,
        SignKind::NonPos,
        SignKind::NonNeg,
        SignKind::NonZero,
        SignKind::Top,
    ]
}

fn members(s: &Sign) -> impl Iterator<Item = i128> + '_ {
    (-12..=12).filter(move |x| s.contains(*x))
}

fn z(x: i64) -> IBig {
    IBig::from_i64(x)
}

fn facts(lo: i64, hi: i64) -> FactsZ {
    FactsZ::from_interval(IntervalZ::new(Lo::Fin(z(lo)), Hi::Fin(z(hi))).unwrap())
}

fn fact_has(f: &FactsZ, x: i64) -> bool {
    IntervalZ::constant(z(x)).leq(&f.interval())
}

/// Every non-bottom Sign category is determined by whether it contains a
/// negative value, zero, and a positive value.  The representatives -1, 0,
/// and 1 therefore check exactness rather than only containment.
fn assert_exact_sign(result: &Sign, expected: impl Fn(i128) -> bool, label: &str) {
    for representative in [-1, 0, 1] {
        assert_eq!(
            result.contains(representative),
            expected(representative),
            "{label}: category for {representative}"
        );
    }
}

fn same_sign_category(value: i128, representative: i128) -> bool {
    (value < 0) == (representative < 0)
        && (value == 0) == (representative == 0)
        && (value > 0) == (representative > 0)
}

#[test]
fn lattice_is_exact_on_all_categories() {
    for a_kind in states() {
        let a = Sign::from_kind(a_kind);
        for b_kind in states() {
            let b = Sign::from_kind(b_kind);
            let join = a.join(&b);
            let meet = a.meet(&b);
            for x in -12..=12 {
                assert_eq!(join.contains(x), a.contains(x) || b.contains(x));
                assert_eq!(
                    match &meet {
                        BotOr::Bot => false,
                        BotOr::Val(v) => v.contains(x),
                    },
                    a.contains(x) && b.contains(x)
                );
            }
            assert_eq!(
                a.leq(&b),
                (-12..=12).all(|x| !a.contains(x) || b.contains(x))
            );
        }
    }
}

#[test]
fn integer_transfers_are_exact_on_all_categories() {
    for a_kind in states() {
        let a = Sign::from_kind(a_kind);
        let euclid_neg = <Sign as Arith<Euclid>>::neg(&a);
        let trunc_neg = <Sign as Arith<Trunc>>::neg(&a);
        for x in members(&a) {
            assert!(euclid_neg.contains(-x), "euclid neg: {a_kind:?}, {x}");
            assert!(trunc_neg.contains(-x), "trunc neg: {a_kind:?}, {x}");
        }
        assert_exact_sign(
            &euclid_neg,
            |z| members(&a).any(|x| same_sign_category(-x, z)),
            "euclid neg",
        );
        assert_exact_sign(
            &trunc_neg,
            |z| members(&a).any(|x| same_sign_category(-x, z)),
            "trunc neg",
        );
        for b_kind in states() {
            let b = Sign::from_kind(b_kind);
            let euclid_add = <Sign as Arith<Euclid>>::add(&a, &b);
            let euclid_sub = <Sign as Arith<Euclid>>::sub(&a, &b);
            let euclid_mul = <Sign as Mul<Euclid>>::mul(&a, &b);
            let trunc_add = <Sign as Arith<Trunc>>::add(&a, &b);
            let trunc_sub = <Sign as Arith<Trunc>>::sub(&a, &b);
            let trunc_mul = <Sign as Mul<Trunc>>::mul(&a, &b);
            for x in members(&a) {
                for y in members(&b) {
                    assert!(
                        euclid_add.contains(x + y),
                        "euclid add: {a_kind:?}, {b_kind:?}, {x}, {y}"
                    );
                    assert!(
                        euclid_sub.contains(x - y),
                        "euclid sub: {a_kind:?}, {b_kind:?}, {x}, {y}"
                    );
                    assert!(
                        euclid_mul.contains(x * y),
                        "euclid mul: {a_kind:?}, {b_kind:?}, {x}, {y}"
                    );
                    assert!(
                        trunc_add.contains(x + y),
                        "trunc add: {a_kind:?}, {b_kind:?}, {x}, {y}"
                    );
                    assert!(
                        trunc_sub.contains(x - y),
                        "trunc sub: {a_kind:?}, {b_kind:?}, {x}, {y}"
                    );
                    assert!(
                        trunc_mul.contains(x * y),
                        "trunc mul: {a_kind:?}, {b_kind:?}, {x}, {y}"
                    );
                }
            }
            assert_exact_sign(
                &euclid_add,
                |z| members(&a).any(|x| members(&b).any(|y| same_sign_category(x + y, z))),
                &format!("euclid add: {a_kind:?}, {b_kind:?}"),
            );
            assert_exact_sign(
                &euclid_sub,
                |z| members(&a).any(|x| members(&b).any(|y| same_sign_category(x - y, z))),
                "euclid sub",
            );
            assert_exact_sign(
                &euclid_mul,
                |z| members(&a).any(|x| members(&b).any(|y| same_sign_category(x * y, z))),
                "euclid mul",
            );
            assert_exact_sign(
                &trunc_add,
                |z| members(&a).any(|x| members(&b).any(|y| same_sign_category(x + y, z))),
                "trunc add",
            );
            assert_exact_sign(
                &trunc_sub,
                |z| members(&a).any(|x| members(&b).any(|y| same_sign_category(x - y, z))),
                "trunc sub",
            );
            assert_exact_sign(
                &trunc_mul,
                |z| members(&a).any(|x| members(&b).any(|y| same_sign_category(x * y, z))),
                "trunc mul",
            );
        }
    }
}

#[test]
fn division_flags_and_results_are_sound() {
    for a_kind in states() {
        let a = Sign::from_kind(a_kind);
        for b_kind in states() {
            let b = Sign::from_kind(b_kind);
            let (eq, ef) = <Sign as DivRem<Euclid>>::div(&a, &b);
            let (er, rf) = <Sign as DivRem<Euclid>>::rem(&a, &b);
            let (tq, tf) = <Sign as DivRem<Trunc>>::div(&a, &b);
            let (tr, tf_r) = <Sign as DivRem<Trunc>>::rem(&a, &b);
            let expected_flag = match b_kind {
                SignKind::Zero => "always",
                SignKind::Neg | SignKind::Pos | SignKind::NonZero => "never",
                SignKind::NonPos | SignKind::NonNeg | SignKind::Top => "maybe",
            };
            for flag in [&ef, &rf, &tf, &tf_r] {
                assert!(
                    matches!(
                        (expected_flag, flag),
                        (
                            "always",
                            semi_persistent_abstract_domains::transfer::DivZero::Always
                        ) | (
                            "never",
                            semi_persistent_abstract_domains::transfer::DivZero::Never
                        ) | (
                            "maybe",
                            semi_persistent_abstract_domains::transfer::DivZero::Maybe
                        )
                    ),
                    "wrong DivZero flag for {b_kind:?}"
                );
            }
            if b.kind() == SignKind::Zero {
                assert!(matches!(
                    (eq, er, tq, tr, ef, rf, tf, tf_r),
                    (BotOr::Bot, BotOr::Bot, BotOr::Bot, BotOr::Bot, _, _, _, _)
                ));
                continue;
            }
            for x in members(&a) {
                for y in members(&b).filter(|y| *y != 0) {
                    assert!(matches!(&eq, BotOr::Val(v) if v.contains(x.div_euclid(y))));
                    assert!(matches!(&er, BotOr::Val(v) if v.contains(x.rem_euclid(y))));
                    assert!(matches!(&tq, BotOr::Val(v) if v.contains(x / y)));
                    assert!(matches!(&tr, BotOr::Val(v) if v.contains(x % y)));
                }
            }

            // Every sign category has a witness among -1, 0, and 1.  The
            // bounded model therefore checks the exact sign result of each
            // quotient/remainder transfer, while the Verus contracts prove
            // universal containment.
            for z in [-1, 0, 1] {
                let trunc_quotient =
                    members(&a).any(|x| members(&b).filter(|y| *y != 0).any(|y| x / y == z));
                let trunc_remainder =
                    members(&a).any(|x| members(&b).filter(|y| *y != 0).any(|y| x % y == z));
                let euclid_quotient = members(&a).any(|x| {
                    members(&b)
                        .filter(|y| *y != 0)
                        .any(|y| x.div_euclid(y) == z)
                });
                let euclid_remainder = members(&a).any(|x| {
                    members(&b)
                        .filter(|y| *y != 0)
                        .any(|y| x.rem_euclid(y) == z)
                });
                assert!(
                    matches!(&tq, BotOr::Val(v) if v.contains(z) == trunc_quotient),
                    "trunc div: {a_kind:?}, {b_kind:?}, {z}"
                );
                assert!(
                    matches!(&tr, BotOr::Val(v) if v.contains(z) == trunc_remainder),
                    "trunc rem: {a_kind:?}, {b_kind:?}, {z}"
                );
                assert!(
                    matches!(&eq, BotOr::Val(v) if v.contains(z) == euclid_quotient),
                    "euclid div: {a_kind:?}, {b_kind:?}, {z}"
                );
                assert!(
                    matches!(&er, BotOr::Val(v) if v.contains(z) == euclid_remainder),
                    "euclid rem: {a_kind:?}, {b_kind:?}, {z}"
                );
            }
        }
    }
}

#[test]
fn refinement_with_integer_facts_preserves_and_never_grows() {
    let fact_ranges = [(-8, -2), (-3, 0), (-1, 1), (0, 0), (1, 5), (-6, 6)];
    for kind in states() {
        let sign = Sign::from_kind(kind);
        for (lo, hi) in fact_ranges {
            let f = facts(lo, hi);
            let refined = <Sign as Refine>::refine(&sign, &f);
            for x in -12..=12i128 {
                let expected = sign.contains(x) && fact_has(&f, x as i64);
                let actual = match &refined {
                    BotOr::Bot => false,
                    BotOr::Val(s) => s.contains(x),
                };
                assert!(
                    expected <= actual,
                    "{kind:?} refined by [{lo}, {hi}] lost {x}"
                );
                assert!(!actual || sign.contains(x));
            }
        }
    }
}
