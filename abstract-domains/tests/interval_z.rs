// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Executable checks for the precise IntervalZ division port.
use semi_persistent_abstract_domains::ibig::IBig;
use semi_persistent_abstract_domains::interval_z::{Hi, IntervalZ, Lo};
use semi_persistent_abstract_domains::lattice::{BotOr, Domain};
use semi_persistent_abstract_domains::semantics::{Euclid, Trunc};
use semi_persistent_abstract_domains::transfer::{DivRem, DivZero, Mul};

fn z(v: i64) -> IBig {
    IBig::from_i64(v)
}

fn iv(lo: i64, hi: i64) -> IntervalZ {
    IntervalZ::new(Lo::Fin(z(lo)), Hi::Fin(z(hi))).expect("lo <= hi")
}

fn ray_pos(lo: i64) -> IntervalZ {
    IntervalZ::new(Lo::Fin(z(lo)), Hi::PosInf).expect("ray")
}

fn has(i: &IntervalZ, x: i64) -> bool {
    IntervalZ::constant(z(x)).leq(i)
}

fn quot(q: (BotOr<IntervalZ>, DivZero)) -> IntervalZ {
    match q.0 {
        BotOr::Val(v) => v,
        BotOr::Bot => panic!("expected a quotient"),
    }
}

#[test]
fn euclid_and_trunc_disagree_on_negatives() {
    let n = iv(-7, -7);
    let d = iv(2, 2);
    let (qe, fe) = <IntervalZ as DivRem<Euclid>>::div(&n, &d);
    let (qt, ft) = <IntervalZ as DivRem<Trunc>>::div(&n, &d);
    assert!(matches!(fe, DivZero::Never) && matches!(ft, DivZero::Never));
    let qe = quot((qe, fe));
    let qt = quot((qt, ft));
    assert!(has(&qe, -4) && !has(&qe, -3));
    assert!(has(&qt, -3) && !has(&qt, -4));
}

#[test]
fn negative_over_pos_inf_is_minus_one_for_euclid() {
    let n = iv(-8, -1);
    let d = ray_pos(1);
    let q = quot(<IntervalZ as DivRem<Euclid>>::div(&n, &d));
    assert!(has(&q, -1) && !has(&q, 0));
    let t = quot(<IntervalZ as DivRem<Trunc>>::div(&n, &d));
    assert!(has(&t, 0) && has(&t, -8));
}

#[test]
fn zero_divisor_is_bot_and_a_straddle_is_maybe() {
    let n = iv(1, 4);
    let zero = iv(0, 0);
    let (q, f) = <IntervalZ as DivRem<Euclid>>::div(&n, &zero);
    assert!(matches!(q, BotOr::Bot) && matches!(f, DivZero::Always));
    let wide = iv(-2, 3);
    let (q, f) = <IntervalZ as DivRem<Euclid>>::div(&n, &wide);
    assert!(matches!(f, DivZero::Maybe));
    let q = quot((q, f));
    assert!(has(&q, 1 / 3) && has(&q, -2));
}

#[test]
fn mul_corners_and_zero_times_infinity() {
    let a = iv(-2, 3);
    let b = iv(-4, 5);
    let p = <IntervalZ as Mul<Euclid>>::mul(&a, &b);
    assert!(has(&p, -12) && has(&p, 15));
    assert!(!has(&p, 16) && !has(&p, -13));
    let z = iv(0, 0);
    let wide = IntervalZ::new(Lo::NegInf, Hi::PosInf).unwrap();
    let p0 = <IntervalZ as Mul<Trunc>>::mul(&z, &wide);
    assert!(has(&p0, 0) && !has(&p0, 1) && !has(&p0, -1));
}

#[test]
fn remainder_is_exact_on_singletons_and_signed() {
    let n = iv(10, 10);
    let d = iv(3, 3);
    let (re, fe) = <IntervalZ as DivRem<Euclid>>::rem(&n, &d);
    let (rt, ft) = <IntervalZ as DivRem<Trunc>>::rem(&n, &d);
    assert!(matches!(fe, DivZero::Never) && matches!(ft, DivZero::Never));
    let re = quot((re, fe));
    let rt = quot((rt, ft));
    assert!(has(&re, 1) && !has(&re, 0) && !has(&re, 2));
    assert!(has(&rt, 1) && !has(&rt, 2));
    let neg = iv(-7, -7);
    let two = iv(2, 2);
    let re = quot(<IntervalZ as DivRem<Euclid>>::rem(&neg, &two));
    let rt = quot(<IntervalZ as DivRem<Trunc>>::rem(&neg, &two));
    assert!(has(&re, 1) && !has(&re, -1));
    assert!(has(&rt, -1) && !has(&rt, 1));
}

#[test]
fn remainder_is_cut_by_the_dividend() {
    let n = iv(-5, -5);
    let d = iv(-5, 1);
    let rt = quot(<IntervalZ as DivRem<Trunc>>::rem(&n, &d));
    assert!(has(&rt, -2) && has(&rt, 0));
    assert!(!has(&rt, -3) && !has(&rt, 1));
    let small = iv(-2, -2);
    let wide = iv(-10, -8);
    let rt = quot(<IntervalZ as DivRem<Trunc>>::rem(&small, &wide));
    assert!(has(&rt, -2) && !has(&rt, -3));
    let nn = iv(0, 5);
    let divs = iv(3, 100);
    let re = quot(<IntervalZ as DivRem<Euclid>>::rem(&nn, &divs));
    assert!(has(&re, 0) && has(&re, 5) && !has(&re, 6));
}

#[test]
fn narrow_replaces_infinity_and_refine_meets() {
    let top = IntervalZ::new(Lo::NegInf, Hi::PosInf).unwrap();
    let fact = iv(1, 2);
    match top.narrow(&fact) {
        BotOr::Val(v) => assert!(has(&v, 1) && has(&v, 2) && !has(&v, 0) && !has(&v, 3)),
        BotOr::Bot => panic!("expected a narrowed interval"),
    }
    let pos = ray_pos(0);
    assert!(matches!(pos.narrow(&iv(-5, -1)), BotOr::Bot));
    let (kept, fuel) = iv(0, 10).refine(&fact, 0);
    match kept {
        BotOr::Val(v) => assert!(has(&v, 0) && has(&v, 10)),
        BotOr::Bot => panic!("budget 0 keeps the interval"),
    }
    assert_eq!(fuel, 0);
    let (met, _) = iv(0, 10).refine(&fact, 1);
    match met {
        BotOr::Val(v) => assert!(has(&v, 1) && has(&v, 2) && !has(&v, 0)),
        BotOr::Bot => panic!("expected the meet"),
    }
}

#[test]
fn widen_jumps_an_unstable_bound() {
    let a = iv(0, 0);
    let b = iv(0, 1);
    let w = a.widen(&b);
    assert!(has(&w, 0) && has(&w, 100));
    assert!(!has(&w, -1));
}
