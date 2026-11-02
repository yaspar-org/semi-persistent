// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Runtime checks of the reduced-product protocol (src/reduce.rs) and the fact
//! records against brute-force concretization at u8, plus u128 instances.
mod common;

use common::{Set8, check_assume_u8, check_binop_u8, check_cmp_u8, set_of};
use semi_persistent_abstract_domains::bool4::Bool4;
use semi_persistent_abstract_domains::facts::Facts;
use semi_persistent_abstract_domains::facts_z::FactsZ;
use semi_persistent_abstract_domains::ibig::IBig;
use semi_persistent_abstract_domains::interval::Interval;
use semi_persistent_abstract_domains::interval_z::{Hi, IntervalZ, Lo};
use semi_persistent_abstract_domains::lattice::{BotOr, Domain};
use semi_persistent_abstract_domains::reduce::{Channel, Product, REDUCE_FUEL, Refine};
use semi_persistent_abstract_domains::semantics::{Euclid, Signed, Trunc, Unsigned};
use semi_persistent_abstract_domains::transfer::{Arith, Compare, DivRem, DivZero, Mul};

type I8 = Interval<u8>;
type F8 = Facts<u8>;
type P8 = Product<I8, I8>;
type U = Unsigned<u8>;

fn iv(lo: u8, hi: u8) -> I8 {
    Interval::new(lo, hi).expect("lo <= hi")
}

fn i_has(i: &I8, x: u8) -> bool {
    let (lo, hi) = i.bounds();
    lo <= x && x <= hi
}

fn f_has(f: &F8, x: u8) -> bool {
    i_has(&f.interval(), x)
}

fn p_has(p: &P8, x: u8) -> bool {
    i_has(&p.a, x) && i_has(&p.b, x)
}

fn bot<D>(b: BotOr<D>) -> Option<D> {
    match b {
        BotOr::Bot => None,
        BotOr::Val(d) => Some(d),
    }
}

/// The smallest interval containing a nonempty set.
fn alpha_i(s: &Set8) -> I8 {
    let lo = (0..256).find(|&z| s[z]).expect("nonempty") as u8;
    let hi = (0..256).rev().find(|&z| s[z]).expect("nonempty") as u8;
    iv(lo, hi)
}

/// Intervals whose bounds lie on a grid that includes the signed and
/// unsigned extremes: 36 of the 32,896 u8 intervals.
fn grid() -> Vec<I8> {
    let pts = [0u8, 1, 50, 127, 128, 129, 200, 255];
    let mut out = Vec::new();
    for &a in &pts {
        for &b in &pts {
            if a <= b {
                out.push(iv(a, b));
            }
        }
    }
    out
}

/// Products of two grid intervals, including disjoint and redundant pairs:
/// 36 * 36 = 1,296 values, optionally thinned to every `step`-th.
fn products(step: usize) -> Vec<P8> {
    let g = grid();
    let mut out = Vec::new();
    for a in &g {
        for b in &g {
            out.push(Product {
                a: a.dup(),
                b: b.dup(),
            });
        }
    }
    out.into_iter().step_by(step).collect()
}

#[test]
fn facts_normalize_every_u8_interval() {
    let mut n = 0;
    for lo in 0..=255u8 {
        for hi in lo..=255u8 {
            let f = Facts::from_interval(iv(lo, hi));
            let r = bot(f.normalize()).expect("nonempty record normalizes to a value");
            assert_eq!(set_of(&r, &f_has), set_of(&f, &f_has));
            n += 1;
        }
    }
    assert_eq!(n, 32_896);
}

#[test]
fn facts_meet_and_refine() {
    let g: Vec<F8> = grid().into_iter().map(Facts::from_interval).collect();
    for a in &g {
        for b in &g {
            let want: Set8 = std::array::from_fn(|z| f_has(a, z as u8) && f_has(b, z as u8));
            for r in [bot(a.meet_exact(b)), bot(a.meet(b)), bot(a.refine(b))] {
                match r {
                    None => assert!(want.iter().all(|&w| !w)),
                    Some(m) => assert_eq!(set_of(&m, &f_has), want),
                }
            }
            if a.leq(b) {
                assert!((0..=255u8).all(|x| !f_has(a, x) || f_has(b, x)));
            }
            let j = a.join(b);
            assert!((0..=255u8).all(|x| !(f_has(a, x) || f_has(b, x)) || f_has(&j, x)));
        }
    }
}

#[test]
fn product_reduce_preserves_gamma_for_every_fuel() {
    let mut reduced = 0;
    let all = products(1);
    for p in &all {
        let want = set_of(p, &p_has);
        for fuel in 0..=4u8 {
            match bot(p.reduce(fuel)) {
                None => {
                    assert!(fuel > 0);
                    assert!(want.iter().all(|&w| !w));
                }
                Some(r) => {
                    assert_eq!(set_of(&r, &p_has), want, "fuel {fuel}");
                    // One round is complete for Interval x Interval: both
                    // components become the intersection.
                    if fuel > 0 {
                        assert_eq!(r.a.bounds(), r.b.bounds());
                        reduced += 1;
                    }
                }
            }
        }
    }
    assert_eq!(all.len(), 1_296);
    assert!(reduced > 0);
}

#[test]
fn product_meet_reduce_is_the_intersection() {
    let ps = products(7);
    for p in &ps {
        for q in &ps {
            let want: Set8 = std::array::from_fn(|z| p_has(p, z as u8) && p_has(q, z as u8));
            match bot(p.meet_reduce(q, 1)) {
                None => assert!(want.iter().all(|&w| !w)),
                Some(m) => assert_eq!(set_of(&m, &p_has), want),
            }
        }
    }
}

/// The nonempty products among `products(1)`, reduced: the values an e-class
/// holds after a merge. 876 of the 1,296 pairs are nonempty; every 9th is kept
/// (98 values, 9,604 operand pairs).
fn reduced_products() -> Vec<P8> {
    let all: Vec<P8> = products(1)
        .iter()
        .filter_map(|p| bot(p.reduce(1)))
        .collect();
    assert_eq!(all.len(), 876);
    all.into_iter().step_by(9).collect()
}

#[test]
fn product_transfers_sound_and_measured() {
    // Transfers are componentwise; as in the e-graph, the root reduces once.
    let ps = reduced_products();
    let alpha = |s: &Set8| Product {
        a: alpha_i(s),
        b: alpha_i(s),
    };
    let add = check_binop_u8(
        "add",
        &ps,
        p_has,
        |a, b| bot(<P8 as Arith<U>>::add(a, b).reduce(REDUCE_FUEL)),
        |x, y| Some(x.wrapping_add(y)),
        alpha,
    );
    let sub = check_binop_u8(
        "sub",
        &ps,
        p_has,
        |a, b| bot(<P8 as Arith<U>>::sub(a, b).reduce(REDUCE_FUEL)),
        |x, y| Some(x.wrapping_sub(y)),
        alpha,
    );
    let mul = check_binop_u8(
        "mul",
        &ps,
        p_has,
        |a, b| bot(<P8 as Mul<U>>::mul(a, b).reduce(REDUCE_FUEL)),
        |x, y| Some(x.wrapping_mul(y)),
        alpha,
    );
    let div = check_binop_u8(
        "udiv",
        &ps,
        p_has,
        |a, b| bot(<P8 as DivRem<U>>::div(a, b).0).and_then(|q| bot(q.reduce(REDUCE_FUEL))),
        |x, y| x.checked_div(y),
        alpha,
    );
    let rem = check_binop_u8(
        "urem",
        &ps,
        p_has,
        |a, b| bot(<P8 as DivRem<U>>::rem(a, b).0).and_then(|q| bot(q.reduce(REDUCE_FUEL))),
        |x, y| x.checked_rem(y),
        alpha,
    );
    for (n, r) in [
        ("add", add),
        ("sub", sub),
        ("mul", mul),
        ("udiv", div),
        ("urem", rem),
    ] {
        println!(
            "Product<Interval<u8>, Interval<u8>> {n}: {} pairs, {:.1}% non-optimal",
            r.cases,
            r.pct_non_optimal()
        );
    }
}

#[test]
fn product_div_flags() {
    let ps = products(9);
    for a in &ps {
        for d in &ps {
            let has0 = p_has(d, 0);
            let only0 = (0..=255u8).all(|y| !p_has(d, y) || y == 0);
            for (q, f) in [<P8 as DivRem<U>>::div(a, d), <P8 as DivRem<U>>::rem(a, d)] {
                assert_eq!(<P8 as DivRem<U>>::contains_zero(d), has0);
                match f {
                    DivZero::Never => assert!(!has0),
                    DivZero::Always => {
                        assert!(only0);
                        assert!(matches!(q, BotOr::Bot));
                    }
                    DivZero::Maybe => assert!(matches!(q, BotOr::Val(_))),
                }
            }
        }
    }
}

#[test]
fn nested_product_reduces() {
    // Product<Product<Interval, Facts>, Interval>: products nest through Refine.
    let inner = Product {
        a: iv(10, 200),
        b: Facts::from_interval(iv(0, 100)),
    };
    let p = Product {
        a: inner,
        b: iv(50, 255),
    };
    let r = bot(p.reduce(2)).expect("nonempty");
    assert_eq!(r.a.a.bounds(), (50, 100));
    assert_eq!(r.a.b.interval().bounds(), (50, 100));
    assert_eq!(r.b.bounds(), (50, 100));
    let empty = Product {
        a: Product {
            a: iv(0, 10),
            b: Facts::from_interval(iv(0, 255)),
        },
        b: iv(20, 30),
    };
    assert!(matches!(empty.reduce(1), BotOr::Bot));
}

#[test]
fn u128_instances() {
    let a = Interval::<u128>::new(u128::MAX - 10, u128::MAX).unwrap();
    let b = Interval::<u128>::new(5, u128::MAX - 5).unwrap();
    let p = Product { a, b };
    let r = bot(p.reduce(1)).expect("nonempty");
    assert_eq!(r.a.bounds(), (u128::MAX - 10, u128::MAX - 5));
    assert_eq!(r.b.bounds(), r.a.bounds());
    let f = Facts::from_interval(Interval::<u128>::new(1, 2).unwrap());
    let g = Facts::from_interval(Interval::<u128>::new(3, 4).unwrap());
    assert!(matches!(f.meet_exact(&g), BotOr::Bot));
    let s = <Facts<u128> as Arith<Unsigned<u128>>>::add(&f, &g);
    assert_eq!(s.interval().bounds(), (4, 6));
}

#[test]
fn bool4_connectives_are_exact() {
    // Every operand pair: 3 x 3 for the binary connectives.
    let vals = [Bool4::False, Bool4::True, Bool4::Top];
    let has = |b: &Bool4, x: bool| match b {
        Bool4::False => !x,
        Bool4::True => x,
        Bool4::Top => true,
    };
    let set = |b: &Bool4| [has(b, false), has(b, true)];
    for a in &vals {
        let n = a.not();
        let want = [has(a, true), has(a, false)];
        assert_eq!(set(&n), want);
        for b in &vals {
            for (r, op) in [
                (a.and(b), (|x, y| x && y) as fn(bool, bool) -> bool),
                (a.or(b), |x, y| x || y),
                (a.eq(b), |x, y| x == y),
            ] {
                let mut want = [false; 2];
                for x in [false, true] {
                    for y in [false, true] {
                        if has(a, x) && has(b, y) {
                            want[op(x, y) as usize] = true;
                        }
                    }
                }
                assert_eq!(set(&r), want);
            }
            let m = bot(a.meet_exact(b));
            let want = [has(a, false) && has(b, false), has(a, true) && has(b, true)];
            match m {
                None => assert_eq!(want, [false, false]),
                Some(m) => assert_eq!(set(&m), want),
            }
        }
    }
}

#[test]
fn facts_z_meet_and_arith() {
    let z = |v: i64| IBig::from_i64(v);
    let fz = |lo: i64, hi: i64| {
        FactsZ::from_interval(IntervalZ::new(Lo::Fin(z(lo)), Hi::Fin(z(hi))).unwrap())
    };
    let has = |f: &FactsZ, x: i64| IntervalZ::constant(z(x)).leq(&f.interval());
    let a = fz(-5, 5);
    let b = fz(3, 9);
    let m = bot(a.meet_exact(&b)).expect("overlap");
    assert!((-20..=20).all(|x| has(&m, x) == (has(&a, x) && has(&b, x))));
    assert!(matches!(a.meet_exact(&fz(6, 7)), BotOr::Bot));
    let s = <FactsZ as Arith<Euclid>>::add(&a, &b);
    for x in -5..=5 {
        for y in 3..=9 {
            assert!(has(&s, x + y));
        }
    }
    let p = Product {
        a: IntervalZ::top(),
        b: fz(0, 3),
    };
    let r = bot(p.reduce(1)).expect("nonempty");
    assert!((-10..=10).all(|x| has(&r.b, x) == (0..=3).contains(&x)));
}

type S8 = Signed<u8>;
type PF8 = Product<F8, F8>;

fn pf_has(p: &PF8, x: u8) -> bool {
    f_has(&p.a, x) && f_has(&p.b, x)
}

/// Prints and returns the measured percentage.
fn report(what: &str, r: common::OpReport) -> f64 {
    println!(
        "{what}: {} cases, {:.1}% non-optimal",
        r.cases,
        r.pct_non_optimal()
    );
    r.pct_non_optimal()
}

/// The Compare stubs answer `Top` and keep both operands, so they are sound
/// and almost never optimal; the planned transfers replace them.
#[test]
fn facts_compare_stubs_sound_and_measured() {
    let g: Vec<F8> = grid().into_iter().map(Facts::from_interval).collect();
    let alpha = |s: &Set8| Facts::from_interval(alpha_i(s));
    let ult = |x: u8, y: u8| x < y;
    let ule = |x: u8, y: u8| x <= y;
    let slt = |x: u8, y: u8| (x as i8) < (y as i8);
    let sle = |x: u8, y: u8| (x as i8) <= (y as i8);
    let eq = |x: u8, y: u8| x == y;
    let fwd: [(&str, f64); 5] = [
        (
            "bvult",
            report(
                "Facts<u8> bvult",
                check_cmp_u8("bvult", &g, f_has, <F8 as Compare<U>>::lt, ult),
            ),
        ),
        (
            "bvule",
            report(
                "Facts<u8> bvule",
                check_cmp_u8("bvule", &g, f_has, <F8 as Compare<U>>::le, ule),
            ),
        ),
        (
            "bvslt",
            report(
                "Facts<u8> bvslt",
                check_cmp_u8("bvslt", &g, f_has, <F8 as Compare<S8>>::lt, slt),
            ),
        ),
        (
            "bvsle",
            report(
                "Facts<u8> bvsle",
                check_cmp_u8("bvsle", &g, f_has, <F8 as Compare<S8>>::le, sle),
            ),
        ),
        (
            "=",
            report(
                "Facts<u8> =",
                check_cmp_u8("=", &g, f_has, <F8 as Compare<U>>::eq, eq),
            ),
        ),
    ];
    let pair = |r: (BotOr<F8>, BotOr<F8>)| (bot(r.0), bot(r.1));
    let bwd: [(&str, f64); 5] = [
        (
            "assume bvult",
            report(
                "Facts<u8> assume bvult",
                check_assume_u8(
                    "assume bvult",
                    &g,
                    f_has,
                    |a, b, t| pair(<F8 as Compare<U>>::assume_lt(a, b, t)),
                    ult,
                    alpha,
                ),
            ),
        ),
        (
            "assume bvule",
            report(
                "Facts<u8> assume bvule",
                check_assume_u8(
                    "assume bvule",
                    &g,
                    f_has,
                    |a, b, t| pair(<F8 as Compare<U>>::assume_le(a, b, t)),
                    ule,
                    alpha,
                ),
            ),
        ),
        (
            "assume bvslt",
            report(
                "Facts<u8> assume bvslt",
                check_assume_u8(
                    "assume bvslt",
                    &g,
                    f_has,
                    |a, b, t| pair(<F8 as Compare<S8>>::assume_lt(a, b, t)),
                    slt,
                    alpha,
                ),
            ),
        ),
        (
            "assume bvsle",
            report(
                "Facts<u8> assume bvsle",
                check_assume_u8(
                    "assume bvsle",
                    &g,
                    f_has,
                    |a, b, t| pair(<F8 as Compare<S8>>::assume_le(a, b, t)),
                    sle,
                    alpha,
                ),
            ),
        ),
        (
            "assume =",
            report(
                "Facts<u8> assume =",
                check_assume_u8(
                    "assume =",
                    &g,
                    f_has,
                    |a, b, t| pair(<F8 as Compare<U>>::assume_eq(a, b, t)),
                    eq,
                    alpha,
                ),
            ),
        ),
    ];
    // Top is optimal only when both truth values occur.
    for (_, pct) in fwd.iter().chain(bwd.iter()) {
        assert!(*pct > 0.0);
    }
}

#[test]
fn product_compare_sound_and_measured() {
    let g: Vec<F8> = grid()
        .into_iter()
        .step_by(3)
        .map(Facts::from_interval)
        .collect();
    let mut ps = Vec::new();
    for a in &g {
        for b in &g {
            ps.push(Product {
                a: a.dup(),
                b: b.dup(),
            });
        }
    }
    let ps: Vec<PF8> = ps.into_iter().filter_map(|p| bot(p.reduce(1))).collect();
    let alpha = |s: &Set8| Product {
        a: Facts::from_interval(alpha_i(s)),
        b: Facts::from_interval(alpha_i(s)),
    };
    report(
        "Product<Facts<u8>, Facts<u8>> bvult",
        check_cmp_u8("bvult", &ps, pf_has, <PF8 as Compare<U>>::lt, |x, y| x < y),
    );
    report(
        "Product<Facts<u8>, Facts<u8>> assume bvslt",
        check_assume_u8(
            "assume bvslt",
            &ps,
            pf_has,
            |a, b, t| {
                let r = <PF8 as Compare<S8>>::assume_lt(a, b, t);
                (bot(r.0), bot(r.1))
            },
            |x, y| (x as i8) < (y as i8),
            alpha,
        ),
    );
}

#[test]
fn facts_z_compare_stubs_sound() {
    let z = |v: i64| IBig::from_i64(v);
    let fz = |lo: i64, hi: i64| {
        FactsZ::from_interval(IntervalZ::new(Lo::Fin(z(lo)), Hi::Fin(z(hi))).unwrap())
    };
    let has = |f: &FactsZ, x: i64| IntervalZ::constant(z(x)).leq(&f.interval());
    let bhas = common::bool4_has;
    let s = [fz(-5, 5), fz(3, 9), fz(-9, -6), fz(0, 0)];
    for a in &s {
        for b in &s {
            for (r, rt) in [
                (
                    <FactsZ as Compare<Euclid>>::lt(a, b),
                    <FactsZ as Compare<Trunc>>::lt(a, b),
                ),
                (
                    <FactsZ as Compare<Euclid>>::le(a, b),
                    <FactsZ as Compare<Trunc>>::le(a, b),
                ),
            ] {
                assert!(bhas(&r, true) && bhas(&r, false) && bhas(&rt, true) && bhas(&rt, false));
            }
            for t in [false, true] {
                let (r0, r1) = <FactsZ as Compare<Euclid>>::assume_eq(a, b, t);
                let (r0, r1) = (bot(r0).unwrap(), bot(r1).unwrap());
                assert!((-20..=20).all(|x| has(&r0, x) == has(a, x) && has(&r1, x) == has(b, x)));
            }
        }
    }
}

/// Intersection of u8 intervals, or `None` when it is empty.
fn meet_all(xs: &[(u8, u8)]) -> Option<(u8, u8)> {
    let lo = xs.iter().map(|x| x.0).max()?;
    let hi = xs.iter().map(|x| x.1).min()?;
    (lo <= hi).then_some((lo, hi))
}

#[test]
fn n_ary_products_reduce_in_one_round() {
    use semi_persistent_abstract_domains::{product, product_pat, product_type};
    // One round meets the records of all leaves and refines every leaf by the
    // result, so after `reduce(1)` each leaf is the intersection of all of them.
    let mut seed = 0x2545_f491_u32;
    let mut next = || {
        seed ^= seed << 13;
        seed ^= seed >> 17;
        seed ^= seed << 5;
        let (x, y) = ((seed & 0xff) as u8, (seed >> 8 & 0xff) as u8);
        (x.min(y), x.max(y))
    };
    let (mut empty, mut nonempty) = (0, 0);
    for _ in 0..2000 {
        let v: Vec<(u8, u8)> = (0..5).map(|_| next()).collect();
        let iv5 = |i: usize| iv(v[i].0, v[i].1);
        let fv5 = |i: usize| F8::from_interval(iv5(i));

        let p2: product_type![I8, F8] = product!(iv5(0), fv5(1));
        let p3: product_type![I8, F8, I8] = product!(iv5(0), fv5(1), iv5(2));
        let p4: product_type![I8, F8, I8, F8] = product!(iv5(0), fv5(1), iv5(2), fv5(3));
        let p5: product_type![I8, F8, I8, F8, I8] =
            product!(iv5(0), fv5(1), iv5(2), fv5(3), iv5(4));

        match meet_all(&v[..2]) {
            None => assert!(matches!(p2.reduce(1), BotOr::Bot)),
            Some(m) => {
                let product_pat!(a, b) = bot(p2.reduce(1)).expect("nonempty");
                assert_eq!((a.bounds(), b.interval().bounds()), (m, m));
            }
        }
        match meet_all(&v[..3]) {
            None => assert!(matches!(p3.reduce(1), BotOr::Bot)),
            Some(m) => {
                let product_pat!(a, b, c) = bot(p3.reduce(1)).expect("nonempty");
                assert_eq!((a.bounds(), b.interval().bounds(), c.bounds()), (m, m, m));
            }
        }
        match meet_all(&v[..4]) {
            None => assert!(matches!(p4.reduce(1), BotOr::Bot)),
            Some(m) => {
                let product_pat!(a, b, c, d) = bot(p4.reduce(1)).expect("nonempty");
                assert_eq!(
                    (
                        a.bounds(),
                        b.interval().bounds(),
                        c.bounds(),
                        d.interval().bounds()
                    ),
                    (m, m, m, m)
                );
            }
        }
        match meet_all(&v) {
            None => {
                empty += 1;
                assert!(matches!(p5.reduce(1), BotOr::Bot));
            }
            Some(m) => {
                nonempty += 1;
                let product_pat!(a, b, c, d, e) = bot(p5.reduce(1)).expect("nonempty");
                assert_eq!(
                    [
                        a.bounds(),
                        b.interval().bounds(),
                        c.bounds(),
                        d.interval().bounds(),
                        e.bounds()
                    ],
                    [m; 5]
                );
            }
        }
    }
    // Both outcomes occur, so the loop exercises the `Bot` path and the refinement.
    assert!(
        empty > 0 && nonempty > 0,
        "{empty} empty, {nonempty} nonempty"
    );
}
