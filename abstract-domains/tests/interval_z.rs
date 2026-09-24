// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Executable checks for IntervalZ: lattice laws, containment, alarms,
//! widen/narrow, and the §4.5 refinement budget.

use semi_persistent_abstract_domains::ibig::IBig;
use semi_persistent_abstract_domains::interval_z::{Alarm, Bound, IntervalR, IntervalZ};

fn fin(n: i64) -> Bound {
    Bound::fin(n)
}

#[test]
fn bottom_has_nothing_top_has_everything() {
    let bot = IntervalZ::bottom();
    assert!(bot.empty);
    for n in [-100i64, 0, 100] {
        assert!(!bot.contains(n));
    }
    let top = IntervalZ::top();
    for n in [i64::MIN, -1, 0, 1, i64::MAX] {
        assert!(top.contains(n));
    }
}

#[test]
fn disjoint_meet_is_bottom() {
    let a = IntervalZ::constant(1);
    let b = IntervalZ::constant(2);
    let m = a.meet(&b);
    assert!(m.empty, "§3.1: disjoint meet must be bottom, not top");
}

#[test]
fn meet_is_intersection_and_join_is_hull() {
    let a = IntervalZ::range(fin(-3), fin(5));
    let b = IntervalZ::range(fin(0), fin(10));
    let m = a.meet(&b);
    assert!(!m.empty);
    assert_eq!(m.lo, fin(0));
    assert_eq!(m.hi, fin(5));
    for n in -5..=12i64 {
        assert_eq!(m.contains(n), a.contains(n) && b.contains(n));
    }
    let j = a.join(&b);
    assert_eq!(j.lo, fin(-3));
    assert_eq!(j.hi, fin(10));
    for n in -5..=12i64 {
        if a.contains(n) || b.contains(n) {
            assert!(j.contains(n));
        }
    }
}

#[test]
fn meet_join_lattice_laws() {
    let vals = [
        IntervalZ::bottom(),
        IntervalZ::top(),
        IntervalZ::constant(0),
        IntervalZ::range(fin(-4), fin(7)),
        IntervalZ::range(Bound::NegInf, fin(3)),
        IntervalZ::range(fin(-2), Bound::PosInf),
    ];
    for a in &vals {
        assert!(a.meet(a).empty == a.empty);
        if !a.empty {
            let m = a.meet(a);
            assert_eq!(&m.lo, &a.lo);
            assert_eq!(&m.hi, &a.hi);
        }
        let top = IntervalZ::top();
        let bot = IntervalZ::bottom();
        let mt = a.meet(&top);
        assert_eq!(mt.empty, a.empty);
        assert!(a.meet(&bot).empty);
        let jb = a.join(&bot);
        assert_eq!(jb.empty, a.empty);
        assert!(!a.join(&top).empty);
        assert_eq!(a.join(&top).lo, Bound::NegInf);
        assert_eq!(a.join(&top).hi, Bound::PosInf);
        for b in &vals {
            let ab = a.meet(b);
            let ba = b.meet(a);
            assert_eq!(ab.empty, ba.empty);
            if !ab.empty {
                assert_eq!(&ab.lo, &ba.lo);
                assert_eq!(&ab.hi, &ba.hi);
            }
            let jab = a.join(b);
            let jba = b.join(a);
            assert_eq!(jab.empty, jba.empty);
            if !jab.empty {
                assert_eq!(&jab.lo, &jba.lo);
                assert_eq!(&jab.hi, &jba.hi);
            }
            for c in &vals {
                let left = a.meet(b).meet(c);
                let right = a.meet(&b.meet(c));
                assert_eq!(left.empty, right.empty);
            }
        }
    }
}

#[test]
fn add_contains_every_concrete_sum() {
    let a = IntervalZ::range(fin(-2), fin(3));
    let b = IntervalZ::range(fin(4), fin(6));
    let s = a.add(&b);
    for x in -2..=3i64 {
        for y in 4..=6i64 {
            assert!(s.contains(x + y), "{x}+{y} not in add");
        }
    }
    assert_eq!(s.lo, fin(2));
    assert_eq!(s.hi, fin(9));
}

#[test]
fn add_empty_is_bottom() {
    let a = IntervalZ::constant(1);
    assert!(a.add(&IntervalZ::bottom()).empty);
    assert!(IntervalZ::bottom().add(&a).empty);
}

#[test]
fn neg_and_sub_contain() {
    let a = IntervalZ::range(fin(-2), fin(5));
    let n = a.neg();
    for x in -2..=5i64 {
        assert!(n.contains(-x));
    }
    assert_eq!(n.lo, fin(-5));
    assert_eq!(n.hi, fin(2));
    let b = IntervalZ::range(fin(1), fin(3));
    let d = a.sub(&b);
    for x in -2..=5i64 {
        for y in 1..=3i64 {
            assert!(d.contains(x - y));
        }
    }
}

#[test]
fn mul_zero_is_zero_otherwise_sound() {
    let z = IntervalZ::constant(0);
    let a = IntervalZ::range(fin(-4), fin(9));
    let p = a.mul(&z);
    assert!(p.contains(0));
    assert_eq!(p.lo, fin(0));
    assert_eq!(p.hi, fin(0));
    let b = IntervalZ::range(fin(2), fin(3));
    let q = a.mul(&b);
    assert_eq!(q.lo, fin(-12));
    assert_eq!(q.hi, fin(27));
    let pos = IntervalZ::range(fin(2), fin(3)).mul(&IntervalZ::range(fin(4), fin(5)));
    assert_eq!(pos.lo, fin(8));
    assert_eq!(pos.hi, fin(15));
    for x in -4..=9i64 {
        for y in 2..=3i64 {
            assert!(q.contains(x * y));
        }
    }
}

#[test]
fn alarm_join_is_concretization_not_severity() {
    assert_eq!(
        Alarm::NoError.join(Alarm::DefiniteError),
        Alarm::MaybeError,
        "joining a safe path with a definite error yields maybe, not definite"
    );
    assert_eq!(Alarm::DefiniteError.join(Alarm::NoError), Alarm::MaybeError);
    assert_eq!(Alarm::NoError.join(Alarm::NoError), Alarm::NoError);
    assert_eq!(
        Alarm::DefiniteError.join(Alarm::DefiniteError),
        Alarm::DefiniteError
    );
}

#[test]
fn div_alarms_and_nonzero_guard() {
    let num = IntervalZ::range(fin(2), fin(10));
    let (r, alarm) = num.div(&IntervalZ::constant(0));
    assert!(r.empty);
    assert_eq!(alarm, Alarm::DefiniteError);

    let maybe = IntervalZ::range(fin(0), fin(4));
    let (r2, alarm2) = num.div(&maybe);
    assert_eq!(alarm2, Alarm::MaybeError);
    assert_eq!(r2.lo, fin(0));
    assert_eq!(r2.hi, fin(10));

    let pos = IntervalZ::range(fin(1), fin(4));
    let (r3, alarm3) = num.div(&pos);
    assert_eq!(alarm3, Alarm::NoError);
    assert_eq!(r3.lo, fin(0));
    assert_eq!(r3.hi, fin(10));
    for x in 2..=10i64 {
        for y in 1..=4i64 {
            assert!(r3.contains(x / y));
        }
    }

    let negn = IntervalZ::range(fin(-8), fin(-1));
    let negd = IntervalZ::range(fin(-4), fin(-2));
    let (rn, an) = negn.div(&negd);
    assert_eq!(an, Alarm::NoError);
    assert_eq!(rn.lo, fin(1));
    assert_eq!(rn.hi, fin(4));
    for x in -8..=-1i64 {
        for y in -4..=-2i64 {
            assert!(rn.contains(x.div_euclid(y)), "{x}/{y}");
        }
    }

    assert!(pos.nonzero());
    assert!(!maybe.nonzero());
    assert!(!IntervalZ::bottom().nonzero(), "bottom must not license guards");
}

#[test]
fn within_guard_licenses_only_contained_ranges() {
    let a = IntervalZ::range(fin(3), fin(10));
    assert!(a.within(0, 255));
    assert!(a.within(3, 10));
    assert!(!a.within(4, 10));
    assert!(!a.within(3, 9));
    assert!(!IntervalZ::bottom().within(0, 255));
    assert!(!IntervalZ::top().within(0, 255));
}

#[test]
fn widen_goes_to_infinity_narrow_recovers() {
    let a = IntervalZ::range(fin(0), fin(5));
    let b = IntervalZ::range(fin(-2), fin(8));
    let w = a.widen(&b);
    assert_eq!(w.lo, Bound::NegInf);
    assert_eq!(w.hi, Bound::PosInf);
    let n = w.narrow(&a);
    assert_eq!(n.lo, fin(0));
    assert_eq!(n.hi, fin(5));
}

#[test]
fn refinement_budget_stops_or_meets() {
    let cur = IntervalZ::range(fin(0), Bound::PosInf);
    let fact = IntervalZ::range(fin(1), Bound::PosInf);
    let (stopped, rem0) = cur.refine(&fact, 0);
    assert_eq!(rem0, 0);
    assert_eq!(stopped.lo, fin(0));
    let (tighter, rem) = cur.refine(&fact, 3);
    assert_eq!(tighter.lo, fin(1));
    assert_eq!(rem, 2);
    let (bot, _) = tighter.refine(&IntervalZ::range(fin(-5), fin(-1)), 1);
    assert!(bot.empty);
}

#[test]
fn refinement_fuel_exhausts_on_strict_meets() {
    let v = IntervalZ::range(fin(0), Bound::PosInf);
    let fuel = 2u8;
    let (v1, f1) = v.refine(&IntervalZ::range(fin(1), Bound::PosInf), fuel);
    assert_eq!(f1, 1);
    assert_eq!(v1.lo, fin(1));
    let (v2, f2) = v1.refine(&IntervalZ::range(fin(2), Bound::PosInf), f1);
    assert_eq!(f2, 0);
    assert_eq!(v2.lo, fin(2));
    let (v3, f3) = v2.refine(&IntervalZ::range(fin(3), Bound::PosInf), f2);
    assert_eq!(f3, 0);
    assert_eq!(v3.lo, fin(2), "zero fuel must keep the current value");
}

#[test]
fn nonneg_guard_allows_unbounded_hi() {
    let a = IntervalZ::range(fin(0), Bound::PosInf);
    assert!(a.nonneg());
    assert!(!a.fits_u8());
    assert!(IntervalZ::range(fin(3), fin(10)).fits_u8());
    assert!(!IntervalZ::range(fin(-1), fin(5)).nonneg());
    assert!(!IntervalZ::bottom().nonneg());
}

#[test]
fn infinities_add() {
    let a = IntervalZ::range(Bound::NegInf, fin(3));
    let b = IntervalZ::constant(1);
    let s = a.add(&b);
    assert_eq!(s.lo, Bound::NegInf);
    assert_eq!(s.hi, fin(4));
}

#[test]
fn unbounded_mul_and_div_use_endpoint_rules() {
    let ray = IntervalZ::range(fin(1), Bound::PosInf);
    let span = IntervalZ::range(fin(2), fin(3));
    let p = ray.mul(&span);
    assert_eq!(p.lo, fin(2));
    assert_eq!(p.hi, Bound::PosInf);
    let neg = IntervalZ::range(Bound::NegInf, fin(-1)).mul(&span);
    assert_eq!(neg.lo, Bound::NegInf);
    assert_eq!(neg.hi, fin(-2));
    let q = IntervalZ::range(fin(2), fin(10)).div(&ray);
    assert_eq!(q.1, Alarm::NoError);
    assert_eq!(q.0.lo, fin(0));
    assert_eq!(q.0.hi, fin(10));
}

#[test]
fn finite_add_past_i64_stays_finite() {
    let s = IntervalZ::constant(i64::MAX).add(&IntervalZ::constant(1));
    let expect = IBig::from_i64(i64::MAX).add(&IBig::from_i64(1));
    match (&s.lo, &s.hi) {
        (Bound::Fin(lo), Bound::Fin(hi)) => {
            assert_eq!(lo, &expect);
            assert_eq!(hi, &expect);
        }
        other => panic!("endpoint left the finite integers: {other:?}"),
    }
    let n = IntervalZ::constant(i64::MIN).neg();
    match &n.lo {
        Bound::Fin(v) => assert_eq!(v, &IBig::from_i64(i64::MIN).neg()),
        other => panic!("negation overflowed: {other:?}"),
    }
}

#[test]
fn ibig_div_euclid_matches_i64() {
    for x in -30i64..=30 {
        for y in -12i64..=12 {
            if y == 0 || (x == i64::MIN && y == -1) {
                continue;
            }
            let q = IBig::from_i64(x).div_euclid(&IBig::from_i64(y));
            assert_eq!(q, IBig::from_i64(x.div_euclid(y)), "{x}/{y}");
        }
    }
}

#[test]
fn stable_meet_does_not_spend_fuel() {
    let a = IntervalZ::constant(3);
    let (r, fuel) = a.refine(&IntervalZ::top(), 4);
    assert_eq!(fuel, 4);
    assert_eq!(r.lo, fin(3));
    assert_eq!(r.hi, fin(3));
}

#[test]
fn ubig_requires_nonnegative_lower_bound() {
    assert!(IntervalZ::range(fin(0), Bound::PosInf).check_ubig());
    assert!(IntervalZ::bottom().check_ubig());
    assert!(!IntervalZ::range(fin(-1), fin(5)).check_ubig());
    assert!(!IntervalZ::range(Bound::NegInf, fin(4)).check_ubig());
}

#[test]
fn rbig_open_endpoint_excludes_the_integer() {
    let open_lo = IntervalR::new(fin(0), false, fin(5), true);
    assert!(!open_lo.contains_int(0));
    assert!(open_lo.contains_int(1));
    assert!(open_lo.contains_int(5));
    let open_hi = IntervalR::new(fin(0), true, fin(5), false);
    assert!(open_hi.contains_int(0));
    assert!(!open_hi.contains_int(5));
    let m = open_lo.meet(&open_hi);
    assert!(!m.contains_int(0));
    assert!(m.contains_int(1));
    assert!(!m.contains_int(5));
}
