// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Executable checks for IntervalZ: lattice laws, containment, alarms,
//! widen/narrow, and the §4.5 refinement budget.

use semi_persistent_abstract_domains::interval_z::{Alarm, Bound, IntervalZ};

fn fin(n: i64) -> Bound {
    Bound::Fin(n)
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
    for a in vals {
        assert!(a.meet(&a).empty == a.empty);
        if !a.empty {
            let m = a.meet(&a);
            assert_eq!(m.lo, a.lo);
            assert_eq!(m.hi, a.hi);
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
        for b in vals {
            let ab = a.meet(&b);
            let ba = b.meet(&a);
            assert_eq!(ab.empty, ba.empty);
            if !ab.empty {
                assert_eq!(ab.lo, ba.lo);
                assert_eq!(ab.hi, ba.hi);
            }
            let jab = a.join(&b);
            let jba = b.join(&a);
            assert_eq!(jab.empty, jba.empty);
            if !jab.empty {
                assert_eq!(jab.lo, jba.lo);
                assert_eq!(jab.hi, jba.hi);
            }
            for c in vals {
                let left = a.meet(&b).meet(&c);
                let right = a.meet(&b.meet(&c));
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
    assert_eq!(p.lo, Bound::Fin(0));
    assert_eq!(p.hi, Bound::Fin(0));
    let b = IntervalZ::range(fin(2), fin(3));
    let q = a.mul(&b);
    for x in -4..=9i64 {
        for y in 2..=3i64 {
            assert!(q.contains(x * y) || q.lo == Bound::NegInf);
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
    let (_r2, alarm2) = num.div(&maybe);
    assert_eq!(alarm2, Alarm::MaybeError);

    let pos = IntervalZ::range(fin(1), fin(4));
    let (r3, alarm3) = num.div(&pos);
    assert_eq!(alarm3, Alarm::NoError);
    for x in 2..=10i64 {
        for y in 1..=4i64 {
            assert!(r3.contains(x / y) || r3.lo == Bound::NegInf);
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
    let stopped = cur.refine(&fact, 0);
    assert_eq!(stopped.lo, fin(0));
    let tighter = cur.refine(&fact, 3);
    assert_eq!(tighter.lo, fin(1));
    let bot = tighter.refine(&IntervalZ::range(fin(-5), fin(-1)), 1);
    assert!(bot.empty);
}

#[test]
fn infinities_add() {
    let a = IntervalZ::range(Bound::NegInf, fin(3));
    let b = IntervalZ::constant(1);
    let s = a.add(&b);
    assert_eq!(s.lo, Bound::NegInf);
    assert_eq!(s.hi, fin(4));
}
