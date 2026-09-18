// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Executable checks for kata 3/4 that sit next to the Verus contracts.

use semi_persistent_abstract_domains::domains::d8::Interval as ProdInterval;
use semi_persistent_abstract_domains::kata::{Interval, IntervalBot};

#[test]
fn add_contains_wrapping_sums() {
    let a = Interval { lo: 10, hi: 12 };
    let b = Interval { lo: 1, hi: 2 };
    let s = a.add(&b);
    assert_eq!((s.lo, s.hi), (11, 14));
    for x in 10..=12u8 {
        for y in 1..=2u8 {
            assert!(s.contains(x.wrapping_add(y)));
        }
    }
}

#[test]
fn add_overflow_returns_top() {
    let a = Interval { lo: 200, hi: 200 };
    let b = Interval { lo: 100, hi: 100 };
    let s = a.add(&b);
    assert_eq!(s, Interval::top());
    assert!(s.contains(200u8.wrapping_add(100)));
}

#[test]
fn without_bottom_disjoint_meet_is_top_and_not_associative() {
    let a = Interval { lo: 1, hi: 1 };
    let b = Interval { lo: 2, hi: 2 };
    assert_eq!(a.meet(&b), Interval::top());

    let prod = ProdInterval { lo: 1, hi: 1 }.meet(&ProdInterval { lo: 2, hi: 2 });
    assert_eq!(
        (prod.lo, prod.hi),
        (0, 255),
        "domains.rs agrees: disjoint meet is top"
    );

    let left = a.meet(&b).meet(&b);
    let right = a.meet(&b.meet(&b));
    assert_eq!(left, b);
    assert_eq!(right, Interval::top());
    assert_ne!(left, right, "no-bottom meet is not associative");
}

#[test]
fn with_bottom_disjoint_meet_is_bottom_and_associative() {
    let a = IntervalBot::range(1, 1);
    let b = IntervalBot::range(2, 2);
    assert!(a.meet(&b).empty);
    let left = a.meet(&b).meet(&b);
    let right = a.meet(&b.meet(&b));
    assert!(left.empty && right.empty);
}
