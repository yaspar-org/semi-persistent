// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Executable checks for the four-point boolean.
//!
//! The four points are `BotOr::Bot` plus `False`, `True`, and `Top`. A
//! `Bool4` value is never empty.

use semi_persistent_abstract_domains::bool4::Bool4;
use semi_persistent_abstract_domains::lattice::{BotOr, Domain};

fn values() -> [Bool4; 3] {
    [Bool4::False, Bool4::True, Bool4::Top]
}

fn has(b: &Bool4, x: bool) -> bool {
    match b {
        Bool4::False => !x,
        Bool4::True => x,
        Bool4::Top => true,
    }
}

fn same(a: &Bool4, b: &Bool4) -> bool {
    has(a, false) == has(b, false) && has(a, true) == has(b, true)
}

#[test]
fn meet_of_unknown_and_true_is_true() {
    match Bool4::Top.meet(&Bool4::True) {
        BotOr::Val(m) => assert!(same(&m, &Bool4::True)),
        BotOr::Bot => panic!("Top meet True is nonempty"),
    }
    assert!(matches!(Bool4::True.meet(&Bool4::False), BotOr::Bot));
    assert!(same(&Bool4::True.join(&Bool4::False), &Bool4::Top));
}

#[test]
fn every_value_contains_a_boolean() {
    for a in values() {
        assert!(has(&a, false) || has(&a, true));
    }
}

#[test]
fn join_and_meet_on_the_three_values() {
    for a in values() {
        assert!(same(&a.join(&a), &a));
        match a.meet(&a) {
            BotOr::Val(m) => assert!(same(&m, &a)),
            BotOr::Bot => panic!("meet of a value with itself is nonempty"),
        }
        assert!(same(&a.join(&Bool4::Top), &Bool4::Top));
        match a.meet(&Bool4::Top) {
            BotOr::Val(m) => assert!(same(&m, &a)),
            BotOr::Bot => panic!("meet with Top keeps the value"),
        }
        for b in values() {
            assert!(same(&a.join(&b), &b.join(&a)));
            let ab = a.meet(&b);
            let ba = b.meet(&a);
            match (ab, ba) {
                (BotOr::Bot, BotOr::Bot) => {},
                (BotOr::Val(x), BotOr::Val(y)) => assert!(same(&x, &y)),
                _ => panic!("meet is not commutative"),
            }
        }
    }
}

#[test]
fn connectives_match_the_concrete_image() {
    let bits = [false, true];
    for a in values() {
        let n = a.not();
        assert_eq!(has(&n, false), has(&a, true));
        assert_eq!(has(&n, true), has(&a, false));
        for b in values() {
            for (r, op) in [
                (a.and(&b), (|x, y| x && y) as fn(bool, bool) -> bool),
                (a.or(&b), |x, y| x || y),
                (a.eq(&b), |x, y| x == y),
            ] {
                let mut want = [false; 2];
                for x in bits {
                    for y in bits {
                        if has(&a, x) && has(&b, y) {
                            want[op(x, y) as usize] = true;
                        }
                    }
                }
                assert_eq!([has(&r, false), has(&r, true)], want);
            }
        }
    }
    assert!(same(&Bool4::False.and(&Bool4::Top), &Bool4::False));
    assert!(same(&Bool4::True.or(&Bool4::Top), &Bool4::True));
    assert!(same(&Bool4::True.eq(&Bool4::False), &Bool4::False));
    assert!(same(&Bool4::True.eq(&Bool4::True), &Bool4::True));
    assert!(same(&Bool4::Top.eq(&Bool4::True), &Bool4::Top));
}
