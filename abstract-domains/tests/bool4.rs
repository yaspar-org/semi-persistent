// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Executable checks for the four-point boolean: lattice laws and containment.

use semi_persistent_abstract_domains::bool4::Bool4;

fn all() -> [Bool4; 4] {
    [Bool4::Bottom, Bool4::False, Bool4::True, Bool4::Top]
}

#[test]
fn canonical_constructors_have_expected_values() {
    assert_eq!(Bool4::bottom(), Bool4::Bottom);
    assert_eq!(Bool4::top(), Bool4::Top);
    assert_eq!(Bool4::constant(false), Bool4::False);
    assert_eq!(Bool4::constant(true), Bool4::True);

    assert!(!Bool4::bottom().contains(false));
    assert!(!Bool4::bottom().contains(true));
    assert!(Bool4::top().contains(false));
    assert!(Bool4::top().contains(true));
    assert!(Bool4::constant(false).contains(false));
    assert!(!Bool4::constant(false).contains(true));
    assert!(Bool4::constant(true).contains(true));
    assert!(!Bool4::constant(true).contains(false));
}

#[test]
fn meet_of_unknown_and_true_is_true() {
    assert_eq!(Bool4::Top.meet(Bool4::True), Bool4::True);
    assert_eq!(Bool4::True.meet(Bool4::False), Bool4::Bottom);
    assert_eq!(Bool4::True.join(Bool4::False), Bool4::Top);
}

#[test]
fn lattice_laws_hold_on_all_four_points() {
    for a in all() {
        assert_eq!(a.join(a), a);
        assert_eq!(a.meet(a), a);
        assert_eq!(a.join(Bool4::Bottom), a);
        assert_eq!(a.join(Bool4::Top), Bool4::Top);
        assert_eq!(a.meet(Bool4::Top), a);
        assert_eq!(a.meet(Bool4::Bottom), Bool4::Bottom);
        for b in all() {
            assert_eq!(a.join(b), b.join(a));
            assert_eq!(a.meet(b), b.meet(a));
            for c in all() {
                assert_eq!(a.join(b).join(c), a.join(b.join(c)));
                assert_eq!(a.meet(b).meet(c), a.meet(b.meet(c)));
            }
        }
    }
}

#[test]
fn boolean_ops_contain_every_concrete_result() {
    let bits = [false, true];
    for a in all() {
        for b in all() {
            let and = a.and(b);
            let or = a.or(b);
            for x in bits {
                if !a.contains(x) {
                    continue;
                }
                assert!(a.not().contains(!x));
                for y in bits {
                    if !b.contains(y) {
                        continue;
                    }
                    assert!(and.contains(x && y));
                    assert!(or.contains(x || y));
                }
            }
        }
    }
    assert_eq!(Bool4::False.and(Bool4::Top), Bool4::False);
    assert_eq!(Bool4::True.or(Bool4::Top), Bool4::True);
    assert_eq!(Bool4::Bottom.not(), Bool4::Bottom);
    assert!(!Bool4::Bottom.contains(false));
    assert!(!Bool4::Bottom.contains(true));
}

// Rows and columns follow `all()`: Bottom, False, True, Top.
const B: Bool4 = Bool4::Bottom;
const F: Bool4 = Bool4::False;
const T: Bool4 = Bool4::True;
const U: Bool4 = Bool4::Top;

fn check_table(name: &str, op: fn(Bool4, Bool4) -> Bool4, table: [[Bool4; 4]; 4]) {
    for (i, a) in all().into_iter().enumerate() {
        for (j, b) in all().into_iter().enumerate() {
            assert_eq!(op(a, b), table[i][j], "{name}({a:?}, {b:?})");
        }
    }
}

#[test]
fn operations_match_exact_truth_tables() {
    assert_eq!(all().map(Bool4::not), [B, T, F, U]);

    check_table(
        "and",
        Bool4::and,
        [[B, B, B, B], [B, F, F, F], [B, F, T, U], [B, F, U, U]],
    );
    check_table(
        "or",
        Bool4::or,
        [[B, B, B, B], [B, F, T, U], [B, T, T, T], [B, U, T, U]],
    );
    check_table(
        "join",
        Bool4::join,
        [[B, F, T, U], [F, F, U, U], [T, U, T, U], [U, U, U, U]],
    );
    check_table(
        "meet",
        Bool4::meet,
        [[B, B, B, B], [B, F, B, F], [B, B, T, T], [B, F, T, U]],
    );
}

/// The abstraction of a set of concrete booleans.
fn alpha(has_false: bool, has_true: bool) -> Bool4 {
    match (has_false, has_true) {
        (false, false) => B,
        (true, false) => F,
        (false, true) => T,
        (true, true) => U,
    }
}

#[test]
fn not_and_or_are_the_best_abstractions() {
    let bits = [false, true];
    for a in all() {
        // not_hit[r]: some concrete x in a has !x == r.
        let mut not_hit = [false; 2];
        for x in bits {
            if a.contains(x) {
                not_hit[!x as usize] = true;
            }
        }
        assert_eq!(a.not(), alpha(not_hit[0], not_hit[1]), "not({a:?})");

        for b in all() {
            let mut and_hit = [false; 2];
            let mut or_hit = [false; 2];
            for x in bits {
                for y in bits {
                    if a.contains(x) && b.contains(y) {
                        and_hit[(x && y) as usize] = true;
                        or_hit[(x || y) as usize] = true;
                    }
                }
            }
            assert_eq!(a.and(b), alpha(and_hit[0], and_hit[1]), "and({a:?}, {b:?})");
            assert_eq!(a.or(b), alpha(or_hit[0], or_hit[1]), "or({a:?}, {b:?})");
        }
    }
}
