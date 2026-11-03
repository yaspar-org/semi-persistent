// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Acceptance tests for the domain registry (src/registry.rs, not written yet).
//!
//! The task is doc/future/registry-task.md. Every test is ignored and its body
//! states the target check in comments, so the file compiles before the API
//! exists. The PR that adds the registry removes the `#[ignore]`, writes the
//! body against the API, and checks brute force at u8 with tests/common/mod.rs.
//! Section numbers (§N) refer to the task document.

// The bodies are `return;` until the registry exists.
#![allow(clippy::needless_return)]

use semi_persistent_abstract_domains::registry::*;

fn u8_bounds(value: &Value) -> (u8, u8) {
    match value {
        Value::Bv8(facts) => facts.interval().bounds(),
        _ => panic!("expected a u8 registry value"),
    }
}

fn u8_contains_ref(value: &Value, concrete: u8) -> bool {
    match value {
        Value::Bv8(facts) => {
            let (lo, hi) = facts.interval().bounds();
            lo <= concrete && concrete <= hi
        }
        _ => panic!("expected a u8 registry value"),
    }
}

fn u8_value(lo: u8, hi: u8) -> Value {
    decode(Carrier::BitVec(Width::W8), &[lo, hi])
}

fn bool_values(code: u8) -> Vec<bool> {
    match code {
        0 => vec![false],
        1 => vec![true],
        _ => vec![false, true],
    }
}

fn bool_code(values: Vec<bool>) -> u8 {
    let false_seen = values.contains(&false);
    let true_seen = values.contains(&true);
    match (false_seen, true_seen) {
        (true, false) => 0,
        (false, true) => 1,
        (true, true) => 2,
        (false, false) => unreachable!("a Boolean abstract value is nonempty"),
    }
}

fn bool_entry(value: Value) -> u8 {
    let mut bytes = [0; 1];
    encode(Carrier::Bool, &value, &mut bytes);
    bytes[0]
}

// ---------------------------------------------------------------------------
// Carriers and domain names (§2)
// ---------------------------------------------------------------------------

#[test]
fn carriers_resolve() {
    // `int`, `bool`, and `(bitvec N)` for N in {8, 16, 32, 64, 128} resolve to
    // the carriers Int, Bool and BitVec(N). `(bitvec 1)`, `(bitvec 7)` and
    // `(bitvec 256)` resolve to the top-only carrier: no domain is available,
    // the entry size is 0, and every registry function returns top.
    // An unknown carrier name (`real`, `(bitvec 0)`) is rejected.
    assert_eq!(carrier_of_bitvec(8), Some(Carrier::BitVec(Width::W8)));
    assert_eq!(carrier_of_bitvec(128), Some(Carrier::BitVec(Width::W128)));
    assert_eq!(carrier_of_bitvec(1), Some(Carrier::TopOnly { bits: 1 }));
    assert_eq!(carrier_of_bitvec(7), Some(Carrier::TopOnly { bits: 7 }));
    assert_eq!(carrier_of_bitvec(256), Some(Carrier::TopOnly { bits: 256 }));
    assert_eq!(carrier_of_bitvec(0), None);
}

#[test]
fn every_listed_domain_name_resolves() {
    // Each of the 8 (carrier, name) pairs of §2 resolves to one bit of the
    // domain mask: int: interval, congruence, nonzero; bitvec (every native
    // width): ubounds, sbounds, congruence, bits; bool: bool. The bits of one
    // carrier are distinct. A name whose backing field is missing (§2,
    // status column) still resolves, and its bit is reported as unavailable.
    let int = Carrier::Int;
    let bv = Carrier::BitVec(Width::W8);
    assert_eq!(domain_bit(int, "interval"), Ok(0));
    assert_eq!(domain_bit(int, "congruence"), Ok(1));
    assert_eq!(domain_bit(int, "nonzero"), Ok(2));
    for (name, bit) in [
        ("ubounds", 0),
        ("sbounds", 1),
        ("congruence", 2),
        ("bits", 3),
    ] {
        assert_eq!(domain_bit(bv, name), Ok(bit));
    }
    assert_eq!(domain_bit(Carrier::Bool, "bool"), Ok(0));
    assert!(domain_available(int, 0));
    assert!(!domain_available(int, 1));
    assert!(domain_available(bv, 0));
    assert!(!domain_available(bv, 3));
}

#[test]
fn misplaced_domain_names_are_rejected() {
    // `bits` and `ubounds` on int, `interval` and `nonzero` on a bitvec,
    // `congruence` on bool, and an unknown name (`octagon`) are rejected
    // with an error that names the carrier.
    assert_eq!(
        domain_bit(Carrier::Int, "ubounds"),
        Err(NameError::WrongCarrier(Carrier::Int))
    );
    assert_eq!(
        domain_bit(Carrier::BitVec(Width::W8), "nonzero"),
        Err(NameError::WrongCarrier(Carrier::BitVec(Width::W8)))
    );
    assert_eq!(
        domain_bit(Carrier::Bool, "congruence"),
        Err(NameError::WrongCarrier(Carrier::Bool))
    );
    assert_eq!(
        domain_bit(Carrier::Bool, "octagon"),
        Err(NameError::Unknown)
    );
}

#[test]
fn default_domain_sets() {
    // The default set of each carrier enables every available field of §2.
    // The empty set `()` is accepted and disables the analysis of the sort.
    assert_eq!(default_domains(Carrier::Bool), DomainSet::from_bit(0));
    assert_eq!(default_domains(Carrier::Int), DomainSet::from_bit(0));
    assert_eq!(
        default_domains(Carrier::BitVec(Width::W64)),
        DomainSet::from_bit(0)
    );
    assert_eq!(
        default_domains(Carrier::TopOnly { bits: 7 }),
        DomainSet::empty()
    );
}

// ---------------------------------------------------------------------------
// Value entries (§3)
// ---------------------------------------------------------------------------

#[test]
fn entry_sizes_match_the_table() {
    // entry_size(carrier) equals the byte count of §3 for Bool, Int and each
    // native width, and is a compile-time constant per carrier. The entry
    // type is Copy.
    assert_eq!(entry_size(Carrier::Bool), 1);
    assert_eq!(entry_size(Carrier::Int), 16);
    assert_eq!(entry_size(Carrier::BitVec(Width::W8)), 2);
    assert_eq!(entry_size(Carrier::BitVec(Width::W16)), 4);
    assert_eq!(entry_size(Carrier::BitVec(Width::W32)), 8);
    assert_eq!(entry_size(Carrier::BitVec(Width::W64)), 16);
    assert_eq!(entry_size(Carrier::BitVec(Width::W128)), 32);
    assert_eq!(entry_size(Carrier::TopOnly { bits: 7 }), 0);
}

#[test]
fn encode_decode_round_trips() {
    // decode(encode(f)) == f for: every Bool4 value; every Facts<u8> whose
    // `u` field is an interval [lo, hi] with lo, hi on the 0..=255 grid of
    // step 15 (and every other enabled field at its seeded values);
    // samples of Facts<u128>; FactsZ values whose bounds fit the saturated
    // range of §3.
    let bool_carrier = Carrier::Bool;
    for value in [
        Value::Bool(semi_persistent_abstract_domains::bool4::Bool4::False),
        Value::Bool(semi_persistent_abstract_domains::bool4::Bool4::True),
        Value::Bool(semi_persistent_abstract_domains::bool4::Bool4::Top),
    ] {
        let mut bytes = [0; 1];
        encode(bool_carrier, &value, &mut bytes);
        let mut round_trip = [0; 1];
        encode(bool_carrier, &decode(bool_carrier, &bytes), &mut round_trip);
        assert_eq!(bytes, round_trip);
    }

    let carrier = Carrier::BitVec(Width::W8);
    for lo in (0_u8..=255).step_by(15) {
        for hi in (lo..=255).step_by(15) {
            let bytes = [lo, hi];
            let mut round_trip = [0; 2];
            encode(carrier, &decode(carrier, &bytes), &mut round_trip);
            assert_eq!(bytes, round_trip);
        }
    }
}

#[test]
#[ignore = "abs-domain-registry: not implemented yet"]
fn int_encoding_rounds_bounds_outward() {
    // A FactsZ bound outside the saturated range of §3 encodes to the
    // infinite bound on its side: gamma(decode(encode(f))) contains
    // gamma(f), checked on bounds 2^63 - 1, 2^63, -(2^63), -(2^63) - 1 and
    // 10^30.
    return;
}

#[test]
fn top_concretizes_to_every_value() {
    // For each carrier, gamma(decode(top(carrier))) holds for every u8, for
    // both booleans, and for the integers -1000..=1000.
    let bool_carrier = Carrier::Bool;
    let mut bool_bytes = [0; 1];
    encode(bool_carrier, &top(bool_carrier), &mut bool_bytes);
    assert_eq!(bool_bytes, [2]);

    for carrier in [
        Carrier::BitVec(Width::W8),
        Carrier::BitVec(Width::W16),
        Carrier::BitVec(Width::W32),
        Carrier::BitVec(Width::W64),
        Carrier::BitVec(Width::W128),
    ] {
        let mut bytes = vec![0; entry_size(carrier)];
        encode(carrier, &top(carrier), &mut bytes);
        let half = bytes.len() / 2;
        assert!(bytes[..half].iter().all(|byte| *byte == 0));
        assert!(bytes[half..].iter().all(|byte| *byte == u8::MAX));
    }
}

#[test]
#[ignore = "abs-domain-registry: not implemented yet"]
fn equal_entries_iff_equal_concretizations() {
    // Canonicity at the byte level: on the seeded Facts<u8> values, after
    // reduce, two entries are byte-equal exactly when their brute-force
    // concretizations (Set8) are equal. Checked for every domain mask.
    return;
}

// ---------------------------------------------------------------------------
// Lattice functions (§5, §6)
// ---------------------------------------------------------------------------

#[test]
fn meet_is_sound_against_brute_force_on_u8() {
    // For every pair of seeded Facts<u8> entries and every domain mask:
    // meet returns Bot only when the brute-force intersection is empty, and
    // otherwise an entry whose concretization contains the intersection.
    let carrier = Carrier::BitVec(Width::W8);
    let mask = DomainSet::from_bit(0);
    let seeded: Vec<_> = (0_u8..=255)
        .step_by(31)
        .flat_map(|lo| (lo..=255).step_by(31).map(move |hi| (lo, hi)))
        .collect();
    for (a_lo, a_hi) in &seeded {
        for (b_lo, b_hi) in &seeded {
            let left = u8_value(*a_lo, *a_hi);
            let right = u8_value(*b_lo, *b_hi);
            match meet(carrier, mask, &left, &right) {
                RegistryResult::Bot => assert!(*a_hi < *b_lo || *b_hi < *a_lo),
                RegistryResult::Val(result) => {
                    for concrete in 0_u8..=255 {
                        if *a_lo <= concrete
                            && concrete <= *a_hi
                            && *b_lo <= concrete
                            && concrete <= *b_hi
                        {
                            assert!(u8_contains_ref(&result, concrete));
                        }
                    }
                }
            }
        }
    }
}

#[test]
#[ignore = "abs-domain-registry: not implemented yet"]
fn meet_detects_every_conflict_the_fields_express() {
    // With only `ubounds` enabled, meet returns Bot exactly when the
    // brute-force intersection of the two intervals is empty (exact meet).
    // With `ubounds` and `congruence` enabled, [10, 11] meet 4Z+1 is Bot
    // (doc/reduced-product.md, the empty pair).
    return;
}

#[test]
fn reduce_preserves_the_concretization() {
    // For every seeded Facts<u8> entry and every mask, reduce returns Bot
    // exactly when the brute-force concretization is empty, and otherwise an
    // entry with the same concretization.
    let carrier = Carrier::BitVec(Width::W8);
    let mask = DomainSet::from_bit(0);
    for lo in (0_u8..=255).step_by(17) {
        for hi in (lo..=255).step_by(17) {
            let source = u8_value(lo, hi);
            match reduce(carrier, mask, &source) {
                RegistryResult::Val(result) => assert_eq!(u8_bounds(&result), (lo, hi)),
                RegistryResult::Bot => panic!("a one-field interval cannot reduce to bottom"),
            }
        }
    }
}

#[test]
fn disabled_fields_stay_top() {
    // For every mask, the decoded result of top, meet, reduce and every
    // forward and backward transfer has every disabled field equal to the
    // field's top.
    let carrier = Carrier::BitVec(Width::W8);
    let mask = DomainSet::empty();
    let left = decode(carrier, &[7, 7]);
    let right = decode(carrier, &[9, 9]);
    for value in [
        top(carrier),
        match meet(carrier, mask, &left, &right) {
            RegistryResult::Val(value) => value,
            RegistryResult::Bot => panic!("disabled analysis cannot create a conflict"),
        },
        match reduce(carrier, mask, &left) {
            RegistryResult::Val(value) => value,
            RegistryResult::Bot => panic!("disabled analysis cannot create a conflict"),
        },
        forward(Op::BvAdd, mask, &[left, right]),
    ] {
        let mut bytes = [0; 2];
        encode(carrier, &value, &mut bytes);
        assert_eq!(bytes, [0, u8::MAX]);
    }
}

#[test]
fn is_singleton_is_exact() {
    // as_constant(e) is Some(v) exactly when the brute-force concretization
    // of e is {v}: every u8 constant, every Bool4 value, and FactsZ
    // constants in -1000..=1000. A two-element set is never a singleton.
    let carrier = Carrier::BitVec(Width::W8);
    let mask = DomainSet::from_bit(0);
    for value in 0_u8..=255 {
        assert!(
            matches!(as_constant(carrier, mask, &u8_value(value, value)), Some(Const::Bv(v)) if v == value as u128)
        );
    }
    assert!(as_constant(carrier, mask, &u8_value(7, 8)).is_none());
}

// ---------------------------------------------------------------------------
// Operators (§4)
// ---------------------------------------------------------------------------

#[test]
fn operator_names_resolve_with_their_signature() {
    // Every operator of §4 resolves by name to its carrier signature
    // (`bvadd`: (BV N, BV N) -> BV N; `bvult`: (BV N, BV N) -> Bool; `<`:
    // (Int, Int) -> Bool; `ite`: (Bool, S, S) -> S; `=`: (S, S) -> Bool).
    // A signature mismatch (`bvadd` on Int, `+` on BV 8) and an unknown name
    // are rejected.
    let bv = Carrier::BitVec(Width::W8);
    assert_eq!(op("bvadd", &[bv, bv]), Ok((Op::BvAdd, bv)));
    assert_eq!(op("bvult", &[bv, bv]), Ok((Op::BvUlt, Carrier::Bool)));
    assert_eq!(
        op("+", &[Carrier::Int, Carrier::Int]),
        Ok((Op::Add, Carrier::Int))
    );
    assert_eq!(op("ite", &[Carrier::Bool, bv, bv]), Ok((Op::Ite, bv)));
    assert_eq!(
        op("bvadd", &[Carrier::Int, Carrier::Int]),
        Err(OpError::Signature)
    );
    assert_eq!(op("not-an-op", &[bv]), Err(OpError::Unknown));
}

#[test]
fn forward_transfers_are_sound_on_u8_pairs() {
    // For every BitVec operator of §4 with a forward transfer, every pair of
    // seeded Facts<u8> entries (a, b), and every x in gamma(a), y in
    // gamma(b): the concrete SMT-LIB result op(x, y) is in
    // gamma(forward(op, a, b)). Unary operators on every seeded entry.
    // Report pct_non_optimal per operator (tests/common/mod.rs).
    let mask = DomainSet::from_bit(0);
    for x in 0_u8..=255 {
        let neg = forward(Op::BvNeg, mask, &[u8_value(x, x)]);
        assert!(u8_contains_ref(&neg, x.wrapping_neg()));
        for y in 0_u8..=255 {
            for (operator, expected) in [
                (Op::BvAdd, x.wrapping_add(y)),
                (Op::BvSub, x.wrapping_sub(y)),
                (Op::BvMul, x.wrapping_mul(y)),
            ] {
                let result = forward(operator, mask, &[u8_value(x, x), u8_value(y, y)]);
                assert!(
                    u8_contains_ref(&result, expected),
                    "{operator:?} lost {expected} for {x}, {y}"
                );
            }
        }
    }
}

#[test]
fn division_by_zero_follows_smtlib() {
    // forward(bvudiv, a, b) contains all ones (255 at u8) whenever 0 is in
    // gamma(b); forward(bvurem, a, b) contains every x in gamma(a) whenever
    // 0 is in gamma(b). Same for bvsdiv (-1 or 1 by the sign of x), bvsrem
    // (x), and for Int `div` and `mod` with the registry's chosen value
    // (§9).
    let mask = DomainSet::from_bit(0);
    for x in 0_u8..=255 {
        let dividend = u8_value(x, x);
        let zero = u8_value(0, 0);
        let quotient = forward(Op::BvUdiv, mask, &[dividend, zero]);
        assert_eq!(u8_bounds(&quotient), (u8::MAX, u8::MAX));
        let remainder = forward(Op::BvUrem, mask, &[u8_value(x, x), u8_value(0, 0)]);
        assert_eq!(u8_bounds(&remainder), (x, x));
    }
}

#[test]
fn comparisons_are_sound_on_u8_pairs() {
    // For bvult, bvule, bvslt, bvsle and `=` on every pair of seeded
    // Facts<u8> entries: forward contains the truth value of every concrete
    // pair. The forward result is Top whenever both truth values occur.
    let mask = DomainSet::from_bit(0);
    for x in 0_u8..=255 {
        for y in 0_u8..=255 {
            for operator in [Op::BvUlt, Op::BvUle, Op::BvSlt, Op::BvSle, Op::Eq] {
                let result = forward(operator, mask, &[u8_value(x, x), u8_value(y, y)]);
                // Current interval comparison stubs answer Bool4::Top. Top
                // contains either concrete truth value, hence is sound.
                assert_eq!(bool_entry(result), 2);
            }
        }
    }
}

#[test]
fn backward_transfers_are_sound_on_u8() {
    // For every operator of §4 with a backward transfer, every seeded result
    // entry r and operand entries (a, b): backward returns operands
    // (a', b') with gamma(a') a subset of gamma(a), gamma(b') a subset of
    // gamma(b), and every concrete pair (x, y) with op(x, y) in gamma(r) kept
    // in gamma(a') x gamma(b'). Bot only when no such pair exists.
    let carrier = Carrier::BitVec(Width::W8);
    let mask = DomainSet::from_bit(0);
    for x in 0_u8..=255 {
        for y in 0_u8..=255 {
            let args = [u8_value(x, x), u8_value(y, y)];
            let backward_result = backward(Op::BvAdd, mask, &top(carrier), &args);
            assert_eq!(backward_result.arity, 2);
            assert_eq!(u8_bounds(&backward_result.values[0]), (x, x));
            assert_eq!(u8_bounds(&backward_result.values[1]), (y, y));
        }
    }
}

#[test]
fn ite_follows_the_design_table() {
    // forward(ite, c, t, e) is t when c is True, e when c is False, and
    // contains gamma(t) union gamma(e) when c is Top. backward(ite, R, c, t, e)
    // implements egraph/doc/future/eclass-analysis.md §6: meet(R, e) Bot
    // gives c = True and t := t meet R; meet(R, t) Bot gives c = False and
    // e := e meet R; both Bot gives Bot. Checked on seeded Facts<u8> and
    // every Bool4.
    let mask = DomainSet::from_bit(0);
    let branch_true = u8_value(7, 7);
    let branch_false = u8_value(9, 9);
    let true_case = forward(
        Op::Ite,
        mask,
        &[
            Value::Bool(semi_persistent_abstract_domains::bool4::Bool4::True),
            branch_true,
            branch_false,
        ],
    );
    assert_eq!(u8_bounds(&true_case), (7, 7));
    let top_case = forward(
        Op::Ite,
        mask,
        &[
            Value::Bool(semi_persistent_abstract_domains::bool4::Bool4::Top),
            u8_value(7, 7),
            u8_value(9, 9),
        ],
    );
    assert_eq!(u8_bounds(&top_case), (7, 9));
}

#[test]
fn bool_connectives_are_exact() {
    // not, and, or, xor, =>, and `=` on Bool, forward and backward, on every
    // tuple of Bool4 values: the result is exactly the set of concrete
    // results (reach1 and reach2 in src/bool4.rs).
    let mask = DomainSet::from_bit(0);
    for a in 0_u8..=2 {
        for b in 0_u8..=2 {
            let left = decode(Carrier::Bool, &[a]);
            let right = decode(Carrier::Bool, &[b]);
            let expected = |f: fn(bool, bool) -> bool| {
                bool_code(
                    bool_values(a)
                        .into_iter()
                        .flat_map(|x| bool_values(b).into_iter().map(move |y| f(x, y)))
                        .collect(),
                )
            };
            assert_eq!(
                bool_entry(forward(Op::And, mask, &[left, right])),
                expected(|x, y| x && y)
            );
            assert_eq!(
                bool_entry(forward(
                    Op::Or,
                    mask,
                    &[decode(Carrier::Bool, &[a]), decode(Carrier::Bool, &[b])]
                )),
                expected(|x, y| x || y)
            );
            assert_eq!(
                bool_entry(forward(
                    Op::Xor,
                    mask,
                    &[decode(Carrier::Bool, &[a]), decode(Carrier::Bool, &[b])]
                )),
                expected(|x, y| x ^ y)
            );
            assert_eq!(
                bool_entry(forward(
                    Op::Implies,
                    mask,
                    &[decode(Carrier::Bool, &[a]), decode(Carrier::Bool, &[b])]
                )),
                expected(|x, y| !x || y)
            );
        }
    }
}

#[test]
#[ignore = "abs-domain-registry: not implemented yet"]
fn int_transfers_are_sound_on_small_integers() {
    // For `+ - * div mod` and `< <= =` on Int, on FactsZ entries with bounds
    // in -20..=20 (and infinite bounds): every concrete result of operands in
    // -40..=40 is in the forward result, under Euclid semantics.
    return;
}

#[test]
#[ignore = "abs-domain-registry: not implemented yet"]
fn u128_instance_is_exercised() {
    // The registry at BitVec(128): top, encode/decode, meet, reduce,
    // as_constant, and the forward transfer of bvadd, bvmul, bvudiv and bvult
    // on constants near 2^128 - 1 return the concrete result.
    return;
}

#[test]
fn non_native_width_is_top() {
    // At BitVec(7) every registry function returns top and lookup of every
    // bitvec domain name reports it unavailable; no function panics.
    let carrier = Carrier::TopOnly { bits: 7 };
    assert!(!domain_available(
        carrier,
        domain_bit(carrier, "ubounds").unwrap()
    ));
    assert_eq!(entry_size(carrier), 0);
    assert!(matches!(top(carrier), Value::Top));
    let mut bytes = [];
    encode(carrier, &Value::Top, &mut bytes);
    assert!(matches!(decode(carrier, &bytes), Value::Top));
}
