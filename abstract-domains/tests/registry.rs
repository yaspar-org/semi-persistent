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

// ---------------------------------------------------------------------------
// Carriers and domain names (§2)
// ---------------------------------------------------------------------------

#[test]
#[ignore = "abs-domain-registry: not implemented yet"]
fn carriers_resolve() {
    // `int`, `bool`, and `(bitvec N)` for N in {8, 16, 32, 64, 128} resolve to
    // the carriers Int, Bool and BitVec(N). `(bitvec 1)`, `(bitvec 7)` and
    // `(bitvec 256)` resolve to the top-only carrier: no domain is available,
    // the entry size is 0, and every registry function returns top.
    // An unknown carrier name (`real`, `(bitvec 0)`) is rejected.
    return;
}

#[test]
#[ignore = "abs-domain-registry: not implemented yet"]
fn every_listed_domain_name_resolves() {
    // Each of the 8 (carrier, name) pairs of §2 resolves to one bit of the
    // domain mask: int: interval, congruence, nonzero; bitvec (every native
    // width): ubounds, sbounds, congruence, bits; bool: bool. The bits of one
    // carrier are distinct. A name whose backing field is missing (§2,
    // status column) still resolves, and its bit is reported as unavailable.
    return;
}

#[test]
#[ignore = "abs-domain-registry: not implemented yet"]
fn misplaced_domain_names_are_rejected() {
    // `bits` and `ubounds` on int, `interval` and `nonzero` on a bitvec,
    // `congruence` on bool, and an unknown name (`octagon`) are rejected
    // with an error that names the carrier.
    return;
}

#[test]
#[ignore = "abs-domain-registry: not implemented yet"]
fn default_domain_sets() {
    // The default set of each carrier enables every available field of §2.
    // The empty set `()` is accepted and disables the analysis of the sort.
    return;
}

// ---------------------------------------------------------------------------
// Value entries (§3)
// ---------------------------------------------------------------------------

#[test]
#[ignore = "abs-domain-registry: not implemented yet"]
fn entry_sizes_match_the_table() {
    // entry_size(carrier) equals the byte count of §3 for Bool, Int and each
    // native width, and is a compile-time constant per carrier. The entry
    // type is Copy.
    return;
}

#[test]
#[ignore = "abs-domain-registry: not implemented yet"]
fn encode_decode_round_trips() {
    // decode(encode(f)) == f for: every Bool4 value; every Facts<u8> whose
    // `u` field is an interval [lo, hi] with lo, hi on the 0..=255 grid of
    // step 15 (and every other enabled field at its seeded values);
    // samples of Facts<u128>; FactsZ values whose bounds fit the saturated
    // range of §3.
    return;
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
#[ignore = "abs-domain-registry: not implemented yet"]
fn top_concretizes_to_every_value() {
    // For each carrier, gamma(decode(top(carrier))) holds for every u8, for
    // both booleans, and for the integers -1000..=1000.
    return;
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
#[ignore = "abs-domain-registry: not implemented yet"]
fn meet_is_sound_against_brute_force_on_u8() {
    // For every pair of seeded Facts<u8> entries and every domain mask:
    // meet returns Bot only when the brute-force intersection is empty, and
    // otherwise an entry whose concretization contains the intersection.
    return;
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
#[ignore = "abs-domain-registry: not implemented yet"]
fn reduce_preserves_the_concretization() {
    // For every seeded Facts<u8> entry and every mask, reduce returns Bot
    // exactly when the brute-force concretization is empty, and otherwise an
    // entry with the same concretization.
    return;
}

#[test]
#[ignore = "abs-domain-registry: not implemented yet"]
fn disabled_fields_stay_top() {
    // For every mask, the decoded result of top, meet, reduce and every
    // forward and backward transfer has every disabled field equal to the
    // field's top.
    return;
}

#[test]
#[ignore = "abs-domain-registry: not implemented yet"]
fn is_singleton_is_exact() {
    // as_constant(e) is Some(v) exactly when the brute-force concretization
    // of e is {v}: every u8 constant, every Bool4 value, and FactsZ
    // constants in -1000..=1000. A two-element set is never a singleton.
    return;
}

// ---------------------------------------------------------------------------
// Operators (§4)
// ---------------------------------------------------------------------------

#[test]
#[ignore = "abs-domain-registry: not implemented yet"]
fn operator_names_resolve_with_their_signature() {
    // Every operator of §4 resolves by name to its carrier signature
    // (`bvadd`: (BV N, BV N) -> BV N; `bvult`: (BV N, BV N) -> Bool; `<`:
    // (Int, Int) -> Bool; `ite`: (Bool, S, S) -> S; `=`: (S, S) -> Bool).
    // A signature mismatch (`bvadd` on Int, `+` on BV 8) and an unknown name
    // are rejected.
    return;
}

#[test]
#[ignore = "abs-domain-registry: not implemented yet"]
fn forward_transfers_are_sound_on_u8_pairs() {
    // For every BitVec operator of §4 with a forward transfer, every pair of
    // seeded Facts<u8> entries (a, b), and every x in gamma(a), y in
    // gamma(b): the concrete SMT-LIB result op(x, y) is in
    // gamma(forward(op, a, b)). Unary operators on every seeded entry.
    // Report pct_non_optimal per operator (tests/common/mod.rs).
    return;
}

#[test]
#[ignore = "abs-domain-registry: not implemented yet"]
fn division_by_zero_follows_smtlib() {
    // forward(bvudiv, a, b) contains all ones (255 at u8) whenever 0 is in
    // gamma(b); forward(bvurem, a, b) contains every x in gamma(a) whenever
    // 0 is in gamma(b). Same for bvsdiv (-1 or 1 by the sign of x), bvsrem
    // (x), and for Int `div` and `mod` with the registry's chosen value
    // (§9).
    return;
}

#[test]
#[ignore = "abs-domain-registry: not implemented yet"]
fn comparisons_are_sound_on_u8_pairs() {
    // For bvult, bvule, bvslt, bvsle and `=` on every pair of seeded
    // Facts<u8> entries: forward contains the truth value of every concrete
    // pair. The forward result is Top whenever both truth values occur.
    return;
}

#[test]
#[ignore = "abs-domain-registry: not implemented yet"]
fn backward_transfers_are_sound_on_u8() {
    // For every operator of §4 with a backward transfer, every seeded result
    // entry r and operand entries (a, b): backward returns operands
    // (a', b') with gamma(a') a subset of gamma(a), gamma(b') a subset of
    // gamma(b), and every concrete pair (x, y) with op(x, y) in gamma(r) kept
    // in gamma(a') x gamma(b'). Bot only when no such pair exists.
    return;
}

#[test]
#[ignore = "abs-domain-registry: not implemented yet"]
fn ite_follows_the_design_table() {
    // forward(ite, c, t, e) is t when c is True, e when c is False, and
    // contains gamma(t) union gamma(e) when c is Top. backward(ite, R, c, t, e)
    // implements egraph/doc/future/eclass-analysis.md §6: meet(R, e) Bot
    // gives c = True and t := t meet R; meet(R, t) Bot gives c = False and
    // e := e meet R; both Bot gives Bot. Checked on seeded Facts<u8> and
    // every Bool4.
    return;
}

#[test]
#[ignore = "abs-domain-registry: not implemented yet"]
fn bool_connectives_are_exact() {
    // not, and, or, xor, =>, and `=` on Bool, forward and backward, on every
    // tuple of Bool4 values: the result is exactly the set of concrete
    // results (reach1 and reach2 in src/bool4.rs).
    return;
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
#[ignore = "abs-domain-registry: not implemented yet"]
fn non_native_width_is_top() {
    // At BitVec(7) every registry function returns top and lookup of every
    // bitvec domain name reports it unavailable; no function panics.
    return;
}
