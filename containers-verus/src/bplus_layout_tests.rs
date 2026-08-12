// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! In-crate contract tests for the bplus_layout primitives, which are
//! `pub(crate)`: external misuse of these is undefined behavior, so the
//! public surface must not carry them, and their tests live here instead of
//! `tests/`. Merged from the former `tests/bplus_layout_proptest.rs` and the
//! bplus_layout block of `tests/external_body_contract_fuzz.rs`.

use crate::bplus_layout::{arr_get, arr_set, arr_shift_up, sel_usize, slice_get};
use proptest::prelude::*;

/// The three array contracts at one `(T, N)` instantiation. Every property
/// compares against a mirror driven through the ordinary checked std form:
/// checked indexing for `arr_get`/`arr_set`, `copy_within` for `arr_shift_up`
/// (whose four-clause postcondition is exactly `copy_within(pos..cnt, pos+1)`
/// stated element-wise).
macro_rules! arr_contract_props {
    ($mod_name:ident, $t:ty, $n:expr) => {
        mod $mod_name {
            use super::*;

            proptest! {
                #[test]
                fn arr_get_agrees_with_checked_indexing(
                    v in prop::collection::vec(any::<$t>(), $n),
                    i in 0usize..$n,
                ) {
                    let a: [$t; $n] = v.try_into().unwrap();
                    prop_assert_eq!(arr_get(&a, i), a[i]);
                }

                #[test]
                fn arr_set_agrees_with_checked_indexing(
                    v in prop::collection::vec(any::<$t>(), $n),
                    i in 0usize..$n,
                    w in any::<$t>(),
                ) {
                    let mut a: [$t; $n] = v.try_into().unwrap();
                    let mut mirror = a;
                    arr_set(&mut a, i, w);
                    mirror[i] = w;
                    // Equality over the WHOLE array: the postcondition is
                    // `update(i, v)`, i.e. every other slot unchanged.
                    prop_assert_eq!(a, mirror);
                }

                #[test]
                fn arr_shift_up_agrees_with_copy_within(
                    v in prop::collection::vec(any::<$t>(), $n),
                    x in 0usize..$n,
                    y in 0usize..$n,
                ) {
                    let (pos, cnt) = if x <= y { (x, y) } else { (y, x) };
                    let mut a: [$t; $n] = v.try_into().unwrap();
                    let mut mirror = a;
                    arr_shift_up(&mut a, pos, cnt);
                    mirror.copy_within(pos..cnt, pos + 1);
                    prop_assert_eq!(a, mirror);
                }
            }
        }
    };
}

// The instantiations the trees use: `Layout64U32` keys (key_cap = 7) and leaf
// data (leaf_cap = 14) over u32 words, and the 62-slot leaf of the prod-parity
// layout over both word widths. N = 62 is also the one size whose `(pos, cnt)`
// distribution reaches both arms of `arr_shift_up`'s length-18 dispatch.
arr_contract_props!(n7_u32, u32, 7);
arr_contract_props!(n14_u32, u32, 14);
arr_contract_props!(n62_u32, u32, 62);
arr_contract_props!(n62_u64, u64, 62);

proptest! {
    #[test]
    fn slice_get_agrees_with_checked_indexing(
        v in prop::collection::vec(any::<u64>(), 1..300usize),
        idx in any::<prop::sample::Index>(),
    ) {
        let i = idx.index(v.len());
        prop_assert_eq!(slice_get(&v, i), v[i]);
    }

    #[test]
    fn sel_usize_agrees_with_if_else(
        c in any::<bool>(),
        a in any::<usize>(),
        b in any::<usize>(),
    ) {
        prop_assert_eq!(sel_usize(c, a, b), if c { b } else { a });
    }
}

/// `sel_usize` at the type's extremes, both arms. Deterministic rather than
/// sampled: proptest's integer strategies do not weight the endpoints, and the
/// postcondition must hold exactly there (a masking implementation is most
/// likely to break at all-ones/all-zeros).
#[test]
fn sel_usize_extremes() {
    for &(a, b) in &[
        (0usize, 0usize),
        (0, usize::MAX),
        (usize::MAX, 0),
        (usize::MAX, usize::MAX),
        (1, usize::MAX - 1),
    ] {
        for c in [false, true] {
            assert_eq!(sel_usize(c, a, b), if c { b } else { a });
        }
    }
}

/// `arr_shift_up` at shift lengths 17 and 18 — the two sides of its internal
/// scalar/`memmove` dispatch — at every `pos` that admits them. Deterministic
/// because the dispatch boundary is the one input the property above only
/// samples: a fast path that disagrees with the slow path is the specific
/// defect a length-dispatched implementation can have.
#[test]
fn arr_shift_up_dispatch_boundary() {
    const N: usize = 62;
    for shift in [17usize, 18] {
        for pos in 0..(N - shift) {
            let cnt = pos + shift;
            let mut a = [0u32; N];
            for (k, slot) in a.iter_mut().enumerate() {
                *slot = k as u32 ^ 0xA5A5_0000;
            }
            let mut mirror = a;
            arr_shift_up(&mut a, pos, cnt);
            mirror.copy_within(pos..cnt, pos + 1);
            assert_eq!(a, mirror, "shift {shift} at pos {pos}");
        }
    }
}

// --------------------------------------------------------------------------
// bplus_layout::arr_get / arr_set / sel_usize / arr_shift_up.
//
// (`slice_get`, the fifth bplus_layout trusted primitive, is covered by the
// property suite `tests/bplus_layout_proptest.rs`, which also re-checks these
// four with shrinking and the tree's actual `(T, N)` instantiations.)
//
// These four are `external_body` so that a fact Verus already PROVED reaches
// the machine code: the elided bounds check (`arr_get`/`arr_set`, whose `i < N`
// is a verified precondition at every call site), the `cmov` lowering of the
// bisection's data-dependent update (`sel_usize`), and one `memmove` where
// Verus's invariant rules force an element loop (`arr_shift_up`). Their
// contracts are trivial to state and therefore trivial to check at runtime,
// which is exactly why they are fuzzed rather than argued about:
// `arr_get`/`arr_set` must agree with checked indexing on every in-range index,
// `sel_usize` must agree with the `if`/`else` it replaces on both boolean
// values, and `arr_shift_up` must agree with `copy_within` at every
// `(pos, cnt)` -- including across its internal length dispatch, which is the
// one place a hand-written fast path could disagree with the slow one.
//
// `arr_get`/`arr_set` are only called OUT of range by a caller that violated a
// verified precondition, so the out-of-range case is deliberately not exercised
// (it is UB, not a testable branch).
// --------------------------------------------------------------------------

#[test]
fn arr_get_set_agree_with_checked_indexing() {
    use crate::bplus_layout::{arr_get, arr_set};

    const N: usize = 62;
    let mut lcg: u64 = 0x5EED_1234_ABCD_0001;
    let mut next = move || {
        lcg = lcg
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        lcg >> 1
    };

    for round in 0..500 {
        // A fresh array and a mirror the test indexes the ordinary, checked way.
        let mut a = [0u32; N];
        let mut mirror = [0u32; N];
        for (i, m) in mirror.iter_mut().enumerate() {
            let v = next() as u32;
            arr_set(&mut a, i, v);
            *m = v;
        }
        // reads agree at every in-range index
        for (i, &m) in mirror.iter().enumerate() {
            assert_eq!(
                arr_get(&a, i),
                m,
                "round {round}: arr_get disagrees with checked read at {i}"
            );
        }
        // an overwrite touches exactly the one slot it names
        let pos = (next() as usize) % N;
        let w = next() as u32;
        arr_set(&mut a, pos, w);
        mirror[pos] = w;
        for (i, &m) in mirror.iter().enumerate() {
            assert_eq!(
                arr_get(&a, i),
                m,
                "round {round}: arr_set perturbed slot {i} while writing {pos}"
            );
        }
    }
    println!("arr_get_set_agree_with_checked_indexing: OK (500 rounds x 62 slots)");
}

#[test]
fn sel_usize_agrees_with_if_else_lcg() {
    use crate::bplus_layout::sel_usize;

    let mut lcg: u64 = 0x9E37_79B9_7F4A_7C15;
    let mut next = move || {
        lcg = lcg
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        lcg >> 1
    };

    // Edge values plus random ones: the postcondition is `if c { b } else { a }`,
    // so both arms must be reproduced exactly, including at the type's extremes.
    let mut cases: Vec<(usize, usize)> = vec![
        (0, 0),
        (0, usize::MAX),
        (usize::MAX, 0),
        (usize::MAX, usize::MAX),
        (1, usize::MAX - 1),
    ];
    for _ in 0..500 {
        cases.push((next() as usize, next() as usize));
    }

    for (i, &(a, b)) in cases.iter().enumerate() {
        for c in [false, true] {
            let expect = if c { b } else { a };
            assert_eq!(
                sel_usize(c, a, b),
                expect,
                "case {i}: sel_usize({c}, {a}, {b}) != if/else"
            );
        }
    }
    println!(
        "sel_usize_agrees_with_if_else: OK ({} cases x 2)",
        cases.len()
    );
}

#[test]
fn arr_shift_up_agrees_with_copy_within() {
    use crate::bplus_layout::arr_shift_up;

    const N: usize = 62;
    let mut lcg: u64 = 0xD1B5_4A32_D192_ED03;
    let mut next = move || {
        lcg = lcg
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        lcg >> 11
    };

    // Every (pos, cnt) with pos <= cnt < N is exercised exhaustively, so both
    // arms of the internal length dispatch (scalar below the measured crossover,
    // `memmove` above it) are covered, as is the boundary between them -- the
    // only place the optimization could introduce a disagreement.
    let mut checked = 0usize;
    for cnt in 0..N {
        for pos in 0..=cnt {
            let mut a = [0u32; N];
            for slot in a.iter_mut() {
                *slot = next() as u32;
            }
            let mut want = a;
            want.copy_within(pos..cnt, pos + 1);

            arr_shift_up(&mut a, pos, cnt);
            assert_eq!(
                a, want,
                "arr_shift_up(pos={pos}, cnt={cnt}) disagrees with copy_within"
            );
            checked += 1;
        }
    }
    println!("arr_shift_up_agrees_with_copy_within: OK ({checked} (pos, cnt) pairs)");
}
