// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Property tests for the five `external_body` primitives in `bplus_layout`:
//! `arr_get`, `arr_set`, `slice_get`, `sel_usize`, `arr_shift_up`.
//!
//! These five are trusted, not proved: each exists so a fact Verus already
//! proved at the call sites (an index bound, a total conditional, a slice-copy
//! effect) reaches the machine code without the check, branch, or element loop
//! `rustc` would otherwise emit — see the module doc and
//! `doc/design/02-trust-boundary.md`. Each contract restates the documented
//! behavior of a std operation the pinned vstd does not spec (`get_unchecked`,
//! `select_unpredictable`, `copy_within`), so the contract can be checked
//! directly against the checked std form it claims to equal. That agreement IS
//! the trusted statement; nothing weaker is being sampled.
//!
//! Preconditions are generated satisfied (in-range indices, `pos <= cnt < N`).
//! A call that violates a verified `requires` is UB by construction, not a
//! testable branch — the same scoping as the hand-rolled fuzzes in
//! `external_body_contract_fuzz.rs`. Relative to those, these add shrinking, a
//! wider input distribution, and the `N`/element-type instantiations the trees
//! actually use.

use proptest::prelude::*;
use semi_persistent_containers_verus::bplus_layout::{
    arr_get, arr_set, arr_shift_up, sel_usize, slice_get,
};

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
