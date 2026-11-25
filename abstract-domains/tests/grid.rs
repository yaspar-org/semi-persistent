// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Runtime checks of grid rounding (src/grid.rs) against brute force: every
//! `(x, r, m)` at u8, and hand-computed boundary cases at u128.
use semi_persistent_abstract_domains::grid::{round_down, round_up};

fn on_grid(x: u8, r: u8, m: u8) -> bool {
    if m == 0 { x == r } else { x % m == r }
}

/// Every well-formed grid `(r, m)` at u8: `m == 0` with any `r`, else `r < m`.
fn u8_grids() -> impl Iterator<Item = (u8, u8)> {
    (0..=255u8).flat_map(|m| {
        (0..=255u8)
            .filter(move |&r| m == 0 || r < m)
            .map(move |r| (r, m))
    })
}

#[test]
fn round_up_matches_brute_force_on_every_u8() {
    for (r, m) in u8_grids() {
        // Sweep x downward so the expected answer is the last grid point seen.
        let mut next: Option<u8> = None;
        for x in (0..=255u8).rev() {
            if on_grid(x, r, m) {
                next = Some(x);
            }
            assert_eq!(round_up(x, r, m), next, "round_up({x}, {r}, {m})");
        }
    }
}

#[test]
fn round_down_matches_brute_force_on_every_u8() {
    for (r, m) in u8_grids() {
        let mut prev: Option<u8> = None;
        for x in 0..=255u8 {
            if on_grid(x, r, m) {
                prev = Some(x);
            }
            assert_eq!(round_down(x, r, m), prev, "round_down({x}, {r}, {m})");
        }
    }
}

#[test]
fn rounding_at_u128_boundaries() {
    const MAX: u128 = u128::MAX;
    const HALF: u128 = 1 << 127;

    // Singleton grid `m == 0`: the only point is `r`.
    assert_eq!(round_up(5u128, 7, 0), Some(7));
    assert_eq!(round_up(8u128, 7, 0), None);
    assert_eq!(round_down(8u128, 7, 0), Some(7));
    assert_eq!(round_down(6u128, 7, 0), None);
    assert_eq!(round_up(MAX, MAX, 0), Some(MAX));
    assert_eq!(round_down(0u128, 0, 0), Some(0));

    // Top `(r, m) == (0, 1)`: every word is on the grid.
    for x in [0, 1, HALF, MAX - 1, MAX] {
        assert_eq!(round_up(x, 0, 1), Some(x));
        assert_eq!(round_down(x, 0, 1), Some(x));
    }

    // Parity at the ends of the range: MAX is odd.
    assert_eq!(round_up(MAX, 1, 2), Some(MAX));
    assert_eq!(round_up(MAX, 0, 2), None);
    assert_eq!(round_up(MAX - 1, 1, 2), Some(MAX));
    assert_eq!(round_down(0u128, 1, 2), None);
    assert_eq!(round_down(0u128, 0, 2), Some(0));
    assert_eq!(round_down(1u128, 0, 2), Some(0));

    // Modulus MAX: the grid of residue 0 is {0, MAX}, of residue 5 is {5}.
    assert_eq!(round_up(1u128, 0, MAX), Some(MAX));
    assert_eq!(round_down(MAX - 1, 0, MAX), Some(0));
    assert_eq!(round_up(6u128, 5, MAX), None);
    assert_eq!(round_down(4u128, 5, MAX), None);

    // Modulus 2^127, residue 3: the grid is {3, 2^127 + 3}.
    assert_eq!(round_up(4u128, 3, HALF), Some(HALF + 3));
    assert_eq!(round_up(HALF + 4, 3, HALF), None);
    assert_eq!(round_down(HALF + 2, 3, HALF), Some(3));
    assert_eq!(round_down(MAX, 3, HALF), Some(HALF + 3));
    assert_eq!(round_down(2u128, 3, HALF), None);

    // Small modulus near MAX: MAX % 10 == 5.
    assert_eq!(round_up(MAX - 9, 7, 10), Some(MAX - 8));
    assert_eq!(round_up(MAX - 7, 7, 10), None);
    assert_eq!(round_down(MAX, 7, 10), Some(MAX - 8));
    assert_eq!(round_down(MAX, 5, 10), Some(MAX));
}
