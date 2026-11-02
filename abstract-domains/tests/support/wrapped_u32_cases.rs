// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Sparse u32 reference cases. No production implementation is connected.
use super::wrapped_oracle::Repr;

pub const MODULUS: u64 = 1u64 << 32;

// Distance along the ring, computed in u64 to avoid native overflow.
fn distance(start: u32, end: u32) -> u64 {
    (u64::from(end) + MODULUS - u64::from(start)) % MODULUS
}

pub fn reference_has(repr: Repr, x: u32) -> bool {
    match repr {
        Repr::Empty => false,
        Repr::Full => true,
        Repr::Arc { lo, hi } => distance(lo, x) <= distance(lo, hi),
    }
}

pub fn cardinality(repr: Repr) -> u64 {
    match repr {
        Repr::Empty => 0,
        Repr::Full => MODULUS,
        Repr::Arc { lo, hi } => distance(lo, hi) + 1,
    }
}

pub fn boundary_cases() -> Vec<Repr> {
    vec![
        Repr::Empty,
        Repr::Full,
        Repr::Arc { lo: 0, hi: 0 },
        Repr::Arc {
            lo: u32::MAX,
            hi: u32::MAX,
        },
        Repr::Arc {
            lo: 0,
            hi: u32::MAX,
        },
        Repr::Arc { lo: 1, hi: 0 },
        Repr::Arc {
            lo: u32::MAX,
            hi: 1,
        },
        Repr::Arc {
            lo: u32::MAX - 1,
            hi: 1,
        },
        Repr::Arc { lo: 0, hi: 15 },
        Repr::Arc { lo: 14, hi: 2 },
        Repr::Arc {
            lo: 0x7fff_ffff,
            hi: 0x8000_0000,
        },
    ]
}

pub fn probes(repr: Repr) -> Vec<u32> {
    let mut xs = vec![
        0,
        1,
        2,
        14,
        15,
        16,
        0x7fff_ffff,
        0x8000_0000,
        u32::MAX - 1,
        u32::MAX,
    ];
    if let Repr::Arc { lo, hi } = repr {
        for endpoint in [lo, hi] {
            xs.extend([endpoint.wrapping_sub(1), endpoint, endpoint.wrapping_add(1)]);
        }
    }
    xs.sort_unstable();
    xs.dedup();
    xs
}

/// Call with the real executable membership once it exists.
/// This samples boundaries; it does not enumerate all u32 values.
pub fn check_membership(mut contains: impl FnMut(Repr, u32) -> bool) -> Result<(), String> {
    for repr in boundary_cases() {
        for x in probes(repr) {
            let expected = reference_has(repr, x);
            let actual = contains(repr, x);
            if actual != expected {
                return Err(format!(
                    "membership mismatch: {repr:?}, x={x}, expected={expected}, actual={actual}"
                ));
            }
        }
    }
    Ok(())
}
