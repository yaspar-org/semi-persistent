// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Canary smoke test: every egraph-shaped fixture runs its operation sequence.

#[test]
fn canary_smoke() {
    containers_verus_canary::run_all_smoke();
}

/// The Tagged-laws fuzzer template with randomized inputs (trust group E
/// mitigation). This is the consumer-shaped executable check of those laws.
#[test]
fn tagged_laws_fuzz() {
    use containers_verus_canary::tagged_fuzzer_template::{JustificationShaped, check_tagged_laws};
    let mut x: u64 = 0x1234_5678_9ABC_DEF0;
    for _ in 0..20_000 {
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        let val = match x % 3 {
            0 => JustificationShaped::Filler,
            1 => JustificationShaped::Root,
            _ => JustificationShaped::ChildOf(
                (x >> 32) as u32 & 0x7FFF_FFFF,
                (x >> 16) as u16,
                x & 1 == 1,
            ),
        };
        check_tagged_laws(val);
    }
}
