// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Prints the kata 5 estimate and exhaustively checks `ExecTnum::sub` on u8.

use semi_persistent_abstract_domains::domains::d8::ExecTnum;
use semi_persistent_abstract_domains::kata5::REPORT;

fn tnum_has(t: ExecTnum, x: u8) -> bool {
    (x & !t.mask) == t.val
}

#[test]
fn report_how_far() {
    println!("{REPORT}");
}

#[test]
fn sub_contains_every_u8_pair_on_constants() {
    for x in 0..=255u8 {
        for y in 0..=255u8 {
            let a = ExecTnum::constant(x);
            let b = ExecTnum::constant(y);
            let r = a.sub(&b);
            assert!(
                tnum_has(r, x.wrapping_sub(y)),
                "constant {x} - {y} not in result val={} mask={}",
                r.val,
                r.mask
            );
        }
    }
}
