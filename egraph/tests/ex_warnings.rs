// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! E3: questionable constructions proceed, and each is reported once.

use semi_persistent_egraph::extraction::oint::{Build, LARGE_DOMAIN, Over, Under, Warning};
use semi_persistent_egraph::extraction::target::CnfTarget;

#[test]
fn each_warning_kind_is_reported_once_and_the_build_proceeds() {
    let mut cnf = CnfTarget::default();
    let mut b = Build::new(&mut cnf);

    let values: Vec<i64> = (0..(LARGE_DOMAIN as i64 + 10)).collect();
    let big = b.int(&values);
    let _again = b.int(&values);

    let small = b.int(&[1, 4, 9]);
    let capped = b.saturate(&small, 5);
    let _capped_again = b.saturate(&small, 5);
    assert_eq!(
        capped.values(),
        &[1, 4, 5],
        "values above the bound collapse onto it"
    );

    let _o: semi_persistent_egraph::extraction::oint::OInt<Over> = small.assume(&mut b);
    let _o2: semi_persistent_egraph::extraction::oint::OInt<Over> = small.assume(&mut b);
    let _u: semi_persistent_egraph::extraction::oint::OInt<Under> = small.assume(&mut b);

    let w = &b.warnings;
    let count = |p: &dyn Fn(&Warning) -> bool| w.iter().filter(|x| p(x)).count();
    assert_eq!(
        count(&|x| matches!(x, Warning::LargeDomain { .. })),
        1,
        "{w:?}"
    );
    assert_eq!(
        count(&|x| matches!(x, Warning::DomainCapped { bound, dropped: 1 } if *bound == 5)),
        1,
        "{w:?}"
    );
    assert_eq!(
        count(&|x| matches!(x, Warning::PolarityEscape { to: "Over", .. })),
        1,
        "{w:?}"
    );
    assert_eq!(
        count(&|x| matches!(x, Warning::PolarityEscape { to: "Under", .. })),
        1,
        "{w:?}"
    );
    assert_eq!(
        big.values().len(),
        LARGE_DOMAIN + 10,
        "a large domain is kept, not truncated"
    );
}
