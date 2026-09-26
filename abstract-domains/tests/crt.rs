// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

macro_rules! crt_cases {
    ($name:ident, $domain:ident, $uint:ty) => {
        #[test]
        fn $name() {
            use semi_persistent_abstract_domains::domains::$domain::{crt_merge, CrtMergeResult};

            assert!(matches!(
                crt_merge(6, 13, 4, 11),
                CrtMergeResult::Merged { modulus: 12, residue: 7 }
            ));
            assert!(matches!(crt_merge(6, 1, 4, 2), CrtMergeResult::Incompatible));

            let max = <$uint>::MAX;
            for expected in [0, 1, max] {
                match crt_merge(max, expected % max, max - 1, expected % (max - 1)) {
                    CrtMergeResult::ModulusOverflow { wide_residue } => {
                        assert_eq!(wide_residue, expected as u128);
                    }
                    _ => panic!("expected an overflowing modulus with a representable solution"),
                }
            }

            match crt_merge(max, max - 1, max - 1, max - 2) {
                CrtMergeResult::ModulusOverflow { wide_residue } => {
                    assert_eq!(wide_residue, (max as u128) * ((max - 1) as u128) - 1);
                    assert!(wide_residue > max as u128);
                }
                _ => panic!("expected an overflowing modulus without a representable solution"),
            }
        }
    };
}

crt_cases!(crt_u8, d8, u8);
crt_cases!(crt_u16, d16, u16);
crt_cases!(crt_u32, d32, u32);
crt_cases!(crt_u64, d64, u64);
