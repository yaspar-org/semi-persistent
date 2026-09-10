// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Exercises the immutable value-only frame (`ValFrame`), the cold tier of the
//! live-path value-major diff log. `compress`/`decode_at` are verified
//! (`decode() == vals@`), so this checks the exec path end to end and the
//! measurement `byte_len` uses (`byte_len` is external_body).

use proptest::prelude::*;

use semi_persistent_containers_verus as verus;
use verus::diff_compress::ValFrame;

proptest! {
    // Value-repetitive frames round-trip and pack below plain.
    #[test]
    fn valframe_roundtrip(vals in prop::collection::vec(0u32..8, 0..300)) {
        let f = ValFrame::<u32>::compress(&vals);
        prop_assert_eq!(f.len(), vals.len());
        for (i, &v) in vals.iter().enumerate() {
            prop_assert_eq!(f.decode_at(i), v);
        }
        // D <= 8 -> 4-bit packed codes; a non-tiny frame beats plain (4 bytes/value).
        if vals.len() >= 16 {
            let plain = vals.len() * 4;
            prop_assert!(f.byte_len() < plain, "byte_len {} !< plain {}", f.byte_len(), plain);
        }
    }

    // Arbitrary-width values still round-trip (byte-granular codes).
    #[test]
    fn valframe_roundtrip_wide(vals in prop::collection::vec(0u32..100000, 0..200)) {
        let f = ValFrame::<u32>::compress(&vals);
        prop_assert_eq!(f.len(), vals.len());
        for (i, &v) in vals.iter().enumerate() {
            prop_assert_eq!(f.decode_at(i), v);
        }
    }
}
