// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! F2.2 conformance: the seven composed index x value modes (plus the
//! struct-family RLE composition) round-trip under 1000 proptest cases each.
//! Non-sorting modes preserve the exact sequence; the sorted-runs modes
//! preserve the write multiset, checked here through restore equivalence on
//! unique-index frames (where application order cannot matter). Every mode's
//! `restore_to` is compared against the reference application (last write to
//! each in-range cell wins), which is `apply_all`'s executable mirror.

use proptest::prelude::*;
use semi_persistent_containers_verus::layered::LayeredFrame;
use semi_persistent_containers_verus::value_compressor::{
    NoValueCompression, ValueCompressor, ValueDelta, ValueDictC, ValueRle,
};

type Diffs = Vec<(u32, u32)>;

/// The reference application: scattered last-write-wins onto `base`.
fn reference_apply(base: &[u32], diffs: &[(u32, u32)]) -> Vec<u32> {
    let mut out = base.to_vec();
    for &(v, i) in diffs {
        if (i as usize) < out.len() {
            out[i as usize] = v;
        }
    }
    out
}

fn check_exact<VC: ValueCompressor<u32>>(
    frame: &LayeredFrame<u32, u32, VC>,
    diffs: &Diffs,
    base: &[u32],
) {
    assert_eq!(frame.entry_len(), diffs.len());
    let mut restored = base.to_vec();
    frame.restore_to(&mut restored);
    assert_eq!(
        restored,
        reference_apply(base, diffs),
        "restore != reference"
    );
    let _ = frame.byte_len();
}

/// For the sorted (reordering) modes: same check, valid because the caller
/// guarantees unique indices, where application order cannot matter.
fn check_multiset<VC: ValueCompressor<u32>>(
    frame: &LayeredFrame<u32, u32, VC>,
    diffs: &Diffs,
    base: &[u32],
) {
    assert_eq!(frame.entry_len(), diffs.len());
    let mut restored = base.to_vec();
    frame.restore_to(&mut restored);
    assert_eq!(
        restored,
        reference_apply(base, diffs),
        "sorted restore != reference on unique-index frame"
    );
}

fn unique_by_index(diffs: Diffs) -> Diffs {
    let mut seen = std::collections::HashSet::new();
    diffs.into_iter().filter(|&(_, i)| seen.insert(i)).collect()
}

/// Runs-friendly generator: a few contiguous bursts plus scattered writes.
fn bursty() -> impl Strategy<Value = Diffs> {
    (
        proptest::collection::vec((0u32..40, 0u32..60), 0..40),
        proptest::collection::vec((0u32..40, 0u32..50, 1usize..8), 0..6),
    )
        .prop_map(|(scattered, bursts)| {
            let mut d = scattered;
            for (v, start, len) in bursts {
                for k in 0..len as u32 {
                    d.push((v.wrapping_add(k), start.saturating_add(k)));
                }
            }
            d
        })
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(1000))]

    // Mode 1: plain index x no value coding (the baseline).
    #[test]
    fn plain_none(diffs in bursty(), base in proptest::collection::vec(0u32..99, 0..64)) {
        let f = LayeredFrame::<u32, u32, NoValueCompression>::compress_plain(&diffs);
        check_exact(&f, &diffs, &base);
    }

    // Mode 2: write-order runs x no value coding.
    #[test]
    fn runs_none(diffs in bursty(), base in proptest::collection::vec(0u32..99, 0..64)) {
        let f = LayeredFrame::<u32, u32, NoValueCompression>::compress_runs(&diffs);
        check_exact(&f, &diffs, &base);
    }

    // Mode 3: sorted runs x no value coding (multiset; unique indices).
    #[test]
    fn runs_sorted_none(diffs in bursty(), base in proptest::collection::vec(0u32..99, 0..64)) {
        let diffs = unique_by_index(diffs);
        let f = LayeredFrame::<u32, u32, NoValueCompression>::compress_runs_sorted(&diffs);
        check_multiset(&f, &diffs, &base);
    }

    // Mode 4: plain index x dictionary values.
    #[test]
    fn plain_dict(diffs in bursty(), base in proptest::collection::vec(0u32..99, 0..64)) {
        let f = LayeredFrame::<u32, u32, ValueDictC>::compress_plain(&diffs);
        check_exact(&f, &diffs, &base);
    }

    // Mode 5: write-order runs x dictionary values.
    #[test]
    fn runs_dict(diffs in bursty(), base in proptest::collection::vec(0u32..99, 0..64)) {
        let f = LayeredFrame::<u32, u32, ValueDictC>::compress_runs(&diffs);
        check_exact(&f, &diffs, &base);
    }

    // Mode 6: sorted runs x dictionary values (multiset; unique indices).
    #[test]
    fn runs_sorted_dict(diffs in bursty(), base in proptest::collection::vec(0u32..99, 0..64)) {
        let diffs = unique_by_index(diffs);
        let f = LayeredFrame::<u32, u32, ValueDictC>::compress_runs_sorted(&diffs);
        check_multiset(&f, &diffs, &base);
    }

    // Mode 7: plain index x successive-delta values.
    #[test]
    fn plain_delta(diffs in bursty(), base in proptest::collection::vec(0u32..99, 0..64)) {
        let f = LayeredFrame::<u32, u32, ValueDelta>::compress_plain(&diffs);
        check_exact(&f, &diffs, &base);
    }

    // The struct-family composition (F2.4's codec): runs x equality-RLE.
    #[test]
    fn runs_rle(diffs in bursty(), base in proptest::collection::vec(0u32..99, 0..64)) {
        let f = LayeredFrame::<u32, u32, ValueRle>::compress_runs(&diffs);
        check_exact(&f, &diffs, &base);
    }
}

/// A frame with contiguous same-value writes: runs x dict undercuts plain on
/// both axes at once (the layered win the goal names).
#[test]
fn layered_size_beats_plain_on_bursty_small_alphabet() {
    let mut diffs: Diffs = Vec::new();
    for b in 0..8u32 {
        for k in 0..64u32 {
            diffs.push((b % 4, b * 64 + k));
        }
    }
    let plain = LayeredFrame::<u32, u32, NoValueCompression>::compress_plain(&diffs);
    let layered = LayeredFrame::<u32, u32, ValueDictC>::compress_runs(&diffs);
    assert!(
        layered.byte_len() * 4 < plain.byte_len(),
        "runs x dict must be at least 4x below plain on this frame: {} vs {}",
        layered.byte_len(),
        plain.byte_len()
    );
}
