// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Documents the calibrated-adaptive selection cycle (`CalibrationPolicy`): run
//! the exact-size selector for a calibration window, promote the average winner
//! to a static default, run the default for a period, then re-calibrate — so the
//! per-frame adaptive cost is paid only during the (short) windows. These cases
//! pin the phase transitions and the promotion decision.

use semi_persistent_containers_verus as verus;
use verus::{CalibrationPolicy, CompressionMode, FrameStats};

const T: usize = 4; // u32 value
const I: usize = 4; // u32 index

fn is_auto(m: CompressionMode) -> bool {
    matches!(m, CompressionMode::Auto)
}
// Index-major family: `recommend` now promotes the sorted encoder (its cost is the
// sorted run count), so accept either index-major mode.
fn is_runs(m: CompressionMode) -> bool {
    matches!(
        m,
        CompressionMode::IndexRuns | CompressionMode::IndexRunsSorted
    )
}

// A clustered frame: 500 entries in one run, all values distinct — index-major
// is the exact-size winner.
fn clustered() -> FrameStats {
    FrameStats {
        n: 500,
        runs: 1,
        distinct: 500,
    }
}

#[test]
fn calibrate_then_promote_then_recalibrate() {
    let mut p = CalibrationPolicy::new(/*window*/ 4, /*period*/ 8);

    // Phase 1 — calibrating: flush uses Auto (per-frame exact) while observing.
    assert!(is_auto(p.flush_mode()), "starts calibrating -> Auto");
    for _ in 0..4 {
        assert!(
            is_auto(p.flush_mode()),
            "still calibrating during the window"
        );
        p.observe_frame(clustered(), T, I);
    }

    // Window filled -> promote the average winner (index-major) as the default,
    // and switch to steady state.
    assert!(!p.calibrating, "window filled -> steady state");
    assert!(
        is_runs(p.default),
        "clustered frames promote IndexRuns as default"
    );
    assert!(
        is_runs(p.flush_mode()),
        "steady state flushes with the promoted default"
    );

    // Phase 2 — default: flush uses the fixed default for `period` frames, no
    // per-frame decision paid.
    for _ in 0..8 {
        assert!(
            is_runs(p.flush_mode()),
            "default phase keeps the promoted mode"
        );
        p.observe_frame(clustered(), T, I);
    }

    // Period elapsed -> re-enter calibration to re-check the default.
    assert!(p.calibrating, "period elapsed -> re-calibrating");
    assert!(
        is_auto(p.flush_mode()),
        "re-calibration flushes with Auto again"
    );
}
