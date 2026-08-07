// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Feeds `examples/alignprobe.rs` a compile-time `ALIGNPROBE_PAD` count.
//!
//! `alignprobe` pads its text section by N nop bytes via `global_asm!`, whose
//! `concat!` requires a string *literal* — `option_env!(...).unwrap_or(...)` is
//! not one. This script turns the `PAD` build-time env var into a literal the
//! macro can consume, defaulting to `0` so a plain `cargo build` (and clippy's
//! `--all-targets`) compiles without any env set. `rerun-if-env-changed` means
//! `PAD=48 cargo run` rebuilds without a manual `touch`.
fn main() {
    let pad = std::env::var("PAD").unwrap_or_else(|_| "0".to_string());
    // Reject non-numeric input so a typo fails the build rather than the assembler.
    assert!(
        pad.chars().all(|c| c.is_ascii_digit()),
        "PAD must be a non-negative integer, got {pad:?}"
    );
    println!("cargo:rustc-env=ALIGNPROBE_PAD={pad}");
    println!("cargo:rerun-if-env-changed=PAD");
}
