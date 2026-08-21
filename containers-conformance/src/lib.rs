// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Cross-implementation conformance harness. It runs finite differential and
//! property-generated traces over the shared operation surface of the reference
//! `semi-persistent-containers` crate and the verified implementation, plus
//! scoped layout and Criterion checks. It does not establish universal
//! observational equality; the implementations have documented API and
//! behavior differences.
//!
//! Layout parity (same struct sizes, same niche bit-stealing) is asserted by
//! `tests/layout_parity.rs`; behavioral parity by `tests/differential.rs`.
//! `benches/retained_containers_bench.rs` is a Criterion comparison against
//! the reference implementation. It reports estimates and confidence intervals;
//! it is not a CI gate or a proof of current production parity.

/// A simple inline-capture e-class ring used as a differential reference model.
pub mod prod_class_ring;

/// Deterministic xorshift64* generator: fixed seeds, exact replay.
pub struct Rng(u64);

#[allow(clippy::should_implement_trait)] // deliberate inherent `next`, matching the harness style
impl Rng {
    pub fn new(seed: u64) -> Self {
        Rng(seed.max(1))
    }
    pub fn next(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.0 = x;
        x.wrapping_mul(0x2545F4914F6CDD1D)
    }
    pub fn below(&mut self, n: u64) -> u64 {
        self.next() % n.max(1)
    }
}
