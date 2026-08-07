// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Compact bitset backed by `std::vec::Vec<u64>`.
//!
//! prod-parity: a verbatim port of
//! production's `containers::bitset` (`containers/src/bitset.rs`). It is a plain
//! scratch utility the e-graph's e-matching uses (`egraph/src/ematch.rs`), NOT a
//! semi-persistent container — production keeps it outside its container proofs
//! for the same reason, so it lives outside `verus!{}` here and carries no
//! contract. `std::vec::Vec` is spelled out because this crate's root re-exports
//! shadow the bare `Vec` name with the verified container.
//!
//! Unlike the transitional aliases in `lib.rs`, this module is a permanent part
//! of the surface (production exposes `pub mod bitset`); it is not dropped at
//! step 3.

/// A compact set of bit indices, backed by a `Vec<u64>` word array.
#[derive(Clone, Debug)]
pub struct BitSet {
    words: std::vec::Vec<u64>,
}

impl BitSet {
    /// A bitset sized to hold indices in `[0, len)`, all clear.
    pub fn new(len: usize) -> Self {
        Self {
            words: std::vec![0; len.div_ceil(64)],
        }
    }

    /// Set bit `i`.
    pub fn set(&mut self, i: usize) {
        self.words[i / 64] |= 1 << (i % 64);
    }
    /// Clear bit `i`.
    pub fn clear(&mut self, i: usize) {
        self.words[i / 64] &= !(1 << (i % 64));
    }
    /// Whether bit `i` is set.
    pub fn test(&self, i: usize) -> bool {
        self.words[i / 64] & (1 << (i % 64)) != 0
    }

    /// Clear every bit.
    pub fn clear_all(&mut self) {
        self.words.iter_mut().for_each(|w| *w = 0);
    }
}
