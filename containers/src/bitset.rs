// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Compact bitset backed by `Vec<u64>`.

#[derive(Clone, Debug)]
pub struct BitSet {
    words: Vec<u64>,
}

impl BitSet {
    pub fn new(len: usize) -> Self {
        Self {
            words: vec![0; len.div_ceil(64)],
        }
    }

    pub fn set(&mut self, i: usize) {
        self.words[i / 64] |= 1 << (i % 64);
    }
    pub fn clear(&mut self, i: usize) {
        self.words[i / 64] &= !(1 << (i % 64));
    }
    pub fn test(&self, i: usize) -> bool {
        self.words[i / 64] & (1 << (i % 64)) != 0
    }

    pub fn clear_all(&mut self) {
        self.words.iter_mut().for_each(|w| *w = 0);
    }
}
