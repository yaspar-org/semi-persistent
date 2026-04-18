// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Dense identifier trait for e-graph data structures.

use crate::tagged::Tagged;
use core::hash::Hash;

/// Types that can be used as dense array indices with inline capture.
///
/// Requirements:
/// - Fits densely in [0, N) where N ≤ 2^k for k ∈ {7, 15, 31, 63}
/// - Has a natural word size (Index: u8/u16/u32/u64)
/// - Can convert to/from usize for array indexing
/// - Can bit-pack capture flag in MSB (InlineCapturable)
///
/// Used by union-find, circular lists, and hashcons.
pub trait DenseId:
    Clone + Copy + Default + PartialEq + Eq + Ord + Hash + Tagged + IndexLike + Into<Self::Index>
{
    /// Natural word size: u8, u16, u32, or u64.
    type Index: IndexLike + Tagged;

    fn to_usize(self) -> usize;
    fn from_usize(n: usize) -> Self;
}

/// Sequential ID allocator. Generates monotonically increasing IDs up to capacity.
pub struct IdFactory<T: DenseId> {
    next: usize,
    _phantom: core::marker::PhantomData<T>,
}

impl<T: DenseId> IdFactory<T> {
    pub fn new() -> Self {
        Self {
            next: 0,
            _phantom: core::marker::PhantomData,
        }
    }

    /// Allocate the next ID, or `None` if the range is exhausted.
    pub fn try_alloc(&mut self) -> Option<T> {
        T::Index::try_from_usize(self.next)?;
        let id = T::from_usize(self.next);
        self.next += 1;
        Some(id)
    }

    /// Allocate the next ID. Panics if the range is exhausted.
    pub fn alloc(&mut self) -> T {
        self.try_alloc().expect("DenseId range exhausted")
    }

    pub fn count(&self) -> usize {
        self.next
    }
}

impl<T: DenseId> Default for IdFactory<T> {
    fn default() -> Self {
        Self::new()
    }
}

/// Defines the bitwidth and addressable capacity of a semi-persistent vector.
///
/// Implementors: u8, u16, u32, u64, and DenseId types.
/// Determines diff entry size and max capacity.
pub trait IndexLike: Copy + Ord + Hash + core::fmt::Debug {
    const MIN: Self;
    const MAX: Self;
    fn as_usize(self) -> usize;
    fn try_from_usize(n: usize) -> Option<Self>;
}

impl IndexLike for u8 {
    const MIN: Self = 0;
    const MAX: Self = u8::MAX;
    fn as_usize(self) -> usize {
        self as usize
    }
    fn try_from_usize(n: usize) -> Option<Self> {
        n.try_into().ok()
    }
}

impl IndexLike for u16 {
    const MIN: Self = 0;
    const MAX: Self = u16::MAX;
    fn as_usize(self) -> usize {
        self as usize
    }
    fn try_from_usize(n: usize) -> Option<Self> {
        n.try_into().ok()
    }
}

impl IndexLike for u32 {
    const MIN: Self = 0;
    const MAX: Self = u32::MAX;
    fn as_usize(self) -> usize {
        self as usize
    }
    fn try_from_usize(n: usize) -> Option<Self> {
        n.try_into().ok()
    }
}

impl IndexLike for u64 {
    const MIN: Self = 0;
    const MAX: Self = u64::MAX;
    fn as_usize(self) -> usize {
        self as usize
    }
    fn try_from_usize(n: usize) -> Option<Self> {
        n.try_into().ok()
    }
}

impl IndexLike for usize {
    const MIN: Self = 0;
    const MAX: Self = usize::MAX;
    fn as_usize(self) -> usize {
        self
    }
    fn try_from_usize(n: usize) -> Option<Self> {
        Some(n)
    }
}
