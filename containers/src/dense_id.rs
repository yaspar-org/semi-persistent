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
        // Checked against `T`, not against `T::Index`. The backing word is one bit
        // wider than the id: a 31-bit id is carried in a `u32`, so
        // `T::Index::try_from_usize` admits everything up to `u32::MAX` and only
        // rejects at twice the real capacity. Every value in between passed this
        // guard and then hit the `expect` inside `T::from_usize` — a panic where the
        // caller had explicitly asked for the fallible path and was entitled to
        // `None`. `T`'s own `IndexLike` checks the payload mask, which is the
        // capacity that actually exists.
        let id = T::try_from_usize(self.next)?;
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
///
/// # Contract
///
/// `as_usize` is an injection into `[0, MAX.as_usize()]`, `MIN.as_usize() == 0`, and
/// `try_from_usize` is its exact inverse: it returns `Some(x)` with
/// `x.as_usize() == n` when `n <= MAX.as_usize()`, and `None` otherwise. In
/// particular it must **never** narrow before range-checking — a `try_from_usize`
/// that returns `Some` for an out-of-range `n` aliases two positions onto one index,
/// which no amount of checking downstream can recover.
///
/// # Arithmetic
///
/// The checked operations below are the only arithmetic this trait offers, and they
/// exist so that index arithmetic can be written generically without falling back to
/// `usize`. Storing a `usize` where the value is an index into a structure sized by
/// `Self` wastes bytes at 31 bits and hides the real capacity; computing in `usize`
/// and casting back with `as` reintroduces exactly the silent truncation the contract
/// above forbids.
///
/// Every operation is bounded by `MAX`, not by the backing word: a 31-bit id lives in
/// a `u32`, so `Self::MAX` is `0x7fff_ffff` and an addition landing at `0x8000_0000`
/// returns `None` even though the `u32` add would not have overflowed. The default
/// bodies get this right for free by routing through `try_from_usize`. An override may
/// only be a faster spelling of the same result.
///
/// # Width
///
/// `as_usize` is **total** — no `Option` — so implementing this trait asserts that the
/// whole index range fits a pointer: `MAX.as_usize()` is exact, never truncated. That is
/// what lets a `usize` counter bounded by an `Self`-indexed collection be incremented
/// without an overflow check, which several callers rely on. The verified crate carries
/// the same statement as a named proof obligation,
/// `IndexLike::lemma_max_nat_fits_usize` (`containers-verus/src/index_like.rs`), because
/// there it has to be discharged rather than assumed. An index type wider than a pointer
/// belongs in neither: here `as_usize` would silently narrow, and there the lemma would
/// not close.
pub trait IndexLike: Copy + Ord + Hash + core::fmt::Debug {
    const MIN: Self;
    const MAX: Self;
    fn as_usize(self) -> usize;
    fn try_from_usize(n: usize) -> Option<Self>;

    /// `self + rhs`, or `None` if the sum is not representable in `Self`.
    #[inline]
    fn checked_add(self, rhs: Self) -> Option<Self> {
        Self::try_from_usize(self.as_usize().checked_add(rhs.as_usize())?)
    }

    /// `self - rhs`, or `None` if `rhs > self`.
    #[inline]
    fn checked_sub(self, rhs: Self) -> Option<Self> {
        Self::try_from_usize(self.as_usize().checked_sub(rhs.as_usize())?)
    }

    /// `self * rhs`, or `None` if the product is not representable in `Self`.
    ///
    /// For strides into a flattened pool: `base + k * stride` is the shape that
    /// overflows first, because the product is unbounded by either factor's width.
    #[inline]
    fn checked_mul(self, rhs: Self) -> Option<Self> {
        Self::try_from_usize(self.as_usize().checked_mul(rhs.as_usize())?)
    }

    /// `self + 1`, or `None` at `MAX`.
    ///
    /// The common case by a wide margin: a cursor, a length, or a fresh position.
    /// Named rather than spelled `checked_add(ONE)` because the trait has no `ONE` —
    /// a bump needs no second value of `Self` to be constructed first.
    #[inline]
    fn checked_incr(self) -> Option<Self> {
        Self::try_from_usize(self.as_usize().checked_add(1)?)
    }

    /// `self - 1`, or `None` at `MIN`.
    #[inline]
    fn checked_decr(self) -> Option<Self> {
        Self::try_from_usize(self.as_usize().checked_sub(1)?)
    }

    /// `self + rhs` where `rhs` is a `usize` count, or `None` if the sum is not
    /// representable in `Self`.
    ///
    /// The boundary between a `std` collection's `len()` and a narrow stored index:
    /// the count arrives as `usize` and must not be assumed to fit.
    #[inline]
    fn checked_add_usize(self, rhs: usize) -> Option<Self> {
        Self::try_from_usize(self.as_usize().checked_add(rhs)?)
    }
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
