// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Checked index arithmetic under the same module surface as the verified crate.

pub use crate::dense_id::IndexLike;

#[inline(always)]
pub fn checked_add<I: IndexLike>(a: I, b: I) -> Option<I> {
    a.checked_add(b)
}

#[inline(always)]
pub fn checked_sub<I: IndexLike>(a: I, b: I) -> Option<I> {
    a.checked_sub(b)
}

#[inline(always)]
pub fn checked_mul<I: IndexLike>(a: I, b: I) -> Option<I> {
    a.checked_mul(b)
}

#[inline(always)]
pub fn checked_incr<I: IndexLike>(a: I) -> Option<I> {
    a.checked_incr()
}

#[inline(always)]
pub fn checked_decr<I: IndexLike>(a: I) -> Option<I> {
    a.checked_decr()
}

#[inline(always)]
pub fn checked_add_usize<I: IndexLike>(a: I, rhs: usize) -> Option<I> {
    a.checked_add_usize(rhs)
}
