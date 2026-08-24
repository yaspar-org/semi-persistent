// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Push-only semi-persistent vector.
//!
//! Mark saves the current length. Restore truncates back to it.
//! No diff log — data is never overwritten, only appended.

use super::token::{ContainerId, ForkHistory, VecToken};
use crate::dense_id::IndexLike;

/// Panic message for every capacity guard in this module.
///
/// Reaching it means the element count would leave `I`'s range, so no index or
/// saved length could name the new element. Widen `I` rather than catching this.
const FULL: &str = "append-only vec is full for its index word";

/// Push-only vec with semi-persistent mark/restore.
///
/// `TRACK=false` compiles out const-gated fork/frame execution. The generic
/// layout still contains empty frame and fork-history fields.
///
/// Mutation is intentionally append-only:
///
/// ```compile_fail
/// use semi_persistent_containers::AppendOnlyVec;
///
/// let mut log = AppendOnlyVec::<u32>::new();
/// let index = log.push(1);
/// *log.get_mut(index) = 2;
/// ```
///
/// # Index width
///
/// `I` is the word that names a position, and it bounds the collection: the last
/// storable element sits at `I::MAX.as_usize() - 1`, so `I::MAX` is never a valid
/// index and stays free as a sentinel. Saved frame lengths are stored as `I` too,
/// since a length here is a position — keeping them `usize` would cost 8 bytes per
/// nesting level to hold a number that provably fits 4.
///
/// The default is `usize` because a container cannot know its own population. On a
/// 64-bit target `usize` never overflows, so defaulting to it is safe but wasteful;
/// a caller who knows the population is bounded by a 31-bit id space opts into `u32`
/// and halves the frame stack. Defaulting the other way would silently cap every
/// caller who never thought about the parameter.
pub struct AppendOnlyVec<T, I: IndexLike = usize, const TRACK: bool = true> {
    data: Vec<T>,
    frames: Vec<I>,
    forks: ForkHistory,
    id: ContainerId,
}

impl<T, I: IndexLike, const TRACK: bool> AppendOnlyVec<T, I, TRACK> {
    pub fn new() -> Self {
        Self {
            data: Vec::new(),
            frames: Vec::new(),
            forks: ForkHistory::new(),
            id: ContainerId::new(),
        }
    }

    /// Append `val` and return its index.
    ///
    /// # Panics
    ///
    /// If the resulting element count would not be representable in `I`. The guard
    /// is on the *new* length, not on the returned index, so that every later
    /// `len()` is infallible by construction; checking only the index would admit a
    /// final push whose successor length traps on the next read.
    /// Total-API counterpart (parity with the verified crate's shell): production's
    /// core panics on misuse, so the counterpart always returns Ok and the panic
    /// stays the documented behavior. Exists so shared prod/verus harness
    /// bodies can use one calling convention.
    pub fn try_push(&mut self, value: T) -> Result<I, &'static str> {
        Ok(self.push(value))
    }

    pub fn push(&mut self, val: T) -> I {
        let idx = I::try_from_usize(self.data.len()).expect(FULL);
        assert!(idx.checked_incr().is_some(), "{FULL}");
        self.data.push(val);
        idx
    }

    #[inline]
    pub fn get(&self, idx: I) -> &T {
        &self.data[idx.as_usize()]
    }

    /// Number of stored elements.
    ///
    /// # Panics
    ///
    /// Never, for a vec grown only through [`push`](Self::push) — that guard keeps
    /// the count inside `I`. The conversion is still checked rather than cast so a
    /// future path that grows `data` behind `push`'s back fails here instead of
    /// silently reporting a wrapped length.
    #[inline]
    pub fn len(&self) -> I {
        I::try_from_usize(self.data.len()).expect("len overflow")
    }

    /// Borrow all currently stored elements as a contiguous slice.
    #[inline]
    pub fn as_slice(&self) -> &[T] {
        &self.data
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.data.is_empty()
    }

    pub fn iter(&self) -> impl Iterator<Item = &T> {
        self.data.iter()
    }

    /// Total-API counterpart (parity with the verified crate's shell): production's
    /// core panics on misuse, so the counterpart always returns Ok and the panic
    /// stays the documented behavior. Exists so shared prod/verus harness
    /// bodies can use one calling convention.
    pub fn try_mark(&mut self, policy: super::ShrinkPolicy) -> Result<VecToken, &'static str> {
        Ok(self.mark(policy))
    }

    pub fn mark(&mut self, shrink: super::ShrinkPolicy) -> VecToken {
        assert!(TRACK, "mark() called on untracked AppendOnlyVec");
        if let super::ShrinkPolicy::IfOverallocated { factor, headroom } = shrink {
            let cap = self.data.capacity();
            let len = self.data.len();
            if cap > len * factor + headroom {
                self.data.shrink_to(len + headroom);
            }
        }
        let depth = crate::token::narrow_count(self.frames.len(), "mark nesting depth");
        let token = VecToken {
            branch_id: self.forks.current_branch(),
            depth,
            frame_index: depth,
            container_id: self.id,
        };
        // `len()` rather than `data.len()`: the frame stack stores positions in `I`,
        // and this is where a length that outgrew the index word would surface.
        let saved = self.len();
        self.frames.push(saved);
        token
    }

    /// Total-API counterpart (parity with the verified crate's shell): production's
    /// core panics on misuse, so the counterpart always returns Ok and the panic
    /// stays the documented behavior. Exists so shared prod/verus harness
    /// bodies can use one calling convention.
    pub fn try_restore(&mut self, token: VecToken) -> Result<(), &'static str> {
        self.restore(token);
        Ok(())
    }

    pub fn restore(&mut self, token: VecToken) {
        assert!(TRACK, "restore() called on untracked AppendOnlyVec");
        self.validate_token(&token);
        let target = token.frame_index as usize;
        let saved_len = self.frames[target].as_usize();
        self.data.truncate(saved_len);
        self.frames.truncate(target);
        self.forks.fork(
            &token,
            crate::token::narrow_count(self.frames.len(), "mark nesting depth"),
        );
    }

    pub fn depth(&self) -> usize {
        self.frames.len()
    }

    pub fn is_valid_token(&self, token: &VecToken) -> bool {
        TRACK
            && token.container_id == self.id
            && self.forks.is_valid(
                token,
                crate::token::narrow_count(self.frames.len(), "mark nesting depth"),
            )
    }

    fn validate_token(&self, token: &VecToken) {
        assert_eq!(
            token.container_id, self.id,
            "token belongs to a different container"
        );
        assert!(
            self.forks.is_valid(
                token,
                crate::token::narrow_count(self.frames.len(), "mark nesting depth")
            ),
            "invalid token (abandoned future)"
        );
        assert!(
            (token.frame_index as usize) < self.frames.len(),
            "token points beyond frame stack"
        );
    }
}

impl<T: std::fmt::Debug, I: IndexLike, const TRACK: bool> std::fmt::Debug
    for AppendOnlyVec<T, I, TRACK>
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("AppendOnlyVec")
            .field("len", &self.data.len())
            .field("depth", &self.frames.len())
            .finish()
    }
}

impl<T, I: IndexLike, const TRACK: bool> Default for AppendOnlyVec<T, I, TRACK> {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ShrinkPolicy;

    #[test]
    fn basic() {
        let mut v: AppendOnlyVec<_, usize, true> = AppendOnlyVec::new();
        v.push(10);
        v.push(20);
        assert_eq!(v.len(), 2);
        assert_eq!(*v.get(0), 10);
        assert_eq!(*v.get(1), 20);
    }

    #[test]
    fn mark_restore() {
        let mut v: AppendOnlyVec<_, usize, true> = AppendOnlyVec::new();
        v.push(1);
        let t = v.mark(ShrinkPolicy::Never);
        v.push(2);
        v.push(3);
        assert_eq!(v.len(), 3);
        v.restore(t);
        assert_eq!(v.len(), 1);
        assert_eq!(*v.get(0), 1);
    }

    #[test]
    fn nested_marks() {
        let mut v: AppendOnlyVec<_, usize, true> = AppendOnlyVec::new();
        v.push(1);
        let t1 = v.mark(ShrinkPolicy::Never);
        v.push(2);
        let t2 = v.mark(ShrinkPolicy::Never);
        v.push(3);
        v.push(4);
        assert_eq!(v.len(), 4);
        v.restore(t2);
        assert_eq!(v.len(), 2);
        v.push(5);
        assert_eq!(*v.get(2), 5);
        v.restore(t1);
        assert_eq!(v.len(), 1);
    }

    #[test]
    #[should_panic(expected = "abandoned future")]
    fn invalidated_token() {
        let mut v: AppendOnlyVec<_, usize, true> = AppendOnlyVec::new();
        v.push(1);
        let t1 = v.mark(ShrinkPolicy::Never);
        v.push(2);
        let t2 = v.mark(ShrinkPolicy::Never);
        v.push(3);
        v.restore(t1);
        v.restore(t2);
    }

    #[test]
    #[should_panic(expected = "different container")]
    fn wrong_container() {
        let mut v1: AppendOnlyVec<i32, usize, true> = AppendOnlyVec::new();
        let mut v2: AppendOnlyVec<i32, usize, true> = AppendOnlyVec::new();
        let t = v1.mark(ShrinkPolicy::Never);
        v2.push(1);
        v2.restore(t);
    }

    // -- Index width --

    /// `u8` indices admit 255 elements, not 256: the guard is on the new length, so
    /// the last valid index is 254 and `u8::MAX` stays free as a sentinel.
    #[test]
    fn narrow_index_reaches_exactly_max_elements() {
        let mut v: AppendOnlyVec<u16, u8, true> = AppendOnlyVec::new();
        for i in 0..255u16 {
            assert_eq!(v.push(i), i as u8);
        }
        assert_eq!(v.len(), 255u8);
        assert_eq!(*v.get(254), 254);
    }

    #[test]
    #[should_panic(expected = "append-only vec is full")]
    fn narrow_index_overflow_panics_instead_of_wrapping() {
        let mut v: AppendOnlyVec<u16, u8, true> = AppendOnlyVec::new();
        for i in 0..256u16 {
            v.push(i);
        }
    }

    /// Frames hold `I`, so mark/restore has to survive the narrow word too.
    #[test]
    fn narrow_index_mark_restore() {
        let mut v: AppendOnlyVec<u16, u8, true> = AppendOnlyVec::new();
        for i in 0..200u16 {
            v.push(i);
        }
        let t = v.mark(ShrinkPolicy::Never);
        for i in 200..254u16 {
            v.push(i);
        }
        assert_eq!(v.len(), 254u8);
        v.restore(t);
        assert_eq!(v.len(), 200u8);
        assert_eq!(*v.get(199), 199);
    }

    #[test]
    fn u32_index_is_a_narrower_frame_stack() {
        let mut v: AppendOnlyVec<&str, u32, true> = AppendOnlyVec::new();
        let a = v.push("a");
        let t = v.mark(ShrinkPolicy::Never);
        let b = v.push("b");
        assert_eq!((a, b), (0u32, 1u32));
        v.restore(t);
        assert_eq!(v.len(), 1u32);
    }
}
