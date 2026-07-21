// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Push-only semi-persistent vector.
//!
//! Mark saves the current length. Restore truncates back to it.
//! No diff log — data is never overwritten, only appended.

use super::token::{ContainerId, ForkHistory, VecToken};

/// Push-only vec with semi-persistent mark/restore.
///
/// `TRACK=false` compiles out all fork history and frame tracking.
pub struct AppendOnlyVec<T, const TRACK: bool = true> {
    data: Vec<T>,
    frames: Vec<usize>,
    forks: ForkHistory,
    id: ContainerId,
}

impl<T, const TRACK: bool> AppendOnlyVec<T, TRACK> {
    pub fn new() -> Self {
        Self {
            data: Vec::new(),
            frames: Vec::new(),
            forks: ForkHistory::new(),
            id: ContainerId::new(),
        }
    }

    pub fn push(&mut self, val: T) -> usize {
        let id = self.data.len();
        self.data.push(val);
        id
    }

    #[inline]
    pub fn get(&self, idx: usize) -> &T {
        &self.data[idx]
    }

    #[inline]
    pub fn get_mut(&mut self, idx: usize) -> &mut T {
        &mut self.data[idx]
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.data.len()
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

    pub fn mark(&mut self, shrink: super::ShrinkPolicy) -> VecToken {
        assert!(TRACK, "mark() called on untracked AppendOnlyVec");
        if let super::ShrinkPolicy::IfOverallocated { factor, headroom } = shrink {
            let cap = self.data.capacity();
            let len = self.data.len();
            if cap > len * factor + headroom {
                self.data.shrink_to(len + headroom);
            }
        }
        let token = VecToken {
            branch_id: self.forks.current_branch(),
            depth: self.frames.len() as u32,
            frame_index: self.frames.len() as u32,
            container_id: self.id,
        };
        self.frames.push(self.data.len());
        token
    }

    pub fn restore(&mut self, token: VecToken) {
        assert!(TRACK, "restore() called on untracked AppendOnlyVec");
        self.validate_token(&token);
        let target = token.frame_index as usize;
        let saved_len = self.frames[target];
        self.data.truncate(saved_len);
        self.frames.truncate(target);
        self.forks.fork(&token, self.frames.len() as u32);
    }

    pub fn depth(&self) -> usize {
        self.frames.len()
    }

    pub fn is_valid_token(&self, token: &VecToken) -> bool {
        TRACK
            && token.container_id == self.id
            && self.forks.is_valid(token, self.frames.len() as u32)
    }

    fn validate_token(&self, token: &VecToken) {
        assert_eq!(
            token.container_id, self.id,
            "token belongs to a different container"
        );
        assert!(
            self.forks.is_valid(token, self.frames.len() as u32),
            "invalid token (abandoned future)"
        );
        assert!(
            (token.frame_index as usize) < self.frames.len(),
            "token points beyond frame stack"
        );
    }
}

impl<T: std::fmt::Debug, const TRACK: bool> std::fmt::Debug for AppendOnlyVec<T, TRACK> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("AppendOnlyVec")
            .field("len", &self.data.len())
            .field("depth", &self.frames.len())
            .finish()
    }
}

impl<T, const TRACK: bool> Default for AppendOnlyVec<T, TRACK> {
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
        let mut v: AppendOnlyVec<_, true> = AppendOnlyVec::new();
        v.push(10);
        v.push(20);
        assert_eq!(v.len(), 2);
        assert_eq!(*v.get(0), 10);
        assert_eq!(*v.get(1), 20);
    }

    #[test]
    fn mark_restore() {
        let mut v: AppendOnlyVec<_, true> = AppendOnlyVec::new();
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
        let mut v: AppendOnlyVec<_, true> = AppendOnlyVec::new();
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
        let mut v: AppendOnlyVec<_, true> = AppendOnlyVec::new();
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
        let mut v1: AppendOnlyVec<i32, true> = AppendOnlyVec::new();
        let mut v2: AppendOnlyVec<i32, true> = AppendOnlyVec::new();
        let t = v1.mark(ShrinkPolicy::Never);
        v2.push(1);
        v2.restore(t);
    }
}
