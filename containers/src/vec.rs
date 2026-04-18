// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
use super::diff_store::DiffStore;
use super::token::{ContainerId, ForkHistory, Frame, VecToken};
use crate::IndexLike;

/// Capacity reclamation policy applied at mark time.
#[derive(Clone, Copy, Debug)]
pub enum ShrinkPolicy {
    Never,
    IfOverallocated { factor: usize, headroom: usize },
}

/// Semi-persistent vector: O(1) snapshots, O(k) restoration.
///
/// - `T` — value type (only `Clone` required, to keep the container general)
/// - `I` — index type (controls capacity and diff entry size)
/// - `S` — storage backend (`InlineStore` or `ParallelStore`)
/// - `TRACK` — compile out all tracking when false
///
/// The `Clone` bound allows this container to work with any value type,
/// including heap-owning types like `String` or `Vec`. For performance-
/// critical paths, use `InlineStore` (via `VecI`), which requires `Tagged`
/// and therefore `Copy` — see [`Tagged`] for rationale.
pub struct Vec<T, I: IndexLike, S, const TRACK: bool = true> {
    store: S,
    diff_log: std::vec::Vec<(T, I)>,
    frames: std::vec::Vec<Frame>,
    active_saved_len: I,
    forks: ForkHistory,
    id: ContainerId,
}

impl<T: Clone, I: IndexLike, S: DiffStore<T, I, TRACK>, const TRACK: bool> Vec<T, I, S, TRACK> {
    pub fn with_store(store: S) -> Self {
        Self {
            store,
            diff_log: std::vec::Vec::new(),
            frames: std::vec::Vec::new(),
            active_saved_len: I::MIN,
            forks: ForkHistory::new(),
            id: ContainerId::new(),
        }
    }

    pub fn len(&self) -> I {
        self.store.len()
    }

    pub fn is_empty(&self) -> bool {
        self.store.len() == I::MIN
    }

    pub fn push(&mut self, value: T) {
        self.store.push(value);
    }

    pub fn pop(&mut self) -> Option<T> {
        if self.is_empty() {
            return None;
        }
        let i = I::try_from_usize(self.store.len().as_usize() - 1).expect("underflow");
        let value = self.store.get(i);
        if TRACK && !self.frames.is_empty() {
            self.store
                .force_capture(i, self.active_saved_len, &mut self.diff_log);
        }
        self.store.pop();
        Some(value)
    }

    pub fn set(&mut self, index: impl Into<I>, value: T) {
        let i = index.into();
        assert!(
            i.as_usize() < self.store.len().as_usize(),
            "index out of bounds"
        );
        if TRACK && !self.frames.is_empty() {
            self.store
                .capture(i, self.active_saved_len, &mut self.diff_log);
        }
        self.store.set_raw(i, value);
    }

    pub fn get(&self, index: impl Into<I>) -> T {
        self.store.get(index.into())
    }

    pub fn view(&self) -> View<'_, T, I, S, TRACK> {
        View {
            store: &self.store,
            len: self.store.len(),
            _phantom: core::marker::PhantomData,
        }
    }

    pub fn as_slice(&self) -> Option<&[T]> {
        self.store.as_slice()
    }

    pub fn mark(&mut self, shrink: ShrinkPolicy) -> VecToken {
        assert!(TRACK, "mark() called on untracked vec");
        self.maybe_shrink(shrink);

        let saved_len = self.store.len();
        let diff_start = self.frames.last().map_or(0, |f| f.diff_start as usize);
        self.store
            .prepare_mark(saved_len, &self.diff_log[diff_start..]);

        let token = VecToken {
            branch_id: self.forks.current_branch(),
            depth: self.frames.len() as u32,
            frame_index: self.frames.len() as u32,
            container_id: self.id,
        };

        self.frames.push(Frame {
            saved_len: saved_len.as_usize() as u32,
            diff_start: self.diff_log.len() as u32,
        });
        self.active_saved_len = saved_len;
        token
    }

    pub fn restore(&mut self, token: VecToken) {
        assert!(TRACK, "restore() called on untracked vec");
        assert_eq!(
            token.container_id, self.id,
            "token belongs to a different container"
        );
        assert!(
            self.forks.is_valid(&token, self.frames.len() as u32),
            "invalid restore token (abandoned future)"
        );

        let target_index = token.frame_index as usize;
        assert!(
            target_index < self.frames.len(),
            "token points beyond frame stack"
        );

        let target_frame = self.frames[target_index];
        let saved_len =
            I::try_from_usize(target_frame.saved_len as usize).expect("saved_len overflow");
        let diff_start = target_frame.diff_start as usize;

        self.store.truncate(saved_len);

        for i in (diff_start..self.diff_log.len()).rev() {
            let (ref old_val, idx) = self.diff_log[i];
            self.store.restore_entry(idx, old_val, saved_len);
        }

        self.diff_log.truncate(diff_start);
        self.frames.truncate(target_index);

        let surviving_start = if target_index > 0 {
            self.frames[target_index - 1].diff_start as usize
        } else {
            0
        };
        let surviving_saved = if target_index > 0 {
            I::try_from_usize(self.frames[target_index - 1].saved_len as usize).expect("overflow")
        } else {
            I::MIN
        };

        self.store
            .finish_restore(&self.diff_log[surviving_start..], surviving_saved);

        self.active_saved_len = if let Some(f) = self.frames.last() {
            I::try_from_usize(f.saved_len as usize).expect("overflow")
        } else {
            I::MIN
        };

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

    /// Total bytes used by this Vec: struct + store + diff_log + frames + forks.
    pub fn total_bytes(&self) -> usize {
        core::mem::size_of::<Self>() + self.store.heap_bytes() + self.tracking_bytes()
    }

    /// Bytes consumed by diff tracking only: diff_log + frames + fork history.
    pub fn tracking_bytes(&self) -> usize {
        self.diff_log.capacity() * core::mem::size_of::<(T, I)>()
            + self.frames.capacity() * core::mem::size_of::<Frame>()
            + self.forks.heap_bytes()
    }

    fn maybe_shrink(&mut self, policy: ShrinkPolicy) {
        match policy {
            ShrinkPolicy::Never => {}
            ShrinkPolicy::IfOverallocated { factor, headroom } => {
                self.store.shrink_if(factor, headroom);
                if self.diff_log.capacity() > factor * self.diff_log.len() {
                    self.diff_log.shrink_to(headroom * self.diff_log.len());
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// View / ViewIter
// ---------------------------------------------------------------------------

pub struct View<'a, T: Clone, I: IndexLike, S: DiffStore<T, I, TRACK>, const TRACK: bool> {
    store: &'a S,
    len: I,
    _phantom: core::marker::PhantomData<(T, I)>,
}

impl<T: Clone, I: IndexLike, S: DiffStore<T, I, TRACK>, const TRACK: bool>
    View<'_, T, I, S, TRACK>
{
    pub fn len(&self) -> I {
        self.len
    }
    pub fn is_empty(&self) -> bool {
        self.len == I::MIN
    }
    pub fn get(&self, i: I) -> T {
        self.store.get(i)
    }
    pub fn iter(&self) -> ViewIter<'_, T, I, S, TRACK> {
        ViewIter {
            store: self.store,
            pos: 0,
            len: self.len.as_usize(),
            _phantom: core::marker::PhantomData,
        }
    }
}

pub struct ViewIter<'a, T: Clone, I: IndexLike, S: DiffStore<T, I, TRACK>, const TRACK: bool> {
    store: &'a S,
    pos: usize,
    len: usize,
    _phantom: core::marker::PhantomData<(T, I)>,
}

impl<T: Clone, I: IndexLike, S: DiffStore<T, I, TRACK>, const TRACK: bool> Iterator
    for ViewIter<'_, T, I, S, TRACK>
{
    type Item = T;
    fn next(&mut self) -> Option<T> {
        if self.pos >= self.len {
            return None;
        }
        let i = I::try_from_usize(self.pos).expect("overflow");
        self.pos += 1;
        Some(self.store.get(i))
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        let rem = self.len - self.pos;
        (rem, Some(rem))
    }
}

impl<T: Clone, I: IndexLike, S: DiffStore<T, I, TRACK>, const TRACK: bool> ExactSizeIterator
    for ViewIter<'_, T, I, S, TRACK>
{
}

// ---------------------------------------------------------------------------
// Constructors
// ---------------------------------------------------------------------------

use super::diff_store::{InlineStore, ParallelStore};
use super::tagged::Tagged;

impl<T: Clone, I: IndexLike, const TRACK: bool> Default for Vec<T, I, ParallelStore<T, I>, TRACK> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T: Clone, I: IndexLike, const TRACK: bool> Vec<T, I, ParallelStore<T, I>, TRACK> {
    pub fn new() -> Self {
        Self::with_store(ParallelStore::new())
    }
}

impl<T: Tagged, I: IndexLike, const TRACK: bool> Default for Vec<T, I, InlineStore<T, I>, TRACK> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T: Tagged, I: IndexLike, const TRACK: bool> Vec<T, I, InlineStore<T, I>, TRACK> {
    pub fn new() -> Self {
        Self::with_store(InlineStore::new())
    }
}
