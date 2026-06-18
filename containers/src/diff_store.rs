// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
use super::tagged::Tagged;
use crate::IndexLike;

/// Storage backend for semi-persistent vector.
///
/// `T` — value type, `I` — index type, `TRACK` — enable capture machinery.
/// Diff entries are `(T, I)` pairs (old value, index).
pub trait DiffStore<T: Clone, I: IndexLike, const TRACK: bool> {
    fn is_empty(&self) -> bool;
    fn len(&self) -> I;
    fn push(&mut self, value: T);
    fn pop(&mut self) -> Option<T>;
    fn get(&self, i: I) -> T;
    fn set_raw(&mut self, i: I, value: T);
    fn truncate(&mut self, len: I);

    // Capture protocol (no-ops when TRACK=false)
    fn prepare_mark(&mut self, saved_len: I, prev_diffs: &[(T, I)]);
    fn capture(&mut self, i: I, saved_len: I, diff_log: &mut Vec<(T, I)>);
    /// Mark slot `i` as already-captured without logging a diff entry.
    ///
    /// Used by `push` when re-entering a popped-but-already-captured marked
    /// slot, so a later `set` on that slot does not re-capture (first-write-wins).
    fn mark_captured(&mut self, i: I);
    fn restore_entry(&mut self, index: I, old_value: &T, target_saved_len: I);
    fn finish_restore(&mut self, current_frame_diffs: &[(T, I)], saved_len: I);

    /// Resize the backing store to exactly `len`, filling any grown slots with
    /// `T::default()`. Used by `restore` to regrow the popped region before the
    /// overwrite-only replay; the fillers are provably never observed (every
    /// regrown cell is overwritten by its captured diff value during replay).
    fn resize_default(&mut self, len: I)
    where
        T: Default;

    fn shrink_if(&mut self, factor: usize, headroom: usize);

    fn heap_bytes(&self) -> usize;

    fn as_slice(&self) -> Option<&[T]> {
        None
    }
}

// ---------------------------------------------------------------------------
// ParallelStore
// ---------------------------------------------------------------------------

/// SoA layout with parallel bitset. Full value range, O(N/64) mark.
pub struct ParallelStore<T, I: IndexLike = u32> {
    data: Vec<T>,
    captured: Vec<u64>,
    _phantom: core::marker::PhantomData<I>,
}

impl<T: Clone, I: IndexLike> Default for ParallelStore<T, I> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T: Clone, I: IndexLike> ParallelStore<T, I> {
    pub fn new() -> Self {
        Self {
            data: Vec::new(),
            captured: Vec::new(),
            _phantom: core::marker::PhantomData,
        }
    }

    #[inline(always)]
    fn is_bit_set(&self, i: usize) -> bool {
        let (w, b) = (i / 64, 1u64 << (i % 64));
        w < self.captured.len() && (self.captured[w] & b) != 0
    }

    #[inline(always)]
    fn set_bit(&mut self, i: usize) {
        let (w, b) = (i / 64, 1u64 << (i % 64));
        if w >= self.captured.len() {
            self.captured.resize(w + 1, 0);
        }
        self.captured[w] |= b;
    }
}

impl<T: Clone, I: IndexLike, const TRACK: bool> DiffStore<T, I, TRACK> for ParallelStore<T, I> {
    fn is_empty(&self) -> bool {
        self.data.is_empty()
    }

    fn len(&self) -> I {
        I::try_from_usize(self.data.len()).expect("len overflow")
    }

    fn push(&mut self, value: T) {
        self.data.push(value);
    }

    fn pop(&mut self) -> Option<T> {
        self.data.pop()
    }

    fn get(&self, i: I) -> T {
        self.data[i.as_usize()].clone()
    }

    fn set_raw(&mut self, i: I, value: T) {
        self.data[i.as_usize()] = value;
    }

    fn truncate(&mut self, len: I) {
        self.data.truncate(len.as_usize());
    }

    fn prepare_mark(&mut self, _saved_len: I, _prev_diffs: &[(T, I)]) {
        if !TRACK {
            return;
        }
        for w in self.captured.iter_mut() {
            *w = 0;
        }
        let needed = self.data.len().div_ceil(64);
        self.captured.resize(needed, 0);
    }

    fn capture(&mut self, i: I, saved_len: I, diff_log: &mut Vec<(T, I)>) {
        if !TRACK {
            return;
        }
        let iu = i.as_usize();
        if iu >= saved_len.as_usize() {
            return;
        }
        if !self.is_bit_set(iu) {
            self.set_bit(iu);
            diff_log.push((self.data[iu].clone(), i));
        }
    }

    fn mark_captured(&mut self, i: I) {
        if !TRACK {
            return;
        }
        self.set_bit(i.as_usize());
    }

    fn resize_default(&mut self, len: I)
    where
        T: Default,
    {
        let target = len.as_usize();
        if self.data.len() > target {
            self.data.truncate(target);
            self.captured.truncate(target.div_ceil(64));
        }
        while self.data.len() < target {
            self.data.push(T::default());
        }
    }

    fn restore_entry(&mut self, index: I, old_value: &T, target_saved_len: I) {
        let iu = index.as_usize();
        if iu >= target_saved_len.as_usize() {
            return;
        }
        if iu >= self.data.len() {
            debug_assert_eq!(iu, self.data.len());
            self.data.push(old_value.clone());
        } else {
            self.data[iu] = old_value.clone();
        }
    }

    fn finish_restore(&mut self, current_frame_diffs: &[(T, I)], _saved_len: I) {
        if !TRACK {
            return;
        }
        for w in self.captured.iter_mut() {
            *w = 0;
        }
        for (_, idx) in current_frame_diffs {
            let iu = idx.as_usize();
            if iu < self.data.len() {
                self.set_bit(iu);
            }
        }
    }

    fn shrink_if(&mut self, factor: usize, headroom: usize) {
        if self.data.capacity() > factor * self.data.len() {
            self.data.shrink_to(headroom * self.data.len());
            let needed = self.data.capacity().div_ceil(64);
            self.captured.truncate(needed);
        }
    }

    fn as_slice(&self) -> Option<&[T]> {
        Some(&self.data)
    }

    fn heap_bytes(&self) -> usize {
        self.data.capacity() * core::mem::size_of::<T>()
            + self.captured.capacity() * core::mem::size_of::<u64>()
    }
}

// ---------------------------------------------------------------------------
// InlineStore
// ---------------------------------------------------------------------------

/// Capture flag inside T::Repr. Zero overhead for bit-stealing types.
///
/// Requires `T: Tagged` (and therefore `T: Copy`) because the tag bit is
/// packed inline into each stored value. This is the preferred storage
/// mode for performance-critical data (node stores, use-lists, sparse sets)
/// where all values are small, copyable indices.
pub struct InlineStore<T: Tagged, I: IndexLike = u32> {
    data: Vec<T::Repr>,
    _phantom: core::marker::PhantomData<I>,
}

impl<T: Tagged, I: IndexLike> Default for InlineStore<T, I> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T: Tagged, I: IndexLike> InlineStore<T, I> {
    pub fn new() -> Self {
        Self {
            data: Vec::new(),
            _phantom: core::marker::PhantomData,
        }
    }
}

impl<T: Tagged, I: IndexLike, const TRACK: bool> DiffStore<T, I, TRACK> for InlineStore<T, I> {
    fn is_empty(&self) -> bool {
        self.data.is_empty()
    }

    fn len(&self) -> I {
        I::try_from_usize(self.data.len()).expect("len overflow")
    }

    fn push(&mut self, value: T) {
        self.data.push(value.into_repr());
    }

    fn pop(&mut self) -> Option<T> {
        self.data.pop().map(|s| T::from_repr(&s))
    }

    fn get(&self, i: I) -> T {
        T::from_repr(&self.data[i.as_usize()])
    }

    fn set_raw(&mut self, i: I, value: T) {
        let iu = i.as_usize();
        let was_captured = TRACK && T::tag(&self.data[iu]);
        self.data[iu] = value.into_repr();
        if was_captured {
            T::set_tag(&mut self.data[iu]);
        }
    }

    fn truncate(&mut self, len: I) {
        self.data.truncate(len.as_usize());
    }

    fn prepare_mark(&mut self, _saved_len: I, prev_diffs: &[(T, I)]) {
        if !TRACK {
            return;
        }
        for (_, idx) in prev_diffs {
            let iu = idx.as_usize();
            if iu < self.data.len() {
                T::clear_tag(&mut self.data[iu]);
            }
        }
    }

    fn capture(&mut self, i: I, saved_len: I, diff_log: &mut Vec<(T, I)>) {
        if !TRACK {
            return;
        }
        let iu = i.as_usize();
        if iu >= saved_len.as_usize() {
            return;
        }
        if !T::tag(&self.data[iu]) {
            diff_log.push((T::from_repr(&self.data[iu]), i));
            T::set_tag(&mut self.data[iu]);
        }
    }

    fn mark_captured(&mut self, i: I) {
        if !TRACK {
            return;
        }
        T::set_tag(&mut self.data[i.as_usize()]);
    }

    fn resize_default(&mut self, len: I)
    where
        T: Default,
    {
        let target = len.as_usize();
        if self.data.len() > target {
            self.data.truncate(target);
        }
        while self.data.len() < target {
            // Route the filler through `into_repr` so the stolen niche bit is
            // re-cleared for any in-domain default value (niche safety).
            self.data.push(T::default().into_repr());
        }
    }

    fn restore_entry(&mut self, index: I, old_value: &T, target_saved_len: I) {
        let iu = index.as_usize();
        if iu >= target_saved_len.as_usize() {
            return;
        }
        if iu >= self.data.len() {
            debug_assert_eq!(iu, self.data.len());
            self.data.push((*old_value).into_repr());
        } else {
            self.data[iu] = (*old_value).into_repr();
        }
    }

    fn finish_restore(&mut self, current_frame_diffs: &[(T, I)], _saved_len: I) {
        if !TRACK {
            return;
        }
        for (_, idx) in current_frame_diffs {
            let iu = idx.as_usize();
            if iu < self.data.len() {
                T::set_tag(&mut self.data[iu]);
            }
        }
    }

    fn shrink_if(&mut self, factor: usize, headroom: usize) {
        if self.data.capacity() > factor * self.data.len() {
            self.data.shrink_to(headroom * self.data.len());
        }
    }

    fn heap_bytes(&self) -> usize {
        self.data.capacity() * core::mem::size_of::<T::Repr>()
    }
}
