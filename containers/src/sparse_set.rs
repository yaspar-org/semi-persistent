// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Semi-persistent sparse set with stable IDs.
//!
//! Three internal vectors:
//! - `dense`: packed values, no gaps (store type configurable)
//! - `sparse`: id → position in dense (always InlineStore)
//! - `indices`: position → id (always InlineStore)

use crate::IndexLike;
use crate::tagged::Tagged;
use crate::{DiffStore, ShrinkPolicy, VecToken};

/// A restorable sparse set with stable IDs.
///
/// - `T` — element type
/// - `Idx` — index type (must be Tagged for sparse/indices)
/// - `S` — DiffStore for the dense array (user chooses inline vs parallel)
/// - `TRACK` — enable restoration
pub struct SparseSet<
    T: Clone,
    Idx: IndexLike + Tagged,
    S: DiffStore<T, Idx, TRACK>,
    const TRACK: bool = true,
> {
    dense: crate::Vec<T, Idx, S, TRACK>,
    sparse: crate::VecI<Idx, Idx, TRACK>,
    indices: crate::VecI<Idx, Idx, TRACK>,
}

impl<T: Clone, Idx: IndexLike + Tagged, S: DiffStore<T, Idx, TRACK>, const TRACK: bool>
    SparseSet<T, Idx, S, TRACK>
{
    pub fn with_store(store: S) -> Self {
        Self {
            dense: crate::Vec::with_store(store),
            sparse: crate::VecI::new(),
            indices: crate::VecI::new(),
        }
    }
}

/// Convenience: parallel dense store.
impl<T: Clone, Idx: IndexLike + Tagged, const TRACK: bool> Default
    for SparseSet<T, Idx, crate::ParallelStore<T, Idx>, TRACK>
{
    fn default() -> Self {
        Self::new()
    }
}

impl<T: Clone, Idx: IndexLike + Tagged, const TRACK: bool>
    SparseSet<T, Idx, crate::ParallelStore<T, Idx>, TRACK>
{
    pub fn new() -> Self {
        Self::with_store(crate::ParallelStore::new())
    }
}

/// Convenience: inline dense store.
impl<T: Tagged, Idx: IndexLike + Tagged, const TRACK: bool>
    SparseSet<T, Idx, crate::InlineStore<T, Idx>, TRACK>
{
    pub fn new_inline() -> Self {
        Self::with_store(crate::InlineStore::new())
    }
}

impl<T: Clone, Idx: IndexLike + Tagged, S: DiffStore<T, Idx, TRACK>, const TRACK: bool>
    SparseSet<T, Idx, S, TRACK>
{
    pub fn len(&self) -> Idx {
        self.dense.len()
    }

    pub fn is_empty(&self) -> bool {
        self.dense.is_empty()
    }

    pub fn add(&mut self, value: T) -> Idx {
        let pos = self.dense.len();
        self.dense.push(value);
        if pos.as_usize() < self.sparse.len().as_usize() {
            let recycled_id = self.indices.get(pos);
            self.sparse.set(recycled_id, pos);
            recycled_id
        } else {
            self.sparse.push(pos);
            self.indices.push(pos);
            pos
        }
    }

    /// Remove by key. Panics if not present.
    pub fn remove(&mut self, id: Idx) {
        assert!(self.contains(id), "SparseSet::remove: id not present");
        self.remove_inner(id);
    }

    /// Remove by value (linear scan). Panics if not present.
    pub fn remove_value(&mut self, value: &T)
    where
        T: PartialEq,
    {
        let len = self.dense.len().as_usize();
        for i in 0..len {
            let idx = Idx::try_from_usize(i).expect("overflow");
            if self.dense.get(idx) == *value {
                let id = self.indices.get(idx);
                self.remove_inner(id);
                return;
            }
        }
        panic!("SparseSet::remove_value: value not present");
    }

    fn remove_inner(&mut self, id: Idx) {
        let pos = self.sparse.get(id);
        let last_pos = Idx::try_from_usize(self.dense.len().as_usize() - 1).expect("underflow");

        if pos != last_pos {
            let last_id = self.indices.get(last_pos);
            let last_val = self.dense.get(last_pos);
            self.dense.set(pos, last_val);
            self.indices.set(pos, last_id);
            self.indices.set(last_pos, id);
            self.sparse.set(last_id, pos);
        }
        self.dense.pop();
    }

    pub fn contains(&self, id: Idx) -> bool {
        let su = id.as_usize();
        if su >= self.sparse.len().as_usize() {
            return false;
        }
        let pos = self.sparse.get(id);
        pos.as_usize() < self.dense.len().as_usize() && self.indices.get(pos) == id
    }

    pub fn get(&self, id: Idx) -> T {
        assert!(self.contains(id), "SparseSet::get: id not present");
        self.dense.get(self.sparse.get(id))
    }

    pub fn set(&mut self, id: Idx, value: T) {
        assert!(self.contains(id), "SparseSet::set: id not present");
        let pos = self.sparse.get(id);
        self.dense.set(pos, value);
    }

    pub fn data(&self) -> &crate::Vec<T, Idx, S, TRACK> {
        &self.dense
    }

    pub fn mark(&mut self, shrink: ShrinkPolicy) -> SparseSetToken {
        SparseSetToken {
            dense: self.dense.mark(shrink),
            sparse: self.sparse.mark(shrink),
            indices: self.indices.mark(shrink),
        }
    }

    pub fn restore(&mut self, token: SparseSetToken) {
        self.dense.restore(token.dense);
        self.sparse.restore(token.sparse);
        self.indices.restore(token.indices);
    }
}

#[derive(Clone, Copy, Debug)]
pub struct SparseSetToken {
    dense: VecToken,
    sparse: VecToken,
    indices: VecToken,
}
