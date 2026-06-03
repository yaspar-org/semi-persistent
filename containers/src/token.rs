// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
use crate::IndexLike;
use std::sync::atomic::{AtomicU32, Ordering};

/// Opaque token returned by `mark()`, used to `backtrack()`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct VecToken {
    pub(crate) branch_id: u32,
    pub(crate) depth: u32,
    pub(crate) frame_index: u32,
    pub(crate) container_id: ContainerId,
}

/// Frame header stored on the frame stack.
///
/// `saved_len: I` matches the vector's index type, so vectors with `I = u64`
/// can grow past `u32::MAX` slots without truncation. `diff_start: usize`
/// indexes into the diff log (a `std::Vec`, so the `usize` domain is the
/// natural fit and is independent of `I`).
#[derive(Clone, Copy, Debug)]
pub(crate) struct Frame<I: IndexLike> {
    pub saved_len: I,
    pub diff_start: usize,
}

/// Unique identity for a `Vec` instance. Prevents using a token from one
/// vec on a different vec.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ContainerId(u32);

static NEXT_CONTAINER_ID: AtomicU32 = AtomicU32::new(1);

impl ContainerId {
    pub(crate) fn new() -> Self {
        Self(NEXT_CONTAINER_ID.fetch_add(1, Ordering::Relaxed))
    }
}

/// Tracks the branching genealogy for token validation.
#[derive(Clone, Debug)]
pub struct ForkHistory {
    current_branch_id: u32,
    origins: std::vec::Vec<ForkOrigin>,
}

#[derive(Clone, Copy, Debug)]
struct ForkOrigin {
    parent_branch_id: u32,
    fork_depth: u32,
}

impl ForkHistory {
    pub(crate) fn new() -> Self {
        Self {
            current_branch_id: 0,
            origins: std::vec::Vec::new(),
        }
    }

    pub(crate) fn current_branch(&self) -> u32 {
        self.current_branch_id
    }

    pub(crate) fn fork(&mut self, token: &VecToken, current_depth: u32) {
        self.origins.push(ForkOrigin {
            parent_branch_id: token.branch_id,
            fork_depth: token.depth,
        });
        self.current_branch_id = self.origins.len() as u32;
        let _ = current_depth;
    }

    pub(crate) fn is_valid(&self, token: &VecToken, current_depth: u32) -> bool {
        if token.branch_id == self.current_branch_id {
            return token.depth <= current_depth;
        }
        let mut branch = self.current_branch_id;
        while branch != token.branch_id {
            if branch == 0 {
                return false;
            }
            let origin = &self.origins[(branch - 1) as usize];
            if origin.parent_branch_id == token.branch_id {
                return token.depth <= origin.fork_depth;
            }
            branch = origin.parent_branch_id;
        }
        token.depth <= current_depth
    }

    pub(crate) fn heap_bytes(&self) -> usize {
        self.origins.capacity() * core::mem::size_of::<ForkOrigin>()
    }
}
