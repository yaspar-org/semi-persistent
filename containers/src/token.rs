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

/// Narrow a frame-stack or fork-history length into the `u32` a [`VecToken`] field
/// holds. Panics rather than wrapping.
///
/// The token is a by-value handle and its `depth`/`frame_index` are `u32` on purpose:
/// they count *nested* marks and forks, a quantity bounded by control-flow depth rather
/// than by data size, so the ceiling is nowhere near any real workload and widening the
/// fields would grow every copied token for nothing.
///
/// Reaching that ceiling silently is a different matter, and is why this is checked. A
/// wrapped `depth` compares as *shallower* than it truly is, so
/// [`ForkHistory::is_valid`] would accept a token belonging to an abandoned future and
/// `restore` would replay a diff range that no longer describes the store — a stale
/// token validating as fresh, which is the one failure this whole module exists to
/// prevent. A wrapped `branch_id` aliases two branches onto one identity, with the same
/// consequence.
#[inline]
pub(crate) fn narrow_count(n: usize, what: &'static str) -> u32 {
    #[cold]
    #[inline(never)]
    fn exceeded(n: usize, what: &'static str) -> ! {
        panic!("{what} reached {n}, which a u32 token field cannot address");
    }
    match u32::try_from(n) {
        Ok(v) => v,
        Err(_) => exceeded(n, what),
    }
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
        self.current_branch_id = narrow_count(self.origins.len(), "fork history depth");
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
