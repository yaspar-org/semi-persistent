// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Fork-history machinery for branch-cut safety.
//!
//! Faithful port of production's `ForkHistory` (`containers/src/token.rs`):
//! a `current_branch_id` plus a list of `(parent_branch_id, fork_depth)`
//! origins. Branch 0 is the root; branch `b ≥ 1` is `origins[b-1]`, forked off
//! `parent_branch_id` at depth `fork_depth`.
//!
//! Two layers (mirrors the M3b spec/exec split):
//!   - `fork_valid(...)` — a pure recursive spec defining token validity by
//!     walking from the current branch up the parent chain. `decreases branch`
//!     is sound because of the well-formedness invariant `fh_wf`:
//!     `origins[b-1].parent_branch_id < b`, so the parent id strictly drops.
//!   - `ForkHistory::is_valid` — the production while-loop, proved to compute
//!     exactly `fork_valid(...)`.
//!
//! See `doc/design/m5-fork-history-design.md`.

use vstd::prelude::*;

verus! {

/// One fork origin: branch `b ≥ 1` (i.e. `origins[b-1]`) was forked off
/// `parent_branch_id` at depth `fork_depth`.
#[derive(Clone, Copy)]
pub struct ForkOrigin {
    pub parent_branch_id: u32,
    pub fork_depth: u32,
}

/// Branching genealogy. `current_branch_id` is the live branch; `origins[b-1]`
/// describes branch `b`.
pub struct ForkHistory {
    pub current_branch_id: u32,
    pub origins: Vec<ForkOrigin>,
}

/// Well-formedness: every branch's parent id is strictly smaller than the
/// branch itself (so the validity walk strictly descends toward 0), and the
/// current branch id is a real branch (`<= origins.len()`).
pub open spec fn fh_wf(origins: Seq<ForkOrigin>, current_branch_id: nat) -> bool {
    &&& current_branch_id <= origins.len()
    &&& (forall|b: int| 1 <= b <= origins.len() ==>
            (#[trigger] origins[b - 1]).parent_branch_id < b)
}

/// Declarative token validity. Walk from `branch` up the parent chain:
///   - if `branch == token_branch`: valid iff `token_depth <= current_depth`
///     (the token is on the branch we're currently walking, whose live prefix
///     is bounded by `current_depth`);
///   - else if `branch == 0`: the token's branch is not an ancestor — invalid;
///   - else step to the parent. If that parent IS the token's branch, the
///     token sits just below the fork point, so it's valid iff
///     `token_depth <= fork_depth` of this origin.
///
/// `current_depth` is only consulted on the *first* branch (the current head);
/// the recursion threads it unchanged but it is only used at `branch ==
/// token_branch`. `decreases branch`, sound under `fh_wf`.
pub open spec fn fork_walk(
    origins: Seq<ForkOrigin>, branch: nat, current_depth: nat,
    token_branch: nat, token_depth: nat,
) -> bool
    decreases branch,
{
    if branch == token_branch {
        token_depth <= current_depth
    } else if branch == 0 {
        false
    } else if branch > origins.len() {
        // out of range: cannot happen under fh_wf with branch <= len, but the
        // spec must be total. Treat as invalid.
        false
    } else {
        let origin = origins[branch - 1];
        if origin.parent_branch_id == token_branch {
            token_depth <= origin.fork_depth
        } else if (origin.parent_branch_id as nat) >= branch {
            // Cannot happen under fh_wf (parent < branch); guard keeps the
            // recursion syntactically decreasing and the spec total.
            false
        } else {
            fork_walk(origins, origin.parent_branch_id as nat, current_depth,
                token_branch, token_depth)
        }
    }
}

/// Top-level validity: start the walk at the current branch.
pub open spec fn fork_valid(
    origins: Seq<ForkOrigin>, current_branch_id: nat, current_depth: nat,
    token_branch: nat, token_depth: nat,
) -> bool {
    fork_walk(origins, current_branch_id, current_depth, token_branch, token_depth)
}

impl ForkHistory {
    pub open spec fn wf(self) -> bool {
        fh_wf(self.origins@, self.current_branch_id as nat)
    }

    pub fn new() -> (r: ForkHistory)
        ensures
            r.wf(),
            r.current_branch_id == 0,
            r.origins@.len() == 0,
    {
        ForkHistory { current_branch_id: 0, origins: Vec::new() }
    }

    pub fn current_branch(&self) -> (b: u32)
        ensures b == self.current_branch_id,
    {
        self.current_branch_id
    }

    /// Record a fork: push origin `(token_branch, token_depth)` and advance the
    /// current branch to the new origin's index. Maintains `wf`.
    pub fn fork(&mut self, token_branch: u32, token_depth: u32)
        requires
            old(self).wf(),
            // The token's branch must be a real, smaller branch id so the new
            // origin keeps the parent-decreasing invariant. At a real restore
            // the token's branch is an ancestor (validity guarantees this);
            // here we require it directly.
            (token_branch as nat) <= old(self).origins@.len(),
            old(self).origins@.len() + 1 <= u32::MAX,
        ensures
            self.wf(),
            self.current_branch_id == self.origins@.len(),
            self.origins@.len() == old(self).origins@.len() + 1,
    {
        self.origins.push(ForkOrigin { parent_branch_id: token_branch, fork_depth: token_depth });
        self.current_branch_id = self.origins.len() as u32;
        proof {
            // New origin is at index len-1 (branch len); its parent is
            // token_branch <= old len < new len == branch. Older origins
            // unchanged.
            assert(forall|b: int| 1 <= b <= self.origins@.len() ==>
                (#[trigger] self.origins@[b - 1]).parent_branch_id < b);
        }
    }

    /// Production validity walk. Proved to compute `fork_valid(...)`.
    pub fn is_valid(&self, token_branch: u32, token_depth: u32, current_depth: u32) -> (r: bool)
        requires self.wf(),
        ensures
            r == fork_valid(self.origins@, self.current_branch_id as nat,
                current_depth as nat, token_branch as nat, token_depth as nat),
    {
        if token_branch == self.current_branch_id {
            return token_depth <= current_depth;
        }
        let mut branch: u32 = self.current_branch_id;
        // Loop invariant: walking from `branch` computes the same predicate as
        // walking from the start (the prefix we've descended never hit
        // token_branch and never reached 0).
        while branch != token_branch
            invariant
                self.wf(),
                branch <= self.origins@.len(),
                // the remaining walk from `branch` equals the whole walk.
                fork_walk(self.origins@, branch as nat, current_depth as nat,
                    token_branch as nat, token_depth as nat)
                    == fork_valid(self.origins@, self.current_branch_id as nat,
                        current_depth as nat, token_branch as nat, token_depth as nat),
            decreases branch,
        {
            if branch == 0 {
                return false;
            }
            let origin = self.origins[(branch - 1) as usize];
            if origin.parent_branch_id == token_branch {
                return token_depth <= origin.fork_depth;
            }
            proof {
                // fh_wf: parent < branch, so the walk strictly descends, and
                // unfolding fork_walk at `branch` (≠ token_branch, ≠ 0,
                // ≤ len, parent ≠ token_branch) steps to the parent — keeping
                // the invariant.
                assert(origin.parent_branch_id < branch);
            }
            branch = origin.parent_branch_id;
        }
        token_depth <= current_depth
    }
}

} // verus!
