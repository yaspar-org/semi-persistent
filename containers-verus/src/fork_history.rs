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

/// Operational definition of token validity (the production `is_valid` walk;
/// design doc §0.6 gives the declarative characterization). Walk from `branch`
/// following `parent` edges:
///   - if `branch == token_branch`: result is `token_depth <= current_depth`;
///   - else if `branch == 0`: `token_branch` is not on the path from the start
///     branch to the root — result `false`;
///   - else let `origin = origins[branch - 1]`. If `origin.parent_branch_id ==
///     token_branch`, result is `token_depth <= origin.fork_depth` (the bound
///     `token_branch` is cut to along this path); otherwise recurse on
///     `origin.parent_branch_id`.
///
/// `current_depth` is consulted only at the `branch == token_branch` case
/// (reached only when the start branch equals `token_branch`, since the walk
/// otherwise stops at the parent test). `decreases branch`; sound under
/// `fh_wf` (`parent < branch`), kept total by the explicit `parent >= branch`
/// guard below.
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

// ===========================================================================
// Branch-safety characterization. Pure lemmas over `fork_valid`/`fh_wf` (no
// `Vec`). These are specific INSTANCES of the general branch-safety theorem
// (design doc §0.6, §2.1); the general theorem over arbitrary current paths is
// not yet proved.
// ===========================================================================

/// Current-branch case: a token whose branch IS the current branch satisfies
/// `fork_valid` iff its depth is `<= current_depth`. (The first arm of
/// `fork_walk`.)
pub proof fn lemma_fork_valid_current_branch(
    origins: Seq<ForkOrigin>, current_branch_id: nat, current_depth: nat,
    token_depth: nat,
)
    ensures
        fork_valid(origins, current_branch_id, current_depth,
            current_branch_id, token_depth)
            == (token_depth <= current_depth),
{
    // fork_walk's first arm fires immediately: branch == token_branch.
}

/// Single-cut instance of the branch-safety theorem (§0.6). Models the state
/// immediately after `fork(cut_branch, cut_depth)`: `origins2` is `origins`
/// with one origin `(cut_branch, cut_depth)` appended, and the current branch
/// is the new origin's index `origins.len() + 1`.
///
/// Conclusion: a token whose branch is `cut_branch` satisfies `fork_valid`
/// (against this post-fork state) iff `token_depth <= cut_depth`:
///   - `token_depth <= cut_depth`  → valid: `cut_branch` is the parent of the
///     new current branch (on the current path), and `cut_depth` is its bound
///     (= the fork_depth of its on-path child), so the token is at or below
///     the bound;
///   - `token_depth >  cut_depth`  → invalid: a position on `cut_branch`
///     strictly deeper than the recorded bound.
///
/// Scope: this covers ONLY a token on the just-cut branch in the
/// single-origin-appended state. It does NOT establish the general theorem
/// (strict-grandparent branches, off-path rejection, multi-cut states); see
/// §2.1.
pub proof fn lemma_branch_cut(
    origins: Seq<ForkOrigin>, cut_branch: nat, cut_depth: nat,
    new_current_depth: nat, token_depth: nat,
)
    requires
        fh_wf(origins, cut_branch),         // cut_branch is a real branch
        cut_branch <= origins.len(),
        origins.len() + 1 <= u32::MAX,
        cut_depth < u32::MAX,               // depths are u32 (token.depth)
    ensures
        ({
            let origins2 = origins.push(
                ForkOrigin { parent_branch_id: cut_branch as u32, fork_depth: cut_depth as u32 });
            let current2 = (origins.len() + 1) as nat;
            fork_valid(origins2, current2, new_current_depth, cut_branch, token_depth)
                == (token_depth <= cut_depth)
        }),
{
    // cut_branch <= origins.len() < u32::MAX and cut_depth < u32::MAX, so the
    // u32 casts round-trip.
    assert(cut_branch < u32::MAX);
    assert((cut_branch as u32) as nat == cut_branch);
    assert((cut_depth as u32) as nat == cut_depth);
    let origins2 = origins.push(
        ForkOrigin { parent_branch_id: cut_branch as u32, fork_depth: cut_depth as u32 });
    let current2 = (origins.len() + 1) as nat;
    // current2 == origins2.len(); current2 != cut_branch (cut_branch <= len <
    // len+1 == current2); origins2[current2 - 1] is the appended origin whose
    // parent IS cut_branch (== token_branch). So fork_walk takes the
    // "parent == token_branch" arm in one step: returns token_depth <= fork_depth.
    assert(origins2.len() == current2);
    assert(current2 != cut_branch);
    assert(current2 != 0);
    assert(current2 <= origins2.len());
    // Seq::push index: origins2[origins.len()] is the appended origin.
    assert(origins2[origins.len() as int]
        == ForkOrigin { parent_branch_id: cut_branch as u32, fork_depth: cut_depth as u32 });
    assert(current2 - 1 == origins.len());
    assert(origins2[current2 - 1].parent_branch_id == cut_branch as u32);
    assert(origins2[current2 - 1].fork_depth == cut_depth as u32);
    // Unfold fork_walk one step at current2: branch != token_branch, != 0,
    // <= len, and origins2[current2-1].parent == cut_branch == token_branch,
    // so it returns token_depth <= fork_depth == cut_depth.
    assert(fork_walk(origins2, current2, new_current_depth, cut_branch, token_depth)
        == (token_depth <= origins2[current2 - 1].fork_depth as nat));
    assert(fork_valid(origins2, current2, new_current_depth, cut_branch, token_depth)
        == (token_depth <= cut_depth));
}

} // verus!
