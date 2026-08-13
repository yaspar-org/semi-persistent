// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Verified union-find over two semi-persistent columns (stage 1 of
//! `doc/future/egraph-wf.md`: W1 as a machine-checked invariant).
//!
//! `parent` and `rank` are verified `Vec`s over `InlineStore`, production's
//! `VecI` columns (`egraph/src/union_find.rs`). The abstract state is a ghost
//! root map `roots@: Seq<usize>` — each element's canonical representative —
//! plus a ghost measure `dist@: Seq<nat>`, the element's path length to its
//! root. The physical parent column is a cache of `roots@`, tied to it by
//! `uf_model_wf`:
//!
//!   - roots are canonical (`roots[roots[i]] == roots[i]`) and self-parented;
//!   - a parent step preserves the root;
//!   - a self-parent is a root;
//!   - `dist` is 0 exactly at roots and strictly decreases along a parent
//!     step — W1's acyclicity in the form a `decreases` clause consumes, so
//!     `find` terminates without rank arithmetic.
//!
//! `find` compresses by path halving: each visited node's parent is rewritten
//! to its grandparent, and the ghost `dist[cur]` is rewritten to
//! `dist[grandparent] + 1`, which is strictly below the old `dist[cur]`, so
//! edges into `cur` keep decreasing and the invariant survives each write
//! locally. `union` attaches the absorbed root under the survivor and remaps
//! the ghost roots in one `Seq::new` (`merge_roots`). The rank bump saturates
//! at `u8::MAX` instead of carrying the `rank <= log2(n)` argument: rank is a
//! survivor-selection heuristic and no `wf` clause reads its value.
//!
//! Semi-persistence composes from the two columns the way `ListArena`'s does
//! from its two arenas (list.rs, Phase 7): one mark pushes one frame on each
//! column and archives the ghost `(roots, dist)` pair; restore prevalidates
//! both tokens, rolls both columns back, and reinstates the archived pair.
//! Production's `PROOFS=true` columns (proof forest, justifications) are
//! metadata with no bearing on W1-W6; they are postponed until a consumer
//! needs `explain` from verified code.

use vstd::prelude::*;

use crate::index_like::IndexLike;
use crate::inline_store::InlineStore;
use crate::opt::DenseId;
use crate::vec::{ShrinkPolicy, Vec as SpVec, VecToken};

verus! {

/// Token bundling the two column tokens (mirrors `ListArenaToken`).
#[derive(Copy, Clone)]
pub struct UnionFindToken {
    pub(crate) parent: VecToken,
    pub(crate) rank: VecToken,
}

impl UnionFindToken {
    pub open(crate) spec fn parent_frame_idx_spec(self) -> nat {
        self.parent.frame_idx as nat
    }

    pub open(crate) spec fn rank_frame_idx_spec(self) -> nat {
        self.rank.frame_idx as nat
    }
}

/// The root map after `ab`'s class is absorbed into `s`'s.
pub open(crate) spec fn merge_roots(roots: Seq<usize>, s: nat, ab: nat) -> Seq<usize> {
    Seq::new(roots.len(), |i: int| if roots[i] == ab as usize { s as usize } else { roots[i] })
}

/// The union-find model invariant over bare sequences, so the mark/restore
/// archive can assert it of archived snapshots (the `arena_model_wf` pattern).
pub open(crate) spec fn uf_model_wf<T: DenseId>(
    parent: Seq<T>, roots: Seq<usize>, dist: Seq<nat>,
) -> bool {
    let n = parent.len();
    &&& n <= T::id_bound()
    &&& roots.len() == n
    &&& dist.len() == n
    // every root value and every parent target is allocated
    &&& (forall|i: int| 0 <= i < n ==> (#[trigger] roots[i]) < n)
    &&& (forall|i: int| 0 <= i < n ==> (#[trigger] parent[i]).id_nat() < n)
    // roots are canonical and self-parented
    &&& (forall|i: int| 0 <= i < n ==> roots[(#[trigger] roots[i]) as int] == roots[i])
    &&& (forall|i: int| 0 <= i < n ==> #[trigger] parent_root_self_parent_clause(parent, roots, i))
    // a parent step preserves the root
    &&& (forall|i: int| 0 <= i < n
            ==> roots[(#[trigger] parent[i]).id_nat() as int] == roots[i])
    // a self-parent is a root
    &&& (forall|i: int| 0 <= i < n ==> #[trigger] parent_self_root_clause(parent, roots, i))
    // dist: 0 exactly at roots, strictly decreasing along a parent step (W1)
    &&& (forall|i: int| 0 <= i < n ==> ((#[trigger] roots[i]) == i as usize ==> dist[i] == 0))
    &&& (forall|i: int| 0 <= i < n
            ==> ((#[trigger] parent[i]).id_nat() != i as nat
                ==> dist[parent[i].id_nat() as int] < dist[i]))
}

/// Archive agreement (Phase 7): each frame's archived `(roots, dist)` pair
/// describes that frame's column snapshots. Opaque for the same reason as
/// `arena_archive_agrees` (list.rs): its nested quantifiers would join every
/// wf-requiring proof's matching context; ops preserve it by congruence
/// because they preserve `snapshots_view`.
#[verifier::opaque]
pub open(crate) spec fn uf_archive_agrees<T: DenseId>(
    roots_archive: Seq<Seq<usize>>,
    dist_archive: Seq<Seq<nat>>,
    parent_snaps: Seq<Seq<T>>,
    rank_snaps: Seq<Seq<u8>>,
) -> bool {
    &&& roots_archive.len() == parent_snaps.len()
    &&& dist_archive.len() == parent_snaps.len()
    &&& rank_snaps.len() == parent_snaps.len()
    &&& (forall|k: int| 0 <= k < parent_snaps.len()
            ==> uf_model_wf(#[trigger] parent_snaps[k], roots_archive[k], dist_archive[k]))
    &&& (forall|k: int| 0 <= k < parent_snaps.len()
            ==> (#[trigger] rank_snaps[k]).len() == parent_snaps[k].len())
}

/// Verified union-find (production parity: the `PROOFS=false` column set of
/// `egraph/src/union_find.rs`).
pub struct UnionFind<T: DenseId, const TRACK: bool> {
    pub(crate) parent: SpVec<T, T::Index, InlineStore<T, T::Index>, TRACK>,
    pub(crate) rank: SpVec<u8, T::Index, InlineStore<u8, T::Index>, TRACK>,
    /// Ghost root map: `roots@[i]` is `i`'s canonical representative.
    pub(crate) roots: Ghost<Seq<usize>>,
    /// Ghost path-length measure (0 at roots, strictly decreasing toward them).
    pub(crate) dist: Ghost<Seq<nat>>,
    /// Ghost archives, parallel to the columns' snapshot stacks.
    pub(crate) roots_snapshots: Ghost<Seq<Seq<usize>>>,
    pub(crate) dist_snapshots: Ghost<Seq<Seq<nat>>>,
}

impl<T: DenseId, const TRACK: bool> UnionFind<T, TRACK> {
    pub open(crate) spec fn parent_view(&self) -> Seq<T> {
        self.parent.view()
    }

    pub open(crate) spec fn rank_view(&self) -> Seq<u8> {
        self.rank.view()
    }

    /// Element count (spec).
    pub open(crate) spec fn n_spec(&self) -> nat {
        self.parent.view().len()
    }

    /// The abstract state: the canonical-root map.
    pub open(crate) spec fn roots_view(&self) -> Seq<usize> {
        self.roots@
    }

    /// `i`'s canonical representative (spec).
    pub open(crate) spec fn root_of(&self, i: int) -> usize {
        self.roots@[i]
    }

    /// Two elements are equivalent iff they share a root.
    pub open(crate) spec fn same_set_spec(&self, a: int, b: int) -> bool {
        self.roots@[a] == self.roots@[b]
    }

    pub open(crate) spec fn parent_depth_spec(&self) -> nat {
        self.parent.depth_spec()
    }

    pub open(crate) spec fn rank_depth_spec(&self) -> nat {
        self.rank.depth_spec()
    }

    pub open(crate) spec fn parent_snapshots_view(&self) -> Seq<Seq<T>> {
        self.parent.snapshots_view()
    }

    pub open(crate) spec fn rank_snapshots_view(&self) -> Seq<Seq<u8>> {
        self.rank.snapshots_view()
    }

    pub open(crate) spec fn roots_snapshots_view(&self) -> Seq<Seq<usize>> {
        self.roots_snapshots@
    }

    pub open(crate) spec fn dist_snapshots_view(&self) -> Seq<Seq<nat>> {
        self.dist_snapshots@
    }

    pub open(crate) spec fn is_token_valid_spec(&self, token: UnionFindToken) -> bool {
        &&& self.parent.is_token_valid_spec(token.parent)
        &&& self.rank.is_token_valid_spec(token.rank)
    }

    pub open(crate) spec fn is_restorable_spec(&self, token: UnionFindToken) -> bool {
        &&& self.parent.is_restorable_spec(token.parent)
        &&& self.rank.is_restorable_spec(token.rank)
    }

    /// Composite restore preconditions (mirrors `ListArena::restore_pre_spec`).
    pub open(crate) spec fn restore_pre_spec(&self, token: UnionFindToken) -> bool {
        &&& self.parent.is_token_valid_spec(token.parent)
        &&& token.parent.frame_idx_spec() < self.parent.depth_spec()
        &&& self.parent.depth_spec() < u32::MAX
        &&& self.parent.fork_count_spec() + 1 <= u32::MAX
        &&& self.rank.is_token_valid_spec(token.rank)
        &&& token.rank.frame_idx_spec() < self.rank.depth_spec()
        &&& self.rank.depth_spec() < u32::MAX
        &&& self.rank.fork_count_spec() + 1 <= u32::MAX
    }

    pub open(crate) spec fn wf(&self) -> bool {
        &&& self.parent.wf()
        &&& self.rank.wf()
        &&& self.rank_view().len() == self.n_spec()
        &&& uf_model_wf(self.parent_view(), self.roots@, self.dist@)
        &&& uf_archive_agrees(self.roots_snapshots@, self.dist_snapshots@,
                self.parent.snapshots_view(), self.rank.snapshots_view())
    }

    pub fn new() -> (u: Self)
        ensures u.wf(), u.n_spec() == 0, u.roots_view().len() == 0,
            u.parent_depth_spec() == 0,
    {
        let u = UnionFind {
            parent: SpVec::<T, T::Index, InlineStore<T, T::Index>, TRACK>::new(),
            rank: SpVec::<u8, T::Index, InlineStore<u8, T::Index>, TRACK>::new(),
            roots: Ghost(Seq::empty()),
            dist: Ghost(Seq::empty()),
            roots_snapshots: Ghost(Seq::empty()),
            dist_snapshots: Ghost(Seq::empty()),
        };
        proof { reveal(uf_archive_agrees); }
        u
    }

    /// Element count as the column's index word (production's `len`).
    pub fn len(&self) -> (n: T::Index)
        requires self.wf(),
        ensures n.as_nat() == self.n_spec(),
    {
        self.parent.len()
    }

    pub fn is_empty(&self) -> (b: bool)
        requires self.wf(),
        ensures b == (self.n_spec() == 0),
    {
        let n = self.parent.len();
        n.as_usize() == 0
    }

    /// Allocate the next element as its own singleton class and return its
    /// id (`Err(CapacityExhausted)` at the id range's end). Production's
    /// `make_set(id)` demands the caller supply `id == len` and asserts it;
    /// minting here removes that misuse channel.
    pub fn try_make_set(&mut self) -> (r: Result<T, crate::error::ContainerError>)
        requires old(self).wf(),
        ensures
            final(self).wf(),
            r matches Ok(id) ==> {
                &&& id.id_nat() == old(self).n_spec()
                &&& final(self).n_spec() == old(self).n_spec() + 1
                &&& final(self).roots_view()
                    == old(self).roots_view().push(old(self).n_spec() as usize)
                &&& final(self).rank_view() == old(self).rank_view().push(0u8)
                &&& final(self).parent_snapshots_view() == old(self).parent_snapshots_view()
                &&& final(self).rank_snapshots_view() == old(self).rank_snapshots_view()
                &&& final(self).roots_snapshots_view() == old(self).roots_snapshots_view()
                &&& final(self).dist_snapshots_view() == old(self).dist_snapshots_view()
            },
            r is Err ==> *final(self) == *old(self),
            r matches Err(e) ==> e == crate::error::ContainerError::CapacityExhausted,
    {
        let n = self.parent.len().as_usize();
        proof {
            assert(n as nat == self.n_spec());
        }
        // Reject-before-mutate: the fresh id must be representable AND its
        // usize successor must exist (the full-range family's id_bound is
        // usize::MAX + 1, where `n < id_bound` alone leaves `n + 1` at the
        // wrap).
        if n == usize::MAX {
            return Err(crate::error::ContainerError::CapacityExhausted);
        }
        let id = match T::try_new(n) {
            Some(id) => id,
            None => {
                return Err(crate::error::ContainerError::CapacityExhausted);
            }
        };
        // Word headroom differs by family: a bit-stealing id has
        // `max_nat == 2 * id_bound`, so `n < id_bound` already leaves word
        // room; a full-range id has `max_nat == id_bound`, so the successor
        // must be representable too or the column word is exactly full.
        if !T::bit_stealing() && T::try_new(n + 1).is_none() {
            return Err(crate::error::ContainerError::CapacityExhausted);
        }
        proof {
            T::lemma_id_bound_word_relation();
            if T::is_bit_stealing() {
                assert(T::id_bound() >= 1);
                assert(T::id_bound() * 2 >= T::id_bound() + 1) by (nonlinear_arith)
                    requires T::id_bound() >= 1;
            }
            assert(self.n_spec() + 1 < <T::Index as IndexLike>::max_nat());
        }
        let ghost old_roots = self.roots@;
        let ghost old_dist = self.dist@;
        self.parent.push(id);
        self.rank.push(0u8);
        self.roots = Ghost(self.roots@.push(n));
        self.dist = Ghost(self.dist@.push(0));
        proof {
            let pv = self.parent_view();
            let roots = self.roots@;
            let dist = self.dist@;
            let nn = pv.len() as int;
            assert(pv[n as int] == id);
            assert(id.id_nat() == n as nat);
            assert(roots[n as int] == n);
            assert(dist[n as int] == 0);
            assert forall|i: int| 0 <= i < nn implies (#[trigger] roots[i]) < nn as nat by {
                if i < n as int { assert(roots[i] == old_roots[i]); }
            }
            assert forall|i: int| 0 <= i < nn implies (#[trigger] pv[i]).id_nat() < nn as nat by {
                if i < n as int { assert(pv[i] == old(self).parent_view()[i]); }
            }
            let opv = old(self).parent_view();
            assert forall|i: int| 0 <= i < nn implies
                roots[(#[trigger] roots[i]) as int] == roots[i] by {
                if i < n as int {
                    assert(roots[i] == old_roots[i]);
                    assert(old_roots[i] < n as nat);
                }
            }
            assert forall|i: int| 0 <= i < nn implies
                #[trigger] parent_root_self_parent_clause(pv, roots, i) by {
                if i < n as int {
                    assert(parent_root_self_parent_clause(opv, old_roots, i));
                    assert(roots[i] == old_roots[i]);
                    assert(old_roots[i] < n as nat);
                    assert(pv[roots[i] as int] == opv[roots[i] as int]);
                }
            }
            assert forall|i: int| 0 <= i < nn implies
                roots[(#[trigger] pv[i]).id_nat() as int] == roots[i] by {
                if i < n as int {
                    assert(pv[i] == opv[i]);
                    assert(pv[i].id_nat() < n as nat);
                    assert(roots[i] == old_roots[i]);
                }
            }
            assert forall|i: int| 0 <= i < nn implies
                #[trigger] parent_self_root_clause(pv, roots, i) by {
                if i < n as int {
                    assert(parent_self_root_clause(opv, old_roots, i));
                    assert(pv[i] == opv[i]);
                    assert(roots[i] == old_roots[i]);
                }
            }
            assert forall|i: int| 0 <= i < nn && (#[trigger] roots[i]) == i as usize
                implies dist[i] == 0 by {
                if i < n as int {
                    assert(roots[i] == old_roots[i]);
                    assert(dist[i] == old_dist[i]);
                }
            }
            assert forall|i: int| 0 <= i < nn && (#[trigger] pv[i]).id_nat() != i as nat
                implies dist[pv[i].id_nat() as int] < dist[i] by {
                if i < n as int {
                    assert(pv[i] == opv[i]);
                    assert(pv[i].id_nat() < n as nat);
                    assert(dist[i] == old_dist[i]);
                }
            }
            assert(uf_model_wf(pv, roots, dist));
        }
        Ok(id)
    }

    /// Canonical representative of `x`, read-only (no compression):
    /// production's `find_const`. Total-with-documented-panic: an
    /// out-of-range id refuses.
    pub fn find_const(&self, x: T) -> (r: T)
        requires self.wf(),
        ensures
            x.id_nat() < self.n_spec() ==> {
                &&& r.id_nat() == self.roots_view()[x.id_nat() as int] as nat
                &&& r.id_nat() < self.n_spec()
            },
    {
        if !(x.to_usize() < self.parent.len().as_usize()) {
            crate::guard::refuse("UnionFind::find_const: id out of range");
        }
        let ghost n = self.n_spec();
        let ghost roots = self.roots@;
        let mut cur = x;
        loop
            invariant
                self.wf(),
                cur.id_nat() < n,
                n == self.n_spec(),
                roots == self.roots@,
                x.id_nat() < n,
                self.roots@[cur.id_nat() as int] == self.roots@[x.id_nat() as int],
            decreases self.dist@[cur.id_nat() as int],
        {
            let p = self.parent.get_index(cur.to_index());
            proof {
                assert(p == self.parent_view()[cur.id_nat() as int]);
                assert(p.id_nat() < n);
            }
            if p.to_usize() == cur.to_usize() {
                proof {
                    T::lemma_id_injective(p, cur);
                    crate::opt::lemma_id_nat_fits_usize(cur);
                    // self-parent is a root; the root of the walk is x's root.
                    assert(parent_self_root_clause(
                        self.parent_view(), self.roots@, cur.id_nat() as int));
                    assert(self.parent_view()[cur.id_nat() as int].id_nat() == cur.id_nat());
                    assert(self.roots@[cur.id_nat() as int] == cur.id_nat() as usize);
                    assert(cur.id_nat() == self.roots@[x.id_nat() as int] as nat);
                }
                return cur;
            }
            proof {
                // measure decreases along the parent step
                assert(p.id_nat() != cur.id_nat());
                assert(self.dist@[p.id_nat() as int] < self.dist@[cur.id_nat() as int]);
            }
            cur = p;
        }
    }

    /// Canonical representative of `x`, compressing by path halving.
    /// Total-with-documented-panic: an out-of-range id refuses. The abstract
    /// state (`roots_view`) is unchanged — compression rewrites the cache,
    /// not the partition.
    pub fn find(&mut self, x: T) -> (r: T)
        requires old(self).wf(),
        ensures
            final(self).wf(),
            final(self).n_spec() == old(self).n_spec(),
            final(self).rank_view() == old(self).rank_view(),
            final(self).rank_snapshots_view() == old(self).rank_snapshots_view(),
            final(self).rank_depth_spec() == old(self).rank_depth_spec(),
            final(self).roots_view() == old(self).roots_view(),
            final(self).parent_snapshots_view() == old(self).parent_snapshots_view(),
            final(self).roots_snapshots_view() == old(self).roots_snapshots_view(),
            final(self).dist_snapshots_view() == old(self).dist_snapshots_view(),
            x.id_nat() < old(self).n_spec() ==> {
                &&& r.id_nat() == old(self).roots_view()[x.id_nat() as int] as nat
                &&& r.id_nat() < old(self).n_spec()
            },
    {
        if !(x.to_usize() < self.parent.len().as_usize()) {
            crate::guard::refuse("UnionFind::find: id out of range");
        }
        let ghost n = old(self).n_spec();
        let mut cur = x;
        loop
            invariant
                self.wf(),
                self.n_spec() == n,
                n == old(self).n_spec(),
                self.rank == old(self).rank,
                self.rank.wf(),
                self.roots@ == old(self).roots@,
                self.roots_snapshots@ == old(self).roots_snapshots@,
                self.dist_snapshots@ == old(self).dist_snapshots@,
                self.parent.snapshots_view() == old(self).parent.snapshots_view(),
                cur.id_nat() < n,
                x.id_nat() < n,
                self.roots@[cur.id_nat() as int] == self.roots@[x.id_nat() as int],
            decreases self.dist@[cur.id_nat() as int],
        {
            let p = self.parent.get_index(cur.to_index());
            proof {
                assert(p == self.parent_view()[cur.id_nat() as int]);
                assert(p.id_nat() < n);
            }
            if p.to_usize() == cur.to_usize() {
                proof {
                    T::lemma_id_injective(p, cur);
                    crate::opt::lemma_id_nat_fits_usize(cur);
                    assert(parent_self_root_clause(
                        self.parent_view(), self.roots@, cur.id_nat() as int));
                    assert(self.parent_view()[cur.id_nat() as int].id_nat() == cur.id_nat());
                    assert(self.roots@[cur.id_nat() as int] == cur.id_nat() as usize);
                }
                return cur;
            }
            proof { assert(p.id_nat() != cur.id_nat()); }
            let g = self.parent.get_index(p.to_index());
            proof {
                assert(g == self.parent_view()[p.id_nat() as int]);
                assert(g.id_nat() < n);
                // g != cur: otherwise dist[cur] < dist[p] < dist[cur] (when
                // p is not self-parented) — and p != cur here.
                if g.id_nat() == cur.id_nat() {
                    if p.id_nat() != g.id_nat() {
                        assert(self.dist@[g.id_nat() as int] < self.dist@[p.id_nat() as int]);
                        assert(self.dist@[p.id_nat() as int] < self.dist@[cur.id_nat() as int]);
                        assert(false);
                    } else {
                        // p self-parented would make p a root == cur's parent;
                        // then parent[p] == p == g == cur contradicts p != cur.
                        assert(false);
                    }
                }
            }
            proof {
                crate::opt::lemma_id_nat_fits_usize(cur);
                crate::opt::lemma_id_nat_fits_usize(p);
                crate::opt::lemma_id_nat_fits_usize(g);
            }
            let ghost pre = *self;
            // the halving write: parent[cur] := grandparent
            self.parent.set_index(cur.to_index(), g);
            self.dist = Ghost(self.dist@.update(
                cur.id_nat() as int, self.dist@[g.id_nat() as int] + 1));
            proof {
                let pv = self.parent_view();
                let opv = pre.parent_view();
                let roots = self.roots@;
                let dist = self.dist@;
                let odist = pre.dist@;
                let ci = cur.id_nat() as int;
                let pi = p.id_nat() as int;
                let gi = g.id_nat() as int;
                assert(pv == opv.update(ci, g));
                assert(dist == odist.update(ci, odist[gi] + 1));
                // cur is not a root (its parent differs), so no dist-zero or
                // root-self-parent clause is disturbed, and cur is not any
                // element's root value.
                assert(roots[ci] != cur.id_nat() as usize) by {
                    if roots[ci] == cur.id_nat() as usize {
                        // root self-parent at i = ci contradicts p != cur
                        assert(opv[ci].id_nat() == cur.id_nat());
                    }
                }
                assert forall|i: int| 0 <= i < n implies
                    (#[trigger] roots[i]) != cur.id_nat() as usize by {
                    if roots[i] == cur.id_nat() as usize {
                        // roots are canonical: roots[roots[i]] == roots[i],
                        // so cur would be its own root — refuted above.
                        assert(roots[ci] == roots[i]);
                    }
                }
                // dist[g] + 1 <= old dist[cur]: through p when g != p, or
                // dist[p] == 0 when p == g (p a root).
                assert(odist[gi] + 1 <= odist[ci]) by {
                    if g.id_nat() == p.id_nat() {
                        assert(opv[pi].id_nat() == p.id_nat());
                        assert(parent_self_root_clause(opv, roots, pi));
                        assert(roots[pi] == p.id_nat() as usize);
                        assert(odist[pi] == 0);
                        assert(odist[ci] >= 1);
                    } else {
                        assert(odist[gi] < odist[pi]);
                        assert(odist[pi] < odist[ci]);
                    }
                }
                // re-establish the model invariant clause by clause
                assert forall|i: int| 0 <= i < n implies (#[trigger] pv[i]).id_nat() < n by {
                    if i != ci { assert(pv[i] == opv[i]); }
                }
                assert forall|i: int| 0 <= i < n implies
                    parent_self_root_clause(pv, roots, i) by {
                    if i != ci {
                        assert(pv[i] == opv[i]);
                        assert(parent_self_root_clause(opv, roots, i));
                    } else {
                        // pv[ci] == g, and g != cur, so the clause is vacuous.
                        assert(pv[ci] == g);
                        assert(pv[ci].id_nat() != ci as nat);
                    }
                }
                assert forall|i: int| 0 <= i < n implies
                    roots[(#[trigger] pv[i]).id_nat() as int] == roots[i] by {
                    if i != ci {
                        assert(pv[i] == opv[i]);
                    } else {
                        // two steps: roots[g] == roots[p] == roots[cur]
                        assert(roots[gi] == roots[pi]);
                        assert(roots[pi] == roots[ci]);
                    }
                }
                assert forall|i: int| 0 <= i < n implies
                    parent_root_self_parent_clause(pv, roots, i) by {
                    // pv changed only at ci, and no roots[i] equals cur's id.
                    assert(roots[i] != cur.id_nat() as usize);
                    assert(pv[roots[i] as int] == opv[roots[i] as int]);
                }
                assert forall|i: int| 0 <= i < n && (#[trigger] roots[i]) == i as usize
                    implies dist[i] == 0 by {
                    assert(i != ci);
                    assert(dist[i] == odist[i]);
                }
                assert forall|i: int| 0 <= i < n && (#[trigger] pv[i]).id_nat() != i as nat
                    implies dist[pv[i].id_nat() as int] < dist[i] by {
                    {
                        if i == ci {
                            // new edge cur -> g: dist[g] unchanged, new
                            // dist[cur] is dist[g] + 1.
                            assert(dist[gi] == odist[gi]);
                            assert(dist[ci] == odist[gi] + 1);
                        } else if opv[i].id_nat() == cur.id_nat() {
                            // an edge into cur: its head's dist shrank.
                            assert(dist[ci] <= odist[ci]);
                            assert(odist[ci] < odist[i]);
                            assert(dist[i] == odist[i]);
                        } else {
                            assert(pv[i] == opv[i]);
                            assert(dist[pv[i].id_nat() as int]
                                == odist[opv[i].id_nat() as int]);
                            assert(dist[i] == odist[i]);
                        }
                    }
                }
                assert(uf_model_wf(pv, roots, dist));
                // archive agreement: snapshots unchanged, congruence.
                assert(self.parent.snapshots_view() == pre.parent.snapshots_view());
            }
            proof {
                // the measure decreases: dist[g] is unchanged by the update
                // (g != cur) and was strictly below dist[cur].
                assert(self.dist@[g.id_nat() as int] < pre.dist@[cur.id_nat() as int]);
            }
            cur = g;
        }
    }

    /// Attach root `ab`'s class under root `s` (the link step of union).
    pub(crate) fn link(&mut self, s: T, ab: T)
        requires
            old(self).wf(),
            s.id_nat() < old(self).n_spec(),
            ab.id_nat() < old(self).n_spec(),
            old(self).roots_view()[s.id_nat() as int] as nat == s.id_nat(),
            old(self).roots_view()[ab.id_nat() as int] as nat == ab.id_nat(),
            s.id_nat() != ab.id_nat(),
        ensures
            final(self).wf(),
            final(self).n_spec() == old(self).n_spec(),
            final(self).rank_view() == old(self).rank_view(),
            final(self).rank_snapshots_view() == old(self).rank_snapshots_view(),
            final(self).rank_depth_spec() == old(self).rank_depth_spec(),
            final(self).roots_view()
                == merge_roots(old(self).roots_view(), s.id_nat(), ab.id_nat()),
            final(self).parent_snapshots_view() == old(self).parent_snapshots_view(),
            final(self).roots_snapshots_view() == old(self).roots_snapshots_view(),
            final(self).dist_snapshots_view() == old(self).dist_snapshots_view(),
    {
        let ghost n = old(self).n_spec();
        let ghost oroots = old(self).roots@;
        let ghost odist = old(self).dist@;
        let ghost opv = old(self).parent_view();
        let ghost si = s.id_nat() as int;
        let ghost abi = ab.id_nat() as int;
        proof {
            crate::opt::lemma_id_nat_fits_usize(ab);
            crate::opt::lemma_id_nat_fits_usize(s);
            T::lemma_id_bound_fits_usize();
            assert(old(self).n_spec() <= usize::MAX as nat + 1);
        }
        self.parent.set_index(ab.to_index(), s);
        self.roots = Ghost(merge_roots(oroots, s.id_nat(), ab.id_nat()));
        self.dist = Ghost(Seq::new(odist.len(),
            |i: int| if oroots[i] == ab.id_nat() as usize { odist[i] + 1 } else { odist[i] }));
        proof {
            let pv = self.parent_view();
            let roots = self.roots@;
            let dist = self.dist@;
            assert(pv == opv.update(abi, s));
            // s's class is untouched by the remap: roots[s] == s != ab.
            assert(oroots[si] != ab.id_nat() as usize);
            assert(roots[si] == s.id_nat() as usize);
            assert(roots[abi] == s.id_nat() as usize);
            // ab was a root, so dist[ab] was 0 and the new dist[ab] is 1;
            // s stays a root with dist 0.
            assert(odist[abi] == 0);
            assert(dist[abi] == 1);
            assert(dist[si] == 0);

            assert forall|i: int| 0 <= i < n implies (#[trigger] roots[i]) < n by {
                if oroots[i] == ab.id_nat() as usize {} else { assert(roots[i] == oroots[i]); }
            }
            assert forall|i: int| 0 <= i < n implies (#[trigger] pv[i]).id_nat() < n by {
                if i != abi { assert(pv[i] == opv[i]); }
            }
            assert forall|i: int| 0 <= i < n implies
                roots[(#[trigger] roots[i]) as int] == roots[i] by {
                if oroots[i] == ab.id_nat() as usize {
                    assert(roots[i] == s.id_nat() as usize);
                } else {
                    assert(roots[i] == oroots[i]);
                    assert(oroots[roots[i] as int] == oroots[i]);
                    assert(oroots[roots[i] as int] != ab.id_nat() as usize
                        || oroots[i] == ab.id_nat() as usize);
                }
            }
            assert forall|i: int| 0 <= i < n implies
                parent_root_self_parent_clause(pv, roots, i) by {
                if oroots[i] == ab.id_nat() as usize {
                    // new root is s, which is not ab, so its parent cell is
                    // untouched and s was self-parented as a root.
                    assert(roots[i] == s.id_nat() as usize);
                    assert(pv[si] == opv[si]);
                    assert(opv[si].id_nat() == s.id_nat());
                } else {
                    assert(roots[i] == oroots[i]);
                    assert(oroots[i] != ab.id_nat() as usize);
                    assert(pv[roots[i] as int] == opv[roots[i] as int]);
                }
            }
            assert forall|i: int| 0 <= i < n implies
                roots[(#[trigger] pv[i]).id_nat() as int] == roots[i] by {
                if i == abi {
                    assert(pv[i] == s);
                } else {
                    assert(pv[i] == opv[i]);
                    // old equality remaps identically on both sides.
                    assert(oroots[opv[i].id_nat() as int] == oroots[i]);
                }
            }
            assert forall|i: int| 0 <= i < n implies
                parent_self_root_clause(pv, roots, i) by {
                if pv[i].id_nat() == i as nat {
                    if i == abi {
                        // pv[abi] == s and s != ab: the antecedent refutes.
                        assert(pv[abi] == s);
                        assert(s.id_nat() == ab.id_nat());
                        assert(false);
                    }
                    assert(pv[i] == opv[i]);
                    assert(parent_self_root_clause(opv, oroots, i));
                    assert(oroots[i] == i as usize);
                    // i is an old root other than ab, so its class is not
                    // ab's and the remap leaves it fixed.
                    assert(oroots[i] != ab.id_nat() as usize);
                }
            }
            assert forall|i: int| 0 <= i < n && (#[trigger] roots[i]) == i as usize
                implies dist[i] == 0 by {
                {
                    if oroots[i] == ab.id_nat() as usize {
                        // then roots[i] == s, so i == s — but oroots[s] == s != ab.
                        assert(i == si);
                        assert(false);
                    }
                    assert(oroots[i] == i as usize);
                    assert(dist[i] == odist[i]);
                }
            }
            assert forall|i: int| 0 <= i < n && (#[trigger] pv[i]).id_nat() != i as nat
                implies dist[pv[i].id_nat() as int] < dist[i] by {
                {
                    if i == abi {
                        assert(dist[si] == 0 && dist[abi] == 1);
                    } else {
                        assert(pv[i] == opv[i]);
                        let pi = opv[i].id_nat() as int;
                        assert(oroots[pi] == oroots[i]);
                        if oroots[i] == ab.id_nat() as usize {
                            assert(dist[pi] == odist[pi] + 1);
                            assert(dist[i] == odist[i] + 1);
                            assert(odist[pi] < odist[i]);
                        } else {
                            assert(dist[pi] == odist[pi]);
                            assert(dist[i] == odist[i]);
                        }
                    }
                }
            }
            assert(uf_model_wf(pv, roots, dist));
        }
    }

    /// Union by rank: merge `a`'s and `b`'s classes, returning
    /// `Some((survivor_root, absorbed_root))`, or `None` if they were already
    /// one class. Total-with-documented-panic on out-of-range ids.
    pub fn union(&mut self, a: T, b: T) -> (r: Option<(T, T)>)
        requires old(self).wf(),
        ensures
            final(self).wf(),
            final(self).n_spec() == old(self).n_spec(),
            final(self).parent_snapshots_view() == old(self).parent_snapshots_view(),
            final(self).rank_snapshots_view() == old(self).rank_snapshots_view(),
            final(self).roots_snapshots_view() == old(self).roots_snapshots_view(),
            final(self).dist_snapshots_view() == old(self).dist_snapshots_view(),
            a.id_nat() < old(self).n_spec() && b.id_nat() < old(self).n_spec() ==> {
                let ra = old(self).roots_view()[a.id_nat() as int] as nat;
                let rb = old(self).roots_view()[b.id_nat() as int] as nat;
                &&& (r is None <==> ra == rb)
                &&& (r is None ==> final(self).roots_view() == old(self).roots_view())
                &&& (r matches Some((s, ab)) ==> {
                        &&& ((s.id_nat() == ra && ab.id_nat() == rb)
                            || (s.id_nat() == rb && ab.id_nat() == ra))
                        &&& ra != rb
                        &&& final(self).roots_view()
                            == merge_roots(old(self).roots_view(), s.id_nat(), ab.id_nat())
                    })
            },
    {
        if !(a.to_usize() < self.parent.len().as_usize()
            && b.to_usize() < self.parent.len().as_usize())
        {
            crate::guard::refuse("UnionFind::union: id out of range");
        }
        let ra = self.find(a);
        let rb = self.find(b);
        if ra.to_usize() == rb.to_usize() {
            proof { T::lemma_id_injective(ra, rb); }
            return None;
        }
        proof {
            assert(ra.id_nat() != rb.id_nat());
            // find's postcondition + canonicity: both are roots.
            assert(self.roots@[ra.id_nat() as int] as nat == ra.id_nat());
            assert(self.roots@[rb.id_nat() as int] as nat == rb.id_nat());
        }
        let rank_a = self.rank.get_index(ra.to_index());
        let rank_b = self.rank.get_index(rb.to_index());
        let (s, ab) = if rank_a < rank_b { (rb, ra) } else { (ra, rb) };
        if rank_a == rank_b && rank_a < 255u8 {
            // saturating bump; no wf clause reads rank values.
            self.rank.set_index(s.to_index(), rank_a + 1);
        }
        self.link(s, ab);
        Some((s, ab))
    }

    /// Directed union: the survivor is `a`'s root when `prefer_a`, else
    /// `b`'s (production's `union_directed`, used by the parent-count
    /// survivor policy). Rank is left untouched.
    pub fn union_directed(&mut self, a: T, b: T, prefer_a: bool) -> (r: Option<(T, T)>)
        requires old(self).wf(),
        ensures
            final(self).wf(),
            final(self).n_spec() == old(self).n_spec(),
            final(self).rank_view() == old(self).rank_view(),
            final(self).parent_snapshots_view() == old(self).parent_snapshots_view(),
            final(self).rank_snapshots_view() == old(self).rank_snapshots_view(),
            final(self).roots_snapshots_view() == old(self).roots_snapshots_view(),
            final(self).dist_snapshots_view() == old(self).dist_snapshots_view(),
            a.id_nat() < old(self).n_spec() && b.id_nat() < old(self).n_spec() ==> {
                let ra = old(self).roots_view()[a.id_nat() as int] as nat;
                let rb = old(self).roots_view()[b.id_nat() as int] as nat;
                &&& (r is None <==> ra == rb)
                &&& (r is None ==> final(self).roots_view() == old(self).roots_view())
                &&& (r matches Some((s, ab)) ==> {
                        &&& s.id_nat() == (if prefer_a { ra } else { rb })
                        &&& ab.id_nat() == (if prefer_a { rb } else { ra })
                        &&& ra != rb
                        &&& final(self).roots_view()
                            == merge_roots(old(self).roots_view(), s.id_nat(), ab.id_nat())
                    })
            },
    {
        if !(a.to_usize() < self.parent.len().as_usize()
            && b.to_usize() < self.parent.len().as_usize())
        {
            crate::guard::refuse("UnionFind::union_directed: id out of range");
        }
        let ra = self.find(a);
        let rb = self.find(b);
        if ra.to_usize() == rb.to_usize() {
            proof { T::lemma_id_injective(ra, rb); }
            return None;
        }
        proof {
            assert(ra.id_nat() != rb.id_nat());
            assert(self.roots@[ra.id_nat() as int] as nat == ra.id_nat());
            assert(self.roots@[rb.id_nat() as int] as nat == rb.id_nat());
        }
        let (s, ab) = if prefer_a { (ra, rb) } else { (rb, ra) };
        self.link(s, ab);
        Some((s, ab))
    }

    // ---- semi-persistence: compose from the two columns (Phase 7) ----

    pub(crate) fn mark(&mut self, shrink: ShrinkPolicy) -> (token: UnionFindToken)
        requires
            old(self).wf(),
            TRACK,
            old(self).parent_depth_spec() < u32::MAX,
            old(self).rank_depth_spec() < u32::MAX,
        ensures
            final(self).wf(),
            final(self).parent_view() == old(self).parent_view(),
            final(self).rank_view() == old(self).rank_view(),
            final(self).roots_view() == old(self).roots_view(),
            token.parent_frame_idx_spec() == old(self).parent_depth_spec(),
            token.rank_frame_idx_spec() == old(self).rank_depth_spec(),
            final(self).parent_depth_spec() == old(self).parent_depth_spec() + 1,
            final(self).rank_depth_spec() == old(self).rank_depth_spec() + 1,
            final(self).roots_snapshots_view()
                == old(self).roots_snapshots_view().push(old(self).roots_view()),
            final(self).parent_snapshots_view()
                == old(self).parent_snapshots_view().push(old(self).parent_view()),
            token.parent_frame_idx_spec()
                == final(self).roots_snapshots_view().len() - 1,
    {
        let parent_tok = self.parent.mark(shrink);
        let rank_tok = self.rank.mark(shrink);
        self.roots_snapshots = Ghost(self.roots_snapshots@.push(self.roots@));
        self.dist_snapshots = Ghost(self.dist_snapshots@.push(self.dist@));
        proof {
            reveal(uf_archive_agrees);
            assert(uf_archive_agrees(old(self).roots_snapshots@, old(self).dist_snapshots@,
                old(self).parent.snapshots_view(), old(self).rank.snapshots_view()));
            let k_new = self.roots_snapshots@.len() - 1;
            assert(self.parent.snapshots_view()[k_new] == old(self).parent_view());
            assert(self.rank.snapshots_view()[k_new] == old(self).rank_view());
            assert(uf_model_wf(self.parent.snapshots_view()[k_new],
                self.roots_snapshots@[k_new], self.dist_snapshots@[k_new]));
            assert forall|k: int| 0 <= k < self.parent.snapshots_view().len()
                implies uf_model_wf(#[trigger] self.parent.snapshots_view()[k],
                    self.roots_snapshots@[k], self.dist_snapshots@[k]) by {
                if k < k_new {
                    assert(self.parent.snapshots_view()[k]
                        == old(self).parent.snapshots_view()[k]);
                    assert(self.roots_snapshots@[k] == old(self).roots_snapshots@[k]);
                    assert(self.dist_snapshots@[k] == old(self).dist_snapshots@[k]);
                }
            }
            assert forall|k: int| 0 <= k < self.parent.snapshots_view().len()
                implies (#[trigger] self.rank.snapshots_view()[k]).len()
                    == self.parent.snapshots_view()[k].len() by {
                if k < k_new {
                    assert(self.rank.snapshots_view()[k]
                        == old(self).rank.snapshots_view()[k]);
                    assert(self.parent.snapshots_view()[k]
                        == old(self).parent.snapshots_view()[k]);
                }
            }
            assert(uf_archive_agrees(self.roots_snapshots@, self.dist_snapshots@,
                self.parent.snapshots_view(), self.rank.snapshots_view()));
        }
        UnionFindToken { parent: parent_tok, rank: rank_tok }
    }

    /// Total mark (the composite of the two columns' `can_mark`).
    pub fn try_mark(&mut self, shrink: ShrinkPolicy)
        -> (r: Result<UnionFindToken, crate::error::ContainerError>)
        requires old(self).wf(),
        ensures
            final(self).wf(),
            r matches Ok(token) ==> {
                &&& final(self).roots_view() == old(self).roots_view()
                &&& final(self).parent_view() == old(self).parent_view()
                &&& token.parent_frame_idx_spec() == old(self).parent_depth_spec()
                &&& token.rank_frame_idx_spec() == old(self).rank_depth_spec()
                &&& final(self).roots_snapshots_view()
                    == old(self).roots_snapshots_view().push(old(self).roots_view())
                &&& final(self).parent_snapshots_view()
                    == old(self).parent_snapshots_view().push(old(self).parent_view())
                &&& token.parent_frame_idx_spec()
                    == final(self).roots_snapshots_view().len() - 1
            },
            r is Err ==> final(self).roots_view() == old(self).roots_view(),
    {
        if !TRACK {
            return Err(crate::error::ContainerError::Untracked);
        }
        if self.parent.can_mark() && self.rank.can_mark() {
            Ok(self.mark(shrink))
        } else {
            Err(crate::error::ContainerError::DepthLimit)
        }
    }

    /// "Restorable now" for the composite token.
    pub fn is_valid_token(&self, token: &UnionFindToken) -> (b: bool)
        requires self.wf(),
        ensures b == self.is_restorable_spec(*token),
    {
        self.parent.is_valid_token(&token.parent) && self.rank.is_valid_token(&token.rank)
    }

    pub(crate) fn restore(&mut self, token: UnionFindToken)
        requires
            old(self).wf(),
            TRACK,
            old(self).restore_pre_spec(token),
            token.parent_frame_idx_spec() == token.rank_frame_idx_spec(),
        ensures
            final(self).wf(),
            final(self).parent_view()
                == old(self).parent_snapshots_view()[token.parent_frame_idx_spec() as int],
            final(self).rank_view()
                == old(self).rank_snapshots_view()[token.rank_frame_idx_spec() as int],
            final(self).roots_view()
                == old(self).roots_snapshots_view()[token.parent_frame_idx_spec() as int],
            final(self).roots_snapshots_view() == old(self).roots_snapshots_view()
                .subrange(0, token.parent_frame_idx_spec() as int),
            final(self).parent_snapshots_view() == old(self).parent_snapshots_view()
                .subrange(0, token.parent_frame_idx_spec() as int),
    {
        // Atomic compound restore: prevalidate BOTH constituent tokens before
        // restoring either (a parent column rolled back without its rank
        // column desyncs the lengths unrecoverably), and pin the same-mark
        // frame agreement.
        crate::guard::check_precondition(
            self.is_valid_token(&token),
            "UnionFind::restore: invalid, foreign, stale, consumed, or abandoned token component",
        );
        crate::guard::check_precondition(
            token.parent.frame_idx == token.rank.frame_idx,
            "UnionFind::restore: token components name different marks",
        );
        let ghost f = token.parent.frame_idx as int;
        let ghost snap_roots = self.roots_snapshots@[f];
        let ghost snap_dist = self.dist_snapshots@[f];
        proof {
            reveal(uf_archive_agrees);
            assert(uf_archive_agrees(old(self).roots_snapshots@, old(self).dist_snapshots@,
                old(self).parent.snapshots_view(), old(self).rank.snapshots_view()));
        }
        self.parent.restore(token.parent);
        self.rank.restore(token.rank);
        self.roots = Ghost(snap_roots);
        self.dist = Ghost(snap_dist);
        self.roots_snapshots = Ghost(self.roots_snapshots@.subrange(0, f));
        self.dist_snapshots = Ghost(self.dist_snapshots@.subrange(0, f));
        proof {
            reveal(uf_archive_agrees);
            assert(uf_model_wf(old(self).parent.snapshots_view()[f], snap_roots, snap_dist));
            assert(self.parent_view() == old(self).parent.snapshots_view()[f]);
            assert(self.rank_view() == old(self).rank.snapshots_view()[f]);
            assert(self.parent.snapshots_view()
                =~= old(self).parent.snapshots_view().subrange(0, f));
            assert(self.rank.snapshots_view()
                =~= old(self).rank.snapshots_view().subrange(0, f));
            assert forall|k: int| 0 <= k < self.parent.snapshots_view().len()
                implies uf_model_wf(#[trigger] self.parent.snapshots_view()[k],
                    self.roots_snapshots@[k], self.dist_snapshots@[k]) by {
                assert(self.parent.snapshots_view()[k]
                    == old(self).parent.snapshots_view()[k]);
                assert(self.roots_snapshots@[k] == old(self).roots_snapshots@[k]);
                assert(self.dist_snapshots@[k] == old(self).dist_snapshots@[k]);
            }
            assert forall|k: int| 0 <= k < self.parent.snapshots_view().len()
                implies (#[trigger] self.rank.snapshots_view()[k]).len()
                    == self.parent.snapshots_view()[k].len() by {
                assert(self.rank.snapshots_view()[k] == old(self).rank.snapshots_view()[k]);
                assert(self.parent.snapshots_view()[k]
                    == old(self).parent.snapshots_view()[k]);
            }
            assert(uf_archive_agrees(self.roots_snapshots@, self.dist_snapshots@,
                self.parent.snapshots_view(), self.rank.snapshots_view()));
        }
    }

    /// Total restore: component restorability plus the same-mark frame
    /// agreement (a mixed token from two different marks refuses).
    pub fn try_restore(&mut self, token: UnionFindToken)
        -> (r: Result<(), crate::error::ContainerError>)
        requires old(self).wf(),
        ensures
            final(self).wf(),
            r is Ok ==> final(self).roots_view()
                == old(self).roots_snapshots_view()[token.parent_frame_idx_spec() as int]
                && final(self).roots_snapshots_view() == old(self).roots_snapshots_view()
                    .subrange(0, token.parent_frame_idx_spec() as int),
            r is Err ==> final(self).roots_view() == old(self).roots_view(),
            r matches Err(e) ==> e == crate::error::ContainerError::InvalidToken,
    {
        if self.is_valid_token(&token)
            && token.parent.frame_idx == token.rank.frame_idx
        {
            self.restore(token);
            Ok(())
        } else {
            Err(crate::error::ContainerError::InvalidToken)
        }
    }
}

/// The self-parent-is-root clause, named so `assert forall` blocks can state
/// it without re-triggering the whole conjunction.
pub open(crate) spec fn parent_self_root_clause<T: DenseId>(
    parent: Seq<T>, roots: Seq<usize>, i: int,
) -> bool {
    parent[i].id_nat() == i as nat ==> roots[i] == i as usize
}

/// The root-is-self-parented clause, same purpose.
pub open(crate) spec fn parent_root_self_parent_clause<T: DenseId>(
    parent: Seq<T>, roots: Seq<usize>, i: int,
) -> bool {
    parent[roots[i] as int].id_nat() == roots[i] as nat
}

} // verus!

// prod-parity: manual `Debug` (composes two `VecToken`s).
impl core::fmt::Debug for UnionFindToken {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("UnionFindToken")
            .field("parent", &self.parent)
            .field("rank", &self.rank)
            .finish()
    }
}
