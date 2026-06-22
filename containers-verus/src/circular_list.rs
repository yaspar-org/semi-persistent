// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Circular intrusive class-list with O(1) ring splicing (verified).
//!
//! This is the *class-membership* structure of the e-graph (production:
//! `egraph/src/classes.rs`, the `EClassEntry { next }` ring), NOT the parent
//! use-list `ListArena`. One vector `entries`, indexed by node id; each entry
//! carries a `next` pointer to the next node in the same equivalence class.
//!
//! ## The model: K disjoint rings (an explicit partition)
//!
//! The buffer decomposes into K **disjoint circular lists**. We carry that
//! structure as a ghost `model: Seq<Seq<usize>>`: `model[c]` is the node indices
//! of class `c`, in ring order, and the physical `next` pointer of a node is the
//! *successor in its ring, wrapping around* — `next[model[c][p]] ==
//! model[c][(p+1) mod len]`. The well-formedness invariant is exactly:
//!   - **in-range**: every `model[c][p] < n`;
//!   - **disjoint**: a node index appears in at most one ring at one position;
//!   - **covers**: every node `i < n` appears in some ring;
//!   - **cyclic**: the wrap-around `next` law above.
//! "Each class is a single cycle" is thus a *stored, maintained invariant*, not
//! something recovered by walking pointers — and "`next` is a permutation of
//! `[0, n)`" falls out as a free consequence (cyclic on each ring × the rings
//! partition `[0, n)`), rather than being assumed.
//!
//! ## What splice does
//!
//! `splice(s, a)` for `s`, `a` in **different** rings swaps `next[s]` and
//! `next[a]`. On the model this merges the two rings into one: the merged ring
//! is `rotate(ring_a, pos_a+1) ++ rotate(ring_s, pos_s+1)`, whose two seams are
//! exactly the two swapped edges and whose every other edge is an unchanged
//! interior link. We prove it preserves `wf` (so the merged result is again a
//! valid disjoint-ring partition) AND that `s` and `a` end up in one ring whose
//! node set is the union — the merge, with NO finite-cycle/pigeonhole side
//! condition. (The source ring slot is left empty: `model[ring_a] := []`,
//! mirroring production marking the absorbed class absent.)
//!
//! ## Modeling choices (documented divergences)
//! - `CircularListNode<T> { payload, next }` is payload-generic, mirroring
//!   production's `EClassEntry<T>`; `next` is a plain `usize` index. The buffer
//!   is generic — it is only *named* `EClass`-anything in the e-graph context.
//! - Storage is the verified semi-persistent `Vec` over `ParallelStore`
//!   (`Copy + Default`), so mark/restore compose for free; `splice` swaps only
//!   `next` and leaves every `payload` untouched.

use vstd::prelude::*;

use crate::parallel_store::ParallelStore;
use crate::vec::{ShrinkPolicy, Vec as SpVec, VecToken};

verus! {

/// One ring node: a generic `payload` plus the index of the next node in the
/// same class (its ring successor, wrapping around).
#[derive(Copy)]
pub struct CircularListNode<T> {
    pub payload: T,
    pub next: usize,
}

impl<T: Copy> Clone for CircularListNode<T> {
    fn clone(&self) -> (r: Self)
        ensures r == *self,
    {
        *self
    }
}

impl<T: core::default::Default> core::default::Default for CircularListNode<T> {
    fn default() -> CircularListNode<T> {
        CircularListNode { payload: T::default(), next: 0 }
    }
}

/// Token for mark/restore (delegates to the inner vector's token).
#[derive(Copy, Clone)]
pub struct CircularListToken {
    pub entries: VecToken,
}

/// `rotate(s, k)` = `s` cyclically left-rotated by `k`: `s[k..] ++ s[..k]`.
/// `rotate(s, k)[p] == s[(k + p) mod len]`.
pub open spec fn rotate(s: Seq<usize>, k: int) -> Seq<usize> {
    s.subrange(k, s.len() as int) + s.subrange(0, k)
}

pub struct CircularList<T, const TRACK: bool>
where T: Sized + Copy + core::default::Default {
    pub entries: SpVec<CircularListNode<T>, usize, ParallelStore<CircularListNode<T>, usize>, TRACK>,
    /// Ghost partition: `model@[c]` is class `c`'s node indices in ring order.
    pub model: Ghost<Seq<Seq<usize>>>,
}

impl<T, const TRACK: bool> CircularList<T, TRACK>
where T: Sized + Copy + core::default::Default {
    /// `next_seq()[i]` is node `i`'s successor pointer.
    pub open spec fn next_seq(&self) -> Seq<usize> {
        Seq::new(self.entries.view().len(), |i: int| self.entries.view()[i].next)
    }

    /// `payload_seq()[i]` is node `i`'s payload.
    pub open spec fn payload_seq(&self) -> Seq<T> {
        Seq::new(self.entries.view().len(), |i: int| self.entries.view()[i].payload)
    }

    pub open spec fn n_spec(&self) -> nat {
        self.entries.view().len()
    }

    pub open spec fn model_view(&self) -> Seq<Seq<usize>> {
        self.model@
    }

    /// in-range: every node named by any ring is allocated.
    pub open spec fn model_in_range(&self) -> bool {
        let m = self.model@;
        forall|c: int, p: int|
            0 <= c < m.len() && 0 <= p < (#[trigger] m[c]).len() ==> #[trigger] m[c][p] < self.n_spec()
    }

    /// disjoint: a node index occurs in at most one ring at one position.
    pub open spec fn model_disjoint(&self) -> bool {
        let m = self.model@;
        forall|c1: int, p1: int, c2: int, p2: int|
            0 <= c1 < m.len() && 0 <= p1 < m[c1].len()
                && 0 <= c2 < m.len() && 0 <= p2 < m[c2].len()
                && (#[trigger] m[c1][p1]) == (#[trigger] m[c2][p2])
                    ==> c1 == c2 && p1 == p2
    }

    /// `i` is some ring's member (used as the per-node `covers` predicate).
    pub open spec fn in_some_ring(&self, i: int) -> bool {
        let m = self.model@;
        exists|c: int, p: int|
            0 <= c < m.len() && 0 <= p < m[c].len() && (#[trigger] m[c][p]) == i
    }

    /// covers: every allocated node is in some ring.
    pub open spec fn model_covers(&self) -> bool {
        forall|i: int| 0 <= i < self.n_spec() ==> #[trigger] self.in_some_ring(i)
    }

    /// cyclic: `next` of a ring node is its successor, wrapping at the end.
    pub open spec fn model_cyclic(&self) -> bool {
        let m = self.model@;
        let ns = self.next_seq();
        forall|c: int, p: int|
            0 <= c < m.len() && 0 <= p < m[c].len()
                ==> ns[#[trigger] m[c][p] as int] == m[c][if p + 1 < m[c].len() { p + 1 } else { 0 }]
    }

    pub open spec fn wf(&self) -> bool {
        &&& self.entries.wf()
        &&& self.model_in_range()
        &&& self.model_disjoint()
        &&& self.model_covers()
        &&& self.model_cyclic()
    }

    pub fn new() -> (c: Self)
        ensures c.wf(), c.n_spec() == 0, c.model_view().len() == 0,
    {
        let c = CircularList {
            entries: SpVec::<CircularListNode<T>, usize, ParallelStore<CircularListNode<T>, usize>, TRACK>::new(),
            model: Ghost(Seq::empty()),
        };
        proof {
            assert(c.n_spec() == 0);
        }
        c
    }

    pub fn len(&self) -> (n: usize)
        requires self.wf(),
        ensures n == self.n_spec(),
    {
        self.entries.len()
    }

    /// `next` of node `i`.
    pub fn next_of(&self, i: usize) -> (r: usize)
        requires self.wf(), i < self.n_spec(),
        ensures r == self.next_seq()[i as int],
    {
        self.entries.get(i).next
    }

    /// Add a new singleton class: node `n` as its own ring `[n]` with the
    /// self-loop `next[n] == n`, carrying `payload`.
    pub fn add_singleton(&mut self, payload: T) -> (id: usize)
        requires old(self).wf(), old(self).n_spec() + 1 < usize::MAX,
        ensures
            self.wf(),
            id == old(self).n_spec(),
            self.n_spec() == old(self).n_spec() + 1,
            self.model_view() == old(self).model_view().push(seq![id]),
            self.payload_seq()[id as int] == payload,
    {
        let id = self.entries.len();
        self.entries.push(CircularListNode { payload, next: id });
        self.model = Ghost(self.model@.push(seq![id]));
        proof {
            let m = self.model@;
            let ns = self.next_seq();
            let cnew = (m.len() - 1) as int;
            assert(m[cnew] =~= seq![id]);
            assert(ns[id as int] == id);
            // in-range: old indices < old_n < new_n; new singleton id < new_n.
            assert forall|c: int, p: int|
                0 <= c < m.len() && 0 <= p < m[c].len() implies #[trigger] m[c][p] < self.n_spec() by {
                if c == cnew { assert(m[c][p] == id); }
                else { assert(m[c][p] == old(self).model_view()[c][p]); }
            }
            // disjoint: id is fresh (== old_n), every old index < old_n.
            assert forall|c1: int, p1: int, c2: int, p2: int|
                0 <= c1 < m.len() && 0 <= p1 < m[c1].len()
                    && 0 <= c2 < m.len() && 0 <= p2 < m[c2].len()
                    && (#[trigger] m[c1][p1]) == (#[trigger] m[c2][p2])
                implies c1 == c2 && p1 == p2 by {
                if c1 == cnew && c2 == cnew {
                } else if c1 == cnew {
                    assert(m[c2][p2] == old(self).model_view()[c2][p2]);
                    assert(m[c2][p2] < old(self).n_spec());
                } else if c2 == cnew {
                    assert(m[c1][p1] < old(self).n_spec());
                } else {
                    assert(m[c1][p1] == old(self).model_view()[c1][p1]);
                    assert(m[c2][p2] == old(self).model_view()[c2][p2]);
                }
            }
            // covers: old nodes in old rings (unchanged prefix); id in cnew.
            assert forall|i: int| 0 <= i < self.n_spec() implies #[trigger] self.in_some_ring(i) by {
                if i < old(self).n_spec() {
                    assert(old(self).in_some_ring(i));  // old covers
                    let (c, p) = choose|c: int, p: int|
                        0 <= c < old(self).model_view().len() && 0 <= p < old(self).model_view()[c].len()
                            && old(self).model_view()[c][p] == i;
                    assert(m[c][p] == i);  // witness for self.in_some_ring(i)
                } else {
                    assert(m[cnew][0] == id);  // witness: i == id at (cnew, 0)
                }
            }
            // cyclic: old rings unchanged; new ring [id] self-loops.
            assert forall|c: int, p: int|
                0 <= c < m.len() && 0 <= p < m[c].len() implies
                ns[#[trigger] m[c][p] as int] == m[c][if p + 1 < m[c].len() { p + 1 } else { 0 }] by {
                if c == cnew {
                    assert(m[c][p] == id && ns[id as int] == id);
                } else {
                    assert(m[c] == old(self).model_view()[c]);
                    assert(m[c][p] == old(self).model_view()[c][p]);
                    assert(m[c][p] < old(self).n_spec());
                    assert(ns[m[c][p] as int] == old(self).next_seq()[m[c][p] as int]);
                }
            }
        }
        id
    }

    /// Ghost: the (ring, position) of node `i`. Well-defined under `wf`
    /// (covers gives existence, disjoint gives uniqueness).
    pub open spec fn locate(&self, i: int) -> (int, int) {
        choose|c: int, p: int|
            0 <= c < self.model@.len() && 0 <= p < self.model@[c].len() && self.model@[c][p] == i
    }

    /// Splice the rings (classes) of `s` and `a` by swapping their `next`
    /// pointers — the O(1) circular-list join. For `s`, `a` in **different**
    /// rings this merges the two rings into one; the merged ring's node set is
    /// the union of the two, and its successor structure is again a single
    /// cycle (`wf` preserved — no finite-cycle side condition). The source ring
    /// slot is emptied. Requires `s`, `a` in different rings (the class-merge
    /// use; splicing within one ring would split it).
    #[verifier::spinoff_prover]
    #[verifier::rlimit(800)]
    pub fn splice(&mut self, s: usize, a: usize)
        requires
            old(self).wf(),
            (s as int) < old(self).n_spec(),
            (a as int) < old(self).n_spec(),
            old(self).locate(s as int).0 != old(self).locate(a as int).0,  // different rings
        ensures
            self.wf(),
            self.n_spec() == old(self).n_spec(),
            self.payload_seq() == old(self).payload_seq(),
            self.model_view().len() == old(self).model_view().len(),
            // the two old rings: cs gets the merged ring, ca emptied.
            ({
                let cs = old(self).locate(s as int).0;
                let ca = old(self).locate(a as int).0;
                let ps = old(self).locate(s as int).1;
                let pa = old(self).locate(a as int).1;
                &&& self.model_view()[cs]
                        == rotate(old(self).model_view()[cs], ps + 1)
                            + rotate(old(self).model_view()[ca], pa + 1)
                &&& self.model_view()[ca] == Seq::<usize>::empty()
                &&& (forall|c: int| 0 <= c < self.model_view().len() && c != cs && c != ca
                        ==> #[trigger] self.model_view()[c] == old(self).model_view()[c])
            }),
    {
        proof {
            // covers ⟹ locate's choose is satisfiable for s and a.
            assert(self.in_some_ring(s as int));
            assert(self.in_some_ring(a as int));
        }
        let ghost cs = self.locate(s as int).0;
        let ghost ca = self.locate(a as int).0;
        let ghost ps = self.locate(s as int).1;
        let ghost pa = self.locate(a as int).1;
        let ghost old_m = self.model@;
        proof {
            // locate picks a valid (ring, pos) for s and a (choose satisfies the pred).
            assert(0 <= cs < old_m.len() && 0 <= ps < old_m[cs].len() && old_m[cs][ps] == s as int);
            assert(0 <= ca < old_m.len() && 0 <= pa < old_m[ca].len() && old_m[ca][pa] == a as int);
        }

        let s_node = self.entries.get(s);
        let a_node = self.entries.get(a);
        let old_s_next = s_node.next;
        let old_a_next = a_node.next;
        self.entries.set(s, CircularListNode { payload: s_node.payload, next: old_a_next });
        self.entries.set(a, CircularListNode { payload: a_node.payload, next: old_s_next });

        let merged = Ghost(rotate(old_m[cs], ps + 1) + rotate(old_m[ca], pa + 1));
        self.model = Ghost(self.model@.update(cs, merged@).update(ca, Seq::empty()));

        proof {
            // establish the next-swap + payload facts the lemma needs.
            assert(self.payload_seq() =~= old(self).payload_seq());
            let ns = self.next_seq();
            let old_ns = old(self).next_seq();
            assert(ns[s as int] == old_ns[a as int]);
            assert(ns[a as int] == old_ns[s as int]);
            assert forall|k: int| 0 <= k < self.n_spec() && k != s as int && k != a as int implies
                #[trigger] ns[k] == old_ns[k] by {}
            // model length: two updates preserve len.
            assert(self.model@.len() == old_m.update(cs, merged@).update(ca, Seq::empty()).len());
            assert(self.model@.len() == old(self).model@.len());
            lemma_splice_merge(*old(self), self, s as int, a as int, cs, ca, ps, pa);
        }
    }

    // ---- semi-persistence: delegate to the inner vector ----

    pub fn mark(&mut self, shrink: ShrinkPolicy) -> (token: CircularListToken)
        requires old(self).wf(), old(self).n_spec() < usize::MAX,
        ensures
            self.wf(),
            self.next_seq() == old(self).next_seq(),
            self.n_spec() == old(self).n_spec(),
            self.model_view() == old(self).model_view(),
            self.entries.snapshots_view()
                == old(self).entries.snapshots_view().push(old(self).entries.view()),
    {
        let entries = self.entries.mark(shrink);
        proof {
            assert(self.entries.view() == old(self).entries.view());
            assert(self.next_seq() =~= old(self).next_seq());
            // model + view unchanged ⟹ covers carries (same witnesses).
            assert forall|i: int| 0 <= i < self.n_spec() implies #[trigger] self.in_some_ring(i) by {
                assert(old(self).in_some_ring(i));
            }
        }
        CircularListToken { entries }
    }

    /// Restore to the marked snapshot. The restored entries, together with the
    /// ghost model live at the mark, must form a valid ring partition.
    pub fn restore(&mut self, token: CircularListToken, Ghost(snap_model): Ghost<Seq<Seq<usize>>>)
        requires
            old(self).wf(),
            old(self).entries.is_token_valid_spec(token.entries),
            token.entries.frame_idx < old(self).entries.frames@.len(),
            old(self).entries.frames@.len() < u32::MAX,
            old(self).entries.forks.origins@.len() + 1 <= u32::MAX,
            ring_snap_wf(
                snap_model,
                old(self).entries.snapshots_view()[token.entries.frame_idx as int]),
        ensures
            self.wf(),
            self.entries.view()
                == old(self).entries.snapshots_view()[token.entries.frame_idx as int],
            self.model_view() == snap_model,
    {
        let ghost snap = old(self).entries.snapshots_view()[token.entries.frame_idx as int];
        self.entries.restore(token.entries);
        self.model = Ghost(snap_model);
        proof {
            assert(self.entries.view() == snap);
            let m = self.model@;
            let ns = self.next_seq();
            assert(self.n_spec() == snap.len());
            // bridge ring_snap_wf(snap_model, snap) to wf's clauses.
            assert forall|c: int, p: int|
                0 <= c < m.len() && 0 <= p < m[c].len() implies
                ns[#[trigger] m[c][p] as int] == m[c][if p + 1 < m[c].len() { p + 1 } else { 0 }] by {
                assert(ns[m[c][p] as int] == snap[m[c][p] as int].next);
            }
            // covers: ring_snap_wf's covers clause is over idx_in_some_ring(snap_model);
            // transfer to self.in_some_ring (same model, same witnesses).
            assert forall|i: int| 0 <= i < self.n_spec() implies #[trigger] self.in_some_ring(i) by {
                assert(idx_in_some_ring(snap_model, i));
                let (c, p) = choose|c: int, p: int|
                    0 <= c < snap_model.len() && 0 <= p < snap_model[c].len() && snap_model[c][p] == i;
                assert(m[c][p] == i);
            }
        }
    }
}

/// The splice-merge proof. `post` differs from `pre` by: `next[s]`/`next[a]`
/// swapped (payloads intact), and the model's ring `cs` replaced by
/// `rotate(pre[cs], ps+1) ++ rotate(pre[ca], pa+1)` with ring `ca` emptied.
/// Establishes `post.wf()`. The crux: the merged ring's `next` law holds because
/// every interior edge is unchanged and the two seams are exactly the two
/// swapped `next` pointers.
#[verifier::spinoff_prover]
#[verifier::rlimit(800)]
pub proof fn lemma_splice_merge<T, const TRACK: bool>(
    pre: CircularList<T, TRACK>, post: &CircularList<T, TRACK>,
    s: int, a: int, cs: int, ca: int, ps: int, pa: int,
)
    where T: Sized + Copy + core::default::Default
    requires
        pre.wf(),
        pre.entries.wf(),
        post.entries.wf(),
        0 <= s < pre.n_spec(),
        0 <= a < pre.n_spec(),
        post.n_spec() == pre.n_spec(),
        // locate facts:
        0 <= cs < pre.model@.len(), 0 <= ps < pre.model@[cs].len(), pre.model@[cs][ps] == s,
        0 <= ca < pre.model@.len(), 0 <= pa < pre.model@[ca].len(), pre.model@[ca][pa] == a,
        cs != ca,
        // next swap (post next_seq vs pre):
        post.next_seq()[s] == pre.next_seq()[a],
        post.next_seq()[a] == pre.next_seq()[s],
        forall|k: int| 0 <= k < post.n_spec() && k != s && k != a
            ==> #[trigger] post.next_seq()[k] == pre.next_seq()[k],
        // model update:
        post.model@.len() == pre.model@.len(),
        post.model@[cs] == rotate(pre.model@[cs], ps + 1) + rotate(pre.model@[ca], pa + 1),
        post.model@[ca] == Seq::<usize>::empty(),
        forall|c: int| 0 <= c < post.model@.len() && c != cs && c != ca
            ==> #[trigger] post.model@[c] == pre.model@[c],
    ensures
        post.wf(),
{
    let pm = pre.model@;
    let qm = post.model@;
    let n = pre.n_spec() as int;
    let rs = pm[cs];   // old ring of s
    let ra = pm[ca];   // old ring of a
    let merged = qm[cs];

    // --- rotate facts: rotate(x, k) is a permutation of x (same len, same
    // membership: position q of rotate is x[(k+q) mod len]).
    lemma_rotate_props(rs, ps + 1);
    lemma_rotate_props(ra, pa + 1);
    assert(merged.len() == rs.len() + ra.len());

    // merged[q] for q < rs.len() is rs[(ps+1+q) mod rs.len()]; for q >= rs.len()
    // it is ra[(pa+1 + (q - rs.len())) mod ra.len()].
    assert forall|q: int| 0 <= q < merged.len() implies
        (#[trigger] merged[q]) == (if q < rs.len() {
            rotate(rs, ps + 1)[q]
        } else {
            rotate(ra, pa + 1)[q - rs.len()]
        }) by {
        if q < rs.len() {
            assert(merged[q] == rotate(rs, ps + 1)[q]);
        } else {
            assert(merged[q] == rotate(ra, pa + 1)[q - rs.len()]);
        }
    }

    lemma_splice_in_range(pre, post, cs, ca, ps, pa);
    lemma_splice_disjoint(pre, post, s, a, cs, ca, ps, pa);
    lemma_splice_covers(pre, post, cs, ca, ps, pa);
    lemma_splice_cyclic(pre, post, s, a, cs, ca, ps, pa);
}

/// `rotate(x, k)` for `0 <= k <= len`: same length, and `rotate(x,k)[q] ==
/// x[(k+q) mod len]` — so it is a permutation of `x` (same multiset/set).
pub proof fn lemma_rotate_props(x: Seq<usize>, k: int)
    requires 0 <= k <= x.len(),
    ensures
        rotate(x, k).len() == x.len(),
        forall|q: int| 0 <= q < x.len()
            ==> #[trigger] rotate(x, k)[q] == x[if k + q < x.len() { k + q } else { k + q - x.len() }],
{
    let r = rotate(x, k);
    assert(r.len() == x.len());
    assert forall|q: int| 0 <= q < x.len() implies
        #[trigger] r[q] == x[if k + q < x.len() { k + q } else { k + q - x.len() }] by {
        // r = x[k..] ++ x[..k]; index q < len-k hits x[k+q], else x[q-(len-k)].
        if q < x.len() - k {
            assert(r[q] == x.subrange(k, x.len() as int)[q]);
        } else {
            assert(r[q] == x.subrange(0, k)[q - (x.len() - k)]);
        }
    }
}

/// in_range clause of post.wf() after splice.
#[verifier::spinoff_prover]
pub proof fn lemma_splice_in_range<T, const TRACK: bool>(
    pre: CircularList<T, TRACK>, post: &CircularList<T, TRACK>,
    cs: int, ca: int, ps: int, pa: int,
)
    where T: Sized + Copy + core::default::Default
    requires
        pre.wf(), post.n_spec() == pre.n_spec(),
        0 <= cs < pre.model@.len(), 0 <= ca < pre.model@.len(), cs != ca,
        0 <= ps < pre.model@[cs].len(), 0 <= pa < pre.model@[ca].len(),
        post.model@.len() == pre.model@.len(),
        post.model@[cs] == rotate(pre.model@[cs], ps + 1) + rotate(pre.model@[ca], pa + 1),
        post.model@[ca] == Seq::<usize>::empty(),
        forall|c: int| 0 <= c < post.model@.len() && c != cs && c != ca
            ==> #[trigger] post.model@[c] == pre.model@[c],
    ensures post.model_in_range(),
{
    let pm = pre.model@; let qm = post.model@;
    lemma_rotate_props(pm[cs], ps + 1);
    lemma_rotate_props(pm[ca], pa + 1);
    assert forall|c: int, p: int|
        0 <= c < qm.len() && 0 <= p < (#[trigger] qm[c]).len() implies
        #[trigger] qm[c][p] < post.n_spec() by {
        if c == cs {
            // merged element comes from rs or ra, both in-range in pre.
            if p < pm[cs].len() {
                assert(qm[cs][p] == rotate(pm[cs], ps + 1)[p]);
            } else {
                assert(qm[cs][p] == rotate(pm[ca], pa + 1)[p - pm[cs].len()]);
            }
        } else if c == ca {
        } else {
            assert(qm[c][p] == pm[c][p]);
        }
    }
}

/// disjoint clause of post.wf() after splice.
#[verifier::spinoff_prover]
#[verifier::rlimit(800)]
pub proof fn lemma_splice_disjoint<T, const TRACK: bool>(
    pre: CircularList<T, TRACK>, post: &CircularList<T, TRACK>,
    s: int, a: int, cs: int, ca: int, ps: int, pa: int,
)
    where T: Sized + Copy + core::default::Default
    requires
        pre.wf(), post.n_spec() == pre.n_spec(),
        0 <= cs < pre.model@.len(), 0 <= ca < pre.model@.len(), cs != ca,
        0 <= ps < pre.model@[cs].len(), 0 <= pa < pre.model@[ca].len(),
        post.model@.len() == pre.model@.len(),
        post.model@[cs] == rotate(pre.model@[cs], ps + 1) + rotate(pre.model@[ca], pa + 1),
        post.model@[ca] == Seq::<usize>::empty(),
        forall|c: int| 0 <= c < post.model@.len() && c != cs && c != ca
            ==> #[trigger] post.model@[c] == pre.model@[c],
    ensures post.model_disjoint(),
{
    let pm = pre.model@; let qm = post.model@;
    lemma_rotate_props(pm[cs], ps + 1);
    lemma_rotate_props(pm[ca], pa + 1);
    let rslen = pm[cs].len();
    // Each post entry qm[c][p] equals SOME pre entry pm[c'][p'], and the map
    // (c,p) -> (c',p') is injective. We expose the source mapping, then lean on
    // pre's disjointness.
    assert forall|c1: int, p1: int, c2: int, p2: int|
        0 <= c1 < qm.len() && 0 <= p1 < qm[c1].len()
            && 0 <= c2 < qm.len() && 0 <= p2 < qm[c2].len()
            && (#[trigger] qm[c1][p1]) == (#[trigger] qm[c2][p2])
        implies c1 == c2 && p1 == p2 by {
        // src(c,p): the (pre-ring, pre-pos) that qm[c][p] came from.
        let src1 = ring_src(pm, cs, ca, ps, pa, rslen as int, c1, p1);
        let src2 = ring_src(pm, cs, ca, ps, pa, rslen as int, c2, p2);
        // qm[ci][pi] == pm[src_i.0][src_i.1]
        lemma_ring_src(pm, qm, cs, ca, ps, pa, rslen as int, c1, p1);
        lemma_ring_src(pm, qm, cs, ca, ps, pa, rslen as int, c2, p2);
        // equal values ⟹ equal pre-source (pre disjoint), then src is injective.
        assert(pm[src1.0][src1.1] == pm[src2.0][src2.1]);
        assert(src1.0 == src2.0 && src1.1 == src2.1);  // pre.model_disjoint
        // src injective back to (c,p): within cs the prefix/suffix split + rotate
        // injectivity; ca empty; other rings identity.
        lemma_ring_src_injective(pm, cs, ca, ps, pa, rslen as int, c1, p1, c2, p2);
    }
}

/// The pre-(ring, position) that post entry `qm[c][p]` originates from, after
/// `splice` merged rings `cs`,`ca` into `cs = rotate(rs,ps+1) ++ rotate(ra,pa+1)`.
pub open spec fn ring_src(
    pm: Seq<Seq<usize>>, cs: int, ca: int, ps: int, pa: int, rslen: int, c: int, p: int,
) -> (int, int) {
    if c == cs {
        if p < rslen {
            // prefix: rotate(rs, ps+1)[p] == rs[(ps+1+p) mod rslen]
            (cs, if ps + 1 + p < rslen { ps + 1 + p } else { ps + 1 + p - rslen })
        } else {
            // suffix: rotate(ra, pa+1)[p-rslen]
            let q = p - rslen;
            let ralen = pm[ca].len() as int;
            (ca, if pa + 1 + q < ralen { pa + 1 + q } else { pa + 1 + q - ralen })
        }
    } else {
        (c, p)
    }
}

/// `qm[c][p] == pm[ring_src(...)]` and the source is in-bounds.
pub proof fn lemma_ring_src(
    pm: Seq<Seq<usize>>, qm: Seq<Seq<usize>>, cs: int, ca: int, ps: int, pa: int, rslen: int,
    c: int, p: int,
)
    requires
        0 <= cs < pm.len(), 0 <= ca < pm.len(), cs != ca,
        0 <= ps < pm[cs].len(), 0 <= pa < pm[ca].len(),
        rslen == pm[cs].len(),
        qm.len() == pm.len(),
        qm[cs] == rotate(pm[cs], ps + 1) + rotate(pm[ca], pa + 1),
        qm[ca] == Seq::<usize>::empty(),
        forall|cc: int| 0 <= cc < qm.len() && cc != cs && cc != ca ==> qm[cc] == pm[cc],
        0 <= c < qm.len(), 0 <= p < qm[c].len(),
    ensures
        ({ let sr = ring_src(pm, cs, ca, ps, pa, rslen, c, p);
           0 <= sr.0 < pm.len() && 0 <= sr.1 < pm[sr.0].len() && qm[c][p] == pm[sr.0][sr.1] }),
{
    lemma_rotate_props(pm[cs], ps + 1);
    lemma_rotate_props(pm[ca], pa + 1);
    if c == cs {
        if p < rslen {
            assert(qm[cs][p] == rotate(pm[cs], ps + 1)[p]);
        } else {
            assert(qm[cs][p] == rotate(pm[ca], pa + 1)[p - rslen]);
        }
    }
}

/// `ring_src` is injective: distinct post positions have distinct pre sources.
pub proof fn lemma_ring_src_injective(
    pm: Seq<Seq<usize>>, cs: int, ca: int, ps: int, pa: int, rslen: int,
    c1: int, p1: int, c2: int, p2: int,
)
    requires
        rslen == pm[cs].len(),
        0 <= ps < rslen, 0 <= pa < pm[ca].len(), cs != ca,
        ring_src(pm, cs, ca, ps, pa, rslen, c1, p1) == ring_src(pm, cs, ca, ps, pa, rslen, c2, p2),
        // both positions are valid in the post-merge model: ring cs has length
        // rslen + |ra|, ring ca is empty, every other ring keeps its length.
        0 <= c1, 0 <= c2,
        (c1 == cs ==> 0 <= p1 < rslen + pm[ca].len()),
        (c2 == cs ==> 0 <= p2 < rslen + pm[ca].len()),
        c1 != ca,  // ca is empty post-merge, so a valid position can't sit there
        c2 != ca,
        (c1 != cs && c1 != ca) ==> 0 <= p1,  // p1 a real index in its (unchanged) ring
        (c2 != cs && c2 != ca) ==> 0 <= p2,
    ensures
        c1 == c2 && p1 == p2,
{
    let ralen = pm[ca].len() as int;
    let sr1 = ring_src(pm, cs, ca, ps, pa, rslen, c1, p1);
    let sr2 = ring_src(pm, cs, ca, ps, pa, rslen, c2, p2);
    assert(sr1.0 == sr2.0 && sr1.1 == sr2.1);  // from requires sr1 == sr2
    // The source RING component (sr.0) already separates the regions:
    //   cs-prefix (c==cs, p<rslen)   -> sr.0 == cs
    //   cs-suffix (c==cs, p>=rslen)  -> sr.0 == ca
    //   other (c != cs)              -> sr.0 == c (which is != cs and != ca, or is
    //                                   a foreign ring; ca itself is empty so c2!=ca)
    // Since sr1 == sr2, the two positions are in the same region; within a region
    // the position map is an injective affine-mod offset.
    if c1 == cs && p1 < rslen {
        // sr1.0 == cs. Force c2 into the same region.
        assert(sr1.0 == cs);
        // p1's source pos = (ps+1+p1) mod rslen; recover p1 from it uniquely.
        if c2 == cs && p2 < rslen {
            // both prefix: sr.1 = (ps+1+p) wrapped into [0,rslen); recover p.
            let o1 = if ps + 1 + p1 < rslen { ps + 1 + p1 } else { ps + 1 + p1 - rslen };
            let o2 = if ps + 1 + p2 < rslen { ps + 1 + p2 } else { ps + 1 + p2 - rslen };
            assert(sr1.1 == o1 && sr2.1 == o2);
            assert(o1 == o2);  // sr1 == sr2
            // o == (ps+1+p) - (0 or rslen); since p in [0,rslen), the map is a bijection.
            assert(p1 == p2);
        } else if c2 == cs {
            // c2 suffix ⟹ sr2.0 == ca; but sr2.0 == sr1.0 == cs != ca: impossible.
            assert(sr2.0 == ca);
            assert(false);
        } else {
            // c2 other ⟹ sr2.0 == c2 != cs; but sr2.0 == cs: impossible.
            assert(sr2.0 == c2);
            assert(false);
        }
    } else if c1 == cs {
        // c1 suffix: sr1.0 == ca.
        assert(sr1.0 == ca);
        if c2 == cs && p2 < rslen {
            assert(sr2.0 == cs);  // sr1.0 == ca != cs: impossible.
            assert(false);
        } else if c2 == cs {
            // both suffix: recover the suffix offset q = p - rslen, then the
            // ra-rotation offset is a bijection in q.
            let q1 = p1 - rslen; let q2 = p2 - rslen;
            let o1 = if pa + 1 + q1 < ralen { pa + 1 + q1 } else { pa + 1 + q1 - ralen };
            let o2 = if pa + 1 + q2 < ralen { pa + 1 + q2 } else { pa + 1 + q2 - ralen };
            assert(sr1.1 == o1 && sr2.1 == o2);
            assert(o1 == o2);
            assert(q1 == q2);
            assert(p1 == p2);
        } else {
            assert(sr2.0 == c2);  // sr1.0 == ca; sr2.0 == c2; c2 != cs.
            assert(false);        // c2 != cs and c2 valid ⟹ c2 != ca (ca empty), so c2 != ca == sr1.0.
        }
    } else {
        // c1 other: sr1.0 == c1 (!= cs), sr1.1 == p1.
        assert(sr1.0 == c1);
        if c2 == cs && p2 < rslen {
            assert(sr2.0 == cs);
            assert(false);
        } else if c2 == cs {
            assert(sr2.0 == ca);
            assert(false);
        } else {
            // both "other": sr.0 == c, sr.1 == p, so sr1==sr2 ⟹ c1==c2 ∧ p1==p2.
            assert(sr2.0 == c2 && sr2.1 == p2);
            assert(sr1.1 == p1);
        }
    }
}

/// covers clause of post.wf() after splice.
///
/// Requires only `pre.model_covers()`, NOT the full `pre.wf()`: the body uses
/// nothing else, and dragging `pre.wf()` in pulls `model_disjoint`'s quad-nested
/// `forall|c1,p1,c2,p2| m[c1][p1]==m[c2][p2]` into scope, where it e-matches
/// combinatorially against every nested-sequence access here and makes the proof
/// blow up (rlimit 800 + spinoff, and even then z3-seed-flaky). The caller has
/// full `pre.wf()`, which implies `model_covers()`, so this is strictly weaker.
#[verifier::spinoff_prover]
#[verifier::rlimit(50)]
pub proof fn lemma_splice_covers<T, const TRACK: bool>(
    pre: CircularList<T, TRACK>, post: &CircularList<T, TRACK>,
    cs: int, ca: int, ps: int, pa: int,
)
    where T: Sized + Copy + core::default::Default
    requires
        pre.model_covers(), post.n_spec() == pre.n_spec(),
        0 <= cs < pre.model@.len(), 0 <= ca < pre.model@.len(), cs != ca,
        0 <= ps < pre.model@[cs].len(), 0 <= pa < pre.model@[ca].len(),
        post.model@.len() == pre.model@.len(),
        post.model@[cs] == rotate(pre.model@[cs], ps + 1) + rotate(pre.model@[ca], pa + 1),
        post.model@[ca] == Seq::<usize>::empty(),
        forall|c: int| 0 <= c < post.model@.len() && c != cs && c != ca
            ==> #[trigger] post.model@[c] == pre.model@[c],
    ensures post.model_covers(),
{
    let pm = pre.model@; let qm = post.model@;
    lemma_rotate_props(pm[cs], ps + 1);
    lemma_rotate_props(pm[ca], pa + 1);
    let rslen = pm[cs].len();
    assert forall|i: int| 0 <= i < post.n_spec() implies #[trigger] post.in_some_ring(i) by {
        assert(pre.in_some_ring(i));  // pre covers
        let (c, p) = choose|c: int, p: int|
            0 <= c < pm.len() && 0 <= p < pm[c].len() && pm[c][p] == i;
        if c == cs {
            // i == rs[p]; rs[p] == rotate(rs, ps+1)[q] for q = (p - (ps+1)) mod rslen.
            let q = if p >= ps + 1 { p - (ps + 1) } else { p + rslen - (ps + 1) };
            assert(0 <= q < rslen);
            assert(rotate(pm[cs], ps + 1)[q] == pm[cs][p]);  // from lemma_rotate_props
            assert(qm[cs][q] == rotate(pm[cs], ps + 1)[q]);  // merged prefix
            assert(qm[cs][q] == i);  // witness in merged ring cs
        } else if c == ca {
            let q = if p >= pa + 1 { p - (pa + 1) } else { p + pm[ca].len() - (pa + 1) };
            assert(0 <= q < pm[ca].len());
            assert(rotate(pm[ca], pa + 1)[q] == pm[ca][p]);
            assert(qm[cs][rslen + q] == rotate(pm[ca], pa + 1)[q]);  // merged suffix
            assert(qm[cs][rslen + q] == i);
        } else {
            assert(qm[c][p] == i);  // unchanged ring
        }
    }
}

/// cyclic clause of post.wf() after splice — the crux.
#[verifier::spinoff_prover]
#[verifier::rlimit(800)]
pub proof fn lemma_splice_cyclic<T, const TRACK: bool>(
    pre: CircularList<T, TRACK>, post: &CircularList<T, TRACK>,
    s: int, a: int, cs: int, ca: int, ps: int, pa: int,
)
    where T: Sized + Copy + core::default::Default
    requires
        pre.wf(), post.n_spec() == pre.n_spec(),
        0 <= s < pre.n_spec(), 0 <= a < pre.n_spec(),
        0 <= cs < pre.model@.len(), 0 <= ca < pre.model@.len(), cs != ca,
        0 <= ps < pre.model@[cs].len(), pre.model@[cs][ps] == s,
        0 <= pa < pre.model@[ca].len(), pre.model@[ca][pa] == a,
        post.next_seq()[s] == pre.next_seq()[a],
        post.next_seq()[a] == pre.next_seq()[s],
        forall|k: int| 0 <= k < post.n_spec() && k != s && k != a
            ==> #[trigger] post.next_seq()[k] == pre.next_seq()[k],
        post.model@.len() == pre.model@.len(),
        post.model@[cs] == rotate(pre.model@[cs], ps + 1) + rotate(pre.model@[ca], pa + 1),
        post.model@[ca] == Seq::<usize>::empty(),
        forall|c: int| 0 <= c < post.model@.len() && c != cs && c != ca
            ==> #[trigger] post.model@[c] == pre.model@[c],
    ensures post.model_cyclic(),
{
    let pm = pre.model@; let qm = post.model@;
    let pns = pre.next_seq(); let qns = post.next_seq();
    let rs = pm[cs]; let ra = pm[ca];
    let rslen = rs.len() as int; let ralen = ra.len() as int;
    let merged = qm[cs];
    lemma_rotate_props(rs, ps + 1);
    lemma_rotate_props(ra, pa + 1);
    // endpoints of the rotations:
    //   rotate(rs,ps+1) starts at rs[ps+1 mod] and ends at rs[ps] == s.
    //   rotate(ra,pa+1) starts at ra[pa+1 mod] and ends at ra[pa] == a.
    assert(merged.len() == rslen + ralen);
    assert(merged[rslen - 1] == rotate(rs, ps + 1)[rslen - 1]);
    assert(rotate(rs, ps + 1)[rslen - 1] == rs[ps]);  // wraps to ps
    assert(merged[rslen - 1] == s);
    assert(merged[merged.len() - 1] == rotate(ra, pa + 1)[ralen - 1]);
    assert(rotate(ra, pa + 1)[ralen - 1] == ra[pa]);
    assert(merged[merged.len() - 1] == a);
    assert(merged[0] == rotate(rs, ps + 1)[0]);
    assert(merged[rslen] == rotate(ra, pa + 1)[0]);

    assert forall|c: int, p: int|
        0 <= c < qm.len() && 0 <= p < qm[c].len() implies
        qns[#[trigger] qm[c][p] as int] == qm[c][if p + 1 < qm[c].len() { p + 1 } else { 0 }] by {
        if c == cs {
            let node = qm[cs][p];
            let succ = qm[cs][if p + 1 < merged.len() { p + 1 } else { 0 }];
            if p == rslen - 1 {
                // node == s; new next[s] == old next[a] == ra[(pa+1) mod] == merged[rslen].
                assert(node == s);
                assert(qns[s] == pns[a]);
                lemma_pre_cyclic_at(pre, ca, pa);            // pns[a] == ra[(pa+1) mod]
                assert(qm[cs][rslen] == rotate(ra, pa + 1)[0]);
                assert(rotate(ra, pa + 1)[0] == ra[if pa + 1 < ralen { pa + 1 } else { pa + 1 - ralen }]);
                assert(succ == qm[cs][rslen]);              // p+1 == rslen < merged.len()
            } else if p == merged.len() - 1 {
                // node == a; new next[a] == old next[s] == rs[(ps+1) mod] == merged[0].
                assert(node == a);
                assert(qns[a] == pns[s]);
                lemma_pre_cyclic_at(pre, cs, ps);            // pns[s] == rs[(ps+1) mod]
                assert(succ == qm[cs][0]);                   // wraps to 0
                assert(qm[cs][0] == rotate(rs, ps + 1)[0]);
                assert(rotate(rs, ps + 1)[0] == rs[if ps + 1 < rslen { ps + 1 } else { ps + 1 - rslen }]);
            } else if p < rslen - 1 {
                // interior of prefix: node == rs[(ps+1+p) mod], next unchanged,
                // succ == rs[(ps+1+p+1) mod] == merged[p+1].
                lemma_merge_interior_prefix(pre, post, cs, ca, ps, pa, p);
            } else {
                // interior of suffix (rslen <= p < merged.len()-1).
                lemma_merge_interior_suffix(pre, post, cs, ca, ps, pa, p);
            }
        } else if c == ca {
            // empty, vacuous.
        } else {
            // unchanged ring: node and successor from pre, next unchanged.
            assert(qm[c] == pm[c]);
            assert(qm[c][p] == pm[c][p]);
            lemma_pre_cyclic_at(pre, c, p);
            // node != s and != a (disjoint from rings cs, ca), so qns == pns there.
            lemma_other_ring_avoids_sa(pre, s, a, cs, ca, c, p);
            assert(qns[qm[c][p] as int] == pns[pm[c][p] as int]);
        }
    }
}

/// pre cyclic at a specific (ring, pos): `pns[pm[c][p]] == pm[c][(p+1) mod]`.
pub proof fn lemma_pre_cyclic_at<T, const TRACK: bool>(
    pre: CircularList<T, TRACK>, c: int, p: int,
)
    where T: Sized + Copy + core::default::Default
    requires pre.wf(), 0 <= c < pre.model@.len(), 0 <= p < pre.model@[c].len(),
    ensures
        pre.next_seq()[pre.model@[c][p] as int]
            == pre.model@[c][if p + 1 < pre.model@[c].len() { p + 1 } else { 0 }],
{
    // direct from pre.model_cyclic().
}

/// A node in a ring other than cs/ca is neither s nor a (disjointness).
pub proof fn lemma_other_ring_avoids_sa<T, const TRACK: bool>(
    pre: CircularList<T, TRACK>, s: int, a: int, cs: int, ca: int, c: int, p: int,
)
    where T: Sized + Copy + core::default::Default
    requires
        pre.wf(),
        0 <= cs < pre.model@.len(), 0 <= ca < pre.model@.len(),
        0 <= c < pre.model@.len(), c != cs, c != ca, 0 <= p < pre.model@[c].len(),
        // s, a sit in rings cs, ca respectively:
        (exists|ps: int| 0 <= ps < pre.model@[cs].len() && pre.model@[cs][ps] == s),
        (exists|pa: int| 0 <= pa < pre.model@[ca].len() && pre.model@[ca][pa] == a),
    ensures
        pre.model@[c][p] != s && pre.model@[c][p] != a,
{
    // disjointness: model@[c][p] in ring c != cs, ca; s in cs, a in ca.
    let ps = choose|ps: int| 0 <= ps < pre.model@[cs].len() && pre.model@[cs][ps] == s;
    let pa = choose|pa: int| 0 <= pa < pre.model@[ca].len() && pre.model@[ca][pa] == a;
    assert(pre.model_disjoint());
}

/// Interior-of-prefix step of the merged ring's cyclic law. For `0 <= p <
/// rslen-1`, `merged[p]` is an interior node of `cs`'s rotation: its `next` is
/// UNCHANGED by the swap (it is neither `s` nor `a`), and old `cyclic` plus the
/// rotate-successor arithmetic give `next[merged[p]] == merged[p+1]`.
#[verifier::spinoff_prover]
pub proof fn lemma_merge_interior_prefix<T, const TRACK: bool>(
    pre: CircularList<T, TRACK>, post: &CircularList<T, TRACK>,
    cs: int, ca: int, ps: int, pa: int, p: int,
)
    where T: Sized + Copy + core::default::Default
    requires
        pre.wf(),
        0 <= cs < pre.model@.len(), 0 <= ca < pre.model@.len(), cs != ca,
        0 <= ps < pre.model@[cs].len(), 0 <= pa < pre.model@[ca].len(),
        0 <= p < pre.model@[cs].len() - 1,
        post.model@[cs] == rotate(pre.model@[cs], ps + 1) + rotate(pre.model@[ca], pa + 1),
        post.n_spec() == pre.n_spec(),
        forall|k: int| 0 <= k < post.n_spec()
            && k != pre.model@[cs][ps] && k != pre.model@[ca][pa]
            ==> #[trigger] post.next_seq()[k] == pre.next_seq()[k],
    ensures
        ({ let m = post.model@[cs];
           post.next_seq()[m[p] as int] == m[if p + 1 < m.len() { p + 1 } else { 0 }] }),
{
    let rs = pre.model@[cs];
    let ra = pre.model@[ca];
    let rslen = rs.len() as int;
    let m = post.model@[cs];
    let s = rs[ps];
    let a = ra[pa];
    lemma_rotate_props(rs, ps + 1);
    lemma_rotate_props(ra, pa + 1);
    assert(m.len() == rslen + ra.len());

    // source positions in rs of merged[p] and merged[p+1]:
    let j  = if ps + 1 + p < rslen { ps + 1 + p } else { ps + 1 + p - rslen };
    let j2 = if ps + 1 + (p + 1) < rslen { ps + 1 + (p + 1) } else { ps + 1 + (p + 1) - rslen };
    assert(0 <= j < rslen && 0 <= j2 < rslen);
    assert(m[p] == rs[j]);                  // rotate_props, p < rslen
    assert(m[p + 1] == rs[j2]);             // rotate_props, p+1 < rslen
    assert(p + 1 < m.len());                // p < rslen-1 <= m.len()-1

    // j != ps (else p == rslen-1), and j2 == (j+1) mod rslen — integer arith.
    assert(j != ps) by { /* ps+1+p ≡ ps (mod rslen) iff p ≡ rslen-1, excluded */ }
    assert(j2 == if j + 1 < rslen { j + 1 } else { 0 }) by {
        // case split on the two conditional subtractions (each value < 2*rslen).
    }

    // old cyclic at (cs, j): pre.next[rs[j]] == rs[(j+1) mod rslen] == rs[j2].
    lemma_pre_cyclic_at(pre, cs, j);
    assert(pre.next_seq()[rs[j] as int] == rs[if j + 1 < rslen { j + 1 } else { 0 }]);
    assert(pre.next_seq()[rs[j] as int] == rs[j2]);

    // merged[p] is neither s nor a (the frame condition for "next unchanged"):
    //   != s : j != ps and ring cs internally distinct (disjoint at c1=c2=cs).
    //   != a : rs[j] in ring cs, a in ring ca, cs != ca (disjoint cross-ring).
    assert(rs[j] != s) by {
        assert(pre.model_disjoint());
        assert(pre.model@[cs][j] == rs[j] && pre.model@[cs][ps] == s);
    }
    assert(rs[j] != a) by {
        assert(pre.model_disjoint());
        assert(pre.model@[cs][j] == rs[j] && pre.model@[ca][pa] == a);
    }
    // frame: next unchanged at an in-range non-{s,a} node.
    assert(0 <= rs[j] < post.n_spec());
    assert(post.next_seq()[rs[j] as int] == pre.next_seq()[rs[j] as int]);
    assert(post.next_seq()[m[p] as int] == m[p + 1]);
}

/// Interior-of-suffix step of the merged ring's cyclic law. Mirror of the
/// prefix case, indexing into `ca`'s rotation (offset by `rslen`).
#[verifier::spinoff_prover]
pub proof fn lemma_merge_interior_suffix<T, const TRACK: bool>(
    pre: CircularList<T, TRACK>, post: &CircularList<T, TRACK>,
    cs: int, ca: int, ps: int, pa: int, p: int,
)
    where T: Sized + Copy + core::default::Default
    requires
        pre.wf(),
        0 <= cs < pre.model@.len(), 0 <= ca < pre.model@.len(), cs != ca,
        0 <= ps < pre.model@[cs].len(), 0 <= pa < pre.model@[ca].len(),
        pre.model@[cs].len() <= p < pre.model@[cs].len() + pre.model@[ca].len() - 1,
        post.model@[cs] == rotate(pre.model@[cs], ps + 1) + rotate(pre.model@[ca], pa + 1),
        post.n_spec() == pre.n_spec(),
        forall|k: int| 0 <= k < post.n_spec()
            && k != pre.model@[cs][ps] && k != pre.model@[ca][pa]
            ==> #[trigger] post.next_seq()[k] == pre.next_seq()[k],
    ensures
        ({ let m = post.model@[cs];
           post.next_seq()[m[p] as int] == m[if p + 1 < m.len() { p + 1 } else { 0 }] }),
{
    let rs = pre.model@[cs];
    let ra = pre.model@[ca];
    let rslen = rs.len() as int;
    let ralen = ra.len() as int;
    let m = post.model@[cs];
    let s = rs[ps];
    let a = ra[pa];
    lemma_rotate_props(rs, ps + 1);
    lemma_rotate_props(ra, pa + 1);
    assert(m.len() == rslen + ralen);

    // suffix offset and its source positions in ra:
    let q = p - rslen;                       // 0 <= q < ralen-1
    assert(0 <= q < ralen - 1);
    let j  = if pa + 1 + q < ralen { pa + 1 + q } else { pa + 1 + q - ralen };
    let j2 = if pa + 1 + (q + 1) < ralen { pa + 1 + (q + 1) } else { pa + 1 + (q + 1) - ralen };
    assert(0 <= j < ralen && 0 <= j2 < ralen);
    assert(m[p] == ra[j]);                   // suffix: rotate(ra,pa+1)[q]
    assert(m[p + 1] == ra[j2]);              // q+1 < ralen ⟹ still suffix
    assert(p + 1 < m.len());

    assert(j != pa) by { }
    assert(j2 == if j + 1 < ralen { j + 1 } else { 0 }) by { }

    lemma_pre_cyclic_at(pre, ca, j);
    assert(pre.next_seq()[ra[j] as int] == ra[if j + 1 < ralen { j + 1 } else { 0 }]);
    assert(pre.next_seq()[ra[j] as int] == ra[j2]);

    assert(ra[j] != a) by {
        assert(pre.model_disjoint());
        assert(pre.model@[ca][j] == ra[j] && pre.model@[ca][pa] == a);
    }
    assert(ra[j] != s) by {
        assert(pre.model_disjoint());
        assert(pre.model@[ca][j] == ra[j] && pre.model@[cs][ps] == s);
    }
    assert(0 <= ra[j] < post.n_spec());
    assert(post.next_seq()[ra[j] as int] == pre.next_seq()[ra[j] as int]);
    assert(post.next_seq()[m[p] as int] == m[p + 1]);
}

/// `i` appears in some ring of `model` (the per-node `covers` predicate, with a
/// clean trigger for the outer `forall|i|`).
pub open spec fn idx_in_some_ring(model: Seq<Seq<usize>>, i: int) -> bool {
    exists|c: int, p: int|
        0 <= c < model.len() && 0 <= p < model[c].len() && (#[trigger] model[c][p]) == i
}

/// Structural ring-partition validity over a raw snapshot + its ghost model
/// (for `restore`): the model and entries jointly satisfy the same in-range +
/// disjoint + covers + cyclic clauses as `wf`.
pub open spec fn ring_snap_wf<T>(model: Seq<Seq<usize>>, entries: Seq<CircularListNode<T>>) -> bool {
    &&& (forall|c: int, p: int|
            0 <= c < model.len() && 0 <= p < (#[trigger] model[c]).len()
                ==> #[trigger] model[c][p] < entries.len())
    &&& (forall|c1: int, p1: int, c2: int, p2: int|
            0 <= c1 < model.len() && 0 <= p1 < model[c1].len()
                && 0 <= c2 < model.len() && 0 <= p2 < model[c2].len()
                && (#[trigger] model[c1][p1]) == (#[trigger] model[c2][p2])
                    ==> c1 == c2 && p1 == p2)
    &&& (forall|i: int| 0 <= i < entries.len() ==> #[trigger] idx_in_some_ring(model, i))
    &&& (forall|c: int, p: int|
            0 <= c < model.len() && 0 <= p < model[c].len()
                ==> (#[trigger] entries[model[c][p] as int]).next
                        == model[c][if p + 1 < model[c].len() { p + 1 } else { 0 }])
}

} // verus!
