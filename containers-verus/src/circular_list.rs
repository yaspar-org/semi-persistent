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
//! - `CircularListNode<T, N> { payload, next }` is payload-generic AND
//!   index-generic, mirroring production's `EClassEntry<T>`: `next` is stored as
//!   the `DenseId` index type `N` at its natural width (e.g. 4 bytes at 31-bit
//!   ids), not a hardcoded `usize`. Its logical position is `next.id_nat()`; the
//!   ghost `model` stays `Seq<Seq<usize>>` (logical indices), so every merge
//!   lemma is width-agnostic. The buffer is generic — it is only *named*
//!   `EClass`-anything in the e-graph context.
//! - Storage is the verified semi-persistent `Vec` over `InlineStore`
//!   (production parity): the mark/restore capture flag is stolen from `next`'s
//!   spare MSB — the same niche the id word never uses — so a node is exactly
//!   `payload + one id word` with NO side capture bitmap. This is production's
//!   `VecI<EClassEntry, _>` layout verbatim (`egraph/src/classes.rs`, where
//!   `Tagged for EClassEntry` delegates the tag to `next`). `splice` swaps only
//!   `next` and leaves every `payload` untouched.

use vstd::prelude::*;

use crate::index_like::IndexLike;
use crate::inline_store::InlineStore;
use crate::opt::DenseId;
use crate::tagged::Tagged;
use crate::vec::{ShrinkPolicy, Vec as SpVec, VecToken};

verus! {

/// One ring node: a generic `payload` plus the *next* node's id in the same
/// class (its ring successor, wrapping around). The successor is stored as the
/// index type `N` itself — a `DenseId` — at its natural width (matching the
/// consumer's `EClassEntry { next: T }`), not as a hardcoded `usize`. A ring
/// never has a null successor (a singleton self-loops), so — unlike
/// `ListNode`'s use-list pointer — this niche is NOT used to encode a null:
/// the id is always present. Instead the spare MSB carries the *capture flag*
/// for semi-persistence, exactly as production's `EClassEntry` does. The
/// logical successor position is `next.id_nat()`.
#[derive(Copy)]
pub struct CircularListNode<T, N: DenseId> {
    pub payload: T,
    pub next: N,
}

impl<T: Copy, N: DenseId> Clone for CircularListNode<T, N> {
    fn clone(&self) -> (r: Self)
        ensures r == *self,
    {
        *self
    }
}

impl<T: core::default::Default, N: DenseId> core::default::Default for CircularListNode<T, N> {
    fn default() -> CircularListNode<T, N> {
        CircularListNode { payload: T::default(), next: N::default() }
    }
}

/// Inline-storable repr of a ring node (production parity with `EClassEntry`'s
/// `Repr = (T::Repr, Index::Repr)`, but a NAMED struct — Verus's
/// trait-conflict checker rejects tuple-typed associated `Repr`s, see
/// `tagged.rs`). The capture flag is stolen from `next_repr`'s spare MSB (the
/// id word never uses it); the `payload` rides along raw and takes no part in
/// the niche, so the node needs no `T: Tagged` bound.
#[derive(Copy)]
pub struct CircularNodeRepr<T, N: DenseId> {
    pub next_repr: <N as Tagged>::Repr,
    pub payload: T,
}

impl<T: Copy, N: DenseId> Clone for CircularNodeRepr<T, N> {
    fn clone(&self) -> (r: Self)
        ensures r == *self,
    {
        *self
    }
}

// `CircularListNode` is `Tagged` by delegating the capture tag entirely to its
// `next` field's `Tagged` impl (`N: DenseId: Tagged`), the same idiom as
// production's `impl Tagged for EClassEntry`. The `payload` is carried raw:
// `value_of`/`repr_wf`/`tag_of` all ignore it, so it needs no niche of its own.
impl<T: Copy + core::default::Default, N: DenseId> Tagged for CircularListNode<T, N> {
    type Repr = CircularNodeRepr<T, N>;

    open spec fn value_of(r: Self::Repr) -> Self {
        CircularListNode { payload: r.payload, next: N::value_of(r.next_repr) }
    }

    open spec fn tag_of(r: Self::Repr) -> bool {
        N::tag_of(r.next_repr)
    }

    open spec fn repr_wf(r: Self::Repr) -> bool {
        N::repr_wf(r.next_repr)
    }

    proof fn lemma_repr_extensional(r1: Self::Repr, r2: Self::Repr) {
        // value_of agreement forces payload equality AND value_of(next_repr)
        // equality; tag_of agreement forces tag_of(next_repr) equality; N's
        // own niche-injectivity then equates the next_reprs. Two structs equal
        // on both fields are equal.
        assert(N::value_of(r1.next_repr) == N::value_of(r2.next_repr));
        assert(r1.payload == r2.payload);
        N::lemma_repr_extensional(r1.next_repr, r2.next_repr);
    }

    fn into_repr(self) -> (r: Self::Repr) {
        CircularNodeRepr { next_repr: self.next.into_repr(), payload: self.payload }
    }

    fn from_repr(r: &Self::Repr) -> (v: Self) {
        CircularListNode { payload: r.payload, next: N::from_repr(&r.next_repr) }
    }

    fn tag(r: &Self::Repr) -> (b: bool) {
        N::tag(&r.next_repr)
    }

    fn set_tag(r: &mut Self::Repr) {
        N::set_tag(&mut r.next_repr);
    }

    fn clear_tag(r: &mut Self::Repr) {
        N::clear_tag(&mut r.next_repr);
    }
}

/// Token for mark/restore (delegates to the inner vector's token).
#[derive(Copy, Clone)]
pub struct CircularListToken {
    pub(crate) entries: VecToken,
}

impl CircularListToken {
    /// Reconstruction coordinate (spec twin).
    pub open(crate) spec fn frame_idx_spec(self) -> nat {
        self.entries.frame_idx as nat
    }
}

/// `rotate(s, k)` = `s` cyclically left-rotated by `k`: `s[k..] ++ s[..k]`.
/// `rotate(s, k)[p] == s[(k + p) mod len]`.
pub open(crate) spec fn rotate(s: Seq<usize>, k: int) -> Seq<usize> {
    s.subrange(k, s.len() as int) + s.subrange(0, k)
}

pub struct CircularList<T, N: DenseId, const TRACK: bool>
where T: Sized + Copy + core::default::Default {
    /// Storage is indexed by the id's own **storage word** `N::Index`, not by
    /// `usize` — production's `VecI<EClassEntry<T>, T::Index>` verbatim. The
    /// width is what makes the semi-persistent diff-log entry `(node, N::Index)`
    /// (16 bytes at 31-bit ids) instead of `(node, usize)` (24 bytes): a `usize`
    /// index would inflate every captured write by 50% for no gain, since the
    /// node count is already bounded by `N::id_bound()`.
    pub(crate) entries: SpVec<
        CircularListNode<T, N>,
        <N as DenseId>::Index,
        InlineStore<CircularListNode<T, N>, <N as DenseId>::Index>,
        TRACK,
    >,
    /// Ghost partition: `model@[c]` is class `c`'s node indices in ring order.
    /// These are *logical* node positions (indices into `entries`), always
    /// `usize`, independent of the `N` chosen for physical storage.
    pub(crate) model: Ghost<Seq<Seq<usize>>>,
    /// Ghost model-snapshot stack (plan Phase 7), parallel to the entries
    /// vec's frame stack; lets `restore(token)` recover the marked ring
    /// partition internally.
    pub(crate) model_snapshots: Ghost<Seq<Seq<Seq<usize>>>>,
}

impl<T, N: DenseId, const TRACK: bool> CircularList<T, N, TRACK>
where T: Sized + Copy + core::default::Default {
    /// `next_seq()[i]` is node `i`'s successor position (the stored id's dense
    /// index). Decoding through `id_nat` is what keeps the ghost `model` — and
    /// every merge lemma stated over it — width-agnostic `usize`.
    pub open(crate) spec fn next_seq(&self) -> Seq<usize> {
        Seq::new(self.entries.view().len(), |i: int| self.entries.view()[i].next.id_nat() as usize)
    }

    /// `payload_seq()[i]` is node `i`'s payload.
    pub open(crate) spec fn payload_seq(&self) -> Seq<T> {
        Seq::new(self.entries.view().len(), |i: int| self.entries.view()[i].payload)
    }

    pub open(crate) spec fn n_spec(&self) -> nat {
        self.entries.view().len()
    }

    /// Entries frame-stack depth (spec twin; fields are `pub(crate)` —
    /// privacy closeout).
    pub open(crate) spec fn depth_spec(&self) -> nat {
        self.entries.depth_spec()
    }

    /// Entries lifetime restore count (spec twin).
    pub open(crate) spec fn fork_count_spec(&self) -> nat {
        self.entries.fork_count_spec()
    }

    /// Entries snapshot stack (spec twin).
    pub open(crate) spec fn entries_snapshots_view(&self) -> Seq<Seq<CircularListNode<T, N>>> {
        self.entries.snapshots_view()
    }

    /// Ring-partition snapshot stack (spec twin, Phase 7 archive).
    pub open(crate) spec fn model_snapshots_view(&self) -> Seq<Seq<Seq<usize>>> {
        self.model_snapshots@
    }

    /// The entries sequence (spec twin; node payload+next pairs).
    pub open(crate) spec fn entries_view(&self) -> Seq<CircularListNode<T, N>> {
        self.entries.view()
    }

    /// Token validity, delegated to the entries component.
    pub open(crate) spec fn is_token_valid_spec(&self, token: CircularListToken) -> bool {
        self.entries.is_token_valid_spec(token.entries)
    }

    /// "Restorable now", delegated to the entries component.
    pub open(crate) spec fn is_restorable_spec(&self, token: CircularListToken) -> bool {
        self.entries.is_restorable_spec(token.entries)
    }

    pub open(crate) spec fn model_view(&self) -> Seq<Seq<usize>> {
        self.model@
    }

    /// in-range: every node named by any ring is allocated.
    pub open(crate) spec fn model_in_range(&self) -> bool {
        let m = self.model@;
        forall|c: int, p: int|
            0 <= c < m.len() && 0 <= p < (#[trigger] m[c]).len() ==> #[trigger] m[c][p] < self.n_spec()
    }

    /// disjoint: a node index occurs in at most one ring at one position.
    pub open(crate) spec fn model_disjoint(&self) -> bool {
        let m = self.model@;
        forall|c1: int, p1: int, c2: int, p2: int|
            0 <= c1 < m.len() && 0 <= p1 < m[c1].len()
                && 0 <= c2 < m.len() && 0 <= p2 < m[c2].len()
                && (#[trigger] m[c1][p1]) == (#[trigger] m[c2][p2])
                    ==> c1 == c2 && p1 == p2
    }

    /// `i` is some ring's member (used as the per-node `covers` predicate).
    pub open(crate) spec fn in_some_ring(&self, i: int) -> bool {
        let m = self.model@;
        exists|c: int, p: int|
            0 <= c < m.len() && 0 <= p < m[c].len() && (#[trigger] m[c][p]) == i
    }

    /// covers: every allocated node is in some ring.
    pub open(crate) spec fn model_covers(&self) -> bool {
        forall|i: int| 0 <= i < self.n_spec() ==> #[trigger] self.in_some_ring(i)
    }

    /// cyclic: `next` of a ring node is its successor, wrapping at the end.
    ///
    /// Trigger note: the pattern is the NEXT-POINTER READ `ns[m[c][p]]`, not the
    /// bare `m[c][p]`. The RHS `m[c][succ]` contains no `ns[..]` application, so
    /// an instantiation cannot re-seed itself — without this the quantifier is a
    /// self-matching loop (its own successor term re-fires the trigger), which
    /// made `RingIter::next` (whose `rotate`/`walk_seq` terms produce many bare
    /// `m[c][_]`) time the solver out. Consumers that need the fact for a
    /// specific `(c,p)` — `lemma_pre_cyclic_at`, the splice lemmas — already
    /// mention `next_seq()[model[c][p]]`, so the read-triggered form still fires
    /// for them.
    pub open(crate) spec fn model_cyclic(&self) -> bool {
        let m = self.model@;
        let ns = self.next_seq();
        forall|c: int, p: int|
            0 <= c < m.len() && 0 <= p < m[c].len()
                ==> #[trigger] ns[m[c][p] as int] == m[c][if p + 1 < m[c].len() { p + 1 } else { 0 }]
    }

    pub open(crate) spec fn wf(&self) -> bool {
        &&& self.entries.wf()
        &&& self.model_in_range()
        &&& self.model_disjoint()
        &&& self.model_covers()
        &&& self.model_cyclic()
        // Model-snapshot agreement (Phase 7). Opaque: ring_snap_wf's nested
        // quantifiers would join every wf-requiring proof's matching context
        // (a z3 matching-loop hazard — see the proof-performance playbook);
        // only mark/restore reveal it, everything else preserves it by
        // congruence (neither the archive nor the vec snapshots change).
        // Keyed on the SNAPSHOT stack (not frames): ops like set/push ensure
        // snapshots_view preservation, so the opaque predicate transfers by
        // congruence; the vec's own wf ties snapshots.len() == frames.len().
        &&& ring_archive_agrees(self.model_snapshots@, self.entries.snapshots_view())
    }

    pub fn new() -> (c: Self)
        ensures c.wf(), c.n_spec() == 0, c.model_view().len() == 0,
            c.entries_snapshots_view().len() == 0,
            c.model_snapshots_view().len() == 0,
    {
        let c = CircularList {
            entries: SpVec::<
                CircularListNode<T, N>,
                <N as DenseId>::Index,
                InlineStore<CircularListNode<T, N>, <N as DenseId>::Index>,
                TRACK,
            >::new(),
            model: Ghost(Seq::empty()),
            model_snapshots: Ghost(Seq::empty()),
        };
        proof {
            assert(c.n_spec() == 0);
            reveal(ring_archive_agrees);
        }
        c
    }

    /// Node count, as the id's storage word — production's `EClasses::len`
    /// returns `T::Index` for exactly this reason (the count is bounded by the
    /// id range, so the narrow word suffices).
    pub fn len(&self) -> (n: <N as DenseId>::Index)
        requires self.wf(),
        ensures n.as_nat() == self.n_spec(),
    {
        self.entries.len()
    }

    pub fn is_empty(&self) -> (b: bool)
        requires self.wf(),
        ensures b == (self.n_spec() == 0),
    {
        self.entries.is_empty()
    }

    /// Bytes consumed by diff tracking only, forwarded from the entries vec.
    /// Diagnostic, no spec content — the same pair production exposes on every
    /// container (`containers/src/vec.rs`), and the pair the consumer's
    /// memory-parity claim is measured through: the ring's retained history is
    /// `(node, N::Index)` per captured write, 16 bytes at 31-bit ids, matching
    /// the hand-rolled `VecI<EClassEntry, u32>` this replaced. Asserted at
    /// runtime in `containers-conformance/tests/differential.rs`.
    pub fn tracking_bytes(&self) -> usize {
        self.entries.tracking_bytes()
    }

    /// Total bytes: this struct + the entries vec's store + its tracking. The
    /// ghost fields cost nothing at runtime (they are erased), so this is the
    /// whole footprint. Diagnostic; no spec content.
    pub fn total_bytes(&self) -> usize {
        self.entries.total_bytes()
    }

    /// `next` of node `i` — its ring successor, returned as the id type itself.
    /// This is the stored word verbatim (no decode), so it is exactly
    /// `next_seq()[i]` under `id_nat`.
    pub fn next_of(&self, i: N) -> (r: N)
        requires self.wf(),
        ensures i.id_nat() < self.n_spec()
            ==> r.id_nat() == self.next_seq()[i.id_nat() as int],
    {
        proof { i.lemma_as_nat_is_id_nat(); }
        // Total-with-documented-panic: explicit node-bound branch.
        if !(i.to_usize() < self.entries.store.data.len()) {
            crate::guard::refuse("CircularList::next_of: node id out of range");
        }
        let r = self.entries.get_index(i.to_index()).next;
        // `next_seq` projects the stored id through `id_nat() as usize`; that
        // cast is lossless because a DenseId's range fits in a usize.
        proof { crate::opt::lemma_id_nat_fits_usize(r); }
        r
    }

    /// Node `i`'s payload. The ring structure carries an arbitrary per-node
    /// payload alongside `next` (production's `EClassEntry` carries the class's
    /// sparse-set repr key there), so the consumer reads and writes it through
    /// this pair rather than owning a second parallel vector.
    pub fn payload_of(&self, i: N) -> (p: T)
        requires self.wf(),
        ensures i.id_nat() < self.n_spec()
            ==> p == self.payload_seq()[i.id_nat() as int],
    {
        proof { i.lemma_as_nat_is_id_nat(); }
        // Total-with-documented-panic: explicit node-bound branch.
        if !(i.to_usize() < self.entries.store.data.len()) {
            crate::guard::refuse("CircularList::payload_of: node id out of range");
        }
        self.entries.get_index(i.to_index()).payload
    }

    /// Overwrite node `i`'s payload, leaving the ring partition untouched. The
    /// stored `next` is read back and rewritten unchanged, so `next_seq` — and
    /// with it every `wf` clause — is preserved by congruence; only
    /// `payload_seq` moves.
    pub fn set_payload(&mut self, i: N, payload: T)
        requires old(self).wf(),
        ensures
            final(self).wf(),
            final(self).n_spec() == old(self).n_spec(),
            final(self).next_seq() == old(self).next_seq(),
            final(self).model_view() == old(self).model_view(),
            final(self).payload_seq() == old(self).payload_seq().update(i.id_nat() as int, payload),
            final(self).entries_snapshots_view() == old(self).entries_snapshots_view(),
            final(self).model_snapshots_view() == old(self).model_snapshots_view(),
    {
        // Total-with-documented-panic: explicit node-bound branch.
        if !(i.to_usize() < self.entries.store.data.len()) {
            crate::guard::refuse("CircularList::set_payload: node id out of range");
        }
        proof { i.lemma_as_nat_is_id_nat(); }
        let iw = i.to_index();
        let next = self.entries.get_index(iw).next;
        self.entries.set_index(iw, CircularListNode { payload, next });
        proof {
            // The stored `next` word is identical at every index, so next_seq
            // (a pointwise `id_nat` projection of it) is unchanged — which is
            // all of `wf` apart from the model clauses, and the model itself
            // was not assigned.
            assert(self.next_seq() =~= old(self).next_seq());
            assert(self.payload_seq() =~= old(self).payload_seq().update(i.id_nat() as int, payload));
            // covers is phrased on `self` (its `in_some_ring` reads `self.model@`),
            // so re-witness it from the old receiver — same model, same witnesses.
            assert forall|k: int| 0 <= k < self.n_spec() implies #[trigger] self.in_some_ring(k) by {
                assert(old(self).in_some_ring(k));
                let (c, p) = choose|c: int, p: int|
                    0 <= c < old(self).model@.len() && 0 <= p < old(self).model@[c].len()
                        && old(self).model@[c][p] == k;
                assert(self.model@[c][p] == k);
            }
            // Phase 7: `set_index` preserves the snapshot stack and the archive
            // was not touched, so the OPAQUE agreement transfers by congruence
            // (no reveal — keeps ring_snap_wf's quantifiers out of scope).
        }
    }

    /// Add a new singleton class: node `n` as its own ring `[n]` with the
    /// self-loop `next[n] == n`, carrying `payload`.
    ///
    /// The new node's id is the pre-push length; it must be representable in the
    /// index type `N` (`< N::id_bound()`) so the stored `next` self-loop
    /// round-trips (`from_usize(id).id_nat() == id`). The e-graph guarantees this
    /// the same way it bounds any dense id — id allocation is width-checked.
    /// Total node allocation (total-API plan phase 3): refuses at either of
    /// `add_singleton`'s two ceilings — the index word, and `N`'s id range one
    /// bit below it — where the partial core's runtime guard panics.
    /// `splice_absorb` has no total form yet: its different-rings
    /// precondition needs the O(1) ring-id witness (plan doc, phase-3
    /// designed item); the debug walk is the interim monitor.
    pub fn try_add_singleton(&mut self, payload: T)
        -> (r: Result<N, crate::error::ContainerError>)
        requires old(self).wf(),
        ensures
            final(self).wf(),
            r matches Ok(nid) ==> nid.id_nat() == old(self).n_spec()
                && final(self).n_spec() == old(self).n_spec() + 1
                && final(self).model_view()
                    == old(self).model_view().push(seq![nid.id_nat() as usize])
                && final(self).payload_seq() == old(self).payload_seq().push(payload),
            r is Err ==> final(self).model_view() == old(self).model_view()
                && final(self).payload_seq() == old(self).payload_seq(),
            final(self).entries_snapshots_view() == old(self).entries_snapshots_view(),
            final(self).model_snapshots_view() == old(self).model_snapshots_view(),

            r matches Err(e) ==> e == crate::error::ContainerError::CapacityExhausted,
    {
        if self.entries.can_push() {
            let n = self.entries.store.data.len();
            proof {
                <N as DenseId>::Index::lemma_max_nat_fits_usize();
                assert(n as nat == self.entries.view().len());
            }
            if N::try_new(n).is_some() && (N::bit_stealing() || N::try_new(n + 1).is_some()) {
                return Ok(self.add_singleton(payload));
            }
        }
        Err(crate::error::ContainerError::CapacityExhausted)
    }

    pub(crate) fn add_singleton(&mut self, payload: T) -> (nid: N)
        requires
            old(self).wf(),
            old(self).n_spec() + 1 < <N as DenseId>::Index::max_nat(),
            // Per id family (production parity: a bit-stealing ring holds its
            // full id range); only the full-range family needs the successor
            // representable, its word having no spare bit.
            old(self).n_spec() < N::id_bound(),
            !N::is_bit_stealing() ==> old(self).n_spec() + 1 < N::id_bound(),
        ensures
            final(self).wf(),
            nid.id_nat() == old(self).n_spec(),
            final(self).n_spec() == old(self).n_spec() + 1,
            final(self).model_view() == old(self).model_view().push(seq![nid.id_nat() as usize]),
            final(self).payload_seq() == old(self).payload_seq().push(payload),
            final(self).payload_seq()[nid.id_nat() as int] == payload,
            final(self).entries_snapshots_view() == old(self).entries_snapshots_view(),
            final(self).model_snapshots_view() == old(self).model_snapshots_view(),
    {
        // Runtime guard for UNVERIFIED callers on the id-range precondition:
        // the sibling word-headroom clause is already trapped by `Vec::len`'s
        // overflow protocol, but `Index::max_nat()` is one bit wider than
        // `id_bound()`, and in the window between them `from_usize` masks —
        // the new node would silently alias node `id - id_bound` and its
        // self-loop would point into an unrelated ring. Same doctrine and
        // shape as `ListArena::{new_list,prepend,append}`.
        proof {
            // `n + 1` fits in usize: the word-headroom precondition bounds it by
            // `Index::max_nat()`, and max_nat is at most usize::MAX + 1.
            <N as DenseId>::Index::lemma_max_nat_fits_usize();
        }
        crate::guard::check_precondition(
            N::try_new(self.entries.len().as_usize()).is_some()
                && (N::bit_stealing()
                    || N::try_new(self.entries.len().as_usize() + 1).is_some()),
            "CircularList::add_singleton: node-id range exhausted",
        );
        // The new node's dense index is the pre-push length. It is representable
        // in `N` (precondition `n_spec < id_bound`), so `from_usize`
        // round-trips and the self-loop `next_seq()[id] == id` holds.
        let idw = self.entries.len();
        let nid = N::from_usize(idw.as_usize());
        let ghost id = nid.id_nat() as usize;
        // Self-loop: the singleton's successor is itself.
        self.entries.push(CircularListNode { payload, next: nid });
        self.model = Ghost(self.model@.push(seq![id]));
        proof {
            let m = self.model@;
            let ns = self.next_seq();
            let cnew = (m.len() - 1) as int;
            assert(m[cnew] =~= seq![id]);
            assert(nid.id_nat() == id as nat);  // from_usize round-trip (id < id_bound)
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
        nid
    }

    /// Ghost: the (ring, position) of node `i`. Well-defined under `wf`
    /// (covers gives existence, disjoint gives uniqueness).
    pub open(crate) spec fn locate(&self, i: int) -> (int, int) {
        choose|c: int, p: int|
            0 <= c < self.model@.len() && 0 <= p < self.model@[c].len() && self.model@[c][p] == i
    }

    /// The node-index sequence a ring walk starting at `start` visits, in
    /// order: the ring of `start` rotated so `start` is first. `class_seq[0] ==
    /// start`, its length is the ring size, and it is a permutation of the
    /// ring's node set — the verified twin of production's `ClassIter` output.
    pub open(crate) spec fn class_seq(&self, start: int) -> Seq<usize> {
        rotate(self.model@[self.locate(start).0], self.locate(start).1)
    }

    /// Iterate the class ring containing `start`, yielding each node index in
    /// ring order beginning at `start` (production's `iter_class`/`ClassIter`).
    /// The cursor wraps once around and stops when it returns to `start` — so
    /// exactly the ring's nodes are visited, each once.
    pub fn iter_class(&self, start: N) -> (it: RingIter<'_, T, N, TRACK>)
        requires self.wf(),
        ensures start.id_nat() < self.n_spec() ==> ({
            &&& it.list_ref() == self
            &&& it.start_spec() == start.id_nat()
            &&& it.pos_spec() == 0
            &&& !it.done_spec()
            &&& it.cursor_ok()
            // The walk enumerates exactly `class_seq(start)` (public twin).
            &&& it.walk_seq() == self.class_seq(start.id_nat() as int)
        }),
    {
        // Total-with-documented-panic: node-bound branch.
        if !(start.to_usize() < self.entries.store.data.len()) {
            crate::guard::refuse("CircularList::iter_class: node id out of range");
        }
        proof {
            // covers ⟹ locate's choose is satisfiable; disjoint ⟹ unique.
            assert(self.in_some_ring(start.id_nat() as int));
        }
        let ghost c = self.locate(start.id_nat() as int).0;
        let ghost p0 = self.locate(start.id_nat() as int).1;
        proof {
            // class_seq(start) == rotate(model[c], p0) == the RingIter's walk_seq.
            lemma_locate_pinned(self, start.id_nat() as int, c, p0);
            lemma_rotate_props(self.model@[c], p0);  // p0 first ⟹ walk_seq[0] == start
        }
        RingIter { list: self, start, cur: start, pos: Ghost(0), done: false, c: Ghost(c), p0: Ghost(p0) }
    }

    /// Debug-build runtime mirror of `splice`'s different-rings precondition
    /// (plan 2.3). `external_body` diagnostic: walks the ring containing `s`
    /// looking for `a` (bounded by the node count) and panics on a hit. A
    /// no-op in release builds — see the rationale at the `splice` call site.
    #[verifier::external_body]
    fn debug_check_different_rings(&self, s: N, a: N)
        requires
            self.wf(),
            s.id_nat() < self.n_spec(),
            a.id_nat() < self.n_spec(),
            self.locate(s.id_nat() as int).0 != self.locate(a.id_nat() as int).0,
    {
        #[cfg(debug_assertions)]
        {
            let su = s.to_usize();
            let au = a.to_usize();
            let mut same_ring = su == au;
            let mut cur = self.entries.get_index(s.to_index()).next.to_usize();
            let mut budget = self.entries.len().as_usize();
            while cur != su && budget > 0 {
                if cur == au {
                    same_ring = true;
                }
                cur = self.entries.get_index(N::from_usize(cur).to_index()).next.to_usize();
                budget -= 1;
            }
            crate::guard::check_precondition_erased(
                !same_ring,
                "CircularList::splice: s and a are in the same ring",
            );
        }
        #[cfg(not(debug_assertions))]
        {
            let _ = (s, a);
        }
    }

    /// Splice the rings (classes) of `s` and `a` by swapping their `next`
    /// pointers — the O(1) circular-list join. For `s`, `a` in **different**
    /// rings this merges the two rings into one; the merged ring's node set is
    /// the union of the two, and its successor structure is again a single
    /// cycle (`wf` preserved — no finite-cycle side condition). The source ring
    /// slot is emptied. Requires `s`, `a` in different rings (the class-merge
    /// use; splicing within one ring would split it).
    ///
    /// Payload-preserving. A caller that also rewrites a payload (the class
    /// merge, which marks the absorbed class's key absent) should use
    /// [`Self::splice_absorb`] rather than following this with `set_payload`:
    /// on a **tracked** ring the separate payload write is a third `set_index`,
    /// and every `set_index` runs the capture protocol. See `splice_absorb`.
    #[verifier::spinoff_prover]
    #[verifier::rlimit(800)]
    pub fn splice(&mut self, sid: N, aid: N)
        requires
            old(self).wf(),
            sid.id_nat() < old(self).n_spec(),
            aid.id_nat() < old(self).n_spec(),
            // different rings
            old(self).locate(sid.id_nat() as int).0 != old(self).locate(aid.id_nat() as int).0,
        ensures
            final(self).wf(),
            final(self).n_spec() == old(self).n_spec(),
            final(self).payload_seq() == old(self).payload_seq(),
            final(self).model_view().len() == old(self).model_view().len(),
            // the two old rings: cs gets the merged ring, ca emptied.
            ({
                let s = sid.id_nat() as int;
                let a = aid.id_nat() as int;
                let cs = old(self).locate(s).0;
                let ca = old(self).locate(a).0;
                let ps = old(self).locate(s).1;
                let pa = old(self).locate(a).1;
                &&& final(self).model_view()[cs]
                        == rotate(old(self).model_view()[cs], ps + 1)
                            + rotate(old(self).model_view()[ca], pa + 1)
                &&& final(self).model_view()[ca] == Seq::<usize>::empty()
                &&& (forall|c: int| 0 <= c < final(self).model_view().len() && c != cs && c != ca
                        ==> #[trigger] final(self).model_view()[c] == old(self).model_view()[c])
            }),
    {
        // Runtime guard (plan 2.3, debug builds only): the different-rings
        // precondition is spec-level (the ghost model is erased at runtime),
        // and a faithful runtime check walks a ring — O(class size) on a hot
        // O(1) operation, an unacceptable complexity change for release
        // builds. Debug builds pay the walk (external_body diagnostic below);
        // release relies on caller discipline — in the e-graph, union-find
        // guarantees distinct classes before a splice, the same discipline
        // production's unchecked ring merge relies on.
        self.debug_check_different_rings(sid, aid);
        // The whole proof below is stated over the dense indices; bind them
        // once (ghost) and the storage words once (exec), so the id→word
        // conversion is paid twice per splice, not per proof step.
        proof {
            // The `as usize` casts below are lossless (dense range fits usize).
            crate::opt::lemma_id_nat_fits_usize(sid);
            crate::opt::lemma_id_nat_fits_usize(aid);
        }
        let ghost s = sid.id_nat() as usize;
        let ghost a = aid.id_nat() as usize;
        let sw = sid.to_index();
        let aw = aid.to_index();
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

        // `to_index` preserves the dense index, so the two storage words address
        // exactly the ghost positions `s` and `a` the proof speaks of.
        assert(sw.as_nat() == s as nat);
        assert(aw.as_nat() == a as nat);

        let s_node = self.entries.get_index(sw);
        let a_node = self.entries.get_index(aw);
        let old_s_next = s_node.next;
        let old_a_next = a_node.next;
        self.entries.set_index(sw, CircularListNode { payload: s_node.payload, next: old_a_next });
        self.entries.set_index(aw, CircularListNode { payload: a_node.payload, next: old_s_next });

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
            // Phase 7: splice only set_index'd two entries — the archive,
            // snapshot stack, and frame stack are untouched (set_index's
            // ensures), so the OPAQUE agreement predicate transfers by
            // congruence; no reveal needed, which keeps ring_snap_wf's nested
            // quantifiers out of this (rlimit-sensitive) proof's context.
            lemma_splice_merge(*old(self), self, s as int, a as int, cs, ca, ps, pa);
        }
    }

    /// [`Self::splice`] with the absorbed node's new payload folded into the
    /// store the ring surgery already performs — the class merge's exact shape
    /// (merge the rings, mark the absorbed class's key absent).
    ///
    /// This exists for a measured reason. `splice` + `set_payload` writes the
    /// absorbed cell **twice**, and on a tracked ring every `set_index` runs the
    /// capture protocol (tag test, and on a first write a diff-log push). Where
    /// production's hand-rolled merge folded the presence-bit clear into the same
    /// full-cell store as the `next` rewrite — 2 cell writes per merge — the
    /// split form pays 3. Folding it back was previously tried and reverted as
    /// "no faster", but that was measured **untracked**, where the third write is
    /// a plain store and LLVM forwards the redundant load
    /// (`containers-conformance/examples/splicesplit.rs`); the tracked path is
    /// where the write count is load-bearing, and there it is worth ~15pp on
    /// `class_merge_restore`.
    ///
    /// Payload-wise this is `set_payload(aid, a_payload)` composed with
    /// `splice(sid, aid)`; `splice` provably preserves payloads, so the order is
    /// observationally irrelevant and the ring postconditions are `splice`'s
    /// verbatim.
    #[verifier::spinoff_prover]
    #[verifier::rlimit(800)]
    pub fn splice_absorb(&mut self, sid: N, aid: N, a_payload: T)
        requires
            old(self).wf(),
            sid.id_nat() < old(self).n_spec(),
            aid.id_nat() < old(self).n_spec(),
            // different rings
            old(self).locate(sid.id_nat() as int).0 != old(self).locate(aid.id_nat() as int).0,
        ensures
            final(self).wf(),
            final(self).n_spec() == old(self).n_spec(),
            // the ONLY difference from `splice`: the absorbed node's payload.
            final(self).payload_seq()
                == old(self).payload_seq().update(aid.id_nat() as int, a_payload),
            final(self).model_view().len() == old(self).model_view().len(),
            ({
                let s = sid.id_nat() as int;
                let a = aid.id_nat() as int;
                let cs = old(self).locate(s).0;
                let ca = old(self).locate(a).0;
                let ps = old(self).locate(s).1;
                let pa = old(self).locate(a).1;
                &&& final(self).model_view()[cs]
                        == rotate(old(self).model_view()[cs], ps + 1)
                            + rotate(old(self).model_view()[ca], pa + 1)
                &&& final(self).model_view()[ca] == Seq::<usize>::empty()
                &&& (forall|c: int| 0 <= c < final(self).model_view().len() && c != cs && c != ca
                        ==> #[trigger] final(self).model_view()[c] == old(self).model_view()[c])
            }),
            final(self).entries_snapshots_view() == old(self).entries_snapshots_view(),
            final(self).model_snapshots_view() == old(self).model_snapshots_view(),
    {
        // Body is `splice`'s verbatim except for the absorbed cell's payload;
        // see `splice` for the commentary on each step.
        self.debug_check_different_rings(sid, aid);
        proof {
            crate::opt::lemma_id_nat_fits_usize(sid);
            crate::opt::lemma_id_nat_fits_usize(aid);
        }
        let ghost s = sid.id_nat() as usize;
        let ghost a = aid.id_nat() as usize;
        let sw = sid.to_index();
        let aw = aid.to_index();
        proof {
            assert(self.in_some_ring(s as int));
            assert(self.in_some_ring(a as int));
        }
        let ghost cs = self.locate(s as int).0;
        let ghost ca = self.locate(a as int).0;
        let ghost ps = self.locate(s as int).1;
        let ghost pa = self.locate(a as int).1;
        let ghost old_m = self.model@;
        proof {
            assert(0 <= cs < old_m.len() && 0 <= ps < old_m[cs].len() && old_m[cs][ps] == s as int);
            assert(0 <= ca < old_m.len() && 0 <= pa < old_m[ca].len() && old_m[ca][pa] == a as int);
        }
        assert(sw.as_nat() == s as nat);
        assert(aw.as_nat() == a as nat);

        let s_node = self.entries.get_index(sw);
        let a_node = self.entries.get_index(aw);
        let old_s_next = s_node.next;
        let old_a_next = a_node.next;
        self.entries.set_index(sw, CircularListNode { payload: s_node.payload, next: old_a_next });
        // The fold: `a_payload` instead of `a_node.payload`, same single store.
        self.entries.set_index(aw, CircularListNode { payload: a_payload, next: old_s_next });

        let merged = Ghost(rotate(old_m[cs], ps + 1) + rotate(old_m[ca], pa + 1));
        self.model = Ghost(self.model@.update(cs, merged@).update(ca, Seq::empty()));

        proof {
            // Payloads: `s`'s is unchanged, `a`'s is the new one, all others by
            // congruence — the `update` in the ensures, extensionally.
            assert(self.payload_seq()
                =~= old(self).payload_seq().update(a as int, a_payload));
            let ns = self.next_seq();
            let old_ns = old(self).next_seq();
            assert(ns[s as int] == old_ns[a as int]);
            assert(ns[a as int] == old_ns[s as int]);
            assert forall|k: int| 0 <= k < self.n_spec() && k != s as int && k != a as int implies
                #[trigger] ns[k] == old_ns[k] by {}
            assert(self.model@.len() == old_m.update(cs, merged@).update(ca, Seq::empty()).len());
            assert(self.model@.len() == old(self).model@.len());
            // `wf` does not constrain payloads, so the merge lemma applies
            // unchanged — this is why the fold is proof-free.
            lemma_splice_merge(*old(self), self, s as int, a as int, cs, ca, ps, pa);
        }
    }

    // ---- semi-persistence: delegate to the inner vector ----

    pub(crate) fn mark(&mut self, shrink: ShrinkPolicy) -> (token: CircularListToken)
        requires
            old(self).wf(),
            TRACK,
            old(self).n_spec() < usize::MAX,
            // inner Vec's u32 depth-cast bound (propagated; guarded there).
            old(self).depth_spec() < u32::MAX,
        ensures
            final(self).wf(),
            final(self).next_seq() == old(self).next_seq(),
            final(self).n_spec() == old(self).n_spec(),
            final(self).model_view() == old(self).model_view(),
            final(self).payload_seq() == old(self).payload_seq(),
            final(self).entries_snapshots_view()
                == old(self).entries_snapshots_view().push(old(self).entries_view()),
            final(self).model_snapshots_view()
                == old(self).model_snapshots_view().push(old(self).model_view()),
            token.frame_idx_spec() == final(self).entries_snapshots_view().len() - 1,
    {
        let entries = self.entries.mark(shrink);
        // Archive the live ring partition alongside the vec snapshot (Phase 7).
        self.model_snapshots = Ghost(self.model_snapshots@.push(self.model@));
        proof {
            assert(self.entries.view() == old(self).entries.view());
            assert(self.model@ == old(self).model@);  // ghost assign touched only model_snapshots
            assert(self.next_seq() =~= old(self).next_seq());
            // model + view unchanged ⟹ covers carries (same witnesses).
            assert forall|i: int| 0 <= i < self.n_spec() implies #[trigger] self.in_some_ring(i) by {
                assert(old(self).in_some_ring(i));
                let (c, p) = choose|c: int, p: int|
                    0 <= c < old(self).model@.len() && 0 <= p < old(self).model@[c].len()
                        && old(self).model@[c][p] == i;
                assert(self.model@[c][p] == i);
            }
            reveal(ring_archive_agrees);
            // The new archive frame: ring_snap_wf(model, just-pushed snapshot)
            // — exactly the live wf clauses over the live view (the snapshot
            // IS the view at mark). Old frames carry over unchanged.
            let k_new = self.model_snapshots@.len() - 1;
            assert(self.entries.snapshots_view()[k_new] == old(self).entries.view());
            assert forall|i: int| 0 <= i < old(self).entries.view().len()
                implies #[trigger] idx_in_some_ring(self.model@, i) by {
                assert(old(self).in_some_ring(i));
            }
            // ring_snap_wf's cyclic clause is over `snap[m[c][p]].next.id_nat()`;
            // model_cyclic (now triggered on the next-pointer READ `ns[m[c][p]]`)
            // gives the same equation via snap == live view. Feed each (c,p) the
            // read term so the retriggered quantifier fires.
            let ghost snap_kn = self.entries.snapshots_view()[k_new];
            assert forall|c: int, p: int|
                0 <= c < self.model@.len() && 0 <= p < self.model@[c].len() implies
                (#[trigger] snap_kn[self.model@[c][p] as int]).next.id_nat() as usize
                    == self.model@[c][if p + 1 < self.model@[c].len() { p + 1 } else { 0 }] by {
                assert(self.next_seq()[self.model@[c][p] as int]
                    == self.model@[c][if p + 1 < self.model@[c].len() { p + 1 } else { 0 }]);
                assert(snap_kn[self.model@[c][p] as int] == self.entries.view()[self.model@[c][p] as int]);
            }
            assert(ring_snap_wf(self.model@, self.entries.snapshots_view()[k_new]));
            assert forall|k: int| 0 <= k < self.model_snapshots@.len()
                implies ring_snap_wf(
                    #[trigger] self.model_snapshots@[k],
                    self.entries.snapshots_view()[k]) by {
                if k < k_new {
                    assert(self.model_snapshots@[k] == old(self).model_snapshots@[k]);
                    assert(self.entries.snapshots_view()[k]
                        == old(self).entries.snapshots_view()[k]);
                }
            }
        }
        CircularListToken { entries }
    }

    /// Restore to the marked snapshot. The restored entries, together with the
    /// ghost model live at the mark, must form a valid ring partition.
    /// "Restorable now" for the token (plan 2.2).
    /// Total mark (Vec's pilot pattern; single component).
    pub fn try_mark(&mut self, shrink: ShrinkPolicy)
        -> (r: Result<CircularListToken, crate::error::ContainerError>)
        requires old(self).wf(),
        ensures
            final(self).wf(),
            r matches Ok(token) ==> {
                &&& final(self).next_seq() == old(self).next_seq()
                &&& final(self).n_spec() == old(self).n_spec()
                &&& final(self).model_view() == old(self).model_view()
                &&& final(self).payload_seq() == old(self).payload_seq()
                &&& final(self).entries_snapshots_view()
                    == old(self).entries_snapshots_view().push(old(self).entries_view())
                &&& final(self).model_snapshots_view()
                    == old(self).model_snapshots_view().push(old(self).model_view())
                &&& token.frame_idx_spec()
                    == final(self).entries_snapshots_view().len() - 1
            },
            r is Err ==> final(self).model_view() == old(self).model_view()
                && final(self).next_seq() == old(self).next_seq(),
    {
        if !TRACK {
            return Err(crate::error::ContainerError::Untracked);
        }
        if !(self.entries.store.data.len() < usize::MAX) {
            return Err(crate::error::ContainerError::CapacityExhausted);
        }
        if !(self.entries.frames.len() < (u32::MAX as usize)) {
            return Err(crate::error::ContainerError::DepthLimit);
        }
        Ok(self.mark(shrink))
    }

    /// Total restore: `is_valid_token` answers exactly "would restore
    /// succeed now" (delegated to the entries component).
    pub fn try_restore(&mut self, token: CircularListToken)
        -> (r: Result<(), crate::error::ContainerError>)
        requires old(self).wf(),
        ensures
            final(self).wf(),
            r is Ok ==> final(self).entries_view()
                == old(self).entries_snapshots_view()[token.frame_idx_spec() as int]
                && final(self).model_view()
                    == old(self).model_snapshots_view()[token.frame_idx_spec() as int]
                && final(self).entries_snapshots_view()
                    == old(self).entries_snapshots_view()
                        .subrange(0, token.frame_idx_spec() as int)
                && final(self).model_snapshots_view()
                    == old(self).model_snapshots_view()
                        .subrange(0, token.frame_idx_spec() as int),
            r is Err ==> final(self).model_view() == old(self).model_view()
                && final(self).next_seq() == old(self).next_seq(),
            r matches Err(e) ==> e == crate::error::ContainerError::InvalidToken,
    {
        if self.is_valid_token(&token) {
            self.restore(token);
            Ok(())
        } else {
            Err(crate::error::ContainerError::InvalidToken)
        }
    }

    pub fn is_valid_token(&self, token: &CircularListToken) -> (b: bool)
        requires self.wf(),
        ensures b == self.is_restorable_spec(*token),
    {
        self.entries.is_valid_token(&token.entries)
    }

    pub(crate) fn restore(&mut self, token: CircularListToken)
        requires
            old(self).wf(),
            TRACK,
            old(self).is_token_valid_spec(token),
            token.frame_idx_spec() < old(self).depth_spec(),
            old(self).depth_spec() < u32::MAX,
            old(self).fork_count_spec() + 1 <= u32::MAX,
        ensures
            final(self).wf(),
            final(self).entries_view()
                == old(self).entries_snapshots_view()[token.frame_idx_spec() as int],
            // Restored to the ring partition archived at that mark (Phase 7).
            final(self).model_view() == old(self).model_snapshots_view()[token.frame_idx_spec() as int],
            final(self).entries_snapshots_view()
                == old(self).entries_snapshots_view().subrange(0, token.frame_idx_spec() as int),
            final(self).model_snapshots_view()
                == old(self).model_snapshots_view().subrange(0, token.frame_idx_spec() as int),
    {
        // Runtime guard (plan 2.3): full restorable predicate before mutation.
        crate::guard::check_precondition(
            self.is_valid_token(&token),
            "CircularList::restore: invalid, foreign, stale, consumed, or abandoned token",
        );
        proof { reveal(ring_archive_agrees); }
        let ghost snap_model = self.model_snapshots@[token.entries.frame_idx_spec() as int];
        let ghost snap = old(self).entries.snapshots_view()[token.entries.frame_idx_spec() as int];
        self.entries.restore(token.entries);
        self.model = Ghost(snap_model);
        self.model_snapshots =
            Ghost(self.model_snapshots@.subrange(0, token.entries.frame_idx_spec() as int));
        proof {
            assert(self.entries.view() == snap);
            let m = self.model@;
            let ns = self.next_seq();
            assert(self.n_spec() == snap.len());
            // bridge ring_snap_wf(snap_model, snap) to wf's clauses.
            assert forall|c: int, p: int|
                0 <= c < m.len() && 0 <= p < m[c].len() implies
                ns[#[trigger] m[c][p] as int] == m[c][if p + 1 < m[c].len() { p + 1 } else { 0 }] by {
                assert(ns[m[c][p] as int] == snap[m[c][p] as int].next.id_nat() as usize);
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
pub(crate) proof fn lemma_splice_merge<T, N: DenseId, const TRACK: bool>(
    pre: CircularList<T, N, TRACK>, post: &CircularList<T, N, TRACK>,
    s: int, a: int, cs: int, ca: int, ps: int, pa: int,
)
    where T: Sized + Copy + core::default::Default, N: DenseId
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
        // splice does not mark/restore: the archive and the vec snapshot/frame
        // stacks are untouched, so the (opaque) Phase 7 agreement transfers
        // from pre by congruence.
        ring_archive_agrees(post.model_snapshots@, post.entries.snapshots_view()),
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
pub(crate) proof fn lemma_rotate_props(x: Seq<usize>, k: int)
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
pub(crate) proof fn lemma_splice_in_range<T, N: DenseId, const TRACK: bool>(
    pre: CircularList<T, N, TRACK>, post: &CircularList<T, N, TRACK>,
    cs: int, ca: int, ps: int, pa: int,
)
    where T: Sized + Copy + core::default::Default, N: DenseId
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
pub(crate) proof fn lemma_splice_disjoint<T, N: DenseId, const TRACK: bool>(
    pre: CircularList<T, N, TRACK>, post: &CircularList<T, N, TRACK>,
    s: int, a: int, cs: int, ca: int, ps: int, pa: int,
)
    where T: Sized + Copy + core::default::Default, N: DenseId
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
pub open(crate) spec fn ring_src(
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
pub(crate) proof fn lemma_ring_src(
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
pub(crate) proof fn lemma_ring_src_injective(
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
pub(crate) proof fn lemma_splice_covers<T, N: DenseId, const TRACK: bool>(
    pre: CircularList<T, N, TRACK>, post: &CircularList<T, N, TRACK>,
    cs: int, ca: int, ps: int, pa: int,
)
    where T: Sized + Copy + core::default::Default, N: DenseId
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
pub(crate) proof fn lemma_splice_cyclic<T, N: DenseId, const TRACK: bool>(
    pre: CircularList<T, N, TRACK>, post: &CircularList<T, N, TRACK>,
    s: int, a: int, cs: int, ca: int, ps: int, pa: int,
)
    where T: Sized + Copy + core::default::Default, N: DenseId
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
pub(crate) proof fn lemma_pre_cyclic_at<T, N: DenseId, const TRACK: bool>(
    pre: CircularList<T, N, TRACK>, c: int, p: int,
)
    where T: Sized + Copy + core::default::Default, N: DenseId
    requires pre.wf(), 0 <= c < pre.model@.len(), 0 <= p < pre.model@[c].len(),
    ensures
        pre.next_seq()[pre.model@[c][p] as int]
            == pre.model@[c][if p + 1 < pre.model@[c].len() { p + 1 } else { 0 }],
{
    // direct from pre.model_cyclic().
}

/// A node in a ring other than cs/ca is neither s nor a (disjointness).
pub(crate) proof fn lemma_other_ring_avoids_sa<T, N: DenseId, const TRACK: bool>(
    pre: CircularList<T, N, TRACK>, s: int, a: int, cs: int, ca: int, c: int, p: int,
)
    where T: Sized + Copy + core::default::Default, N: DenseId
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
pub(crate) proof fn lemma_merge_interior_prefix<T, N: DenseId, const TRACK: bool>(
    pre: CircularList<T, N, TRACK>, post: &CircularList<T, N, TRACK>,
    cs: int, ca: int, ps: int, pa: int, p: int,
)
    where T: Sized + Copy + core::default::Default, N: DenseId
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
pub(crate) proof fn lemma_merge_interior_suffix<T, N: DenseId, const TRACK: bool>(
    pre: CircularList<T, N, TRACK>, post: &CircularList<T, N, TRACK>,
    cs: int, ca: int, ps: int, pa: int, p: int,
)
    where T: Sized + Copy + core::default::Default, N: DenseId
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

/// Forward iterator over one class ring, yielding node indices starting at
/// `start` and wrapping once around (production's `ClassIter`). Carries a
/// physical cursor `cur` (the node at ring position `pos` relative to `start`),
/// so each `next` is O(1): yield `cur`, step it along the verified `next`
/// pointer (which `wf`'s `model_cyclic` ties to the ring), and stop when it
/// returns to `start`. The ghost `(c, p0)` pin the located ring and the start's
/// position within it; `cursor_ok` is "`cur` names `class_seq[pos]`, or the
/// walk is done and `pos == ring length`".
pub struct RingIter<'a, T, N: DenseId, const TRACK: bool>
where T: Sized + Copy + core::default::Default {
    pub(crate) list: &'a CircularList<T, N, TRACK>,
    /// The node the walk started at, as the id type — production's `ClassIter`
    /// stores `start_idx: T`, and yielding `N` (not `usize`) is what lets the
    /// consumer's `iter_class` return `impl Iterator<Item = T>` unchanged.
    pub(crate) start: N,
    /// Physical cursor: the node at ring position `pos` (meaningless once
    /// `done`; `cursor_ok`'s exhausted arm).
    pub(crate) cur: N,
    pub(crate) done: bool,
    /// Ghost cursor position within the walk (0-based from `start`). Purely a
    /// verification device — production's `ClassIter` has no counter, it only
    /// compares `cur` to `start` — so making it ghost keeps exec identical to
    /// production AND sidesteps a spurious `pos+1` usize-overflow obligation.
    /// (Spec-only: erased in plain builds, hence `dead_code`.)
    #[allow(dead_code)]
    pub(crate) pos: Ghost<nat>,
    /// Ghost: the located ring index and `start`'s position within it.
    #[allow(dead_code)]
    pub(crate) c: Ghost<int>,
    #[allow(dead_code)]
    pub(crate) p0: Ghost<int>,
}

/// Disjointness within a single ring: two positions of ring `c` holding the
/// same node index are the same position. Isolates `model_disjoint`'s
/// quad-nested instantiation so `RingIter::next` never brings it into scope.
pub(crate) proof fn lemma_ring_same_pos<T, N: DenseId, const TRACK: bool>(
    list: &CircularList<T, N, TRACK>, c: int, p1: int, p2: int,
)
    where T: Sized + Copy + core::default::Default, N: DenseId
    requires
        list.model_disjoint(),
        0 <= c < list.model@.len(),
        0 <= p1 < list.model@[c].len(),
        0 <= p2 < list.model@[c].len(),
        list.model@[c][p1] == list.model@[c][p2],
    ensures p1 == p2,
{
    // direct instantiation of model_disjoint at (c,p1),(c,p2).
}

/// The ring-walk step arithmetic (pure). With `j = (p0+oldpos) mod len` and
/// `jn = (j+1) mod len` (each a single conditional subtraction, valid because
/// `p0, oldpos < len`), the successor position `jn` equals the start position
/// `p0` exactly when the walk has come full circle (`oldpos+1 == len`); and
/// when it has not, `jn` is the rotation index of `oldpos+1`.
pub(crate) proof fn lemma_ring_step_arith(p0: int, oldpos: int, len: int, j: int, jn: int)
    requires
        0 <= p0 < len,
        0 <= oldpos < len,
        j == (if p0 + oldpos < len { p0 + oldpos } else { p0 + oldpos - len }),
        jn == (if j + 1 < len { j + 1 } else { 0 }),
    ensures
        0 <= j < len,
        0 <= jn < len,
        (jn == p0) <==> (oldpos + 1 == len),
        (oldpos + 1 < len)
            ==> jn == (if p0 + (oldpos + 1) < len { p0 + (oldpos + 1) } else { p0 + (oldpos + 1) - len }),
{
    // All linear; the case-splits on the two conditional subtractions decide it.
}

/// `locate` is pinned: if `(c, p0)` names `start` (`model[c][p0] == start`),
/// then under disjointness `locate(start) == (c, p0)`, so the caller-facing
/// `class_seq(start)` equals the iterator's internal walk `rotate(model[c],
/// p0)`. Isolates the `choose`/disjoint reasoning out of the hot `next` body.
pub(crate) proof fn lemma_locate_pinned<T, N: DenseId, const TRACK: bool>(
    list: &CircularList<T, N, TRACK>, start: int, c: int, p0: int,
)
    where T: Sized + Copy + core::default::Default, N: DenseId
    requires
        list.model_disjoint(),
        0 <= c < list.model@.len(),
        0 <= p0 < list.model@[c].len(),
        list.model@[c][p0] == start,
    ensures
        list.locate(start) == (c, p0),
        list.class_seq(start) == rotate(list.model@[c], p0),
{
    // covers/existence gives locate a witness; disjoint forces it to (c, p0).
    let (lc, lp) = list.locate(start);
    assert(0 <= lc < list.model@.len() && 0 <= lp < list.model@[lc].len()
        && list.model@[lc][lp] == start);  // choose satisfies its predicate
    assert(list.model_disjoint());  // (lc,lp) and (c,p0) both name start ⟹ equal
}

impl<'a, T, N: DenseId, const TRACK: bool> RingIter<'a, T, N, TRACK>
where T: Sized + Copy + core::default::Default {
    /// The list this iterator walks (spec twin; fields are `pub(crate)`).
    pub open(crate) spec fn list_ref(&self) -> &'a CircularList<T, N, TRACK> {
        self.list
    }

    pub open(crate) spec fn start_spec(&self) -> nat { self.start.id_nat() }
    pub open(crate) spec fn pos_spec(&self) -> nat { self.pos@ }
    pub open(crate) spec fn done_spec(&self) -> bool { self.done }
    /// Ghost located-ring index (spec twin; field is `pub(crate)`).
    pub open(crate) spec fn c_spec(&self) -> int { self.c@ }
    /// Ghost start-position-within-ring (spec twin).
    pub open(crate) spec fn p0_spec(&self) -> int { self.p0@ }

    /// The located ring (`model[c]`).
    pub open(crate) spec fn ring(&self) -> Seq<usize> {
        self.list.model@[self.c@]
    }

    /// The walk sequence, phrased on the STORED `(c, p0)` — `rotate(ring, p0)`.
    /// Equal to `class_seq(start)` once `locate` is pinned (lemma_locate_pinned),
    /// but referencing `p0@` directly keeps `locate`'s `choose` out of the hot
    /// `next` body (referencing `class_seq` there timed the solver out).
    pub open(crate) spec fn walk_seq(&self) -> Seq<usize> {
        rotate(self.ring(), self.p0@)
    }

    /// Cursor validity: `(c, p0)` correctly locate `start`, and — while live —
    /// `cur` names the next node to yield (`walk_seq[pos]`), in range. Once
    /// `done`, the whole ring has been visited (`pos == ring length`).
    pub open(crate) spec fn cursor_ok(&self) -> bool {
        let m = self.list.model@;
        let ring = self.ring();
        &&& 0 <= self.c@ < m.len()
        &&& 0 <= self.p0@ < ring.len()
        &&& ring[self.p0@] as nat == self.start.id_nat()
        &&& self.pos@ <= ring.len()
        &&& (self.done <==> self.pos@ == ring.len())
        &&& (!self.done ==> {
                &&& (self.pos@ as int) < ring.len()
                &&& self.cur.id_nat() == self.walk_seq()[self.pos@ as int] as nat
                &&& self.cur.id_nat() < self.list.n_spec()
            })
    }

    /// Yield `walk_seq[pos]` (= `class_seq(start)[pos]`, a node index) and
    /// advance the cursor — O(1) per call. Returns `None` once the ring has
    /// been fully traversed. The contract is stated on `walk_seq()` (the
    /// stored-`p0` phrasing); `walk_seq() == class_seq(start)` under `wf`
    /// (lemma_locate_pinned), which the public `class_seq` accessor bridges.
    #[verifier::spinoff_prover]
    #[verifier::rlimit(50)]
    pub fn next(&mut self) -> (r: Option<N>)
        requires
            old(self).list_ref().wf(),
            old(self).cursor_ok(),
        ensures
            final(self).list_ref() == old(self).list_ref(),
            final(self).start_spec() == old(self).start_spec(),
            final(self).c_spec() == old(self).c_spec(),
            final(self).p0_spec() == old(self).p0_spec(),
            final(self).cursor_ok(),
            !old(self).done_spec() ==> {
                &&& r is Some
                // The yielded id's dense index is the walk position's node —
                // stated through `id_nat` because the model is width-agnostic.
                &&& r->Some_0.id_nat() == old(self).walk_seq()[old(self).pos_spec() as int] as nat
                &&& final(self).pos_spec() == old(self).pos_spec() + 1
            },
            old(self).done_spec() ==> {
                &&& r is None
                &&& final(self).pos_spec() == old(self).pos_spec()
            },
    {
        if self.done {
            return None;
        }
        let result = self.cur;
        let ghost ring = self.ring();
        let ghost len = ring.len() as int;
        let ghost oldpos = self.pos@ as int;
        // j = (p0 + pos) mod len — the ring position `cur` sits at. Valid as a
        // single conditional subtraction since p0, pos < len ⟹ p0+pos < 2*len.
        let ghost j = if self.p0@ + oldpos < len {
            self.p0@ + oldpos
        } else {
            self.p0@ + oldpos - len
        };
        // jn = (j + 1) mod len — the successor position (nxt sits here).
        let ghost jn = if j + 1 < len { j + 1 } else { 0 };
        proof {
            lemma_rotate_props(ring, self.p0@);
            lemma_ring_step_arith(self.p0@, oldpos, len, j, jn);
            // cur == walk_seq[pos] == rotate(ring, p0)[pos] == ring[j].
            assert(self.cur.id_nat() == ring[j] as nat);
            assert(self.cur.id_nat() < self.list.n_spec());
        }
        let nxt = self.list.next_of(self.cur);
        proof {
            // model_cyclic at (c, j): next_seq()[ring[j]] == ring[jn]. Routed
            // through lemma_pre_cyclic_at (as the splice proofs do) so the
            // solver never SEARCHES model_cyclic's quantifier — the direct
            // instantiation is what caused a matching loop / rlimit blow-up.
            assert(nxt.id_nat() == self.list.next_seq()[self.cur.id_nat() as int] as nat);
            lemma_pre_cyclic_at(*self.list, self.c@, j);
            assert(self.list.next_seq()[self.cur.id_nat() as int] == ring[jn]);
            assert(nxt.id_nat() == ring[jn] as nat);
        }
        // Identity test on the dense index, not on `PartialEq` — `N`'s `==` has
        // no spec contract, but `to_usize`'s ensures ties the word to `id_nat`,
        // and `lemma_id_injective` makes index equality decide id equality. In
        // exec this is production's `current_idx == start_idx` verbatim (both
        // ids are already clean words; `to_usize` is a cast).
        let wrapped = nxt.to_usize() == self.start.to_usize();
        proof {
            // wrapped ⟺ ring[jn] == ring[p0] ⟺ jn == p0 (disjointness),
            // isolated in pure lemmas so this body never pulls wf's quad-nested
            // foralls into the solver (that made it rlimit-blow-up / time out).
            if wrapped {
                lemma_ring_same_pos(self.list, self.c@, jn, self.p0@);  // jn == p0
            }
            if jn == self.p0@ {
                assert(nxt.id_nat() == self.start.id_nat());  // ring[jn] == ring[p0]
                assert(wrapped);
            }
        }
        proof {
            self.pos@ = self.pos@ + 1;  // ghost counter (production has none)
        }
        if wrapped {
            self.done = true;
        } else {
            self.cur = nxt;
        }
        proof {
            let newpos = self.pos@ as int;   // oldpos + 1
            // done ⟺ wrapped ⟺ jn == p0 ⟺ newpos == len (lemma_ring_step_arith).
            if self.done {
                assert(newpos == len);
                assert(self.pos@ == ring.len());
            } else {
                assert(newpos < len);
                // jn is the rotation index of newpos (lemma_ring_step_arith), so
                // cur == ring[jn] == rotate(ring, p0)[newpos] == walk_seq[newpos].
                assert(self.cur.id_nat() == self.walk_seq()[newpos] as nat);
                assert(self.cur.id_nat() < self.list.n_spec());
            }
        }
        Some(result)
    }
}

/// `i` appears in some ring of `model` (the per-node `covers` predicate, with a
/// clean trigger for the outer `forall|i|`).
/// The Phase 7 archive agreement, opaque (see `wf`'s comment): the ghost
/// model-snapshot stack is parallel to the frame stack and each archived
/// partition describes its archived entry snapshot.
#[verifier::opaque]
pub open(crate) spec fn ring_archive_agrees<T, N: DenseId>(
    archive: Seq<Seq<Seq<usize>>>, snaps: Seq<Seq<CircularListNode<T, N>>>,
) -> bool {
    &&& archive.len() == snaps.len()
    &&& (forall|k: int| 0 <= k < archive.len()
            ==> ring_snap_wf(#[trigger] archive[k], snaps[k]))
}

pub open(crate) spec fn idx_in_some_ring(model: Seq<Seq<usize>>, i: int) -> bool {
    exists|c: int, p: int|
        0 <= c < model.len() && 0 <= p < model[c].len() && (#[trigger] model[c][p]) == i
}

/// Structural ring-partition validity over a raw snapshot + its ghost model
/// (for `restore`): the model and entries jointly satisfy the same in-range +
/// disjoint + covers + cyclic clauses as `wf`.
pub open(crate) spec fn ring_snap_wf<T, N: DenseId>(model: Seq<Seq<usize>>, entries: Seq<CircularListNode<T, N>>) -> bool {
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
                ==> (#[trigger] entries[model[c][p] as int]).next.id_nat() as usize
                        == model[c][if p + 1 < model[c].len() { p + 1 } else { 0 }])
}

} // verus!

// prod-parity: the consumer's `EClassesToken` derives `Debug` and bundles this
// token, so it must be `Debug` (matching `VecToken`/`ListArenaToken`). Manual,
// not derived — `#[derive(Debug)]` inside `verus!{}` is unsupported.
impl core::fmt::Debug for CircularListToken {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("CircularListToken")
            .field("entries", &self.entries)
            .finish()
    }
}

// ---------------------------------------------------------------------------
// Trusted glue (outside verus!{}; trust ledger group E): std Iterator via a
// 1-line delegation to the verified inherent `next`, mirroring `ListIter`.
// Yields node indices in ring order (production's `ClassIter`).
// ---------------------------------------------------------------------------
impl<'a, T, N: DenseId, const TRACK: bool> Iterator for RingIter<'a, T, N, TRACK>
where
    T: Sized + Copy + core::default::Default,
{
    type Item = N;

    #[inline(always)]
    fn next(&mut self) -> Option<N> {
        RingIter::next(self)
    }
}

// ---------------------------------------------------------------------------
// White-box oracle access (plain Rust; see bplus.rs's matching comment).
// Read-only — cannot violate any invariant.
// ---------------------------------------------------------------------------
impl<T, N: DenseId, const TRACK: bool> CircularList<T, N, TRACK>
where
    T: Sized + Copy + core::default::Default,
{
    /// Read-only entries access for white-box tests.
    #[doc(hidden)]
    pub fn white_box_entries(
        &self,
    ) -> &SpVec<
        CircularListNode<T, N>,
        <N as DenseId>::Index,
        InlineStore<CircularListNode<T, N>, <N as DenseId>::Index>,
        TRACK,
    > {
        &self.entries
    }
}
