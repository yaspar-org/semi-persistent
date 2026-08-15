// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Arena-backed intrusive singly-linked lists with semi-persistence (verified).
//!
//! `ListArena` owns two arenas, each a verified `Vec` over `InlineStore`:
//!   - `heads[L]`  — per-list head pointer (+ tail index for O(1) append);
//!   - `nodes[k]`  — `{ payload, next }`, the intrusive node cells.
//! This is the *parent use-list* of the e-graph (production: `list.rs`'s
//! `ListArena`), supporting O(1) `prepend`, O(1) `append` (via the cached
//! tail), and O(1) `splice` (link dst's tail to src's head).
//!
//! ## The invariant: a ghost model list (NOT index ordering)
//!
//! Each list `l` carries a **ghost `Seq<usize>`** — the indices of its nodes in
//! list order — kept in `model@[l]`. The abstract content `list_seq(l)` is the
//! payload read off that finite sequence, so it is defined without any
//! recursion over `next` and needs no termination measure. The physical
//! pointers are a *cache* of the model, tied to it by `wf`:
//!   - `heads[l].head` is null iff `model[l]` is empty, else points at
//!     `model[l][0]`; `heads[l].tail` is `model[l].last()`;
//!   - for each list position `p`, `nodes[model[l][p]].next_ref()` points at
//!     `model[l][p+1]` (null at the end).
//! The only constraint on a `next`/`head` target is that it is **in range**
//! `[0, nodes.len())` — there is deliberately NO "next points to a smaller
//! index" discipline (that earlier crutch made the chain-walk terminate by a
//! decreasing index, but it is false for `append`/`splice`, which link a node
//! forward to a freshly-pushed — larger — index). A global **disjointness**
//! invariant (each node index occurs in at most one list, at most once) makes
//! the models partition a subset of `[0, nodes.len())`; from it, every list is
//! at most as long as the arena, and relinking one list frames the others.
//!
//! ## Storage layout (production parity)
//! - Both columns are `InlineStore`, as production's are: the capture flag is
//!   stolen from a niche in the element's own `Tagged` repr, so there is no side
//!   bit-vector on either side. This needs `ListNode`/`ListHead` to BE `Tagged`,
//!   which they are (impls below, mirroring `containers/src/list.rs:52-138`):
//!   a node delegates the tag to its payload, a header steals it from the tail
//!   word. The payload bound is therefore `T: Tagged` — satisfied at the real
//!   call site, where the e-graph instantiates `T` with a `DenseId` (and
//!   `DenseId: Tagged`).
//! - Both columns are indexed by `L::Index`/`N::Index` (production's
//!   `VecI<ListHead<N>, L::Index>` / `VecI<ListNode<T, N>, N::Index>`), not by
//!   `usize`: the index width is what a semi-persistent diff-log entry `(T, I)`
//!   and a frame are made of, so a `usize` index would inflate every captured
//!   write for no gain — the row count is already bounded by the id range. The
//!   verified core still speaks `usize` (the ghost model is `Seq<usize>`); the
//!   two widths meet only in the `head_ix`/`node_ix`/`heads_len`/`nodes_len`
//!   bridge, where the conversion is TOTAL because an in-bounds row is below
//!   `Index::max_nat()` by the store's own `wf`.
//! - Net effect, asserted exactly in
//!   `containers-conformance/tests/list_arena_differential.rs`: `tracking_bytes`
//!   is byte-identical to production's and `total_bytes` differs by a constant
//!   16 (the `u64` vs `u32` `ContainerId`, migration plan 2.6), at any size.
//! - `Copy + Default` throughout (the crate convention; `Vec::restore` regrow).

use vstd::prelude::*;

use crate::diff_store::DiffStore;
use crate::index_like::IndexLike;
use crate::inline_store::InlineStore;
use crate::opt::DenseId;
use crate::tagged::Tagged;
use crate::vec::{ShrinkPolicy, Vec as SpVec, VecToken};

verus! {

/// Optional node pointer (model-level `Opt<NodeId>`; `some==false` is null).
#[derive(Copy, Clone)]
pub struct NodeRef {
    pub some: bool,
    pub idx: usize,
}

impl NodeRef {
    pub open(crate) spec fn is_null(self) -> bool {
        !self.some
    }
    pub open(crate) spec fn target(self) -> nat {
        self.idx as nat
    }
    #[inline(always)]
    pub fn null() -> (r: NodeRef) ensures r.is_null() {
        NodeRef { some: false, idx: 0 }
    }
    #[inline(always)]
    pub fn is_null_exec(&self) -> (b: bool) ensures b == self.is_null() {
        !self.some
    }
    #[inline(always)]
    pub fn to(i: usize) -> (r: NodeRef) ensures !r.is_null(), r.idx == i {
        NodeRef { some: true, idx: i }
    }
}

impl core::default::Default for NodeRef {
    fn default() -> (r: NodeRef) ensures r.is_null() {
        NodeRef { some: false, idx: 0 }
    }
}

/// Intrusive node: payload + NICHE-PACKED next pointer (production layout).
///
/// The next pointer is stored as `Opt<N>`'s repr — the None tag stolen from
/// the id's spare MSB — so the node is `payload + one id word` (8 bytes for a
/// u32-id payload vs 24 with an unpacked `{bool, usize}` pointer; list
/// traversal is a pointer-chase, so node bytes are cache misses). `NodeRef`
/// remains the SPEC view via [`ListNode::next_ref`]; exec reads/writes go
/// through [`ListNode::next`]/[`ListNode::set_next`], whose contracts tie the
/// packed repr to that view using the verified `Tagged` round-trip laws.
#[derive(Copy)]
pub struct ListNode<T, N: DenseId + Tagged> {
    pub payload: T,
    /// `pub` (not `pub(crate)`) so the `Tagged` impl's `open spec fn value_of`
    /// can construct a node: an open spec body may only mention fields at least
    /// as visible as itself, and the trait's spec fns are public. Writing the
    /// field is still guarded — `set_next` is the only verified packing
    /// primitive and every mutation path goes through it.
    pub next_repr: <N as Tagged>::Repr,
}

// Hand-written `Clone` (a plain copy); the autoderived `Clone` on a generic
// struct emits a "clone is not a copy" warning under Verus otherwise.
impl<T: Copy, N: DenseId + Tagged> Clone for ListNode<T, N> {
    fn clone(&self) -> (r: Self)
        ensures r == *self,
    {
        *self
    }
}

impl<T, N: DenseId + Tagged> ListNode<T, N> {
    /// The next pointer's spec view: null iff the tag is set, else the
    /// packed id's dense index. Canonical (null is always `{false, 0}`), so
    /// `NodeRef` equalities in the model lemmas keep working unchanged.
    pub open(crate) spec fn next_ref(self) -> NodeRef {
        if N::tag_of(self.next_repr) {
            NodeRef { some: false, idx: 0 }
        } else {
            NodeRef { some: true, idx: N::value_of(self.next_repr).id_nat() as usize }
        }
    }

    /// Well-formed repr + in-range target (needed so `as usize` in the spec
    /// view and `as_usize` in the exec read agree).
    pub open(crate) spec fn next_wf(self) -> bool {
        N::repr_wf(self.next_repr)
    }

    /// Read the next pointer (unpack the niche).
    pub(crate) fn next(&self) -> (r: NodeRef)
        requires self.next_wf(),
        ensures r == self.next_ref(),
    {
        let o = crate::opt::Opt::<N>::from_raw(self.next_repr);
        if o.is_none() {
            NodeRef { some: false, idx: 0 }
        } else {
            let id = o.get();
            proof {
                // id == value_of(repr); as_usize == id_nat.
                assert(id == N::value_of(self.next_repr));
                // as_usize's ensures is stated in `as_nat` (IndexLike supertrait);
                // bridge to `id_nat` so `idx == id_nat` holds. prod-parity.
                id.lemma_as_nat_is_id_nat();
            }
            NodeRef { some: true, idx: id.as_usize() }
        }
    }

}

impl<T, N: DenseId + Tagged + core::default::Default> ListNode<T, N> {
    /// Write the next pointer (pack into the niche). `r.idx` must be a
    /// representable id (callers hold `idx < N::id_bound()` from the arena's
    /// allocation guard).
    pub(crate) fn set_next(&mut self, r: NodeRef)
        requires !r.is_null() ==> (r.idx as nat) < N::id_bound(),
        ensures
            final(self).next_wf(),
            final(self).next_ref() == r || (r.is_null() && final(self).next_ref() == NodeRef { some: false, idx: 0 }),
            final(self).payload == old(self).payload,
    {
        if r.some {
            let id = N::from_usize(r.idx);
            let o = crate::opt::Opt::<N>::some(id);
            self.next_repr = o.into_raw();
            proof {
                assert(!N::tag_of(self.next_repr));
                assert(N::value_of(self.next_repr) == id);
                assert(id.id_nat() == r.idx as nat);
                assert(self.next_ref() == r);
            }
        } else {
            let o = crate::opt::Opt::<N>::none();
            self.next_repr = o.into_raw();
            proof {
                assert(N::tag_of(self.next_repr));
                assert(self.next_ref() == NodeRef { some: false, idx: 0 });
            }
        }
    }
}

impl<T: core::default::Default, N: DenseId + Tagged + core::default::Default>
    core::default::Default for ListNode<T, N>
{
    fn default() -> (r: ListNode<T, N>)
        ensures r.next_wf(), r.next_ref().is_null(),
    {
        let o = crate::opt::Opt::<N>::none();
        ListNode { payload: T::default(), next_repr: o.into_raw() }
    }
}

/// Repr for `ListNode`: the payload's repr carries the capture tag, the packed
/// next-pointer word rides along untagged. Production parity — its `ListNode`
/// has `type Repr = (T::Repr, <N as Tagged>::Repr)` and delegates the tag to
/// `T` (`containers/src/list.rs:52-73`). A named struct rather than a tuple
/// because Verus's trait-conflict checker rejects `Tagged` impls on tuples (the
/// same limitation behind `Pair`/`BoolTagged`).
#[derive(Copy)]
pub struct ListNodeRepr<TR, NR> {
    pub a: TR,
    pub b: NR,
}

impl<TR: Copy, NR: Copy> Clone for ListNodeRepr<TR, NR> {
    fn clone(&self) -> (r: Self)
        ensures r == *self,
    {
        *self
    }
}

/// `Tagged` for `ListNode`, delegating to the payload — production's impl
/// verbatim. This is what lets the node arena live in an `InlineStore`: the
/// capture flag is stolen from a niche the payload already owns, so no side
/// bit-vector is needed and the footprint matches production's exactly.
impl<T: Tagged, N: DenseId + Tagged> Tagged for ListNode<T, N> {
    type Repr = ListNodeRepr<T::Repr, <N as Tagged>::Repr>;

    open spec fn value_of(r: Self::Repr) -> Self {
        ListNode { payload: T::value_of(r.a), next_repr: r.b }
    }
    open spec fn tag_of(r: Self::Repr) -> bool {
        T::tag_of(r.a)
    }
    open spec fn repr_wf(r: Self::Repr) -> bool {
        T::repr_wf(r.a)
    }

    proof fn lemma_repr_extensional(r1: Self::Repr, r2: Self::Repr) {
        // The payload's extensionality pins `a`; `b` is exposed directly in
        // `value_of` (as `next_repr`), so equal views force it equal too.
        T::lemma_repr_extensional(r1.a, r2.a);
    }

    fn into_repr(self) -> (r: Self::Repr) {
        ListNodeRepr { a: self.payload.into_repr(), b: self.next_repr }
    }
    fn from_repr(r: &Self::Repr) -> (v: Self) {
        ListNode { payload: T::from_repr(&r.a), next_repr: r.b }
    }
    fn tag(r: &Self::Repr) -> (b: bool) {
        T::tag(&r.a)
    }
    fn set_tag(r: &mut Self::Repr) {
        T::set_tag(&mut r.a);
    }
    fn clear_tag(r: &mut Self::Repr) {
        T::clear_tag(&mut r.a);
    }
}

/// Per-list header: head pointer, (when non-empty) tail node index, and a cached
/// element count. `len` mirrors the ghost model length (`wf`'s `cache_len` clause),
/// so `ListArena::len` is O(1) and *verified* to return the true list length, not
/// merely trusted. Maintained on `prepend`/`append` (+1) and `splice` (dst gains
/// src's count, src resets to 0).
// `Clone` here is a copy: `N: Tagged` and `Tagged: Copy`, so every field is
// `Copy` and the derived body is a bitwise move. Verus cannot see that through
// the derive, which emits an `N: Clone` bound rather than `N: Copy`, so it warns
// that it is deriving `Clone` without a specification. The two non-generic
// `#[derive(Copy, Clone)]` structs in this module (`NodeRef`, `ListArenaToken`)
// do not warn for exactly that reason. Nothing in the crate calls
// `ListHead::clone` — the type is used by value — so the missing `Clone` spec
// costs nothing.
#[verifier::allow(autoderive_clone_without_spec)]
#[derive(Copy, Clone)]
pub struct ListHead<N: DenseId + Tagged> {
    // `pub` for the same reason as `ListNode::next_repr`: the `Tagged` impl's
    // open spec bodies construct and project a header. Mutation still goes
    // through the verified `set_head`/`set_tail` packing primitives.
    //
    // `head_repr` is a packed word because it must encode "empty" in a niche
    // (`head_ref`/`head_wf` read it as an `Opt<N>`). `tail` is a bare id: it is
    // only meaningful when the head is Some, so it needs no None encoding, and
    // keeping it unpacked is what lets the `Tagged` impl below project it with
    // `N::value_of` — a projection the trait's laws already preserve across
    // `set_tag`/`clear_tag`. Same size either way (an id is its own word).
    pub head_repr: <N as Tagged>::Repr,
    pub tail: N,
    /// Cached element count, in the NODE arena's index type — see [`ListHead::len_spec`].
    pub len: N::Index,
}

impl<N: DenseId + Tagged> ListHead<N> {
    /// Head pointer's spec view (canonical null, like `ListNode::next_ref`).
    pub open(crate) spec fn head_ref(self) -> NodeRef {
        if N::tag_of(self.head_repr) {
            NodeRef { some: false, idx: 0 }
        } else {
            NodeRef { some: true, idx: N::value_of(self.head_repr).id_nat() as usize }
        }
    }

    /// Tail node index (meaningful only when the list is non-empty; the
    /// stored id's dense index — production keeps the same convention).
    pub open(crate) spec fn tail_spec(self) -> usize {
        self.tail.id_nat() as usize
    }

    /// Cached length, projected to `nat`.
    ///
    /// The field is `N::Index` — the node arena's index type — because a list's
    /// length is bounded by the node arena's population and by nothing else. It was
    /// `u32`, which put a hard 4-billion ceiling on a single list at *every* id
    /// width: reachable for a 63-bit `N`, where the arena itself has room for far
    /// more, and a ceiling the caller had to keep proving it stayed under (the
    /// `< 0x1_0000_0000` precondition every mutator used to carry). Widening it to
    /// `N::Index` makes that obligation *derivable* instead — `lemma_len_bounded`
    /// already bounds a list by the arena, and the store's own `wf` bounds the arena
    /// by `Index::max_nat()` — so the preconditions are gone and no caller states a
    /// length bound at all.
    ///
    /// Free at both id widths, hence unconditional: at a 31-bit `N` the field was
    /// already 4 bytes, and at a 63-bit `N` the header is two 8-byte words plus the
    /// count, which pads to 24 either way (`containers-conformance/tests/layout_parity.rs`).
    ///
    /// `nat`, not `usize`: the count is compared against ghost sequence lengths
    /// throughout, and `N::Index`'s projection to `nat` (`as_nat`) is the exact one.
    pub open(crate) spec fn len_spec(self) -> nat {
        self.len.as_nat()
    }

    /// Repr well-formedness. Only the head word is packed now (the tail is a
    /// bare id, which is well-formed by construction), so this is a single
    /// conjunct where it used to be two.
    pub open(crate) spec fn head_wf(self) -> bool {
        N::repr_wf(self.head_repr)
    }
}

impl<N: DenseId + Tagged + core::default::Default> ListHead<N> {
    /// Read the head pointer (unpack).
    pub(crate) fn head(&self) -> (r: NodeRef)
        requires self.head_wf(),
        ensures r == self.head_ref(),
    {
        let o = crate::opt::Opt::<N>::from_raw(self.head_repr);
        if o.is_none() {
            NodeRef { some: false, idx: 0 }
        } else {
            let id = o.get();
            proof {
                assert(id == N::value_of(self.head_repr));
                id.lemma_as_nat_is_id_nat();  // as_nat -> id_nat bridge. prod-parity
            }
            NodeRef { some: true, idx: id.as_usize() }
        }
    }

    /// Read the tail index (the tail is a bare id; no unpacking needed).
    pub(crate) fn tail(&self) -> (r: usize)
        requires self.head_wf(),
        ensures r == self.tail_spec(),
    {
        let id = self.tail;
        proof { id.lemma_as_nat_is_id_nat(); }  // as_usize -> id_nat bridge. prod-parity
        id.as_usize()
    }

    /// Write the head pointer (pack).
    pub(crate) fn set_head(&mut self, r: NodeRef)
        requires !r.is_null() ==> (r.idx as nat) < N::id_bound(),
        ensures
            N::repr_wf(final(self).head_repr),
            final(self).tail == old(self).tail,
            final(self).len == old(self).len,
            final(self).head_ref() == r
                || (r.is_null() && final(self).head_ref() == NodeRef { some: false, idx: 0 }),
    {
        if r.some {
            let id = N::from_usize(r.idx);
            let o = crate::opt::Opt::<N>::some(id);
            self.head_repr = o.into_raw();
            proof {
                assert(!N::tag_of(self.head_repr));
                assert(N::value_of(self.head_repr) == id);
                assert(self.head_ref() == r);
            }
        } else {
            let o = crate::opt::Opt::<N>::none();
            self.head_repr = o.into_raw();
        }
    }

    /// Write the tail index (`t < N::id_bound()` from allocation). The tail is
    /// a bare id, so this is a direct store — no niche packing.
    pub(crate) fn set_tail(&mut self, t: usize)
        requires (t as nat) < N::id_bound(),
        ensures
            final(self).head_repr == old(self).head_repr,
            final(self).len == old(self).len,
            final(self).tail_spec() == t,
    {
        let id = N::from_usize(t);
        self.tail = id;
        proof { assert(id.id_nat() == t as nat); }
    }

    /// Read-only unpacked head for white-box tests.
    #[doc(hidden)]
    #[verifier::external_body]
    pub fn white_box_head(&self) -> Option<usize> {
        let o = crate::opt::Opt::<N>::from_raw(self.head_repr);
        if o.is_none() { None } else { Some(o.get().as_usize()) }
    }
}

impl<N: DenseId + Tagged + core::default::Default> core::default::Default for ListHead<N> {
    fn default() -> (r: ListHead<N>)
        ensures r.head_wf(), r.head_ref().is_null(), r.len_spec() == 0,
    {
        let o = crate::opt::Opt::<N>::none();
        let none_repr = o.into_raw();
        let zero = N::from_usize(0);
        proof { <N::Index as IndexLike>::lemma_min_as_nat(); }
        ListHead { head_repr: none_repr, tail: zero, len: <N::Index as IndexLike>::min() }
    }
}

/// Repr for `ListHead`: tail word first (it carries the capture tag), then the
/// head word, then the cached length. Production's tuple ordering verbatim
/// (`containers/src/list.rs:116-138`: `(tail_repr, head_repr, len)` with `tag`
/// delegating to `.0`).
///
/// Both `a` and `b` are `<N as Tagged>::Repr`-typed words and `c` is the node
/// arena's index type, so this struct has exactly production's
/// `(Repr, Repr, N::Index)` layout — the whole point of the exercise. The tag is
/// stolen from `a` (the tail), which the header stores as a bare id, so
/// `into_repr`/`from_repr` pack and unpack it through `N`'s own verified `Tagged`
/// round-trip.
///
/// `I` is a second type parameter rather than a hardcoded `u32` for the reason
/// [`ListHead::len_spec`] gives: the stored count follows the node index width, so a
/// 63-bit arena is not capped at 4 billion elements per list.
#[derive(Copy)]
pub struct ListHeadRepr<NR, I> {
    pub a: NR,
    pub b: NR,
    pub c: I,
}

impl<NR: Copy, I: Copy> Clone for ListHeadRepr<NR, I> {
    fn clone(&self) -> (r: Self)
        ensures r == *self,
    {
        *self
    }
}

/// `Tagged` for `ListHead`, stealing the tag from the TAIL word — production's
/// choice, and a deliberate one: the head word must keep its own niche to encode
/// the empty list (`head_wf`/`head_ref` read it as an `Opt<N>`), whereas the tail
/// is only ever read when the head is Some, so its spare bit is genuinely free.
impl<N: DenseId + Tagged> Tagged for ListHead<N> {
    type Repr = ListHeadRepr<<N as Tagged>::Repr, N::Index>;

    // `value_of` projects the tail word through `N::value_of`, which strips the
    // stolen bit and yields the clean id — exactly the type the header stores.
    // That is what makes the tag invisible to the header's value: `set_tag` and
    // `clear_tag` move only the bit, and `N`'s own laws say `N::value_of`
    // survives them, so `value_of` is preserved as the trait requires. Storing
    // the tail as an id rather than a repr is what makes this a pure projection
    // (a repr-typed tail would need a spec-level re-pack, which the `Tagged`
    // trait deliberately does not expose).
    open spec fn value_of(r: Self::Repr) -> Self {
        ListHead { head_repr: r.b, tail: N::value_of(r.a), len: r.c }
    }
    open spec fn tag_of(r: Self::Repr) -> bool {
        N::tag_of(r.a)
    }
    open spec fn repr_wf(r: Self::Repr) -> bool {
        N::repr_wf(r.a)
    }

    proof fn lemma_repr_extensional(r1: Self::Repr, r2: Self::Repr) {
        // `a` is pinned by N's extensionality; `b` and `c` are exposed directly
        // in `value_of`, so equal views force them equal.
        N::lemma_repr_extensional(r1.a, r2.a);
    }

    fn into_repr(self) -> (r: Self::Repr) {
        ListHeadRepr { a: self.tail.into_repr(), b: self.head_repr, c: self.len }
    }
    fn from_repr(r: &Self::Repr) -> (v: Self) {
        ListHead { head_repr: r.b, tail: N::from_repr(&r.a), len: r.c }
    }
    fn tag(r: &Self::Repr) -> (b: bool) {
        N::tag(&r.a)
    }
    fn set_tag(r: &mut Self::Repr) {
        N::set_tag(&mut r.a);
    }
    fn clear_tag(r: &mut Self::Repr) {
        N::clear_tag(&mut r.a);
    }
}

/// Token bundling the two inner-vector tokens.
#[derive(Copy, Clone)]
pub struct ListArenaToken {
    pub(crate) heads: VecToken,
    pub(crate) nodes: VecToken,
}

impl ListArenaToken {
    /// Reconstruction coordinates of the two components (spec twins).
    pub open(crate) spec fn heads_frame_idx_spec(self) -> nat {
        self.heads.frame_idx as nat
    }

    pub open(crate) spec fn nodes_frame_idx_spec(self) -> nat {
        self.nodes.frame_idx as nat
    }
}

/// Typed-id list arena (production parity: `ListArena<T, L, N, TRACK>` with
/// `L` the list-handle id type and `N` the node id type). The verified CORE
/// operates on `usize` rows (the ghost model and every proof below); `L`/`N`
/// type the API boundary, with conversions through the verified `DenseId`
/// axioms (`id_nat` injective + bounded). `N` bounds node allocation
/// (production's `VecI<_, N::Index>` capacity); nodes are otherwise internal
/// — the iterator yields payloads by value, as production's does.
pub struct ListArena<T, L, N, const TRACK: bool>
where
    T: Sized + Copy + core::default::Default + Tagged,
    L: DenseId,
    N: DenseId + Tagged + core::default::Default,
{
    pub(crate) heads: SpVec<ListHead<N>, L::Index, InlineStore<ListHead<N>, L::Index>, TRACK>,
    pub(crate) nodes: SpVec<ListNode<T, N>, N::Index, InlineStore<ListNode<T, N>, N::Index>, TRACK>,
    pub(crate) _l: core::marker::PhantomData<L>,
    pub(crate) _n: core::marker::PhantomData<N>,
    /// Ghost model: `model@[l]` is the in-order node indices of list `l`.
    pub(crate) model: Ghost<Seq<Seq<usize>>>,
    /// Ghost model-snapshot stack (plan Phase 7): `model_snapshots@[k]` is the
    /// model live at frame `k`'s mark, parallel to the inner vecs' snapshot
    /// stacks (`wf`'s agreement clauses). Lets `restore(token)` recover the
    /// marked model internally — no caller-supplied `Ghost` parameter.
    pub(crate) model_snapshots: Ghost<Seq<Seq<Seq<usize>>>>,
}

impl<T, L, N, const TRACK: bool> ListArena<T, L, N, TRACK>
where
    T: Sized + Copy + core::default::Default + Tagged,
    L: DenseId,
    N: DenseId + Tagged + core::default::Default,
{
    // -- index-width bridge --------------------------------------------------
    //
    // The inner vecs are indexed by `L::Index`/`N::Index` (production parity:
    // `VecI<ListHead<N>, L::Index>` / `VecI<ListNode<T, N>, N::Index>`,
    // `containers/src/list.rs:151-152`), so a diff-log entry is `(T, u32)` and a
    // frame is `(u32, ..)` on both sides rather than verus paying `usize` per
    // logged cell. The verified CORE below still speaks `usize` — the ghost
    // model is `Seq<usize>` and every proof is stated over it — so these two
    // helpers are the only places the widths meet.
    //
    // The conversion is TOTAL, not fallible, which is what keeps it out of the
    // proof body: a row index that is `< view().len()` is `< Index::max_nat()`
    // by the store's own `wf` (`InlineStore::wf_spec` carries
    // `data@.len() < I::max_nat()`), so `try_from_usize` cannot be `None` at
    // any in-bounds index. Each wrapper discharges that once and hands the core
    // a plain index; no call site needs its own bound.

    /// `usize` row -> `L::Index`, for an index known in-bounds for `heads`.
    #[inline(always)]
    pub(crate) fn head_ix(&self, i: usize) -> (r: L::Index)
        requires
            self.heads.wf(),
            i < self.heads_view().len(),
        ensures r.as_nat() == i as nat,
    {
        proof { self.lemma_head_row_fits(i as nat); }
        match <L::Index as crate::index_like::IndexLike>::try_from_usize(i) {
            Some(x) => x,
            None => {
                // Unreachable: the bound above proves `try_from_usize` is Some.
                proof { assert(false); }
                #[allow(clippy::empty_loop)]
                loop
                    invariant false,
                    decreases 0int,
                {
                }
            }
        }
    }

    /// `usize` row -> `N::Index`, for an index known in-bounds for `nodes`.
    #[inline(always)]
    pub(crate) fn node_ix(&self, i: usize) -> (r: N::Index)
        requires
            self.nodes.wf(),
            i < self.nodes_view().len(),
        ensures r.as_nat() == i as nat,
    {
        proof { self.lemma_node_row_fits(i as nat); }
        match <N::Index as crate::index_like::IndexLike>::try_from_usize(i) {
            Some(x) => x,
            None => {
                proof { assert(false); }
                #[allow(clippy::empty_loop)]
                loop
                    invariant false,
                    decreases 0int,
                {
                }
            }
        }
    }

    // -- cached-length arithmetic -------------------------------------------
    //
    // `ListHead::len` is `N::Index`, so growing it is index arithmetic, and it goes
    // through the checked operations for the same reason `head_ix`/`node_ix` go through
    // `try_from_usize`: `N::Index` may be narrower than the word carrying it (a 31-bit
    // node id lives in a `u32` whose MSB is the capture flag), so a sum that does not
    // overflow the word can still fail to be an index. A raw `+` would produce a value
    // whose top bit reads as a tag, which is not a length at all.
    //
    // Both are TOTAL, like the two row-index bridges: the `requires` is discharged once
    // at each call site from `wf` (via `lemma_len_bounded` / `lemma_concat_len_bounded`
    // and `lemma_nodes_len_fits`), so the `None` arm is dead and provably so. That is the
    // whole reason the mutators below no longer carry a length precondition.

    /// `len + 1` as a node-arena index.
    #[inline(always)]
    pub(crate) fn len_incr(len: N::Index) -> (r: N::Index)
        requires len.as_nat() + 1 < <N::Index as crate::index_like::IndexLike>::max_nat(),
        ensures r.as_nat() == len.as_nat() + 1,
    {
        match crate::index_like::checked_incr(len) {
            Some(x) => x,
            None => {
                // Unreachable: the bound above proves `checked_incr` is Some.
                proof { assert(false); }
                #[allow(clippy::empty_loop)]
                loop
                    invariant false,
                    decreases 0int,
                {
                }
            }
        }
    }

    /// `a + b` as a node-arena index (splice: the destination gains the source's count).
    #[inline(always)]
    pub(crate) fn len_add(a: N::Index, b: N::Index) -> (r: N::Index)
        requires
            a.as_nat() + b.as_nat() < <N::Index as crate::index_like::IndexLike>::max_nat(),
        ensures r.as_nat() == a.as_nat() + b.as_nat(),
    {
        match crate::index_like::checked_add(a, b) {
            Some(x) => x,
            None => {
                proof { assert(false); }
                #[allow(clippy::empty_loop)]
                loop
                    invariant false,
                    decreases 0int,
                {
                }
            }
        }
    }

    /// `heads.len()` as a `usize` row count (the core's width). The inner vec
    /// returns `L::Index`; `as_usize`'s ensures is stated in `as_nat`, which is
    /// exactly the vec's `len` postcondition, so the bridge is definitional.
    #[inline(always)]
    pub(crate) fn heads_len(&self) -> (n: usize)
        requires self.heads.wf(),
        ensures n as nat == self.heads_view().len(),
    {
        self.heads.len().as_usize()
    }

    /// `nodes.len()` as a `usize` row count. Same bridge as `heads_len`.
    #[inline(always)]
    pub(crate) fn nodes_len(&self) -> (n: usize)
        requires self.nodes.wf(),
        ensures n as nat == self.nodes_view().len(),
    {
        self.nodes.len().as_usize()
    }

    /// Push headroom, per id family: an arena with room for one more
    /// id-representable node also has room in the storage WORD. This is what
    /// lets the `push` sites state the id-range precondition — the meaningful
    /// bound (it limits what a `next` pointer can name) — rather than a
    /// second, separate one about the storage word `N::Index`.
    ///
    /// The two arms of `lemma_id_bound_word_relation`:
    ///   - bit-stealing (Id31/Id63): `Index::max_nat() == 2 * id_bound`, and
    ///     `len < id_bound` gives `len + 1 <= id_bound < 2 * id_bound`. The
    ///     arena therefore holds its FULL id range, `id_bound` nodes —
    ///     production parity (production's own test fills all 128 slots of a
    ///     7-bit arena).
    ///   - full-range (`DenseUsize`): `Index::max_nat() == id_bound ==
    ///     usize::MAX + 1`, no spare bit, so this family alone also needs the
    ///     successor representable (the second hypothesis; same split as
    ///     `UnionFind::try_make_set`).
    pub(crate) proof fn lemma_node_push_fits(len: nat)
        requires
            len < N::id_bound(),
            !N::is_bit_stealing() ==> len + 1 < N::id_bound(),
        ensures len + 1 < <N::Index as IndexLike>::max_nat(),
    {
        N::lemma_id_bound_word_relation();
        if N::is_bit_stealing() {
            // max_nat == 2 * id_bound >= id_bound + 1 >= len + 2 > len + 1.
            assert(N::id_bound() >= 1);
            assert(N::id_bound() * 2 >= N::id_bound() + 1) by (nonlinear_arith)
                requires N::id_bound() >= 1;
        }
        // full-range arm: max_nat == id_bound, so the hypothesis IS the goal.
    }

    /// The `heads` twin of `lemma_node_push_fits`, over `L`.
    pub(crate) proof fn lemma_head_push_fits(len: nat)
        requires
            len < L::id_bound(),
            !L::is_bit_stealing() ==> len + 1 < L::id_bound(),
        ensures len + 1 < <L::Index as IndexLike>::max_nat(),
    {
        L::lemma_id_bound_word_relation();
        if L::is_bit_stealing() {
            assert(L::id_bound() >= 1);
            assert(L::id_bound() * 2 >= L::id_bound() + 1) by (nonlinear_arith)
                requires L::id_bound() >= 1;
        }
    }

    /// Any in-bounds `heads` row is representable in `L::Index`. The store's
    /// `wf` bounds its data length by `Index::max_nat()`, and `view()` IS that
    /// data, so an index below the length is below the bound.
    pub(crate) proof fn lemma_head_row_fits(&self, i: nat)
        requires
            self.heads.wf(),
            i < self.heads_view().len(),
        ensures i < <L::Index as crate::index_like::IndexLike>::max_nat(),
    {
    }

    /// Same for `nodes` / `N::Index`.
    pub(crate) proof fn lemma_node_row_fits(&self, i: nat)
        requires
            self.nodes.wf(),
            i < self.nodes_view().len(),
        ensures i < <N::Index as crate::index_like::IndexLike>::max_nat(),
    {
    }

    /// The node arena's *population* — not just any row in it — is representable in
    /// `N::Index`. One past the last row, which `lemma_node_row_fits` does not give.
    ///
    /// This is what retires the length-bound preconditions the mutators used to carry.
    /// A list's cached count is bounded by the arena (`lemma_len_bounded`,
    /// `lemma_concat_len_bounded`) and the arena is bounded here, so `len + 1` and
    /// `dst.len + src.len` are both in range as a consequence of `wf` — no caller has
    /// to state it, and there is nothing left for a caller to state it *wrongly*.
    ///
    /// Empty body: the bound is literally `InlineStore::wf_spec`'s first conjunct
    /// (`data@.len() < I::max_nat()`), and `nodes_view()` is that data mapped through
    /// `value_of`, which preserves length.
    pub(crate) proof fn lemma_nodes_len_fits(&self)
        requires self.nodes.wf(),
        ensures self.nodes_view().len() < <N::Index as crate::index_like::IndexLike>::max_nat(),
    {
    }

    pub open(crate) spec fn nodes_view(&self) -> Seq<ListNode<T, N>> {
        self.nodes.view()
    }
    pub open(crate) spec fn heads_view(&self) -> Seq<ListHead<N>> {
        self.heads.view()
    }
    /// Heads/nodes frame-stack depths and snapshot stacks (spec twins;
    /// fields are `pub(crate)` — privacy closeout).
    pub open(crate) spec fn heads_depth_spec(&self) -> nat {
        self.heads.depth_spec()
    }

    pub open(crate) spec fn nodes_depth_spec(&self) -> nat {
        self.nodes.depth_spec()
    }

    pub open(crate) spec fn heads_snapshots_view(&self) -> Seq<Seq<ListHead<N>>> {
        self.heads.snapshots_view()
    }

    pub open(crate) spec fn nodes_snapshots_view(&self) -> Seq<Seq<ListNode<T, N>>> {
        self.nodes.snapshots_view()
    }

    pub open(crate) spec fn heads_fork_count_spec(&self) -> nat {
        self.heads.fork_count_spec()
    }

    pub open(crate) spec fn nodes_fork_count_spec(&self) -> nat {
        self.nodes.fork_count_spec()
    }

    /// Model-snapshot stack (spec twin, Phase 7 archive).
    pub open(crate) spec fn model_snapshots_view(&self) -> Seq<Seq<Seq<usize>>> {
        self.model_snapshots@
    }

    /// Per-component token validity (composite).
    pub open(crate) spec fn is_token_valid_spec(&self, token: ListArenaToken) -> bool {
        &&& self.heads.is_token_valid_spec(token.heads)
        &&& self.nodes.is_token_valid_spec(token.nodes)
    }

    /// "Restorable now" for the composite token.
    pub open(crate) spec fn is_restorable_spec(&self, token: ListArenaToken) -> bool {
        &&& self.heads.is_restorable_spec(token.heads)
        &&& self.nodes.is_restorable_spec(token.nodes)
    }

    /// Composite restore preconditions (everything except the same-mark
    /// frame agreement, which restore states explicitly).
    pub open(crate) spec fn restore_pre_spec(&self, token: ListArenaToken) -> bool {
        &&& self.heads.is_token_valid_spec(token.heads)
        &&& token.heads.frame_idx_spec() < self.heads.depth_spec()
        &&& self.heads.depth_spec() < u32::MAX
        &&& self.heads.fork_count_spec() + 1 <= u32::MAX
        &&& self.nodes.is_token_valid_spec(token.nodes)
        &&& token.nodes.frame_idx_spec() < self.nodes.depth_spec()
        &&& self.nodes.depth_spec() < u32::MAX
        &&& self.nodes.fork_count_spec() + 1 <= u32::MAX
    }

    pub open(crate) spec fn model_view(&self) -> Seq<Seq<usize>> {
        self.model@
    }

    /// In-range: every node index named by any list is allocated. (The ONLY
    /// constraint on a list-membership index — no ordering.)
    pub open(crate) spec fn model_in_range(&self) -> bool {
        let model = self.model@;
        let nodes = self.nodes_view();
        forall|l: int, p: int|
            0 <= l < model.len() && 0 <= p < (#[trigger] model[l]).len()
                ==> #[trigger] model[l][p] < nodes.len()
    }

    /// Disjointness: a node index occurs in at most one list at one position.
    /// Makes the models partition a subset of `[0, nodes.len())`, so each list
    /// is at most as long as the arena and relinking one list frames the rest.
    pub open(crate) spec fn model_disjoint(&self) -> bool {
        let model = self.model@;
        forall|l1: int, p1: int, l2: int, p2: int|
            0 <= l1 < model.len() && 0 <= p1 < model[l1].len()
                && 0 <= l2 < model.len() && 0 <= p2 < model[l2].len()
                && (#[trigger] model[l1][p1]) == (#[trigger] model[l2][p2])
                    ==> l1 == l2 && p1 == p2
    }

    /// Cache consistency: `head`/`tail`/`next` match the model's endpoints.
    pub open(crate) spec fn cache_ok(&self) -> bool {
        let model = self.model@;
        let heads = self.heads_view();
        let nodes = self.nodes_view();
        &&& (forall|l: int| 0 <= l < model.len() ==> {
                let h = (#[trigger] heads[l]).head_ref();
                if model[l].len() == 0 {
                    h.is_null()
                } else {
                    !h.is_null() && h.target() == model[l][0]
                }
            })
        &&& (forall|l: int| 0 <= l < model.len() && (#[trigger] model[l]).len() > 0
                ==> heads[l].tail_spec() == model[l][model[l].len() - 1])
        &&& (forall|l: int, p: int|
                0 <= l < model.len() && 0 <= p < model[l].len() ==> {
                    let nx = nodes[#[trigger] model[l][p] as int].next_ref();
                    if p == model[l].len() - 1 {
                        nx.is_null()
                    } else {
                        !nx.is_null() && nx.target() == model[l][p + 1]
                    }
                })
    }

    /// Cached-length consistency: each header's `len` equals its model list length.
    /// This is what makes the O(1) `len()` accessor return the true length.
    ///
    /// Stated through `len_spec()` (the field's projection to `nat`) rather than on the
    /// field: `len` is `N::Index`, so comparing it to a ghost `Seq::len()` needs the
    /// projection the index type already provides.
    pub open(crate) spec fn cache_len(&self) -> bool {
        let model = self.model@;
        let heads = self.heads_view();
        forall|l: int| 0 <= l < model.len()
            ==> (#[trigger] heads[l]).len_spec() == (#[trigger] model[l]).len()
    }

    /// Packed-repr invariant: every stored next-repr is Tagged-well-formed
    /// (so reads round-trip) and the arena never outgrows N's id range (so
    /// every next target is representable — the packing precondition).
    pub open(crate) spec fn nodes_repr_wf(&self) -> bool {
        &&& self.nodes_view().len() <= N::id_bound()
        &&& forall|i: int| 0 <= i < self.nodes_view().len()
                ==> (#[trigger] self.nodes_view()[i]).next_wf()
        &&& forall|l: int| 0 <= l < self.heads_view().len()
                ==> (#[trigger] self.heads_view()[l]).head_wf()
    }

    pub open(crate) spec fn wf(&self) -> bool {
        &&& self.heads.wf()
        &&& self.nodes.wf()
        &&& self.nodes_repr_wf()
        &&& self.model@.len() == self.heads_view().len()
        &&& self.model_in_range()
        &&& self.model_disjoint()
        &&& self.cache_ok()
        &&& self.cache_len()
        // Model-snapshot agreement (Phase 7): the ghost model stack is
        // parallel to the inner vecs' snapshot stacks (mark/restore keep them
        // in lockstep — one mark pushes both, one restore truncates both),
        // and each archived model describes the archived vec snapshots.
        // Opaque + keyed on the snapshot stacks (see circular_list's wf
        // comment): ops ensure snapshots_view preservation, so this transfers
        // by congruence without joining their matching contexts.
        &&& arena_archive_agrees(self.model_snapshots@,
                self.heads.snapshots_view(), self.nodes.snapshots_view())
    }

    /// Every list is at most as long as the node arena: its model index sequence has
    /// no duplicates (from `model_disjoint`), and each index lies in `[0, nodes.len())`
    /// (from `model_in_range`), so by pigeonhole `model[l].len() <= nodes.len()`. This
    /// bounds the cached `len` and makes the `+1` in `prepend`/`append` overflow-free
    /// (callers already require `nodes.len() + 1 < usize::MAX`).
    pub(crate) proof fn lemma_len_bounded(&self, l: int)
        requires self.wf(), 0 <= l < self.model_view().len(),
        ensures self.model_view()[l].len() <= self.nodes_view().len(),
    {
        let s = self.model@[l];
        let n = self.nodes_view().len();
        // Work over the int-cast index sequence so the range set is `Set<int>`.
        let si = s.map(|_i: int, x: usize| x as int);
        assert(si.len() == s.len());
        // 1. si has no duplicates: a repeat would violate model_disjoint (same list,
        //    two positions, same index).
        assert(si.no_duplicates()) by {
            assert forall|p1: int, p2: int|
                0 <= p1 < si.len() && 0 <= p2 < si.len() && p1 != p2
                implies si[p1] != si[p2] by {
                // model_disjoint at (l,p1),(l,p2): equal index ⇒ p1 == p2.
                assert(si[p1] == s[p1] as int);
                assert(si[p2] == s[p2] as int);
            }
        }
        // 2. no-dup seq ⇒ len == to_set().len().
        si.unique_seq_to_set();
        // 3. to_set() ⊆ set_int_range(0, n): every element is in-range.
        let range = vstd::set_lib::set_int_range(0, n as int);
        assert(si.to_set().subset_of(range)) by {
            assert forall|x: int| #![trigger range.contains(x)] si.to_set().contains(x) implies range.contains(x) by {
                // x is some si[p] == s[p] as int, which model_in_range bounds to [0, n).
                let p = choose|p: int| 0 <= p < si.len() && si[p] == x;
                assert(0 <= p < si.len() && si[p] == x);
                assert(self.model@[l][p] < n);  // model_in_range
            }
        }
        // 4. cardinality: |to_set()| <= |range| == n.
        vstd::set_lib::lemma_int_range(0, n as int);
        vstd::set_lib::lemma_len_subset(si.to_set(), range);
    }

    /// Two distinct lists' combined length is at most the arena size: their
    /// concatenated index sequence has no duplicates (each is internally
    /// duplicate-free and they share no index, both from `model_disjoint`) and
    /// every index is in `[0, nodes.len())`. Bounds `splice`'s `dst.len + src.len`.
    /// Measured ~53.1M rlimit (3.0s) -- 5.3x the default budget of 10, so this
    /// genuinely needs a raise; 120 is ~2.3x measured need. It was 400.
    #[verifier::spinoff_prover]
    #[verifier::rlimit(120)]
    pub(crate) proof fn lemma_concat_len_bounded(&self, a: int, b: int)
        requires
            self.wf(),
            0 <= a < self.model_view().len(),
            0 <= b < self.model_view().len(),
            a != b,
        ensures
            self.model_view()[a].len() + self.model_view()[b].len()
                <= self.nodes_view().len(),
    {
        let sa = self.model@[a];
        let sb = self.model@[b];
        let cat = sa + sb;
        let n = self.nodes_view().len();
        let ci = cat.map(|_i: int, x: usize| x as int);
        assert(ci.len() == cat.len());
        assert(cat.len() == sa.len() + sb.len());
        // no duplicates in the concatenation: within-a, within-b (both from
        // model_disjoint at a single list), and across a/b (disjoint lists).
        assert(ci.no_duplicates()) by {
            assert forall|p1: int, p2: int|
                0 <= p1 < ci.len() && 0 <= p2 < ci.len() && p1 != p2
                implies ci[p1] != ci[p2] by {
                // map each position back to (list, pos) in a or b, then disjointness.
                let l1 = if p1 < sa.len() { a } else { b };
                let q1 = if p1 < sa.len() { p1 } else { p1 - sa.len() };
                let l2 = if p2 < sa.len() { a } else { b };
                let q2 = if p2 < sa.len() { p2 } else { p2 - sa.len() };
                assert(cat[p1] == self.model@[l1][q1]);
                assert(cat[p2] == self.model@[l2][q2]);
                // model_disjoint: equal index ⇒ (l1,q1) == (l2,q2); but (p1)!=(p2)
                // maps to distinct (l,q), so the indices differ.
                assert(ci[p1] == cat[p1] as int);
                assert(ci[p2] == cat[p2] as int);
            }
        }
        ci.unique_seq_to_set();
        let range = vstd::set_lib::set_int_range(0, n as int);
        assert(ci.to_set().subset_of(range)) by {
            assert forall|x: int| #![trigger range.contains(x)] ci.to_set().contains(x) implies range.contains(x) by {
                let p = choose|p: int| 0 <= p < ci.len() && ci[p] == x;
                assert(0 <= p < ci.len() && ci[p] == x);
                let lp = if p < sa.len() { a } else { b };
                let qp = if p < sa.len() { p } else { p - sa.len() };
                assert(cat[p] == self.model@[lp][qp]);
                assert(self.model@[lp][qp] < n);  // model_in_range
            }
        }
        vstd::set_lib::lemma_int_range(0, n as int);
        vstd::set_lib::lemma_len_subset(ci.to_set(), range);
    }

    /// The abstract content of list `l`: payloads read off the model, in order.
    /// No recursion over `next` — defined directly on the finite model seq.
    pub open(crate) spec fn list_seq(&self, l: int) -> Seq<T> {
        let model = self.model@;
        let nodes = self.nodes_view();
        Seq::new(model[l].len(), |p: int| nodes[model[l][p] as int].payload)
    }

    pub fn new() -> (a: Self)
        ensures a.wf(), a.heads_view().len() == 0, a.nodes_view().len() == 0,
            a.model_view().len() == 0,
            a.heads_snapshots_view().len() == 0,
            a.nodes_snapshots_view().len() == 0,
            a.model_snapshots_view().len() == 0,
    {
        let a = ListArena {
            heads:
                SpVec::<ListHead<N>, L::Index, InlineStore<ListHead<N>, L::Index>, TRACK>::new(),
            nodes:
                SpVec::<ListNode<T, N>, N::Index, InlineStore<ListNode<T, N>, N::Index>, TRACK>::new(),
            _l: core::marker::PhantomData,
            _n: core::marker::PhantomData,
            model: Ghost(Seq::empty()),
            model_snapshots: Ghost(Seq::empty()),
        };
        proof { reveal(arena_archive_agrees); }
        a
    }

    /// Create a new empty list; returns its id.
    pub(crate) fn new_list_raw(&mut self) -> (l: usize)
        requires
            old(self).wf(),
            old(self).heads_view().len() + 1 < usize::MAX,
            // Row headroom in `L`'s id range, per family. The heads column is
            // indexed by `L::Index` (production parity), so growing it needs
            // the WORD to have room; `lemma_head_push_fits` derives that from
            // the id bound. A bit-stealing `L` holds its full id range; only
            // the full-range family needs the successor representable too.
            old(self).heads_view().len() < L::id_bound(),
            !L::is_bit_stealing() ==> old(self).heads_view().len() + 1 < L::id_bound(),
        ensures
            final(self).wf(),
            l == old(self).heads_view().len(),
            final(self).nodes_view() == old(self).nodes_view(),
            final(self).model_view() == old(self).model_view().push(Seq::<usize>::empty()),
            final(self).list_seq(l as int) == Seq::<T>::empty(),
            // existing lists unchanged.
            forall|m: int| 0 <= m < old(self).model_view().len()
                ==> #[trigger] final(self).list_seq(m) == old(self).list_seq(m),
            final(self).heads_snapshots_view() == old(self).heads_snapshots_view(),
            final(self).nodes_snapshots_view() == old(self).nodes_snapshots_view(),
            final(self).model_snapshots_view() == old(self).model_snapshots_view(),
    {
        let l = self.heads_len();
        proof { Self::lemma_head_push_fits(self.heads_view().len()); }
        self.heads.push(ListHead::default());
        self.model = Ghost(self.model@.push(Seq::empty()));
        proof {
            let model = self.model@;
            assert(model[l as int].len() == 0);
            assert(self.heads_view()[l as int].head_ref().is_null());
            assert(self.list_seq(l as int) =~= Seq::<T>::empty());
            // existing lists: model + nodes unchanged, head[m] unchanged.
            assert forall|m: int| 0 <= m < old(self).model_view().len() implies
                #[trigger] self.list_seq(m) == old(self).list_seq(m) by {
                assert(model[m] == old(self).model_view()[m]);
                assert(self.list_seq(m) =~= old(self).list_seq(m));
            }
            // disjointness preserved: the new list is empty (no indices).
            assert(self.model_disjoint());
        }
        l
    }

    /// Prepend `payload` to the front of list `l`. Pushes a fresh node (at the
    /// arena's end — a *larger* index than anything in the list, which the old
    /// index-ordering crutch forbade and is now simply fine), links it to the
    /// old head, and makes it the new model[l][0].
    pub(crate) fn prepend_raw(&mut self, l: usize, payload: T)
        requires
            old(self).wf(),
            (l as int) < old(self).model_view().len(),
            old(self).nodes_view().len() + 1 < usize::MAX,
            // Packing headroom, per id family: the fresh slot's id must be
            // representable, and `lemma_node_push_fits` derives the `N::Index`
            // word bound from that. A bit-stealing `N` holds its full id range
            // (production parity); only the full-range family also needs the
            // successor representable, because its word has no spare bit.
            old(self).nodes_view().len() < N::id_bound(),
            !N::is_bit_stealing() ==> old(self).nodes_view().len() + 1 < N::id_bound(),
            // No length-cache precondition. The count is `N::Index`-wide (the node
            // arena's own index type), so `len + 1` being representable follows from
            // `wf` — see the proof block below — rather than from anything the caller
            // has to know or could state wrongly.
        ensures
            final(self).wf(),
            final(self).model_view().len() == old(self).model_view().len(),
            final(self).list_seq(l as int) == seq![payload] + old(self).list_seq(l as int),
            forall|m: int| 0 <= m < final(self).model_view().len() && m != l as int
                ==> #[trigger] final(self).list_seq(m) == old(self).list_seq(m),
    {
        // Bound the old list length BEFORE mutating: a list is no longer than the arena
        // (`lemma_len_bounded`, from disjointness + in-range by pigeonhole). Combined with
        // the arena bound taken *after* the push below, that is what replaces the deleted
        // length precondition. Old `cache_len` ties `h.len` to this model length.
        proof { self.lemma_len_bounded(l as int); }
        let ghost old_nodes = self.nodes_view();
        let ghost old_model = self.model@;
        let h0 = self.heads.get_index(self.head_ix(l));
        let old_head = h0.head();
        let was_empty = old_head.is_null_exec();

        let slot = self.nodes_len();
        let mut new_node: ListNode<T, N> = ListNode::default();
        new_node.payload = payload;
        new_node.set_next(old_head);
        proof { Self::lemma_node_push_fits(self.nodes_view().len()); }
        self.nodes.push(new_node);

        // model[l] := [slot] ++ model[l]
        self.model = Ghost(self.model@.update(l as int, seq![slot] + self.model@[l as int]));

        // Single head read (production parity): h0 is still current — the
        // heads vec is untouched since it was read.
        let mut h = h0;
        h.set_head(NodeRef::to(slot));
        if was_empty {
            h.set_tail(slot);
        }
        // `h.len + 1` is representable, with no help from the caller. `h.len` is the OLD
        // model length (old `cache_len`), which `lemma_len_bounded` above bounded by the
        // OLD arena size; the node just pushed makes the arena one longer, and the store's
        // own `wf` bounds *that* by `N::Index`'s range. So
        //   h.len + 1 <= old_nodes.len() + 1 == nodes.len() < N::Index::max_nat().
        // The two ends only meet because the count and the node index are the same width.
        proof {
            assert(h.len_spec() == old_model[l as int].len());
            self.lemma_nodes_len_fits();
            assert(self.nodes_view().len() == old_nodes.len() + 1);
        }
        h.len = Self::len_incr(h.len);
        let li = self.head_ix(l);
        self.heads.set_index(li, h);

        proof {
            let model = self.model@;
            let nodes = self.nodes_view();
            let heads = self.heads_view();
            assert(nodes.len() == old_nodes.len() + 1);
            assert(slot == old_nodes.len());
            // node prefix [0, slot) unchanged by the push.
            assert(forall|k: int| 0 <= k < old_nodes.len() ==> nodes[k] == old_nodes[k]);
            // model[l] = [slot] ++ old_model[l]; other lists unchanged.
            assert(model[l as int] =~= seq![slot] + old_model[l as int]);
            assert(forall|m: int| 0 <= m < model.len() && m != l as int ==> model[m] == old_model[m]);
            // old in_range gives: every OLD index < old_nodes.len() == slot.
            assert(forall|l2: int, p: int|
                0 <= l2 < old_model.len() && 0 <= p < old_model[l2].len()
                    ==> old_model[l2][p] < slot);

            // --- in_range
            assert forall|l2: int, p: int|
                0 <= l2 < model.len() && 0 <= p < model[l2].len() implies
                #[trigger] model[l2][p] < nodes.len() by {
                if l2 == l as int && p == 0 {
                } else if l2 == l as int {
                    assert(model[l2][p] == old_model[l as int][p - 1]);
                } else {
                    assert(model[l2][p] == old_model[l2][p]);
                }
            }

            // --- disjoint: every entry except (l,0) maps to a distinct old entry
            // (< slot); (l,0) holds the fresh slot, present nowhere old.
            // Delegated: this quantifier e-matches combinatorially if left here.
            lemma_insert_fresh_disjoint(old_model, model, l as int, 0, slot);

            // --- cache_ok nexts
            assert(heads[l as int].head_ref().target() == slot);
            // set_next canonicalizes nulls, so equality holds only up to the
            // is_null/target observation — which is all cache_ok reads.
            assert(nodes[slot as int].next_ref().is_null() == old_head.is_null());
            assert(!old_head.is_null()
                ==> nodes[slot as int].next_ref().target() == old_head.target());
            assert forall|l2: int, p: int|
                0 <= l2 < model.len() && 0 <= p < model[l2].len() implies {
                    let nx = nodes[#[trigger] model[l2][p] as int].next_ref();
                    if p == model[l2].len() - 1 { nx.is_null() }
                    else { !nx.is_null() && nx.target() == model[l2][p + 1] }
                } by {
                if l2 == l as int && p == 0 {
                    // node[slot].next_ref() == old_head == old model[l][0] (or null if empty).
                    if old_model[l as int].len() == 0 {
                        assert(old_head.is_null());
                    } else {
                        assert(!old_head.is_null());
                        assert(old_head.target() == old_model[l as int][0]);  // old cache_ok head
                        assert(model[l as int][1] == old_model[l as int][0]);
                    }
                } else if l2 == l as int {
                    // shifted old node; its next is old's, model shifted by 1.
                    assert(model[l2][p] == old_model[l as int][p - 1]);
                    assert(nodes[model[l2][p] as int] == old_nodes[model[l2][p] as int]);
                } else {
                    assert(model[l2][p] == old_model[l2][p]);
                    assert(nodes[model[l2][p] as int] == old_nodes[model[l2][p] as int]);
                }
            }

            // --- cache_ok heads/tails
            assert forall|l2: int| 0 <= l2 < model.len() implies {
                let hh = (#[trigger] heads[l2]).head_ref();
                if model[l2].len() == 0 { hh.is_null() }
                else { !hh.is_null() && hh.target() == model[l2][0] }
            } by {
                if l2 != l as int { assert(heads[l2] == old(self).heads_view()[l2]); }
            }
            assert forall|l2: int| #![auto] 0 <= l2 < model.len() && model[l2].len() > 0 implies
                heads[l2].tail_spec() == model[l2][model[l2].len() - 1] by {
                if l2 != l as int { assert(heads[l2] == old(self).heads_view()[l2]); }
                else if !was_empty {
                    assert(model[l as int][model[l as int].len() - 1]
                        == old_model[l as int][old_model[l as int].len() - 1]);
                }
            }

            // --- list_seq(l): payload prepended.
            assert(self.list_seq(l as int) =~= seq![payload] + old(self).list_seq(l as int)) by {
                let post_seq = self.list_seq(l as int);
                let pre_seq = old(self).list_seq(l as int);
                assert(post_seq.len() == pre_seq.len() + 1);
                assert(post_seq[0] == payload);
                assert forall|p: int| 1 <= p < post_seq.len() implies
                    post_seq[p] == pre_seq[p - 1] by {
                    assert(model[l as int][p] == old_model[l as int][p - 1]);
                    assert(nodes[model[l as int][p] as int]
                        == old_nodes[old_model[l as int][p - 1] as int]);
                }
            }
            // --- list_seq(others): unchanged.
            assert forall|m: int| 0 <= m < model.len() && m != l as int implies
                #[trigger] self.list_seq(m) == old(self).list_seq(m) by {
                assert(model[m] == old_model[m]);
                assert(self.list_seq(m) =~= old(self).list_seq(m)) by {
                    assert forall|p: int| #![auto] 0 <= p < model[m].len() implies
                        nodes[model[m][p] as int].payload == old_nodes[old_model[m][p] as int].payload by {
                        assert(model[m][p] == old_model[m][p]);
                        assert(model[m][p] < slot);  // old index, unchanged node
                    }
                }
            }

            // --- cache_len: heads[l].len grew by 1 with model[l]; others unchanged.
            assert forall|l2: int| 0 <= l2 < model.len() implies
                (#[trigger] heads[l2]).len_spec() == (#[trigger] model[l2]).len() by {
                if l2 == l as int {
                    assert(model[l as int].len() == old_model[l as int].len() + 1);
                } else {
                    assert(heads[l2] == old(self).heads_view()[l2]);
                    assert(model[l2] == old_model[l2]);
                }
            }
        }
    }

    /// Append `payload` to the back of list `l` in O(1) via the cached tail.
    /// Pushes a fresh node (null next), then — if the list was non-empty —
    /// relinks the OLD TAIL node's `next` *forward* to the new (larger-index)
    /// node. This forward link is exactly what the old index-ordering crutch
    /// could not represent; the ghost model makes it routine.
    /// Measured ~11.7M rlimit (2.4s) once the disjointness quantifier is
    /// delegated to `lemma_insert_fresh_disjoint`, i.e. ~1.17x the default
    /// budget of 10, so this still does not pass bare. 30 was ~2.5x measured
    /// need until the phase-3 shell additions moved the module's proof seed
    /// and it tripped at 30; 60 restores the same ~2.5x margin over the new
    /// measurement. The real fix is the splice_raw-style dimension split this
    /// fn is queued for (plan doc, remaining tail).
    #[verifier::rlimit(60)]
    pub(crate) fn append_raw(&mut self, l: usize, payload: T)
        requires
            old(self).wf(),
            (l as int) < old(self).model_view().len(),
            old(self).nodes_view().len() + 1 < usize::MAX,
            // Packing headroom, per id family; see `prepend_raw`.
            old(self).nodes_view().len() < N::id_bound(),
            !N::is_bit_stealing() ==> old(self).nodes_view().len() + 1 < N::id_bound(),
            // No length-cache precondition; see `prepend_raw`. The count shares the node
            // index's width, so `wf` already bounds it.
        ensures
            final(self).wf(),
            final(self).model_view().len() == old(self).model_view().len(),
            final(self).list_seq(l as int) == old(self).list_seq(l as int).push(payload),
            forall|m: int| 0 <= m < final(self).model_view().len() && m != l as int
                ==> #[trigger] final(self).list_seq(m) == old(self).list_seq(m),
            // raw effects, for aggregate invariants stated over the model
            // (egraph-wf W5): the model gains exactly the fresh node at the
            // list's end, and no stored payload changes.
            final(self).model_view() == old(self).model_view().update(l as int,
                old(self).model_view()[l as int].push(old(self).nodes_view().len() as usize)),
            final(self).nodes_view().len() == old(self).nodes_view().len() + 1,
            forall|k: int| 0 <= k < old(self).nodes_view().len()
                ==> (#[trigger] final(self).nodes_view()[k]).payload
                    == old(self).nodes_view()[k].payload,
            final(self).heads_snapshots_view() == old(self).heads_snapshots_view(),
            final(self).nodes_snapshots_view() == old(self).nodes_snapshots_view(),
            final(self).model_snapshots_view() == old(self).model_snapshots_view(),
            final(self).nodes_view()[old(self).nodes_view().len() as int].payload == payload,
    {
        // Bound the old list length before mutating; paired with the arena bound taken
        // after the push, this is what makes `len + 1` representable (see `prepend_raw`).
        proof { self.lemma_len_bounded(l as int); }
        let ghost old_nodes = self.nodes_view();
        let ghost old_model = self.model@;
        let h0 = self.heads.get_index(self.head_ix(l));
        let was_empty = h0.head().is_null_exec();

        let slot = self.nodes_len();
        let mut new_node: ListNode<T, N> = ListNode::default();
        new_node.payload = payload;
        new_node.set_next(NodeRef::null());
        proof { Self::lemma_node_push_fits(self.nodes_view().len()); }
        self.nodes.push(new_node);

        if !was_empty {
            // relink old tail node forward to slot.
            let old_tail = h0.tail();
            let mut tnode = self.nodes.get_index(self.node_ix(old_tail));
            tnode.set_next(NodeRef::to(slot));
            let ti = self.node_ix(old_tail);
            self.nodes.set_index(ti, tnode);
        }

        // model[l] := model[l] ++ [slot]
        self.model = Ghost(self.model@.update(l as int, self.model@[l as int].push(slot)));

        // Single head read (production parity): h0 is still current.
        let mut h = h0;
        if was_empty {
            h.set_head(NodeRef::to(slot));
        }
        h.set_tail(slot);
        // Same chain as `prepend_raw`: old count <= old arena, arena grew by the pushed
        // node, and the store's `wf` bounds the grown arena by `N::Index`'s range.
        proof {
            assert(h.len_spec() == old_model[l as int].len());
            self.lemma_nodes_len_fits();
            assert(self.nodes_view().len() == old_nodes.len() + 1);
        }
        h.len = Self::len_incr(h.len);
        let li = self.head_ix(l);
        self.heads.set_index(li, h);

        proof {
            let model = self.model@;
            let nodes = self.nodes_view();
            let heads = self.heads_view();
            let ghost old_tail = old_model[l as int].len() > 0;
            assert(slot == old_nodes.len());
            assert(model[l as int] =~= old_model[l as int].push(slot));
            assert(forall|m: int| 0 <= m < model.len() && m != l as int ==> model[m] == old_model[m]);
            assert(forall|l2: int, p: int|
                0 <= l2 < old_model.len() && 0 <= p < old_model[l2].len()
                    ==> old_model[l2][p] < slot);

            // --- in_range
            assert forall|l2: int, p: int|
                0 <= l2 < model.len() && 0 <= p < model[l2].len() implies
                #[trigger] model[l2][p] < nodes.len() by {
                if l2 == l as int && p == model[l as int].len() - 1 {
                } else if l2 == l as int {
                    assert(model[l2][p] == old_model[l as int][p]);
                } else {
                    assert(model[l2][p] == old_model[l2][p]);
                }
            }

            // --- disjoint: fresh slot only at (l, last); others map to old.
            // Delegated: this quantifier e-matches combinatorially if left here.
            lemma_insert_fresh_disjoint(
                old_model, model, l as int, model[l as int].len() - 1, slot);

            // --- cache_ok nexts. The only mutated node-next is the old tail
            // (now -> slot) and the new node slot (null). All others unchanged.
            assert forall|l2: int, p: int|
                0 <= l2 < model.len() && 0 <= p < model[l2].len() implies {
                    let nx = nodes[#[trigger] model[l2][p] as int].next_ref();
                    if p == model[l2].len() - 1 { nx.is_null() }
                    else { !nx.is_null() && nx.target() == model[l2][p + 1] }
                } by {
                if l2 == l as int {
                    let last = model[l as int].len() - 1;
                    if p == last {
                        // node slot: pushed with null next; not the relinked tail.
                        assert(model[l as int][p] == slot);
                        assert(nodes[slot as int].next_ref().is_null());
                    } else if p == last - 1 {
                        // old tail position: relinked to slot == model[l][last].
                        assert(model[l as int][p] == old_model[l as int][p]);
                        assert(model[l as int][p] == h0.tail_spec());  // old cache: tail == old last
                        assert(nodes[model[l as int][p] as int].next_ref().target() == slot);
                        assert(model[l as int][p + 1] == slot);
                    } else {
                        // interior old node, untouched.
                        assert(model[l as int][p] == old_model[l as int][p]);
                        assert(model[l as int][p] != h0.tail_spec());
                        assert(nodes[model[l as int][p] as int] == old_nodes[old_model[l as int][p] as int]);
                        assert(model[l as int][p + 1] == old_model[l as int][p + 1]);
                    }
                } else {
                    // other list: its nodes are disjoint from l's tail and slot.
                    assert(model[l2][p] == old_model[l2][p]);
                    assert(model[l2][p] != slot);
                    assert(was_empty || model[l2][p] != h0.tail_spec());  // disjoint from l's tail
                    assert(nodes[model[l2][p] as int] == old_nodes[old_model[l2][p] as int]);
                }
            }

            // --- cache_ok heads/tails
            assert forall|l2: int| 0 <= l2 < model.len() implies {
                let hh = (#[trigger] heads[l2]).head_ref();
                if model[l2].len() == 0 { hh.is_null() }
                else { !hh.is_null() && hh.target() == model[l2][0] }
            } by {
                if l2 != l as int { assert(heads[l2] == old(self).heads_view()[l2]); }
                else if was_empty {
                    assert(model[l as int][0] == slot);
                } else {
                    assert(model[l as int][0] == old_model[l as int][0]);
                }
            }
            assert forall|l2: int| #![auto] 0 <= l2 < model.len() && model[l2].len() > 0 implies
                heads[l2].tail_spec() == model[l2][model[l2].len() - 1] by {
                if l2 != l as int { assert(heads[l2] == old(self).heads_view()[l2]); }
            }

            // --- list_seq(l): payload appended.
            assert(self.list_seq(l as int) =~= old(self).list_seq(l as int).push(payload)) by {
                let post_seq = self.list_seq(l as int);
                let pre_seq = old(self).list_seq(l as int);
                assert(post_seq.len() == pre_seq.len() + 1);
                assert forall|p: int| 0 <= p < pre_seq.len() implies post_seq[p] == pre_seq[p] by {
                    assert(model[l as int][p] == old_model[l as int][p]);
                    assert(model[l as int][p] < slot);
                    // node may be the relinked tail, but only its `next` changed,
                    // not its payload.
                    assert(nodes[model[l as int][p] as int].payload
                        == old_nodes[old_model[l as int][p] as int].payload);
                }
                assert(post_seq[pre_seq.len() as int] == payload);
            }
            // --- list_seq(others): unchanged (their nodes' payloads untouched).
            assert forall|m: int| 0 <= m < model.len() && m != l as int implies
                #[trigger] self.list_seq(m) == old(self).list_seq(m) by {
                assert(model[m] == old_model[m]);
                assert(self.list_seq(m) =~= old(self).list_seq(m)) by {
                    assert forall|p: int| #![auto] 0 <= p < model[m].len() implies
                        nodes[model[m][p] as int].payload == old_nodes[old_model[m][p] as int].payload by {
                        assert(model[m][p] == old_model[m][p]);
                        assert(model[m][p] < slot);
                        assert(was_empty || model[m][p] != h0.tail_spec());
                    }
                }
            }

            // --- cache_len: heads[l].len grew by 1 with model[l]; others unchanged.
            assert forall|l2: int| 0 <= l2 < model.len() implies
                (#[trigger] heads[l2]).len_spec() == (#[trigger] model[l2]).len() by {
                if l2 == l as int {
                    assert(model[l as int].len() == old_model[l as int].len() + 1);
                } else {
                    assert(heads[l2] == old(self).heads_view()[l2]);
                    assert(model[l2] == old_model[l2]);
                }
            }
        }
    }

    /// Number of elements in list `l`, O(1) from the cached header count. Verified
    /// (via `wf`'s `cache_len`) to equal the abstract list length.
    ///
    /// Returns `N::Index`, not `usize`, even though the raw core takes a `usize` row:
    /// the argument is a row and the result is a count, and the count's type is the node
    /// arena's index type — the same reasoning that widened the stored field, and the same
    /// convention the inner vec follows (`DiffStore::len(&self) -> I`, matching
    /// production's `Vec::len` and `ListArena::len`). Callers wanting a plain count use
    /// `IndexLike::as_usize`.
    pub(crate) fn len_raw(&self, l: usize) -> (n: N::Index)
        requires self.wf(), (l as int) < self.model_view().len(),
        ensures n.as_nat() == self.list_seq(l as int).len(),
    {
        proof {
            // header len == model len (cache_len); list_seq len == model len (by def).
            assert(self.heads_view()[l as int].len_spec() == self.model@[l as int].len());
            assert(self.list_seq(l as int).len() == self.model@[l as int].len());
        }
        self.heads.get_index(self.head_ix(l)).len
    }

    /// Is list `l` empty?
    pub(crate) fn is_empty_raw(&self, l: usize) -> (b: bool)
        requires self.wf(), (l as int) < self.model_view().len(),
        ensures b == (self.list_seq(l as int) == Seq::<T>::empty()),
    {
        let h = self.heads.get_index(self.head_ix(l));
        proof {
            // head null iff model[l] empty (cache_ok); list_seq empty iff model empty.
            assert(h.head_ref() == self.heads_view()[l as int].head_ref());
            if self.model@[l as int].len() == 0 {
                assert(self.list_seq(l as int) =~= Seq::<T>::empty());
            } else {
                assert(self.list_seq(l as int).len() == self.model@[l as int].len());
            }
        }
        h.head().is_null_exec()
    }

    /// Splice `src` onto the back of `dst`: `dst` becomes `dst ++ src`, and
    /// `src` is cleared to empty. O(1): link `dst`'s tail node forward to
    /// `src`'s head (a single `next` mutation across arbitrary indices — the
    /// general case the old invariant could not model), then concatenate the
    /// models. Disjointness (the two lists share no node) is what makes the
    /// concatenation a valid list and lets `src` clear without dangling.
    /// `spinoff_prover` is load-bearing, not padding: without it this fails even
    /// at `rlimit(100)` (10x its measured need), because the disjointness
    /// quantifier below shares a solver context with the rest of the module.
    /// Measured ~75.9M rlimit (17.6s) once the quad-nested disjointness goal is
    /// delegated to `lemma_splice_disjoint`; 150 was ~2x that. It was 800, sized
    /// for the 1.56-BILLION-rlimit (223s) version where that goal was proved
    /// inline here -- see the lemma's header for why that was so expensive.
    ///
    /// Re-measured when the cached count became `N::Index`-wide: the floor moved above
    /// 150 (bisected — 150 fails, 175 passes), so 300 keeps the same ~2x margin. The
    /// growth is the length arithmetic, not the concatenation: the merged count is now a
    /// checked `len_add` whose in-range obligation is *derived* here from
    /// `lemma_concat_len_bounded` + `lemma_nodes_len_fits` instead of being asserted by
    /// the caller as a `< 0x1_0000_0000` precondition. That trade is the point — a
    /// precondition an unverified caller could get wrong became a proof obligation
    /// discharged from `wf`, and it costs solver time here rather than soundness there.
    #[verifier::spinoff_prover]
    #[verifier::rlimit(300)]
    pub(crate) fn splice_raw(&mut self, dst: usize, src: usize)
        requires
            old(self).wf(),
            (dst as int) < old(self).model_view().len(),
            (src as int) < old(self).model_view().len(),
            dst != src,
            // No length-cache precondition for the merged list. The two lists are
            // disjoint, so their combined length is bounded by the arena
            // (`lemma_concat_len_bounded`) and the arena by `N::Index`'s range
            // (`lemma_nodes_len_fits`) — the sum is in range as a consequence of `wf`.
        ensures
            final(self).wf(),
            final(self).model_view().len() == old(self).model_view().len(),
            final(self).list_seq(dst as int)
                == old(self).list_seq(dst as int) + old(self).list_seq(src as int),
            final(self).list_seq(src as int) == Seq::<T>::empty(),
            forall|m: int| 0 <= m < final(self).model_view().len()
                && m != dst as int && m != src as int
                ==> #[trigger] final(self).list_seq(m) == old(self).list_seq(m),
            // raw effects (egraph-wf W5): concatenated model, no payload moves.
            final(self).model_view() == old(self).model_view()
                .update(dst as int,
                    old(self).model_view()[dst as int] + old(self).model_view()[src as int])
                .update(src as int, Seq::<usize>::empty()),
            final(self).nodes_view().len() == old(self).nodes_view().len(),
            forall|k: int| 0 <= k < old(self).nodes_view().len()
                ==> (#[trigger] final(self).nodes_view()[k]).payload
                    == old(self).nodes_view()[k].payload,
            final(self).heads_snapshots_view() == old(self).heads_snapshots_view(),
            final(self).nodes_snapshots_view() == old(self).nodes_snapshots_view(),
            final(self).model_snapshots_view() == old(self).model_snapshots_view(),
    {
        // Bound dst.len + src.len before mutating: the two lists are disjoint, so their
        // combined length fits the arena, and the arena fits `N::Index`. No node is
        // pushed here, so unlike prepend/append both facts are about the *current* arena
        // and can be taken together. Old cache_len ties each header len to its model.
        proof {
            self.lemma_concat_len_bounded(dst as int, src as int);
            self.lemma_nodes_len_fits();
        }
        let ghost old_nodes = self.nodes_view();
        let ghost old_model = self.model@;
        let hd = self.heads.get_index(self.head_ix(dst));
        let hs = self.heads.get_index(self.head_ix(src));
        let dst_empty = hd.head().is_null_exec();
        let src_empty = hs.head().is_null_exec();
        // hd.len == |old dst|, hs.len == |old src| (old cache_len); sum <= nodes.len()
        // < N::Index::max_nat() from the two lemmas above.
        proof {
            assert(hd.len_spec() == old_model[dst as int].len());
            assert(hs.len_spec() == old_model[src as int].len());
        }
        let new_dst_len = Self::len_add(hd.len, hs.len);

        if !src_empty {
            if dst_empty {
                // dst takes over src's head/tail.
                let mut h = self.heads.get_index(self.head_ix(dst));
                h.set_head(hs.head());
                h.set_tail(hs.tail());
                h.len = new_dst_len;
                let di = self.head_ix(dst);
                self.heads.set_index(di, h);
            } else {
                // link dst's tail node forward to src's head.
                let dtail = hd.tail();
                let mut tnode = self.nodes.get_index(self.node_ix(dtail));
                tnode.set_next(hs.head());
                let ti = self.node_ix(dtail);
                self.nodes.set_index(ti, tnode);
                let mut h = self.heads.get_index(self.head_ix(dst));
                h.set_tail(hs.tail());
                h.len = new_dst_len;
                let di = self.head_ix(dst);
                self.heads.set_index(di, h);
            }
        }
        // clear src (len resets to 0 via default).
        let si = self.head_ix(src);
        self.heads.set_index(si, ListHead::default());

        // model: dst := dst ++ src; src := [].
        self.model = Ghost(
            self.model@
                .update(dst as int, old_model[dst as int] + old_model[src as int])
                .update(src as int, Seq::empty()));

        proof {
            let model = self.model@;
            let nodes = self.nodes_view();
            let heads = self.heads_view();
            assert(nodes.len() == old_nodes.len());
            // nodes_repr_wf carries: length unchanged; the only touched node
            // (dst's old tail, when relinked) went through set_next, whose
            // ensures includes next_wf; every other node is old and wf.
            assert forall|i: int| 0 <= i < nodes.len()
                implies (#[trigger] nodes[i]).next_wf() by {
                if nodes[i] != old_nodes[i] {
                    // only the set_index'd node differs, and set_next
                    // established its next_wf before the write.
                }
            }
            assert(model[dst as int] =~= old_model[dst as int] + old_model[src as int]);
            assert(model[src as int] =~= Seq::<usize>::empty());
            assert(forall|m: int| 0 <= m < model.len() && m != dst as int && m != src as int
                ==> model[m] == old_model[m]);

            // helper: position p of model[dst] sources to old dst (p < |dst|) or
            // old src (p - |dst|).
            let dlen = old_model[dst as int].len();

            // --- in_range: all indices are old indices (no node pushed).
            assert forall|l2: int, p: int|
                0 <= l2 < model.len() && 0 <= p < model[l2].len() implies
                #[trigger] model[l2][p] < nodes.len() by {
                if l2 == dst as int {
                    if p < dlen { assert(model[l2][p] == old_model[dst as int][p]); }
                    else { assert(model[l2][p] == old_model[src as int][p - dlen]); }
                } else {
                    assert(model[l2][p] == old_model[l2][p]);
                }
            }

            // --- disjoint: dst++src concatenates two OLD-disjoint lists; every
            // entry still maps to a distinct old (list,pos), and src is now empty.
            // Delegated: proved here, with both states' `wf()` in scope, this
            // one quantifier e-matched its way to 17.6M instantiations.
            lemma_splice_disjoint(old_model, model, dst as int, src as int);

            // --- cache_ok nexts: only dst's old tail node was relinked
            // (its next -> src's head); every other node-next is unchanged.
            assert forall|l2: int, p: int|
                0 <= l2 < model.len() && 0 <= p < model[l2].len() implies {
                    let nx = nodes[#[trigger] model[l2][p] as int].next_ref();
                    if p == model[l2].len() - 1 { nx.is_null() }
                    else { !nx.is_null() && nx.target() == model[l2][p + 1] }
                } by {
                splice_cache_node(*old(self), self, dst as int, src as int,
                    hd.tail_spec(), hs.head_ref(), dst_empty, src_empty, l2, p);
            }

            // --- cache_ok heads/tails
            assert forall|l2: int| 0 <= l2 < model.len() implies {
                let hh = (#[trigger] heads[l2]).head_ref();
                if model[l2].len() == 0 { hh.is_null() }
                else { !hh.is_null() && hh.target() == model[l2][0] }
            } by {
                if l2 == src as int {
                } else if l2 == dst as int {
                    if old_model[dst as int].len() > 0 {
                        assert(model[dst as int][0] == old_model[dst as int][0]);
                    } else if old_model[src as int].len() > 0 {
                        assert(model[dst as int][0] == old_model[src as int][0]);
                    }
                } else {
                    assert(heads[l2] == old(self).heads_view()[l2]);
                }
            }
            assert forall|l2: int| #![auto] 0 <= l2 < model.len() && model[l2].len() > 0 implies
                heads[l2].tail_spec() == model[l2][model[l2].len() - 1] by {
                if l2 == dst as int {
                    if old_model[src as int].len() > 0 {
                        assert(model[dst as int][model[dst as int].len() - 1]
                            == old_model[src as int][old_model[src as int].len() - 1]);
                    } else {
                        assert(model[dst as int][model[dst as int].len() - 1]
                            == old_model[dst as int][old_model[dst as int].len() - 1]);
                    }
                } else if l2 != src as int {
                    assert(heads[l2] == old(self).heads_view()[l2]);
                }
            }

            // --- list_seq
            assert(self.list_seq(src as int) =~= Seq::<T>::empty());
            assert(self.list_seq(dst as int)
                =~= old(self).list_seq(dst as int) + old(self).list_seq(src as int)) by {
                let post = self.list_seq(dst as int);
                let pre_d = old(self).list_seq(dst as int);
                let pre_s = old(self).list_seq(src as int);
                assert(post.len() == pre_d.len() + pre_s.len());
                assert forall|p: int| #![auto] 0 <= p < post.len() implies
                    post[p] == (if p < pre_d.len() { pre_d[p] } else { pre_s[p - pre_d.len()] }) by {
                    if p < dlen {
                        assert(model[dst as int][p] == old_model[dst as int][p]);
                    } else {
                        assert(model[dst as int][p] == old_model[src as int][p - dlen]);
                    }
                }
            }
            assert forall|m: int| 0 <= m < model.len() && m != dst as int && m != src as int implies
                #[trigger] self.list_seq(m) == old(self).list_seq(m) by {
                assert(model[m] == old_model[m]);
                assert(self.list_seq(m) =~= old(self).list_seq(m)) by {
                    assert forall|p: int| #![auto] 0 <= p < model[m].len() implies
                        nodes[model[m][p] as int].payload == old_nodes[old_model[m][p] as int].payload by {
                        assert(model[m][p] == old_model[m][p]);
                        // m's nodes are disjoint from dst's relinked tail.
                        assert(dst_empty || model[m][p] != hd.tail_spec());
                    }
                }
            }

            // --- cache_len: dst.len := |old dst| + |old src| == |new dst model|;
            // src.len := 0 == |empty|; all other headers and model lengths unchanged.
            assert forall|l2: int| 0 <= l2 < model.len() implies
                (#[trigger] heads[l2]).len_spec() == (#[trigger] model[l2]).len() by {
                if l2 == dst as int {
                    assert(model[dst as int].len()
                        == old_model[dst as int].len() + old_model[src as int].len());
                    // heads[dst].len was set to hd.len + hs.len (both non-empty), or
                    // left unchanged when src_empty (then hs.len == 0 and dst model
                    // is unchanged) — either way equals the new model length.
                } else if l2 == src as int {
                    assert(model[src as int].len() == 0);
                    assert(heads[src as int].len_spec() == 0);  // ListHead::default()
                } else {
                    assert(heads[l2] == old(self).heads_view()[l2]);
                    assert(model[l2] == old_model[l2]);
                }
            }
        }
    }

    // ---- semi-persistence: delegate to the two inner vectors ----

    pub(crate) fn mark(&mut self, shrink: ShrinkPolicy) -> (token: ListArenaToken)
        requires
            old(self).wf(),
            TRACK,
            old(self).heads_view().len() < usize::MAX,
            old(self).nodes_view().len() < usize::MAX,
            old(self).heads_depth_spec() < u32::MAX,
            old(self).nodes_depth_spec() < u32::MAX,
        ensures
            final(self).wf(),
            final(self).heads_view() == old(self).heads_view(),
            final(self).nodes_view() == old(self).nodes_view(),
            final(self).model_view() == old(self).model_view(),
            token.heads_frame_idx_spec() == old(self).heads_depth_spec(),
            token.nodes_frame_idx_spec() == old(self).nodes_depth_spec(),
            final(self).heads_snapshots_view()
                == old(self).heads_snapshots_view().push(old(self).heads_view()),
            final(self).nodes_snapshots_view()
                == old(self).nodes_snapshots_view().push(old(self).nodes_view()),
            final(self).model_snapshots_view()
                == old(self).model_snapshots_view().push(old(self).model_view()),
            token.heads_frame_idx_spec() == final(self).heads_snapshots_view().len() - 1,
            token.nodes_frame_idx_spec() == final(self).nodes_snapshots_view().len() - 1,
    {
        let heads = self.heads.mark(shrink);
        let nodes = self.nodes.mark(shrink);
        // Archive the live model alongside the vec snapshots (Phase 7): the
        // new frame's arena_model_wf obligation is exactly the live wf
        // clauses over the just-pushed snapshot (== the live views).
        self.model_snapshots = Ghost(self.model_snapshots@.push(self.model@));
        proof {
            reveal(arena_archive_agrees);
            // Old-frame agreement (reveal the old(self) instance).
            assert(arena_archive_agrees(old(self).model_snapshots@,
                old(self).heads.snapshots_view(), old(self).nodes.snapshots_view()));
            let k_new = self.model_snapshots@.len() - 1;
            // The pushed frame archives the live views; the live wf clauses
            // ARE arena_model_wf over them.
            assert(self.heads.snapshots_view()[k_new] == old(self).heads_view());
            assert(self.nodes.snapshots_view()[k_new] == old(self).nodes_view());
            assert(arena_model_wf(self.model@,
                self.heads.snapshots_view()[k_new], self.nodes.snapshots_view()[k_new]));
            assert forall|k: int| 0 <= k < self.model_snapshots@.len()
                implies arena_model_wf(
                    #[trigger] self.model_snapshots@[k],
                    self.heads.snapshots_view()[k], self.nodes.snapshots_view()[k]) by {
                if k < k_new {
                    assert(self.model_snapshots@[k] == old(self).model_snapshots@[k]);
                    assert(self.heads.snapshots_view()[k]
                        == old(self).heads.snapshots_view()[k]);
                    assert(self.nodes.snapshots_view()[k]
                        == old(self).nodes.snapshots_view()[k]);
                }
            }
            assert(arena_archive_agrees(self.model_snapshots@,
                self.heads.snapshots_view(), self.nodes.snapshots_view()));
        }
        ListArenaToken { heads, nodes }
    }

    // ------------------------------------------------------------------
    // Total shell (total-API plan phase 3).
    // ------------------------------------------------------------------

    /// Total list allocation: refuses at `L`'s id range.
    pub fn try_new_list(&mut self) -> (r: Result<L, crate::error::ContainerError>)
        requires old(self).wf(),
        ensures
            final(self).wf(),
            r matches Ok(l) ==> l.id_nat() == old(self).heads_view().len()
                && final(self).nodes_view() == old(self).nodes_view()
                && final(self).model_view() == old(self).model_view().push(Seq::empty()),
            r is Err ==> final(self).model_view() == old(self).model_view(),
            r matches Err(e) ==> e == crate::error::ContainerError::CapacityExhausted,
            final(self).heads_snapshots_view() == old(self).heads_snapshots_view(),
            final(self).nodes_snapshots_view() == old(self).nodes_snapshots_view(),
            final(self).model_snapshots_view() == old(self).model_snapshots_view(),
    {
        let n = self.heads.store.data.len();
        if n < usize::MAX - 1
            && L::try_new(n).is_some()
            && (L::bit_stealing() || L::try_new(n + 1).is_some())
        {
            Ok(self.new_list())
        } else {
            Err(crate::error::ContainerError::CapacityExhausted)
        }
    }

    /// Total append: refuses a bad list handle as `IndexOutOfBounds` and node
    /// exhaustion as `CapacityExhausted`, where the guarded core panics.
    pub fn try_append(&mut self, l: L, payload: T)
        -> (r: Result<(), crate::error::ContainerError>)
        requires old(self).wf(),
        ensures
            final(self).wf(),
            r is Ok ==> final(self).list_seq(l.id_nat() as int)
                == old(self).list_seq(l.id_nat() as int).push(payload),
            r is Ok ==> {
                &&& final(self).model_view() == old(self).model_view().update(
                        l.id_nat() as int, old(self).model_view()[l.id_nat() as int].push(
                            old(self).nodes_view().len() as usize))
                &&& final(self).nodes_view().len() == old(self).nodes_view().len() + 1
                &&& (forall|k: int| 0 <= k < old(self).nodes_view().len()
                        ==> (#[trigger] final(self).nodes_view()[k]).payload
                            == old(self).nodes_view()[k].payload)
                &&& final(self).nodes_view()[old(self).nodes_view().len() as int].payload
                    == payload
            },
            r is Err ==> final(self).model_view() == old(self).model_view()
                && final(self).nodes_view() == old(self).nodes_view(),
            final(self).heads_snapshots_view() == old(self).heads_snapshots_view(),
            final(self).nodes_snapshots_view() == old(self).nodes_snapshots_view(),
            final(self).model_snapshots_view() == old(self).model_snapshots_view(),
    {
        if !(l.to_usize() < self.heads.store.data.len()) {
            return Err(crate::error::ContainerError::IndexOutOfBounds);
        }
        let n = self.nodes.store.data.len();
        if n < usize::MAX - 1
            && N::try_new(n).is_some()
            && (N::bit_stealing() || N::try_new(n + 1).is_some())
        {
            self.append(l, payload);
            Ok(())
        } else {
            Err(crate::error::ContainerError::CapacityExhausted)
        }
    }

    /// Total prepend: refuses a bad list handle as `IndexOutOfBounds` and node
    /// exhaustion as `CapacityExhausted`, where the guarded core panics.
    pub fn try_prepend(&mut self, l: L, payload: T)
        -> (r: Result<(), crate::error::ContainerError>)
        requires old(self).wf(),
        ensures
            final(self).wf(),
            r is Ok ==> final(self).list_seq(l.id_nat() as int)
                == seq![payload] + old(self).list_seq(l.id_nat() as int),
            r is Err ==> final(self).model_view() == old(self).model_view(),
    {
        if !(l.to_usize() < self.heads.store.data.len()) {
            return Err(crate::error::ContainerError::IndexOutOfBounds);
        }
        let n = self.nodes.store.data.len();
        if n < usize::MAX - 1
            && N::try_new(n).is_some()
            && (N::bit_stealing() || N::try_new(n + 1).is_some())
        {
            self.prepend(l, payload);
            Ok(())
        } else {
            Err(crate::error::ContainerError::CapacityExhausted)
        }
    }

    /// Total mark.
    pub fn try_mark(&mut self, shrink: ShrinkPolicy)
        -> (r: Result<ListArenaToken, crate::error::ContainerError>)
        requires old(self).wf(),
        ensures
            final(self).wf(),
            r matches Ok(token) ==> {
                &&& final(self).model_view() == old(self).model_view()
                &&& final(self).heads_view() == old(self).heads_view()
                &&& final(self).nodes_view() == old(self).nodes_view()
                &&& token.heads_frame_idx_spec() == old(self).heads_depth_spec()
                &&& token.nodes_frame_idx_spec() == old(self).nodes_depth_spec()
                &&& final(self).heads_snapshots_view()
                    == old(self).heads_snapshots_view().push(old(self).heads_view())
                &&& final(self).nodes_snapshots_view()
                    == old(self).nodes_snapshots_view().push(old(self).nodes_view())
                &&& final(self).model_snapshots_view()
                    == old(self).model_snapshots_view().push(old(self).model_view())
                &&& token.heads_frame_idx_spec()
                    == final(self).heads_snapshots_view().len() - 1
                &&& token.nodes_frame_idx_spec()
                    == final(self).nodes_snapshots_view().len() - 1
            },
            r is Err ==> final(self).model_view() == old(self).model_view(),
    {
        if !TRACK {
            return Err(crate::error::ContainerError::Untracked);
        }
        let hn = self.heads.store.data.len();
        let nn = self.nodes.store.data.len();
        if !(hn < usize::MAX && nn < usize::MAX) {
            return Err(crate::error::ContainerError::CapacityExhausted);
        }
        if !(self.heads.frames.len() < u32::MAX as usize
            && self.nodes.frames.len() < u32::MAX as usize)
        {
            return Err(crate::error::ContainerError::DepthLimit);
        }
        Ok(self.mark(shrink))
    }

    /// Total restore: component restorability plus the same-mark frame
    /// agreement (a mixed token from two different marks refuses).
    pub fn try_restore(&mut self, token: ListArenaToken)
        -> (r: Result<(), crate::error::ContainerError>)
        requires old(self).wf(),
        ensures
            final(self).wf(),
            r is Err ==> final(self).model_view() == old(self).model_view(),
            r matches Err(e) ==> e == crate::error::ContainerError::InvalidToken,
    {
        if self.is_valid_token(&token)
            && token.heads.frame_idx == token.nodes.frame_idx
        {
            self.restore(token);
            Ok(())
        } else {
            Err(crate::error::ContainerError::InvalidToken)
        }
    }

    /// "Restorable now" for the composite token (plan 2.2/2.3).
    pub fn is_valid_token(&self, token: &ListArenaToken) -> (b: bool)
        requires self.wf(),
        ensures b == self.is_restorable_spec(*token),
    {
        self.heads.is_valid_token(&token.heads) && self.nodes.is_valid_token(&token.nodes)
    }

    /// Restore both arenas to the marked snapshot. The restored snapshots must
    /// jointly form a valid arena *for the current ghost model* — i.e. the
    /// model still describes them (`arena_model_wf`). Semi-persistence composes
    /// from the two inner `Vec`s.
    pub(crate) fn restore(&mut self, token: ListArenaToken)
        requires
            old(self).wf(),
            TRACK,
            old(self).restore_pre_spec(token),
            // The two component tokens name the SAME mark: one mark pushes
            // one frame on each vec (wf keeps the stacks in lockstep), so a
            // genuine ListArenaToken always satisfies this; a mixed
            // frankentoken does not.
            token.heads_frame_idx_spec() == token.nodes_frame_idx_spec(),
        ensures
            final(self).wf(),
            final(self).heads_view()
                == old(self).heads_snapshots_view()[token.heads_frame_idx_spec() as int],
            final(self).nodes_view()
                == old(self).nodes_snapshots_view()[token.nodes_frame_idx_spec() as int],
            // The restored model is the one archived at that mark (Phase 7:
            // recovered internally, no caller-supplied ghost).
            final(self).model_view() == old(self).model_snapshots_view()[token.heads_frame_idx_spec() as int],
            final(self).heads_snapshots_view() == old(self).heads_snapshots_view()
                .subrange(0, token.heads_frame_idx_spec() as int),
            final(self).nodes_snapshots_view() == old(self).nodes_snapshots_view()
                .subrange(0, token.nodes_frame_idx_spec() as int),
            final(self).model_snapshots_view() == old(self).model_snapshots_view()
                .subrange(0, token.heads_frame_idx_spec() as int),
    {
        // Atomic compound restore (plan 2.3): prevalidate BOTH constituent
        // tokens before restoring either — heads rolled back without nodes
        // breaks the model invariants unrecoverably. Also pin the same-mark
        // frame agreement at runtime (frankentoken defense; free for genuine
        // tokens).
        crate::guard::check_precondition(
            self.is_valid_token(&token),
            "ListArena::restore: invalid, foreign, stale, consumed, or abandoned token component",
        );
        crate::guard::check_precondition(
            token.heads.frame_idx == token.nodes.frame_idx,
            "ListArena::restore: token components name different marks",
        );
        let ghost snap_model = self.model_snapshots@[token.heads.frame_idx as int];
        self.heads.restore(token.heads);
        self.nodes.restore(token.nodes);
        self.model = Ghost(snap_model);
        // Truncate the archive in lockstep with the vec snapshot stacks
        // (restore leaves frames@.len() == frame_idx on both).
        self.model_snapshots =
            Ghost(self.model_snapshots@.subrange(0, token.heads.frame_idx as int));
        proof {
            reveal(arena_archive_agrees);
            let f = token.heads.frame_idx as int;
            // Old-frame agreement (reveal the old(self) instance).
            assert(arena_archive_agrees(old(self).model_snapshots@,
                old(self).heads.snapshots_view(), old(self).nodes.snapshots_view()));
            // The archived model at frame f describes the restored views:
            // this is BOTH the live-wf reconstruction (in-range/disjoint/
            // cache clauses over the restored heads/nodes) AND the model
            // ensures.
            assert(arena_model_wf(snap_model,
                old(self).heads.snapshots_view()[f], old(self).nodes.snapshots_view()[f]));
            assert(self.heads_view() == old(self).heads.snapshots_view()[f]);
            assert(self.nodes_view() == old(self).nodes.snapshots_view()[f]);
            // Truncated archive agrees frame-wise with the truncated stacks.
            assert(self.heads.snapshots_view()
                =~= old(self).heads.snapshots_view().subrange(0, f));
            assert(self.nodes.snapshots_view()
                =~= old(self).nodes.snapshots_view().subrange(0, f));
            assert forall|k: int| 0 <= k < self.model_snapshots@.len()
                implies arena_model_wf(
                    #[trigger] self.model_snapshots@[k],
                    self.heads.snapshots_view()[k], self.nodes.snapshots_view()[k]) by {
                assert(self.model_snapshots@[k] == old(self).model_snapshots@[k]);
                assert(self.heads.snapshots_view()[k] == old(self).heads.snapshots_view()[k]);
                assert(self.nodes.snapshots_view()[k] == old(self).nodes.snapshots_view()[k]);
            }
            assert(arena_archive_agrees(self.model_snapshots@,
                self.heads.snapshots_view(), self.nodes.snapshots_view()));
        }
    }

    // =======================================================================
    // Typed-id API (production surface, plan 5.4). Each method converts the
    // typed handle to the verified usize core through the DenseId axioms:
    // `l.as_usize()` ensures `r as nat == l.id_nat()`, so the core's
    // contracts restate over `id_nat`. The typed handle returned by
    // `new_list` round-trips (`L::try_new` on the fresh row index).
    // =======================================================================

    /// Create a new empty list, returning its typed handle (production
    /// `new_list() -> L` parity). Requires headroom in `L`'s id range.
    pub(crate) fn new_list(&mut self) -> (l: L)
        requires
            old(self).wf(),
            old(self).heads_view().len() + 1 < usize::MAX,
            old(self).heads_view().len() < L::id_bound(),
            !L::is_bit_stealing() ==> old(self).heads_view().len() + 1 < L::id_bound(),
        ensures
            final(self).wf(),
            l.id_nat() == old(self).heads_view().len(),
            final(self).nodes_view() == old(self).nodes_view(),
            final(self).model_view() == old(self).model_view().push(Seq::<usize>::empty()),
            final(self).list_seq(l.id_nat() as int) == Seq::<T>::empty(),
            forall|m: int| 0 <= m < old(self).model_view().len()
                ==> #[trigger] final(self).list_seq(m) == old(self).list_seq(m),
            final(self).heads_snapshots_view() == old(self).heads_snapshots_view(),
            final(self).nodes_snapshots_view() == old(self).nodes_snapshots_view(),
            final(self).model_snapshots_view() == old(self).model_snapshots_view(),
    {
        // Mint the typed handle for the WOULD-BE fresh row BEFORE any
        // mutation (plan 2.3: reject-before-mutate) — id-range exhaustion
        // must not leave a headless grown arena behind.
        let next_row = self.heads_len();
        let l = match L::try_new(next_row) {
            Some(l) => l,
            None => {
                proof { assert(false); }
                crate::guard::check_precondition(
                    false,
                    "ListArena::new_list: list-id range exhausted",
                );
                #[allow(clippy::empty_loop)]
                loop
                    invariant false,
                    decreases 0int,
                {
                }
            }
        };
        let raw = self.new_list_raw();
        proof {
            // new_list_raw returns the fresh row == heads_view().len() at
            // entry == next_row, so the pre-minted handle names it.
            assert(raw == next_row);
        }
        l
    }

    /// O(1) prepend through the typed handle.
    #[inline(always)]
    pub(crate) fn prepend(&mut self, l: L, payload: T)
        requires
            old(self).wf(),
            l.id_nat() < old(self).model_view().len(),
            old(self).nodes_view().len() + 1 < usize::MAX,
            // node allocation stays within N's id range (production's
            // VecI<_, N::Index> capacity semantics: the full range for a
            // bit-stealing family).
            old(self).nodes_view().len() < N::id_bound(),
            !N::is_bit_stealing() ==> old(self).nodes_view().len() + 1 < N::id_bound(),
            // No length-cache precondition. The cached count is `N::Index`-wide, so its
            // bound follows from `wf` at every id width — including 63-bit, where the old
            // `u32` cache was a real 4-billion ceiling the caller had to promise to stay
            // under. `prepend_raw` derives it; nothing is left for a caller to get wrong.
        ensures
            final(self).wf(),
            final(self).model_view().len() == old(self).model_view().len(),
            final(self).list_seq(l.id_nat() as int)
                == seq![payload] + old(self).list_seq(l.id_nat() as int),
            forall|m: int| 0 <= m < final(self).model_view().len() && m != l.id_nat() as int
                ==> #[trigger] final(self).list_seq(m) == old(self).list_seq(m),
    {
        // Runtime guard: node-id headroom before allocating (N::try_new on
        // the fresh node row; reject-before-mutate).
        crate::guard::check_precondition(
            // The fresh slot's id must be representable
            // (`try_new(n).is_some() <==> n < id_bound`); the full-range
            // family alone also needs the successor representable
            // (`lemma_node_push_fits` derives the word bound).
            N::try_new(self.nodes_len()).is_some()
                && (N::bit_stealing() || N::try_new(self.nodes_len() + 1).is_some()),
            "ListArena::prepend: node-id range exhausted",
        );
        let lu = l.as_usize();
        proof {
            l.lemma_as_nat_is_id_nat();  // as_usize ensures as_nat; bridge to id_nat. prod-parity
            assert(lu as nat == l.id_nat());
            assert(self.model_view()[lu as int]
                =~= self.model_view()[l.id_nat() as int]);
        }
        self.prepend_raw(lu, payload)
    }

    /// O(1) append through the typed handle (cached tail).
    #[inline(always)]
    pub(crate) fn append(&mut self, l: L, payload: T)
        requires
            old(self).wf(),
            l.id_nat() < old(self).model_view().len(),
            old(self).nodes_view().len() + 1 < usize::MAX,
            // node allocation stays within N's id range; see `prepend`.
            old(self).nodes_view().len() < N::id_bound(),
            !N::is_bit_stealing() ==> old(self).nodes_view().len() + 1 < N::id_bound(),
            // No length-cache precondition; see `prepend`.
        ensures
            final(self).wf(),
            final(self).model_view().len() == old(self).model_view().len(),
            final(self).list_seq(l.id_nat() as int)
                == old(self).list_seq(l.id_nat() as int).push(payload),
            forall|m: int| 0 <= m < final(self).model_view().len() && m != l.id_nat() as int
                ==> #[trigger] final(self).list_seq(m) == old(self).list_seq(m),
            // raw effects (egraph-wf W5), inherited from `append_raw`.
            final(self).model_view() == old(self).model_view().update(l.id_nat() as int,
                old(self).model_view()[l.id_nat() as int].push(
                    old(self).nodes_view().len() as usize)),
            final(self).nodes_view().len() == old(self).nodes_view().len() + 1,
            forall|k: int| 0 <= k < old(self).nodes_view().len()
                ==> (#[trigger] final(self).nodes_view()[k]).payload
                    == old(self).nodes_view()[k].payload,
            final(self).heads_snapshots_view() == old(self).heads_snapshots_view(),
            final(self).nodes_snapshots_view() == old(self).nodes_snapshots_view(),
            final(self).model_snapshots_view() == old(self).model_snapshots_view(),
            final(self).nodes_view()[old(self).nodes_view().len() as int].payload == payload,
    {
        // Runtime guard: node-id headroom before allocating; see `prepend`.
        crate::guard::check_precondition(
            N::try_new(self.nodes_len()).is_some()
                && (N::bit_stealing() || N::try_new(self.nodes_len() + 1).is_some()),
            "ListArena::append: node-id range exhausted",
        );
        proof { l.lemma_as_nat_is_id_nat(); }  // as_usize -> id_nat bridge. prod-parity
        self.append_raw(l.as_usize(), payload)
    }

    /// O(1) verified length through the typed handle.
    ///
    /// `N::Index`, matching production (`containers/src/list.rs`'s `len`): a list's
    /// length is bounded by the node arena's population, so the node arena's index type
    /// is the width it belongs in. The postcondition is stated through `as_nat`, which is
    /// `IndexLike`'s exact projection, so this is as strong as the `usize` form it
    /// replaced — the caller learns the count *is* the abstract list length, not merely
    /// that it fits.
    #[inline(always)]
    pub fn len(&self, l: L) -> (n: N::Index)
        requires self.wf(),
        ensures l.id_nat() < self.model_view().len() ==> n.as_nat() == self.list_seq(l.id_nat() as int).len(),
    {
        proof { l.lemma_as_nat_is_id_nat(); }  // prod-parity
        // Total-with-documented-panic: explicit handle-bound branch.
        if !(l.as_usize() < self.heads.store.data.len()) {
            crate::guard::refuse("ListArena::len: list handle out of range");
        }
        self.len_raw(l.as_usize())
    }

    pub fn is_empty(&self, l: L) -> (b: bool)
        requires self.wf(),
        ensures l.id_nat() < self.model_view().len() ==> b == (self.list_seq(l.id_nat() as int) == Seq::<T>::empty()),
    {
        proof { l.lemma_as_nat_is_id_nat(); }  // prod-parity
        // Total-with-documented-panic: explicit handle-bound branch.
        if !(l.as_usize() < self.heads.store.data.len()) {
            crate::guard::refuse("ListArena::is_empty: list handle out of range");
        }
        self.is_empty_raw(l.as_usize())
    }

    /// Bytes consumed by diff tracking only, summed over the two inner vecs.
    /// Diagnostic, no spec content — the same pair production exposes on every
    /// container (`containers/src/vec.rs`). Used by the store-choice memory
    /// exception in `containers-conformance/tests/layout_parity.rs`.
    /// `external_body`: the sum is an unmodeled capacity diagnostic (like
    /// `Vec::tracking_bytes`), so the overflow obligation on `+` is not proof
    /// content — a real footprint never approaches `usize::MAX`.
    #[verifier::external_body]
    pub fn tracking_bytes(&self) -> usize {
        self.heads.tracking_bytes() + self.nodes.tracking_bytes()
    }

    /// Total bytes: both inner vecs (struct + store backing + tracking). The
    /// ghost `model`/`model_snapshots` fields are erased, so this is the whole
    /// runtime footprint. Diagnostic; no spec content.
    ///
    /// This is the number memory parity with production is measured through
    /// (`containers-conformance/tests/list_arena_differential.rs`). Both sides
    /// use `InlineStore` over `L::Index`/`N::Index` columns, so elements, capture
    /// flags and diff-log entries are all the same width; the only residual delta
    /// is a constant 16 bytes from the `u64` `ContainerId` (migration plan 2.6).
    /// `external_body`: unmodeled capacity diagnostic (see `tracking_bytes`).
    #[verifier::external_body]
    pub fn total_bytes(&self) -> usize {
        self.heads.total_bytes() + self.nodes.total_bytes()
    }

    /// O(1) splice through typed handles: `dst := dst ++ src`, `src` cleared
    /// (handle stays valid and names the empty list).
    #[inline(always)]
    pub fn splice(&mut self, dst: L, src: L)
        requires
            old(self).wf(),
            // No length-cache precondition for the merged list; see `prepend`. The two
            // lists are disjoint, so `splice_raw` derives the bound from `wf`.
        ensures
            final(self).wf(),
            (dst.id_nat() < old(self).model_view().len()
                && src.id_nat() < old(self).model_view().len()
                && dst.id_nat() != src.id_nat()) ==> {
                &&& final(self).model_view().len() == old(self).model_view().len()
                &&& final(self).list_seq(dst.id_nat() as int)
                    == old(self).list_seq(dst.id_nat() as int)
                        + old(self).list_seq(src.id_nat() as int)
                &&& final(self).list_seq(src.id_nat() as int) == Seq::<T>::empty()
                &&& forall|m: int| 0 <= m < final(self).model_view().len()
                    && m != dst.id_nat() as int && m != src.id_nat() as int
                    ==> #[trigger] final(self).list_seq(m) == old(self).list_seq(m)
                // raw effects (egraph-wf W5), inherited from `splice_raw`.
                &&& final(self).model_view() == old(self).model_view()
                    .update(dst.id_nat() as int, old(self).model_view()[dst.id_nat() as int]
                        + old(self).model_view()[src.id_nat() as int])
                    .update(src.id_nat() as int, Seq::<usize>::empty())
                &&& final(self).nodes_view().len() == old(self).nodes_view().len()
                &&& (forall|k: int| 0 <= k < old(self).nodes_view().len()
                        ==> (#[trigger] final(self).nodes_view()[k]).payload
                            == old(self).nodes_view()[k].payload)
            },
            // out-of-range or equal handles refuse before any mutation, so
            // every returning path outside the guarded case is a no-op
            // (vacuously provable: those paths diverge).
            !(dst.id_nat() < old(self).model_view().len()
                && src.id_nat() < old(self).model_view().len()
                && dst.id_nat() != src.id_nat())
                ==> final(self).model_view() == old(self).model_view()
                    && final(self).nodes_view() == old(self).nodes_view(),
            final(self).heads_snapshots_view() == old(self).heads_snapshots_view(),
            final(self).nodes_snapshots_view() == old(self).nodes_snapshots_view(),
            final(self).model_snapshots_view() == old(self).model_snapshots_view(),
    {
        proof { dst.lemma_as_nat_is_id_nat(); src.lemma_as_nat_is_id_nat(); }  // prod-parity
        let du = dst.as_usize();
        let su = src.as_usize();
        // Total-with-documented-panic: handle bounds and the same-handle case
        // are explicit branches (the same-handle splice would corrupt the
        // list; formerly a check_precondition on an erased requires).
        let hn = self.heads.store.data.len();
        if !(du < hn && su < hn) {
            crate::guard::refuse("ListArena::splice: list handle out of range");
        }
        if du == su {
            crate::guard::refuse("ListArena::splice: dst and src are the same list");
        }
        self.splice_raw(du, su)
    }

    /// Iterate list `l` in order, yielding payloads by value (production
    /// `ListIter` parity).
    pub fn iter(&self, l: L) -> (it: ListIter<'_, T, L, N, TRACK>)
        requires self.wf(),
        ensures l.id_nat() < self.model_view().len() ==> ({
            &&& it.arena_ref() == self
            &&& it.list_spec() == l.id_nat()
            &&& it.pos_spec() == 0
            &&& it.cursor_ok()
        }),
    {
        proof { l.lemma_as_nat_is_id_nat(); }  // prod-parity
        // Total-with-documented-panic: handle-bound branch.
        if !(l.as_usize() < self.heads.store.data.len()) {
            crate::guard::refuse("ListArena::iter: list handle out of range");
        }
        let lu = l.as_usize();
        let head = self.heads.get_index(self.head_ix(lu)).head();
        proof {
            // cache_ok head clause: null iff the model is empty, else names
            // model[l][0] — exactly cursor_ok at pos 0.
            let m = self.model_view()[lu as int];
            if m.len() == 0 {
                assert(head.is_null());
            } else {
                assert(!head.is_null() && head.target() == m[0]);
            }
        }
        ListIter { arena: self, list: lu, pos: 0, cur: head }
    }
}

/// Forward iterator over one list's payloads. Carries the CURSOR (`cur` = the
/// physical node at model position `pos`), so each `next` is O(1): read the
/// node, step the cursor along the verified `next` cache (which `wf`'s
/// `cache_ok` ties to the model). The invariant `cursor_ok` is exactly
/// "cur names model[list][pos] (or pos == len and the cursor is exhausted)".
pub struct ListIter<'a, T, L, N, const TRACK: bool>
where
    T: Sized + Copy + core::default::Default + Tagged,
    L: DenseId,
    N: DenseId + Tagged + core::default::Default,
{
    pub(crate) arena: &'a ListArena<T, L, N, TRACK>,
    /// The raw list row; read only by spec code (plain builds erase it).
    #[allow(dead_code)]
    pub(crate) list: usize,
    pub(crate) pos: usize,
    /// Physical cursor: the node at model position `pos` (meaningless once
    /// `pos == len`; `cursor_ok`'s exhausted arm).
    pub(crate) cur: NodeRef,
}

impl<'a, T, L, N, const TRACK: bool> ListIter<'a, T, L, N, TRACK>
where
    T: Sized + Copy + core::default::Default + Tagged,
    L: DenseId,
    N: DenseId + Tagged + core::default::Default,
{
    /// The arena this iterator walks (spec twin; fields are `pub(crate)` —
    /// privacy closeout).
    pub open(crate) spec fn arena_ref(&self) -> &'a ListArena<T, L, N, TRACK> {
        self.arena
    }

    /// The (raw) list row (spec twin).
    pub open(crate) spec fn list_spec(&self) -> nat {
        self.list as nat
    }

    /// The cursor position (spec twin).
    pub open(crate) spec fn pos_spec(&self) -> nat {
        self.pos as nat
    }

    /// Cursor validity: at a live position the cursor names the model node;
    /// at the end it is null (read off the last node's next, or the head of
    /// an empty list).
    pub open(crate) spec fn cursor_ok(&self) -> bool {
        let m = self.arena.model_view()[self.list as int];
        &&& self.pos <= m.len()
        &&& if (self.pos as int) < m.len() {
                !self.cur.is_null() && self.cur.target() == m[self.pos as int]
            } else {
                self.cur.is_null()
            }
    }

    /// Yield `list_seq(list)[pos]` and advance the cursor — O(1) per call.
    ///
    /// No `rlimit` and no `spinoff_prover`: this verifies at the default budget. Worth
    /// recording, because widening the cached count first presented here as an rlimit
    /// exhaustion, which reads like a solver-budget problem and is not one — raising the
    /// budget only let the solver get far enough to report the real goal, the `pos + 1`
    /// overflow check below. The fix was the missing fact (`IndexLike::
    /// lemma_max_nat_fits_usize`), not more budget; with it, the cost is back where it was.
    #[inline(always)]
    pub fn next(&mut self) -> (r: Option<T>)
        requires
            old(self).arena_ref().wf(),
            old(self).cursor_ok(),
        ensures
            (old(self).list_spec() as int) < old(self).arena_ref().model_view().len() ==> ({
                &&& final(self).arena_ref() == old(self).arena_ref()
                &&& final(self).list_spec() == old(self).list_spec()
                &&& final(self).cursor_ok()
                &&& (old(self).pos_spec() < old(self).arena_ref().list_seq(old(self).list_spec() as int).len() ==> {
                    &&& r == Some(old(self).arena_ref().list_seq(old(self).list_spec() as int)[old(self).pos_spec() as int])
                    &&& final(self).pos_spec() == old(self).pos_spec() + 1
                })
                &&& (old(self).pos_spec() >= old(self).arena_ref().list_seq(old(self).list_spec() as int).len() ==> {
                    &&& r is None
                    &&& final(self).pos_spec() == old(self).pos_spec()
                })
            }),
    {
        // Total-with-documented-panic: stale-handle branch.
        if !(self.list < self.arena.heads.store.data.len()) {
            crate::guard::refuse("ListIter::next: list handle out of range");
        }
        let ghost m = self.arena.model_view()[self.list as int];
        if self.cur.is_null_exec() {
            proof {
                // cursor_ok's null arm forces pos == len.
                assert(self.pos as int >= m.len());
            }
            return None;
        }
        proof {
            // cursor_ok's live arm: cur names m[pos]; in range by
            // model_in_range, so the arena read is safe, and cache_ok gives
            // the node's next = m[pos+1] (or null at the last position).
            assert((self.pos as int) < m.len());
            assert(self.cur.target() == m[self.pos as int]);
            assert(m[self.pos as int] < self.arena.nodes_view().len());
            // `pos + 1` does not overflow the counter. The chain is: `pos < m.len()`
            // (above), `m.len() <= nodes.len()` (the model's entries are distinct rows),
            // `nodes.len() < N::Index::max_nat()` (the store's own `wf`), and finally
            // `max_nat() <= usize::MAX + 1` (`IndexLike`'s width obligation). The last
            // step is the one the cached count used to supply for free when it was a
            // literal `u32`; now that it follows the id family, the bound has to come
            // from the index type's contract instead of from a fixed word.
            self.arena.lemma_len_bounded(self.list as int);
            self.arena.lemma_nodes_len_fits();
            <N::Index as IndexLike>::lemma_max_nat_fits_usize();
        }
        let node = self.arena.nodes.get_index(self.arena.node_ix(self.cur.idx));
        self.cur = node.next();
        self.pos = self.pos + 1;
        proof {
            // cache_ok at (list, old pos) re-establishes cursor_ok at pos+1.
            let p = (self.pos - 1) as int;
            if self.pos as int == m.len() {
                assert(node.next_ref().is_null());
            } else {
                assert(!node.next_ref().is_null() && node.next_ref().target() == m[self.pos as int]);
            }
        }
        Some(node.payload)
    }
}

/// Structural arena validity over raw snapshot sequences *plus* the ghost model
/// that was live at the mark (for `restore`): the restored heads/nodes, with
/// `model`, must satisfy the same in-range + disjoint + cache clauses as `wf`.
/// The Phase 7 archive agreement for ListArena, opaque (see `wf`'s comment).
#[verifier::opaque]
pub open(crate) spec fn arena_archive_agrees<T, N: DenseId + Tagged>(
    archive: Seq<Seq<Seq<usize>>>,
    head_snaps: Seq<Seq<ListHead<N>>>,
    node_snaps: Seq<Seq<ListNode<T, N>>>,
) -> bool {
    &&& archive.len() == head_snaps.len()
    &&& head_snaps.len() == node_snaps.len()
    &&& (forall|k: int| 0 <= k < archive.len()
            ==> arena_model_wf(#[trigger] archive[k], head_snaps[k], node_snaps[k]))
}

pub open(crate) spec fn arena_model_wf<T, N: DenseId + Tagged>(
    model: Seq<Seq<usize>>, heads: Seq<ListHead<N>>, nodes: Seq<ListNode<T, N>>,
) -> bool {
    &&& model.len() == heads.len()
    // Packed-repr invariant, archived with each snapshot so restore can
    // re-establish it: reprs well-formed, arena within N's id range.
    &&& nodes.len() <= N::id_bound()
    &&& (forall|i: int| 0 <= i < nodes.len() ==> (#[trigger] nodes[i]).next_wf())
    &&& (forall|l: int| 0 <= l < heads.len() ==> (#[trigger] heads[l]).head_wf())
    &&& (forall|l: int, p: int|
            0 <= l < model.len() && 0 <= p < (#[trigger] model[l]).len()
                ==> #[trigger] model[l][p] < nodes.len())
    &&& (forall|l1: int, p1: int, l2: int, p2: int|
            0 <= l1 < model.len() && 0 <= p1 < model[l1].len()
                && 0 <= l2 < model.len() && 0 <= p2 < model[l2].len()
                && (#[trigger] model[l1][p1]) == (#[trigger] model[l2][p2])
                    ==> l1 == l2 && p1 == p2)
    &&& (forall|l: int| 0 <= l < model.len() ==> {
            let h = (#[trigger] heads[l]).head_ref();
            if model[l].len() == 0 { h.is_null() }
            else { !h.is_null() && h.target() == model[l][0] }
        })
    &&& (forall|l: int| 0 <= l < model.len() && (#[trigger] model[l]).len() > 0
            ==> heads[l].tail_spec() == model[l][model[l].len() - 1])
    &&& (forall|l: int, p: int|
            0 <= l < model.len() && 0 <= p < model[l].len() ==> {
                let nx = nodes[#[trigger] model[l][p] as int].next_ref();
                if p == model[l].len() - 1 { nx.is_null() }
                else { !nx.is_null() && nx.target() == model[l][p + 1] }
            })
    &&& (forall|l: int| 0 <= l < model.len()
            ==> (#[trigger] heads[l]).len_spec() == (#[trigger] model[l]).len())
}

/// Source position of `model[lx][px]` after `splice(dst, src)` (model =
/// dst++src at dst, [] at src): maps each post-position back to its OLD
/// `(list, pos)`. Used to discharge disjointness via the old global disjointness.
pub open(crate) spec fn splice_src(
    old_model: Seq<Seq<usize>>, dst: int, src: int, lx: int, px: int,
) -> (int, int) {
    if lx == dst {
        if px < old_model[dst].len() { (dst, px) } else { (src, px - old_model[dst].len()) }
    } else {
        (lx, px)
    }
}

/// `splice_src` is injective, so `splice`'s post-model stays disjoint.
///
/// Stated over bare `Seq<Seq<usize>>` rather than over `&ListArena`, and taking
/// only the old disjointness rather than a full `wf()`: the goal here is
/// `model_disjoint`'s quad-nested
/// `forall|l1,p1,l2,p2| m[l1][p1] == m[l2][p2] ==> ...`, whose trigger matches
/// two *independent* nested accesses. Proved inside `splice_raw`'s body it
/// e-matched against every sequence access reachable from both states' `wf()`
/// and blew up to 17.6M instantiations on its own (see that function's header).
/// With nothing else in scope there is almost nothing for it to match.
///
/// Mirrors `circular_list::lemma_splice_disjoint` / `lemma_ring_same_pos`, which
/// isolate the same quantifier for the same reason.
pub(crate) proof fn lemma_splice_disjoint(
    old_model: Seq<Seq<usize>>, model: Seq<Seq<usize>>, dst: int, src: int,
)
    requires
        0 <= dst < old_model.len(),
        0 <= src < old_model.len(),
        dst != src,
        // old disjointness, the only hypothesis the body needs.
        forall|l1: int, p1: int, l2: int, p2: int|
            0 <= l1 < old_model.len() && 0 <= p1 < old_model[l1].len()
                && 0 <= l2 < old_model.len() && 0 <= p2 < old_model[l2].len()
                && (#[trigger] old_model[l1][p1]) == (#[trigger] old_model[l2][p2])
                    ==> l1 == l2 && p1 == p2,
        // how splice rewrote the model.
        model.len() == old_model.len(),
        model[dst] == old_model[dst] + old_model[src],
        model[src] == Seq::<usize>::empty(),
        forall|m: int| 0 <= m < model.len() && m != dst && m != src
            ==> #[trigger] model[m] == old_model[m],
    ensures
        forall|l1: int, p1: int, l2: int, p2: int|
            0 <= l1 < model.len() && 0 <= p1 < model[l1].len()
                && 0 <= l2 < model.len() && 0 <= p2 < model[l2].len()
                && (#[trigger] model[l1][p1]) == (#[trigger] model[l2][p2])
                    ==> l1 == l2 && p1 == p2,
{
    let dlen = old_model[dst].len();
    assert forall|l1: int, p1: int, l2: int, p2: int|
        0 <= l1 < model.len() && 0 <= p1 < model[l1].len()
            && 0 <= l2 < model.len() && 0 <= p2 < model[l2].len()
            && (#[trigger] model[l1][p1]) == (#[trigger] model[l2][p2])
        implies l1 == l2 && p1 == p2 by {
        // each post entry is an old entry, at splice_src's coordinates.
        let s1 = splice_src(old_model, dst, src, l1, p1);
        let s2 = splice_src(old_model, dst, src, l2, p2);
        assert(model[l1][p1] == old_model[s1.0][s1.1]);
        assert(model[l2][p2] == old_model[s2.0][s2.1]);
        // old disjointness collapses the two sources...
        assert(s1.0 == s2.0 && s1.1 == s2.1);
        // ...and splice_src is injective: within dst the p < dlen split is
        // decided by which side each landed on, and src is empty so no
        // position of it is ever in range.
        assert(l1 == l2 && p1 == p2);
    }
}

/// Inserting one fresh index into list `l` at position `fp` keeps the model
/// disjoint. Serves both `prepend_raw` (`fp == 0`) and `append_raw`
/// (`fp == |model[l]| - 1`): in both the new entry holds `slot`, an index no old
/// list contained (`slot` is the arena's fresh end, and every old entry is
/// `< slot`), and every other entry maps injectively back to an old one via
/// `shift` -- identity off `l`, and off-by-one past `fp` within `l`.
///
/// Extracted for the same reason as `lemma_splice_disjoint` (see its header):
/// the goal is `model_disjoint`'s quad-nested quantifier, whose trigger matches
/// two independent nested accesses, so leaving it in an exec body makes it
/// e-match against everything both states' `wf()` puts in scope.
pub(crate) proof fn lemma_insert_fresh_disjoint(
    old_model: Seq<Seq<usize>>, model: Seq<Seq<usize>>, l: int, fp: int, slot: usize,
)
    requires
        0 <= l < old_model.len(),
        0 <= fp < model[l].len(),
        // old disjointness.
        forall|l1: int, p1: int, l2: int, p2: int|
            0 <= l1 < old_model.len() && 0 <= p1 < old_model[l1].len()
                && 0 <= l2 < old_model.len() && 0 <= p2 < old_model[l2].len()
                && (#[trigger] old_model[l1][p1]) == (#[trigger] old_model[l2][p2])
                    ==> l1 == l2 && p1 == p2,
        // `slot` is fresh: strictly above every old index.
        forall|lx: int, px: int|
            0 <= lx < old_model.len() && 0 <= px < old_model[lx].len()
                ==> #[trigger] old_model[lx][px] < slot,
        // shape of the insertion.
        model.len() == old_model.len(),
        model[l].len() == old_model[l].len() + 1,
        model[l][fp] == slot,
        forall|px: int| 0 <= px < model[l].len() && px != fp
            ==> #[trigger] model[l][px]
                == old_model[l][if px < fp { px } else { px - 1 }],
        forall|lx: int| 0 <= lx < model.len() && lx != l
            ==> #[trigger] model[lx] == old_model[lx],
    ensures
        forall|l1: int, p1: int, l2: int, p2: int|
            0 <= l1 < model.len() && 0 <= p1 < model[l1].len()
                && 0 <= l2 < model.len() && 0 <= p2 < model[l2].len()
                && (#[trigger] model[l1][p1]) == (#[trigger] model[l2][p2])
                    ==> l1 == l2 && p1 == p2,
{
    assert forall|l1: int, p1: int, l2: int, p2: int|
        0 <= l1 < model.len() && 0 <= p1 < model[l1].len()
            && 0 <= l2 < model.len() && 0 <= p2 < model[l2].len()
            && (#[trigger] model[l1][p1]) == (#[trigger] model[l2][p2])
        implies l1 == l2 && p1 == p2 by {
        let fresh1 = l1 == l && p1 == fp;
        let fresh2 = l2 == l && p2 == fp;
        if fresh1 && fresh2 {
        } else if fresh1 {
            // one side is `slot`, the other an old index, which is < slot.
            assert(model[l2][p2] < slot);
        } else if fresh2 {
            assert(model[l1][p1] < slot);
        } else {
            // both old: pull back through `shift`, apply old disjointness, and
            // note the shift is injective (it is monotone on each side of fp).
            let s1 = if l1 == l && p1 > fp { p1 - 1 } else { p1 };
            let s2 = if l2 == l && p2 > fp { p2 - 1 } else { p2 };
            assert(model[l1][p1] == old_model[l1][s1]);
            assert(model[l2][p2] == old_model[l2][s2]);
            assert(l1 == l2 && s1 == s2);
            assert(p1 == p2);
        }
    }
}

/// Cache-consistency of a single node's `next` after `splice`. Only `dst`'s old
/// tail node was relinked (to `src`'s head); all others are unchanged.
pub(crate) proof fn splice_cache_node<T, L, N, const TRACK: bool>(
    pre: ListArena<T, L, N, TRACK>, post: &ListArena<T, L, N, TRACK>,
    dst: int, src: int, dtail: usize, shead: NodeRef,
    dst_empty: bool, src_empty: bool, l2: int, p: int,
)
    where
        T: Sized + Copy + core::default::Default + Tagged,
        L: DenseId,
        N: DenseId + Tagged + core::default::Default,
    requires
        pre.wf(),
        0 <= dst < pre.model_view().len(),
        0 <= src < pre.model_view().len(),
        dst != src,
        0 <= l2 < post.model_view().len(),
        0 <= p < post.model_view()[l2].len(),
        post.nodes_view().len() == pre.nodes_view().len(),
        post.model_view().len() == pre.model_view().len(),
        // post model = dst++src at dst, [] at src, else unchanged.
        post.model_view()[dst]
            == pre.model_view()[dst] + pre.model_view()[src],
        post.model_view()[src] == Seq::<usize>::empty(),
        forall|m: int| 0 <= m < post.model_view().len() && m != dst && m != src
            ==> post.model_view()[m] == pre.model_view()[m],
        dst_empty == (pre.model_view()[dst].len() == 0),
        src_empty == (pre.model_view()[src].len() == 0),
        // nodes: only dtail relinked to shead (when both non-empty); else equal.
        !dst_empty && !src_empty ==> {
            &&& dtail == pre.model_view()[dst][pre.model_view()[dst].len() - 1]
            &&& shead == pre.heads_view()[src].head_ref()
            &&& post.nodes_view()[dtail as int].next_ref() == shead
            &&& (forall|k: int| 0 <= k < post.nodes_view().len() && k != dtail as int
                    ==> post.nodes_view()[k] == pre.nodes_view()[k])
        },
        (dst_empty || src_empty) ==>
            (forall|k: int| 0 <= k < post.nodes_view().len()
                ==> post.nodes_view()[k] == pre.nodes_view()[k]),
    ensures
        ({
            let nx = post.nodes_view()[post.model_view()[l2][p] as int].next_ref();
            if p == post.model_view()[l2].len() - 1 { nx.is_null() }
            else { !nx.is_null() && nx.target() == post.model_view()[l2][p + 1] }
        }),
{
    let pm = pre.model_view();
    let pn = pre.nodes_view();
    let pom = post.model_view();
    let pon = post.nodes_view();
    let dlen = pm[dst].len();
    let idx = pom[l2][p];

    if l2 == dst && !dst_empty && !src_empty {
        // dst's concatenated list: [old dst nodes][old src nodes].
        if p < dlen - 1 {
            // interior of old dst (not the tail): node & its successor unchanged
            // from old dst's cache; idx != dtail since dtail is dst's LAST.
            assert(pom[l2][p] == pm[dst][p]);
            assert(pm[dst][p] != dtail);  // dtail is the last of dst, p < dlen-1
            assert(pon[idx as int] == pn[idx as int]);
            // old cache_ok for dst at p: next -> pm[dst][p+1] == pom[l2][p+1].
            assert(pom[l2][p + 1] == pm[dst][p + 1]);
        } else if p == dlen - 1 {
            // dst's old tail, relinked to src's head == old src[0] == pom[l2][dlen].
            assert(pm[dst][p] == dtail);
            assert(pon[dtail as int].next_ref() == shead);
            assert(shead.target() == pm[src][0]);          // old cache: src head
            assert(pom[l2][p + 1] == pm[src][0]);
        } else {
            // src portion: index p maps to old src[p - dlen]; nodes unchanged
            // (only dtail relinked, and src nodes != dtail by disjointness).
            assert(pom[l2][p] == pm[src][p - dlen]);
            assert(pm[src][p - dlen] != dtail);            // disjoint: src ∩ dst = ∅
            assert(pon[idx as int] == pn[idx as int]);
            if p == pom[l2].len() - 1 {
                // last of src: old src cache says null.
                assert(p - dlen == pm[src].len() - 1);
            } else {
                assert(pom[l2][p + 1] == pm[src][p + 1 - dlen]);
            }
        }
    } else if l2 == dst {
        // dst empty or src empty: model[dst] is whichever was non-empty (or
        // empty), nodes fully unchanged.
        assert(pom[l2][p] == pm[dst][p] || pom[l2][p] == pm[src][p - dlen]);
        assert(pon[idx as int] == pn[idx as int]);
    } else {
        // other list (incl. src, which is now empty so vacuous): unchanged model,
        // and its nodes are disjoint from dtail.
        assert(pom[l2] == pm[l2]);
        assert(pm[l2][p] != dtail || dst_empty || src_empty);
        assert(pon[idx as int] == pn[idx as int]);
    }
}

} // verus!

// prod-parity: production derives `Debug` on `ListArenaToken`; manual here
// (composes two `VecToken`s, now `Debug`).
impl core::fmt::Debug for ListArenaToken {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("ListArenaToken")
            .field("heads", &self.heads)
            .field("nodes", &self.nodes)
            .finish()
    }
}

// ---------------------------------------------------------------------------
// White-box oracle access (plain Rust; see bplus.rs's matching comment).
// Read-only — cannot violate any invariant.
// ---------------------------------------------------------------------------
impl<T, N: DenseId + Tagged + core::default::Default> ListNode<T, N> {
    /// Read-only unpacked next pointer for white-box tests:
    /// `None` = end of list, `Some(i)` = arena index of the next node.
    #[doc(hidden)]
    pub fn white_box_next(&self) -> Option<usize> {
        let o = crate::opt::Opt::<N>::from_raw(self.next_repr);
        if o.is_none() {
            None
        } else {
            Some(o.get().as_usize())
        }
    }
}

impl<T, L, N, const TRACK: bool> ListArena<T, L, N, TRACK>
where
    T: Sized + Copy + core::default::Default + Tagged,
    L: DenseId,
    N: DenseId + Tagged + core::default::Default,
{
    /// Read-only heads-column access for white-box tests.
    #[doc(hidden)]
    pub fn white_box_heads(
        &self,
    ) -> &SpVec<ListHead<N>, L::Index, InlineStore<ListHead<N>, L::Index>, TRACK> {
        &self.heads
    }

    /// Read-only nodes-column access for white-box tests.
    #[doc(hidden)]
    pub fn white_box_nodes(
        &self,
    ) -> &SpVec<ListNode<T, N>, N::Index, InlineStore<ListNode<T, N>, N::Index>, TRACK> {
        &self.nodes
    }
}

// ---------------------------------------------------------------------------
// Trusted glue (outside verus!{}; trust ledger group E): std Iterator via
// 1-line delegation to the verified inherent `next`.
// ---------------------------------------------------------------------------

impl<'a, T, L, N, const TRACK: bool> Iterator for ListIter<'a, T, L, N, TRACK>
where
    T: Sized + Copy + core::default::Default + Tagged,
    L: crate::opt::DenseId,
    N: crate::opt::DenseId + crate::tagged::Tagged + core::default::Default,
{
    type Item = T;

    #[inline(always)]
    fn next(&mut self) -> Option<T> {
        ListIter::next(self)
    }
}

// Production-surface parity (production ships Default).
impl<T, L, N, const TRACK: bool> Default for ListArena<T, L, N, TRACK>
where
    T: Sized + Copy + core::default::Default + Tagged,
    L: DenseId,
    N: DenseId + Tagged + core::default::Default,
{
    fn default() -> Self {
        Self::new()
    }
}
