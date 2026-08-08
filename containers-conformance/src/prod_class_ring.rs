// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! The e-class ring **as it was before the consumer swap** — the baseline
//! every class-ring parity claim is measured against.
//!
//! `egraph/src/classes.rs` no longer hand-rolls its class ring; it uses the
//! verified `CircularList`. So the production arm for the ring's perf and memory
//! rows cannot be "some other production container": it has to be the exact
//! implementation the swap deleted. This module reproduces it verbatim from
//! `git show origin/main:egraph/src/classes.rs` (`EClassEntry`, its `Tagged` impl,
//! `splice_classes`'s ring surgery, and `ClassIter`'s walk) on production's
//! `VecI`.
//!
//! It lives in the shared lib rather than in each harness because there are now
//! four consumers of it (`benches/perf_gate.rs`, `tests/layout_parity.rs`,
//! `tests/differential.rs`, `examples/splicesplit.rs`) and the whole value of a
//! "verbatim" baseline is that all of them measure the *same* baseline. Four
//! copy-pasted reproductions would drift, and a drifting baseline silently
//! rewrites the comparison it exists to anchor.
//!
//! ## Generic over the node id, as the original was
//!
//! `origin/main`'s entry was `EClassEntry<T: DenseId>` with
//! `repr_stored: <T::Index as Tagged>::Repr`, and today's `ClassRing<T, TRACK> =
//! CircularList<Opt<T::Index>, T, TRACK>` is parameterized the same way. So this
//! reproduction is too: the storage word is `T::Index`, never a hard-coded `u32`.
//! Monomorphizing it here would pin every harness to the 31-bit id family and
//! quietly narrow the "verbatim" claim to one instantiation — and the index type
//! is exactly what the memory rows are about (a captured write logs
//! `(cell, T::Index)`, 16 bytes at `u32`, not `(cell, usize)` at 24).
//! [`Ring31`]/[`Node31`] name the 31-bit instantiation the harnesses use.
use prod::Tagged as _;
use prod::{DenseId, IndexLike};
use semi_persistent_containers as prod;

prod::define_id31! { pub struct PNodeId / StoredPNodeId, "n"; }

/// The 31-bit node id the harnesses instantiate the ring at — the family
/// `egraph`'s `NodeId` belongs to, so `T::Index` is `u32` and a captured write
/// logs 16 bytes.
pub type Node31 = PNodeId;

/// The pre-swap ring cell: the `next` pointer around the class ring (capture bit
/// stolen from its spare MSB) plus the class's sparse-set key with its own
/// presence bit. 12 bytes at 31-bit ids — the size the verified
/// `CircularNodeRepr<Opt<T::Index>, T>` has to match (`tests/layout_parity.rs`).
#[derive(Clone, Copy)]
pub struct EClassEntry<T: DenseId> {
    pub next: T,
    repr_stored: <T::Index as prod::Tagged>::Repr,
}

impl<T: DenseId> Default for EClassEntry<T> {
    fn default() -> Self {
        Self::new(T::default(), T::Index::MIN)
    }
}

impl<T: DenseId> EClassEntry<T> {
    pub fn new(next: T, repr_id: T::Index) -> Self {
        Self {
            next,
            repr_stored: repr_id.into_repr(),
        }
    }
    pub fn repr_id_unchecked(&self) -> T::Index {
        <T::Index as prod::Tagged>::from_repr(&self.repr_stored)
    }
    /// Mark the class key absent — the presence-bit clear an absorbed class gets.
    pub fn set_absent(&mut self) {
        <T::Index as prod::Tagged>::set_tag(&mut self.repr_stored);
    }
    pub fn is_absent(&self) -> bool {
        <T::Index as prod::Tagged>::tag(&self.repr_stored)
    }
}

impl<T: DenseId> prod::Tagged for EClassEntry<T> {
    type Repr = (<T as prod::Tagged>::Repr, <T::Index as prod::Tagged>::Repr);
    fn into_repr(self) -> Self::Repr {
        (self.next.into_repr(), self.repr_stored)
    }
    fn from_repr(s: &Self::Repr) -> Self {
        Self {
            next: T::from_repr(&s.0),
            repr_stored: s.1,
        }
    }
    fn tag(s: &Self::Repr) -> bool {
        T::tag(&s.0)
    }
    fn set_tag(s: &mut Self::Repr) {
        T::set_tag(&mut s.0);
    }
    fn clear_tag(s: &mut Self::Repr) {
        T::clear_tag(&mut s.0);
    }
}

/// The pre-swap ring: production's inline-capture vector, indexed by the id's
/// own storage word (so a captured write logs `(cell, T::Index)` = 16 bytes at
/// 31-bit ids, not `(cell, usize)` = 24 — the same width the verified ring
/// keeps).
pub type ProdRingOf<T, const TRACK: bool> =
    prod::VecI<EClassEntry<T>, <T as DenseId>::Index, TRACK>;

/// The 31-bit instantiation the harnesses measure.
pub type ProdRing<const TRACK: bool> = ProdRingOf<Node31, TRACK>;

/// `n` singleton classes, each its own self-loop.
pub fn build<const TRACK: bool>(n: usize) -> ProdRing<TRACK> {
    build_of::<Node31, TRACK>(n)
}

/// [`build`] at an arbitrary id family.
pub fn build_of<T: DenseId, const TRACK: bool>(n: usize) -> ProdRingOf<T, TRACK> {
    let mut ring: ProdRingOf<T, TRACK> = ProdRingOf::new();
    for i in 0..n {
        let id = T::from_usize(i);
        ring.push(EClassEntry::new(
            id,
            T::Index::try_from_usize(i).expect("id range exhausted"),
        ));
    }
    ring
}

/// The pre-swap `splice_classes` ring surgery: two full-cell writes, the second
/// with the absorbed class's key marked absent. (The sparse-set `remove` that
/// followed it in the consumer is not part of the ring, so it is excluded here
/// and from the verus arm alike.)
pub fn splice<T: DenseId, const TRACK: bool>(
    ring: &mut ProdRingOf<T, TRACK>,
    survivor: T,
    absorbed: T,
) {
    let surv = ring.get(survivor.into());
    let abs = ring.get(absorbed.into());
    ring.set(
        survivor.into(),
        EClassEntry::new(abs.next, surv.repr_id_unchecked()),
    );
    let mut absorbed_entry = EClassEntry::new(surv.next, abs.repr_id_unchecked());
    absorbed_entry.set_absent();
    ring.set(absorbed.into(), absorbed_entry);
}

/// The pre-swap `ClassIter`, reproduced verbatim from
/// `git show origin/main:egraph/src/classes.rs` — an `Iterator` with a `done`
/// flag, *not* a plain counting loop.
///
/// The distinction is not cosmetic. A hand-rolled `loop` lets LLVM hoist the
/// vector's data pointer and length into a single paired load (`ldp`) and keep
/// the whole walk in one basic block; the `Iterator` shape reloads through
/// `&mut self` per `next` call and carries the `done` flag. On a two-node ring
/// — the shape `class_walk` measures — that preamble difference is most of the
/// timed work, so comparing a plain loop against the verified `RingIter` scores
/// the *walk style* rather than the container. The baseline has to be the
/// implementation the swap deleted, and that implementation was this one.
pub struct ClassIter<'a, T: DenseId, const TRACK: bool> {
    entries: &'a ProdRingOf<T, TRACK>,
    start_idx: T,
    current_idx: T,
    done: bool,
}

impl<T: DenseId, const TRACK: bool> Iterator for ClassIter<'_, T, TRACK> {
    type Item = T;

    fn next(&mut self) -> Option<T> {
        if self.done {
            return None;
        }
        let result = self.current_idx;
        self.current_idx = self.entries.get(self.current_idx.into()).next;
        if self.current_idx == self.start_idx {
            self.done = true;
        }
        Some(result)
    }
}

/// The pre-swap `iter_class`: walk `start`'s ring, yielding each node once.
pub fn iter_class<T: DenseId, const TRACK: bool>(
    ring: &ProdRingOf<T, TRACK>,
    start: T,
) -> ClassIter<'_, T, TRACK> {
    ClassIter {
        entries: ring,
        start_idx: start,
        current_idx: start,
        done: false,
    }
}

/// Class size via the pre-swap `ClassIter` — the counting form the perf row
/// uses, kept as a thin wrapper so the walk itself stays the shipped shape.
pub fn walk<T: DenseId, const TRACK: bool>(ring: &ProdRingOf<T, TRACK>, start: T) -> usize {
    iter_class(ring, start).count()
}
