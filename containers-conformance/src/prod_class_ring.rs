// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Reference e-class ring for layout and byte-accounting differentials.
//!
//! The model uses the reference crate's inline-capture `VecI` and the same
//! two-cell splice semantics as `CircularList`. Keeping it in one module lets
//! layout and dynamic byte-accounting tests share one oracle.
//!
//! The model is generic over the node id: its storage word is `T::Index`, never
//! a hard-coded `u32`. The index type is part of the memory contract because a
//! captured write logs `(cell, T::Index)`, 12 bytes for the 31-bit e-class
//! instantiation, rather than the 16-byte `(cell, usize)` form.
//! [`crate::prod_class_ring::ProdRing`]/[`crate::prod_class_ring::Node31`] name
//! the 31-bit instantiation the harnesses use.
use prod::DenseId;
use semi_persistent_containers as prod;

prod::define_id31! { pub struct PNodeId / StoredPNodeId, "n"; }
prod::define_id31! { pub struct PClassKey / StoredPClassKey, "k"; }

/// The 31-bit node id used by the default reference-ring tests.
pub type Node31 = PNodeId;

/// Reference ring cell: the `next` pointer around the class ring (capture bit
/// stolen from its spare MSB) plus the class's sparse-set key with its own
/// presence bit. Both are configured-width bit-stealing IDs.
#[derive(Clone, Copy)]
pub struct EClassEntry<T: DenseId, K: DenseId<Index = T::Index>> {
    pub next: T,
    class_key: prod::Opt<K>,
}

impl<T: DenseId, K: DenseId<Index = T::Index>> Default for EClassEntry<T, K> {
    fn default() -> Self {
        Self::new(T::default(), K::default())
    }
}

impl<T: DenseId, K: DenseId<Index = T::Index>> EClassEntry<T, K> {
    pub fn new(next: T, repr_id: K) -> Self {
        Self {
            next,
            class_key: prod::Opt::some(repr_id),
        }
    }
    pub fn repr_id_unchecked(&self) -> K {
        self.class_key.get_unchecked()
    }
    /// Mark the class key absent — the presence-bit clear an absorbed class gets.
    pub fn set_absent(&mut self) {
        self.class_key.set_none();
    }
    pub fn is_absent(&self) -> bool {
        self.class_key.is_none()
    }
}

impl<T: DenseId, K: DenseId<Index = T::Index>> prod::Tagged for EClassEntry<T, K> {
    type Repr = (<T as prod::Tagged>::Repr, <K as prod::Tagged>::Repr);
    fn into_repr(self) -> Self::Repr {
        (self.next.into_repr(), self.class_key.into_raw())
    }
    fn from_repr(s: &Self::Repr) -> Self {
        Self {
            next: T::from_repr(&s.0),
            class_key: prod::Opt::from_raw(s.1),
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

/// Reference ring over the inline-capture vector, indexed by the id's
/// own storage word (so a captured write logs `(cell, T::Index)` = 12 bytes at
/// 31-bit ids, not `(cell, usize)` = 16 — the same width the verified ring
/// keeps).
pub type ProdRingOf<T, K, const TRACK: bool> =
    prod::VecI<EClassEntry<T, K>, <T as DenseId>::Index, TRACK>;

/// The 31-bit instantiation the harnesses measure.
pub type ProdRing<const TRACK: bool> = ProdRingOf<Node31, PClassKey, TRACK>;

/// `n` singleton classes, each its own self-loop.
pub fn build<const TRACK: bool>(n: usize) -> ProdRing<TRACK> {
    build_of::<Node31, PClassKey, TRACK>(n)
}

/// [`build`] at an arbitrary id family.
pub fn build_of<T: DenseId, K: DenseId<Index = T::Index>, const TRACK: bool>(
    n: usize,
) -> ProdRingOf<T, K, TRACK> {
    let mut ring: ProdRingOf<T, K, TRACK> = ProdRingOf::new();
    for i in 0..n {
        let id = T::from_usize(i);
        ring.push(EClassEntry::new(id, K::from_usize(i)));
    }
    ring
}

/// Ring splice: two full-cell writes, the second
/// with the absorbed class's key marked absent. (The sparse-set `remove` that
/// followed it in the consumer is not part of the ring, so it is excluded here
/// and from the verus arm alike.)
pub fn splice<T: DenseId, K: DenseId<Index = T::Index>, const TRACK: bool>(
    ring: &mut ProdRingOf<T, K, TRACK>,
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

/// Iterator-shaped ring walk used by the differential oracle.
pub struct ClassIter<'a, T: DenseId, K: DenseId<Index = T::Index>, const TRACK: bool> {
    entries: &'a ProdRingOf<T, K, TRACK>,
    start_idx: T,
    current_idx: T,
    done: bool,
}

impl<T: DenseId, K: DenseId<Index = T::Index>, const TRACK: bool> Iterator
    for ClassIter<'_, T, K, TRACK>
{
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

/// Walk `start`'s ring, yielding each node once.
pub fn iter_class<T: DenseId, K: DenseId<Index = T::Index>, const TRACK: bool>(
    ring: &ProdRingOf<T, K, TRACK>,
    start: T,
) -> ClassIter<'_, T, K, TRACK> {
    ClassIter {
        entries: ring,
        start_idx: start,
        current_idx: start,
        done: false,
    }
}

/// Class size via [`ClassIter`].
pub fn walk<T: DenseId, K: DenseId<Index = T::Index>, const TRACK: bool>(
    ring: &ProdRingOf<T, K, TRACK>,
    start: T,
) -> usize {
    iter_class(ring, start).count()
}
