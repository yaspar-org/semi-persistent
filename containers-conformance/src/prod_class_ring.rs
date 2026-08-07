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
use prod::Tagged as _;
use semi_persistent_containers as prod;

prod::define_id31! { pub struct PNodeId / StoredPNodeId, "n"; }

/// The pre-swap ring cell: the `next` pointer around the class ring (capture bit
/// stolen from its spare MSB) plus the class's sparse-set key with its own
/// presence bit. 12 bytes at 31-bit ids — the size the verified
/// `CircularNodeRepr<Opt<u32>, N>` has to match (`tests/layout_parity.rs`).
#[derive(Clone, Copy)]
pub struct EClassEntry {
    pub next: PNodeId,
    repr_stored: <u32 as prod::Tagged>::Repr,
}

impl Default for EClassEntry {
    fn default() -> Self {
        Self::new(PNodeId::default(), 0)
    }
}

impl EClassEntry {
    pub fn new(next: PNodeId, repr_id: u32) -> Self {
        Self {
            next,
            repr_stored: repr_id.into_repr(),
        }
    }
    pub fn repr_id_unchecked(&self) -> u32 {
        <u32 as prod::Tagged>::from_repr(&self.repr_stored)
    }
    /// Mark the class key absent — the presence-bit clear an absorbed class gets.
    pub fn set_absent(&mut self) {
        <u32 as prod::Tagged>::set_tag(&mut self.repr_stored);
    }
    pub fn is_absent(&self) -> bool {
        <u32 as prod::Tagged>::tag(&self.repr_stored)
    }
}

impl prod::Tagged for EClassEntry {
    type Repr = (<PNodeId as prod::Tagged>::Repr, <u32 as prod::Tagged>::Repr);
    fn into_repr(self) -> Self::Repr {
        (self.next.into_repr(), self.repr_stored)
    }
    fn from_repr(s: &Self::Repr) -> Self {
        Self {
            next: PNodeId::from_repr(&s.0),
            repr_stored: s.1,
        }
    }
    fn tag(s: &Self::Repr) -> bool {
        PNodeId::tag(&s.0)
    }
    fn set_tag(s: &mut Self::Repr) {
        PNodeId::set_tag(&mut s.0);
    }
    fn clear_tag(s: &mut Self::Repr) {
        PNodeId::clear_tag(&mut s.0);
    }
}

/// The pre-swap ring: production's inline-capture vector, indexed by the id's
/// own storage word (so a captured write logs `(cell, u32)` = 16 bytes, not
/// `(cell, usize)` = 24 — the same width the verified ring keeps).
pub type ProdRing<const TRACK: bool> = prod::VecI<EClassEntry, u32, TRACK>;

/// `RING_N` singleton classes, each its own self-loop.
pub fn build<const TRACK: bool>(n: usize) -> ProdRing<TRACK> {
    let mut ring: ProdRing<TRACK> = ProdRing::new();
    for i in 0..n {
        let id = PNodeId::new(i as u32);
        ring.push(EClassEntry::new(id, i as u32));
    }
    ring
}

/// The pre-swap `splice_classes` ring surgery: two full-cell writes, the second
/// with the absorbed class's key marked absent. (The sparse-set `remove` that
/// followed it in the consumer is not part of the ring, so it is excluded here
/// and from the verus arm alike.)
pub fn splice<const TRACK: bool>(ring: &mut ProdRing<TRACK>, survivor: PNodeId, absorbed: PNodeId) {
    let surv = ring.get(survivor);
    let abs = ring.get(absorbed);
    ring.set(
        survivor,
        EClassEntry::new(abs.next, surv.repr_id_unchecked()),
    );
    let mut absorbed_entry = EClassEntry::new(surv.next, abs.repr_id_unchecked());
    absorbed_entry.set_absent();
    ring.set(absorbed, absorbed_entry);
}

/// The pre-swap `ClassIter`: yield, step through `next`, stop on return to the
/// start. Returns the class size.
pub fn walk<const TRACK: bool>(ring: &ProdRing<TRACK>, start: PNodeId) -> usize {
    let mut cur = start;
    let mut n = 0usize;
    loop {
        n += 1;
        cur = ring.get(cur).next;
        if cur == start {
            return n;
        }
    }
}
