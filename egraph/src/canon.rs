// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Canonization strategies for node children during rebuild.
//!
//! Two traits:
//! - `FixedCanon<G, K>` — in-place canonization of `[G; K]` (never shrinks)
//! - `VarCanon<G, C>` — destination-passing canonization into a reusable buffer

use crate::containers::DenseId;

// ---------------------------------------------------------------------------
// Fixed-arity canonization
// ---------------------------------------------------------------------------

/// Canonize a fixed-size children array in place.
pub trait FixedCanon<G: DenseId, const K: usize> {
    fn canonize(children: &mut [G; K], find: impl Fn(G) -> G);
}

/// Plain: just apply find to each child, preserve order.
pub struct PlainCanon;

impl<G: DenseId, const K: usize> FixedCanon<G, K> for PlainCanon {
    #[inline]
    fn canonize(children: &mut [G; K], find: impl Fn(G) -> G) {
        for c in children.iter_mut() {
            *c = find(*c);
        }
    }
}

/// Commutative: apply find, then sort the pair.
pub struct CCanon;

impl<G: DenseId + Ord> FixedCanon<G, 2> for CCanon {
    #[inline]
    fn canonize(children: &mut [G; 2], find: impl Fn(G) -> G) {
        children[0] = find(children[0]);
        children[1] = find(children[1]);
        if children[0] > children[1] {
            children.swap(0, 1);
        }
    }
}

// ---------------------------------------------------------------------------
// Variable-arity canonization
// ---------------------------------------------------------------------------

/// The count clamp for a variadic op's canonical form (design "storage partition and clamp are
/// independent axes"). Passed to [`VarCanon::canonize`] so the clamp is applied *inside*
/// canonization (its output is always the canonical form), not fixed up afterward. Kept
/// clamp-mode-only here so `canon.rs` needs no `registry` dependency: the caller maps the op's
/// `Clamp` descriptor to this before canonizing. Only [`MSetCanon`] acts on a non-`None` value;
/// the clamp-free canonizers ([`OrderedCanon`]) and the ones whose clamp is structural
/// ([`SetCanon`]'s `dedup` = idempotent) ignore it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MSetClamp {
    /// No count clamp beyond what the canonizer bakes in (plain AC; also the value passed to the
    /// clamp-free / structurally-clamped canonizers).
    None,
    /// Nilpotent order `n`: counts reduce mod `n`, zeroed summands drop (`x∘x = e`).
    Nilpotent { order: u8 },
}

/// `canonize` must *establish* the representation invariant: its output is, by definition, the
/// canonical child form for the op — never a temporarily-wrong form fixed up by a later pass.
/// Where an op's canonical form depends on an algebraic count clamp (nilpotent: counts mod n), the
/// clamp is applied *inside* `canonize` via the `mode` argument, exactly as [`SetCanon`] bakes its
/// idempotent clamp (`dedup`) into its own `canonize`. `mode` is a concrete parameter (not an
/// associated type) so it adds no `where`-clause bound anywhere; canonizers that do not act on it
/// take it and ignore it.
pub trait VarCanon<G: DenseId, C> {
    fn canonize(
        buf: &mut Vec<C>,
        start: usize,
        end: usize,
        get: impl Fn(usize) -> C,
        find: impl Fn(G) -> G,
        mode: MSetClamp,
    );
}

/// Ordered: apply find, preserve order. (PlainN, A). No clamp; `mode` ignored.
pub struct OrderedCanon;

impl<G: DenseId> VarCanon<G, G> for OrderedCanon {
    #[inline]
    fn canonize(
        buf: &mut Vec<G>,
        start: usize,
        end: usize,
        get: impl Fn(usize) -> G,
        find: impl Fn(G) -> G,
        _mode: MSetClamp,
    ) {
        for i in start..end {
            buf.push(find(get(i)));
        }
    }
}

/// AC: apply find to G component, sort by G, merge duplicate G's by summing multiplicities, then
/// apply the op's count clamp. The two named steps — [`update_multiset`](Self::update_multiset)
/// (raw representation: find+sort+coalesce, ℕ counts) and [`clamp_multiset`](Self::clamp_multiset)
/// (the algebraic clamp) — are sequenced by `canonize`, so its output is always the canonical form.
pub struct MSetCanon;

impl MSetCanon {
    /// Raw multiset maintenance: find each child, sort by class id, coalesce duplicates by summing
    /// multiplicities. Produces a sorted, duplicate-free multiset with ℕ counts — the
    /// representation, before any algebraic clamp.
    pub fn update_multiset<G: DenseId + Ord>(
        buf: &mut Vec<(G, crate::multiplicity::Multiplicity)>,
        start: usize,
        end: usize,
        get: impl Fn(usize) -> (G, crate::multiplicity::Multiplicity),
        find: impl Fn(G) -> G,
    ) {
        use crate::multiplicity::Multiplicity;
        for i in start..end {
            let (g, m) = get(i);
            buf.push((find(g), m));
        }
        buf.sort_by_key(|a| a.0);
        // merge adjacent duplicates
        let mut w = 0;
        for r in 1..buf.len() {
            if buf[r].0 == buf[w].0 {
                buf[w].1 = Multiplicity(buf[w].1.0 + buf[r].1.0);
            } else {
                w += 1;
                buf[w] = buf[r];
            }
        }
        if !buf.is_empty() {
            buf.truncate(w + 1);
        }
    }

    /// Apply the op's count clamp to an already-`update_multiset`'d buffer, in place. `None` is a
    /// no-op (plain AC). `Nilpotent { order: n }` reduces each count mod `n` and drops the summands
    /// that vanish, so `xor(a,a)` (`{a:2}`) becomes `{}`. Preserves sort order (`retain`), so the
    /// result stays canonical.
    pub fn clamp_multiset<G: DenseId>(
        buf: &mut Vec<(G, crate::multiplicity::Multiplicity)>,
        mode: MSetClamp,
    ) {
        use crate::multiplicity::Multiplicity;
        if let MSetClamp::Nilpotent { order } = mode {
            let n = order as u32;
            for p in buf.iter_mut() {
                p.1 = Multiplicity(p.1.0 % n);
            }
            buf.retain(|p| p.1.0 != 0);
        }
    }
}

impl<G: DenseId + Ord> VarCanon<G, (G, crate::multiplicity::Multiplicity)> for MSetCanon {
    fn canonize(
        buf: &mut Vec<(G, crate::multiplicity::Multiplicity)>,
        start: usize,
        end: usize,
        get: impl Fn(usize) -> (G, crate::multiplicity::Multiplicity),
        find: impl Fn(G) -> G,
        mode: MSetClamp,
    ) {
        Self::update_multiset(buf, start, end, get, find);
        Self::clamp_multiset(buf, mode);
    }
}

/// ACI: apply find, sort, dedup. The `dedup` *is* the idempotent clamp, baked into canonize (no
/// separate mode) — the precedent for keeping a clamp inside canonize rather than after it.
/// `mode` is ignored (idempotence is structural here, not a count clamp).
pub struct SetCanon;

impl<G: DenseId + Ord> VarCanon<G, G> for SetCanon {
    fn canonize(
        buf: &mut Vec<G>,
        start: usize,
        end: usize,
        get: impl Fn(usize) -> G,
        find: impl Fn(G) -> G,
        _mode: MSetClamp,
    ) {
        for i in start..end {
            buf.push(find(get(i)));
        }
        buf.sort();
        buf.dedup();
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::id::ENodeId;
    use crate::multiplicity::Multiplicity;

    fn id(n: u32) -> ENodeId {
        ENodeId::new(n)
    }

    #[test]
    fn plain_canon_preserves_order() {
        let mut ch = [id(2), id(4), id(6)];
        // find: even → half
        PlainCanon::canonize(&mut ch, |g| ENodeId::new(g.raw() / 2));
        assert_eq!(ch, [id(1), id(2), id(3)]);
    }

    #[test]
    fn c_canon_sorts() {
        let mut ch = [id(5), id(2)];
        CCanon::canonize(&mut ch, |g| g);
        assert_eq!(ch, [id(2), id(5)]);
    }

    #[test]
    fn c_canon_find_then_sort() {
        // find maps 10→1, 20→2
        let mut ch = [id(20), id(10)];
        CCanon::canonize(&mut ch, |g| ENodeId::new(g.raw() / 10));
        assert_eq!(ch, [id(1), id(2)]);
    }

    #[test]
    fn mset_canon_merges() {
        let pool = [
            (id(3), Multiplicity(1)),
            (id(1), Multiplicity(2)),
            (id(3), Multiplicity(1)),
        ];
        let mut buf = Vec::new();
        MSetCanon::canonize(&mut buf, 0, 3, |i| pool[i], |g| g, MSetClamp::None);
        assert_eq!(
            buf,
            vec![(id(1), Multiplicity(2)), (id(3), Multiplicity(2))]
        );
    }

    #[test]
    fn mset_canon_nilpotent_clamps_mod_order() {
        // xor(a,a) → {a:2} → {} at order 2; xor(a,a,a,b) → {a:3,b:1} → {a:1,b:1}.
        let pool = [
            (id(1), Multiplicity(1)),
            (id(1), Multiplicity(1)),
            (id(1), Multiplicity(1)),
            (id(2), Multiplicity(1)),
        ];
        let mut buf = Vec::new();
        MSetCanon::canonize(
            &mut buf,
            0,
            4,
            |i| pool[i],
            |g| g,
            MSetClamp::Nilpotent { order: 2 },
        );
        assert_eq!(
            buf,
            vec![(id(1), Multiplicity(1)), (id(2), Multiplicity(1))]
        );
        // A fully-even monomial empties to {}.
        let even = [(id(1), Multiplicity(1)), (id(1), Multiplicity(1))];
        let mut b2 = Vec::new();
        MSetCanon::canonize(
            &mut b2,
            0,
            2,
            |i| even[i],
            |g| g,
            MSetClamp::Nilpotent { order: 2 },
        );
        assert!(b2.is_empty());
    }

    #[test]
    fn mset_canon_find_and_merge() {
        // find: 2→1, 3→1, 4→4
        let pool = [
            (id(2), Multiplicity(1)),
            (id(3), Multiplicity(1)),
            (id(4), Multiplicity(1)),
        ];
        let mut buf = Vec::new();
        MSetCanon::canonize(
            &mut buf,
            0,
            3,
            |i| pool[i],
            |g| {
                if g.raw() <= 3 { id(1) } else { g }
            },
            MSetClamp::None,
        );
        assert_eq!(
            buf,
            vec![(id(1), Multiplicity(2)), (id(4), Multiplicity(1))]
        );
    }

    #[test]
    fn aci_canon_dedup() {
        let pool = [id(3), id(1), id(3), id(2), id(1)];
        let mut buf = Vec::new();
        SetCanon::canonize(&mut buf, 0, 5, |i| pool[i], |g| g, MSetClamp::None);
        assert_eq!(buf, vec![id(1), id(2), id(3)]);
    }

    #[test]
    fn aci_canon_find_and_dedup() {
        // find: 2→1, 3→1
        let pool = [id(1), id(2), id(3)];
        let mut buf = Vec::new();
        SetCanon::canonize(
            &mut buf,
            0,
            3,
            |i| pool[i],
            |g| {
                if g.raw() <= 3 { id(1) } else { g }
            },
            MSetClamp::None,
        );
        assert_eq!(buf, vec![id(1)]);
    }
}
