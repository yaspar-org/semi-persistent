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

/// Canonize variable-arity children via destination-passing.
///
/// Reads `end - start` elements from pool via `get`, applies `find` to the
/// G component, canonizes (sort/dedup/merge), writes result into `buf`.
/// `buf` must be cleared by caller before each call.
/// Returns nothing — caller reads `buf.len()` for the new span length.
pub trait VarCanon<G: DenseId, C> {
    fn canonize(
        buf: &mut Vec<C>,
        start: usize,
        end: usize,
        get: impl Fn(usize) -> C,
        find: impl Fn(G) -> G,
    );
}

/// Ordered: apply find, preserve order. (PlainN, A)
pub struct OrderedCanon;

impl<G: DenseId> VarCanon<G, G> for OrderedCanon {
    #[inline]
    fn canonize(
        buf: &mut Vec<G>,
        start: usize,
        end: usize,
        get: impl Fn(usize) -> G,
        find: impl Fn(G) -> G,
    ) {
        for i in start..end {
            buf.push(find(get(i)));
        }
    }
}

/// AC: apply find to G component, sort by G, merge duplicate G's by summing multiplicities.
pub struct ACCanon;

impl<G: DenseId + Ord> VarCanon<G, (G, crate::multiplicity::Multiplicity)> for ACCanon {
    fn canonize(
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
}

/// ACI: apply find, sort, dedup.
pub struct ACICanon;

impl<G: DenseId + Ord> VarCanon<G, G> for ACICanon {
    fn canonize(
        buf: &mut Vec<G>,
        start: usize,
        end: usize,
        get: impl Fn(usize) -> G,
        find: impl Fn(G) -> G,
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
    fn ac_canon_merges() {
        let pool = [
            (id(3), Multiplicity(1)),
            (id(1), Multiplicity(2)),
            (id(3), Multiplicity(1)),
        ];
        let mut buf = Vec::new();
        ACCanon::canonize(&mut buf, 0, 3, |i| pool[i], |g| g);
        assert_eq!(
            buf,
            vec![(id(1), Multiplicity(2)), (id(3), Multiplicity(2))]
        );
    }

    #[test]
    fn ac_canon_find_and_merge() {
        // find: 2→1, 3→1, 4→4
        let pool = [
            (id(2), Multiplicity(1)),
            (id(3), Multiplicity(1)),
            (id(4), Multiplicity(1)),
        ];
        let mut buf = Vec::new();
        ACCanon::canonize(
            &mut buf,
            0,
            3,
            |i| pool[i],
            |g| {
                if g.raw() <= 3 { id(1) } else { g }
            },
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
        ACICanon::canonize(&mut buf, 0, 5, |i| pool[i], |g| g);
        assert_eq!(buf, vec![id(1), id(2), id(3)]);
    }

    #[test]
    fn aci_canon_find_and_dedup() {
        // find: 2→1, 3→1
        let pool = [id(1), id(2), id(3)];
        let mut buf = Vec::new();
        ACICanon::canonize(
            &mut buf,
            0,
            3,
            |i| pool[i],
            |g| {
                if g.raw() <= 3 { id(1) } else { g }
            },
        );
        assert_eq!(buf, vec![id(1)]);
    }
}
