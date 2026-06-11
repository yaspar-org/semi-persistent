// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Leapfrog triejoin — intersect N sorted iterators.
//!
//! Implements the unary leapfrog join from:
//! Veldhuizen, "Leapfrog Triejoin: A Simple, Worst-Case Optimal Join Algorithm" (ICDT 2014)

use crate::containers::DenseId;
use crate::index::SortedVecCursor;
pub use semi_persistent_containers::SortedCursor;

impl<'a, G: DenseId> SortedCursor for SortedVecCursor<'a, G> {
    type Key = G;
    #[inline]
    fn key(&self) -> Option<G> {
        if SortedVecCursor::is_valid(self) {
            Some(SortedVecCursor::key(self))
        } else {
            None
        }
    }
    #[inline]
    fn step(&mut self) {
        SortedVecCursor::step(self);
    }
    #[inline]
    fn seek(&mut self, target: G) {
        SortedVecCursor::seek(self, target);
    }
}

/// Cursor combinator yielding `full ∖ delta`: every key from `full` that is
/// absent from `delta`. Generic over any two `SortedCursor`s with the same
/// key type — works for `SortedVecCursor`, `BPlusCursor`, or nested
/// combinators, with no coupling to a backend. Itself a `SortedCursor`, so
/// leapfrog consumes it like any other cursor.
///
/// Used by semi-naive evaluation to restrict an atom to "old" nodes
/// (`full ∖ delta`) without materialising a third index.
///
/// Invariant: after construction and after every `step`/`seek`, the `full`
/// sub-cursor points at a non-excluded key or is exhausted, so `key()` just
/// reads `full`. Relies on leapfrog's monotonic-forward seeks — the `delta`
/// sub-cursor only ever advances, never rewinds. Cost is `O(|full|+|delta|)`
/// across a full scan.
pub struct Difference<A, B> {
    full: A,
    delta: B,
}

impl<K, A, B> Difference<A, B>
where
    K: Copy + Ord,
    A: SortedCursor<Key = K>,
    B: SortedCursor<Key = K>,
{
    /// Wrap `full` and `delta`, establishing the skip invariant.
    pub fn new(full: A, delta: B) -> Self {
        let mut d = Self { full, delta };
        d.skip();
        d
    }

    /// Advance `full` past any key currently present in `delta`.
    #[inline]
    fn skip(&mut self) {
        while let Some(k) = self.full.key() {
            self.delta.seek(k);
            if self.delta.key() == Some(k) {
                self.full.step();
            } else {
                break;
            }
        }
    }
}

impl<K, A, B> SortedCursor for Difference<A, B>
where
    K: Copy + Ord,
    A: SortedCursor<Key = K>,
    B: SortedCursor<Key = K>,
{
    type Key = K;
    #[inline]
    fn key(&self) -> Option<K> {
        self.full.key()
    }
    #[inline]
    fn step(&mut self) {
        self.full.step();
        self.skip();
    }
    #[inline]
    fn seek(&mut self, target: K) {
        self.full.seek(target);
        self.delta.seek(target);
        self.skip();
    }
}

/// Leapfrog join over k sorted iterators.
///
/// Maintains a ring of cursors. `p` is the index of the iterator at the
/// minimum key; `(p + k - 1) % k` is the index at the maximum key.
/// After `search()`, either all iterators point to the same key (a match)
/// or some iterator is exhausted.
pub struct LeapfrogJoin<C: SortedCursor> {
    iters: Vec<C>,
    p: usize,
    at_end: bool,
}

impl<C: SortedCursor> LeapfrogJoin<C> {
    /// leapfrog-init (Algorithm 1 in the paper).
    pub fn new(iters: Vec<C>) -> Self {
        assert!(!iters.is_empty());
        // Fetch each cursor's current key. If any is exhausted, the join is empty.
        let keys: Option<Vec<C::Key>> = iters.iter().map(|it| it.key()).collect();
        let Some(keys) = keys else {
            return Self {
                iters,
                p: 0,
                at_end: true,
            };
        };
        // Sort iters by current key.
        let mut with_keys: Vec<(C::Key, C)> = keys.into_iter().zip(iters).collect();
        with_keys.sort_by_key(|(k, _)| *k);
        let iters: Vec<C> = with_keys.into_iter().map(|(_, it)| it).collect();

        let mut join = Self {
            iters,
            p: 0,
            at_end: false,
        };
        join.search();
        join
    }

    #[inline]
    pub fn is_valid(&self) -> bool {
        !self.at_end
    }

    #[inline]
    pub fn key(&self) -> C::Key {
        self.iters[self.p]
            .key()
            .expect("leapfrog: key on invalid cursor")
    }

    /// leapfrog-next (Algorithm 3).
    pub fn next(&mut self) {
        self.iters[self.p].step();
        if self.iters[self.p].key().is_none() {
            self.at_end = true;
            return;
        }
        self.p = (self.p + 1) % self.iters.len();
        self.search();
    }

    /// leapfrog-search (Algorithm 2).
    fn search(&mut self) {
        let k = self.iters.len();
        let mut max_key = self.iters[(self.p + k - 1) % k]
            .key()
            .expect("leapfrog: invariant broken");
        loop {
            let min_key = self.iters[self.p]
                .key()
                .expect("leapfrog: invariant broken");
            if min_key == max_key {
                return;
            }
            self.iters[self.p].seek(max_key);
            match self.iters[self.p].key() {
                Some(k) => max_key = k,
                None => {
                    self.at_end = true;
                    return;
                }
            }
            self.p = (self.p + 1) % k;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::index::SortedVec;

    fn svec<G: DenseId>(vals: &[usize]) -> SortedVec<G> {
        SortedVec {
            data: vals.iter().map(|&v| G::from_usize(v)).collect(),
        }
    }

    fn collect<'a, G: DenseId>(j: &mut LeapfrogJoin<SortedVecCursor<'a, G>>) -> Vec<usize> {
        let mut out = Vec::new();
        while j.is_valid() {
            out.push(j.key().to_usize());
            j.next();
        }
        out
    }

    macro_rules! dual {
        ($(fn $name:ident<$G:ident>() $body:block)*) => {$(
            mod $name {
                use super::*;
                fn run<$G: DenseId>() $body
                #[test] fn bits31() { run::<crate::id::ENodeId>(); }
                #[test] fn bits63() { run::<crate::nodes::ENodeId64>(); }
            }
        )*};
    }

    dual! {
        fn single<G>() {
            let s = svec::<G>(&[1, 3, 5, 7]);
            let mut j = LeapfrogJoin::new(vec![s.iter()]);
            assert_eq!(collect(&mut j), [1, 3, 5, 7]);
        }

        fn two_way<G>() {
            let a = svec::<G>(&[1, 2, 3, 5, 8]);
            let b = svec::<G>(&[2, 3, 6, 8, 9]);
            let mut j = LeapfrogJoin::new(vec![a.iter(), b.iter()]);
            assert_eq!(collect(&mut j), [2, 3, 8]);
        }

        fn three_way<G>() {
            let a = svec::<G>(&[1, 2, 3, 5, 8, 10]);
            let b = svec::<G>(&[2, 3, 6, 8, 9, 10]);
            let c = svec::<G>(&[0, 3, 4, 8, 10, 11]);
            let mut j = LeapfrogJoin::new(vec![a.iter(), b.iter(), c.iter()]);
            assert_eq!(collect(&mut j), [3, 8, 10]);
        }

        fn disjoint<G>() {
            let a = svec::<G>(&[1, 3, 5]);
            let b = svec::<G>(&[2, 4, 6]);
            let mut j = LeapfrogJoin::new(vec![a.iter(), b.iter()]);
            assert_eq!(collect(&mut j), Vec::<usize>::new());
        }

        fn all_same<G>() {
            let a = svec::<G>(&[5]);
            let b = svec::<G>(&[5]);
            let c = svec::<G>(&[5]);
            let mut j = LeapfrogJoin::new(vec![a.iter(), b.iter(), c.iter()]);
            assert_eq!(collect(&mut j), [5]);
        }

        fn one_empty<G>() {
            let a = svec::<G>(&[1, 2, 3]);
            let b = svec::<G>(&[]);
            let mut j = LeapfrogJoin::new(vec![a.iter(), b.iter()]);
            assert_eq!(collect(&mut j), Vec::<usize>::new());
        }

        fn large_sparse<G>() {
            let av: Vec<usize> = (0..1000).step_by(3).collect();
            let bv: Vec<usize> = (0..1000).step_by(7).collect();
            let a = svec::<G>(&av);
            let b = svec::<G>(&bv);
            let mut j = LeapfrogJoin::new(vec![a.iter(), b.iter()]);
            let expected: Vec<usize> = (0..1000).filter(|x| x % 3 == 0 && x % 7 == 0).collect();
            assert_eq!(collect(&mut j), expected);
        }

        fn five_way<G>() {
            let a = svec::<G>(&[1, 2, 3, 5, 7, 10, 15, 20]);
            let b = svec::<G>(&[2, 3, 5, 10, 15, 20, 25]);
            let c = svec::<G>(&[3, 5, 10, 15, 30]);
            let d = svec::<G>(&[5, 10, 15, 20, 30, 40]);
            let e = svec::<G>(&[0, 5, 10, 15, 50]);
            let mut j = LeapfrogJoin::new(vec![a.iter(), b.iter(), c.iter(), d.iter(), e.iter()]);
            assert_eq!(collect(&mut j), [5, 10, 15]);
        }

        fn all_empty<G>() {
            let a = svec::<G>(&[]);
            let b = svec::<G>(&[]);
            let c = svec::<G>(&[]);
            let mut j = LeapfrogJoin::new(vec![a.iter(), b.iter(), c.iter()]);
            assert_eq!(collect(&mut j), Vec::<usize>::new());
        }

        fn large_overlap<G>() {
            // Two sets sharing 90% of elements
            let av: Vec<usize> = (0..1000).collect();
            let bv: Vec<usize> = (0..900).chain(1000..1100).collect();
            let a = svec::<G>(&av);
            let b = svec::<G>(&bv);
            let mut j = LeapfrogJoin::new(vec![a.iter(), b.iter()]);
            let expected: Vec<usize> = (0..900).collect();
            assert_eq!(collect(&mut j), expected);
        }

        fn needle_in_haystack<G>() {
            // One element in common across three large sets
            let av: Vec<usize> = (0..10000).step_by(2).collect();       // evens
            let bv: Vec<usize> = (0..10000).step_by(3).collect();       // mult of 3
            let cv: Vec<usize> = (0..10000).step_by(5000).collect();    // [0, 5000]
            let a = svec::<G>(&av);
            let b = svec::<G>(&bv);
            let c = svec::<G>(&cv);
            let mut j = LeapfrogJoin::new(vec![a.iter(), b.iter(), c.iter()]);
            // 0 is in all three; 5000 is even and not mult of 3
            assert_eq!(collect(&mut j), [0]);
        }

        fn adjacent_miss<G>() {
            // Evens vs odds — no intersection
            let av: Vec<usize> = (0..10000).step_by(2).collect();
            let bv: Vec<usize> = (1..10000).step_by(2).collect();
            let a = svec::<G>(&av);
            let b = svec::<G>(&bv);
            let mut j = LeapfrogJoin::new(vec![a.iter(), b.iter()]);
            assert_eq!(collect(&mut j), Vec::<usize>::new());
        }

        fn asymmetric_sizes<G>() {
            // Tiny set vs huge set
            let small = svec::<G>(&[500, 5000, 50000]);
            let bigv: Vec<usize> = (0..100000).collect();
            let big = svec::<G>(&bigv);
            let mut j = LeapfrogJoin::new(vec![small.iter(), big.iter()]);
            assert_eq!(collect(&mut j), [500, 5000, 50000]);
        }

        fn identical_sets<G>() {
            // Four copies of the same set — intersection is the full set
            let v: Vec<usize> = (0..500).collect();
            let a = svec::<G>(&v);
            let b = svec::<G>(&v);
            let c = svec::<G>(&v);
            let d = svec::<G>(&v);
            let mut j = LeapfrogJoin::new(vec![a.iter(), b.iter(), c.iter(), d.iter()]);
            assert_eq!(collect(&mut j), v);
        }

        fn million_two_way<G>() {
            let av: Vec<usize> = (0..1_000_000).step_by(2).collect();
            let bv: Vec<usize> = (0..1_000_000).step_by(3).collect();
            let a = svec::<G>(&av);
            let b = svec::<G>(&bv);
            let mut j = LeapfrogJoin::new(vec![a.iter(), b.iter()]);
            let result = collect(&mut j);
            let expected: Vec<usize> = (0..1_000_000).step_by(6).collect();
            assert_eq!(result, expected);
        }

        fn million_three_way_sparse<G>() {
            // Multiples of 97, 101, 103 — very sparse intersection
            let av: Vec<usize> = (0..2_000_000).step_by(97).collect();
            let bv: Vec<usize> = (0..2_000_000).step_by(101).collect();
            let cv: Vec<usize> = (0..2_000_000).step_by(103).collect();
            let a = svec::<G>(&av);
            let b = svec::<G>(&bv);
            let c = svec::<G>(&cv);
            let mut j = LeapfrogJoin::new(vec![a.iter(), b.iter(), c.iter()]);
            let result = collect(&mut j);
            let lcm = 97 * 101 * 103; // 1_009_691
            let expected: Vec<usize> = (0..2_000_000).step_by(lcm).collect();
            assert_eq!(result, expected);
        }
    }

    // -- A4: Difference combinator (full ∖ delta) tests --
    mod difference {
        use super::*;
        use crate::id::ENodeId;
        use proptest::prelude::*;

        /// Iterate a `Difference` by `step` and collect the keys.
        fn diff_step(full: &[usize], delta: &[usize]) -> Vec<usize> {
            let fv = svec::<ENodeId>(full);
            let dv = svec::<ENodeId>(delta);
            let mut d = Difference::new(fv.iter(), dv.iter());
            let mut out = Vec::new();
            while let Some(k) = d.key() {
                out.push(k.to_usize());
                d.step();
            }
            out
        }

        #[test]
        fn basic_step() {
            assert_eq!(diff_step(&[1, 2, 3, 4, 5], &[2, 4]), vec![1, 3, 5]);
        }

        #[test]
        fn empty_delta_is_identity() {
            assert_eq!(diff_step(&[1, 2, 3], &[]), vec![1, 2, 3]);
        }

        #[test]
        fn delta_covers_all() {
            assert_eq!(diff_step(&[1, 2, 3], &[1, 2, 3]), Vec::<usize>::new());
        }

        #[test]
        fn delta_outside_full_ignored() {
            // delta entries not in full simply match nothing.
            assert_eq!(diff_step(&[1, 3, 5], &[2, 4, 6]), vec![1, 3, 5]);
        }

        #[test]
        fn basic_seek() {
            // For every target, seek lands on the first key ≥ target in [1,3,5].
            let fv = svec::<ENodeId>(&[1, 2, 3, 4, 5]);
            let dv = svec::<ENodeId>(&[2, 4]);
            let present = [1usize, 3, 5];
            for t in 0..7usize {
                let mut d = Difference::new(fv.iter(), dv.iter());
                d.seek(ENodeId::from_usize(t));
                let got = d.key().map(|k| k.to_usize());
                let exp = present.iter().copied().find(|&x| x >= t);
                assert_eq!(got, exp, "seek({t})");
            }
        }

        fn sorted_unique() -> impl Strategy<Value = Vec<usize>> {
            proptest::collection::vec(0usize..60, 0..30).prop_map(|mut v| {
                v.sort_unstable();
                v.dedup();
                v
            })
        }

        proptest! {
            #![proptest_config(ProptestConfig::with_cases(2000))]

            /// `Difference` by step == `full.filter(|x| !delta.contains(x))`,
            /// for arbitrary sorted-unique full and delta (delta need not be
            /// a subset of full).
            #[test]
            fn matches_filter(full in sorted_unique(), delta in sorted_unique()) {
                let got = diff_step(&full, &delta);
                let expected: Vec<usize> =
                    full.iter().copied().filter(|x| !delta.contains(x)).collect();
                prop_assert_eq!(got, expected);
            }

            /// Seek to every possible target and confirm it lands on the first
            /// non-excluded key ≥ target.
            #[test]
            fn seek_matches_filter(full in sorted_unique(), delta in sorted_unique()) {
                let present: Vec<usize> =
                    full.iter().copied().filter(|x| !delta.contains(x)).collect();
                let fv = svec::<ENodeId>(&full);
                let dv = svec::<ENodeId>(&delta);
                for t in 0..62usize {
                    let mut d = Difference::new(fv.iter(), dv.iter());
                    d.seek(ENodeId::from_usize(t));
                    let got = d.key().map(|k| k.to_usize());
                    let exp = present.iter().copied().find(|&x| x >= t);
                    prop_assert_eq!(got, exp, "seek({})", t);
                }
            }
        }
    }
}
