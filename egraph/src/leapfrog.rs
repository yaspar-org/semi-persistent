// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Leapfrog triejoin — intersect N sorted iterators.
//!
//! Implements the unary leapfrog join from:
//! Veldhuizen, "Leapfrog Triejoin: A Simple, Worst-Case Optimal Join Algorithm" (ICDT 2014)

use crate::containers::DenseId;
use crate::index::SortedVecIter;

/// Leapfrog join over k sorted iterators.
///
/// Maintains a ring of cursors. `p` is the index of the iterator at the
/// minimum key; `(p + k - 1) % k` is the index at the maximum key.
/// After `search()`, either all iterators point to the same key (a match)
/// or some iterator is exhausted.
pub struct LeapfrogJoin<'a, G: DenseId> {
    iters: Vec<SortedVecIter<'a, G>>,
    p: usize,
    at_end: bool,
}

impl<'a, G: DenseId> LeapfrogJoin<'a, G> {
    /// leapfrog-init (Algorithm 1 in the paper).
    pub fn new(mut iters: Vec<SortedVecIter<'a, G>>) -> Self {
        assert!(!iters.is_empty());
        if iters.iter().any(|it| !it.is_valid()) {
            return Self {
                iters,
                p: 0,
                at_end: true,
            };
        }
        iters.sort_by_key(|it| it.key().to_usize());
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
    pub fn key(&self) -> G {
        self.iters[self.p].key()
    }

    /// leapfrog-next (Algorithm 3).
    pub fn next(&mut self) {
        self.iters[self.p].step();
        if !self.iters[self.p].is_valid() {
            self.at_end = true;
            return;
        }
        self.p = (self.p + 1) % self.iters.len();
        self.search();
    }

    /// leapfrog-search (Algorithm 2).
    fn search(&mut self) {
        let k = self.iters.len();
        // x' = max key = Iter[(p-1) mod k].key()
        let mut max_key = self.iters[(self.p + k - 1) % k].key();
        loop {
            let min_key = self.iters[self.p].key();
            if min_key == max_key {
                return; // all iterators agree
            }
            self.iters[self.p].seek(max_key);
            if !self.iters[self.p].is_valid() {
                self.at_end = true;
                return;
            }
            max_key = self.iters[self.p].key();
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

    fn collect<G: DenseId>(j: &mut LeapfrogJoin<G>) -> Vec<usize> {
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
}
