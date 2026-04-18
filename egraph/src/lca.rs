// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Batch LCA queries on the proof forest via Bender–Farach-Colton.
//!
//! Two implementations:
//! - [`LcaTable`]: stores full absolute depths. Simpler, faster queries.
//! - [`LcaTableCompact`]: stores `i8` deltas + block-start depths. ~4× less
//!   memory for the depth array, queries do a short prefix sum (~16 adds).
//!
//! Both use O(n) preprocessing and O(1) queries. Both handle forests by
//! introducing a virtual root that parents all actual roots, preserving
//! the ±1 depth property across the entire Euler tour.
//!
//! # Staleness
//!
//! The table is a snapshot of the proof forest at build time. Any subsequent
//! `union_justified` / `rebuild` calls invalidate it — the caller must
//! rebuild the table after mutations. This is not enforced by the type system.

use crate::containers::dense_id::DenseId;

// ---------------------------------------------------------------------------
// Shared helpers
// ---------------------------------------------------------------------------

/// Virtual-root Euler tour from a proof-parent array.
/// Returns `(euler, depth, first, tree_id)`.
/// `euler` and `depth` have length 2*(n+1)-1 (virtual root included).
/// `first` and `tree_id` have length n+1 (index n = virtual root).
///
/// Depths are stored as `u16`. This is safe because proof tree depth is
/// bounded by the number of union operations (at most n), and with
/// union-by-rank the depth is O(log n). Even without rank optimization,
/// depths in practice stay well below 65535. A debug assertion checks this.
fn euler_tour<T: DenseId, const TRACK: bool>(
    pp: &crate::containers::VecI<T, T::Index, TRACK>,
    n: usize,
) -> (Vec<T>, Vec<u16>, Vec<u32>, Vec<u32>) {
    let vroot = n;
    let mut children: Vec<Vec<usize>> = vec![Vec::new(); n + 1];
    let mut roots = Vec::new();
    for i in 0..n {
        let p = pp.get(T::from_usize(i)).to_usize();
        if p == i {
            roots.push(i);
            children[vroot].push(i);
        } else {
            children[p].push(i);
        }
    }

    let cap = 2 * (n + 1);
    let mut euler = Vec::with_capacity(cap);
    let mut depth: Vec<u16> = Vec::with_capacity(cap);
    let mut first = vec![u32::MAX; n + 1];
    let mut tree_id = vec![0u32; n + 1];

    // Single DFS from virtual root
    // Stack: (node, child_index, depth)
    let mut stack: Vec<(usize, usize, u16)> = Vec::new();
    stack.push((vroot, 0, 0));
    euler.push(T::from_usize(0)); // placeholder for vroot
    depth.push(0);
    first[vroot] = 0;

    let mut current_tree: u32 = 0;

    while let Some((node, ci, d)) = stack.last_mut() {
        if *ci < children[*node].len() {
            let child = children[*node][*ci];
            *ci += 1;
            let child_depth = d.checked_add(1).expect(
                "proof tree depth exceeds u16::MAX (65535); this should never happen \
                 with union-by-rank (max depth = log₂(n) ≈ 31)",
            );
            euler.push(T::from_usize(child.min(n.saturating_sub(1))));
            depth.push(child_depth);
            if first[child] == u32::MAX {
                first[child] =
                    u32::try_from(euler.len() - 1).expect("Euler tour length exceeds u32::MAX");
            }
            if *node == vroot {
                current_tree = roots.iter().position(|&r| r == child).unwrap_or(0) as u32;
            }
            if child < n {
                tree_id[child] = current_tree;
            }
            stack.push((child, 0, child_depth));
        } else {
            stack.pop();
            if let Some(&(parent, _, pd)) = stack.last() {
                let id = if parent < n { parent } else { 0 };
                euler.push(T::from_usize(id));
                depth.push(pd);
            }
        }
    }

    (euler, depth, first, tree_id)
}

/// Block decomposition shared state.
struct BlockDecomp {
    block_size: usize,
    num_blocks: usize,
    /// Tour position of the minimum-depth entry in each block.
    block_min: Vec<u32>,
    /// ±1 pattern for each block.
    block_type: Vec<u16>,
}

fn block_decompose(depth: &[u16], m: usize) -> BlockDecomp {
    let block_size = ((usize::BITS - m.leading_zeros()) as usize / 2).max(1);
    let num_blocks = m.div_ceil(block_size);

    let mut block_min = vec![0u32; num_blocks];
    let mut block_type = vec![0u16; num_blocks];

    for b in 0..num_blocks {
        let start = b * block_size;
        let end = (start + block_size).min(m);
        let mut min_idx = start;
        let mut min_depth = depth[start];
        let mut pattern: u16 = 0;
        for i in start..end {
            if depth[i] < min_depth {
                min_depth = depth[i];
                min_idx = i;
            }
            if i > start && depth[i] > depth[i - 1] {
                pattern |= 1 << (i - start - 1);
            }
        }
        block_min[b] = u32::try_from(min_idx).expect("Euler tour length exceeds u32::MAX");
        block_type[b] = pattern;
    }

    BlockDecomp {
        block_size,
        num_blocks,
        block_min,
        block_type,
    }
}

fn build_sparse_table(depth: &[u16], bd: &BlockDecomp) -> Vec<Vec<u32>> {
    let num_blocks = bd.num_blocks;
    let log_blocks = if num_blocks > 1 {
        (usize::BITS - (num_blocks - 1).leading_zeros()) as usize
    } else {
        1
    };
    let mut sparse: Vec<Vec<u32>> = Vec::with_capacity(log_blocks);
    sparse.push(bd.block_min.clone());

    for k in 1..log_blocks {
        let prev = &sparse[k - 1];
        let half = 1 << (k - 1);
        let len = num_blocks.saturating_sub(1 << k) + 1;
        let mut level = Vec::with_capacity(len);
        for i in 0..len {
            let left = prev[i];
            let right = prev[i + half];
            level.push(if depth[left as usize] <= depth[right as usize] {
                left
            } else {
                right
            });
        }
        sparse.push(level);
    }
    sparse
}

fn build_block_lookup(depth: &[u16], bd: &BlockDecomp, m: usize) -> Vec<Vec<u16>> {
    let block_size = bd.block_size;
    let num_patterns = 1u16 << block_size.saturating_sub(1);
    let mut block_lookup: Vec<Vec<u16>> = vec![Vec::new(); num_patterns as usize];

    for b in 0..bd.num_blocks {
        let bt = bd.block_type[b] as usize;
        if !block_lookup[bt].is_empty() {
            continue;
        }
        let bs = block_size;
        let base = b * bs;
        let end = (base + bs).min(m);
        let mut table = vec![0u16; bs * bs];

        for i in 0..bs {
            table[i * bs + i] = i as u16;
            for j in (i + 1)..bs {
                let prev_min = table[i * bs + j - 1] as usize;
                table[i * bs + j] = if base + j < end && depth[base + j] < depth[base + prev_min] {
                    j as u16
                } else {
                    prev_min as u16
                };
            }
        }
        block_lookup[bt] = table;
    }
    block_lookup
}

// ---------------------------------------------------------------------------
// LcaTable — full depth array
// ---------------------------------------------------------------------------

/// Precomputed LCA structure with O(1) queries.
///
/// Depths are stored as `u16` (2 bytes each instead of 8). This is safe
/// because proof tree depth is bounded by the number of union operations,
/// and union-by-rank keeps depth O(log n) — at most 31 for 2³¹ nodes.
/// Even degenerate chains would need 65536 unions to overflow, which is
/// far beyond any practical proof tree. A debug assertion in `euler_tour`
/// checks this invariant.
pub struct LcaTable<T: DenseId> {
    euler: Vec<T>,
    depth: Vec<u16>,
    first: Vec<u32>,
    tree_id: Vec<u32>,
    n: usize,
    block_size: usize,
    sparse: Vec<Vec<u32>>,
    block_lookup: Vec<Vec<u16>>,
    block_type: Vec<u16>,
}

impl<T: DenseId> LcaTable<T> {
    pub fn build<const TRACK: bool>(
        pp: &crate::containers::VecI<T, T::Index, TRACK>,
        n: usize,
    ) -> Self {
        if n == 0 {
            return Self {
                euler: Vec::new(),
                depth: Vec::new(),
                first: Vec::new(),
                tree_id: Vec::new(),
                n: 0,
                block_size: 1,
                sparse: Vec::new(),
                block_lookup: Vec::new(),
                block_type: Vec::new(),
            };
        }

        let (euler, depth, first, tree_id) = euler_tour(pp, n);
        let m = euler.len();

        let bd = block_decompose(&depth, m);
        let sparse = build_sparse_table(&depth, &bd);
        let block_lookup = build_block_lookup(&depth, &bd, m);

        Self {
            euler,
            depth,
            first,
            tree_id,
            n,
            block_size: bd.block_size,
            sparse,
            block_lookup,
            block_type: bd.block_type,
        }
    }

    pub fn lca(&self, a: T, b: T) -> Option<T> {
        let ai = a.to_usize();
        let bi = b.to_usize();
        if ai >= self.n || bi >= self.n {
            return None;
        }
        let fa = self.first[ai];
        let fb = self.first[bi];
        if fa == u32::MAX || fb == u32::MAX {
            return None;
        }
        if self.tree_id[ai] != self.tree_id[bi] {
            return None;
        }
        let (i, j) = if fa <= fb {
            (fa as usize, fb as usize)
        } else {
            (fb as usize, fa as usize)
        };
        let idx = self.rmq(i, j);
        let result = self.euler[idx];
        // If the LCA is the virtual root, nodes are in different trees
        if result.to_usize() >= self.n {
            return None;
        }
        Some(result)
    }

    fn rmq(&self, i: usize, j: usize) -> usize {
        let bi = i / self.block_size;
        let bj = j / self.block_size;

        if bi == bj {
            return self.in_block_min(bi, i % self.block_size, j % self.block_size);
        }

        let left_min = self.in_block_min(bi, i % self.block_size, self.block_size - 1);
        let right_min = self.in_block_min(bj, 0, j % self.block_size);

        let mut best = if self.depth[left_min] <= self.depth[right_min] {
            left_min
        } else {
            right_min
        };

        if bi + 1 < bj {
            let mid_min = self.sparse_query(bi + 1, bj - 1);
            if self.depth[mid_min] < self.depth[best] {
                best = mid_min;
            }
        }

        best
    }

    fn sparse_query(&self, bl: usize, br: usize) -> usize {
        let len = br - bl + 1;
        let k = (usize::BITS - len.leading_zeros()) as usize - 1;
        let left = self.sparse[k][bl] as usize;
        let right = self.sparse[k][br - (1 << k) + 1] as usize;
        if self.depth[left] <= self.depth[right] {
            left
        } else {
            right
        }
    }

    fn in_block_min(&self, b: usize, i: usize, j: usize) -> usize {
        let bt = self.block_type[b] as usize;
        let table = &self.block_lookup[bt];
        let rel = table[i * self.block_size + j] as usize;
        b * self.block_size + rel
    }
}

// ---------------------------------------------------------------------------
// LcaTableCompact — delta-encoded depths
// ---------------------------------------------------------------------------

/// Precomputed LCA structure with delta-encoded depths.
/// Uses ~4× less memory for the depth representation. Queries do a
/// short prefix sum (~block_size ≈ 16 additions) to recover absolute
/// depths when comparing candidates.
pub struct LcaTableCompact<T: DenseId> {
    euler: Vec<T>,
    /// ±1 deltas between consecutive Euler tour depths. Length = tour_len - 1.
    delta: Vec<i8>,
    /// Absolute depth at the start of each block.
    block_depth: Vec<u16>,
    first: Vec<u32>,
    tree_id: Vec<u32>,
    n: usize,
    block_size: usize,
    /// Sparse table entries: (tour_position, absolute_depth).
    sparse: Vec<Vec<(u32, u16)>>,
    block_lookup: Vec<Vec<u16>>,
    block_type: Vec<u16>,
}

impl<T: DenseId> LcaTableCompact<T> {
    pub fn build<const TRACK: bool>(
        pp: &crate::containers::VecI<T, T::Index, TRACK>,
        n: usize,
    ) -> Self {
        if n == 0 {
            return Self {
                euler: Vec::new(),
                delta: Vec::new(),
                block_depth: Vec::new(),
                first: Vec::new(),
                tree_id: Vec::new(),
                n: 0,
                block_size: 1,
                sparse: Vec::new(),
                block_lookup: Vec::new(),
                block_type: Vec::new(),
            };
        }

        let (euler, depth, first, tree_id) = euler_tour(pp, n);
        let m = euler.len();

        // Build delta array
        let mut delta: Vec<i8> = Vec::with_capacity(m.saturating_sub(1));
        for i in 1..m {
            let d = depth[i] as i32 - depth[i - 1] as i32;
            debug_assert!(
                d == 1 || d == -1,
                "±1 property violated: delta={d} at position {i}"
            );
            delta.push(d as i8);
        }

        let bd = block_decompose(&depth, m);

        // Block-start absolute depths
        let mut block_depth = Vec::with_capacity(bd.num_blocks);
        for b in 0..bd.num_blocks {
            block_depth.push(depth[b * bd.block_size]);
        }

        // Sparse table storing (position, depth) pairs
        let sparse = {
            let num_blocks = bd.num_blocks;
            let log_blocks = if num_blocks > 1 {
                (usize::BITS - (num_blocks - 1).leading_zeros()) as usize
            } else {
                1
            };
            let mut sparse: Vec<Vec<(u32, u16)>> = Vec::with_capacity(log_blocks);
            // Level 0
            let level0: Vec<(u32, u16)> = bd
                .block_min
                .iter()
                .map(|&pos| (pos, depth[pos as usize]))
                .collect();
            sparse.push(level0);

            for k in 1..log_blocks {
                let prev = &sparse[k - 1];
                let half = 1 << (k - 1);
                let len = num_blocks.saturating_sub(1 << k) + 1;
                let mut level = Vec::with_capacity(len);
                for i in 0..len {
                    let left = prev[i];
                    let right = prev[i + half];
                    level.push(if left.1 <= right.1 { left } else { right });
                }
                sparse.push(level);
            }
            sparse
        };

        let block_lookup = build_block_lookup(&depth, &bd, m);

        Self {
            euler,
            delta,
            block_depth,
            first,
            tree_id,
            n,
            block_size: bd.block_size,
            sparse,
            block_lookup,
            block_type: bd.block_type,
        }
    }

    pub fn lca(&self, a: T, b: T) -> Option<T> {
        let ai = a.to_usize();
        let bi = b.to_usize();
        if ai >= self.n || bi >= self.n {
            return None;
        }
        let fa = self.first[ai];
        let fb = self.first[bi];
        if fa == u32::MAX || fb == u32::MAX {
            return None;
        }
        if self.tree_id[ai] != self.tree_id[bi] {
            return None;
        }
        let (i, j) = if fa <= fb {
            (fa as usize, fb as usize)
        } else {
            (fb as usize, fa as usize)
        };
        let idx = self.rmq(i, j);
        let result = self.euler[idx];
        if result.to_usize() >= self.n {
            return None;
        }
        Some(result)
    }

    /// Recover absolute depth at tour position `pos` from block-start depth + prefix sum.
    fn depth_at(&self, pos: usize) -> u16 {
        let b = pos / self.block_size;
        let offset = pos % self.block_size;
        let base = self.block_depth[b] as i32;
        let block_start = b * self.block_size;
        let mut d = base;
        // offset ≤ block_size ≈ 16, so this is at most 16 additions
        for i in block_start..block_start + offset {
            d += self.delta[i] as i32;
        }
        debug_assert!(d >= 0, "negative depth in prefix sum at position {pos}");
        d as u16
    }

    fn rmq(&self, i: usize, j: usize) -> usize {
        let bi = i / self.block_size;
        let bj = j / self.block_size;

        if bi == bj {
            return self.in_block_min(bi, i % self.block_size, j % self.block_size);
        }

        let left_pos = self.in_block_min(bi, i % self.block_size, self.block_size - 1);
        let right_pos = self.in_block_min(bj, 0, j % self.block_size);
        let left_d = self.depth_at(left_pos);
        let right_d = self.depth_at(right_pos);

        let (mut best, mut best_d) = if left_d <= right_d {
            (left_pos, left_d)
        } else {
            (right_pos, right_d)
        };

        if bi + 1 < bj {
            let (mid_pos, mid_d) = self.sparse_query(bi + 1, bj - 1);
            if mid_d < best_d {
                best = mid_pos;
                best_d = mid_d;
            }
        }

        let _ = best_d;
        best
    }

    fn sparse_query(&self, bl: usize, br: usize) -> (usize, u16) {
        let len = br - bl + 1;
        let k = (usize::BITS - len.leading_zeros()) as usize - 1;
        let left = self.sparse[k][bl];
        let right = self.sparse[k][br - (1 << k) + 1];
        if left.1 <= right.1 {
            (left.0 as usize, left.1)
        } else {
            (right.0 as usize, right.1)
        }
    }

    fn in_block_min(&self, b: usize, i: usize, j: usize) -> usize {
        let bt = self.block_type[b] as usize;
        let table = &self.block_lookup[bt];
        let rel = table[i * self.block_size + j] as usize;
        b * self.block_size + rel
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::containers::VecI;
    semi_persistent_containers::define_id31! { struct TestId / StoredTestId, "t"; }

    fn make_pp(n: usize, edges: &[(usize, usize)]) -> VecI<TestId, u32, false> {
        let mut pp = VecI::<TestId, u32, false>::new();
        for i in 0..n {
            pp.push(TestId::new(i as u32));
        }
        for &(child, parent) in edges {
            pp.set(TestId::new(child as u32), TestId::new(parent as u32));
        }
        pp
    }

    /// Run the same assertion on both implementations.
    macro_rules! assert_lca {
        ($pp:expr, $n:expr, $a:expr, $b:expr, $expected:expr) => {{
            let table = LcaTable::build(&$pp, $n);
            let compact = LcaTableCompact::build(&$pp, $n);
            let a = TestId::new($a);
            let b = TestId::new($b);
            let expected: Option<TestId> = $expected.map(TestId::new);
            assert_eq!(table.lca(a, b), expected, "LcaTable({}, {})", $a, $b);
            assert_eq!(
                compact.lca(a, b),
                expected,
                "LcaTableCompact({}, {})",
                $a,
                $b
            );
        }};
    }

    #[test]
    fn lca_simple_tree() {
        //       0
        //      / \
        //     1   2
        //    / \
        //   3   4
        let pp = make_pp(5, &[(1, 0), (2, 0), (3, 1), (4, 1)]);
        assert_lca!(pp, 5, 3, 4, Some(1));
        assert_lca!(pp, 5, 3, 2, Some(0));
        assert_lca!(pp, 5, 1, 2, Some(0));
        assert_lca!(pp, 5, 3, 1, Some(1));
        assert_lca!(pp, 5, 0, 4, Some(0));
    }

    #[test]
    fn lca_chain() {
        let pp = make_pp(5, &[(1, 0), (2, 1), (3, 2), (4, 3)]);
        assert_lca!(pp, 5, 0, 4, Some(0));
        assert_lca!(pp, 5, 2, 4, Some(2));
        assert_lca!(pp, 5, 3, 3, Some(3));
    }

    #[test]
    fn lca_single_node() {
        let pp = make_pp(1, &[]);
        assert_lca!(pp, 1, 0, 0, Some(0));
    }

    #[test]
    fn lca_two_roots() {
        let pp = make_pp(4, &[(1, 0), (3, 2)]);
        assert_lca!(pp, 4, 0, 1, Some(0));
        assert_lca!(pp, 4, 2, 3, Some(2));
        assert_lca!(pp, 4, 0, 2, None);
    }

    #[test]
    fn lca_wide_tree() {
        let pp = make_pp(7, &[(1, 0), (2, 0), (3, 0), (4, 0), (5, 0), (6, 0)]);
        for i in 1u32..7 {
            for j in (i + 1)..7 {
                assert_lca!(pp, 7, i, j, Some(0));
            }
        }
    }

    #[test]
    fn lca_larger_tree() {
        let pp = make_pp(8, &[(1, 0), (2, 0), (3, 1), (4, 1), (5, 2), (6, 2), (7, 3)]);
        assert_lca!(pp, 8, 7, 4, Some(1));
        assert_lca!(pp, 8, 7, 5, Some(0));
        assert_lca!(pp, 8, 5, 6, Some(2));
        assert_lca!(pp, 8, 7, 3, Some(3));
        assert_lca!(pp, 8, 3, 6, Some(0));
    }

    /// Regression: forest with siblings under second root.
    /// The ±1 property was violated at tree boundaries before the virtual root fix.
    #[test]
    fn lca_forest_siblings_under_second_root() {
        // parents = [0, 0, 2, 2, 2]
        // tree0 = {0 <- 1}, tree1 = {2 <- 3, 2 <- 4}
        let pp = make_pp(5, &[(1, 0), (3, 2), (4, 2)]);
        assert_lca!(pp, 5, 3, 4, Some(2));
        assert_lca!(pp, 5, 0, 1, Some(0));
        assert_lca!(pp, 5, 0, 3, None);
    }

    // --- Proptest -----------------------------------------------------------

    use proptest::prelude::*;
    use std::collections::HashSet;

    fn forest_strategy(max_n: usize) -> impl Strategy<Value = Vec<usize>> {
        (2..=max_n).prop_flat_map(|n| {
            let strats: Vec<_> = (0..n)
                .map(|i| {
                    if i == 0 {
                        Just(0usize).boxed()
                    } else {
                        (0..=i).boxed()
                    }
                })
                .collect();
            strats
        })
    }

    fn naive_lca(parents: &[usize], a: usize, b: usize) -> Option<usize> {
        let n = parents.len();
        if a >= n || b >= n {
            return None;
        }
        let mut anc_a = HashSet::new();
        let mut cur = a;
        loop {
            anc_a.insert(cur);
            let p = parents[cur];
            if p == cur {
                break;
            }
            cur = p;
        }
        cur = b;
        loop {
            if anc_a.contains(&cur) {
                return Some(cur);
            }
            let p = parents[cur];
            if p == cur {
                return if anc_a.contains(&cur) {
                    Some(cur)
                } else {
                    None
                };
            }
            cur = p;
        }
    }

    fn pp_from_parents(parents: &[usize]) -> VecI<TestId, u32, false> {
        let mut pp = VecI::<TestId, u32, false>::new();
        for &p in parents {
            pp.push(TestId::new(p as u32));
        }
        pp
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(5000))]

        #[test]
        fn prop_lca_matches_naive(
            parents in forest_strategy(50),
            a_idx in 0usize..50,
            b_idx in 0usize..50,
        ) {
            let n = parents.len();
            let a = a_idx % n;
            let b = b_idx % n;

            let pp = pp_from_parents(&parents);
            let table = LcaTable::build(&pp, n);
            let compact = LcaTableCompact::build(&pp, n);

            let expected = naive_lca(&parents, a, b);
            let full_result = table.lca(TestId::new(a as u32), TestId::new(b as u32))
                .map(|x| x.to_usize());
            let compact_result = compact.lca(TestId::new(a as u32), TestId::new(b as u32))
                .map(|x| x.to_usize());

            prop_assert_eq!(
                full_result, expected,
                "LcaTable({}, {}) in {:?}", a, b, parents
            );
            prop_assert_eq!(
                compact_result, expected,
                "LcaTableCompact({}, {}) in {:?}", a, b, parents
            );
        }
    }
}
