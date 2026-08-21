// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Batch LCA queries on the proof forest via Bender–Farach-Colton.
//!
//! Two implementations:
//! - [`LcaTable`]: stores full absolute depths. Simpler, faster queries.
//! - [`LcaTableCompact`]: stores `i8` deltas + block-start depths instead of
//!   one absolute depth per tour entry; queries do a short prefix sum.
//!
//! Both use O(n) preprocessing. `LcaTable` has O(1) queries;
//! `LcaTableCompact` reconstructs candidate depths with an O(log n)-length
//! in-block prefix sum. Both handle forests by introducing a virtual root
//! that parents all actual roots, preserving the ±1 depth property across
//! the entire Euler tour.
//!
//! # Staleness
//!
//! The table is a snapshot of the proof forest at build time. Any subsequent
//! `union_justified` / `rebuild` calls invalidate it — the caller must
//! rebuild the table after mutations. This is not enforced by the type system.

use crate::containers::{DenseId, IndexLike};

// ---------------------------------------------------------------------------
// Shared helpers
// ---------------------------------------------------------------------------

/// A tour position in `T`'s index word.
///
/// # Why `T::Index` is exactly wide enough
///
/// The tour has `2*(n + 1) - 1` entries for `n` nodes, so the largest position is `2n`.
/// For the bit-stealing id families (`Id31`/`Id63`, the only ones a session configures),
/// the word holds twice the ids: `Index::max_nat() == 2 * id_bound()`. Every node id is
/// below `id_bound`, so `n <= id_bound` and the largest position `2n` is at most
/// `Index::max_nat()` — representable, with the stolen bit paying for the doubling. The
/// tour of a full-capacity proof forest fits in the id's own word and needs nothing
/// wider, which is why these positions are not `usize`.
///
/// Checked rather than cast because that argument is about the id family, and a `T` with
/// a full-range `Index` (no stolen bit) would not satisfy it. Such a `T` cannot reach
/// half capacity in memory anyway, so the check never fires; it just refuses to be
/// silently wrong if one appears.
#[inline]
fn tour_pos<T: DenseId>(pos: usize) -> T::Index {
    <T::Index as IndexLike>::try_from_usize(pos)
        .expect("Euler tour position exceeds T::Index; configure a wider index word")
}

/// Virtual-root Euler tour from a proof-parent array.
/// Returns `(euler, depth, first, tree_id)`.
/// `euler` and `depth` have length 2*(n+1)-1 (virtual root included).
/// `first` and `tree_id` have length n+1 (index n = virtual root).
///
/// Depths use `usize`, so every forest that can be represented in memory can
/// also represent its maximum depth. The proof forest is re-rooted around the
/// original nodes and does not inherit the representative forest's rank bound.
///
/// # The unvisited marker in `first`
///
/// `first[i] == Index::min()` (zero) means "node `i` has no tour entry yet". Zero is
/// available as a marker rather than a position because tour position 0 is always the
/// virtual root's own entry, so no real node's first occurrence can be there — every
/// `first[i]` this function writes is `>= 1`. The previous marker was `u32::MAX`, which
/// **is** a reachable position: at full 31-bit capacity the largest position is
/// `2 * 2^31 == u32::MAX + 1`, so a tour long enough would have written the marker value
/// into `first` and `lca` would have reported "no such node" for a node that has one.
fn euler_tour<T: DenseId, const TRACK: bool>(
    pp: &crate::containers::VecI<T, T::Index, TRACK>,
    n: usize,
) -> (Vec<T>, Vec<usize>, Vec<T::Index>, Vec<T::Index>) {
    let vroot = n;
    // The virtual root gets its own id, one past the real nodes, so that `lca` can
    // recognize it in the tour and report "different trees". It used to be *aliased onto
    // node 0* (`euler.push(T::from_usize(0))` as a "placeholder"), which made the
    // `result >= n` guard in both `lca` bodies unreachable: a query whose LCA is the
    // virtual root read back as `Some(node_0)`. Today that range is unreachable for a
    // second reason — `tree_id` rejects cross-tree pairs before the RMQ runs — so the
    // guard was a dead fallback that looked live. It is live now.
    // This also bounds every `T::from_usize` below: `IndexLike::try_from_usize` on a dense
    // id rejects anything at or past `id_bound()`, so surviving it proves `n` — and therefore
    // every real node index `< n` — is inside the id space. The masking mint is then exact,
    // and the check is paid once per tour rather than once per node.
    let vroot_id = <T as IndexLike>::try_from_usize(n).expect(
        "proof forest fills the id range, leaving nothing to name the LCA virtual root; \
         configure a wider id family",
    );
    let mut children: Vec<Vec<usize>> = vec![Vec::new(); n + 1];
    for i in 0..n {
        let p = pp.get(T::from_usize(i)).to_usize();
        if p == i {
            children[vroot].push(i);
        } else {
            children[p].push(i);
        }
    }

    let cap = 2 * (n + 1);
    let mut euler = Vec::with_capacity(cap);
    let mut depth: Vec<usize> = Vec::with_capacity(cap);
    let unvisited = <T::Index as IndexLike>::min();
    let mut first = vec![unvisited; n + 1];
    let mut tree_id = vec![unvisited; n + 1];

    // Single DFS from virtual root
    // Stack: (node, child_index, depth)
    let mut stack: Vec<(usize, usize, usize)> = Vec::new();
    stack.push((vroot, 0, 0));
    euler.push(vroot_id);
    depth.push(0);
    // `first[vroot]` stays at the unvisited marker, which is also its true position (0).
    // Both readings are unused: `lca` rejects `ai >= n` before touching `first`.

    let mut current_tree = unvisited;

    while let Some((node, ci, d)) = stack.last_mut() {
        if *ci < children[*node].len() {
            // The cursor before the bump: `children[vroot]` is filled in ascending node
            // order, so the k-th descent from the virtual root enters the k-th root and
            // this ordinal *is* the tree number. The old code recovered it by scanning a
            // `roots` vector with `position()` — O(roots²) over the build, and an
            // unchecked `as u32` on the result.
            let child_ordinal = *ci;
            let child = children[*node][*ci];
            *ci += 1;
            let child_depth = d
                .checked_add(1)
                .expect("proof tree depth exceeds addressable memory");
            // Every entry of `children` is a real node index below `n` (the parent array
            // has `n` rows), so this is in range without clamping.
            euler.push(T::from_usize(child));
            depth.push(child_depth);
            if first[child] == unvisited {
                first[child] = tour_pos::<T>(euler.len() - 1);
            }
            if *node == vroot {
                current_tree = tour_pos::<T>(child_ordinal);
            }
            tree_id[child] = current_tree;
            stack.push((child, 0, child_depth));
        } else {
            stack.pop();
            if let Some(&(parent, _, pd)) = stack.last() {
                euler.push(if parent == vroot {
                    vroot_id
                } else {
                    T::from_usize(parent)
                });
                depth.push(pd);
            }
        }
    }

    (euler, depth, first, tree_id)
}

/// Block decomposition shared state. `I` is the tour-position word (see [`tour_pos`]).
struct BlockDecomp<I> {
    block_size: usize,
    num_blocks: usize,
    /// Tour position of the minimum-depth entry in each block.
    block_min: Vec<I>,
    /// ±1 pattern for each block.
    block_type: Vec<usize>,
}

fn block_decompose<T: DenseId>(depth: &[usize], m: usize) -> BlockDecomp<T::Index> {
    let block_size = ((usize::BITS - m.leading_zeros()) as usize / 2).max(1);
    let num_blocks = m.div_ceil(block_size);

    let mut block_min = vec![<T::Index as IndexLike>::min(); num_blocks];
    let mut block_type = vec![0usize; num_blocks];

    for b in 0..num_blocks {
        let start = b * block_size;
        let end = (start + block_size).min(m);
        let mut min_idx = start;
        let mut min_depth = depth[start];
        let mut pattern: usize = 0;
        for i in start..end {
            if depth[i] < min_depth {
                min_depth = depth[i];
                min_idx = i;
            }
            if i > start && depth[i] > depth[i - 1] {
                pattern |= 1 << (i - start - 1);
            }
        }
        block_min[b] = tour_pos::<T>(min_idx);
        block_type[b] = pattern;
    }

    BlockDecomp {
        block_size,
        num_blocks,
        block_min,
        block_type,
    }
}

fn build_sparse_table<T: DenseId>(
    depth: &[usize],
    bd: &BlockDecomp<T::Index>,
) -> Vec<Vec<T::Index>> {
    let num_blocks = bd.num_blocks;
    let log_blocks = if num_blocks > 1 {
        (usize::BITS - (num_blocks - 1).leading_zeros()) as usize
    } else {
        1
    };
    let mut sparse: Vec<Vec<T::Index>> = Vec::with_capacity(log_blocks);
    sparse.push(bd.block_min.clone());

    for k in 1..log_blocks {
        let prev = &sparse[k - 1];
        let half = 1 << (k - 1);
        let len = num_blocks.saturating_sub(1 << k) + 1;
        let mut level = Vec::with_capacity(len);
        for i in 0..len {
            let left = prev[i];
            let right = prev[i + half];
            level.push(if depth[left.as_usize()] <= depth[right.as_usize()] {
                left
            } else {
                right
            });
        }
        sparse.push(level);
    }
    sparse
}

fn build_block_lookup<I>(depth: &[usize], bd: &BlockDecomp<I>, m: usize) -> Vec<Vec<u16>> {
    let block_size = bd.block_size;
    let num_patterns = 1usize << block_size.saturating_sub(1);
    let mut block_lookup: Vec<Vec<u16>> = vec![Vec::new(); num_patterns];

    for b in 0..bd.num_blocks {
        let bt = bd.block_type[b];
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
/// Absolute depths use `usize`: proof-edge re-rooting can form a linear chain,
/// independently of the rank bound on the representative forest.
pub struct LcaTable<T: DenseId> {
    euler: Vec<T>,
    depth: Vec<usize>,
    /// First tour position of each node, or [`IndexLike::min`] if it has none.
    first: Vec<T::Index>,
    tree_id: Vec<T::Index>,
    n: usize,
    block_size: usize,
    sparse: Vec<Vec<T::Index>>,
    block_lookup: Vec<Vec<u16>>,
    block_type: Vec<usize>,
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

        let bd = block_decompose::<T>(&depth, m);
        let sparse = build_sparse_table::<T>(&depth, &bd);
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
        // `min()` is the "no tour entry" marker, never a real node's first position —
        // position 0 belongs to the virtual root. See `euler_tour`.
        let unvisited = <T::Index as IndexLike>::min();
        if fa == unvisited || fb == unvisited {
            return None;
        }
        if self.tree_id[ai] != self.tree_id[bi] {
            return None;
        }
        let (i, j) = if fa <= fb {
            (fa.as_usize(), fb.as_usize())
        } else {
            (fb.as_usize(), fa.as_usize())
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
        let left = self.sparse[k][bl].as_usize();
        let right = self.sparse[k][br - (1 << k) + 1].as_usize();
        if self.depth[left] <= self.depth[right] {
            left
        } else {
            right
        }
    }

    fn in_block_min(&self, b: usize, i: usize, j: usize) -> usize {
        let bt = self.block_type[b];
        let table = &self.block_lookup[bt];
        let rel = table[i * self.block_size + j] as usize;
        b * self.block_size + rel
    }
}

// ---------------------------------------------------------------------------
// LcaTableCompact — delta-encoded depths
// ---------------------------------------------------------------------------

/// Precomputed LCA structure with delta-encoded depths.
/// It avoids one absolute-depth word per Euler entry. Queries do a short
/// prefix sum to recover absolute depths when comparing candidates.
pub struct LcaTableCompact<T: DenseId> {
    euler: Vec<T>,
    /// ±1 deltas between consecutive Euler tour depths. Length = tour_len - 1.
    delta: Vec<i8>,
    /// Absolute depth at the start of each block.
    block_depth: Vec<usize>,
    /// First tour position of each node, or [`IndexLike::min`] if it has none.
    first: Vec<T::Index>,
    tree_id: Vec<T::Index>,
    n: usize,
    block_size: usize,
    /// Sparse table entries: (tour_position, absolute_depth).
    sparse: Vec<Vec<(T::Index, usize)>>,
    block_lookup: Vec<Vec<u16>>,
    block_type: Vec<usize>,
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
            let d = match depth[i].cmp(&depth[i - 1]) {
                std::cmp::Ordering::Greater => 1,
                std::cmp::Ordering::Less => -1,
                std::cmp::Ordering::Equal => 0,
            };
            debug_assert_eq!(
                depth[i].abs_diff(depth[i - 1]),
                1,
                "±1 property violated at position {i}"
            );
            delta.push(d);
        }

        let bd = block_decompose::<T>(&depth, m);

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
            let mut sparse: Vec<Vec<(T::Index, usize)>> = Vec::with_capacity(log_blocks);
            // Level 0
            let level0: Vec<(T::Index, usize)> = bd
                .block_min
                .iter()
                .map(|&pos| (pos, depth[pos.as_usize()]))
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
        // `min()` is the "no tour entry" marker, never a real node's first position —
        // position 0 belongs to the virtual root. See `euler_tour`.
        let unvisited = <T::Index as IndexLike>::min();
        if fa == unvisited || fb == unvisited {
            return None;
        }
        if self.tree_id[ai] != self.tree_id[bi] {
            return None;
        }
        let (i, j) = if fa <= fb {
            (fa.as_usize(), fb.as_usize())
        } else {
            (fb.as_usize(), fa.as_usize())
        };
        let idx = self.rmq(i, j);
        let result = self.euler[idx];
        if result.to_usize() >= self.n {
            return None;
        }
        Some(result)
    }

    /// Recover absolute depth at tour position `pos` from block-start depth + prefix sum.
    fn depth_at(&self, pos: usize) -> usize {
        let b = pos / self.block_size;
        let offset = pos % self.block_size;
        let block_start = b * self.block_size;
        let mut d = self.block_depth[b];
        for i in block_start..block_start + offset {
            if self.delta[i] > 0 {
                d += 1;
            } else {
                d = d
                    .checked_sub(1)
                    .expect("Euler-tour depth cannot become negative");
            }
        }
        d
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

    fn sparse_query(&self, bl: usize, br: usize) -> (usize, usize) {
        let len = br - bl + 1;
        let k = (usize::BITS - len.leading_zeros()) as usize - 1;
        let left = self.sparse[k][bl];
        let right = self.sparse[k][br - (1 << k) + 1];
        if left.1 <= right.1 {
            (left.0.as_usize(), left.1)
        } else {
            (right.0.as_usize(), right.1)
        }
    }

    fn in_block_min(&self, b: usize, i: usize, j: usize) -> usize {
        let bt = self.block_type[b];
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
            pp.try_push(TestId::new(i as u32))
                .expect("push: within index word");
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
            pp.try_push(TestId::new(p as u32))
                .expect("push: within index word");
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
