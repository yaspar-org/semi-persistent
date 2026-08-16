// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! UNVERIFIED PROTOTYPES. Measurement only, not a landing.
//!
//! Three interchangeable implementations of the index families' span table, so
//! the cost of the dense build's `O(num_keys)` term can be measured against the
//! alternatives on the real workload rather than argued about:
//!
//! * default (no feature): the verified [`DenseSpanMap`], unchanged;
//! * `span-proto-sorted`, sort-based: LSD radix sort by key, spans derived from
//!   run boundaries, probes by binary search over the occupied keys;
//! * `span-proto-reuse`: dense keys and `O(1)` probes kept, but the span table
//!   is a generation-stamped buffer recycled across rounds, so a build touches
//!   only the keys that occur.
//!
//! Everything here is unverified Rust with no proof obligations, and none of it
//! is meant to land: the chosen design is stated in the findings doc and gets
//! written against `containers-verus`'s proof discipline separately. It is
//! nonetheless meant to be correct, because a measurement of a wrong build is a
//! measurement of nothing, so the corpus and the test suite are conditions on it.
//!
//! `index.rs` is written once, against the free functions at the bottom of this
//! module, and the feature selects which representation those functions reach.

use crate::containers::DenseId;
#[cfg(not(any(feature = "span-proto-sorted", feature = "span-proto-reuse")))]
use semi_persistent_containers::DenseSpanMap;

// ---------------------------------------------------------------------------
// Representation selection
// ---------------------------------------------------------------------------

#[cfg(not(any(feature = "span-proto-sorted", feature = "span-proto-reuse")))]
pub type Family<V> = DenseSpanMap<V>;
#[cfg(feature = "span-proto-sorted")]
pub type Family<V> = SortedSpanMap<V>;
#[cfg(feature = "span-proto-reuse")]
pub type Family<V> = ReuseSpanMap<V>;

/// Build one family from its stream. `num_keys` is the stream's own key bound.
#[inline]
pub fn build<V: DenseId>(stream: &[(usize, V)], num_keys: usize) -> Family<V> {
    #[cfg(not(any(feature = "span-proto-sorted", feature = "span-proto-reuse")))]
    {
        DenseSpanMap::try_build(stream, num_keys)
            .expect("num_keys is the stream's own key bound, accumulated as it was written")
    }
    #[cfg(feature = "span-proto-sorted")]
    {
        SortedSpanMap::build(stream, num_keys)
    }
    #[cfg(feature = "span-proto-reuse")]
    {
        ReuseSpanMap::build(stream, num_keys)
    }
}

/// Key `k`'s values, or the empty slice when `k` names no key of this build.
#[inline]
pub fn get<V: DenseId>(m: &Family<V>, k: usize) -> &[V] {
    #[cfg(not(any(feature = "span-proto-sorted", feature = "span-proto-reuse")))]
    {
        m.try_get(k).unwrap_or(&[])
    }
    #[cfg(any(feature = "span-proto-sorted", feature = "span-proto-reuse"))]
    {
        m.get(k)
    }
}

/// Number of keys the build was sized for (its key bound).
#[inline]
pub fn num_keys<V: DenseId>(m: &Family<V>) -> usize {
    m.len()
}

/// Number of values under key `k`.
#[inline]
pub fn key_len<V: DenseId>(m: &Family<V>, k: usize) -> usize {
    get(m, k).len()
}

/// Total number of values across all keys.
#[inline]
pub fn total<V: DenseId>(m: &Family<V>) -> usize {
    m.total()
}

/// Visit every key with at least one value, in an unspecified order.
///
/// The dense representation has to scan the whole key space to find them, which
/// is the same `O(num_keys)` walk `measure_fanouts` already did; the prototypes
/// hold the occupied keys explicitly and hand them over directly. The order
/// differs between the three, ascending for the dense and sorted maps and
/// first-occurrence for the recycled one, and no caller depends on it: the
/// fan-out pass reads each key's position as `k / stride` and accumulates into
/// a map, and the two assertions and the counter are per bucket.
#[inline]
pub fn for_each_occupied<V: DenseId>(m: &Family<V>, mut f: impl FnMut(usize, &[V])) {
    #[cfg(not(any(feature = "span-proto-sorted", feature = "span-proto-reuse")))]
    {
        for k in 0..m.len() {
            let b = m.get(k);
            if !b.is_empty() {
                f(k, b);
            }
        }
    }
    #[cfg(any(feature = "span-proto-sorted", feature = "span-proto-reuse"))]
    {
        m.for_each_occupied(&mut f);
    }
}

// ---------------------------------------------------------------------------
// Prototype 1: sort-based span derivation
// ---------------------------------------------------------------------------

/// Spans derived from the run boundaries of a key-sorted stream.
///
/// No array is proportional to the key space: `keys` and `offs` are one entry
/// per *occupied* key, and the pool is one entry per value. What that buys on
/// the build it gives back on the probe, which becomes a binary search over
/// `keys` instead of an array index.
#[cfg(feature = "span-proto-sorted")]
pub struct SortedSpanMap<V> {
    /// Occupied keys, ascending.
    keys: Vec<u32>,
    /// `offs[i]` is where key `keys[i]`'s run starts; `offs[len]` is the pool
    /// length, so a run is `offs[i]..offs[i + 1]` and needs no length field.
    offs: Vec<u32>,
    pool: Vec<V>,
    /// The key bound the build was handed, so `len()` answers what the dense
    /// map's does and callers that iterate a key range are unaffected.
    num_keys: usize,
}

#[cfg(feature = "span-proto-sorted")]
impl<V: DenseId> SortedSpanMap<V> {
    /// LSD radix sort by key in 11-bit digits, then one scan for the runs.
    ///
    /// Radix rather than a comparison sort because the key is bounded by
    /// `num_keys` and two passes cover 22 bits, which is the whole key space of
    /// the family this is aimed at; a `sort_unstable` over the same stream is
    /// `V log V` comparisons on a branchy predicate. Stability is what keeps
    /// each bucket ascending in node id: the build stream is written in
    /// ascending id, and an LSD radix pass preserves the order of equal keys.
    fn build(stream: &[(usize, V)], num_keys: usize) -> Self {
        let n = stream.len();
        if n == 0 {
            return Self {
                keys: Vec::new(),
                offs: vec![0],
                pool: Vec::new(),
                num_keys,
            };
        }

        // Pack (key, value) into one u64 so the sort moves 8 bytes per entry
        // rather than the stream's 16. Keys are below `num_keys` and values are
        // dense ids; both fit in 32 bits for the 31-bit id family, which is what
        // the corpus runs.
        let packable = num_keys <= u32::MAX as usize
            && stream
                .iter()
                .all(|&(_, v)| v.to_usize() <= u32::MAX as usize);
        assert!(
            packable,
            "span-proto-sorted prototype covers the 32-bit key/value range only"
        );

        let mut a: Vec<u64> = stream
            .iter()
            .map(|&(k, v)| ((k as u64) << 32) | (v.to_usize() as u64))
            .collect();
        let mut b: Vec<u64> = vec![0; n];

        const BITS: u32 = 11;
        const RADIX: usize = 1 << BITS;
        const MASK: u64 = (RADIX - 1) as u64;
        let key_bits = usize::BITS - num_keys.saturating_sub(1).leading_zeros();
        let passes = key_bits.div_ceil(BITS).max(1);

        let mut hist = [0u32; RADIX];
        for p in 0..passes {
            let shift = 32 + p * BITS;
            hist.fill(0);
            for &x in a.iter() {
                hist[((x >> shift) & MASK) as usize] += 1;
            }
            // Skip a pass whose digit is constant: the top digit of a key space
            // that does not fill its width is usually one value.
            if hist.iter().any(|&c| c as usize == n) {
                continue;
            }
            let mut acc = 0u32;
            for c in hist.iter_mut() {
                let t = *c;
                *c = acc;
                acc += t;
            }
            for &x in a.iter() {
                let d = ((x >> shift) & MASK) as usize;
                b[hist[d] as usize] = x;
                hist[d] += 1;
            }
            std::mem::swap(&mut a, &mut b);
        }

        // Runs. `a` is ascending in key, and inside a key ascending in the
        // stream's own order, which is ascending in node id.
        let mut keys: Vec<u32> = Vec::with_capacity(64);
        let mut offs: Vec<u32> = Vec::with_capacity(64);
        let mut pool: Vec<V> = Vec::with_capacity(n);
        let mut prev = u32::MAX;
        for (i, &x) in a.iter().enumerate() {
            let k = (x >> 32) as u32;
            if i == 0 || k != prev {
                keys.push(k);
                offs.push(i as u32);
                prev = k;
            }
            pool.push(V::from_usize((x & 0xFFFF_FFFF) as usize));
        }
        offs.push(n as u32);

        Self {
            keys,
            offs,
            pool,
            num_keys,
        }
    }

    #[inline]
    fn get(&self, k: usize) -> &[V] {
        if k >= self.num_keys || k > u32::MAX as usize {
            return &[];
        }
        match self.keys.binary_search(&(k as u32)) {
            Ok(i) => &self.pool[self.offs[i] as usize..self.offs[i + 1] as usize],
            Err(_) => &[],
        }
    }

    #[inline]
    fn len(&self) -> usize {
        self.num_keys
    }

    #[inline]
    fn total(&self) -> usize {
        self.pool.len()
    }

    fn for_each_occupied(&self, f: &mut impl FnMut(usize, &[V])) {
        for (i, &k) in self.keys.iter().enumerate() {
            f(
                k as usize,
                &self.pool[self.offs[i] as usize..self.offs[i + 1] as usize],
            );
        }
    }
}

// ---------------------------------------------------------------------------
// Prototype 2: dense keys, recycled generation-stamped span table
// ---------------------------------------------------------------------------

/// A dense span table entry that carries the build it belongs to.
///
/// The stamp is what removes the clear: a key whose stamp is not the current
/// build's is empty whatever `off`/`len` still say, so a build starts by
/// bumping a counter instead of writing `num_keys` zeros.
#[cfg(feature = "span-proto-reuse")]
#[derive(Clone, Copy, Default)]
struct StampedSpan {
    stamp: u32,
    off: u32,
    len: u32,
}

/// One recycled span-table buffer.
#[cfg(feature = "span-proto-reuse")]
#[derive(Default)]
struct SpanBuf {
    spans: Vec<StampedSpan>,
    /// Keys this build touched, in first-occurrence order. Doubles as the list
    /// the offset assignment walks, which is why the assignment is `O(occupied)`
    /// and not a prefix sum over the key space.
    occ: Vec<u32>,
    stamp: u32,
}

#[cfg(feature = "span-proto-reuse")]
thread_local! {
    /// Free list of span-table buffers. A round has two maps of a family alive
    /// at once (full and delta), so this hands out distinct buffers rather than
    /// sharing one; a prototype's stand-in for threading an arena through
    /// `IndexScratch`, which is what the landing would do.
    static FREE: std::cell::RefCell<Vec<SpanBuf>> = const { std::cell::RefCell::new(Vec::new()) };
}

/// Dense-keyed span map whose span table outlives the build that filled it.
#[cfg(feature = "span-proto-reuse")]
pub struct ReuseSpanMap<V> {
    buf: Option<SpanBuf>,
    pool: Vec<V>,
    num_keys: usize,
}

#[cfg(feature = "span-proto-reuse")]
impl<V> Drop for ReuseSpanMap<V> {
    fn drop(&mut self) {
        if let Some(b) = self.buf.take() {
            FREE.with(|f| f.borrow_mut().push(b));
        }
    }
}

#[cfg(feature = "span-proto-reuse")]
impl<V: DenseId> ReuseSpanMap<V> {
    fn build(stream: &[(usize, V)], num_keys: usize) -> Self {
        let mut buf = FREE.with(|f| f.borrow_mut().pop()).unwrap_or_default();
        buf.occ.clear();
        buf.stamp = buf.stamp.wrapping_add(1);
        // Generation 0 is the "never written" stamp `StampedSpan::default` carries,
        // so a wrap must skip it and re-stamp the whole table once.
        if buf.stamp == 0 {
            buf.spans.iter_mut().for_each(|s| s.stamp = 0);
            buf.stamp = 1;
        }
        if buf.spans.len() < num_keys {
            buf.spans.resize(num_keys, StampedSpan::default());
        }
        let g = buf.stamp;

        // Pass 1: population per key, and the occupied-key list.
        for &(k, _) in stream {
            let s = &mut buf.spans[k];
            if s.stamp != g {
                s.stamp = g;
                s.off = 0;
                s.len = 0;
                buf.occ.push(k as u32);
            }
            s.len += 1;
        }
        // Pass 1b: extents, over the occupied keys only. Keys are laid out in
        // first-occurrence order rather than key order, which the per-key
        // refinement does not constrain: each key's slice is still the stream's
        // order-preserving filter down to that key.
        let mut acc: u32 = 0;
        for &k in buf.occ.iter() {
            let s = &mut buf.spans[k as usize];
            s.off = acc;
            acc += s.len;
            s.len = 0;
        }
        // Pass 2: placement, with each key's `len` as its running cursor.
        let mut pool: Vec<V> = vec![V::default(); acc as usize];
        for &(k, v) in stream {
            let s = &mut buf.spans[k];
            pool[(s.off + s.len) as usize] = v;
            s.len += 1;
        }

        Self {
            buf: Some(buf),
            pool,
            num_keys,
        }
    }

    #[inline]
    fn spans(&self) -> &[StampedSpan] {
        &self
            .buf
            .as_ref()
            .expect("buffer is taken only on drop")
            .spans
    }

    #[inline]
    fn stamp(&self) -> u32 {
        self.buf
            .as_ref()
            .expect("buffer is taken only on drop")
            .stamp
    }

    #[inline]
    fn get(&self, k: usize) -> &[V] {
        if k >= self.num_keys {
            return &[];
        }
        let s = self.spans()[k];
        if s.stamp != self.stamp() {
            return &[];
        }
        &self.pool[s.off as usize..(s.off + s.len) as usize]
    }

    #[inline]
    fn len(&self) -> usize {
        self.num_keys
    }

    #[inline]
    fn total(&self) -> usize {
        self.pool.len()
    }

    /// First-occurrence order, which is the order the build already has: sorting
    /// it would put back an `O(occupied log occupied)` term per call, and no
    /// caller reads the keys in order (see [`for_each_occupied`]).
    fn for_each_occupied(&self, f: &mut impl FnMut(usize, &[V])) {
        let b = self.buf.as_ref().expect("buffer is taken only on drop");
        for i in 0..b.occ.len() {
            let k = b.occ[i] as usize;
            f(k, self.get(k));
        }
    }
}
