// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! `ValueCompressor`: the value-layer strategy (goal F2).
//!
//! Indices are always `IndexLike`, so the index layers (runs, sorted runs) are
//! universally available. The VALUE layer is the open extension point: the
//! dictionary calls `T::as_usize` and delta does value arithmetic, so those
//! need `T: IndexLike`, while the node caches and the class-data columns hold
//! structs where only verbatim or equality-RLE applies. The value codec is a
//! strategy parameter and the bound lives on the strategy impl, never on
//! `Vec`, `DiffLog` or the frames. An illegal column/codec pairing (a struct
//! column with `ValueDictC`) does not typecheck, so no runtime fallback needs
//! to forbid it; see the `compile_fail` doc-test on [`ValueDictC`].
//!
//! Decompression stays universal at `T: Copy`: `decode_at` needs no
//! `IndexLike`, so a frame HOLDING a coded column restores under the weakest
//! bound; only building one requires the capability.
//!
//! Interface deviations from the goal appendix, recorded per its own rule:
//! - `ValueRle` is bounded `T: Copy + EqSpec`, not `T: Copy + PartialEq`:
//!   an exec `PartialEq` call carries no spec meaning in Verus, so RLE (whose
//!   exactness proof turns on "the coalesced value IS the input value") needs
//!   the spec-carrying counterpart. `EqSpec` is one method with the obvious
//!   contract; machine words implement it here and a struct column implements
//!   it as a trusted one-liner (the same leaf-trust shape as `external_body`).
//! - `ValueDelta` codes against the PREVIOUS VALUE, not the cell index: this
//!   interface sees only the value column (the index column belongs to the
//!   frame's index layer), so against-cell-index delta remains `DeltaFrame`
//!   (F3), which lives at the `(value, index)` frame level where the index
//!   exists.

use crate::diff_compress::ValFrame;
use crate::index_like::IndexLike;
use vstd::prelude::*;

verus! {

/// Spec-carrying equality: `eq_exec` returns exactly spec equality. The bound
/// RLE coalescing needs; `PartialEq` alone gives an unspecified bool.
pub trait EqSpec: Sized {
    fn eq_exec(&self, other: &Self) -> (r: bool)
        ensures r == (self == other);
}

/// Strategy for one column's value layer. Whatever bound a codec needs sits on
/// ITS impl. `compress` is exact: `decode` reproduces the input sequence, so
/// the layered frame's reconstruction theorems are codec-agnostic.
pub trait ValueCompressor<T: Copy>: Sized {
    type Compressed;

    spec fn decode(c: &Self::Compressed) -> Seq<T>;

    /// Structural well-formedness `compress` establishes and `decode_at` needs.
    spec fn cwf(c: &Self::Compressed) -> bool;

    fn compress(vals: &Vec<T>) -> (c: Self::Compressed)
        ensures
            Self::cwf(&c),
            Self::decode(&c) == vals@;

    fn decoded_len(c: &Self::Compressed) -> (n: usize)
        requires Self::cwf(c),
        ensures n == Self::decode(c).len();

    fn decode_at(c: &Self::Compressed, i: usize) -> (v: T)
        requires
            Self::cwf(c),
            i < Self::decode(c).len(),
        ensures v == Self::decode(c)[i as int];

    /// Length-based byte count (diagnostic; the selector costs candidates
    /// with it).
    fn byte_len(c: &Self::Compressed) -> usize;

    /// Whether the per-frame selector should build layered candidates with
    /// this codec. The identity codec answers false (a layered frame over it
    /// duplicates the index-only encoders), every real codec answers true.
    fn enabled() -> bool;
}

// ---------------------------------------------------------------------------
// NoValueCompression — identity, any `T: Copy`. What struct columns default to.
// ---------------------------------------------------------------------------

pub struct NoValueCompression;

impl<T: Copy> ValueCompressor<T> for NoValueCompression {
    type Compressed = Vec<T>;

    open spec fn decode(c: &Vec<T>) -> Seq<T> {
        c@
    }

    open spec fn cwf(c: &Vec<T>) -> bool {
        true
    }

    fn compress(vals: &Vec<T>) -> (c: Vec<T>) {
        let mut out: Vec<T> = Vec::new();
        let n = vals.len();
        let mut i: usize = 0;
        while i < n
            invariant i <= n, n == vals@.len(), out@ == vals@.subrange(0, i as int),
            decreases n - i,
        {
            out.push(vals[i]);
            i += 1;
        }
        proof { assert(out@ =~= vals@); }
        out
    }

    fn decoded_len(c: &Vec<T>) -> (n: usize) {
        c.len()
    }

    fn decode_at(c: &Vec<T>, i: usize) -> (v: T) {
        c[i]
    }

    fn byte_len(c: &Vec<T>) -> usize {
        // Saturating: a diagnostic must never trap. vstd models both
        // `size_of` and `checked_mul`, so this needs no trust.
        match c.len().checked_mul(core::mem::size_of::<T>()) {
            Some(n) => n,
            None => usize::MAX,
        }
    }

    fn enabled() -> bool {
        false
    }
}

// ---------------------------------------------------------------------------
// ValueRle — equality run-length coding, `T: Copy + EqSpec` (structs
// included). The struct-column compressor: a cache column whose frame writes
// repeat one entry value pays len(runs) instead of len(values).
// ---------------------------------------------------------------------------

/// Runs of equal values: `(value, count)`.
pub struct RleVals<T> {
    pub runs: Vec<(T, usize)>,
}

/// The value sequence a run list decodes to (recursive over the run list).
pub open spec fn rle_decode<T>(runs: Seq<(T, usize)>) -> Seq<T>
    decreases runs.len(),
{
    if runs.len() == 0 {
        Seq::empty()
    } else {
        rle_decode(runs.drop_last())
            + Seq::new(runs.last().1 as nat, |_i: int| runs.last().0)
    }
}

/// Appending a fresh run of count 1 appends exactly one value.
proof fn lemma_rle_push_new<T>(runs: Seq<(T, usize)>, v: T)
    ensures rle_decode(runs.push((v, 1usize))) == rle_decode(runs).push(v),
{
    let pushed = runs.push((v, 1usize));
    assert(pushed.drop_last() =~= runs);
    assert(Seq::new(1nat, |_i: int| v) =~= Seq::empty().push(v));
    assert(rle_decode(pushed) =~= rle_decode(runs).push(v));
}

/// Incrementing the last run's count appends one copy of its value.
proof fn lemma_rle_bump_last<T>(runs: Seq<(T, usize)>, k: usize)
    requires
        runs.len() > 0,
        runs.last().1 == k,
        k < usize::MAX,
    ensures
        rle_decode(runs.update(runs.len() - 1, (runs.last().0, (k + 1) as usize)))
            == rle_decode(runs).push(runs.last().0),
{
    let v = runs.last().0;
    let updated = runs.update(runs.len() - 1, (v, (k + 1) as usize));
    assert(updated.drop_last() =~= runs.drop_last());
    assert(updated.last() == (v, (k + 1) as usize));
    assert(Seq::new((k + 1) as nat, |_i: int| v)
        =~= Seq::new(k as nat, |_i: int| v).push(v));
    assert(rle_decode(updated) =~= rle_decode(runs).push(v));
}

/// `rle_decode` of a prefix of the run list is a prefix of `rle_decode` of the
/// whole list (induction on the dropped suffix).
proof fn lemma_rle_prefix_is_prefix<T>(runs: Seq<(T, usize)>, j: int)
    requires 0 <= j <= runs.len(),
    ensures
        rle_decode(runs.subrange(0, j)).len() <= rle_decode(runs).len(),
        rle_decode(runs.subrange(0, j)) =~= rle_decode(runs).subrange(
            0, rle_decode(runs.subrange(0, j)).len() as int),
    decreases runs.len() - j,
{
    if j == runs.len() {
        assert(runs.subrange(0, j) =~= runs);
    } else {
        lemma_rle_prefix_is_prefix(runs, j + 1);
        assert(runs.subrange(0, j + 1).drop_last() =~= runs.subrange(0, j));
        assert(rle_decode(runs.subrange(0, j + 1))
            == rle_decode(runs.subrange(0, j))
                + Seq::new(runs[j].1 as nat, |_i: int| runs[j].0));
    }
}

/// The decoded length of a one-run-longer prefix grows by that run's count.
proof fn lemma_rle_prefix_len<T>(runs: Seq<(T, usize)>, j: int)
    requires 0 <= j < runs.len(),
    ensures
        rle_decode(runs.subrange(0, j + 1)).len()
            == rle_decode(runs.subrange(0, j)).len() + runs[j].1,
        rle_decode(runs.subrange(0, j + 1)).len() <= rle_decode(runs).len(),
{
    lemma_rle_prefix_is_prefix(runs, j + 1);
    assert(runs.subrange(0, j + 1).drop_last() =~= runs.subrange(0, j));
    assert(rle_decode(runs.subrange(0, j + 1))
        == rle_decode(runs.subrange(0, j))
            + Seq::new(runs[j].1 as nat, |_i: int| runs[j].0));
}

/// Position `off` inside run `j` decodes to run `j`'s value.
proof fn lemma_rle_at<T>(runs: Seq<(T, usize)>, j: int, off: int)
    requires
        0 <= j < runs.len(),
        0 <= off < runs[j].1,
    ensures
        rle_decode(runs).len() >= rle_decode(runs.subrange(0, j)).len() + runs[j].1,
        rle_decode(runs)[rle_decode(runs.subrange(0, j)).len() + off] == runs[j].0,
{
    lemma_rle_prefix_len(runs, j);
    lemma_rle_prefix_is_prefix(runs, j + 1);
    let pfx = rle_decode(runs.subrange(0, j)).len() as int;
    assert(runs.subrange(0, j + 1).drop_last() =~= runs.subrange(0, j));
    assert(rle_decode(runs.subrange(0, j + 1))
        == rle_decode(runs.subrange(0, j))
            + Seq::new(runs[j].1 as nat, |_i: int| runs[j].0));
    assert(rle_decode(runs.subrange(0, j + 1))[pfx + off] == runs[j].0);
    assert(rle_decode(runs)[pfx + off] == runs[j].0);
}

impl<T: Copy> RleVals<T> {
    /// Sum of counts (the decoded length). The bound is what `ValueRle::cwf`
    /// carries: it makes the equality promise satisfiable.
    pub fn decoded_len(&self) -> (n: usize)
        requires rle_decode(self.runs@).len() <= usize::MAX as nat,
        ensures n as nat == rle_decode(self.runs@).len(),
    {
        let m = self.runs.len();
        let mut total: usize = 0;
        let mut j: usize = 0;
        proof {
            assert(self.runs@.subrange(0, 0) =~= Seq::<(T, usize)>::empty());
            assert(rle_decode::<T>(Seq::empty()) =~= Seq::<T>::empty());
        }
        while j < m
            invariant
                j <= m,
                m == self.runs@.len(),
                rle_decode(self.runs@).len() <= usize::MAX as nat,
                total as nat == rle_decode(self.runs@.subrange(0, j as int)).len(),
                rle_decode(self.runs@.subrange(0, j as int)).len()
                    <= rle_decode(self.runs@).len(),
            decreases m - j,
        {
            proof {
                lemma_rle_prefix_len(self.runs@, j as int);
            }
            total = total + self.runs[j].1;
            j += 1;
        }
        proof { assert(self.runs@.subrange(0, m as int) =~= self.runs@); }
        total
    }

    /// The value at decoded position `i`: linear scan with a running total.
    pub fn decode_at(&self, i: usize) -> (v: T)
        requires (i as nat) < rle_decode(self.runs@).len(),
        ensures v == rle_decode(self.runs@)[i as int],
    {
        let m = self.runs.len();
        let mut seen: usize = 0;
        let mut j: usize = 0;
        proof {
            assert(self.runs@.subrange(0, 0) =~= Seq::<(T, usize)>::empty());
            assert(rle_decode::<T>(Seq::empty()) =~= Seq::<T>::empty());
        }
        loop
            invariant
                j <= m,
                m == self.runs@.len(),
                seen as nat == rle_decode(self.runs@.subrange(0, j as int)).len(),
                seen <= i,
                (i as nat) < rle_decode(self.runs@).len(),
            decreases m - j,
        {
            proof {
                if j == m {
                    assert(self.runs@.subrange(0, m as int) =~= self.runs@);
                }
            }
            assert(j < m);
            proof { lemma_rle_prefix_len(self.runs@, j as int); }
            let (rv, rk) = self.runs[j];
            if i - seen < rk {
                proof { lemma_rle_at(self.runs@, j as int, (i - seen) as int); }
                return rv;
            }
            seen = seen + rk;
            j += 1;
        }
    }
}

pub struct ValueRle;

impl<T: Copy + EqSpec> ValueCompressor<T> for ValueRle {
    type Compressed = RleVals<T>;

    open spec fn decode(c: &RleVals<T>) -> Seq<T> {
        rle_decode(c.runs@)
    }

    /// The decoded length fits `usize`, so `decoded_len` can promise equality
    /// with it. `compress` gets it for free: decode equals the input vec's
    /// sequence.
    open spec fn cwf(c: &RleVals<T>) -> bool {
        rle_decode(c.runs@).len() <= usize::MAX as nat
    }

    fn compress(vals: &Vec<T>) -> (c: RleVals<T>) {
        let mut runs: Vec<(T, usize)> = Vec::new();
        let n = vals.len();
        let mut i: usize = 0;
        proof { assert(rle_decode::<T>(runs@) =~= Seq::<T>::empty()); }
        while i < n
            invariant
                i <= n,
                n == vals@.len(),
                rle_decode(runs@) == vals@.subrange(0, i as int),
            decreases n - i,
        {
            let v = vals[i];
            proof {
                assert(vals@.subrange(0, (i + 1) as int)
                    =~= vals@.subrange(0, i as int).push(vals@[i as int]));
            }
            let mut extended = false;
            if runs.len() > 0 {
                let li = runs.len() - 1;
                let last = runs[li];
                if last.1 < usize::MAX && last.0.eq_exec(&v) {
                    // `eq_exec` carries spec equality, so extending the run
                    // appends exactly `vals[i]`.
                    proof { lemma_rle_bump_last(runs@, last.1); }
                    runs.set(li, (last.0, last.1 + 1));
                    extended = true;
                }
            }
            if !extended {
                proof { lemma_rle_push_new(runs@, v); }
                runs.push((v, 1));
            }
            i += 1;
        }
        proof {
            assert(vals@.subrange(0, n as int) =~= vals@);
            // n: usize == vals@.len(), so the decoded length fits usize.
            assert(vals@.len() <= usize::MAX as nat);
        }
        RleVals { runs }
    }

    fn decoded_len(c: &RleVals<T>) -> (n: usize) {
        RleVals::decoded_len(c)
    }

    fn decode_at(c: &RleVals<T>, i: usize) -> (v: T) {
        RleVals::decode_at(c, i)
    }

    fn byte_len(c: &RleVals<T>) -> usize {
        crate::compression_stats::sat_mul(
            c.runs.len(),
            crate::compression_stats::sat_add(
                core::mem::size_of::<T>(), core::mem::size_of::<usize>()))
    }

    fn enabled() -> bool {
        true
    }
}

// ---------------------------------------------------------------------------
// ValueDictC — dictionary + bit-packed codes, `T: IndexLike`. Delegates to the
// existing verified `ValFrame` (the value-major cold tier).
// ---------------------------------------------------------------------------

/// Dictionary + narrow/bit-packed codes for id-like values.
///
/// A struct column cannot instantiate it; the pairing is rejected at the type
/// level, not at runtime:
///
/// ```compile_fail
/// use semi_persistent_containers_verus::value_compressor::{ValueCompressor, ValueDictC};
/// #[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, Default)]
/// struct CacheEntryLike { a: u32, b: u32 }
/// // No `IndexLike` for the struct, so `ValueDictC` has no impl for it.
/// fn reject(vals: &Vec<CacheEntryLike>) {
///     let _ = <ValueDictC as ValueCompressor<CacheEntryLike>>::compress(vals);
/// }
/// ```
///
/// The same rejection at the COLUMN type (F2.3): a struct-element `Vec`
/// declared with the dictionary strategy does not name a type.
///
/// ```compile_fail
/// use semi_persistent_containers_verus::vec::Vec as SpVec;
/// use semi_persistent_containers_verus::parallel_store::ParallelStore;
/// use semi_persistent_containers_verus::value_compressor::ValueDictC;
/// #[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, Default)]
/// struct CacheEntryLike { a: u32, b: u32 }
/// fn reject(_v: SpVec<CacheEntryLike, u32,
///     ParallelStore<CacheEntryLike, u32>, true, ValueDictC>) {}
/// ```
pub struct ValueDictC;

impl<T: IndexLike> ValueCompressor<T> for ValueDictC {
    type Compressed = ValFrame<T>;

    open spec fn decode(c: &ValFrame<T>) -> Seq<T> {
        c.decode()
    }

    open spec fn cwf(c: &ValFrame<T>) -> bool {
        c.wf()
    }

    fn compress(vals: &Vec<T>) -> (c: ValFrame<T>) {
        ValFrame::compress(vals)
    }

    fn decoded_len(c: &ValFrame<T>) -> (n: usize) {
        c.len()
    }

    fn decode_at(c: &ValFrame<T>, i: usize) -> (v: T) {
        c.decode_at(i)
    }

    fn byte_len(c: &ValFrame<T>) -> usize {
        c.byte_len()
    }

    fn enabled() -> bool {
        true
    }
}

// ---------------------------------------------------------------------------
// ValueDelta — successive-difference coding, `T: IndexLike` (see the module
// doc for the recorded deviation from "against the cell index").
// ---------------------------------------------------------------------------

/// First value verbatim, then per-entry `(negative, magnitude)` against the
/// previous decoded value. The ghost `model` is the decoded sequence; `cwf`
/// ties the stored columns to it step by step, which is what keeps the replay
/// arithmetic in range (every intermediate equals a model value, and model
/// values are bounded).
pub struct DeltaVals<T> {
    pub model: Ghost<Seq<T>>,
    pub first: Vec<T>,
    pub steps: Vec<(bool, usize)>,
}

pub struct ValueDelta;

impl<T: IndexLike> ValueCompressor<T> for ValueDelta {
    type Compressed = DeltaVals<T>;

    open spec fn decode(c: &DeltaVals<T>) -> Seq<T> {
        c.model@
    }

    open spec fn cwf(c: &DeltaVals<T>) -> bool {
        &&& c.model@.len() <= usize::MAX as nat
        &&& c.first@.len() == (if c.model@.len() == 0 { 0int } else { 1int })
        &&& (c.model@.len() > 0 ==> c.first@[0] == c.model@[0])
        &&& c.steps@.len() as int
            == (if c.model@.len() == 0 { 0int } else { c.model@.len() - 1 })
        &&& forall|t: int| 0 <= t < c.model@.len()
                ==> (#[trigger] c.model@[t]).as_nat() < T::max_nat()
        &&& forall|t: int| 0 <= t < c.steps@.len() ==> {
            let prev = (#[trigger] c.model@[t]).as_nat();
            let cur = c.model@[t + 1].as_nat();
            if c.steps@[t].0 {
                prev >= c.steps@[t].1 as nat && cur == prev - c.steps@[t].1 as nat
            } else {
                cur == prev + c.steps@[t].1 as nat
            }
        }
    }

    fn compress(vals: &Vec<T>) -> (c: DeltaVals<T>) {
        let n = vals.len();
        let mut first: Vec<T> = Vec::new();
        let mut steps: Vec<(bool, usize)> = Vec::new();
        proof { assert(vals@.len() == n as nat); }
        if n == 0 {
            return DeltaVals { model: Ghost(vals@), first, steps };
        }
        let head = vals[0];
        proof { head.lemma_as_nat_bounded(); }
        first.push(head);
        let mut i: usize = 1;
        while i < n
            invariant
                1 <= i <= n,
                n == vals@.len(),
                first@.len() == 1,
                first@[0] == vals@[0],
                steps@.len() == i - 1,
                forall|t: int| 0 <= t < i
                    ==> (#[trigger] vals@[t]).as_nat() < T::max_nat(),
                forall|t: int| 0 <= t < steps@.len() ==> {
                    let prev = (#[trigger] vals@[t]).as_nat();
                    let cur = vals@[t + 1].as_nat();
                    if steps@[t].0 {
                        prev >= steps@[t].1 as nat && cur == prev - steps@[t].1 as nat
                    } else {
                        cur == prev + steps@[t].1 as nat
                    }
                },
            decreases n - i,
        {
            let pv = vals[i - 1];
            let cv = vals[i];
            proof { cv.lemma_as_nat_bounded(); }
            let prev = pv.as_usize();
            let cur = cv.as_usize();
            if cur >= prev {
                steps.push((false, cur - prev));
            } else {
                steps.push((true, prev - cur));
            }
            i += 1;
        }
        DeltaVals { model: Ghost(vals@), first, steps }
    }

    fn decoded_len(c: &DeltaVals<T>) -> (n: usize) {
        if c.first.len() == 0 {
            0
        } else {
            c.steps.len() + 1
        }
    }

    fn decode_at(c: &DeltaVals<T>, i: usize) -> (v: T) {
        // Replay the steps up to `i`; each replayed value equals the model's,
        // so the arithmetic stays in `T`'s range by that equality.
        let mut cur = c.first[0];
        let mut t: usize = 0;
        while t < i
            invariant
                t <= i,
                (i as nat) < c.model@.len(),
                <ValueDelta as ValueCompressor<T>>::cwf(c),
                cur == c.model@[t as int],
            decreases i - t,
        {
            let (neg, mag) = c.steps[t];
            let prev_usize = cur.as_usize();
            proof {
                T::lemma_max_nat_fits_usize();
                // Instantiate the step and boundedness clauses at `t`.
                assert(c.model@[t as int].as_nat() < T::max_nat());
                assert(c.model@[t as int + 1].as_nat() < T::max_nat());
                if c.steps@[t as int].0 {
                    assert(c.model@[t as int].as_nat() >= c.steps@[t as int].1 as nat);
                } else {
                    assert(c.model@[t as int + 1].as_nat()
                        == c.model@[t as int].as_nat() + c.steps@[t as int].1 as nat);
                }
            }
            let next_usize = if neg { prev_usize - mag } else { prev_usize + mag };
            proof {
                assert(next_usize as nat == c.model@[t as int + 1].as_nat());
            }
            let next = match T::try_from_usize(next_usize) {
                Some(x) => x,
                None => {
                    proof { assert(false); }
                    cur
                }
            };
            proof {
                T::lemma_as_nat_injective(next, c.model@[t as int + 1]);
            }
            cur = next;
            t += 1;
        }
        cur
    }

    fn byte_len(c: &DeltaVals<T>) -> usize {
        crate::compression_stats::sat_add(
            crate::compression_stats::sat_mul(c.first.len(), core::mem::size_of::<T>()),
            crate::compression_stats::sat_mul(
                c.steps.len(),
                crate::compression_stats::sat_add(1, core::mem::size_of::<usize>())))
    }

    fn enabled() -> bool {
        true
    }
}

} // verus!

macro_rules! eq_spec_prim {
    ($($t:ty),*) => {
        verus! {
        $(
        impl EqSpec for $t {
            fn eq_exec(&self, other: &Self) -> (r: bool)
                ensures r == (self == other),
            {
                *self == *other
            }
        }
        )*
        }
    };
}

eq_spec_prim!(u8, u16, u32, u64, usize);
