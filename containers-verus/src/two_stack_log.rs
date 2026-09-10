// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! The two-stack diff log: a plain mutable top and a compressed read-only bottom
//! with an activate-on-mark compression API
//! (`doc/design/09-diff-stack-compression.md`).
//!
//! `TwoStackLog<T, I>` keeps the recent, still-mutable frames plain (`hot`, a
//! `DiffLog`) and the older, finalized frames compressed (`cold`, a
//! `CompressedStack`). Its **abstract view is the flat `Seq<(T, I)>`**
//! `cold@ ++ hot@` — the same diff sequence a single plain log would present — so
//! it is a drop-in history representation. `mark` opens a frame boundary and, if
//! the column's policy fires, flushes the cold hot-frames into the compressed
//! bottom (`flush_cold`): "when compression is activated on mark, the uncompressed
//! top frames are compressed into the compressed stack." The flush preserves the
//! flat view exactly, by the `CompressedStack` push bijection, so no diff is lost
//! or reordered across the boundary.

use crate::compressed_stack::CompressedStack;
use crate::compression_config::ColumnConfig;
use crate::diff_log::DiffLog;
use crate::index_like::{IndexFromNat, IndexLike};
use vstd::multiset::Multiset;
use vstd::prelude::*;

verus! {

pub struct TwoStackLog<T: Copy, I> {
    /// Compressed, read-only bottom (older finalized frames).
    pub cold: CompressedStack<T, I>,
    /// Plain, mutable top (recent frames, including the active one).
    pub hot: DiffLog<T, I>,
    /// Start offset of each hot frame within `hot@`. `hot_starts[0] == 0`; the
    /// last frame is the active one, its diffs `hot@[hot_starts.last()..]`.
    pub hot_starts: Vec<usize>,
    pub config: ColumnConfig,
}

impl<T: IndexLike, I: IndexFromNat> View for TwoStackLog<T, I> {
    type V = Seq<(T, I)>;
    open spec fn view(&self) -> Seq<(T, I)> {
        self.cold@ + self.hot@
    }
}

impl<T: IndexLike, I: IndexFromNat> TwoStackLog<T, I> {
    pub open spec fn wf(&self) -> bool {
        &&& self.cold.wf()
        &&& self.hot.wf()
        // There is always at least the active frame; it opens at the hot front,
        // so the frames tile `hot@` in order.
        &&& self.hot_starts@.len() > 0
        &&& self.hot_starts@[0] == 0
        &&& forall|k: int| 0 <= k < self.hot_starts@.len() ==>
                (#[trigger] self.hot_starts@[k]) <= self.hot@.len()
        &&& forall|a: int, b: int| 0 <= a <= b < self.hot_starts@.len() ==>
                (#[trigger] self.hot_starts@[a]) <= (#[trigger] self.hot_starts@[b])
    }

    /// The exclusive end of hot frame `j`: the next frame's start, or (for the
    /// active, last frame) the hot top.
    pub open spec fn hot_hi(&self, j: int) -> int {
        if j + 1 < self.hot_starts@.len() {
            self.hot_starts@[j + 1] as int
        } else {
            self.hot@.len() as int
        }
    }

    /// The write multiset of hot frame `j` (its slice of `hot@`).
    pub open spec fn hot_frame_mset(&self, j: int) -> Multiset<(T, I)> {
        self.hot@.subrange(self.hot_starts@[j] as int, self.hot_hi(j)).to_multiset()
    }

    /// The per-frame write multisets of the hot (uncompressed) top, in order.
    pub open spec fn hot_frame_msets(&self) -> Seq<Multiset<(T, I)>> {
        Seq::new(self.hot_starts@.len(), |j: int| self.hot_frame_mset(j))
    }

    /// The two-stack's semantic contract: one write multiset per frame, cold frames
    /// then hot frames, in stack order. Order-insensitive WITHIN a frame (each cell
    /// is written once in a finalized frame, so the restore overlay is determined by
    /// the per-frame write set), which is what lets a reordering encoder
    /// (`IndexRunsSorted`) flush a frame while preserving this view. The flat `@`
    /// (`cold@ ++ hot@`) is only one linearization and is NOT preserved across a
    /// flush that reorders; `frame_msets` is.
    pub open spec fn frame_msets(&self) -> Seq<Multiset<(T, I)>> {
        self.cold.frame_msets() + self.hot_frame_msets()
    }

    /// An empty two-stack log with the given column configuration. Seeds one
    /// (empty) active frame at offset 0, so `hot_starts` is never empty and its
    /// first element stays 0 (it is only ever extended at the end or rebased to
    /// 0 by a flush).
    pub fn new(config: ColumnConfig) -> (r: TwoStackLog<T, I>)
        ensures
            r.wf(),
            r@ == Seq::<(T, I)>::empty(),
            r.frame_msets() == seq![Multiset::<(T, I)>::empty()],
    {
        // Not `vec![0]`: that macro expands to a let expression, which Verus
        // does not support.
        #[allow(clippy::vec_init_then_push)]
        let mut hot_starts: Vec<usize> = Vec::new();
        hot_starts.push(0);
        let r = TwoStackLog {
            cold: CompressedStack::new(),
            hot: DiffLog::new_plain(),
            hot_starts,
            config,
        };
        assert(r@ =~= Seq::<(T, I)>::empty());
        assert(r.hot_starts@[0] == 0);
        // One empty active frame: hot_frame_msets == [empty], cold empty.
        proof {
            broadcast use vstd::seq_lib::group_to_multiset_ensures;
            assert(r.hot_starts@.len() == 1);
            assert(r.hot_hi(0) == 0);
            assert(r.hot@.subrange(0, 0) =~= Seq::<(T, I)>::empty());
            assert(r.hot_frame_mset(0) =~= Multiset::<(T, I)>::empty());
            assert(r.hot_frame_msets() =~= seq![Multiset::<(T, I)>::empty()]);
            assert(r.frame_msets() =~= seq![Multiset::<(T, I)>::empty()]);
        }
        r
    }

    /// Total entries across both stacks (the flat view length).
    pub open spec fn len_spec(&self) -> nat {
        self@.len()
    }

    /// Append one diff to the active (top) frame. The active frame is always the
    /// last, so its write multiset gains `(t, idx)` and every other frame's is
    /// unchanged.
    pub fn push(&mut self, t: T, idx: I)
        requires old(self).wf(),
        ensures
            final(self).wf(),
            final(self)@ == old(self)@.push((t, idx)),
            final(self).frame_msets() == old(self).frame_msets().update(
                old(self).frame_msets().len() - 1,
                old(self).frame_msets()[old(self).frame_msets().len() - 1].insert((t, idx))),
    {
        let ghost hot0 = self.hot@;
        let ghost L = self.hot_starts@.len();
        self.hot.push(t, idx);
        assert(self@ =~= old(self)@.push((t, idx)));
        assert(self.hot@ =~= hot0.push((t, idx)));
        assert forall|k: int| 0 <= k < self.hot_starts@.len() implies
            (#[trigger] self.hot_starts@[k]) <= self.hot@.len() by {
            assert(self.hot_starts@[k] <= old(self).hot@.len());
        }
        // The last hot frame's slice grows by (t, idx); every earlier frame's slice
        // (ending at a fixed start <= old hot len) is unchanged.
        let ghost active = (L - 1) as int;
        assert(self.hot_frame_mset(active)
            == old(self).hot_frame_mset(active).insert((t, idx))) by {
            let lo = self.hot_starts@[active] as int;
            assert(self.hot_hi(active) == hot0.len() as int + 1);
            assert(old(self).hot_hi(active) == hot0.len() as int);
            assert(self.hot@.subrange(lo, hot0.len() as int + 1)
                =~= hot0.subrange(lo, hot0.len() as int).push((t, idx)));
            hot0.subrange(lo, hot0.len() as int).to_multiset_ensures();
            assert(hot0.subrange(lo, hot0.len() as int).push((t, idx)).to_multiset()
                =~= hot0.subrange(lo, hot0.len() as int).to_multiset().insert((t, idx)));
        }
        assert forall|j: int| 0 <= j < active implies
            self.hot_frame_mset(j) == old(self).hot_frame_mset(j) by {
            assert(self.hot_hi(j) == old(self).hot_hi(j));
            assert(self.hot_hi(j) <= hot0.len());
            assert(self.hot@.subrange(self.hot_starts@[j] as int, self.hot_hi(j))
                =~= hot0.subrange(self.hot_starts@[j] as int, self.hot_hi(j)));
        }
        assert(self.frame_msets() =~= old(self).frame_msets().update(
            old(self).frame_msets().len() - 1,
            old(self).frame_msets()[old(self).frame_msets().len() - 1].insert((t, idx))));
    }

    /// Number of hot (uncompressed) frames.
    pub fn num_hot_frames(&self) -> (n: usize)
        ensures n == self.hot_starts@.len(),
    {
        self.hot_starts.len()
    }

    /// Number of compressed frames.
    pub fn num_cold_frames(&self) -> (n: usize)
        ensures n == self.cold.frames@.len(),
    {
        self.cold.num_frames()
    }

    /// Open a new frame boundary at the current hot top (a `mark`). The just
    /// active frame closes; a fresh empty active frame opens.
    pub fn open_frame(&mut self)
        requires old(self).wf(),
        ensures
            final(self).wf(),
            final(self)@ == old(self)@,
            final(self).frame_msets() == old(self).frame_msets().push(Multiset::empty()),
    {
        let ghost hot0 = self.hot@;
        let ghost starts0 = self.hot_starts@;
        let ghost L = starts0.len();
        let n = self.hot.len();
        self.hot_starts.push(n);
        assert(self@ =~= old(self)@);
        assert(self.hot_starts@[self.hot_starts@.len() - 1] == n as int);
        assert(self.hot_starts@[0] == old(self).hot_starts@[0]);
        assert forall|a: int, b: int| 0 <= a <= b < self.hot_starts@.len() implies
            (#[trigger] self.hot_starts@[a]) <= (#[trigger] self.hot_starts@[b]) by {
            if b < old(self).hot_starts@.len() {
                assert(self.hot_starts@[a] == old(self).hot_starts@[a]);
                assert(self.hot_starts@[b] == old(self).hot_starts@[b]);
            } else {
                // b is the new last element (== hot.len()); a is old or new.
                if a < old(self).hot_starts@.len() {
                    assert(self.hot_starts@[a] == old(self).hot_starts@[a]);
                    assert(self.hot_starts@[a] <= old(self).hot@.len());
                }
            }
        }
        // The previously-active frame keeps the same slice (its end was hot.len(),
        // now pinned as the next start = hot.len()); a fresh empty active frame is
        // appended. So hot_frame_msets grows by one empty multiset.
        assert(self.hot_frame_msets() =~= old(self).hot_frame_msets().push(Multiset::empty())) by {
            assert forall|j: int| 0 <= j < L implies
                self.hot_frame_mset(j) == old(self).hot_frame_mset(j) by {
                assert(self.hot_hi(j) == old(self).hot_hi(j));
            }
            assert(self.hot_frame_mset(L as int)
                =~= Multiset::<(T, I)>::empty()) by {
                broadcast use vstd::seq_lib::group_to_multiset_ensures;
                assert(self.hot_starts@[L as int] == n);
                assert(n == hot0.len());
                assert(self.hot_hi(L as int) == hot0.len() as int);
                assert(self.hot@.subrange(n as int, hot0.len() as int)
                    =~= Seq::<(T, I)>::empty());
            }
        }
        assert(self.frame_msets() =~= old(self).frame_msets().push(Multiset::empty()));
    }

    /// Compress the first `k` hot frames into the cold bottom and drop them from
    /// the hot top. `k` must leave at least the active frame hot. The flat view
    /// is unchanged: the `k` compressed frames' decodes tile exactly the hot
    /// prefix that is dropped. `mode` selects the encoder for these frames
    /// (`Auto` for per-frame exact-size selection during calibration; a promoted
    /// default in steady state); the view is preserved for any mode, so the proof
    /// does not depend on the choice.
    pub fn flush_cold(&mut self, k: usize, mode: crate::diff_compress::CompressionMode)
        requires
            old(self).wf(),
            k < old(self).hot_starts@.len(),
        ensures
            final(self).wf(),
            final(self).frame_msets() == old(self).frame_msets(),
    {
        let ghost hot0 = self.hot@;
        let ghost starts0 = self.hot_starts@;
        let ghost cold0_msets = self.cold.frame_msets();
        let ghost L = starts0.len();
        // `G(j)` is old hot frame j's write multiset (the slice `[starts0[j], hi(j))`
        // where `hi(j)` is the next start, or `hot0.len()` for the active last
        // frame). For j < k <= L-1 the next start exists, so the flushed frames'
        // multisets match what `push_frame` records.
        // `H(j) == old(self).hot_frame_mset(j)` is old hot frame j's write multiset
        // (a real spec fn, so it reduces reliably where a local closure would not).
        // Properties of the immutable ghosts, from the entry wf.
        assert(starts0[0] == 0);
        assert(forall|j: int| 0 <= j < L ==> #[trigger] starts0[j] <= hot0.len());
        assert(forall|a: int, b: int| 0 <= a <= b < L ==>
            #[trigger] starts0[a] <= #[trigger] starts0[b]);
        let mut f: usize = 0;
        while f < k
            invariant
                k < self.hot_starts@.len(),
                self.hot@ == hot0,
                self.hot_starts@ == starts0,
                self.hot.wf(),
                starts0[0] == 0,
                L == starts0.len(),
                forall|j: int| 0 <= j < L ==> #[trigger] starts0[j] <= hot0.len(),
                forall|a: int, b: int| 0 <= a <= b < L ==>
                    #[trigger] starts0[a] <= #[trigger] starts0[b],
                0 <= f <= k,
                k < L,
                self.cold.wf(),
                // Flushed frames' multisets accumulate onto cold, in order.
                self.cold.frame_msets() =~= cold0_msets
                    + Seq::new(f as nat, |j: int| old(self).hot_frame_mset(j)),
            decreases k - f,
        {
            let lo = self.hot_starts[f];
            let hi = self.hot_starts[f + 1];
            assert(lo <= hi <= hot0.len());
            let diffs = self.hot.subrange_vec(lo, hi);
            // For f < k <= L-1, old hot frame f is exactly this slice's multiset.
            assert(lo == starts0[f as int]);
            assert(hi == starts0[f as int + 1]);
            assert(f as int + 1 < L);
            assert(old(self).hot_hi(f as int) == hi as int);
            assert(diffs@ =~= hot0.subrange(lo as int, hi as int));
            assert(old(self).hot_frame_mset(f as int)
                == hot0.subrange(lo as int, hi as int).to_multiset());
            assert(diffs@.to_multiset() == old(self).hot_frame_mset(f as int));
            self.cold.push_frame(&diffs, mode);
            proof {
                // Seq::new(f+1, H) == Seq::new(f, H).push(H(f)); and (A + B).push(x)
                // == A + B.push(x).
                assert(Seq::new((f + 1) as nat, |j: int| old(self).hot_frame_mset(j))
                    =~= Seq::new(f as nat, |j: int| old(self).hot_frame_mset(j))
                        .push(old(self).hot_frame_mset(f as int)));
                assert((cold0_msets + Seq::new(f as nat, |j: int| old(self).hot_frame_mset(j)))
                        .push(old(self).hot_frame_mset(f as int))
                    =~= cold0_msets + Seq::new(f as nat, |j: int| old(self).hot_frame_mset(j))
                        .push(old(self).hot_frame_mset(f as int)));
            }
            f += 1;
        }
        // After the loop, cold.frame_msets() == cold0_msets + [H(0)..H(k-1)].
        let m = self.hot_starts[k];
        assert(m == starts0[k as int]);
        assert(self.cold.frame_msets()
            =~= cold0_msets + Seq::new(k as nat, |j: int| old(self).hot_frame_mset(j)));
        self.hot.drop_front(m);
        assert(self.hot@ =~= hot0.subrange(m as int, hot0.len() as int));

        // Rebuild hot_starts: keep frames [k, len), rebased by `m`.
        let ghost old_starts = self.hot_starts@;
        let mut new_starts: Vec<usize> = Vec::new();
        let slen = self.hot_starts.len();
        let mut i: usize = k;
        while i < slen
            invariant
                k <= i <= slen,
                k < starts0.len(),
                slen == self.hot_starts@.len(),
                self.hot_starts@ == old_starts,
                old_starts == starts0,
                m == starts0[k as int],
                forall|a: int, b: int| 0 <= a <= b < starts0.len() ==>
                    #[trigger] starts0[a] <= #[trigger] starts0[b],
                new_starts@.len() == i - k,
                forall|j: int| 0 <= j < i - k ==>
                    #[trigger] new_starts@[j] == (starts0[k + j] - m) as int,
            decreases slen - i,
        {
            let v = self.hot_starts[i];
            proof {
                assert(v == starts0[i as int]);
                assert(starts0[k as int] <= starts0[i as int]);
                assert(v >= m);
            }
            new_starts.push(v - m);
            i += 1;
        }
        self.hot_starts = new_starts;

        proof {
            // wf for the rebuilt hot_starts.
            assert(self.hot@.len() == hot0.len() - m);
            assert(self.hot_starts@.len() == L - k);
            if self.hot_starts@.len() > 0 {
                assert(self.hot_starts@[0] == (starts0[k as int] - m) as int);
                assert(starts0[k as int] == m);
            }
            assert forall|j: int| 0 <= j < self.hot_starts@.len() implies
                (#[trigger] self.hot_starts@[j]) <= self.hot@.len() by {
                assert(self.hot_starts@[j] == (starts0[k + j] - m) as int);
                assert(starts0[k + j] <= hot0.len());
            }
            assert forall|a: int, b: int| 0 <= a <= b < self.hot_starts@.len() implies
                (#[trigger] self.hot_starts@[a]) <= (#[trigger] self.hot_starts@[b]) by {
                assert(self.hot_starts@[a] == (starts0[k + a] - m) as int);
                assert(self.hot_starts@[b] == (starts0[k + b] - m) as int);
                assert(starts0[k + a] <= starts0[k + b]);
            }
            // The surviving hot frames are exactly the old frames [k, L): each new
            // frame i is old frame k+i (its slice shifted back by m).
            assert(self.hot_frame_msets()
                =~= Seq::new((L - k) as nat, |i: int| old(self).hot_frame_mset(k + i))) by {
                assert forall|i: int| 0 <= i < L - k implies
                    self.hot_frame_mset(i) == old(self).hot_frame_mset(k + i) by {
                    let lo_i = self.hot_starts@[i] as int;
                    assert(lo_i == starts0[k + i] as int - m as int);
                    // new hot_hi(i) shifts old hot_hi(k+i) back by m.
                    if i + 1 < L - k {
                        assert(self.hot_hi(i) == self.hot_starts@[i + 1] as int);
                        assert(self.hot_hi(i) == starts0[k + i + 1] as int - m as int);
                        assert(old(self).hot_hi(k + i) == starts0[k + i + 1] as int)
                            by { assert(k + i + 1 < L); }
                    } else {
                        assert(self.hot_hi(i) == self.hot@.len() as int);
                        assert(self.hot_hi(i) == hot0.len() as int - m as int);
                        assert(old(self).hot_hi(k + i) == hot0.len() as int)
                            by { assert(!(k + i + 1 < L)); }
                    }
                    // slice shift: hot0[m..].subrange(a-m, b-m) == hot0.subrange(a, b).
                    assert(self.hot@.subrange(lo_i, self.hot_hi(i))
                        =~= hot0.subrange(starts0[k + i] as int, old(self).hot_hi(k + i)));
                }
            }
            // Combine: cold gets H[0..k), hot keeps H[k..L); concatenation is the
            // whole H[0..L) == old hot frame msets, so frame_msets is preserved.
            assert(Seq::new(k as nat, |j: int| old(self).hot_frame_mset(j))
                    + Seq::new((L - k) as nat, |i: int| old(self).hot_frame_mset(k + i))
                =~= Seq::new(L, |j: int| old(self).hot_frame_mset(j)));
            assert(old(self).hot_frame_msets()
                =~= Seq::new(L, |j: int| old(self).hot_frame_mset(j)));
            assert(self.frame_msets() =~= old(self).frame_msets());
        }
    }

    /// `mark`: open a frame boundary, then activate compression per the column's
    /// policy — if the trigger fires, flush the cold hot-frames (all but the
    /// `keep_hot_frames` most recent) into the compressed bottom. `uncompressed`
    /// and `base` are the byte sizes the size-fraction trigger reads. The flat
    /// view is unchanged.
    pub fn mark(&mut self, uncompressed_bytes: usize, base_bytes: usize)
        requires old(self).wf(),
        ensures
            final(self).wf(),
            final(self).frame_msets() == old(self).frame_msets().push(Multiset::empty()),
    {
        self.open_frame();
        // open_frame appended the empty active frame; flush_cold (if it fires)
        // preserves frame_msets, so the post-mark contract is the same either way.
        if self.config.should_flush(uncompressed_bytes, base_bytes) {
            let nframes = self.hot_starts.len();
            let want = self.config.frames_to_compress(nframes);
            // Never flush the active (last) frame: keep k < nframes. wf gives
            // nframes >= 1, so nframes - 1 is safe.
            let k = if want < nframes { want } else { nframes - 1 };
            if k < nframes {
                self.flush_cold(k, self.config.scheme);
            }
        }
    }

    /// Restore within the hot region: truncate the plain top to `hot_n` entries,
    /// dropping the hot frames that started above it. The common near-backtrack,
    /// which the `keep_hot_frames` floor guarantees stays plain (no decode). The
    /// flat view becomes `cold@ ++ hot@[0..hot_n]`. Deeper backtracks into the
    /// compressed region first materialize the needed frames back to the top (a
    /// later addition; `CompressedStack::pop_frame` is the primitive).
    pub fn truncate_hot(&mut self, hot_n: usize)
        requires old(self).wf(), hot_n <= old(self).hot@.len(),
        ensures
            final(self).wf(),
            final(self)@ == old(self).cold@ + old(self).hot@.subrange(0, hot_n as int),
    {
        let ghost hot0 = self.hot@;
        let ghost starts0 = self.hot_starts@;
        self.hot.truncate(hot_n);
        assert(self.hot@ =~= hot0.subrange(0, hot_n as int));
        // Keep the sorted-prefix of frame starts that are <= hot_n. Frame 0's
        // start is 0 <= hot_n, so at least one frame survives.
        let mut c: usize = self.hot_starts.len();
        while c > 0 && self.hot_starts[c - 1] > hot_n
            invariant
                0 <= c <= self.hot_starts@.len(),
                self.hot_starts@ == starts0,
                starts0[0] == 0,
                forall|a: int, b: int| 0 <= a <= b < starts0.len() ==>
                    #[trigger] starts0[a] <= #[trigger] starts0[b],
                // everything at or above c is above hot_n.
                forall|j: int| c <= j < starts0.len() ==> #[trigger] starts0[j] > hot_n,
            decreases c,
        {
            c -= 1;
        }
        proof {
            // c >= 1: index 0 has start 0 <= hot_n, so the loop cannot drop it.
            if c == 0 {
                assert(starts0[0] > hot_n);
                assert(starts0[0] == 0);
            }
        }
        self.hot_starts.truncate(c);
        proof {
            assert(self@ =~= old(self).cold@ + hot0.subrange(0, hot_n as int));
            assert(self.hot_starts@[0] == 0);
            assert forall|j: int| 0 <= j < self.hot_starts@.len() implies
                (#[trigger] self.hot_starts@[j]) <= self.hot@.len() by {
                assert(self.hot_starts@[j] == starts0[j]);
                // j < c, so starts0[j] <= hot_n == new hot len (sorted, not > hot_n).
                assert(!(starts0[j] > hot_n));
            }
            assert forall|a: int, b: int| 0 <= a <= b < self.hot_starts@.len() implies
                (#[trigger] self.hot_starts@[a]) <= (#[trigger] self.hot_starts@[b]) by {
                assert(self.hot_starts@[a] == starts0[a]);
                assert(self.hot_starts@[b] == starts0[b]);
            }
        }
    }

    // -- monitoring --------------------------------------------------------

    /// Heap bytes held by the uncompressed (hot) top.
    pub fn hot_bytes(&self) -> usize {
        self.hot.heap_bytes()
    }

    /// Heap bytes held by the compressed (cold) bottom.
    pub fn cold_bytes(&self) -> usize {
        self.cold.heap_bytes()
    }
}

} // verus!
