// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! The compressed bottom of the two-stack diff history
//! (`doc/design/09-diff-stack-compression.md`).
//!
//! A `Vec`'s diff history is split into two stacks: a plain, mutable top (the
//! active and hot frames, a `DiffLog`) and this compressed, read-only bottom (the
//! cold finalized frames). `CompressedStack<T, I>` holds one `FrameEncoding` per
//! compressed frame; its **abstract view is the flat `Seq<(T, I)>`** obtained by
//! concatenating every frame's `decode()`, in stack order. Because each encoder is
//! bijective (`decode(compress_frame(d)) == d`), pushing a frame extends the view
//! by exactly the diffs it was built from and popping it removes exactly them, so
//! the two-stack presents the same flat diff sequence a single plain log would —
//! which is what lets `Vec`'s mark/restore proofs, stated over that flat view,
//! carry across the split.

use crate::diff_compress::{CompressionMode, FrameEncoding, compress_frame};
use crate::index_like::{IndexFromNat, IndexLike};
use vstd::multiset::Multiset;
use vstd::prelude::*;

verus! {

/// Flat decode of a frame sequence: concatenate each frame's `decode()`, in
/// order. The stack's abstract view.
pub open spec fn decode_all<T: IndexLike, I: IndexFromNat>(
    frames: Seq<FrameEncoding<T, I>>,
) -> Seq<(T, I)>
    decreases frames.len(),
{
    if frames.len() == 0 {
        Seq::empty()
    } else {
        frames[0].decode() + decode_all(frames.subrange(1, frames.len() as int))
    }
}

/// Appending a frame extends the flat decode by exactly that frame's decode.
/// The inductive step reassociates the three concrete sub-sequences by hand
/// (Verus does not reassociate `+` over the recursive subterm on its own),
/// mirroring `diff_compress::lemma_expand_runs_snoc`.
pub proof fn lemma_decode_all_snoc<T: IndexLike, I: IndexFromNat>(
    frames: Seq<FrameEncoding<T, I>>,
    f: FrameEncoding<T, I>,
)
    ensures
        decode_all(frames.push(f)) == decode_all(frames) + f.decode(),
    decreases frames.len(),
{
    reveal_with_fuel(decode_all, 2);
    if frames.len() == 0 {
        assert(frames.push(f) =~= seq![f]);
        assert(decode_all(frames) =~= Seq::<(T, I)>::empty());
        assert(decode_all(frames.push(f)) =~= f.decode());
        assert(decode_all(frames) + f.decode() =~= f.decode());
    } else {
        let head = frames[0];
        let tail = frames.subrange(1, frames.len() as int);
        lemma_decode_all_snoc(tail, f);
        assert(frames.push(f)[0] == head);
        assert(frames.push(f).subrange(1, frames.push(f).len() as int) =~= tail.push(f));
        assert(decode_all(frames.push(f))
            == head.decode() + decode_all(tail.push(f)));
        let a = head.decode();
        let b = decode_all(tail);
        let c = f.decode();
        // IH: decode_all(tail.push(f)) == b + c; reassociate a + (b + c) == (a + b) + c.
        assert(a + (b + c) =~= (a + b) + c);
        assert(decode_all(frames) == a + b);
    }
}

/// The compressed, read-only bottom of the two-stack diff history.
pub struct CompressedStack<T, I> {
    pub frames: Vec<FrameEncoding<T, I>>,
}

impl<T: IndexLike, I: IndexFromNat> View for CompressedStack<T, I> {
    type V = Seq<(T, I)>;
    open spec fn view(&self) -> Seq<(T, I)> {
        decode_all(self.frames@)
    }
}

impl<T: IndexLike, I: IndexFromNat> CompressedStack<T, I> {
    pub open spec fn wf(&self) -> bool {
        forall|k: int| 0 <= k < self.frames@.len() ==> (#[trigger] self.frames@[k]).wf()
    }

    /// The per-frame write multiset: one `Multiset` per compressed frame, in stack
    /// order. This is the order-insensitive contract the reordering encoders
    /// (`IndexRunsSorted`) satisfy where the flat `@` cannot: within a finalized
    /// frame each cell is written once, so the restore overlay depends only on the
    /// per-frame write set, not its linearization. `decode_all`/`@` remains a valid
    /// flat linearization (used by `pop_frame` to materialize a frame back), but
    /// `frame_msets` is what `push_frame`/`flush_cold` preserve for every mode.
    pub open spec fn frame_msets(&self) -> Seq<Multiset<(T, I)>> {
        Seq::new(self.frames@.len(), |k: int| self.frames@[k].decode().to_multiset())
    }

    /// An empty compressed stack (the state when compression is off, or before
    /// the first flush).
    pub fn new() -> (r: CompressedStack<T, I>)
        ensures
            r.wf(),
            r@ == Seq::<(T, I)>::empty(),
            r.frame_msets() == Seq::<Multiset<(T, I)>>::empty(),
    {
        let r = CompressedStack { frames: Vec::new() };
        assert(r@ =~= Seq::<(T, I)>::empty());
        assert(r.frame_msets() =~= Seq::<Multiset<(T, I)>>::empty());
        r
    }

    /// Number of compressed frames (the stack depth, not the decoded entry count).
    pub fn num_frames(&self) -> (n: usize)
        ensures n == self.frames@.len(),
    {
        self.frames.len()
    }

    /// Compress `diffs` in `mode` and push it as the new top compressed frame.
    /// Extends `frame_msets` by exactly `diffs@`'s write multiset (encoder multiset
    /// contract + snoc). The flat `@` also extends, by the frame's own `decode()`
    /// (which is `diffs@` for the order-preserving modes and a permutation of it for
    /// `IndexRunsSorted`); the per-frame multiset is the mode-independent guarantee.
    pub fn push_frame(&mut self, diffs: &Vec<(T, I)>, mode: CompressionMode)
        requires old(self).wf(),
        ensures
            final(self).wf(),
            final(self).frame_msets() == old(self).frame_msets().push(diffs@.to_multiset()),
    {
        let f = compress_frame(diffs, mode);
        let ghost fg = f;
        self.frames.push(f);
        assert(self.frames@ =~= old(self).frames@.push(fg));
        assert forall|k: int| 0 <= k < self.frames@.len()
            implies (#[trigger] self.frames@[k]).wf() by {
            if k < old(self).frames@.len() {
                assert(self.frames@[k] == old(self).frames@[k]);
            } else {
                assert(self.frames@[k] == fg);
            }
        }
        // frame_msets extends by fg.decode().to_multiset() == diffs@.to_multiset().
        assert(fg.decode().to_multiset() == diffs@.to_multiset());
        assert(self.frame_msets() =~= old(self).frame_msets().push(diffs@.to_multiset())) by {
            assert(self.frame_msets().len() == old(self).frame_msets().len() + 1);
            assert forall|k: int| 0 <= k < old(self).frames@.len() implies
                self.frame_msets()[k] == old(self).frame_msets()[k] by {
                assert(self.frames@[k] == old(self).frames@[k]);
            }
        }
    }

    /// Decode and remove the top compressed frame, returning its flat diffs.
    /// `old@ == final@ + r@`: the popped frame was the view's suffix, so the
    /// two-stack restore can materialize it back onto the plain top.
    pub fn pop_frame(&mut self) -> (r: Vec<(T, I)>)
        requires old(self).wf(), old(self).frames@.len() > 0,
        ensures
            final(self).wf(),
            old(self)@ == final(self)@ + r@,
    {
        let ghost old_frames = self.frames@;
        let f = self.frames.pop().unwrap();
        let ghost fg = f;
        assert(old_frames =~= self.frames@.push(fg));
        let r = f.decode_exec();
        proof {
            lemma_decode_all_snoc(self.frames@, fg);
            // old@ == decode_all(old_frames) == decode_all(final.frames.push(fg))
            //      == decode_all(final.frames) + fg.decode() == final@ + r@.
        }
        assert forall|k: int| 0 <= k < self.frames@.len()
            implies (#[trigger] self.frames@[k]).wf() by {
            assert(self.frames@[k] == old_frames[k]);
        }
        assert(old(self)@ == self@ + r@);
        r
    }

    /// Diagnostic heap footprint of the compressed frames (capacity-based; no
    /// spec content). The monitoring hook for compressed size.
    #[verifier::external_body]
    pub fn heap_bytes(&self) -> usize {
        let mut total = self.frames.capacity() * core::mem::size_of::<FrameEncoding<T, I>>();
        for f in self.frames.iter() {
            total += match f {
                FrameEncoding::Plain(v) => v.capacity() * core::mem::size_of::<(T, I)>(),
                FrameEncoding::Dict(d) => {
                    d.dict.capacity() * core::mem::size_of::<T>()
                        + d.codes.heap_bytes()
                        + d.idxs.capacity() * core::mem::size_of::<I>()
                }
                FrameEncoding::Runs(rf) => {
                    let mut b = rf.starts.capacity() * core::mem::size_of::<usize>();
                    for run in rf.vals.iter() {
                        b += run.capacity() * core::mem::size_of::<T>();
                    }
                    b
                }
            };
        }
        total
    }
}

} // verus!
