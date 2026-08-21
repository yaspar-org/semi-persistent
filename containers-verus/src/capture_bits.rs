// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! `CaptureBits`: a LAZILY-materialized packed bit-vector (production parity).
//!
//! Production's `ParallelStore` keeps its per-slot capture flags in a packed
//! `Vec<u64>` that is only touched when flags are actually USED: `push`/`pop`
//! never write it, `set_bit` resizes on demand, `prepare_mark` re-zeroes it.
//! This module reproduces that cost model under a verified view:
//!
//! - The abstract flag at position `i` is [`padded_bit`]: bit `i` of the
//!   materialized words when word `i/64` exists, `false` otherwise (the
//!   "padding"). Production's `is_bit_set` — `w < words.len() && bit != 0` —
//!   is exactly this spec's exec form.
//! - The LOGICAL length lives with the caller (the store passes its
//!   `data.len()`); `CaptureBits` itself is just the materialized words.
//!   The store's abstract `captured()` is `Seq::new(data.len(), padded_bit)`,
//!   so a data push EXTENDS the flag sequence with no exec work at all.
//! - Soundness of that free extension is the [`tail_clear`] invariant:
//!   every materialized bit at position `>= len` is zero. Then a fresh
//!   position always reads `false`, whether its word exists (tail-clear) or
//!   not (padding). `pop`/`truncate` re-establish it by clearing the bits
//!   they retire (a no-op while nothing is materialized — the whole
//!   `TRACK=false` lifetime).
//!
//! The previous eager design pushed/popped the bit-vector in lockstep with
//! the data (simplest possible invariant, but it made every `Vec::push` pay
//! word-index math and possible allocation even with `TRACK=false`). The
//! retained Criterion conformance benchmarks, rather than a historical point
//! estimate, are the performance evidence for this choice.

use vstd::prelude::*;

verus! {

/// Bit `i` of a packed word sequence: word `i / 64`, position `i % 64`.
pub open spec fn spec_bit(words: Seq<u64>, i: int) -> bool {
    (words[i / 64] >> ((i % 64) as u64)) & 1u64 == 1u64
}

/// The PADDED bit: `false` beyond the materialized words. The store's
/// abstract flag sequence is `Seq::new(data_len, |i| padded_bit(words, i))`.
pub open spec fn padded_bit(words: Seq<u64>, i: int) -> bool {
    i / 64 < words.len() && spec_bit(words, i)
}

/// The masked boundary word (spec helper so bit_vector asserts can name it
/// without spec-side shift arithmetic): `w & ((1 << rem) - 1)`.
pub open spec fn mask_of(rem: u64, w: u64) -> u64 {
    w & (((1u64 << rem) - 1) as u64)
}

/// The padded flag sequence over raw words at logical length `len` (free
/// spec form of `CaptureBits::flags`, for proofs that snapshot the words).
pub open spec fn flags_of(words: Seq<u64>, len: int) -> Seq<bool> {
    Seq::new(len as nat, |i: int| padded_bit(words, i))
}

/// Tail-clear invariant: every materialized bit at logical position `>= len`
/// is zero, so extending the logical length always exposes `false` bits.
pub open spec fn tail_clear(words: Seq<u64>, len: int) -> bool {
    forall|i: int| len <= i && #[trigger] (i / 64) < words.len() ==> !spec_bit(words, i)
}

/// Lazily-materialized capture flags. See the module doc; the logical
/// length is supplied by the owning store at each call.
pub struct CaptureBits {
    words: Vec<u64>,
}

impl CaptureBits {
    /// The materialized words (spec view; padding applies beyond them).
    pub closed spec fn words_view(&self) -> Seq<u64> {
        self.words@
    }

    /// The padded flag sequence at logical length `len`.
    pub open spec fn flags(&self, len: int) -> Seq<bool> {
        flags_of(self.words_view(), len)
    }

    /// Empty: no materialized words — every position reads `false`.
    #[inline(always)]
    pub fn new() -> (r: CaptureBits)
        ensures
            r.words_view().len() == 0,
            forall|len: int| 0 <= len ==> tail_clear(r.words_view(), len),
    {
        CaptureBits { words: Vec::new() }
    }

    /// Read the flag at `i` (production's `is_bit_set`, verbatim).
    #[inline(always)]
    pub fn get(&self, i: usize) -> (b: bool)
        ensures b == padded_bit(self.words_view(), i as int),
    {
        let w = i / 64;
        w < self.words.len() && (self.words[w] >> ((i % 64) as u64)) & 1u64 == 1u64
    }

    /// Materialize zero words up to `need`, preserving every stored word.
    ///
    /// Split out of [`Self::set_true`] so the cold growth loop stays out of
    /// line while the hot load/or/store inlines — see the note at the call site.
    #[inline(never)]
    fn grow_to(&mut self, need: usize)
        ensures
            old(self).words_view().len() <= final(self).words_view().len(),
            need <= final(self).words_view().len(),
            forall|k: int| 0 <= k < old(self).words_view().len()
                ==> #[trigger] final(self).words_view()[k] == old(self).words_view()[k],
            forall|k: int| old(self).words_view().len() <= k < final(self).words_view().len()
                ==> #[trigger] final(self).words_view()[k] == 0u64,
    {
        let ghost pre_grow = self.words@;
        while self.words.len() < need
            invariant
                pre_grow.len() <= self.words@.len(),
                forall|k: int| 0 <= k < pre_grow.len()
                    ==> #[trigger] self.words@[k] == pre_grow[k],
                forall|k: int| pre_grow.len() <= k < self.words@.len()
                    ==> #[trigger] self.words@[k] == 0u64,
            decreases need - self.words.len(),
        {
            self.words.push(0u64);
        }
    }

    /// Set the flag at `i` to `true`, materializing words on demand
    /// (production's `set_bit`, verbatim). `i < len` keeps tail-clear.
    ///
    /// `inline(always)` matches production's attribute on `set_bit`
    /// (`containers/src/diff_store.rs:80`): this is the bitmap op on the
    /// first-write capture path, and the common case is a load/or/store. Keep
    /// or change the hint based on the Criterion mark/restore benchmark.
    #[inline(always)]
    pub fn set_true(&mut self, i: usize, Ghost(len): Ghost<int>)
        requires
            (i as int) < len,
            tail_clear(old(self).words_view(), len),
        ensures
            tail_clear(final(self).words_view(), len),
            forall|j: int|
                #![trigger padded_bit(final(self).words_view(), j)]
                0 <= j ==> padded_bit(final(self).words_view(), j)
                    == if j == i as int { true } else { padded_bit(old(self).words_view(), j) },
    {
        let wi = i / 64;
        proof {
            // wi + 1 cannot overflow: wi == i/64 <= usize::MAX/64.
            assert(wi <= usize::MAX / 64);
        }
        let ghost pre_grow = self.words@;
        if wi >= self.words.len() {
            // Materialize zero words through wi: every padded bit is
            // preserved (old materialized bits unchanged; freshly
            // materialized positions flip from padding-false to
            // stored-zero-false).
            //
            // Kept OUT of line (`grow_to`) even though the enclosing fn is
            // `inline(always)`: the growth path is cold because `prepare_mark`
            // bulk-materializes, so a steady-state `set_true` finds its word
            // already present. Criterion covers the code-generation tradeoff.
            self.grow_to(wi + 1);
            proof {
                assert forall|j: int|
                    #![trigger padded_bit(pre_grow, j)]
                    0 <= j implies padded_bit(self.words@, j)
                    == padded_bit(pre_grow, j) by {
                    if j / 64 < pre_grow.len() {
                        assert(self.words@[j / 64] == pre_grow[j / 64]);
                    } else if j / 64 < self.words@.len() {
                        // freshly materialized zero word: bit is 0.
                        assert(self.words@[j / 64] == 0u64);
                        let bj = (j % 64) as u64;
                        assert((0u64 >> bj) & 1u64 == 0u64) by (bit_vector);
                    }
                }
                // tail_clear carries: every materialized bit >= len equals its
                // pre-grow padded value, which tail_clear pins false.
                assert forall|k: int| len <= k && k / 64 < self.words@.len()
                    implies !spec_bit(self.words@, k) by {
                    assert(padded_bit(self.words@, k) == padded_bit(pre_grow, k));
                }
            }
        }
        let ghost grown = self.words@;
        let bit = (i % 64) as u64;
        let old_word = self.words[wi];
        let new_word = old_word | (1u64 << bit);
        self.words.set(wi, new_word);
        proof {
            assert(wi < grown.len());
            assert forall|j: int|
                #![trigger padded_bit(self.words@, j)]
                0 <= j implies padded_bit(self.words@, j)
                == if j == i as int { true } else { padded_bit(grown, j) } by {
                lemma_or_bit_pointwise(grown, self.words@, i as int, j, bit, wi as int, new_word);
            }
            assert forall|k: int| len <= k && k / 64 < self.words@.len()
                implies !spec_bit(self.words@, k) by {
                assert(k != i as int);  // i < len <= k
                assert(padded_bit(self.words@, k) == padded_bit(grown, k));
            }
        }
    }

    /// Clear the flag at `i` if its word is materialized (retiring a
    /// popped/truncated position — re-establishes tail-clear one bit at a
    /// time). A pure branch while nothing is materialized (`TRACK=false`).
    #[inline(always)]
    pub fn clear_bit(&mut self, i: usize)
        ensures
            forall|j: int|
                #![trigger padded_bit(final(self).words_view(), j)]
                0 <= j ==> padded_bit(final(self).words_view(), j)
                    == if j == i as int { false } else { padded_bit(old(self).words_view(), j) },
    {
        let wi = i / 64;
        if wi < self.words.len() {
            let bit = (i % 64) as u64;
            let old_word = self.words[wi];
            let new_word = old_word & !(1u64 << bit);
            self.words.set(wi, new_word);
            proof {
                assert forall|j: int|
                    #![trigger padded_bit(self.words@, j)]
                    0 <= j implies padded_bit(self.words@, j)
                    == if j == i as int { false } else { padded_bit(old(self).words@, j) } by {
                    lemma_andnot_bit_pointwise(
                        old(self).words@, self.words@, i as int, j, bit, wi as int, new_word);
                }
            }
        } else {
            proof {
                // Unmaterialized: the bit already reads false, nothing changes.
                assert(!padded_bit(self.words@, i as int));
            }
        }
    }

    /// Zero every materialized word IN PLACE: all positions read `false`
    /// (zeroed or padding), tail-clear at every length. Production's
    /// `prepare_mark` zeroing, O(materialized words) — a vectorizable
    /// memset. Keeping the words allocated (vs dropping them) means the
    /// next capture's `set_true` finds its word already materialized
    /// instead of re-pushing the vector one word at a time (the 1M-element
    /// mark-churn regression the conformance sweep caught).
    pub fn zero_all(&mut self)
        ensures
            forall|j: int| 0 <= j ==> !padded_bit(final(self).words_view(), j),
            forall|len: int| 0 <= len ==> tail_clear(final(self).words_view(), len),
            // Word-level, not just bit-level: `zero_and_materialize` needs to
            // know the surviving words are literally zero so that appending
            // more zeros keeps the whole vector zero.
            final(self).words_view().len() == old(self).words_view().len(),
            forall|k: int| 0 <= k < final(self).words_view().len()
                ==> #[trigger] final(self).words_view()[k] == 0u64,
    {
        let n = self.words.len();
        let mut i: usize = 0;
        while i < n
            invariant
                self.words@.len() == n,
                forall|k: int| 0 <= k < i as int ==> #[trigger] self.words@[k] == 0u64,
            decreases (n - i) as int,
        {
            self.words.set(i, 0u64);
            i += 1;
        }
        proof {
            assert forall|j: int| 0 <= j implies !padded_bit(self.words@, j) by {
                if j / 64 < self.words@.len() {
                    assert(self.words@[j / 64] == 0u64);
                    let bj = (j % 64) as u64;
                    assert((0u64 >> bj) & 1u64 == 0u64) by (bit_vector);
                }
            }
            // tail_clear at every length follows from all-padded-false.
            assert forall|len: int| 0 <= len implies
                #[trigger] tail_clear(self.words@, len) by {
                assert forall|j: int| len <= j && #[trigger] (j / 64) < self.words@.len()
                    implies !spec_bit(self.words@, j) by {
                    assert(!padded_bit(self.words@, j));
                }
            }
        }
    }

    /// Production's `prepare_mark`/`finish_restore` bitmap protocol verbatim:
    /// zero every materialized word, THEN bulk-resize the word vector to cover
    /// `data_len` positions. Postcondition is `zero_all`'s — all positions read
    /// `false` — but the eager resize is load-bearing for PERFORMANCE, not
    /// correctness.
    ///
    /// Why eager: `set_true` materializes on demand by pushing one word at a
    /// time. Under `zero_all` alone, a frame whose writes span a wide index
    /// range pays that growth loop inside the write path. One bulk resize moves
    /// that work to the frame boundary. Narrow and wide spans have different
    /// constant factors, so the maintained Criterion nested-mark workloads are
    /// the evidence for this policy.
    ///
    /// One `Vec::resize` is a single vectorizable memset, and it subsumes the
    /// zeroing of any words it appends.
    pub fn zero_and_materialize(&mut self, data_len: usize)
        ensures
            forall|j: int| 0 <= j ==> !padded_bit(final(self).words_view(), j),
            forall|len: int| 0 <= len ==> tail_clear(final(self).words_view(), len),
    {
        self.zero_all();
        let ghost zeroed = self.words@;
        // div_ceil(64): words needed to cover `data_len` positions. Spelled out
        // with `/` and `%` rather than `div_ceil`/`is_multiple_of` because
        // vstd specs the primitive operators, not those methods
        // (hence the `clippy::manual_is_multiple_of` allow).
        #[allow(clippy::manual_is_multiple_of)]
        let needed = data_len / 64 + if data_len % 64 == 0 { 0 } else { 1 };
        if needed > self.words.len() {
            self.words.resize(needed, 0u64);
        }
        proof {
            // Every word is 0: the pre-existing ones by `zero_all`'s
            // word-level postcondition, the appended ones because `resize`'s
            // filler is `cloned(0u64, _)` and `u64::clone` is the identity.
            assert forall|k: int| 0 <= k < self.words@.len() implies
                #[trigger] self.words@[k] == 0u64 by {
                if k < zeroed.len() {
                    assert(zeroed[k] == 0u64);
                }
            }
            assert forall|j: int| 0 <= j implies !padded_bit(self.words@, j) by {
                if j / 64 < self.words@.len() {
                    assert(self.words@[j / 64] == 0u64);
                    let bj = (j % 64) as u64;
                    assert((0u64 >> bj) & 1u64 == 0u64) by (bit_vector);
                }
            }
            assert forall|len: int| 0 <= len implies
                #[trigger] tail_clear(self.words@, len) by {
                assert forall|j: int| len <= j && #[trigger] (j / 64) < self.words@.len()
                    implies !spec_bit(self.words@, j) by {
                    assert(!padded_bit(self.words@, j));
                }
            }
        }
    }

    /// Retire every flag at logical position `>= len`: truncate the word
    /// vector to the boundary word and mask the partial word's high bits.
    /// O(1) plus the `Vec::truncate`. Preserves every padded bit `< len`,
    /// forces every padded bit `>= len` to `false`, establishing tail-clear
    /// at `len` outright. (The exec analogue of production's restore-path
    /// flag retirement; also serves `truncate`'s `subrange` contract.)
    pub fn retire_from(&mut self, len: usize)
        ensures
            forall|j: int| 0 <= j < len as int ==> padded_bit(final(self).words_view(), j)
                == padded_bit(old(self).words_view(), j),
            forall|j: int| len as int <= j ==> !padded_bit(final(self).words_view(), j),
            tail_clear(final(self).words_view(), len as int),
    {
        let ghost final_check: bool = true;
        let full_words = len / 64;
        let rem = (len % 64) as u64;
        let ghost pre = self.words@;
        if rem == 0 {
            // Exact boundary: drop every word at index >= full_words.
            if self.words.len() > full_words {
                self.words.truncate(full_words);
            }
            proof {
                assert(self.words@.len() <= full_words as int);
                assert forall|j: int| #![trigger padded_bit(pre, j)] 0 <= j < len as int implies
                    padded_bit(self.words@, j) == padded_bit(pre, j) by {
                    if j / 64 < self.words@.len() {
                        assert(self.words@[j / 64] == pre[j / 64]);
                    } else {
                        // j < len == 64*full_words and j/64 >= words.len():
                        // only possible when pre also lacked the word...
                        if j / 64 < pre.len() {
                            // word was dropped, but j/64 < full_words
                            // contradicts truncate keeping full_words words
                            // unless pre had fewer — handle: j/64 < full_words
                            // and words.len() == min(pre.len(), full_words).
                            assert(j / 64 < full_words as int);
                            assert(self.words@.len() as int
                                == if pre.len() < full_words as nat { pre.len() as int }
                                   else { full_words as int });
                            assert(false);  // j/64 < full_words <= words.len()
                        }
                    }
                }
                assert forall|j: int| len as int <= j implies
                    !padded_bit(self.words@, j) by {
                    if j / 64 < self.words@.len() {
                        assert(j / 64 < full_words as int);
                        assert(j < 64 * full_words as int);
                        assert(j < len as int);  // contradiction with len <= j
                    }
                }
            }
        } else {
            let boundary = full_words + 1;
            if self.words.len() > boundary {
                self.words.truncate(boundary);
            }
            let ghost trunc = self.words@;
            if full_words < self.words.len() {
                // Mask the boundary word: keep bits [0, rem), clear the rest.
                proof {
                    assert(rem < 64);
                    assert((1u64 << rem) >= 1u64) by (bit_vector) requires rem < 64;
                }
                let mask: u64 = (1u64 << rem) - 1;
                let w = self.words[full_words];
                self.words.set(full_words, w & mask);
                proof {
                    assert forall|j: int| #![trigger padded_bit(pre, j)] 0 <= j < len as int implies
                        padded_bit(self.words@, j) == padded_bit(pre, j) by {
                        if j / 64 < self.words@.len() {
                            if j / 64 == full_words as int {
                                // in the boundary word, j%64 < rem
                                assert(j % 64 < rem as int);
                                let bj = (j % 64) as u64;
                                assert(((w & (((1u64 << rem) - 1) as u64)) >> bj) & 1u64
                                    == (w >> bj) & 1u64) by (bit_vector)
                                    requires bj < rem && rem < 64;
                                assert(mask_of(rem, w) == w & (((1u64 << rem) - 1) as u64));
                                assert(trunc[full_words as int] == pre[full_words as int]);
                            } else {
                                assert(self.words@[j / 64] == pre[j / 64]);
                            }
                        } else {
                            if j / 64 < pre.len() {
                                assert(j / 64 <= full_words as int);
                                assert(false);  // words kept through boundary
                            }
                        }
                    }
                    assert forall|j: int| len as int <= j implies
                        !padded_bit(self.words@, j) by {
                        if j / 64 < self.words@.len() {
                            assert(j / 64 == full_words as int);  // words end at boundary
                            assert(j % 64 >= rem as int);
                            let bj = (j % 64) as u64;
                            assert(((w & (((1u64 << rem) - 1) as u64)) >> bj) & 1u64 == 0u64)
                                by (bit_vector)
                                requires rem <= bj && bj < 64 && rem < 64;
                            assert(mask_of(rem, w) == w & (((1u64 << rem) - 1) as u64));
                        }
                    }
                }
            } else {
                proof {
                    // No boundary word materialized: bits >= len were already
                    // padding; bits < len in existing words unchanged.
                    assert(self.words@ == pre || self.words@.len() <= full_words as int);
                    assert forall|j: int| len as int <= j implies
                        !padded_bit(self.words@, j) by {
                        if j / 64 < self.words@.len() {
                            assert(j / 64 < boundary as int);
                            assert(j / 64 <= full_words as int);
                            assert(j / 64 == full_words as int || j < len as int);
                            assert(j / 64 < full_words as int ==> j < len as int);
                            // j/64 == full_words impossible: words.len() <= full_words
                            assert(false);
                        }
                    }
                    assert forall|j: int| #![trigger padded_bit(pre, j)] 0 <= j < len as int implies
                        padded_bit(self.words@, j) == padded_bit(pre, j) by {
                        if j / 64 < self.words@.len() {
                            assert(self.words@[j / 64] == pre[j / 64]);
                        } else if j / 64 < pre.len() {
                            // dropped word at index in [words.len(), boundary):
                            // but truncate kept min(pre.len(), boundary) words
                            assert(self.words@.len() as int
                                == if pre.len() < boundary as nat { pre.len() as int }
                                   else { boundary as int });
                            assert(false);
                        }
                    }
                }
            }
        }
        proof {
            // tail_clear at len follows pointwise from clause 2: a
            // materialized bit at position >= len has padded_bit false,
            // and for a materialized word padded_bit == spec_bit.
            assert forall|k: int| len as int <= k && k / 64 < self.words@.len()
                implies !spec_bit(self.words@, k) by {
                assert(!padded_bit(self.words@, k));
            }
        }
    }

    /// Heap bytes used by the word vector (diagnostic; no spec content —
    /// capacity is unmodeled by Verus, so this is `external_body`; it reads
    /// state without mutating. Trust ledger: group B). Matches production's
    /// `captured.capacity() * size_of::<u64>()` term in
    /// `ParallelStore::heap_bytes`.
    #[verifier::external_body]
    pub fn heap_bytes(&self) -> usize {
        self.words.capacity() * core::mem::size_of::<u64>()
    }

    /// Drop materialized words that lie entirely beyond `keep_bits` logical
    /// positions, reclaiming their heap. This is production's
    /// `captured.truncate(capacity.div_ceil(64))` in `ParallelStore::shrink_if`
    /// (`containers/src/diff_store.rs:195`) — without it the word vector is a
    /// permanent high-water mark and the verus store's footprint diverges from
    /// production's after a shrink.
    ///
    /// The bound is `div_ceil(64)`: word `keep_bits.div_ceil(64)` is the first
    /// whose every bit is at a position `>= keep_bits`, so truncating there can
    /// only discard flags at positions the caller has declared out of range.
    /// Every padded bit below `keep_bits` is preserved, which is what makes this
    /// invisible to `flags(len)` for any `len <= keep_bits` — hence the
    /// `shrink_if` caller passing the post-shrink capacity.
    ///
    /// `Vec::truncate` to a length `>=` the current one is a no-op, so this
    /// never grows the vector and never materializes a word.
    pub fn truncate_words_for(&mut self, keep_bits: usize)
        ensures
            forall|j: int| 0 <= j < keep_bits as int ==> padded_bit(final(self).words_view(), j)
                == padded_bit(old(self).words_view(), j),
            final(self).words_view().len() <= old(self).words_view().len(),
            // `tail_clear` survives for every length the caller could still be
            // holding: dropping words only shrinks the `i / 64 < words.len()`
            // domain of its quantifier, so a store whose `wf` held at `len`
            // before still has it after. This is the clause `shrink_if` needs.
            forall|len: int| 0 <= len && tail_clear(old(self).words_view(), len)
                ==> tail_clear(final(self).words_view(), len),
    {
        // Number of words needed to cover `keep_bits` positions.
        let need = keep_bits / 64 + if keep_bits % 64 == 0 { 0 } else { 1 };
        let ghost pre = self.words@;
        if self.words.len() > need {
            self.words.truncate(need);
        }
        proof {
            // Words kept are pointwise unchanged; a position below `keep_bits`
            // either lives in a kept word (same value) or in no word at all
            // both before and after (padding reads false on both sides).
            assert(self.words@.len() <= pre.len());
            assert forall|j: int| #![trigger padded_bit(pre, j)] 0 <= j < keep_bits as int implies
                padded_bit(self.words@, j) == padded_bit(pre, j) by {
                if j / 64 < self.words@.len() {
                    assert(self.words@[j / 64] == pre[j / 64]);
                } else {
                    // j < keep_bits ==> j / 64 < need, and truncate keeps
                    // min(pre.len(), need) words, so the word is missing only
                    // if `pre` lacked it too — both sides read padding.
                    assert(j / 64 < need as int) by (nonlinear_arith)
                        requires 0 <= j < keep_bits as int,
                                 need as int == keep_bits as int / 64
                                     + if keep_bits as int % 64 == 0 { 0int } else { 1int };
                    assert(j / 64 >= pre.len());
                }
            }
            // tail_clear transfer: its body is guarded by `i / 64 < words.len()`,
            // and the word vector only shrank, so every instance that has to be
            // discharged after is an instance that already held before.
            assert forall|len: int|
                #![trigger tail_clear(pre, len)]
                0 <= len && tail_clear(pre, len) implies
                tail_clear(self.words@, len) by {
                assert forall|i: int| len <= i && i / 64 < self.words@.len() implies
                    !spec_bit(self.words@, i) by {
                    assert(i / 64 < pre.len());
                    assert(self.words@[i / 64] == pre[i / 64]);
                    assert(!spec_bit(pre, i));
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Per-bit refinement lemmas (the bit_vector core).
// ---------------------------------------------------------------------------

/// `new_word = old | (1 << bit)` at word `wi` sets exactly logical bit
/// `i = wi*64 + bit` (to true) and preserves every other padded bit.
pub(crate) proof fn lemma_or_bit_pointwise(
    old_words: Seq<u64>,
    new_words: Seq<u64>,
    i: int,
    j: int,
    bit: u64,
    wi: int,
    new_word: u64,
)
    requires
        0 <= i,
        0 <= j,
        bit == (i % 64) as u64,
        wi == i / 64,
        0 <= wi < old_words.len(),
        new_word == old_words[wi] | (1u64 << bit),
        new_words == old_words.update(wi, new_word),
    ensures
        padded_bit(new_words, j) == if j == i { true } else { padded_bit(old_words, j) },
{
    let old_word = old_words[wi];
    let bj = (j % 64) as u64;
    if j / 64 < old_words.len() {
        if j / 64 == wi {
            if j == i {
                assert(bj == bit);
                assert(((old_word | (1u64 << bit)) >> bit) & 1u64 == 1u64) by (bit_vector)
                    requires bit < 64;
                assert(bit < 64) by {
                    assert(0 <= i % 64 < 64);
                }
            } else {
                // same word, different bit position
                assert(bj != bit) by {
                    // j/64 == i/64 and j != i force j%64 != i%64.
                    assert(j == 64 * (j / 64) + (j % 64));
                    assert(i == 64 * (i / 64) + (i % 64));
                }
                assert(bj < 64 && bit < 64) by {
                    assert(0 <= j % 64 < 64);
                    assert(0 <= i % 64 < 64);
                }
                assert(((old_word | (1u64 << bit)) >> bj) & 1u64 == (old_word >> bj) & 1u64)
                    by (bit_vector)
                    requires bj != bit && bj < 64 && bit < 64;
            }
        } else {
            assert(new_words[j / 64] == old_words[j / 64]);
        }
    } else {
        // beyond materialized words in BOTH (update preserves length)
        assert(new_words.len() == old_words.len());
    }
}

/// `new_word = old & !(1 << bit)` at word `wi` clears exactly logical bit
/// `i = wi*64 + bit` and preserves every other padded bit.
pub(crate) proof fn lemma_andnot_bit_pointwise(
    old_words: Seq<u64>,
    new_words: Seq<u64>,
    i: int,
    j: int,
    bit: u64,
    wi: int,
    new_word: u64,
)
    requires
        0 <= i,
        0 <= j,
        bit == (i % 64) as u64,
        wi == i / 64,
        0 <= wi < old_words.len(),
        new_word == old_words[wi] & !(1u64 << bit),
        new_words == old_words.update(wi, new_word),
    ensures
        padded_bit(new_words, j) == if j == i { false } else { padded_bit(old_words, j) },
{
    let old_word = old_words[wi];
    let bj = (j % 64) as u64;
    if j / 64 < old_words.len() {
        if j / 64 == wi {
            if j == i {
                assert(bj == bit);
                assert(((old_word & !(1u64 << bit)) >> bit) & 1u64 == 0u64) by (bit_vector);
            } else {
                assert(bj != bit) by {
                    assert(j == 64 * (j / 64) + (j % 64));
                    assert(i == 64 * (i / 64) + (i % 64));
                }
                assert(bj < 64 && bit < 64) by {
                    assert(0 <= j % 64 < 64);
                    assert(0 <= i % 64 < 64);
                }
                assert(((old_word & !(1u64 << bit)) >> bj) & 1u64 == (old_word >> bj) & 1u64)
                    by (bit_vector)
                    requires bj != bit && bj < 64 && bit < 64;
            }
        } else {
            assert(new_words[j / 64] == old_words[j / 64]);
        }
    } else {
        assert(new_words.len() == old_words.len());
    }
}

} // verus!
