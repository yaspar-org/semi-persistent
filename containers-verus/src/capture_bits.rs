// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! `CaptureBits`: a packed bit-vector that refines a ghost `Seq<bool>`.
//!
//! Production's `ParallelStore` keeps its per-slot capture flags in a packed
//! `Vec<u64>` (one bit per slot) for cache density — 8× less memory than a
//! `Vec<bool>`. This type carries that packed representation under a ghost
//! `Seq<bool>` view, so a backend can store its capture flags here while the
//! `DiffStore` proof continues to reason about a plain sequence of booleans.
//!
//! Representation: `words: Vec<u64>` holds the bits, bit `i` living in
//! `words[i / 64]` at position `i % 64`; `len` records how many bits are live
//! (trailing bits of the last word are unconstrained — the view never reads
//! them). The well-formedness invariant is that the word vector is long
//! enough to hold `len` bits.

use vstd::prelude::*;

verus! {

/// Bit `i` of a packed word sequence: word `i / 64`, position `i % 64`.
pub open spec fn spec_bit(words: Seq<u64>, i: int) -> bool {
    (words[i / 64] >> ((i % 64) as u64)) & 1u64 == 1u64
}

/// A packed bit-vector with a `Seq<bool>` view.
pub struct CaptureBits {
    words: Vec<u64>,
    len: usize,
}

impl View for CaptureBits {
    type V = Seq<bool>;

    /// The abstract flag sequence: `len` bits, bit `i` unpacked from `words`.
    closed spec fn view(&self) -> Seq<bool> {
        Seq::new(self.len as nat, |i: int| spec_bit(self.words@, i))
    }
}

impl CaptureBits {
    /// Well-formed iff the word vector can hold all `len` bits.
    pub closed spec fn wf(&self) -> bool {
        self.len <= self.words.len() * 64
    }

    /// Empty bit-vector.
    pub fn new() -> (r: CaptureBits)
        ensures r.wf(), r@ == Seq::<bool>::empty(),
    {
        let r = CaptureBits { words: Vec::new(), len: 0 };
        assert(r@ =~= Seq::<bool>::empty());
        r
    }

    /// Number of live bits.
    pub fn len(&self) -> (n: usize)
        ensures n == self@.len(),
    {
        self.len
    }

    /// Read bit `i`.
    pub fn get(&self, i: usize) -> (b: bool)
        requires self.wf(), i < self@.len(),
        ensures b == self@[i as int],
    {
        let w = self.words[i / 64];
        let bit = (w >> ((i % 64) as u64)) & 1u64;
        bit == 1u64
    }

    /// Set bit `i` to `value`. Every other bit's view is preserved.
    pub fn set(&mut self, i: usize, value: bool)
        requires old(self).wf(), i < old(self)@.len(),
        ensures
            self.wf(),
            self@ == old(self)@.update(i as int, value),
    {
        let wi = i / 64;
        let bit = (i % 64) as u64;
        let old_word = self.words[wi];
        let new_word = if value {
            old_word | (1u64 << bit)
        } else {
            old_word & !(1u64 << bit)
        };
        self.words.set(wi, new_word);
        proof {
            assert(self@ =~= old(self)@.update(i as int, value)) by {
                assert forall|j: int| 0 <= j < self.len implies
                    #[trigger] self@[j] == old(self)@.update(i as int, value)[j] by {
                    lemma_set_bit_pointwise(
                        old(self).words@, self.words@, i as int, j, bit, value, wi as int, new_word);
                }
            }
        }
    }

    /// Append a bit.
    pub fn push(&mut self, value: bool)
        requires old(self).wf(), old(self)@.len() < usize::MAX,
        ensures
            self.wf(),
            self@ == old(self)@.push(value),
    {
        let n = self.len;
        let wi = n / 64;
        // Grow the word vector if the new bit needs a fresh word. After this,
        // wi is in bounds and the old words (hence all old bits) are preserved.
        if wi >= self.words.len() {
            self.words.push(0u64);
        }
        let ghost grown = self.words@;
        proof {
            // wf of old means len <= old_words*64; we grew iff n was exactly at
            // the word boundary, so now wi < words.len().
            assert(wi < self.words@.len());
            assert(n + 1 <= self.words@.len() * 64);
        }
        let bit = (n % 64) as u64;
        let old_word = self.words[wi];
        let new_word = if value {
            old_word | (1u64 << bit)
        } else {
            old_word & !(1u64 << bit)
        };
        self.words.set(wi, new_word);
        self.len = n + 1;
        proof {
            assert(self@ =~= old(self)@.push(value)) by {
                assert forall|j: int| 0 <= j < self.len implies
                    #[trigger] self@[j] == old(self)@.push(value)[j] by {
                    if j < n as int {
                        // old bit j: preserved by the grow (grown[k]==old for
                        // k<old.len) and untouched by the set at a fresh/other
                        // position.
                        lemma_set_bit_pointwise(
                            grown, self.words@, n as int, j, bit, value, wi as int, new_word);
                        lemma_grow_preserves_bit(old(self).words@, grown, j);
                    } else {
                        // j == n: the bit we just set.
                        lemma_set_bit_at(self.words@, n as int, bit, value, wi as int, new_word);
                    }
                }
            }
        }
    }

    /// Drop the last bit.
    pub fn pop(&mut self)
        requires old(self).wf(), old(self)@.len() > 0,
        ensures
            self.wf(),
            self@ == old(self)@.drop_last(),
    {
        self.len = self.len - 1;
        proof {
            assert(self@ =~= old(self)@.drop_last());
        }
    }

    /// Truncate to `new_len` bits.
    pub fn truncate(&mut self, new_len: usize)
        requires old(self).wf(), new_len <= old(self)@.len(),
        ensures
            self.wf(),
            self@ == old(self)@.subrange(0, new_len as int),
    {
        self.len = new_len;
        proof {
            assert(self@ =~= old(self)@.subrange(0, new_len as int));
        }
    }
}

// ---------------------------------------------------------------------------
// Per-bit refinement lemmas (the bit_vector core).
// ---------------------------------------------------------------------------

/// Setting word `wi` to `new_word = old | (1<<bit)` or `old & !(1<<bit)` (per
/// `value`) updates exactly the one logical bit at index `i = wi*64 + bit` and
/// leaves every other logical bit's value unchanged.
pub proof fn lemma_set_bit_pointwise(
    old_words: Seq<u64>,
    new_words: Seq<u64>,
    i: int,
    j: int,
    bit: u64,
    value: bool,
    wi: int,
    new_word: u64,
)
    requires
        0 <= i,
        0 <= j,
        j / 64 < old_words.len(),
        bit == (i % 64) as u64,
        wi == i / 64,
        0 <= wi < old_words.len(),
        new_words.len() == old_words.len(),
        new_words[wi] == new_word,
        forall|k: int| 0 <= k < old_words.len() && k != wi ==> new_words[k] == old_words[k],
        value ==> new_word == (old_words[wi] | (1u64 << bit)),
        !value ==> new_word == (old_words[wi] & !(1u64 << bit)),
    ensures
        j == i ==> spec_bit(new_words, j) == value,
        j != i ==> spec_bit(new_words, j) == spec_bit(old_words, j),
{
    if j == i {
        lemma_set_bit_at(new_words, i, bit, value, wi, new_word);
    } else if j / 64 != wi {
        // different word entirely — unchanged.
        assert(new_words[j / 64] == old_words[j / 64]);
    } else {
        // same word, different position within it.
        let bj = (j % 64) as u64;
        assert(bj != bit) by {
            // j != i and same word ⟹ different position. i = wi*64+bit,
            // j = wi*64+bj, both in [wi*64, wi*64+64).
            lemma_same_word_diff_pos(i, j, wi);
        }
        let ow = old_words[wi];
        let nw = new_words[wi];
        // bit bj of nw equals bit bj of ow when nw differs from ow only at bit.
        assert(bit < 64 && bj < 64 && bj != bit
            && (value ==> nw == (ow | (1u64 << bit)))
            && (!value ==> nw == (ow & !(1u64 << bit)))
            ==> ((nw >> bj) & 1u64) == ((ow >> bj) & 1u64)) by (bit_vector);
    }
}

/// The bit just written reads back as `value`.
pub proof fn lemma_set_bit_at(words: Seq<u64>, i: int, bit: u64, value: bool, wi: int, new_word: u64)
    requires
        0 <= i,
        bit == (i % 64) as u64,
        wi == i / 64,
        0 <= wi < words.len(),
        words[wi] == new_word,
        value ==> exists|ow: u64| new_word == (ow | (1u64 << bit)),
        !value ==> exists|ow: u64| new_word == (ow & !(1u64 << bit)),
    ensures
        spec_bit(words, i) == value,
{
    let nw = new_word;
    if value {
        let ow = choose|ow: u64| nw == (ow | (1u64 << bit));
        assert(bit < 64 && nw == (ow | (1u64 << bit)) ==> ((nw >> bit) & 1u64) == 1u64)
            by (bit_vector);
    } else {
        let ow = choose|ow: u64| nw == (ow & !(1u64 << bit));
        assert(bit < 64 && nw == (ow & !(1u64 << bit)) ==> ((nw >> bit) & 1u64) == 0u64)
            by (bit_vector);
    }
}

/// Two distinct indices in the same 64-bit word have distinct positions.
pub proof fn lemma_same_word_diff_pos(i: int, j: int, wi: int)
    requires 0 <= i, 0 <= j, i != j, wi == i / 64, wi == j / 64,
    ensures (i % 64) != (j % 64),
{
    // i = 64*wi + (i%64), j = 64*wi + (j%64); equal positions ⟹ i == j.
}

/// Appending a fresh word to the end of the packed sequence preserves the
/// value of every bit that lived in the original words.
pub proof fn lemma_grow_preserves_bit(old_words: Seq<u64>, grown: Seq<u64>, j: int)
    requires
        0 <= j,
        j / 64 < old_words.len(),
        old_words.len() <= grown.len(),
        forall|k: int| 0 <= k < old_words.len() ==> grown[k] == old_words[k],
    ensures
        spec_bit(grown, j) == spec_bit(old_words, j),
{
    assert(grown[j / 64] == old_words[j / 64]);
}

} // verus!
