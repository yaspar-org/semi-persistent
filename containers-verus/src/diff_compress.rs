// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Value-dictionary encoding of a finalized diff frame — the value axis of
//! diff-stack compression (`doc/design/09-diff-stack-compression.md`).
//!
//! Standalone and additive: this module proves the encode/decode bijection over
//! the abstract diff sequence, independent of the `Vec` integration. It is the
//! value-axis win for repetitive columns (the union-find `parent`/`rank`
//! columns, where the captured old values are a low-cardinality multiset): store
//! `dict.len()` distinct values plus one `usize` code per entry, versus one full
//! `T` per entry. The index column is kept verbatim here; the index axis
//! (run-coalescing / Elias-Fano / delta-varint) composes on top and is a
//! separate encoder.

use crate::index_like::{IndexFromNat, IndexLike};
use vstd::prelude::*;

verus! {

/// The dictionary code column, stored at the narrowest byte width that fits the
/// dictionary size (`u8` for `D <= 256`, `u16` for `D <= 65536`, else `u32`).
/// Its abstract value is `Seq<nat>` regardless of width, so `DictFrame`'s
/// bijection is stated over `view()` and the storage is swappable: a future
/// bit-packed variant (`ceil(log2 D)` bits) drops in behind this same contract
/// without touching the frame or any caller. This is what takes value-major from
/// a loss at `usize` codes to a win (measured 0.63x byte / 0.30x bit-packed).
pub enum Codes {
    U8(Vec<u8>),
    U16(Vec<u16>),
    U32(Vec<u32>),
    Usize(Vec<usize>),
    /// Sub-byte bit-packed codes: `bits` bits per code (1/2/4, for `D <= 2/4/16`),
    /// packed `64 / bits` codes per `u64` word with no cross-word straddle (so a
    /// code is always within one word). `len` codes total. This is the value-major
    /// win below one byte per code (union-find `D <= 4` reaches ~0.30x plain). The
    /// pack/extract pair is `external_body` (variable-width bit arithmetic is not a
    /// tractable proof surface) with `view()` the exact extraction formula and the
    /// round-trip checked by `packed_codes_roundtrip` (containers-conformance);
    /// trust ledger group B (bit shifts/masks, no `unsafe`).
    Packed { words: Vec<u64>, bits: u8, len: usize },
}

/// The code extracted from bit-packed `words` at position `i`: word `i / (64/bits)`,
/// then the `bits`-wide field at offset `(i % (64/bits)) * bits`. The abstract value
/// of a `Packed` column; `bits` is 1/2/4 so `64/bits` is exact and a code never
/// straddles a word.
pub open spec fn packed_code_at(words: Seq<u64>, bits: nat, i: int) -> nat {
    let per_word = 64nat / bits;
    let wi = i / (per_word as int);
    let shift = (i % (per_word as int)) * (bits as int);
    ((words[wi] >> (shift as u64)) & ((sub(1u64 << (bits as u64), 1)) as u64)) as nat
}

impl Codes {
    /// Structural well-formedness of the packed variant: a legal width and
    /// enough words to cover `len` (so `view` never reads out of range). The
    /// plain-width variants are unconstrained. Introduced when `pack_codes`/
    /// `packed_get` were discharged from the trust ledger: the verified
    /// extractor needs the coverage fact its trusted predecessor assumed.
    pub open spec fn wf(&self) -> bool {
        match self {
            Codes::Packed { words, bits, len } => {
                &&& (*bits == 1 || *bits == 2 || *bits == 4)
                &&& (*len as nat) <= words@.len() * (64nat / (*bits as nat))
            }
            _ => true,
        }
    }

    pub open spec fn view(&self) -> Seq<nat> {
        match self {
            Codes::U8(v) => Seq::new(v@.len(), |i: int| v@[i] as nat),
            Codes::U16(v) => Seq::new(v@.len(), |i: int| v@[i] as nat),
            Codes::U32(v) => Seq::new(v@.len(), |i: int| v@[i] as nat),
            Codes::Usize(v) => Seq::new(v@.len(), |i: int| v@[i] as nat),
            Codes::Packed { words, bits, len } =>
                Seq::new(*len as nat, |i: int| packed_code_at(words@, *bits as nat, i)),
        }
    }

    pub fn len(&self) -> (n: usize)
        ensures n == self.view().len(),
    {
        match self {
            Codes::U8(v) => v.len(),
            Codes::U16(v) => v.len(),
            Codes::U32(v) => v.len(),
            Codes::Usize(v) => v.len(),
            Codes::Packed { len, .. } => *len,
        }
    }

    pub fn get(&self, i: usize) -> (c: usize)
        requires
            self.wf(),
            i < self.view().len(),
        ensures c as nat == self.view()[i as int],
    {
        match self {
            Codes::U8(v) => v[i] as usize,
            Codes::U16(v) => v[i] as usize,
            Codes::U32(v) => v[i] as usize,
            Codes::Usize(v) => v[i],
            Codes::Packed { words, bits, .. } => packed_get(words, *bits, i),
        }
    }

    /// Bytes of the code column (diagnostic).
    #[verifier::external_body]
    pub fn heap_bytes(&self) -> usize {
        match self {
            Codes::U8(v) => v.capacity(),
            Codes::U16(v) => v.capacity() * 2,
            Codes::U32(v) => v.capacity() * 4,
            Codes::Usize(v) => v.capacity() * 8,
            Codes::Packed { words, .. } => words.capacity() * 8,
        }
    }

    /// Length-based byte count (deterministic; for measurement/comparison, unlike
    /// capacity-based `heap_bytes`).
    pub fn byte_len(&self) -> usize {
        match self {
            Codes::U8(v) => v.len(),
            Codes::U16(v) => crate::compression_stats::sat_mul(v.len(), 2),
            Codes::U32(v) => crate::compression_stats::sat_mul(v.len(), 4),
            Codes::Usize(v) => crate::compression_stats::sat_mul(v.len(), 8),
            Codes::Packed { words, .. } => crate::compression_stats::sat_mul(words.len(), 8),
        }
    }

    /// Build the narrowest-width code column from `usize` codes, given the
    /// dictionary size they index into. `view()` reproduces the codes exactly.
    pub fn from_usize(codes: &Vec<usize>, dict_len: usize) -> (r: Codes)
        requires forall|t: int| 0 <= t < codes@.len() ==> #[trigger] codes@[t] < dict_len,
        ensures
            r.wf(),
            r.view().len() == codes@.len(),
            forall|t: int| 0 <= t < codes@.len() ==> #[trigger] r.view()[t] == codes@[t] as nat,
    {
        // Sub-byte bit-packing for small dictionaries: 1/2/4 bits per code covers
        // D <= 2/4/16, the value-major win below one byte per code. Each code fits
        // in `bits` because `codes[t] < dict_len <= 2^bits`.
        if dict_len <= 2 {
            assert(forall|t: int| 0 <= t < codes@.len() ==> #[trigger] codes@[t] < (1usize << 1u8)) by {
                assert((1usize << 1u8) == 2) by (bit_vector);
            }
            pack_codes(codes, 1)
        } else if dict_len <= 4 {
            assert(forall|t: int| 0 <= t < codes@.len() ==> #[trigger] codes@[t] < (1usize << 2u8)) by {
                assert((1usize << 2u8) == 4) by (bit_vector);
            }
            pack_codes(codes, 2)
        } else if dict_len <= 16 {
            assert(forall|t: int| 0 <= t < codes@.len() ==> #[trigger] codes@[t] < (1usize << 4u8)) by {
                assert((1usize << 4u8) == 16) by (bit_vector);
            }
            pack_codes(codes, 4)
        } else if dict_len <= 256 {
            let mut v: Vec<u8> = Vec::new();
            let mut t: usize = 0;
            while t < codes.len()
                invariant
                    t <= codes@.len(),
                    dict_len <= 256,
                    forall|k: int| 0 <= k < codes@.len() ==> #[trigger] codes@[k] < dict_len,
                    v@.len() == t,
                    forall|k: int| 0 <= k < t ==> #[trigger] v@[k] as nat == codes@[k] as nat,
                decreases codes@.len() - t,
            {
                v.push(codes[t] as u8);
                t += 1;
            }
            let r = Codes::U8(v);
            assert forall|k: int| 0 <= k < codes@.len() implies #[trigger] r.view()[k] == codes@[k] as nat by {}
            r
        } else if dict_len <= 65536 {
            let mut v: Vec<u16> = Vec::new();
            let mut t: usize = 0;
            while t < codes.len()
                invariant
                    t <= codes@.len(),
                    dict_len <= 65536,
                    forall|k: int| 0 <= k < codes@.len() ==> #[trigger] codes@[k] < dict_len,
                    v@.len() == t,
                    forall|k: int| 0 <= k < t ==> #[trigger] v@[k] as nat == codes@[k] as nat,
                decreases codes@.len() - t,
            {
                v.push(codes[t] as u16);
                t += 1;
            }
            let r = Codes::U16(v);
            assert forall|k: int| 0 <= k < codes@.len() implies #[trigger] r.view()[k] == codes@[k] as nat by {}
            r
        } else if dict_len <= u32::MAX as usize {
            let mut v: Vec<u32> = Vec::new();
            let mut t: usize = 0;
            while t < codes.len()
                invariant
                    t <= codes@.len(),
                    dict_len <= u32::MAX as usize,
                    forall|k: int| 0 <= k < codes@.len() ==> #[trigger] codes@[k] < dict_len,
                    v@.len() == t,
                    forall|k: int| 0 <= k < t ==> #[trigger] v@[k] as nat == codes@[k] as nat,
                decreases codes@.len() - t,
            {
                v.push(codes[t] as u32);
                t += 1;
            }
            let r = Codes::U32(v);
            assert forall|k: int| 0 <= k < codes@.len() implies #[trigger] r.view()[k] == codes@[k] as nat by {}
            r
        } else {
            // Fallback: dictionary larger than 2^32 entries — keep usize codes
            // (no narrowing possible without truncation).
            let mut v: Vec<usize> = Vec::new();
            let mut t: usize = 0;
            while t < codes.len()
                invariant
                    t <= codes@.len(),
                    v@.len() == t,
                    forall|k: int| 0 <= k < t ==> #[trigger] v@[k] as nat == codes@[k] as nat,
                decreases codes@.len() - t,
            {
                v.push(codes[t]);
                t += 1;
            }
            let r = Codes::Usize(v);
            assert forall|k: int| 0 <= k < codes@.len() implies #[trigger] r.view()[k] == codes@[k] as nat by {}
            r
        }
    }
}

/// One packed field is set by OR-ing a shifted code into a zero field, and
/// every other aligned field of the word is untouched. The two bit-vector
/// facts the packing loop rests on, quantifier-free per call.
proof fn lemma_pack_field_set(w: u64, code: u64, bits: u64, shift: u64)
    by (bit_vector)
    requires
        bits == 1 || bits == 2 || bits == 4,
        shift + bits <= 64,
        code < (1u64 << bits),
        (w >> shift) & (sub(1u64 << bits, 1)) == 0,
    ensures
        ((w | (code << shift)) >> shift) & (sub(1u64 << bits, 1)) == code,
{
}

proof fn lemma_pack_field_other(w: u64, code: u64, bits: u64, shift: u64, shift2: u64)
    by (bit_vector)
    requires
        bits == 1 || bits == 2 || bits == 4,
        shift + bits <= 64,
        shift2 + bits <= 64,
        shift2 + bits <= shift || shift + bits <= shift2,
        code < (1u64 << bits),
    ensures
        ((w | (code << shift)) >> shift2) & (sub(1u64 << bits, 1))
            == (w >> shift2) & (sub(1u64 << bits, 1)),
{
}

/// Bit-pack `codes` at `bits` bits each (1/2/4), `64/bits` per `u64` word with no
/// cross-word straddle. VERIFIED: the loop invariant carries "every packed field
/// below `t` reads back its code, every field at or above `t` is still zero",
/// maintained by the two field lemmas above (aligned fields of one word are
/// disjoint intervals). Discharged from the trust ledger 2026-09; the
/// `packed_codes_roundtrip` proptest stays as a belt.
pub fn pack_codes(codes: &Vec<usize>, bits: u8) -> (r: Codes)
    requires
        bits == 1 || bits == 2 || bits == 4,
        forall|t: int| 0 <= t < codes@.len() ==> #[trigger] codes@[t] < (1usize << bits),
    ensures
        r.wf(),
        r.view().len() == codes@.len(),
        forall|t: int| 0 <= t < codes@.len() ==> #[trigger] r.view()[t] == codes@[t] as nat,
{
    let per_word: usize = 64 / (bits as usize);
    proof {
        assert(per_word >= 16) by (nonlinear_arith)
            requires (bits == 1 || bits == 2 || bits == 4),
                per_word == 64usize / (bits as usize);
    }
    let n = codes.len();
    let nwords = if n == 0 { 0 } else { (n - 1) / per_word + 1 };
    proof {
        // Coverage: nwords * per_word >= n (exact-division ceiling).
        if n > 0 {
            assert(nwords * per_word >= n) by (nonlinear_arith)
                requires per_word > 0, n > 0,
                    nwords as int == (n - 1) as int / per_word as int + 1;
        }
    }
    let mut words: Vec<u64> = Vec::new();
    let mut z: usize = 0;
    while z < nwords
        invariant
            z <= nwords,
            words@.len() == z,
            forall|k: int| 0 <= k < z ==> #[trigger] words@[k] == 0u64,
        decreases nwords - z,
    {
        words.push(0u64);
        z += 1;
    }
    let ghost per = per_word as nat;
    proof {
        // All-zero words decode to all-zero fields.
        assert forall|k: int| 0 <= k < nwords * per_word implies
            #[trigger] packed_code_at(words@, bits as nat, k) == 0 by {
            let kwi = k / (per as int);
            assert(0 <= kwi < words@.len()) by (nonlinear_arith)
                requires per > 0, 0 <= k, (k as nat) < words@.len() * per,
                    kwi == k / (per as int);
            assert(words@[kwi] == 0u64);
            let kshu: u64 = ((k % (per as int)) * (bits as int)) as u64;
            assert((0u64 >> kshu) & (sub(1u64 << (bits as u64), 1)) == 0u64)
                by (bit_vector);
            assert(packed_code_at(words@, bits as nat, k)
                == ((words@[kwi] >> kshu) & (sub(1u64 << (bits as u64), 1))) as nat
                || packed_code_at(words@, bits as nat, k) == 0) by {
                assert(((k % (per as int)) * (bits as int)) as u64 == kshu);
            }
        }
    }
    let mut t: usize = 0;
    while t < n
        invariant
            bits == 1 || bits == 2 || bits == 4,
            per_word == 64usize / (bits as usize),
            per_word >= 16,
            per == per_word as nat,
            n == codes@.len(),
            words@.len() == nwords,
            n <= nwords * per_word,
            forall|k: int| 0 <= k < codes@.len() ==> #[trigger] codes@[k] < (1usize << bits),
            0 <= t <= n,
            forall|k: int| 0 <= k < t
                ==> #[trigger] packed_code_at(words@, bits as nat, k) == codes@[k] as nat,
            forall|k: int| t <= k < nwords * per_word
                ==> #[trigger] packed_code_at(words@, bits as nat, k) == 0,
        decreases n - t,
    {
        let wi = t / per_word;
        let f = t % per_word;
        proof {
            assert(wi < nwords) by (nonlinear_arith)
                requires per_word > 0, t < n, n <= nwords * per_word,
                    wi == t / per_word;
            assert(f < per_word) by (nonlinear_arith)
                requires per_word > 0, f == t % per_word;
            assert((f as u64) * (bits as u64) + (bits as u64) <= 64) by (nonlinear_arith)
                requires f < per_word, per_word == 64usize / (bits as usize),
                    (bits == 1 || bits == 2 || bits == 4);
        }
        let shift = (f as u64) * (bits as u64);
        let code = codes[t] as u64;
        let ghost mask_spec = (((1u64 << (bits as u64)) - 1) as u64);
        proof {
            assert(mask_spec == sub(1u64 << (bits as u64), 1)) by (bit_vector)
                requires bits == 1u8 || bits == 2u8 || bits == 4u8,
                    mask_spec == (((1u64 << (bits as u64)) - 1) as u64);
            let cu: usize = codes@[t as int];
            assert(cu < (1usize << bits));
            assert(cu < (1usize << bits) && (bits == 1u8 || bits == 2u8 || bits == 4u8)
                ==> (cu as u64) < (1u64 << (bits as u64))) by (bit_vector);
            assert(code < (1u64 << (bits as u64)));
            // The target field is inside coverage and still zero.
            assert((t as int) < nwords * per_word);
            assert(packed_code_at(words@, bits as nat, t as int) == 0);
            assert(t as int / (per as int) == wi as int) by (nonlinear_arith)
                requires per > 0, wi == t / per_word, per == per_word as nat;
            assert((t as int % (per as int)) * (bits as int) == shift as int)
                by (nonlinear_arith)
                requires per > 0, f == t % per_word, per == per_word as nat,
                    shift == (f as u64) * (bits as u64);
        }
        let old_w = words[wi];
        proof {
            assert((old_w >> shift) & (sub(1u64 << (bits as u64), 1)) == 0u64);
        }
        let ghost pre_words = words@;
        let new_w = old_w | (code << shift);
        words.set(wi, new_w);
        proof {
            lemma_pack_field_set(old_w, code, bits as u64, shift);
            // Position t reads back its code.
            assert(packed_code_at(words@, bits as nat, t as int) == code as nat);
            // Every other covered position keeps its previous field value.
            assert forall|k: int| 0 <= k < nwords * per_word && k != t as int implies
                #[trigger] packed_code_at(words@, bits as nat, k)
                    == packed_code_at(pre_words, bits as nat, k) by {
                let kwi = k / (per as int);
                let ksh = (k % (per as int)) * (bits as int);
                if kwi == wi as int {
                    assert(0 <= ksh && ksh + bits <= 64
                        && (ksh + bits <= shift as int || shift as int + bits <= ksh))
                        by (nonlinear_arith)
                        requires per > 0, 0 <= k, k != t as int,
                            kwi == k / (per as int), kwi == wi as int,
                            ksh == (k % (per as int)) * (bits as int),
                            wi == t / per_word, per == per_word as nat,
                            f == t % per_word,
                            shift == (f as u64) * (bits as u64),
                            (bits == 1 || bits == 2 || bits == 4),
                            per_word == 64usize / (bits as usize),
                            t as int / (per as int) == wi as int,
                            (t as int % (per as int)) * (bits as int) == shift as int;
                    lemma_pack_field_other(old_w, code, bits as u64, shift, ksh as u64);
                    assert(words@[kwi] == new_w && pre_words[kwi] == old_w);
                } else {
                    assert(words@[kwi] == pre_words[kwi]);
                }
            }
        }
        t += 1;
    }
    let r = Codes::Packed { words, bits, len: n };
    proof {
        assert(r.wf()) by (nonlinear_arith)
            requires n <= nwords * per_word, r == (Codes::Packed { words, bits, len: n }),
                words@.len() == nwords, per_word == 64usize / (bits as usize),
                (bits == 1 || bits == 2 || bits == 4);
        assert forall|k: int| 0 <= k < codes@.len() implies
            #[trigger] r.view()[k] == codes@[k] as nat by {}
    }
    r
}

/// Extract the code at position `i` from bit-packed `words`. VERIFIED: the
/// body is the spec expression (`packed_code_at`) rendered in exec operators;
/// the coverage requires pins the word read in range and the shift below 64.
/// Discharged from the trust ledger 2026-09.
pub fn packed_get(words: &Vec<u64>, bits: u8, i: usize) -> (c: usize)
    requires
        bits == 1 || bits == 2 || bits == 4,
        (i as nat) < words@.len() * (64nat / (bits as nat)),
    ensures c as nat == packed_code_at(words@, bits as nat, i as int),
{
    let per_word: usize = 64 / (bits as usize);
    let wi = i / per_word;
    let f = i % per_word;
    proof {
        assert(f < per_word) by (nonlinear_arith) requires per_word > 0, f == i % per_word;
        assert((f as u64) * (bits as u64) + (bits as u64) <= 64) by (nonlinear_arith)
            requires f < per_word, per_word == 64usize / (bits as usize),
                (bits == 1 || bits == 2 || bits == 4);
    }
    let shift = (f as u64) * (bits as u64);
    proof {
        let per = per_word as nat;
        assert(wi < words@.len()) by (nonlinear_arith)
            requires per_word > 0, (i as nat) < words@.len() * (64nat / (bits as nat)),
                per == 64nat / (bits as nat), per == per_word as nat, wi == i / per_word;
        assert(f < per_word) by (nonlinear_arith) requires per_word > 0, f == i % per_word;
        assert(shift + bits <= 64) by (nonlinear_arith)
            requires f < per_word, per_word == 64usize / (bits as usize),
                (bits == 1 || bits == 2 || bits == 4),
                shift == (f as u64) * (bits as u64);
        assert(i as int / (per as int) == wi as int) by (nonlinear_arith)
            requires per > 0, wi == i / per_word, per == per_word as nat;
        assert((i as int % (per as int)) * (bits as int) == shift as int)
            by (nonlinear_arith)
            requires per > 0, f == i % per_word, per == per_word as nat,
                shift == (f as u64) * (bits as u64);
        // The extracted field fits usize: it is at most the bits-wide mask.
        let w0 = words@[wi as int];
        assert(((w0 >> shift) & (sub(1u64 << (bits as u64), 1))) <= 0xFFFFu64)
            by (bit_vector)
            requires bits == 1u8 || bits == 2u8 || bits == 4u8;
    }
    proof {
        assert(1u64 << (bits as u64) >= 1) by (bit_vector)
            requires bits == 1u8 || bits == 2u8 || bits == 4u8;
    }
    let mask = (1u64 << (bits as u64)) - 1;
    ((words[wi] >> shift) & mask) as usize
}

/// An immutable value-only frame: `dict` plus a narrow/bit-packed `codes` column,
/// no index column. This is the cold tier of the live-path value-major diff log
/// (`diff_log.rs`): one such frame per finalized frame, decoding to that frame's
/// value sequence, while the diff log keeps the index column contiguous and whole.
/// Unlike `DictFrame` it drops `idxs` (the diff log owns them), so it is the value
/// axis alone. Built once from a value slice and never appended to, which is what
/// lets its codes be sub-byte packed.
pub struct ValFrame<T> {
    pub dict: Vec<T>,
    pub codes: Codes,
}

impl<T: Copy> ValFrame<T> {
    /// Every code indexes the dictionary, over a structurally sound column.
    pub open spec fn wf(&self) -> bool {
        &&& self.codes.wf()
        &&& forall|t: int| 0 <= t < self.codes.view().len()
                ==> (#[trigger] self.codes.view()[t]) < self.dict@.len()
    }

    /// The value sequence this frame decodes to. Spec over `dict`/`codes` alone, so
    /// it needs no `IndexLike` bound (the value column consumer, `DiffVals`, is
    /// generic over `T`).
    pub open spec fn decode(&self) -> Seq<T> {
        Seq::new(self.codes.view().len(), |i: int| self.dict@[self.codes.view()[i] as int])
    }

    pub fn len(&self) -> (n: usize)
        ensures n == self.decode().len(),
    {
        self.codes.len()
    }

    /// The value at position `i` (dictionary lookup through the packed code).
    pub fn decode_at(&self, i: usize) -> (v: T)
        requires self.wf(), i < self.decode().len(),
        ensures v == self.decode()[i as int],
    {
        let c = self.codes.get(i);
        self.dict[c]
    }

    /// Length-based byte count (deterministic; for measurement).
    pub fn byte_len(&self) -> usize {
        crate::compression_stats::sat_add(
            crate::compression_stats::sat_mul(self.dict.len(), core::mem::size_of::<T>()),
            self.codes.byte_len())
    }
}

impl<T: IndexLike> ValFrame<T> {
    /// Value-dictionary-encode `vals` into an immutable frame: dedup to a dictionary
    /// (`assign_codes`, O(N) hash), then narrow the codes to the smallest width that
    /// fits (`Codes::from_usize`, bit-packed for `D <= 16`). `decode()` reproduces
    /// `vals` exactly.
    pub fn compress(vals: &Vec<T>) -> (r: ValFrame<T>)
        ensures
            r.wf(),
            r.decode() == vals@,
    {
        let (dict, ucodes) = assign_codes(vals);
        let codes = Codes::from_usize(&ucodes, dict.len());
        let r = ValFrame { dict, codes };
        assert(r.decode() =~= vals@);
        r
    }
}

/// One finalized frame's diffs with the value column dictionary-encoded and the
/// index column kept verbatim. `codes[t]` indexes `dict` to entry `t`'s value;
/// `idxs[t]` is entry `t`'s original cell index.
pub struct DictFrame<T, I> {
    pub dict: Vec<T>,
    pub codes: Codes,
    pub idxs: Vec<I>,
}

impl<T: Copy, I: IndexLike> DictFrame<T, I> {
    /// Well-formed: the code/index columns are parallel and every code indexes
    /// the dictionary. Stated over `codes.view()`, so the code storage width is
    /// invisible here.
    pub open spec fn wf(&self) -> bool {
        &&& self.codes.wf()
        &&& self.codes.view().len() == self.idxs@.len()
        &&& forall|t: int| 0 <= t < self.codes.view().len()
                ==> (#[trigger] self.codes.view()[t]) < self.dict@.len()
    }

    /// Decode back to the flat `(value, index)` diff sequence.
    pub open spec fn decode(&self) -> Seq<(T, I)> {
        Seq::new(
            self.idxs@.len(),
            |t: int| (self.dict@[self.codes.view()[t] as int], self.idxs@[t]),
        )
    }

    /// Entry count (O(1)): the index column length.
    pub fn entry_len(&self) -> (n: usize)
        requires self.wf(),
        ensures n == self.decode().len(),
    {
        self.idxs.len()
    }

    /// Random access to entry `i` (dictionary lookup through the packed code, plus the
    /// parallel index). The read a cold `Dict` frame needs for `DiffLog::index`.
    pub fn decode_at(&self, i: usize) -> (r: (T, I))
        requires self.wf(), i < self.decode().len(),
        ensures r == self.decode()[i as int],
    {
        let code = self.codes.get(i);
        (self.dict[code], self.idxs[i])
    }

    /// Executable decode: materialize the flat diff sequence. The two-stack
    /// `Vec` integration calls this to bring a compressed frame back to plain
    /// before a restore lands in it; the benchmark suite times it as the
    /// decompression cost. `r@ == decode()`, so it is transparent to the
    /// reconstruction proof.
    pub fn decode_exec(&self) -> (r: Vec<(T, I)>)
        requires self.wf(),
        ensures r@ == self.decode(),
    {
        let mut out: Vec<(T, I)> = Vec::new();
        let n = self.idxs.len();
        let mut t: usize = 0;
        while t < n
            invariant
                t <= n,
                n == self.idxs@.len(),
                self.wf(),
                out@.len() == t,
                forall|k: int| 0 <= k < t ==> out@[k] == self.decode()[k],
            decreases n - t,
        {
            let code = self.codes.get(t);
            let v = self.dict[code];
            let idx = self.idxs[t];
            out.push((v, idx));
            t += 1;
        }
        assert(out@ =~= self.decode());
        out
    }
}

/// Assign dictionary codes to a value column: `dict` holds each distinct
/// value once, `codes[t]` indexes `dict` at `vals[t]`. VERIFIED: a linear
/// dict scan per value (values compare through `as_usize`, lifted to value
/// equality by `as_nat` injectivity) replaces the unmodeled std HashMap.
/// Discharged from the trust ledger 2026-09; `dict_roundtrip` stays as a
/// belt. Cost is O(n * D) with D the dictionary size - the value-dictionary
/// mode exists precisely for small-D columns, and the all-distinct
/// worst case is the recorded upgrade trigger (a verified map, or the
/// sort-dedup construction, behind this same contract).
pub fn assign_codes<T: IndexLike>(diffs_vals: &Vec<T>) -> (r: (Vec<T>, Vec<usize>))
    ensures
        r.1@.len() == diffs_vals@.len(),
        forall|t: int| 0 <= t < diffs_vals@.len() ==> (#[trigger] r.1@[t]) < r.0@.len(),
        forall|t: int| 0 <= t < diffs_vals@.len()
            ==> r.0@[#[trigger] r.1@[t] as int] == diffs_vals@[t],
{
    let mut dict: Vec<T> = Vec::new();
    let mut codes: Vec<usize> = Vec::new();
    let n = diffs_vals.len();
    let mut t: usize = 0;
    while t < n
        invariant
            n == diffs_vals@.len(),
            0 <= t <= n,
            codes@.len() == t,
            forall|k: int| 0 <= k < t ==> (#[trigger] codes@[k]) < dict@.len(),
            forall|k: int| 0 <= k < t
                ==> dict@[#[trigger] codes@[k] as int] == diffs_vals@[k],
        decreases n - t,
    {
        let v = diffs_vals[t];
        let key = v.as_usize();
        let dlen = dict.len();
        let mut j: usize = 0;
        let mut found: bool = false;
        let mut code: usize = 0;
        while j < dlen && !found
            invariant
                dlen == dict@.len(),
                0 <= j <= dlen,
                v == diffs_vals@[t as int],
                key as nat == v.as_nat(),
                found ==> code < dict@.len() && dict@[code as int] == v,
                !found ==> forall|q: int| 0 <= q < j
                    ==> (#[trigger] dict@[q]) != v,
            decreases dlen - j + (if found { 0int } else { 1int }),
        {
            if dict[j].as_usize() == key {
                proof {
                    // as_usize agreement lifts to value equality (as_usize's
                    // ensures ties it to as_nat; injectivity closes it).
                    T::lemma_as_nat_injective(dict@[j as int], v);
                }
                code = j;
                found = true;
            } else {
                proof {
                    assert(dict@[j as int] != v);
                }
                j += 1;
            }
        }
        if !found {
            code = dict.len();
            dict.push(v);
        }
        codes.push(code);
        t += 1;
    }
    (dict, codes)
}

/// Compress a finalized frame's diffs by value-dictionary encoding.
/// The bijection: `decode(compress(d)) == d`.
pub fn compress<T: IndexLike, I: IndexLike>(diffs: &Vec<(T, I)>) -> (r: DictFrame<T, I>)
    ensures
        r.wf(),
        r.decode() == diffs@,
{
    // Split into value and index columns (indices kept verbatim).
    let mut vals: Vec<T> = Vec::new();
    let mut idxs: Vec<I> = Vec::new();
    let mut i: usize = 0;
    while i < diffs.len()
        invariant
            i <= diffs@.len(),
            vals@.len() == i,
            idxs@.len() == i,
            forall|t: int| 0 <= t < i ==> #[trigger] vals@[t] == diffs@[t].0,
            forall|t: int| 0 <= t < i ==> #[trigger] idxs@[t] == diffs@[t].1,
        decreases diffs@.len() - i,
    {
        vals.push(diffs[i].0);
        idxs.push(diffs[i].1);
        i += 1;
    }
    // O(N) dedup, then narrow codes to the smallest width indexing the dict.
    let (dict, codes) = assign_codes(&vals);
    let dict_len = dict.len();
    let packed = Codes::from_usize(&codes, dict_len);
    let r = DictFrame { dict, codes: packed, idxs };
    proof {
        assert forall|t: int| 0 <= t < diffs@.len()
            implies r.decode()[t] == diffs@[t] by {
            assert(r.codes.view()[t] == codes@[t] as nat);      // from_usize
            assert(r.dict@[codes@[t] as int] == vals@[t]);      // assign_codes
            assert(vals@[t] == diffs@[t].0);                    // split loop
            assert(r.idxs@[t] == diffs@[t].1);
        }
        assert(r.decode() =~= diffs@);
    }
    r
}

// ---------------------------------------------------------------------------
// Index axis: run-coalescing encoder
// ---------------------------------------------------------------------------

/// Expand one run: `vals` laid at consecutive indices `start, start+1, ...`.
pub open spec fn expand_run<T>(start: nat, vals: Seq<T>) -> Seq<(T, nat)>
    decreases vals.len(),
{
    if vals.len() == 0 {
        Seq::empty()
    } else {
        seq![(vals[0], start)] + expand_run(start + 1, vals.subrange(1, vals.len() as int))
    }
}

/// Expand a run list to the flat `(value, index)` sequence.
pub open spec fn expand_runs<T>(starts: Seq<nat>, vals: Seq<Seq<T>>) -> Seq<(T, nat)>
    decreases starts.len(),
{
    if starts.len() == 0 || vals.len() == 0 {
        Seq::empty()
    } else {
        expand_run(starts[0], vals[0]) + expand_runs(
            starts.subrange(1, starts.len() as int),
            vals.subrange(1, vals.len() as int),
        )
    }
}

/// `expand_run` appends at the end: laying one more value `v` at `start +
/// vals.len()` extends the expansion by exactly `(v, start + vals.len())`.
pub proof fn lemma_expand_run_push<T>(start: nat, vals: Seq<T>, v: T)
    ensures
        expand_run(start, vals.push(v))
            == expand_run(start, vals) + seq![(v, start + vals.len())],
    decreases vals.len(),
{
    reveal_with_fuel(expand_run, 2);
    if vals.len() == 0 {
        assert(vals.push(v) =~= seq![v]);
        assert(expand_run(start, vals) =~= Seq::<(T, nat)>::empty());
        assert(expand_run(start, vals.push(v)) =~= seq![(v, start)]);
        assert(expand_run(start, vals) + seq![(v, start + vals.len())] =~= seq![(v, start)]);
    } else {
        // head stays; recurse on the tail, which is `vals[1..].push(v)`.
        let tail = vals.subrange(1, vals.len() as int);
        lemma_expand_run_push(start + 1, tail, v);
        assert(tail.len() == (vals.len() - 1) as nat);
        // unfold the LHS one step: head is `vals[0]`, tail becomes `tail.push(v)`.
        assert(vals.push(v)[0] == vals[0]);
        assert(vals.push(v).subrange(1, vals.push(v).len() as int) =~= tail.push(v));
        assert(expand_run(start, vals.push(v))
            == seq![(vals[0], start)] + expand_run(start + 1, tail.push(v)));
        // IH gives the tail expansion; the appended index reassociates to `start + vals.len()`.
        assert((start + 1) + tail.len() == start + vals.len());
        assert(expand_run(start + 1, tail.push(v))
            == expand_run(start + 1, tail) + seq![(v, start + vals.len())]);
        // unfold the RHS's `expand_run(start, vals)` one step, then reassociate the
        // three concrete sub-sequences explicitly (Verus does not reassociate `+`
        // over the recursive subterms on its own).
        let a = seq![(vals[0], start)];
        let b = expand_run(start + 1, tail);
        let c = seq![(v, start + vals.len())];
        assert(expand_run(start, vals) == a + b);
        assert(expand_run(start, vals.push(v)) == a + (b + c));
        assert(a + (b + c) =~= (a + b) + c);
        assert(expand_run(start, vals.push(v)) == expand_run(start, vals) + c);
    }
}

/// `expand_run` lays `vals` at consecutive indices: entry `o` is `(vals[o],
/// start + o)`, and the length is `vals.len()`. The pointwise fact the run
/// decoder needs to reconstruct each dropped index from `start + offset`.
pub proof fn lemma_expand_run_index<T>(start: nat, vals: Seq<T>)
    ensures
        expand_run(start, vals).len() == vals.len(),
        forall|o: int| 0 <= o < vals.len() ==>
            #[trigger] expand_run(start, vals)[o] == (vals[o], (start + o) as nat),
    decreases vals.len(),
{
    reveal_with_fuel(expand_run, 2);
    if vals.len() == 0 {
    } else {
        let tail = vals.subrange(1, vals.len() as int);
        lemma_expand_run_index(start + 1, tail);
        // expand_run(start, vals) == [(vals[0], start)] + expand_run(start+1, tail)
        assert forall|o: int| 0 <= o < vals.len() implies
            #[trigger] expand_run(start, vals)[o] == (vals[o], (start + o) as nat) by {
            if o == 0 {
            } else {
                assert(tail[o - 1] == vals[o]);
                assert(expand_run(start, vals)[o] == expand_run(start + 1, tail)[o - 1]);
            }
        }
    }
}

/// Appending a whole new run to the end of a run list appends that run's
/// expansion to the end of the flattened result.
pub proof fn lemma_expand_runs_snoc<T>(starts: Seq<nat>, vals: Seq<Seq<T>>, s: nat, vs: Seq<T>)
    requires
        starts.len() == vals.len(),
    ensures
        expand_runs(starts.push(s), vals.push(vs))
            == expand_runs(starts, vals) + expand_run(s, vs),
    decreases starts.len(),
{
    reveal_with_fuel(expand_runs, 2);
    if starts.len() == 0 {
        assert(starts.push(s) =~= seq![s]);
        assert(vals.push(vs) =~= seq![vs]);
        assert(expand_runs(starts, vals) =~= Seq::<(T, nat)>::empty());
        assert(seq![s].subrange(1, 1) =~= Seq::<nat>::empty());
        assert(seq![vs].subrange(1, 1) =~= Seq::<Seq<T>>::empty());
        assert(expand_runs(seq![s], seq![vs]) =~= expand_run(s, vs));
    } else {
        let rs = starts.subrange(1, starts.len() as int);
        let rv = vals.subrange(1, vals.len() as int);
        lemma_expand_runs_snoc(rs, rv, s, vs);
        assert(starts.push(s)[0] == starts[0]);
        assert(vals.push(vs)[0] == vals[0]);
        assert(starts.push(s).subrange(1, starts.push(s).len() as int) =~= rs.push(s));
        assert(vals.push(vs).subrange(1, vals.push(vs).len() as int) =~= rv.push(vs));
        let a = expand_run(starts[0], vals[0]);
        let b = expand_runs(rs, rv);
        let c = expand_run(s, vs);
        assert(expand_runs(starts.push(s), vals.push(vs))
            == a + expand_runs(rs.push(s), rv.push(vs)));
        assert(expand_runs(rs.push(s), rv.push(vs)) == b + c);
        assert(expand_runs(starts, vals) == a + b);
        assert(expand_runs(starts.push(s), vals.push(vs)) == a + (b + c));
        assert(a + (b + c) =~= (a + b) + c);
        assert(expand_runs(starts.push(s), vals.push(vs)) == expand_runs(starts, vals) + c);
    }
}

/// `expand_runs` splits at any run boundary: the flat expansion of the whole
/// list is the expansion of the first `r` runs followed by the expansion of
/// the rest. The prefix/position bridge the verified run decoder walks.
pub proof fn lemma_expand_runs_split<T>(starts: Seq<nat>, vals: Seq<Seq<T>>, r: int)
    requires
        starts.len() == vals.len(),
        0 <= r <= starts.len(),
    ensures
        expand_runs(starts, vals)
            == expand_runs(starts.take(r), vals.take(r))
                + expand_runs(starts.skip(r), vals.skip(r)),
    decreases r,
{
    reveal_with_fuel(expand_runs, 2);
    if r == 0 {
        assert(starts.take(0) =~= Seq::<nat>::empty());
        assert(vals.take(0) =~= Seq::<Seq<T>>::empty());
        assert(starts.skip(0) =~= starts);
        assert(vals.skip(0) =~= vals);
        assert(expand_runs(starts.take(0), vals.take(0)) =~= Seq::<(T, nat)>::empty());
        assert(expand_runs(starts.take(0), vals.take(0)) + expand_runs(starts, vals)
            =~= expand_runs(starts, vals));
    } else {
        let ts = starts.subrange(1, starts.len() as int);
        let tv = vals.subrange(1, vals.len() as int);
        lemma_expand_runs_split(ts, tv, r - 1);
        // Head-unfold both the whole and the taken prefix.
        let a = expand_run(starts[0], vals[0]);
        assert(expand_runs(starts, vals) == a + expand_runs(ts, tv));
        assert(starts.take(r)[0] == starts[0]);
        assert(vals.take(r)[0] == vals[0]);
        assert(starts.take(r).subrange(1, r) =~= ts.take(r - 1));
        assert(vals.take(r).subrange(1, r) =~= tv.take(r - 1));
        assert(expand_runs(starts.take(r), vals.take(r))
            == a + expand_runs(ts.take(r - 1), tv.take(r - 1)));
        assert(starts.skip(r) =~= ts.skip(r - 1));
        assert(vals.skip(r) =~= tv.skip(r - 1));
        let b = expand_runs(ts.take(r - 1), tv.take(r - 1));
        let c = expand_runs(ts.skip(r - 1), tv.skip(r - 1));
        assert(expand_runs(ts, tv) == b + c);
        assert(a + (b + c) =~= (a + b) + c);
    }
}

/// Index-major run-coalescing encoding of one finalized frame, proven bijective
/// against a sorted-strictly-ascending-by-index diff sequence at the `nat` index
/// level (`Vec` integration materializes `I` from these `usize` starts via
/// `try_from_usize`). `starts[r]` is run `r`'s first index; `vals[r]` its
/// values, laid at consecutive indices.
pub struct RunFrame<T> {
    pub starts: Vec<usize>,
    pub vals: Vec<Vec<T>>,
}

impl<T: Copy> RunFrame<T> {
    /// Run values as a `Seq<Seq<T>>`.
    pub open spec fn vals_seq(&self) -> Seq<Seq<T>> {
        Seq::new(self.vals@.len(), |r: int| self.vals@[r]@)
    }

    /// Run starts as a `Seq<nat>`.
    pub open spec fn starts_nat(&self) -> Seq<nat> {
        Seq::new(self.starts@.len(), |r: int| self.starts@[r] as nat)
    }

    pub open spec fn wf(&self) -> bool {
        self.starts@.len() == self.vals@.len()
    }

    pub open spec fn decode(&self) -> Seq<(T, nat)> {
        expand_runs(self.starts_nat(), self.vals_seq())
    }

    /// Decode to `(T, I)` diffs, reconstructing each dropped index from its `nat`
    /// via `from_nat`. Well-defined when every decoded index fits `I` (`fits`),
    /// which holds for any run frame built from real `I` indices.
    pub open spec fn decode_i<I: IndexFromNat>(&self) -> Seq<(T, I)> {
        Seq::new(
            self.decode().len(),
            |t: int| (self.decode()[t].0, I::from_nat(self.decode()[t].1)),
        )
    }

    /// Every decoded index is a valid `I` (below `max_nat`). Established at
    /// compress time: the indices came from real `I` values.
    pub open spec fn fits<I: IndexFromNat>(&self) -> bool {
        forall|t: int| 0 <= t < self.decode().len() ==> (#[trigger] self.decode()[t].1) < I::max_nat()
    }

    /// Executable decode to `(T, I)`, VERIFIED against the `decode_i` spec: the
    /// outer loop carries "out equals the expansion of the first `r` runs,
    /// index-mapped", bridged to the full decode by `lemma_expand_runs_split`;
    /// the inner loop lays one run pointwise via `lemma_expand_run_index`, and
    /// `fits` discharges both the `from_usize` success and the `start + off`
    /// non-overflow (`max_nat` fits `usize`). Discharged from the trust ledger
    /// 2026-09: formerly `external_body` with the `run_frame_roundtrip`
    /// proptest as its only check; the proptest stays as a belt.
    pub fn decode_exec_i<I: IndexFromNat>(&self) -> (r: Vec<(T, I)>)
        requires self.wf(), self.fits::<I>(),
        ensures r@ == self.decode_i::<I>(),
    {
        let ghost sn = self.starts_nat();
        let ghost vv = self.vals_seq();
        let ghost full = self.decode();
        let mut out: Vec<(T, I)> = Vec::new();
        let nruns = self.starts.len();
        let mut r: usize = 0;
        while r < nruns
            invariant
                self.wf(),
                self.fits::<I>(),
                sn == self.starts_nat(),
                vv == self.vals_seq(),
                full == self.decode(),
                0 <= r <= nruns,
                nruns == self.starts@.len(),
                out@.len() == expand_runs(sn.take(r as int), vv.take(r as int)).len(),
                forall|t: int| 0 <= t < out@.len() ==> {
                    let pre = expand_runs(sn.take(r as int), vv.take(r as int));
                    #[trigger] out@[t] == (pre[t].0, I::from_nat(pre[t].1))
                },
            decreases nruns - r,
        {
            let start = self.starts[r];
            let run = &self.vals[r];
            let ghost base = expand_runs(sn.take(r as int), vv.take(r as int));
            let ghost rest_head = expand_run(sn[r as int], vv[r as int]);
            proof {
                // full == base + (current run's expansion + remainder): the
                // split at r, then one head-unfold of the skipped part.
                lemma_expand_runs_split(sn, vv, r as int);
                reveal_with_fuel(expand_runs, 2);
                assert(sn.skip(r as int)[0] == sn[r as int]);
                assert(vv.skip(r as int)[0] == vv[r as int]);
                assert(sn.skip(r as int).subrange(1, sn.skip(r as int).len() as int)
                    =~= sn.skip(r as int + 1));
                assert(vv.skip(r as int).subrange(1, vv.skip(r as int).len() as int)
                    =~= vv.skip(r as int + 1));
                assert(expand_runs(sn.skip(r as int), vv.skip(r as int))
                    == rest_head + expand_runs(sn.skip(r as int + 1), vv.skip(r as int + 1)));
                lemma_expand_run_index(sn[r as int], vv[r as int]);
            }
            let mut off: usize = 0;
            while off < run.len()
                invariant
                    self.wf(),
                    self.fits::<I>(),
                    sn == self.starts_nat(),
                    vv == self.vals_seq(),
                    full == self.decode(),
                    0 <= r < nruns,
                    nruns == self.starts@.len(),
                    0 <= off <= run@.len(),
                    run@ == self.vals@[r as int]@,
                    start == self.starts@[r as int],
                    base == expand_runs(sn.take(r as int), vv.take(r as int)),
                    rest_head == expand_run(sn[r as int], vv[r as int]),
                    full == base + rest_head
                        + expand_runs(sn.skip(r as int + 1), vv.skip(r as int + 1)),
                    rest_head.len() == run@.len(),
                    forall|o: int| 0 <= o < run@.len() ==>
                        #[trigger] rest_head[o] == (run@[o], (start + o) as nat),
                    out@.len() == base.len() + off,
                    forall|t: int| 0 <= t < base.len() ==>
                        #[trigger] out@[t] == (base[t].0, I::from_nat(base[t].1)),
                    forall|o: int| 0 <= o < off ==>
                        #[trigger] out@[base.len() + o]
                            == (rest_head[o].0, I::from_nat(rest_head[o].1)),
                decreases run@.len() - off,
            {
                proof {
                    // The global position of this entry inside the full decode
                    // pins its index below max_nat (fits), which also bounds
                    // the usize sum.
                    let gpos = base.len() + off;
                    assert(full[gpos as int] == rest_head[off as int]);
                    assert(full[gpos as int].1 == (start + off) as nat);
                    assert(((start + off) as nat) < I::max_nat());
                    I::lemma_max_nat_fits_usize();
                }
                let idx = match I::from_usize(start + off) {
                    Some(i) => i,
                    None => {
                        proof { assert(false); }
                        crate::guard::refuse("run index fits I (established by fits)")
                    }
                };
                out.push((run[off], idx));
                off += 1;
            }
            proof {
                // Fold the completed run into the prefix: take(r+1) is
                // take(r) plus this run, and its expansion appends rest_head.
                lemma_expand_runs_snoc(
                    sn.take(r as int), vv.take(r as int), sn[r as int], vv[r as int]);
                assert(sn.take(r as int + 1) =~= sn.take(r as int).push(sn[r as int]));
                assert(vv.take(r as int + 1) =~= vv.take(r as int).push(vv[r as int]));
                assert(expand_runs(sn.take(r as int + 1), vv.take(r as int + 1))
                    == base + rest_head);
                // Merge the two pointwise loop facts into the prefix form the
                // outer invariant states at r + 1 (concat indexing case split).
                assert forall|t: int| 0 <= t < out@.len() implies {
                    let pre = expand_runs(sn.take(r as int + 1), vv.take(r as int + 1));
                    #[trigger] out@[t] == (pre[t].0, I::from_nat(pre[t].1))
                } by {
                    let pre = base + rest_head;
                    if t < base.len() {
                        assert(pre[t] == base[t]);
                    } else {
                        let o = t - base.len();
                        assert(pre[t] == rest_head[o]);
                        // Instantiate the inner-loop fact at o via its own
                        // trigger shape, then rewrite the position.
                        assert(out@[base.len() + o]
                            == (rest_head[o].0, I::from_nat(rest_head[o].1)));
                        assert(base.len() + o == t);
                    }
                }
            }
            r += 1;
        }
        proof {
            assert(sn.take(nruns as int) =~= sn);
            assert(vv.take(nruns as int) =~= vv);
            assert(out@ =~= self.decode_i::<I>());
        }
        out
    }
}

/// The diff sequence with indices projected to `nat` — the abstract target the
/// run encoder reproduces.
pub open spec fn mapped_diffs<T>(d: Seq<(T, usize)>, n: nat) -> Seq<(T, nat)> {
    Seq::new(n, |t: int| (d[t as int].0, d[t as int].1 as nat))
}

/// Local run-list `starts` projected to `nat` (matches `RunFrame::starts_nat`).
pub open spec fn starts_to_nat(s: Seq<usize>) -> Seq<nat> {
    Seq::new(s.len(), |r: int| s[r] as nat)
}

/// Local run-list `vals` projected to `Seq<Seq<T>>` (matches `RunFrame::vals_seq`).
pub open spec fn vals_to_seq<T>(v: Seq<Vec<T>>) -> Seq<Seq<T>> {
    Seq::new(v.len(), |r: int| v[r]@)
}

/// `mapped_diffs` extends by one element as `n` grows.
pub proof fn lemma_mapped_push<T>(d: Seq<(T, usize)>, n: nat)
    requires
        n < d.len(),
    ensures
        mapped_diffs(d, n + 1) == mapped_diffs(d, n) + seq![(d[n as int].0, d[n as int].1 as nat)],
{
    assert(mapped_diffs(d, n + 1)
        =~= mapped_diffs(d, n) + seq![(d[n as int].0, d[n as int].1 as nat)]);
}

/// Encode a finalized frame (sorted strictly ascending by index) as run-coalesced
/// runs. The bijection: `decode(compress_runs(d)) == d` at the `nat` index level.
/// `rlimit` pinned: the run-coalescing invariant carries several `expand_*`
/// sequence identities whose instantiation is near the default budget (z3-seed
/// flaky otherwise).
#[verifier::rlimit(800)]
pub fn compress_runs<T: Copy>(diffs: &Vec<(T, usize)>) -> (r: RunFrame<T>)
    requires
        forall|a: int, b: int| #![trigger diffs@[a].1, diffs@[b].1]
            0 <= a < b < diffs@.len() ==> diffs@[a].1 < diffs@[b].1,
    ensures
        r.wf(),
        r.decode() == mapped_diffs(diffs@, diffs@.len()),
{
    let mut starts: Vec<usize> = Vec::new();
    let mut vals: Vec<Vec<T>> = Vec::new();
    let mut cur_start: usize = 0;
    let mut cur_vals: Vec<T> = Vec::new();
    let mut i: usize = 0;
    while i < diffs.len()
        invariant
            i <= diffs@.len(),
            starts@.len() == vals@.len(),
            expand_runs(starts_to_nat(starts@), vals_to_seq(vals@))
                + expand_run(cur_start as nat, cur_vals@)
                == mapped_diffs(diffs@, i as nat),
            (cur_vals@.len() == 0) <==> (i == 0),
            cur_vals@.len() > 0
                ==> cur_start as nat == diffs@[i as int - cur_vals@.len()].1 as nat,
            cur_vals@.len() > 0
                ==> cur_start as nat + cur_vals@.len() - 1 == diffs@[i as int - 1].1 as nat,
            forall|a: int, b: int| #![trigger diffs@[a].1, diffs@[b].1]
                0 <= a < b < diffs@.len() ==> diffs@[a].1 < diffs@[b].1,
        decreases diffs@.len() - i,
    {
        let v = diffs[i].0;
        let idx = diffs[i].1;
        let ghost old_starts = starts@;
        let ghost old_vals = vals@;
        let ghost old_cur_start = cur_start;
        let ghost old_cur_vals = cur_vals@;
        if cur_vals.len() == 0 {
            cur_start = idx;
            cur_vals.push(v);
            proof {
                lemma_expand_run_push(idx as nat, Seq::<T>::empty(), v);
                assert(Seq::<T>::empty().push(v) =~= cur_vals@);
                assert(expand_run(idx as nat, cur_vals@) =~= seq![(v, idx as nat)]);
                lemma_mapped_push(diffs@, i as nat);
            }
        } else if idx - cur_start == cur_vals.len() {
            proof {
                lemma_expand_run_push(cur_start as nat, cur_vals@, v);
            }
            cur_vals.push(v);
            proof {
                assert(old_cur_vals.push(v) =~= cur_vals@);
                assert(cur_start as nat + old_cur_vals.len() == idx as nat);
                let a = expand_runs(starts_to_nat(starts@), vals_to_seq(vals@));
                let b = expand_run(cur_start as nat, old_cur_vals);
                let c = seq![(v, idx as nat)];
                assert(expand_run(cur_start as nat, cur_vals@) == b + c);
                assert(a + (b + c) =~= (a + b) + c);
                lemma_mapped_push(diffs@, i as nat);
            }
        } else {
            proof {
                lemma_expand_runs_snoc(starts_to_nat(starts@), vals_to_seq(vals@),
                    cur_start as nat, cur_vals@);
            }
            starts.push(cur_start);
            vals.push(cur_vals);
            cur_start = idx;
            cur_vals = Vec::new();
            cur_vals.push(v);
            proof {
                assert(starts_to_nat(starts@) =~= starts_to_nat(old_starts).push(old_cur_start as nat));
                assert(vals_to_seq(vals@) =~= vals_to_seq(old_vals).push(old_cur_vals));
                lemma_expand_run_push(idx as nat, Seq::<T>::empty(), v);
                assert(Seq::<T>::empty().push(v) =~= cur_vals@);
                assert(expand_run(idx as nat, cur_vals@) =~= seq![(v, idx as nat)]);
                let a = expand_runs(starts_to_nat(old_starts), vals_to_seq(old_vals));
                let b = expand_run(old_cur_start as nat, old_cur_vals);
                let c = seq![(v, idx as nat)];
                assert(expand_runs(starts_to_nat(starts@), vals_to_seq(vals@)) == a + b);
                assert(a + b + c =~= (a + b) + c);
                lemma_mapped_push(diffs@, i as nat);
            }
        }
        i += 1;
    }
    // Loop exit: i == diffs.len(), so the invariant reads
    //   expand_runs(sn(starts@), vs(vals@)) + expand_run(cur_start, cur_vals@)
    //     == mapped_diffs(diffs@, diffs@.len()).
    let ghost pre_starts = starts@;
    let ghost pre_vals = vals@;
    let ghost pre_cur_start = cur_start;
    let ghost pre_cur_vals = cur_vals@;
    if cur_vals.len() > 0 {
        starts.push(cur_start);
        vals.push(cur_vals);
        proof {
            lemma_expand_runs_snoc(starts_to_nat(pre_starts), vals_to_seq(pre_vals),
                pre_cur_start as nat, pre_cur_vals);
            assert(starts_to_nat(starts@) =~= starts_to_nat(pre_starts).push(pre_cur_start as nat));
            assert(vals_to_seq(vals@) =~= vals_to_seq(pre_vals).push(pre_cur_vals));
        }
    } else {
        proof {
            // cur empty ⇒ i == 0 ⇒ diffs empty; the current-run term is empty, so
            // the flushed runs alone reproduce the (empty) mapped sequence.
            assert(expand_run(cur_start as nat, cur_vals@) =~= Seq::<(T, nat)>::empty());
        }
    }
    let r = RunFrame { starts, vals };
    proof {
        assert(r.starts_nat() =~= starts_to_nat(r.starts@));
        assert(r.vals_seq() =~= vals_to_seq(r.vals@));
    }
    r
}

/// Write-order run-coalescing: coalesces only entries that are consecutive in
/// BOTH capture order and index (`idx == cur_start + cur_vals.len()`), so it
/// reproduces the input sequence EXACTLY — no sort, no reorder — hence
/// `decode(compress_runs_writeorder(d)) == mapped_diffs(d)` for ANY `d`. This is
/// the encoder the two-stack uses: it preserves the flat view exactly (unlike a
/// sort-first index-major encoder, which would permute the frame), so the
/// mark/restore theorems carry. It coalesces a contiguous range only when it was
/// captured in ascending order; scattered or descending captures fall back to
/// singleton runs (correct, just uncompressed). The `idx >= cur_start` guard
/// makes the run-extension test underflow-free without a sortedness precondition.
#[verifier::rlimit(800)]
pub fn compress_runs_writeorder<T: Copy>(diffs: &Vec<(T, usize)>) -> (r: RunFrame<T>)
    ensures
        r.wf(),
        r.decode() == mapped_diffs(diffs@, diffs@.len()),
{
    let mut starts: Vec<usize> = Vec::new();
    let mut vals: Vec<Vec<T>> = Vec::new();
    let mut cur_start: usize = 0;
    let mut cur_vals: Vec<T> = Vec::new();
    let mut i: usize = 0;
    while i < diffs.len()
        invariant
            i <= diffs@.len(),
            starts@.len() == vals@.len(),
            expand_runs(starts_to_nat(starts@), vals_to_seq(vals@))
                + expand_run(cur_start as nat, cur_vals@)
                == mapped_diffs(diffs@, i as nat),
            (cur_vals@.len() == 0) <==> (i == 0),
        decreases diffs@.len() - i,
    {
        let v = diffs[i].0;
        let idx = diffs[i].1;
        let ghost old_starts = starts@;
        let ghost old_vals = vals@;
        let ghost old_cur_start = cur_start;
        let ghost old_cur_vals = cur_vals@;
        if cur_vals.len() == 0 {
            cur_start = idx;
            cur_vals.push(v);
            proof {
                lemma_expand_run_push(idx as nat, Seq::<T>::empty(), v);
                assert(Seq::<T>::empty().push(v) =~= cur_vals@);
                assert(expand_run(idx as nat, cur_vals@) =~= seq![(v, idx as nat)]);
                lemma_mapped_push(diffs@, i as nat);
            }
        } else if idx >= cur_start && idx - cur_start == cur_vals.len() {
            proof {
                lemma_expand_run_push(cur_start as nat, cur_vals@, v);
            }
            cur_vals.push(v);
            proof {
                assert(old_cur_vals.push(v) =~= cur_vals@);
                assert(cur_start as nat + old_cur_vals.len() == idx as nat);
                let a = expand_runs(starts_to_nat(starts@), vals_to_seq(vals@));
                let b = expand_run(cur_start as nat, old_cur_vals);
                let c = seq![(v, idx as nat)];
                assert(expand_run(cur_start as nat, cur_vals@) == b + c);
                assert(a + (b + c) =~= (a + b) + c);
                lemma_mapped_push(diffs@, i as nat);
            }
        } else {
            proof {
                lemma_expand_runs_snoc(starts_to_nat(starts@), vals_to_seq(vals@),
                    cur_start as nat, cur_vals@);
            }
            starts.push(cur_start);
            vals.push(cur_vals);
            cur_start = idx;
            cur_vals = Vec::new();
            cur_vals.push(v);
            proof {
                assert(starts_to_nat(starts@) =~= starts_to_nat(old_starts).push(old_cur_start as nat));
                assert(vals_to_seq(vals@) =~= vals_to_seq(old_vals).push(old_cur_vals));
                lemma_expand_run_push(idx as nat, Seq::<T>::empty(), v);
                assert(Seq::<T>::empty().push(v) =~= cur_vals@);
                assert(expand_run(idx as nat, cur_vals@) =~= seq![(v, idx as nat)]);
                let a = expand_runs(starts_to_nat(old_starts), vals_to_seq(old_vals));
                let b = expand_run(old_cur_start as nat, old_cur_vals);
                let c = seq![(v, idx as nat)];
                assert(expand_runs(starts_to_nat(starts@), vals_to_seq(vals@)) == a + b);
                assert(a + b + c =~= (a + b) + c);
                lemma_mapped_push(diffs@, i as nat);
            }
        }
        i += 1;
    }
    let ghost pre_starts = starts@;
    let ghost pre_vals = vals@;
    let ghost pre_cur_start = cur_start;
    let ghost pre_cur_vals = cur_vals@;
    if cur_vals.len() > 0 {
        starts.push(cur_start);
        vals.push(cur_vals);
        proof {
            lemma_expand_runs_snoc(starts_to_nat(pre_starts), vals_to_seq(pre_vals),
                pre_cur_start as nat, pre_cur_vals);
            assert(starts_to_nat(starts@) =~= starts_to_nat(pre_starts).push(pre_cur_start as nat));
            assert(vals_to_seq(vals@) =~= vals_to_seq(pre_vals).push(pre_cur_vals));
        }
    } else {
        proof {
            assert(expand_run(cur_start as nat, cur_vals@) =~= Seq::<(T, nat)>::empty());
        }
    }
    let r = RunFrame { starts, vals };
    proof {
        assert(r.starts_nat() =~= starts_to_nat(r.starts@));
        assert(r.vals_seq() =~= vals_to_seq(r.vals@));
    }
    r
}

/// `unique_idx` is invariant under permutation (multiset equality): a
/// duplicated pair is visible in the multiset, and two distinct pairs sharing
/// an index in one sequence both occur in the other.
pub proof fn lemma_unique_idx_multiset<T, I: IndexLike>(s1: Seq<(T, I)>, s2: Seq<(T, I)>)
    requires
        s1.to_multiset() == s2.to_multiset(),
        unique_idx(s1),
    ensures
        unique_idx(s2),
{
    broadcast use vstd::seq_lib::group_to_multiset_ensures;
    assert(s1.no_duplicates()) by {
        assert forall|a: int, b: int| 0 <= a < b < s1.len()
            implies s1[a] != s1[b] by {
            assert(s1[a].1.as_nat() != s1[b].1.as_nat());
        }
    }
    s1.lemma_multiset_has_no_duplicates();
    s2.lemma_multiset_has_no_duplicates_conv();
    assert(s2.no_duplicates());
    assert forall|a: int, b: int|
        0 <= a < s2.len() && 0 <= b < s2.len() && a != b
        implies (#[trigger] s2[a]).1.as_nat() != (#[trigger] s2[b]).1.as_nat() by {
        let x = s2[a];
        let y = s2[b];
        assert(x != y);
        if x.1.as_nat() == y.1.as_nat() {
            assert(s2.contains(x) && s2.contains(y));
            vstd::seq_lib::to_multiset_contains(s2, x);
            vstd::seq_lib::to_multiset_contains(s2, y);
            vstd::seq_lib::to_multiset_contains(s1, x);
            vstd::seq_lib::to_multiset_contains(s1, y);
            assert(s1.contains(x) && s1.contains(y));
            let ia = choose|k: int| 0 <= k < s1.len() && s1[k] == x;
            let ib = choose|k: int| 0 <= k < s1.len() && s1[k] == y;
            assert(ia != ib);
            assert(s1[ia].1.as_nat() != s1[ib].1.as_nat());
        }
    }
}

/// Sorted-and-adjacent-distinct implies globally strict: the little induction
/// the verified uniqueness scan rests on.
proof fn lemma_sorted_distinct_strict<T, I: IndexLike>(r: Seq<(T, I)>, a: int, b: int)
    requires
        forall|x: int, y: int| 0 <= x < y < r.len()
            ==> (#[trigger] r[x]).1.as_nat() <= (#[trigger] r[y]).1.as_nat(),
        forall|x: int| 0 <= x < r.len() - 1
            ==> (#[trigger] r[x]).1.as_nat() != r[x + 1].1.as_nat(),
        0 <= a < b < r.len(),
    ensures
        r[a].1.as_nat() < r[b].1.as_nat(),
    decreases b - a,
{
    if b == a + 1 {
        assert(r[a].1.as_nat() != r[a + 1].1.as_nat());
    } else {
        lemma_sorted_distinct_strict::<T, I>(r, a, b - 1);
        assert(r[b - 1].1.as_nat() != r[b].1.as_nat());
    }
}

/// Sort one finalized frame ascending by index. VERIFIED insertion sort by
/// adjacent swaps: each swap is `remove(j).insert(j-1, ..)` at the spec level,
/// so the multiset is preserved by the vstd lemmas; sortedness is the standard
/// insertion invariant; uniqueness transfers through the permutation via the
/// no-duplicates bridge (a duplicate index in the output would need either a
/// duplicated pair, impossible when the input's pairs are distinct, or two
/// distinct pairs sharing an index, which the input forbids). Discharged from
/// the trust ledger 2026-09 (formerly `sort_unstable_by_key` behind a trusted
/// contract); the `sort_frame_roundtrip` proptest stays as a belt. Insertion
/// sort is O(n) on the ascending capture order the write path usually
/// produces; if an adversarial frame profile ever measures the quadratic
/// worst case, the upgrade path is a verified merge sort behind this same
/// contract.
pub fn sort_frame_by_index<T: Copy, I: IndexLike>(d: &Vec<(T, I)>) -> (r: Vec<(T, I)>)
    ensures
        r@.len() == d@.len(),
        r@.to_multiset() == d@.to_multiset(),
        forall|a: int, b: int| 0 <= a < b < r@.len()
            ==> (#[trigger] r@[a]).1.as_nat() <= (#[trigger] r@[b]).1.as_nat(),
        unique_idx(d@) ==> unique_idx(r@),
{
    broadcast use vstd::seq_lib::group_to_multiset_ensures;
    let mut r: Vec<(T, I)> = Vec::new();
    let n = d.len();
    let mut c: usize = 0;
    while c < n
        invariant c <= n, n == d@.len(), r@ =~= d@.subrange(0, c as int),
        decreases n - c,
    {
        r.push(d[c]);
        c += 1;
    }
    proof {
        assert(r@ =~= d@);
    }
    let mut i: usize = if n == 0 { 0 } else { 1 };
    while i < n
        invariant
            n == r@.len(),
            n == d@.len(),
            i <= n,
            n == 0 || 1 <= i,
            r@.to_multiset() == d@.to_multiset(),
            forall|a: int, b: int| 0 <= a < b < i
                ==> (#[trigger] r@[a]).1.as_nat() <= (#[trigger] r@[b]).1.as_nat(),
        decreases n - i,
    {
        let mut j: usize = i;
        while j > 0 && r[j - 1].1.as_usize() > r[j].1.as_usize()
            invariant
                n == r@.len(),
                n == d@.len(),
                0 <= j <= i < n,
                r@.to_multiset() == d@.to_multiset(),
                // Ordered among positions [0, i] excluding the hole j.
                forall|a: int, b: int| 0 <= a < b <= i as int && a != j && b != j
                    ==> (#[trigger] r@[a]).1.as_nat() <= (#[trigger] r@[b]).1.as_nat(),
                // The moving element is below everything after the hole.
                forall|b: int| j < b <= i as int
                    ==> r@[j as int].1.as_nat() <= (#[trigger] r@[b]).1.as_nat(),
            decreases j,
        {
            let x = r[j - 1];
            let y = r[j];
            let ghost pre = r@;
            r.set(j - 1, y);
            r.set(j, x);
            proof {
                assert(r@ =~= pre.remove(j as int).insert(j as int - 1, pre[j as int]));
                vstd::seq_lib::to_multiset_remove(pre, j as int);
                vstd::seq_lib::to_multiset_insert(
                    pre.remove(j as int), j as int - 1, pre[j as int]);
                assert(pre.to_multiset().count(pre[j as int]) >= 1) by {
                    assert(pre.contains(pre[j as int]));
                    vstd::seq_lib::to_multiset_contains(pre, pre[j as int]);
                }
                assert(pre.to_multiset().remove(pre[j as int]).insert(pre[j as int])
                    =~= pre.to_multiset()) by {
                    broadcast use vstd::multiset::group_multiset_axioms;
                }
            }
            j -= 1;
        }
        proof {
            // Loop exit: hole at 0, or in-order with its predecessor; either
            // way [0, i] is fully sorted.
            assert forall|a: int, b: int| 0 <= a < b <= i as int implies
                (#[trigger] r@[a]).1.as_nat() <= (#[trigger] r@[b]).1.as_nat() by {
                if a == j as int {
                    // covered by the hole clause
                } else if b == j as int {
                    assert(j > 0);
                    assert(r@[j as int - 1].1.as_nat() <= r@[j as int].1.as_nat());
                    if a < j as int - 1 {
                        assert(r@[a].1.as_nat() <= r@[j as int - 1].1.as_nat());
                    }
                }
            }
        }
        i += 1;
    }
    proof {
        if unique_idx(d@) {
            lemma_unique_idx_multiset(d@, r@);
        }
    }
    r
}

/// A finalized frame has at most one write per cell (first-write-wins), so its
/// index projection is injective. Mirrors `vec::unique_idx` for the encoder side.
pub open spec fn unique_idx<T, I: IndexLike>(d: Seq<(T, I)>) -> bool {
    forall|a: int, b: int|
        0 <= a < d.len() && 0 <= b < d.len() && a != b
            ==> (#[trigger] d[a]).1.as_nat() != (#[trigger] d[b]).1.as_nat()
}

/// Runtime `unique_idx` check: does the frame write each cell at most once?
/// VERIFIED via the verified sort: sort a copy, scan adjacent indices. An
/// adjacent equal pair falsifies uniqueness of the sorted copy, which
/// falsifies the input's by the permutation lemma (contrapositive of the
/// sort's own transfer clause); an all-distinct scan plus sortedness gives
/// strict order, hence uniqueness, transferred back the same way. Discharged
/// from the trust ledger 2026-09 (formerly a trusted HashSet scan); the
/// `unique_idx_check` proptest stays as a belt. Costs a sort where the old
/// scan cost a hash pass; the sealing paths sort anyway on the unique branch.
pub fn is_unique_idx<T: Copy, I: IndexLike>(diffs: &Vec<(T, I)>) -> (b: bool)
    ensures b == unique_idx(diffs@),
{
    let sorted = sort_frame_by_index(diffs);
    let n = sorted.len();
    if n == 0 {
        proof {
            assert(unique_idx(diffs@)) by {
                assert(diffs@.len() == 0) by {
                    vstd::seq_lib::to_multiset_len(diffs@);
                    vstd::seq_lib::to_multiset_len(sorted@);
                }
            }
        }
        return true;
    }
    let mut k: usize = 1;
    while k < n
        invariant
            1 <= k <= n,
            n == sorted@.len(),
            sorted@.to_multiset() == diffs@.to_multiset(),
            unique_idx(diffs@) ==> unique_idx(sorted@),
            forall|a: int, b: int| 0 <= a < b < sorted@.len()
                ==> (#[trigger] sorted@[a]).1.as_nat() <= (#[trigger] sorted@[b]).1.as_nat(),
            forall|x: int| 0 <= x < k - 1
                ==> (#[trigger] sorted@[x]).1.as_nat() != sorted@[x + 1].1.as_nat(),
        decreases n - k,
    {
        if sorted[k - 1].1.as_usize() == sorted[k].1.as_usize() {
            proof {
                assert(!unique_idx(sorted@)) by {
                    assert(sorted@[k as int - 1].1.as_nat() == sorted@[k as int].1.as_nat());
                }
                if unique_idx(diffs@) {
                    assert(unique_idx(sorted@));
                }
            }
            return false;
        }
        k += 1;
    }
    proof {
        assert forall|a: int, b: int|
            0 <= a < sorted@.len() && 0 <= b < sorted@.len() && a != b
            implies (#[trigger] sorted@[a]).1.as_nat() != (#[trigger] sorted@[b]).1.as_nat() by {
            if a < b {
                lemma_sorted_distinct_strict::<T, I>(sorted@, a, b);
            } else {
                lemma_sorted_distinct_strict::<T, I>(sorted@, b, a);
            }
        }
        lemma_unique_idx_multiset(sorted@, diffs@);
    }
    true
}

/// Sort-first index-major encoding: sort the frame by index, then run-coalesce.
/// Because sorting captures ALL index contiguity (not just capture-order runs),
/// this is the strongest index-major compressor. It is a REORDERING codec, so it
/// does not reproduce the input sequence — but it preserves the multiset of
/// writes (`decode_i().to_multiset() == diffs@.to_multiset()`), which is the whole
/// codec contract: `vec::lemma_multiset_eq_overlay` then gives identical restore.
/// Requires the frame's indices be unique (first-write-wins), which is what makes
/// the sort strictly ascending (so `compress_runs` applies) and the reorder sound.
pub fn compress_runs_sorted<T: IndexLike, I: IndexFromNat>(diffs: &Vec<(T, I)>) -> (r: RunFrame<T>)
    requires unique_idx(diffs@),
    ensures
        r.wf(),
        r.fits::<I>(),
        r.decode_i::<I>().to_multiset() == diffs@.to_multiset(),
        unique_idx(r.decode_i::<I>()),
{
    let s = sort_frame_by_index(diffs);
    // s: same multiset as diffs, sorted (<=) by index, unique indices.
    assert(unique_idx(s@));
    // Project to usize and prove strictly ascending (sorted + unique => strict).
    let mut usized: Vec<(T, usize)> = Vec::new();
    let mut i: usize = 0;
    while i < s.len()
        invariant
            i <= s@.len(),
            usized@.len() == i,
            forall|t: int| #![trigger usized@[t]] 0 <= t < i ==>
                usized@[t].0 == s@[t].0
                && usized@[t].1 as nat == s@[t].1.as_nat(),
        decreases s@.len() - i,
    {
        let (v, idx) = s[i];
        usized.push((v, idx.as_usize()));
        i += 1;
    }
    proof {
        // Strictly ascending: sorted gives <=, uniqueness upgrades to <.
        assert forall|a: int, b: int| #![auto] 0 <= a < b < usized@.len() implies
            usized@[a].1 < usized@[b].1 by {
            assert(s@[a].1.as_nat() <= s@[b].1.as_nat());
            assert(s@[a].1.as_nat() != s@[b].1.as_nat());
            assert(usized@[a].1 as nat == s@[a].1.as_nat());
            assert(usized@[b].1 as nat == s@[b].1.as_nat());
        }
    }
    let rf = compress_runs(&usized);
    proof {
        // rf.decode() == mapped_diffs(usized@) == the (T, nat) projection of s;
        // decode_i maps each nat back via from_nat, recovering s exactly.
        assert(usized@.len() == s@.len());
        assert forall|t: int| #![auto] 0 <= t < s@.len() implies
            rf.decode()[t] == (s@[t].0, s@[t].1.as_nat()) by {
            assert(rf.decode()[t] == (usized@[t].0, usized@[t].1 as nat));
        }
        assert forall|t: int| 0 <= t < rf.decode().len() implies
            (#[trigger] rf.decode()[t].1) < I::max_nat() by {
            I::lemma_as_nat_bounded_val(s@[t].1);
        }
        assert forall|t: int| 0 <= t < s@.len() implies
            #[trigger] rf.decode_i::<I>()[t] == s@[t] by {
            I::lemma_from_as_nat(s@[t].1);
        }
        assert(rf.decode_i::<I>() =~= s@);
        // Same multiset as diffs, and uniqueness carries.
        assert(rf.decode_i::<I>().to_multiset() == s@.to_multiset());
        assert(s@.to_multiset() == diffs@.to_multiset());
    }
    rf
}

/// Per-instance compression mode, selected at `Vec` construction (not a const
/// generic): one binary runs SMT with `None` (speed) and equality saturation
/// with a per-column mode (memory). `ValueDict` is value-major (dictionary +
/// codes, for value-repetitive columns like union-find `parent`/`rank`);
/// `IndexRuns` is index-major (write-order run-coalescing, for columns with
/// contiguous batch updates — it drops the index column).
#[derive(Clone, Copy)]
pub enum CompressionMode {
    None,
    ValueDict,
    IndexRuns,
    /// Sort-first index-major: sort the frame by index, then run-coalesce
    /// (`compress_runs_sorted`). Captures ALL index contiguity, not just
    /// capture-order runs, so it is the strongest index-major compressor for
    /// scattered writes that land in a contiguous set. It REORDERS, so it
    /// preserves only the write multiset, not the sequence; `compress_frame`
    /// applies it only when the frame's indices are unique (checked at runtime)
    /// and falls back to `IndexRuns` (write-order, exact) otherwise. Selectable
    /// through the two-stack, whose contract is the per-frame write multiset.
    IndexRunsSorted,
    /// Choose per frame by exact-size costing (`choose_mode`): compute the plain,
    /// run, and dictionary sizes for this frame and pick the smallest. Lets one
    /// column carry a mix of schemes — value-major frames where a value repeats,
    /// index-major frames where indices cluster — decided from the frame's own
    /// content rather than a fixed guess.
    Auto,
}

/// Exact-size cost selector: pick the cheapest scheme for this specific frame.
/// `external_body` — a heuristic with no spec content: whichever mode it returns,
/// `compress_frame`'s bijection still holds, so correctness does not depend on the
/// choice, only the size does. `R` (run count) is the scatter signal; `D`
/// (distinct values) is the value-repetition signal.
#[verifier::external_body]
pub fn choose_mode<T: IndexLike, I: IndexLike>(diffs: &Vec<(T, I)>) -> CompressionMode {
    // One O(N) stats pass (R runs, D distinct; no sort), then the exact-size
    // decision. `external_body` only for the `size_of`/hashset it threads
    // through; the arithmetic lives in the verified `FrameStats::best_mode`.
    let stats = crate::compression_stats::frame_stats(diffs);
    // best_mode costs each scheme at the shipped encoders' achievable widths
    // (sorted run count, narrow code width computed from D internally).
    stats.best_mode(core::mem::size_of::<T>(), core::mem::size_of::<I>())
}

/// A finalized frame in whichever representation its column's mode selected. The
/// active frame is always uncompressed; this is what `mark` stores for a closed
/// frame, and what `restore` decodes. The `Runs` arm needs `I: IndexFromNat` to
/// reconstruct the dropped index column, so the whole enum carries that bound.
pub enum FrameEncoding<T, I> {
    Plain(Vec<(T, I)>),
    Dict(DictFrame<T, I>),
    Runs(RunFrame<T>),
}

impl<T: IndexLike, I: IndexFromNat> FrameEncoding<T, I> {
    pub open spec fn wf(&self) -> bool {
        match self {
            FrameEncoding::Plain(_) => true,
            FrameEncoding::Dict(d) => d.wf(),
            FrameEncoding::Runs(rf) => rf.wf() && rf.fits::<I>(),
        }
    }

    /// Decode back to the flat `(value, index)` diff sequence, mode-agnostically.
    pub open spec fn decode(&self) -> Seq<(T, I)> {
        match self {
            FrameEncoding::Plain(v) => v@,
            FrameEncoding::Dict(d) => d.decode(),
            FrameEncoding::Runs(rf) => rf.decode_i::<I>(),
        }
    }

    /// Executable decode: materialize the flat diff sequence for a finalized
    /// frame. This is what the two-stack restore calls to bring a compressed
    /// frame back to plain. `r@ == decode()`.
    pub fn decode_exec(&self) -> (r: Vec<(T, I)>)
        requires self.wf(),
        ensures r@ == self.decode(),
    {
        match self {
            FrameEncoding::Plain(v) => {
                let mut copy: Vec<(T, I)> = Vec::new();
                let mut i: usize = 0;
                while i < v.len()
                    invariant
                        i <= v@.len(),
                        copy@ == v@.subrange(0, i as int),
                    decreases v@.len() - i,
                {
                    copy.push(v[i]);
                    i += 1;
                }
                assert(copy@ =~= v@);
                copy
            }
            FrameEncoding::Dict(d) => d.decode_exec(),
            FrameEncoding::Runs(rf) => rf.decode_exec_i::<I>(),
        }
    }
}

/// Write-order index-major frame: project indices to `usize`, run-coalesce in
/// capture order (exact-view-preserving), and wrap. `decode_i` reconstructs each
/// `I` via `from_nat`, so the frame decodes back to `diffs@` exactly. Factored out
/// of `compress_frame` because it is both the `IndexRuns` encoding and the
/// fallback the `IndexRunsSorted` arm uses when a frame's indices are not unique.
pub fn runs_writeorder_frame<T: IndexLike, I: IndexFromNat>(diffs: &Vec<(T, I)>) -> (r: FrameEncoding<T, I>)
    ensures
        r.wf(),
        r.decode() == diffs@,
{
    let mut usized: Vec<(T, usize)> = Vec::new();
    let mut i: usize = 0;
    while i < diffs.len()
        invariant
            i <= diffs@.len(),
            usized@.len() == i,
            forall|t: int| 0 <= t < i ==>
                #[trigger] usized@[t].0 == diffs@[t].0
                && usized@[t].1 as nat == diffs@[t].1.as_nat(),
        decreases diffs@.len() - i,
    {
        let (v, idx) = diffs[i];
        usized.push((v, idx.as_usize()));
        i += 1;
    }
    let rf = compress_runs_writeorder(&usized);
    // rf.decode() == mapped_diffs(usized@) == the (T, nat) projection of
    // diffs; decode_i maps each nat back to I via from_nat, recovering diffs.
    proof {
        assert(usized@.len() == diffs@.len());
        assert forall|t: int| #![auto] 0 <= t < diffs@.len() implies
            rf.decode()[t] == (diffs@[t].0, diffs@[t].1.as_nat()) by {
            assert(rf.decode()[t] == (usized@[t].0, usized@[t].1 as nat));
        }
        // fits: every decoded index is some diffs[t].1.as_nat() < max_nat.
        assert forall|t: int| 0 <= t < rf.decode().len() implies
            (#[trigger] rf.decode()[t].1) < I::max_nat() by {
            I::lemma_as_nat_bounded_val(diffs@[t].1);
        }
        // decode_i recovers diffs: from_nat(diffs[t].1.as_nat()) == diffs[t].1.
        assert forall|t: int| 0 <= t < diffs@.len() implies
            #[trigger] rf.decode_i::<I>()[t] == diffs@[t] by {
            I::lemma_from_as_nat(diffs@[t].1);
        }
        assert(rf.decode_i::<I>() =~= diffs@);
    }
    FrameEncoding::Runs(rf)
}

/// Encode a finalized frame in the given mode. Every mode preserves the frame's
/// write MULTISET: `decode(compress_frame(d, mode)).to_multiset() == d.to_multiset()`.
/// The order-preserving modes (`None`/`ValueDict`/`IndexRuns`) decode back to `d`
/// exactly; `IndexRunsSorted` reorders (sorts by index) so it preserves only the
/// multiset, which is the whole contract: within a finalized frame each cell is
/// written at most once, so the restore overlay is determined by the write set,
/// not its order (`vec::lemma_multiset_eq_overlay`). `IndexRunsSorted` needs unique
/// indices for the sort to be sound; `compress_frame` checks that at runtime and
/// falls back to the write-order encoder otherwise, so it carries no uniqueness
/// precondition of its own.
pub fn compress_frame<T: IndexLike, I: IndexFromNat>(
    diffs: &Vec<(T, I)>,
    mode: CompressionMode,
) -> (r: FrameEncoding<T, I>)
    ensures
        r.wf(),
        r.decode().to_multiset() == diffs@.to_multiset(),
{
    // Resolve Auto to a concrete scheme per frame; the contract below holds for
    // whichever concrete mode is chosen, so the choice is size-only.
    let mode = match mode {
        CompressionMode::Auto => choose_mode(diffs),
        other => other,
    };
    match mode {
        // choose_mode never returns Auto; if it somehow did, plain is safe.
        CompressionMode::Auto | CompressionMode::None => {
            let mut copy: Vec<(T, I)> = Vec::new();
            let mut i: usize = 0;
            while i < diffs.len()
                invariant
                    i <= diffs@.len(),
                    copy@ == diffs@.subrange(0, i as int),
                decreases diffs@.len() - i,
            {
                copy.push(diffs[i]);
                i += 1;
            }
            assert(copy@ =~= diffs@);
            FrameEncoding::Plain(copy)
        }
        CompressionMode::ValueDict => FrameEncoding::Dict(compress(diffs)),
        CompressionMode::IndexRuns => runs_writeorder_frame(diffs),
        CompressionMode::IndexRunsSorted => {
            // Sort-first is sound only when indices are unique (a duplicate index
            // would let the permutation shadow a different write). Check at runtime;
            // fall back to the exact write-order encoder when it does not hold.
            if is_unique_idx(diffs) {
                let rf = compress_runs_sorted(diffs);
                // FrameEncoding::Runs(rf).decode() == rf.decode_i(), multiset == diffs.
                FrameEncoding::Runs(rf)
            } else {
                runs_writeorder_frame(diffs)
            }
        }
    }
}

// ===========================================================================
// RunCol: index-major run column that reconstructs indices via IndexLike
// arithmetic (checked_add), carrying a ghost of the write pairs. NO IndexFromNat,
// so it works for opaque id index types (the A2 sidestep). Write-order runs:
// exact. `run_seq` is nat-space (index-as-nat, value), so no `I` is constructed in
// spec; the actual `I` values live in the ghost `pairs`, tied to `run_seq` by
// `as_nat` in `wf`. This mirrors the verified `diff_log::cold_vals` structure.
// ===========================================================================

/// One run: values at consecutive indices `start, start+1, ...`.
pub struct RunEntry<T, I> {
    pub start: I,
    pub vals: Vec<T>,
}

/// The (index-as-nat, value) pairs of a run sequence, concatenated in order.
pub open spec fn run_seq<T: Copy, I: IndexLike>(runs: Seq<RunEntry<T, I>>) -> Seq<(nat, T)>
    decreases runs.len(),
{
    if runs.len() == 0 {
        Seq::empty()
    } else {
        Seq::new(runs[0].vals@.len(),
            |k: int| ((runs[0].start.as_nat() + k) as nat, runs[0].vals@[k]))
        + run_seq(runs.subrange(1, runs.len() as int))
    }
}

/// Appending a run extends `run_seq` by exactly that run's pairs.
pub proof fn lemma_run_seq_snoc<T: Copy, I: IndexLike>(runs: Seq<RunEntry<T, I>>, r: RunEntry<T, I>)
    ensures
        run_seq(runs.push(r)) == run_seq(runs)
            + Seq::new(r.vals@.len(), |k: int| ((r.start.as_nat() + k) as nat, r.vals@[k])),
    decreases runs.len(),
{
    reveal_with_fuel(run_seq, 2);
    if runs.len() == 0 {
        assert(runs.push(r) =~= seq![r]);
        assert(run_seq(runs) =~= Seq::<(nat, T)>::empty());
    } else {
        let tail = runs.subrange(1, runs.len() as int);
        lemma_run_seq_snoc(tail, r);
        assert(runs.push(r)[0] == runs[0]);
        assert(runs.push(r).subrange(1, runs.push(r).len() as int) =~= tail.push(r));
        let a = Seq::new(runs[0].vals@.len(),
            |k: int| ((runs[0].start.as_nat() + k) as nat, runs[0].vals@[k]));
        let b = run_seq(tail);
        let c = Seq::new(r.vals@.len(), |k: int| ((r.start.as_nat() + k) as nat, r.vals@[k]));
        assert(a + (b + c) =~= (a + b) + c);
    }
}

/// The pair-seq a single in-progress run contributes: values at `start, start+1, ...`
/// in `as_nat` space. `run_seq(runs) + cur_pairs(cur_start, cur_vals)` is the
/// coalescing loop invariant's left side.
pub open spec fn cur_pairs<T: Copy, I: IndexLike>(start: I, vals: Seq<T>) -> Seq<(nat, T)> {
    Seq::new(vals.len(), |k: int| ((start.as_nat() + k) as nat, vals[k]))
}

/// The first `n` write pairs projected to `(index-as-nat, value)`: the abstract
/// target the write-order run encoder reproduces. `run_seq(compress(d).runs)`
/// equals `nat_pairs(d, d.len())`.
pub open spec fn nat_pairs<T: Copy, I: IndexLike>(d: Seq<(T, I)>, n: nat) -> Seq<(nat, T)> {
    Seq::new(n, |t: int| (d[t].1.as_nat(), d[t].0))
}

/// `cur_pairs` extends by one at index `start + old_len` when a value is pushed.
pub proof fn lemma_cur_pairs_push<T: Copy, I: IndexLike>(start: I, vals: Seq<T>, v: T)
    ensures
        cur_pairs::<T, I>(start, vals.push(v))
            == cur_pairs::<T, I>(start, vals)
                + seq![((start.as_nat() + vals.len()) as nat, v)],
{
    assert(cur_pairs::<T, I>(start, vals.push(v))
        =~= cur_pairs::<T, I>(start, vals)
            + seq![((start.as_nat() + vals.len()) as nat, v)]);
}

/// `nat_pairs` extends by one as `n` grows.
pub proof fn lemma_nat_pairs_push<T: Copy, I: IndexLike>(d: Seq<(T, I)>, n: nat)
    requires n < d.len(),
    ensures
        nat_pairs(d, n + 1) == nat_pairs(d, n) + seq![(d[n as int].1.as_nat(), d[n as int].0)],
{
    assert(nat_pairs(d, n + 1)
        =~= nat_pairs(d, n) + seq![(d[n as int].1.as_nat(), d[n as int].0)]);
}

/// An index-major run column: the runs plus a ghost of the write pairs it encodes,
/// tied to the runs by `as_nat` (so no `from_nat`/`IndexFromNat` is needed).
pub struct RunCol<T, I> {
    pub runs: Vec<RunEntry<T, I>>,
    pub pairs: Ghost<Seq<(T, I)>>,
    /// Cached entry count (`== pairs.len()`). Stored so a cold tier can read a frame's
    /// length in O(1) without summing run lengths (which would risk `usize` overflow).
    pub len: usize,
}

impl<T: Copy, I: IndexLike> RunCol<T, I> {
    /// The ghost pairs are exactly the runs' reconstruction: same length, same
    /// value, and each index's `as_nat` is `start + offset` (and in range).
    pub open spec fn wf(&self) -> bool {
        let rs = run_seq(self.runs@);
        &&& self.pairs@.len() == rs.len()
        &&& self.len == self.pairs@.len()
        &&& forall|j: int| 0 <= j < rs.len() ==> {
            &&& (#[trigger] self.pairs@[j]).0 == rs[j].1
            &&& self.pairs@[j].1.as_nat() == rs[j].0
            &&& rs[j].0 < I::max_nat()
        }
    }

    /// Abstract value: the write pairs (carried as ghost).
    pub open spec fn decode(&self) -> Seq<(T, I)> {
        self.pairs@
    }

    /// Entry count, O(1) from the cached field.
    pub fn entry_len(&self) -> (n: usize)
        requires self.wf(),
        ensures n == self.decode().len(),
    {
        self.len
    }

    /// Encoded footprint (deterministic, length-based): one `start` index per run
    /// plus the value column. The index column is dropped, so this is below a plain
    /// `Vec<(T, I)>`'s `len * (size_of::<T>() + size_of::<I>())` whenever runs
    /// coalesce (fewer starts than entries). The measurement A2's heap check reads.
    pub fn byte_len(&self) -> usize {
        let mut total = crate::compression_stats::sat_mul(self.runs.len(), core::mem::size_of::<I>());
        let n = self.runs.len();
        let mut r: usize = 0;
        while r < n
            invariant 0 <= r <= n, n == self.runs@.len(),
            decreases n - r,
        {
            total = crate::compression_stats::sat_add(total, crate::compression_stats::sat_mul(self.runs[r].vals.len(), core::mem::size_of::<T>()));
            r += 1;
        }
        total
    }

    /// Write-order run-coalescing over generic `I` (no `IndexFromNat`): coalesces a
    /// value into the current run only when its index is `cur_start + cur_vals.len()`
    /// in `as_nat` space (tested via `as_usize`), so the encoding reproduces the input
    /// sequence exactly for ANY `diffs`; scattered or descending captures fall back to
    /// singleton runs. `decode() == diffs@` (via `run_seq == nat_pairs`). This is the
    /// general A2 encoder; `single_run` is its one-run special case.
    #[verifier::rlimit(800)]
    pub fn compress(diffs: &Vec<(T, I)>) -> (r: RunCol<T, I>)
        ensures
            r.wf(),
            r.decode() == diffs@,
    {
        proof { reveal(run_seq); }
        let mut runs: Vec<RunEntry<T, I>> = Vec::new();
        let mut cur_start: I = <I as IndexLike>::max();  // dummy; overwritten before use
        let mut cur_vals: Vec<T> = Vec::new();
        let mut i: usize = 0;
        while i < diffs.len()
            invariant
                i <= diffs@.len(),
                run_seq(runs@) + cur_pairs::<T, I>(cur_start, cur_vals@)
                    == nat_pairs(diffs@, i as nat),
                (cur_vals@.len() == 0) <==> (i == 0),
                cur_vals@.len() > 0
                    ==> cur_start.as_nat() == diffs@[i as int - cur_vals@.len()].1.as_nat(),
                cur_vals@.len() > 0
                    ==> cur_start.as_nat() + cur_vals@.len() - 1 == diffs@[i as int - 1].1.as_nat(),
                forall|t: int| 0 <= t < i ==> (#[trigger] diffs@[t].1).as_nat() < I::max_nat(),
            decreases diffs@.len() - i,
        {
            let v = diffs[i].0;
            let idx = diffs[i].1;
            proof { idx.lemma_as_nat_bounded(); }
            let ghost old_runs = runs@;
            let ghost old_cur_start = cur_start;
            let ghost old_cur_vals = cur_vals@;
            if cur_vals.len() == 0 {
                cur_start = idx;
                cur_vals.push(v);
                proof {
                    lemma_cur_pairs_push::<T, I>(idx, Seq::<T>::empty(), v);
                    assert(Seq::<T>::empty().push(v) =~= cur_vals@);
                    assert(cur_pairs::<T, I>(idx, cur_vals@) =~= seq![(idx.as_nat(), v)]);
                    lemma_nat_pairs_push::<T, I>(diffs@, i as nat);
                }
            } else if idx.as_usize() >= cur_start.as_usize()
                && idx.as_usize() - cur_start.as_usize() == cur_vals.len() {
                proof { lemma_cur_pairs_push::<T, I>(cur_start, cur_vals@, v); }
                cur_vals.push(v);
                proof {
                    assert(old_cur_vals.push(v) =~= cur_vals@);
                    assert(cur_start.as_nat() + old_cur_vals.len() == idx.as_nat());
                    let a = run_seq(runs@);
                    let b = cur_pairs::<T, I>(cur_start, old_cur_vals);
                    let c = seq![(idx.as_nat(), v)];
                    assert(cur_pairs::<T, I>(cur_start, cur_vals@) == b + c);
                    assert(a + (b + c) =~= (a + b) + c);
                    lemma_nat_pairs_push::<T, I>(diffs@, i as nat);
                }
            } else {
                let entry = RunEntry { start: cur_start, vals: cur_vals };
                let ghost gentry = entry;
                runs.push(entry);
                cur_start = idx;
                cur_vals = Vec::new();
                cur_vals.push(v);
                proof {
                    lemma_run_seq_snoc(old_runs, gentry);
                    lemma_cur_pairs_push::<T, I>(idx, Seq::<T>::empty(), v);
                    assert(Seq::<T>::empty().push(v) =~= cur_vals@);
                    assert(cur_pairs::<T, I>(idx, cur_vals@) =~= seq![(idx.as_nat(), v)]);
                    let a = run_seq(old_runs);
                    let b = cur_pairs::<T, I>(old_cur_start, old_cur_vals);
                    let c = seq![(idx.as_nat(), v)];
                    assert(run_seq(runs@) == a + b);
                    assert(a + b + c =~= (a + b) + c);
                    lemma_nat_pairs_push::<T, I>(diffs@, i as nat);
                }
            }
            i += 1;
        }
        let ghost pre_runs = runs@;
        let ghost pre_cur_start = cur_start;
        let ghost pre_cur_vals = cur_vals@;
        if cur_vals.len() > 0 {
            let entry = RunEntry { start: cur_start, vals: cur_vals };
            let ghost gentry = entry;
            runs.push(entry);
            proof {
                lemma_run_seq_snoc(pre_runs, gentry);
            }
        } else {
            proof {
                // cur empty ⇒ i == 0 ⇒ diffs empty; current-run term is empty.
                assert(cur_pairs::<T, I>(cur_start, cur_vals@) =~= Seq::<(nat, T)>::empty());
            }
        }
        let r = RunCol { runs, pairs: Ghost(diffs@), len: diffs.len() };
        proof {
            // run_seq(runs) == nat_pairs(diffs, len); wf follows by the as_nat relation.
            assert(run_seq(r.runs@) == nat_pairs(diffs@, diffs@.len() as nat));
            let rs = run_seq(r.runs@);
            assert(rs.len() == diffs@.len());
            assert forall|j: int| 0 <= j < rs.len() implies {
                &&& (#[trigger] r.pairs@[j]).0 == rs[j].1
                &&& r.pairs@[j].1.as_nat() == rs[j].0
                &&& rs[j].0 < I::max_nat()
            } by {
                assert(rs[j] == (diffs@[j].1.as_nat(), diffs@[j].0));
            }
        }
        r
    }

    /// Sort-first index-major encoding (A3): sort the frame by index, then
    /// write-order coalesce the sorted stream. Because sorting captures ALL index
    /// contiguity (not just capture-order runs), this is the strongest index-major
    /// compressor; it is a REORDERING codec, so it does not reproduce the capture
    /// sequence, but it preserves the write multiset
    /// (`decode().to_multiset() == diffs@.to_multiset()`), which is the whole codec
    /// contract: with unique per-frame indices, `vec::lemma_multiset_eq_overlay`
    /// gives identical restore. Opaque-id safe (no `IndexFromNat`), unlike
    /// `compress_runs_sorted`.
    pub fn compress_sorted(diffs: &Vec<(T, I)>) -> (r: RunCol<T, I>)
        ensures
            r.wf(),
            r.decode().to_multiset() == diffs@.to_multiset(),
            unique_idx(diffs@) ==> unique_idx(r.decode()),
    {
        let s = sort_frame_by_index(diffs);
        let r = RunCol::compress(&s);
        // r.decode() == s@ (compress), s@.to_multiset() == diffs@.to_multiset() (sort is
        // a permutation), and sort preserves unique_idx.
        assert(r.decode().to_multiset() == diffs@.to_multiset());
        r
    }

    /// Reconstruct the write pairs. The index-major payoff: indices are rebuilt from
    /// each run's `start` via `IndexLike::checked_add` (opaque-id safe, NO IndexFromNat),
    /// and `decode_exec@ == decode()` is proved from `wf`'s `as_nat` relation plus
    /// `lemma_as_nat_injective`.
    pub fn decode_exec(&self) -> (out: Vec<(T, I)>)
        requires self.wf(),
        ensures out@ == self.decode(),
    {
        proof { reveal(run_seq); }
        let mut out: Vec<(T, I)> = Vec::new();
        let mut r: usize = 0;
        while r < self.runs.len()
            invariant
                0 <= r <= self.runs@.len(),
                self.wf(),
                out@.len() == run_seq(self.runs@.subrange(0, r as int)).len(),
                out@ == self.pairs@.subrange(0, out@.len() as int),
            decreases self.runs@.len() - r,
        {
            let ghost base = out@.len();
            let start = self.runs[r].start;
            let m = self.runs[r].vals.len();
            let mut k: usize = 0;
            while k < m
                invariant
                    0 <= r < self.runs@.len(),
                    self.wf(),
                    m == self.runs@[r as int].vals@.len(),
                    start == self.runs@[r as int].start,
                    base == run_seq(self.runs@.subrange(0, r as int)).len(),
                    0 <= k <= m,
                    out@.len() == base + k,
                    out@ == self.pairs@.subrange(0, out@.len() as int),
                decreases m - k,
            {
                let ghost g = base + k;
                proof {
                    // global position g == base + k lands in run r at offset k.
                    lemma_run_seq_at(self.runs@, r as int, k as int);
                    start.lemma_as_nat_bounded();
                    // g is in range: run_seq(runs[0..r+1]).len() == base + m > g.
                    lemma_run_seq_split(self.runs@, (r + 1) as int);
                    assert(self.runs@.subrange(0, r + 1)
                        =~= self.runs@.subrange(0, r as int).push(self.runs@[r as int]));
                    lemma_run_seq_snoc(self.runs@.subrange(0, r as int), self.runs@[r as int]);
                    let rs = run_seq(self.runs@);
                    // run_seq(runs[0..r+1]).len() == base + m, and rs is that prefix plus a
                    // tail, so g == base + k < base + m <= rs.len().
                    assert(run_seq(self.runs@.subrange(0, r + 1)).len() == base + m);
                    assert(g < rs.len());
                    // rs[g] == (start.as_nat()+k, vals[k]); wf ⇒ rs[g].0 < max_nat (via pairs[g]).
                    assert(rs[g as int].0 == (start.as_nat() + k) as nat);
                    assert(self.pairs@[g as int].1.as_nat() == rs[g as int].0);
                    assert(rs[g as int].0 < I::max_nat());
                    assert((k as nat) < I::max_nat());
                }
                let off = I::try_from_usize(k).unwrap();
                let idx = crate::index_like::checked_add(start, off).unwrap();
                proof {
                    // idx.as_nat() == start.as_nat() + k == run_seq[g].0 == pairs[g].1.as_nat()
                    // ⇒ idx == pairs[g].1 by injectivity; value matches directly.
                    let rs = run_seq(self.runs@);
                    assert(idx.as_nat() == self.pairs@[g as int].1.as_nat());
                    I::lemma_as_nat_injective(idx, self.pairs@[g as int].1);
                    assert(self.runs@[r as int].vals@[k as int] == self.pairs@[g as int].0);
                }
                out.push((self.runs[r].vals[k], idx));
                proof {
                    assert(out@ =~= self.pairs@.subrange(0, out@.len() as int));
                }
                k = k + 1;
            }
            proof {
                assert(self.runs@.subrange(0, r + 1)
                    =~= self.runs@.subrange(0, r as int).push(self.runs@[r as int]));
                lemma_run_seq_snoc(self.runs@.subrange(0, r as int), self.runs@[r as int]);
            }
            r = r + 1;
        }
        proof {
            assert(self.runs@.subrange(0, self.runs@.len() as int) =~= self.runs@);
            assert(out@ =~= self.pairs@);
        }
        out
    }


    /// The index column this frame decodes to (the `.1` projection of `decode()`).
    /// When `RunCol` is used as an index-only cold frame (`T` a zero-size type), this
    /// is the whole payload: `DiffIdxs`'s cold tier concatenates `idx_seq` across
    /// frames, mirroring how `DiffVals` concatenates `ValFrame::decode`.
    pub open spec fn idx_seq(&self) -> Seq<I> {
        Seq::new(self.decode().len(), |j: int| self.decode()[j].1)
    }

    /// Random access to just the index at position `i` (`decode_at(i).1`). The read
    /// accessor an index-only cold frame needs.
    pub fn idx_at(&self, i: usize) -> (r: I)
        requires self.wf(), i < self.decode().len(),
        ensures r == self.idx_seq()[i as int],
    {
        self.decode_at(i).1
    }

    /// Random access to entry `i`, reconstructing its index from the run it lands in
    /// (`checked_add(run_start, offset)`). O(runs) walk to locate the run; the read
    /// accessor a cold `RunCol` frame needs so `DiffLog::index` can read a single
    /// entry without decoding the whole frame. `decode_at(i) == decode()[i]`.
    pub fn decode_at(&self, i: usize) -> (e: (T, I))
        requires self.wf(), i < self.decode().len(),
        ensures e == self.decode()[i as int],
    {
        proof { reveal(run_seq); }
        // Walk runs, carrying the remaining within-frame offset `d == i - prefix_r`.
        let mut d: usize = i;
        let mut r: usize = 0;
        while r < self.runs.len() && self.runs[r].vals.len() <= d
            invariant
                0 <= r <= self.runs@.len(),
                self.wf(),
                i < run_seq(self.runs@).len(),
                d + run_seq(self.runs@.subrange(0, r as int)).len() == i,
            decreases self.runs@.len() - r,
        {
            let flen = self.runs[r].vals.len();
            proof {
                assert(self.runs@.subrange(0, r + 1)
                    =~= self.runs@.subrange(0, r as int).push(self.runs@[r as int]));
                lemma_run_seq_snoc(self.runs@.subrange(0, r as int), self.runs@[r as int]);
                // prefix_{r+1} == prefix_r + flen; still <= i, so r+1 is a valid run.
                lemma_run_seq_split(self.runs@, (r + 1) as int);
            }
            d = d - flen;
            r = r + 1;
        }
        // Loop exit: r < runs.len() (else i >= total, contradiction) and d < len_r.
        proof {
            lemma_run_seq_split(self.runs@, r as int);
            assert(r < self.runs@.len());
        }
        let start = self.runs[r].start;
        let ghost base = run_seq(self.runs@.subrange(0, r as int)).len();
        proof {
            lemma_run_seq_at(self.runs@, r as int, d as int);
            start.lemma_as_nat_bounded();
            let rs = run_seq(self.runs@);
            assert(base + d == i);
            assert(rs[i as int].0 == (start.as_nat() + d) as nat);
            assert(self.pairs@[i as int].1.as_nat() == rs[i as int].0);
            assert(rs[i as int].0 < I::max_nat());
            assert((d as nat) < I::max_nat());
        }
        let off = I::try_from_usize(d).unwrap();
        let idx = crate::index_like::checked_add(start, off).unwrap();
        proof {
            let rs = run_seq(self.runs@);
            assert(idx.as_nat() == self.pairs@[i as int].1.as_nat());
            I::lemma_as_nat_injective(idx, self.pairs@[i as int].1);
            assert(self.runs@[r as int].vals@[d as int] == self.pairs@[i as int].0);
        }
        (self.runs[r].vals[d], idx)
    }

    /// Encode a single contiguous frame (all indices `start, start+1, ...`) as one
    /// run, dropping the index column. The minimal index-major encoder; multi-run
    /// coalescing generalizes it. `decode() == diffs@`.
    pub fn single_run(diffs: &Vec<(T, I)>) -> (r: RunCol<T, I>)
        requires
            diffs@.len() > 0,
            forall|k: int| 0 <= k < diffs@.len()
                ==> (#[trigger] diffs@[k]).1.as_nat() == diffs@[0].1.as_nat() + k,
        ensures
            r.wf(),
            r.decode() == diffs@,
    {
        proof { reveal(run_seq); }
        let start = diffs[0].1;
        let mut vals: Vec<T> = Vec::new();
        let mut i: usize = 0;
        while i < diffs.len()
            invariant
                0 <= i <= diffs@.len(),
                vals@.len() == i,
                forall|k: int| 0 <= k < i ==> #[trigger] vals@[k] == diffs@[k].0,
                forall|k: int| 0 <= k < i
                    ==> (#[trigger] diffs@[k].1).as_nat() < I::max_nat(),
            decreases diffs@.len() - i,
        {
            let cur = diffs[i].1;
            proof { cur.lemma_as_nat_bounded(); }
            vals.push(diffs[i].0);
            i += 1;
        }
        let ghost gvals = vals@;
        let entry = RunEntry { start, vals };
        // Not `vec![entry]`: that macro expands to a let expression, which Verus
        // does not support.
        #[allow(clippy::vec_init_then_push)]
        let mut runs: Vec<RunEntry<T, I>> = Vec::new();
        runs.push(entry);
        let r = RunCol { runs, pairs: Ghost(diffs@), len: diffs.len() };
        proof {
            reveal_with_fuel(run_seq, 2);
            assert(r.runs@.len() == 1);
            assert(r.runs@.subrange(1, 1) =~= Seq::<RunEntry<T, I>>::empty());
            assert(r.runs@[0].start == start);
            assert(r.runs@[0].vals@ == gvals);
            let rs = run_seq(r.runs@);
            // Singleton run: rs[j] == (start.as_nat()+j, gvals[j]).
            assert(rs =~= Seq::new(gvals.len(),
                |k: int| ((start.as_nat() + k) as nat, gvals[k])));
            assert(rs.len() == diffs@.len());
            assert forall|j: int| 0 <= j < rs.len() implies {
                &&& (#[trigger] r.pairs@[j]).0 == rs[j].1
                &&& r.pairs@[j].1.as_nat() == rs[j].0
                &&& rs[j].0 < I::max_nat()
            } by {
                // value: gvals[j] == diffs[j].0; index: diffs[j].1.as_nat() == start+j.
                assert(rs[j] == ((start.as_nat() + j) as nat, gvals[j]));
            }
        }
        r
    }
}

/// `run_seq(runs)[g]` for a global position `g` in run `r` at offset `k`:
/// `(start_r + k, vals_r[k])`. The random-access bridge `decode_exec` needs.
pub proof fn lemma_run_seq_at<T: Copy, I: IndexLike>(runs: Seq<RunEntry<T, I>>, r: int, k: int)
    requires
        0 <= r < runs.len(),
        0 <= k < runs[r].vals@.len(),
    ensures
        run_seq(runs)[run_seq(runs.subrange(0, r)).len() + k]
            == ((runs[r].start.as_nat() + k) as nat, runs[r].vals@[k]),
    decreases runs.len(),
{
    reveal_with_fuel(run_seq, 2);
    let head = runs[0];
    let rest = runs.subrange(1, runs.len() as int);
    let hpairs = Seq::new(head.vals@.len(),
        |j: int| ((head.start.as_nat() + j) as nat, head.vals@[j]));
    if r == 0 {
        assert(runs.subrange(0, 0) =~= Seq::<RunEntry<T, I>>::empty());
        assert(run_seq(runs) == hpairs + run_seq(rest));
    } else {
        assert(runs.subrange(0, r).subrange(1, r) =~= rest.subrange(0, r - 1));
        assert(run_seq(runs.subrange(0, r)) =~= hpairs + run_seq(rest.subrange(0, r - 1)));
        let base = run_seq(runs.subrange(0, r)).len();
        let hl = hpairs.len();
        assert(base == hl + run_seq(rest.subrange(0, r - 1)).len());
        lemma_run_seq_at(rest, r - 1, k);
        assert(rest[r - 1] == runs[r]);
        lemma_run_seq_split(runs, r);
        assert(run_seq(runs) == hpairs + run_seq(rest));
    }
}

/// `run_seq` splits at any run boundary.
pub proof fn lemma_run_seq_split<T: Copy, I: IndexLike>(runs: Seq<RunEntry<T, I>>, r: int)
    requires 0 <= r <= runs.len(),
    ensures
        run_seq(runs) == run_seq(runs.subrange(0, r))
            + run_seq(runs.subrange(r, runs.len() as int)),
    decreases runs.len(),
{
    reveal_with_fuel(run_seq, 2);
    if runs.len() == 0 {
        assert(runs.subrange(0, r) =~= Seq::<RunEntry<T, I>>::empty());
        assert(runs.subrange(r, runs.len() as int) =~= Seq::<RunEntry<T, I>>::empty());
    } else if r == 0 {
        assert(runs.subrange(0, 0) =~= Seq::<RunEntry<T, I>>::empty());
        assert(runs.subrange(0, runs.len() as int) =~= runs);
    } else {
        let head = runs[0];
        let rest = runs.subrange(1, runs.len() as int);
        lemma_run_seq_split(rest, r - 1);
        let hpairs = Seq::new(head.vals@.len(),
            |j: int| ((head.start.as_nat() + j) as nat, head.vals@[j]));
        assert(runs.subrange(0, r).subrange(1, r) =~= rest.subrange(0, r - 1));
        assert(run_seq(runs.subrange(0, r)) =~= hpairs + run_seq(rest.subrange(0, r - 1)));
        assert(runs.subrange(r, runs.len() as int) =~= rest.subrange(r - 1, rest.len() as int));
        let a = hpairs;
        let b = run_seq(rest.subrange(0, r - 1));
        let c = run_seq(rest.subrange(r - 1, rest.len() as int));
        assert(a + (b + c) =~= (a + b) + c);
    }
}

// ===========================================================================
// ColdFrame: a per-frame-adaptive cold frame. Each finalized frame independently
// picks the encoding that fits it: plain, value-major (dictionary + codes, keeps a
// plain index column) for the union-find shape, or index-major runs (opaque-id safe
// via RunCol, write-order or sorted) for contiguous captures. This is the A4
// substrate: unlike the column-level `DiffVals`/`DiffIdxs` split, a `Vec<ColdFrame>`
// cold tier can hold different modes in different frames. `decode()` is mode-agnostic
// `Seq<(T, I)>`, so the restore reconstruction is uniform across the mix.
// ===========================================================================

/// One finalized frame in whichever mode fit it. `Runs` uses the verified `RunCol`
/// (no `IndexFromNat`), so the whole enum stays opaque-id safe.
/// Bytes of a plain frame of `n` entries (the demotion comparison's baseline).
/// `external_body`: saturating size arithmetic with no spec content; the demotion
/// it feeds is correctness-invisible (both branches carry the same contract).
pub fn plain_frame_bytes<T, I>(n: usize) -> usize {
    crate::compression_stats::sat_mul(
        n,
        crate::compression_stats::sat_add(
            core::mem::size_of::<T>(), core::mem::size_of::<I>()))
}

/// Writing a frame's `(value, index)` set back onto a live column, in order
/// (last write wins; out-of-range indices are skipped). A frame's `restore_to`
/// reproduces this, whether it does it with a sliced memcpy or scattered writes.
pub open spec fn apply_all<T, I: IndexLike>(base: Seq<T>, d: Seq<(T, I)>) -> Seq<T>
    decreases d.len(),
{
    if d.len() == 0 {
        base
    } else {
        let prev = apply_all(base, d.subrange(0, d.len() - 1));
        let e = d[d.len() - 1];
        if e.1.as_nat() < prev.len() {
            prev.update(e.1.as_nat() as int, e.0)
        } else {
            prev
        }
    }
}

/// `apply_all` never changes the column's length (it only overwrites).
pub proof fn lemma_apply_all_len<T, I: IndexLike>(base: Seq<T>, d: Seq<(T, I)>)
    ensures apply_all::<T, I>(base, d).len() == base.len(),
    decreases d.len(),
{
    if d.len() == 0 {
    } else {
        lemma_apply_all_len::<T, I>(base, d.subrange(0, d.len() - 1));
    }
}

/// One more write extends `apply_all` by exactly that write. The step rule a
/// scattered `restore_to` loop needs.
pub proof fn lemma_apply_all_snoc<T, I: IndexLike>(base: Seq<T>, d: Seq<(T, I)>, k: int)
    requires 0 <= k < d.len(),
    ensures
        apply_all::<T, I>(base, d.subrange(0, k + 1))
            == (if d[k].1.as_nat() < apply_all::<T, I>(base, d.subrange(0, k)).len() {
                    apply_all::<T, I>(base, d.subrange(0, k)).update(d[k].1.as_nat() as int, d[k].0)
                } else {
                    apply_all::<T, I>(base, d.subrange(0, k))
                }),
{
    let s = d.subrange(0, k + 1);
    assert(s.len() == k + 1);
    assert(s[s.len() - 1] == d[k]);
    assert(s.subrange(0, s.len() - 1) =~= d.subrange(0, k));
}

/// A finalized frame in some compressed representation. Abstractly it IS the set of
/// `(value, index)` writes it holds (`decode()`), so every impl is interchangeable to
/// a caller: read one entry, or write the whole frame straight back onto a live
/// column. `restore_to` is the cold-to-live path: an impl whose indices are
/// contiguous does it with a sliced memcpy, one with scattered indices writes
/// element by element, and the caller does not care which.
pub trait CompressedFrame<T: Copy, I: IndexLike>: Sized {
    spec fn wf(&self) -> bool;

    /// The write set this frame holds.
    spec fn decode(&self) -> Seq<(T, I)>;

    fn entry_len(&self) -> (n: usize)
        requires self.wf(),
        ensures n == self.decode().len();

    fn decode_at(&self, i: usize) -> (e: (T, I))
        requires self.wf(), i < self.decode().len(),
        ensures e == self.decode()[i as int];

    /// Write this frame's set back onto a live column (cold to live, no decode
    /// detour). Sliced or scattered is the impl's choice.
    fn restore_to(&self, target: &mut Vec<T>)
        requires self.wf(),
        ensures final(target)@ == apply_all::<T, I>(old(target)@, self.decode());
}

/// Value-major frames restore by SCATTERED writes: the index column is stored
/// verbatim and is generally not contiguous, so each write goes to its own slot.
impl<T: Copy, I: IndexLike> CompressedFrame<T, I> for DictFrame<T, I> {
    open spec fn wf(&self) -> bool { DictFrame::wf(self) }

    open spec fn decode(&self) -> Seq<(T, I)> { DictFrame::decode(self) }

    fn entry_len(&self) -> (n: usize) { DictFrame::entry_len(self) }

    fn decode_at(&self, i: usize) -> (e: (T, I)) { DictFrame::decode_at(self, i) }

    // `g` is incremented past its last exec read: the trailing value is used
    // only by the proof (`pairs.subrange(0, g as int)`), which rustc cannot see.
    fn restore_to(&self, target: &mut Vec<T>) {
        let ghost base = target@;
        let n = DictFrame::entry_len(self);
        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i <= n,
                n == DictFrame::decode(self).len(),
                DictFrame::wf(self),
                target@ == apply_all::<T, I>(base, DictFrame::decode(self).subrange(0, i as int)),
            decreases n - i,
        {
            let (v, idx) = DictFrame::decode_at(self, i);
            proof { lemma_apply_all_snoc::<T, I>(base, DictFrame::decode(self), i as int); }
            let u = idx.as_usize();
            if u < target.len() {
                target.set(u, v);
            }
            i = i + 1;
        }
        proof {
            assert(DictFrame::decode(self).subrange(0, n as int) =~= DictFrame::decode(self));
        }
    }
}

/// Index-major run frames restore by SLICED writes: each run's values are contiguous
/// in the frame AND land at consecutive indices, so a run is one `copy_from_slice`
/// (a memcpy) instead of `len` scattered stores. `external_body`: the slice copy is a
/// raw-memory primitive (trust ledger group B); its `apply_all` contract is
/// conformance-checked against the scattered reference.
impl<T: Copy, I: IndexLike> CompressedFrame<T, I> for RunCol<T, I> {
    open spec fn wf(&self) -> bool { RunCol::wf(self) }

    open spec fn decode(&self) -> Seq<(T, I)> { RunCol::decode(self) }

    fn entry_len(&self) -> (n: usize) { RunCol::entry_len(self) }

    fn decode_at(&self, i: usize) -> (e: (T, I)) { RunCol::decode_at(self, i) }

    /// VERIFIED per-element run replay: walks runs mirroring `run_seq`,
    /// writing each in-range entry and skipping out-of-range ones — exactly
    /// `apply_all`'s per-entry step, carried by `lemma_apply_all_snoc` with
    /// the position algebra from `lemma_run_seq_at`. Discharged from the
    /// trust ledger 2026-09: formerly a per-run `copy_from_slice` memcpy
    /// behind a trusted contract. If the restore benchmarks measure the
    /// memcpy delta, the recorded upgrade is a trusted memcpy fast path
    /// behind this same contract with this loop as the verified reference.
    // `g` is incremented past its last executable read: the trailing value is
    // used only by the proof (`pairs.subrange(0, g as int)`), which rustc
    // cannot see.
    #[allow(unused_assignments)]
    fn restore_to(&self, target: &mut Vec<T>) {
        let ghost base = target@;
        let ghost pairs = self.pairs@;
        let nruns = self.runs.len();
        let mut r: usize = 0;
        let mut g: usize = 0;
        while r < nruns
            invariant
                self.wf(),
                pairs == self.pairs@,
                nruns == self.runs@.len(),
                0 <= r <= nruns,
                g == run_seq(self.runs@.subrange(0, r as int)).len(),
                g <= pairs.len(),
                target@ == apply_all::<T, I>(base, pairs.subrange(0, g as int)),
                target@.len() == base.len(),
            decreases nruns - r,
        {
            let run_len = self.runs[r].vals.len();
            let start = self.runs[r].start;
            let mut k: usize = 0;
            while k < run_len
                invariant
                    self.wf(),
                    pairs == self.pairs@,
                    nruns == self.runs@.len(),
                    0 <= r < nruns,
                    run_len == self.runs@[r as int].vals@.len(),
                    start == self.runs@[r as int].start,
                    0 <= k <= run_len,
                    g == run_seq(self.runs@.subrange(0, r as int)).len() + k,
                    g <= pairs.len(),
                    target@ == apply_all::<T, I>(base, pairs.subrange(0, g as int)),
                    target@.len() == base.len(),
                decreases run_len - k,
            {
                proof {
                    // pairs[g] is this run's entry k: value verbatim, index
                    // as_nat == start + k, in range of I.
                    lemma_run_seq_at(self.runs@, r as int, k as int);
                    assert(g < pairs.len()) by {
                        // pairs.len == run_seq(all).len == prefix + rest, and
                        // this run's entry k sits inside rest's head.
                        lemma_run_seq_split(self.runs@, r as int);
                        reveal_with_fuel(run_seq, 2);
                        assert(self.runs@.subrange(r as int, self.runs@.len() as int)[0]
                            == self.runs@[r as int]);
                        assert(run_seq(self.runs@.subrange(r as int, self.runs@.len() as int)).len()
                            >= self.runs@[r as int].vals@.len());
                    }
                    assert(pairs[g as int].0 == self.runs@[r as int].vals@[k as int]);
                    assert(pairs[g as int].1.as_nat() == start.as_nat() + k);
                    assert(start.as_nat() + k < I::max_nat());
                    I::lemma_max_nat_fits_usize();
                    lemma_apply_all_snoc::<T, I>(base, pairs, g as int);
                }
                let idx = start.as_usize() + k;
                if idx < target.len() {
                    target.set(idx, self.runs[r].vals[k]);
                }
                g += 1;
                k += 1;
            }
            proof {
                assert(self.runs@.subrange(0, r as int + 1)
                    =~= self.runs@.subrange(0, r as int).push(self.runs@[r as int]));
                lemma_run_seq_snoc(self.runs@.subrange(0, r as int), self.runs@[r as int]);
            }
            r += 1;
        }
        proof {
            assert(self.runs@.subrange(0, nruns as int) =~= self.runs@);
            assert(pairs.subrange(0, g as int) =~= pairs);
        }
    }
}

// ===========================================================================
// DeltaFrame: value-equals-index with exceptions (F3). The proof-forest shape:
// a self-parented union-find root's captured old value IS its own cell index, so
// the value column collapses to the (rare) exceptions. The design carries NO
// arithmetic at all: encoding tests `value.as_usize() == index.as_usize()`, and
// decoding reconstructs the value from the index via `try_from_usize`, whose
// success is proved from the wf bound. Overflow and underflow are impossible by
// construction, discharging F3's proved-in-range requirement without a single
// add or subtract.
// ===========================================================================

pub struct DeltaFrame<T, I> {
    /// The index column, verbatim.
    pub idxs: Vec<I>,
    /// Positions whose value is NOT the index, with the verbatim value.
    pub exceptions: Vec<(usize, T)>,
    /// The write pairs this frame holds (carried as ghost, tied to the columns).
    pub pairs: Ghost<Seq<(T, I)>>,
}

impl<T: IndexLike, I: IndexLike> DeltaFrame<T, I> {
    pub open spec fn wf(&self) -> bool {
        &&& self.pairs@.len() == self.idxs@.len()
        &&& forall|k: int| 0 <= k < self.pairs@.len()
                ==> (#[trigger] self.pairs@[k]).1 == self.idxs@[k]
        // Exception positions are in range and carry the pair's exact value.
        &&& forall|e: int| 0 <= e < self.exceptions@.len() ==> {
                &&& (#[trigger] self.exceptions@[e]).0 < self.pairs@.len()
                &&& self.exceptions@[e].1 == self.pairs@[self.exceptions@[e].0 as int].0
            }
        // Every non-exception position's value IS its index (as a nat), and that
        // nat fits T, so `try_from_usize` reconstructs it.
        &&& forall|k: int| 0 <= k < self.pairs@.len()
                && !exception_at(self.exceptions@, k)
                ==> {
                    &&& (#[trigger] self.pairs@[k]).0.as_nat() == self.idxs@[k].as_nat()
                    &&& self.idxs@[k].as_nat() < T::max_nat()
                }
    }

    pub open spec fn decode(&self) -> Seq<(T, I)> {
        self.pairs@
    }

    pub fn entry_len(&self) -> (n: usize)
        requires self.wf(),
        ensures n == self.decode().len(),
    {
        self.idxs.len()
    }

    /// Random access. Non-exception positions reconstruct the value from the
    /// index (`try_from_usize`, success proved from wf); exceptions read verbatim.
    /// O(exceptions) scan; acceptable because the shape this frame targets has
    /// almost none.
    pub fn decode_at(&self, i: usize) -> (e: (T, I))
        requires self.wf(), i < self.decode().len(),
        ensures e == self.decode()[i as int],
    {
        let idx = self.idxs[i];
        let m = self.exceptions.len();
        let mut k: usize = 0;
        while k < m
            invariant
                0 <= k <= m,
                m == self.exceptions@.len(),
                self.wf(),
                i < self.decode().len(),
                idx == self.idxs@[i as int],
                forall|e: int| 0 <= e < k ==> (#[trigger] self.exceptions@[e]).0 != i,
            decreases m - k,
        {
            let (pos, v) = self.exceptions[k];
            if pos == i {
                return (v, idx);
            }
            k = k + 1;
        }
        proof {
            assert(!exception_at(self.exceptions@, i as int));
            // Instantiate wf's non-exception clause at i: value == index as nat, in T range.
            assert(self.pairs@[i as int].0.as_nat() == self.idxs@[i as int].as_nat());
            assert(self.idxs@[i as int].as_nat() < T::max_nat());
        }
        let v = T::try_from_usize(idx.as_usize()).unwrap();
        proof {
            T::lemma_as_nat_injective(v, self.pairs@[i as int].0);
        }
        (v, idx)
    }

    /// Encode a frame. Always succeeds and is always exact (`decode() == diffs@`);
    /// whether it PAYS is the caller's size comparison (the same demotion protocol
    /// as the run encoders).
    pub fn compress(diffs: &Vec<(T, I)>) -> (r: DeltaFrame<T, I>)
        ensures
            r.wf(),
            r.decode() == diffs@,
    {
        let mut idxs: Vec<I> = Vec::new();
        let mut exceptions: Vec<(usize, T)> = Vec::new();
        let mut i: usize = 0;
        while i < diffs.len()
            invariant
                0 <= i <= diffs@.len(),
                idxs@.len() == i,
                forall|k: int| 0 <= k < i ==> #[trigger] idxs@[k] == diffs@[k].1,
                forall|e: int| 0 <= e < exceptions@.len() ==> {
                    &&& (#[trigger] exceptions@[e]).0 < i
                    &&& exceptions@[e].1 == diffs@[exceptions@[e].0 as int].0
                },
                forall|k: int| 0 <= k < i && !exception_at(exceptions@, k)
                    ==> {
                        &&& (#[trigger] diffs@[k]).0.as_nat() == diffs@[k].1.as_nat()
                        &&& diffs@[k].1.as_nat() < T::max_nat()
                    },
            decreases diffs@.len() - i,
        {
            let (v, idx) = diffs[i];
            let ghost pre_ex = exceptions@;
            idxs.push(idx);
            if v.as_usize() == idx.as_usize() {
                // value == index as a nat; the value itself witnesses the T bound.
                proof {
                    v.lemma_as_nat_bounded();
                    assert forall|k: int| 0 <= k < i + 1 && !exception_at(exceptions@, k)
                        implies (#[trigger] diffs@[k]).0.as_nat() == diffs@[k].1.as_nat()
                            && diffs@[k].1.as_nat() < T::max_nat() by {
                        if k < i {
                            assert(!exception_at(pre_ex, k));
                        }
                    }
                }
            } else {
                exceptions.push((i, v));
                proof {
                    // Position i is now an exception (the just-pushed last element).
                    assert(exceptions@[exceptions@.len() - 1].0 == i);
                    assert(exception_at(exceptions@, i as int));
                    assert forall|k: int| 0 <= k < i + 1 && !exception_at(exceptions@, k)
                        implies (#[trigger] diffs@[k]).0.as_nat() == diffs@[k].1.as_nat()
                            && diffs@[k].1.as_nat() < T::max_nat() by {
                        if k == i {
                            assert(exception_at(exceptions@, k));
                            assert(false);
                        }
                        assert(!exception_at(pre_ex, k)) by {
                            if exception_at(pre_ex, k) {
                                let e = choose|e: int| 0 <= e < pre_ex.len()
                                    && (#[trigger] pre_ex[e]).0 == k;
                                assert(exceptions@[e] == pre_ex[e]);
                            }
                        }
                    }
                }
            }
            i = i + 1;
        }

        DeltaFrame { idxs, exceptions, pairs: Ghost(diffs@) }
    }

    /// Deterministic encoded footprint: the index column plus the exception list.
    pub fn byte_len(&self) -> usize {
        crate::compression_stats::sat_add(
            crate::compression_stats::sat_mul(self.idxs.len(), core::mem::size_of::<I>()),
            crate::compression_stats::sat_mul(self.exceptions.len(),
                crate::compression_stats::sat_add(core::mem::size_of::<usize>(), core::mem::size_of::<T>())))
    }
}

/// Whether position `k` appears in the exception list.
pub open spec fn exception_at<T>(ex: Seq<(usize, T)>, k: int) -> bool {
    exists|e: int| 0 <= e < ex.len() && (#[trigger] ex[e]).0 == k
}

pub enum ColdFrame<T: Copy, I, VC: crate::value_compressor::ValueCompressor<T> = crate::value_compressor::NoValueCompression> {
    Plain(Vec<(T, I)>),
    Dict(DictFrame<T, I>),
    Runs(RunCol<T, I>),
    /// The F2 composed mode: index layer x `ValueCompressor` value layer on
    /// one frame. The arm every column family can inhabit (the codec's bound
    /// decides which compressors exist for `T`).
    Layered(crate::layered::LayeredFrame<T, I, VC>),
}

/// An uncompressed (still-open) frame: the plain `(value, index)` write set. Takes
/// writes one at a time, can be sealed into any `CompressedFrame`, and can restore
/// itself straight to a live column (hot to live) by scattered writes.
pub struct HotFrame<T, I> {
    pub pairs: Vec<(T, I)>,
}

impl<T: Copy, I: IndexLike> HotFrame<T, I> {
    pub open spec fn wf(&self) -> bool { true }

    /// The write set, same abstraction as a compressed frame's `decode()`.
    pub open spec fn decode(&self) -> Seq<(T, I)> { self.pairs@ }

    pub fn new() -> (r: HotFrame<T, I>)
        ensures r.wf(), r.decode() == Seq::<(T, I)>::empty(),
    {
        let r = HotFrame { pairs: Vec::new() };
        assert(r.decode() =~= Seq::<(T, I)>::empty());
        r
    }

    pub fn entry_len(&self) -> (n: usize)
        ensures n == self.decode().len(),
    {
        self.pairs.len()
    }

    /// Record one write.
    pub fn add_write(&mut self, value: T, idx: I)
        ensures final(self).decode() == old(self).decode().push((value, idx)),
    {
        self.pairs.push((value, idx));
    }

    /// Restore this open frame straight to a live column (hot to live), scattered.
    pub fn restore_to(&self, target: &mut Vec<T>)
        ensures final(target)@ == apply_all::<T, I>(old(target)@, self.decode()),
    {
        let ghost base = target@;
        let n = self.pairs.len();
        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i <= n,
                n == self.pairs@.len(),
                target@ == apply_all::<T, I>(base, self.decode().subrange(0, i as int)),
            decreases n - i,
        {
            let (v, idx) = self.pairs[i];
            proof { lemma_apply_all_snoc::<T, I>(base, self.decode(), i as int); }
            let u = idx.as_usize();
            if u < target.len() {
                target.set(u, v);
            }
            i = i + 1;
        }
        proof { assert(self.decode().subrange(0, n as int) =~= self.decode()); }
    }
}

impl<T: IndexLike, I: IndexLike> HotFrame<T, I> {
    /// Seal this frame into a compressed one in the given mode (the per-frame runtime
    /// choice). Preserves the write set as a multiset.
    pub fn compress<VC: crate::value_compressor::ValueCompressor<T>>(&self, mode: CompressionMode) -> (r: ColdFrame<T, I, VC>)
        ensures
            r.wf(),
            r.decode().to_multiset() == self.decode().to_multiset(),
            unique_idx(self.decode()) ==> unique_idx(r.decode()),
    {
        ColdFrame::compress_mode(&self.pairs, mode)
    }
}

impl<T: Copy, I: IndexLike, VC: crate::value_compressor::ValueCompressor<T>> ColdFrame<T, I, VC> {
    pub open spec fn wf(&self) -> bool {
        match self {
            ColdFrame::Plain(_) => true,
            ColdFrame::Dict(d) => d.wf(),
            ColdFrame::Runs(r) => r.wf(),
            ColdFrame::Layered(l) => l.wf(),
        }
    }

    /// The flat write sequence this frame decodes to, mode-agnostically.
    pub open spec fn decode(&self) -> Seq<(T, I)> {
        match self {
            ColdFrame::Plain(v) => v@,
            ColdFrame::Dict(d) => d.decode(),
            ColdFrame::Runs(r) => r.decode(),
            ColdFrame::Layered(l) => l.decode(),
        }
    }

    /// Entry count, O(1) in every mode except the layered one (codec-defined).
    pub fn entry_len(&self) -> (n: usize)
        requires self.wf(),
        ensures n == self.decode().len(),
    {
        match self {
            ColdFrame::Plain(v) => v.len(),
            ColdFrame::Dict(d) => d.entry_len(),
            ColdFrame::Runs(r) => r.entry_len(),
            ColdFrame::Layered(l) => l.entry_len(),
        }
    }

    /// Random access to entry `i`, mode-agnostically (the read `DiffLog::index` needs).
    pub fn decode_at(&self, i: usize) -> (e: (T, I))
        requires self.wf(), i < self.decode().len(),
        ensures e == self.decode()[i as int],
    {
        match self {
            ColdFrame::Plain(v) => v[i],
            ColdFrame::Dict(d) => d.decode_at(i),
            ColdFrame::Runs(r) => r.decode_at(i),
            ColdFrame::Layered(l) => l.decode_at(i),
        }
    }

    /// Value-opaque encode: the modes that move values verbatim (no dictionary),
    /// so only `T: Copy` is needed — every column qualifies, structs included.
    /// Implements the self-demotion rule (goal F2.1b): after encoding runs, the
    /// encoder compares its real `byte_len` against the plain frame and emits the
    /// PLAIN frame when runs did not coalesce enough to pay; the contract is the
    /// same either way, so the demotion is invisible to callers, and a run frame
    /// larger than its plain equivalent can never be stored.
    pub fn compress_mode_copy(diffs: &Vec<(T, I)>, mode: CompressionMode) -> (r: ColdFrame<T, I, VC>)
        ensures
            r.wf(),
            r.decode().to_multiset() == diffs@.to_multiset(),
            unique_idx(diffs@) ==> unique_idx(r.decode()),
    {
        let runs = match mode {
            CompressionMode::IndexRuns => Some(RunCol::compress(diffs)),
            CompressionMode::IndexRunsSorted => Some(RunCol::compress_sorted(diffs)),
            _ => None,
        };
        let base = match runs {
            Some(rc) => {
                // Self-demotion: real encoded size against the plain frame.
                let plain_bytes = plain_frame_bytes::<T, I>(diffs.len());
                if rc.byte_len() <= plain_bytes {
                    ColdFrame::Runs(rc)
                } else {

                    Self::plain_copy(diffs)
                }
            }
            None => Self::plain_copy(diffs),
        };
        Self::select_layered(diffs, base)
    }

    /// The F2.5 selector: when the column's codec is enabled, ALSO build the
    /// layered candidates (index runs x codec, plain index x codec) and keep
    /// whichever of {base, layered} has the smallest real encoded size. The
    /// layered candidates decode EXACTLY the input, so every contract the
    /// base carries (write multiset, unique-index preservation) is theirs
    /// too, and self-demotion to the base (which itself demotes to plain) is
    /// the fallback whenever the codec does not pay. `byte_len` is
    /// diagnostic-only, so the CHOICE carries no proof weight: whichever
    /// frame wins, its own wf/decode contract is what restores.
    pub fn select_layered(diffs: &Vec<(T, I)>, base: ColdFrame<T, I, VC>)
        -> (r: ColdFrame<T, I, VC>)
        requires
            base.wf(),
            base.decode().to_multiset() == diffs@.to_multiset(),
            unique_idx(diffs@) ==> unique_idx(base.decode()),
        ensures
            r.wf(),
            r.decode().to_multiset() == diffs@.to_multiset(),
            unique_idx(diffs@) ==> unique_idx(r.decode()),
    {
        if !VC::enabled() {
            return base;
        }
        // The sorted candidate reorders, so it enters only when the frame's
        // indices are unique (the same runtime gate the base sorted encoder
        // rides behind); the exact candidates enter unconditionally.
        let lay_runs = crate::layered::LayeredFrame::<T, I, VC>::compress_runs(diffs);
        let lay_plain = crate::layered::LayeredFrame::<T, I, VC>::compress_plain(diffs);
        let lay_sorted = if is_unique_idx(diffs) {
            Some(crate::layered::LayeredFrame::<T, I, VC>::compress_runs_sorted(diffs))
        } else {
            None
        };
        let bb = base.byte_len();
        let rb = lay_runs.byte_len();
        let pb = lay_plain.byte_len();
        let sb = match &lay_sorted {
            Some(f) => f.byte_len(),
            None => usize::MAX,
        };
        if sb <= bb && sb <= rb && sb <= pb {
            match lay_sorted {
                Some(f) => ColdFrame::Layered(f),
                None => base,
            }
        } else if rb <= bb && rb <= pb {
            ColdFrame::Layered(lay_runs)
        } else if pb <= bb {
            ColdFrame::Layered(lay_plain)
        } else {
            base
        }
    }

    /// The plain frame (exact copy). Factored so both the `None` mode and the
    /// self-demotion path share it.
    pub fn plain_copy(diffs: &Vec<(T, I)>) -> (r: ColdFrame<T, I, VC>)
        ensures
            r.wf(),
            r.decode() == diffs@,
    {
        let mut copy: Vec<(T, I)> = Vec::new();
        let mut i: usize = 0;
        while i < diffs.len()
            invariant i <= diffs@.len(), copy@ == diffs@.subrange(0, i as int),
            decreases diffs@.len() - i,
        {
            copy.push(diffs[i]);
            i += 1;
        }
        assert(copy@ =~= diffs@);
        ColdFrame::Plain(copy)
    }

    /// Deterministic encoded footprint (for the per-frame size comparison / heap check).
    pub fn byte_len(&self) -> usize {
        match self {
            ColdFrame::Plain(v) => crate::compression_stats::sat_mul(v.len(),
                crate::compression_stats::sat_add(core::mem::size_of::<T>(), core::mem::size_of::<I>())),
            ColdFrame::Dict(d) => crate::compression_stats::sat_add(
                crate::compression_stats::sat_add(crate::compression_stats::sat_mul(d.dict.len(), core::mem::size_of::<T>()), d.codes.byte_len()),
                crate::compression_stats::sat_mul(d.idxs.len(), core::mem::size_of::<I>())),
            ColdFrame::Runs(r) => r.byte_len(),
            ColdFrame::Layered(l) => l.byte_len(),
        }
    }

    /// Bulk decode: materialize the whole frame's pairs. One pass per mode
    /// (`Plain` copies, `Dict` decodes codes, `Runs` reconstructs indices).
    pub fn decode_exec_cold(&self) -> (r: Vec<(T, I)>)
        requires self.wf(),
        ensures r@ == self.decode(),
    {
        match self {
            ColdFrame::Plain(v) => {
                let mut copy: Vec<(T, I)> = Vec::new();
                let mut i: usize = 0;
                while i < v.len()
                    invariant i <= v@.len(), copy@ == v@.subrange(0, i as int),
                    decreases v@.len() - i,
                {
                    copy.push(v[i]);
                    i += 1;
                }
                assert(copy@ =~= v@);
                copy
            }
            ColdFrame::Dict(d) => d.decode_exec(),
            ColdFrame::Runs(r) => r.decode_exec(),
            ColdFrame::Layered(l) => l.decode_exec(),
        }
    }

    /// Restore this frame straight to a live column (cold to live), dispatching on the
    /// per-frame mode: `Runs` uses the sliced memcpy, `Plain`/`Dict` write scattered.
    /// Same contract for every mode, so the caller is representation-agnostic.
    pub fn restore_to(&self, target: &mut Vec<T>)
        requires self.wf(),
        ensures final(target)@ == apply_all::<T, I>(old(target)@, self.decode()),
    {
        match self {
            ColdFrame::Plain(v) => {
                let ghost base = target@;
                let n = v.len();
                let mut i: usize = 0;
                while i < n
                    invariant
                        0 <= i <= n,
                        n == v@.len(),
                        target@ == apply_all::<T, I>(base, v@.subrange(0, i as int)),
                    decreases n - i,
                {
                    let (val, idx) = v[i];
                    proof { lemma_apply_all_snoc::<T, I>(base, v@, i as int); }
                    let u = idx.as_usize();
                    if u < target.len() {
                        target.set(u, val);
                    }
                    i = i + 1;
                }
                proof { assert(v@.subrange(0, n as int) =~= v@); }
            }
            ColdFrame::Dict(d) => CompressedFrame::restore_to(d, target),
            ColdFrame::Runs(r) => CompressedFrame::restore_to(r, target),
            ColdFrame::Layered(l) => l.restore_to(target),
        }
    }
}

/// The enum is the runtime-dispatch carrier: `choose_mode` picks a variant per frame,
/// and this impl makes the whole per-frame mix satisfy one interface, so callers hold
/// `ColdFrame` and never see which encoding a frame actually uses.
impl<T: Copy, I: IndexLike, VC: crate::value_compressor::ValueCompressor<T>> CompressedFrame<T, I> for ColdFrame<T, I, VC> {
    open spec fn wf(&self) -> bool { ColdFrame::wf(self) }

    open spec fn decode(&self) -> Seq<(T, I)> { ColdFrame::decode(self) }

    fn entry_len(&self) -> (n: usize) { ColdFrame::entry_len(self) }

    fn decode_at(&self, i: usize) -> (e: (T, I)) { ColdFrame::decode_at(self, i) }

    fn restore_to(&self, target: &mut Vec<T>) { ColdFrame::restore_to(self, target) }
}

impl<T: IndexLike, I: IndexLike, VC: crate::value_compressor::ValueCompressor<T>> ColdFrame<T, I, VC> {
    /// Encode a finalized frame, picking the mode. `Plain`, `ValueDict`, `IndexRuns`
    /// (write-order) and `IndexRunsSorted` (sort-first) all preserve the write
    /// multiset; `Plain`/`ValueDict`/`IndexRuns` also preserve the exact sequence.
    /// `decode().to_multiset() == diffs@.to_multiset()` for every mode.
    pub fn compress_mode(diffs: &Vec<(T, I)>, mode: CompressionMode) -> (r: ColdFrame<T, I, VC>)
        ensures
            r.wf(),
            r.decode().to_multiset() == diffs@.to_multiset(),
            unique_idx(diffs@) ==> unique_idx(r.decode()),
    {
        let base = match mode {
            CompressionMode::ValueDict => {
                let d = compress(diffs);
                ColdFrame::Dict(d)
            }
            CompressionMode::IndexRuns => {
                let rc = RunCol::compress(diffs);
                assert(rc.decode() == diffs@);
                ColdFrame::Runs(rc)
            }
            CompressionMode::IndexRunsSorted => {
                let rc = RunCol::compress_sorted(diffs);
                ColdFrame::Runs(rc)
            }
            // None and Auto (which is resolved to a concrete mode before flush) fall
            // back to a plain copy.
            _ => {
                let mut copy: Vec<(T, I)> = Vec::new();
                let mut i: usize = 0;
                while i < diffs.len()
                    invariant i <= diffs@.len(), copy@ == diffs@.subrange(0, i as int),
                    decreases diffs@.len() - i,
                {
                    copy.push(diffs[i]);
                    i += 1;
                }
                assert(copy@ =~= diffs@);
                ColdFrame::Plain(copy)
            }
        };
        Self::select_layered(diffs, base)
    }
}

} // verus!
