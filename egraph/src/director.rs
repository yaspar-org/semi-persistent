// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Director bitmatrices for alpha-invariant e-graphs.
//!
//! See `doc/future/semi-persistent-director-bitmatrices.md` for the full design.

use core::fmt;
use core::hash::Hash;

use crate::containers::Tagged;
use crate::containers::dense_id::IndexLike;
use crate::containers::{AppendOnlyVec, ShrinkPolicy, VecI, VecToken};

// ---------------------------------------------------------------------------
// PortArity — transparent newtype over u8 for matrix dimensions
// ---------------------------------------------------------------------------

/// Matrix dimension / e-class arity. Transparent wrapper over `u8`.
/// Max value 255, checked arithmetic on increment.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
#[repr(transparent)]
pub struct PortArity(pub u8);

impl PortArity {
    pub const ZERO: Self = PortArity(0);
    pub const ONE: Self = PortArity(1);
    pub const MAX: Self = PortArity(u8::MAX);

    #[inline]
    pub fn new(n: u8) -> Self {
        PortArity(n)
    }

    /// Checked increment. Panics with diagnostic on overflow.
    #[inline]
    pub fn checked_add(self, d: PortArity) -> Self {
        PortArity(self.0.checked_add(d.0).expect("arity overflow (max 255)"))
    }

    /// `max(self, other)` — used for merge.
    #[inline]
    pub fn max(self, other: Self) -> Self {
        PortArity(self.0.max(other.0))
    }

    /// Product `self * other` as u32 (for bit count calculations).
    #[inline]
    pub fn product(self, other: Self) -> u32 {
        (self.0 as u32) * (other.0 as u32)
    }
}

impl From<PortArity> for u8 {
    #[inline]
    fn from(a: PortArity) -> u8 {
        a.0
    }
}

impl From<u8> for PortArity {
    #[inline]
    fn from(n: u8) -> PortArity {
        PortArity(n)
    }
}

impl From<PortArity> for u32 {
    #[inline]
    fn from(a: PortArity) -> u32 {
        a.0 as u32
    }
}

impl From<PortArity> for usize {
    #[inline]
    fn from(a: PortArity) -> usize {
        a.0 as usize
    }
}

impl fmt::Debug for PortArity {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl fmt::Display for PortArity {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

// ---------------------------------------------------------------------------
// DirectorBits — compile-time word width for inline director storage
// ---------------------------------------------------------------------------

/// Trait selecting the inline bit width for director matrices.
///
/// `BITS = 0` (impl for `()`) disables binder support entirely.
/// `BITS > 0` reserves the MSB as a spill tag, leaving `BITS - 1`
/// inline matrix bits.
pub trait DirectorBits: Copy + Eq + Hash + Ord + fmt::Debug + 'static {
    const BITS: u32;
    const SPILL_TAG: Self;
    fn from_u64(v: u64) -> Self;
    fn to_u64(self) -> u64;
}

// -- () : no directors, zero overhead --

impl DirectorBits for () {
    const BITS: u32 = 0;
    const SPILL_TAG: Self = ();
    #[inline(always)]
    fn from_u64(_: u64) -> Self {}
    #[inline(always)]
    fn to_u64(self) -> u64 {
        0
    }
}

// -- u16 : 15 inline bits --

impl DirectorBits for u16 {
    const BITS: u32 = 16;
    const SPILL_TAG: Self = 0x8000;
    #[inline(always)]
    fn from_u64(v: u64) -> Self {
        v as u16
    }
    #[inline(always)]
    fn to_u64(self) -> u64 {
        self as u64
    }
}

// -- u32 : 31 inline bits --

impl DirectorBits for u32 {
    const BITS: u32 = 32;
    const SPILL_TAG: Self = 0x8000_0000;
    #[inline(always)]
    fn from_u64(v: u64) -> Self {
        v as u32
    }
    #[inline(always)]
    fn to_u64(self) -> u64 {
        self as u64
    }
}

// -- u64 : 63 inline bits --

impl DirectorBits for u64 {
    const BITS: u32 = 64;
    const SPILL_TAG: Self = 0x8000_0000_0000_0000;
    #[inline(always)]
    fn from_u64(v: u64) -> Self {
        v
    }
    #[inline(always)]
    fn to_u64(self) -> u64 {
        self
    }
}

// ---------------------------------------------------------------------------
// Director<W> — inline or spilled director bitmatrix
// ---------------------------------------------------------------------------

/// A k×n bit matrix stored inline (MSB=0) or as a spill pool reference (MSB=1).
///
/// When `W = ()`, this is a ZST — all methods are no-ops.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub struct Director<W: DirectorBits>(pub(crate) W);

impl<W: DirectorBits> fmt::Debug for Director<W> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if W::BITS == 0 {
            write!(f, "Dir(∅)")
        } else if self.is_inline() {
            write!(f, "Dir(0x{:x})", self.0.to_u64())
        } else {
            write!(f, "Dir(spill@{})", self.pool_index())
        }
    }
}

impl<W: DirectorBits> Director<W> {
    /// All-zero matrix (ground edge, no variable ports).
    #[inline]
    pub fn zero() -> Self {
        Director(W::from_u64(0))
    }

    /// Inline matrix from raw bits. Panics if bits overflow inline capacity.
    #[inline]
    pub fn new_inline(bits: u64) -> Self {
        if W::BITS > 0 {
            debug_assert!(
                bits & (W::SPILL_TAG.to_u64()) == 0,
                "inline bits overflow: MSB must be 0"
            );
        }
        Director(W::from_u64(bits))
    }

    /// Spilled matrix referencing a pool entry.
    #[inline]
    pub fn new_spilled(pool_index: usize) -> Self {
        assert!(W::BITS > 0, "cannot spill with DIRECTOR_BITS=0");
        let idx = pool_index as u64;
        debug_assert!(idx & W::SPILL_TAG.to_u64() == 0, "pool index overflow");
        Director(W::from_u64(idx | W::SPILL_TAG.to_u64()))
    }

    /// True if the matrix data is stored inline (not spilled).
    #[inline]
    pub fn is_inline(&self) -> bool {
        W::BITS == 0 || (self.0.to_u64() & W::SPILL_TAG.to_u64()) == 0
    }

    /// Raw inline bits. Panics if spilled.
    #[inline]
    pub fn inline_bits(&self) -> u64 {
        debug_assert!(self.is_inline(), "called inline_bits on spilled matrix");
        self.0.to_u64()
    }

    /// Pool start index. Panics if inline.
    #[inline]
    pub fn pool_index(&self) -> usize {
        debug_assert!(!self.is_inline(), "called pool_index on inline matrix");
        (self.0.to_u64() & !W::SPILL_TAG.to_u64()) as usize
    }

    /// Raw word value (for hashing, sort keys).
    #[inline]
    pub fn raw(&self) -> W {
        self.0
    }

    // -- Resolve / pack helpers -----------------------------------------------

    /// Resolve to raw u64 bits. For inline, returns the bits directly.
    /// For spilled, reads from pool and packs into a single u64.
    /// Panics if spilled matrix exceeds 64 bits (caller must use
    /// `resolve_pooled` for large matrices).
    fn resolve<const TRACK: bool, const PROOFS: bool>(
        &self,
        pool: &DirectorPool<TRACK, PROOFS>,
    ) -> u64 {
        if W::BITS == 0 {
            return 0;
        }
        if self.is_inline() {
            self.inline_bits()
        } else {
            let (bit_length, data) = pool.read(self.pool_index());
            assert!(bit_length <= 64, "spilled matrix too large for resolve()");
            if data.is_empty() { 0 } else { data[0].bits() }
        }
    }

    /// Pack raw u64 bits into a Director<W>. If the bits fit inline, store
    /// directly. Otherwise spill to pool.
    fn pack<const TRACK: bool, const PROOFS: bool>(
        bits: u64,
        total_bits: u32,
        pool: &mut DirectorPool<TRACK, PROOFS>,
    ) -> Self {
        if W::BITS == 0 {
            return Self::zero();
        }
        let inline_cap = W::BITS - 1;
        if total_bits <= inline_cap && (bits & W::SPILL_TAG.to_u64()) == 0 {
            Self::new_inline(bits)
        } else {
            let data = [PoolDirector::new(bits)];
            let start = pool.append(total_bits, &data);
            Self::new_spilled(start)
        }
    }

    // -- Reads ----------------------------------------------------------------

    /// Extract row `i` from a k×n matrix. Returns an n-bit value with
    /// at most one bit set (the parent port that child port `i` maps to).
    /// Zero means child port `i` is unbound (consumed by a binder).
    pub fn row_extract<const TRACK: bool, const PROOFS: bool>(
        &self,
        i: u8,
        n: u8,
        pool: &DirectorPool<TRACK, PROOFS>,
    ) -> u64 {
        ops::row_extract(self.resolve(pool), i, n)
    }

    /// Does any child port map to parent port `j`?
    pub fn col_present<const TRACK: bool, const PROOFS: bool>(
        &self,
        j: u8,
        k: u8,
        n: u8,
        pool: &DirectorPool<TRACK, PROOFS>,
    ) -> bool {
        ops::col_present(self.resolve(pool), j, k, n)
    }

    /// OR of all rows: which parent ports are referenced by any child port?
    pub fn embed_bitset<const TRACK: bool, const PROOFS: bool>(
        &self,
        k: u8,
        n: u8,
        pool: &DirectorPool<TRACK, PROOFS>,
    ) -> u64 {
        ops::embed_bitset(self.resolve(pool), k, n)
    }

    // -- Transforms -----------------------------------------------------------

    /// Chain two edges: outer (k_mid × n_outer) ∘ inner (k_inner × k_mid).
    /// Result is k_inner × n_outer.
    pub fn compose<const TRACK: bool, const PROOFS: bool>(
        outer: &Self,
        inner: &Self,
        k_inner: u8,
        k_mid: u8,
        n_outer: u8,
        pool: &mut DirectorPool<TRACK, PROOFS>,
    ) -> Self {
        let ob = outer.resolve(pool);
        let ib = inner.resolve(pool);
        let result = ops::compose(ob, ib, k_inner, k_mid, n_outer);
        Self::pack(result, (k_inner as u32) * (n_outer as u32), pool)
    }

    /// Parent arity grew from old_n to new_n. Re-lay rows to wider width.
    pub fn widen_columns<const TRACK: bool, const PROOFS: bool>(
        &self,
        k: u8,
        old_n: u8,
        new_n: u8,
        pool: &mut DirectorPool<TRACK, PROOFS>,
    ) -> Self {
        let bits = self.resolve(pool);
        let result = ops::widen_columns(bits, k, old_n, new_n);
        Self::pack(result, (k as u32) * (new_n as u32), pool)
    }

    /// Child arity grew from old_k to new_k. New rows are zero.
    pub fn add_zero_rows<const TRACK: bool, const PROOFS: bool>(
        &self,
        old_k: u8,
        new_k: u8,
        n: u8,
        pool: &mut DirectorPool<TRACK, PROOFS>,
    ) -> Self {
        let bits = self.resolve(pool);
        let result = ops::add_zero_rows(bits, old_k, new_k, n);
        Self::pack(result, (new_k as u32) * (n as u32), pool)
    }

    /// Reorder rows according to a permutation (port reconciliation on merge).
    pub fn permute_rows<const TRACK: bool, const PROOFS: bool>(
        &self,
        perm: &[u8],
        k: u8,
        n: u8,
        pool: &mut DirectorPool<TRACK, PROOFS>,
    ) -> Self {
        let bits = self.resolve(pool);
        let result = ops::permute_rows(bits, perm, k, n);
        Self::pack(result, (k as u32) * (n as u32), pool)
    }

    /// Introduce `d` bound variable ports. Input k×n → result (k+d)×(n+d).
    pub fn shift<const TRACK: bool, const PROOFS: bool>(
        &self,
        k: u8,
        n: u8,
        d: u8,
        pool: &mut DirectorPool<TRACK, PROOFS>,
    ) -> Self {
        let bits = self.resolve(pool);
        let result = ops::shift(bits, k, n, d);
        Self::pack(result, ((k + d) as u32) * ((n + d) as u32), pool)
    }

    /// Eliminate parent port `j` (substitution). Input k×n → result k×(n-1).
    pub fn delete_column<const TRACK: bool, const PROOFS: bool>(
        &self,
        j: u8,
        k: u8,
        n: u8,
        pool: &mut DirectorPool<TRACK, PROOFS>,
    ) -> Self {
        let bits = self.resolve(pool);
        let result = ops::delete_column(bits, j, k, n);
        Self::pack(result, (k as u32) * ((n - 1) as u32), pool)
    }

    // -- Constructors ---------------------------------------------------------

    /// k×n identity matrix. Spills if k*n exceeds inline capacity.
    pub fn identity<const TRACK: bool, const PROOFS: bool>(
        k: u8,
        n: u8,
        pool: &mut DirectorPool<TRACK, PROOFS>,
    ) -> Self {
        let bits = ops::identity(k, n);
        Self::pack(bits, (k as u32) * (n as u32), pool)
    }
}

// ---------------------------------------------------------------------------
// Edge<G, W> — e-class id + director matrix
// ---------------------------------------------------------------------------

/// An edge from a parent e-node to a child e-class, carrying a director
/// matrix that routes variable ports.
///
/// When `W = ()`, this has the same size and layout as `G`.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct Edge<G, W: DirectorBits> {
    pub class: G,
    pub director: Director<W>,
}

impl<G: fmt::Debug, W: DirectorBits> fmt::Debug for Edge<G, W> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if W::BITS == 0 {
            write!(f, "{:?}", self.class)
        } else {
            write!(f, "({:?}, {:?})", self.class, self.director)
        }
    }
}

impl<G, W: DirectorBits> Edge<G, W> {
    #[inline]
    pub fn new(class: G, director: Director<W>) -> Self {
        Self { class, director }
    }

    /// Ground edge (no variable ports).
    #[inline]
    pub fn ground(class: G) -> Self {
        Self {
            class,
            director: Director::zero(),
        }
    }
}

// ---------------------------------------------------------------------------
// PoolDirector — a u64 with MSB stolen for Tagged capture tracking
// ---------------------------------------------------------------------------

/// A 64-bit word stored in the spill pool. The MSB is reserved for the
/// `Tagged` capture bit used by `SemiVec`, leaving 63 usable bits for
/// director matrix data.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct PoolDirector(u64);

// Filler for `resize_default` during restore; never observed. `new(0)` leaves
// the MSB tag bit clear, so the all-zero word is niche-safe.
impl Default for PoolDirector {
    fn default() -> Self {
        PoolDirector::new(0)
    }
}

impl PoolDirector {
    /// Usable bits per pool word (64 - 1 tag bit).
    pub const USABLE_BITS: u32 = 63;
    const TAG_BIT: u64 = 1 << 63;

    #[inline]
    pub fn new(bits: u64) -> Self {
        debug_assert!(
            bits & Self::TAG_BIT == 0,
            "pool word overflow: bit 63 reserved"
        );
        PoolDirector(bits)
    }

    #[inline]
    pub fn bits(self) -> u64 {
        self.0 & !Self::TAG_BIT
    }
}

impl Tagged for PoolDirector {
    type Repr = Self;

    #[inline]
    fn into_repr(self) -> Self {
        self
    }

    #[inline]
    fn from_repr(r: &Self) -> Self {
        PoolDirector(r.0 & !Self::TAG_BIT)
    }

    #[inline]
    fn tag(r: &Self) -> bool {
        r.0 & Self::TAG_BIT != 0
    }

    #[inline]
    fn set_tag(r: &mut Self) {
        r.0 |= Self::TAG_BIT;
    }

    #[inline]
    fn clear_tag(r: &mut Self) {
        r.0 &= !Self::TAG_BIT;
    }
}

// ---------------------------------------------------------------------------
// DirectorPool — append-only spill arena for oversized director matrices
// ---------------------------------------------------------------------------

/// Semi-persistent spill pool for oversized director matrices.
///
/// Each entry is length-prefixed:
///   `pool[start]`     = bit_length (as PoolDirector)
///   `pool[start+1..]` = matrix data, `ceil(bit_length / 63)` words
///
/// The working pool is a `VecI<PoolDirector, u32, TRACK>` — supports in-place
/// mutation (for re-canonization during rebuild) with capture tracking.
///
/// When `PROOFS = true`, a separate append-only proof pool snapshots
/// spilled matrices at copy-on-first-recanonicalization time. The proof
/// pool is never truncated during working rollback.
pub struct DirectorPool<const TRACK: bool = true, const PROOFS: bool = false> {
    /// Working pool: mutable, capture-tracked, rollback by restore.
    work: VecI<PoolDirector, u32, TRACK>,
    /// Proof pool: append-only, survives working rollback.
    proof: AppendOnlyVec<PoolDirector, TRACK>,
}

impl<const TRACK: bool, const PROOFS: bool> Default for DirectorPool<TRACK, PROOFS> {
    fn default() -> Self {
        Self::new()
    }
}

impl<const TRACK: bool, const PROOFS: bool> DirectorPool<TRACK, PROOFS> {
    pub fn new() -> Self {
        Self {
            work: VecI::with_store(Default::default()),
            proof: AppendOnlyVec::new(),
        }
    }

    // -- Working pool ---------------------------------------------------------

    /// Append a spilled matrix to the working pool. Returns the start index.
    pub fn append(&mut self, bit_length: u32, data: &[PoolDirector]) -> usize {
        let start = self.work.len().as_usize();
        self.work.push(PoolDirector::new(bit_length as u64));
        for &w in data {
            self.work.push(w);
        }
        start
    }

    /// Read bit_length from a working pool entry.
    pub fn bit_length(&self, start: usize) -> u32 {
        self.work.get(start as u32).bits() as u32
    }

    /// Get a single working pool word by index.
    pub fn get(&self, idx: u32) -> PoolDirector {
        self.work.get(idx)
    }

    /// Mutate a working pool word in place (for re-canonization).
    pub fn set(&mut self, idx: u32, val: PoolDirector) {
        self.work.set(idx, val);
    }

    /// Read a spilled matrix from the working pool.
    pub fn read(&self, start: usize) -> (u32, std::vec::Vec<PoolDirector>) {
        let bit_length = self.work.get(start as u32).bits() as u32;
        let word_count = ceil_div(bit_length, PoolDirector::USABLE_BITS);
        let mut data = std::vec::Vec::with_capacity(word_count);
        for i in 0..word_count {
            data.push(self.work.get((start + 1 + i) as u32));
        }
        (bit_length, data)
    }

    /// Current working pool length.
    pub fn len(&self) -> usize {
        self.work.len().as_usize()
    }

    pub fn is_empty(&self) -> bool {
        self.work.is_empty()
    }

    /// Mark for semi-persistent checkpoint.
    pub fn mark(&mut self, shrink: ShrinkPolicy) -> VecToken {
        self.work.mark(shrink)
    }

    /// Restore to a previous checkpoint.
    pub fn restore(&mut self, token: VecToken) {
        self.work.restore(token);
    }

    // -- Proof pool -----------------------------------------------------------

    /// Snapshot a spilled matrix into the proof pool (copy-on-first-recanon).
    /// Returns the start index in the proof pool.
    pub fn snapshot_to_proof(&mut self, work_start: usize) -> usize {
        assert!(PROOFS, "snapshot_to_proof called with PROOFS=false");
        let (bit_length, data) = self.read(work_start);
        let proof_start = self.proof.len();
        self.proof.push(PoolDirector::new(bit_length as u64));
        for w in data {
            self.proof.push(w);
        }
        proof_start
    }

    /// Read a spilled matrix from the proof pool.
    pub fn read_proof(&self, start: usize) -> (u32, std::vec::Vec<PoolDirector>) {
        let bit_length = self.proof.get(start).bits() as u32;
        let word_count = ceil_div(bit_length, PoolDirector::USABLE_BITS);
        let mut data = std::vec::Vec::with_capacity(word_count);
        for i in 0..word_count {
            data.push(*self.proof.get(start + 1 + i));
        }
        (bit_length, data)
    }

    /// Proof pool length.
    pub fn proof_len(&self) -> usize {
        self.proof.len()
    }
}

fn ceil_div(a: u32, b: u32) -> usize {
    (a as usize).div_ceil(b as usize)
}

// ---------------------------------------------------------------------------
// Matrix operations — work on inline bits only (spill variants later)
// ---------------------------------------------------------------------------

/// All matrix ops take raw inline bits + dimensions. Callers must resolve
/// spilled matrices through the pool before calling these.
///
/// Layout: row-major, k rows of n bits each. Bit (i,j) at position i*n + j.
/// Row i represents child port i. At most one bit set per row (injection).
/// Bit (i,j) = 1 means child port i maps to parent port j.
pub mod ops {
    /// Extract row `i` from a k×n matrix (n-bit value, at most one bit set).
    #[inline]
    pub fn row_extract(bits: u64, i: u8, n: u8) -> u64 {
        let shift = (i as u32) * (n as u32);
        let mask = (1u64 << n) - 1;
        (bits >> shift) & mask
    }

    /// Set row `i` in a k×n matrix to `val`.
    #[inline]
    pub fn row_set(bits: u64, i: u8, n: u8, val: u64) -> u64 {
        let shift = (i as u32) * (n as u32);
        let mask = (1u64 << n) - 1;
        (bits & !(mask << shift)) | ((val & mask) << shift)
    }

    /// Is parent port `j` referenced by any child port?
    #[inline]
    pub fn col_present(bits: u64, j: u8, k: u8, n: u8) -> bool {
        for i in 0..k {
            if row_extract(bits, i, n) & (1u64 << j) != 0 {
                return true;
            }
        }
        false
    }

    /// Which parent ports are used? OR of all rows.
    #[inline]
    pub fn embed_bitset(bits: u64, k: u8, n: u8) -> u64 {
        let mask = (1u64 << n) - 1;
        let mut result = 0u64;
        for i in 0..k {
            result |= row_extract(bits, i, n);
        }
        result & mask
    }

    /// Identity matrix for k×n (bit (i,i) = 1 for i < min(k,n)).
    pub fn identity(k: u8, n: u8) -> u64 {
        let mut bits = 0u64;
        for i in 0..k.min(n) {
            bits |= 1u64 << ((i as u32) * (n as u32) + (i as u32));
        }
        bits
    }

    /// Compose outer (k_mid × n_outer) with inner (k_inner × k_mid).
    /// Result is k_inner × n_outer.
    ///
    /// Each row of inner has at most one bit at column p;
    /// composed row = row p of outer. Zero row → zero row.
    pub fn compose(outer: u64, inner: u64, k_inner: u8, k_mid: u8, n_outer: u8) -> u64 {
        let mut result = 0u64;
        for i in 0..k_inner {
            let inner_row = row_extract(inner, i, k_mid);
            if inner_row == 0 {
                continue; // zero row stays zero
            }
            let p = inner_row.trailing_zeros() as u8;
            let outer_row = row_extract(outer, p, n_outer);
            result |= outer_row << ((i as u32) * (n_outer as u32));
        }
        result
    }

    /// Widen columns: parent arity grew from old_n to new_n.
    /// Row values stay the same (bit j stays at j), rows just get wider.
    pub fn widen_columns(bits: u64, k: u8, old_n: u8, new_n: u8) -> u64 {
        debug_assert!(new_n >= old_n);
        let mut result = 0u64;
        for i in 0..k {
            let row = row_extract(bits, i, old_n);
            result |= row << ((i as u32) * (new_n as u32));
        }
        result
    }

    /// Add zero rows: child arity grew from old_k to new_k.
    /// Existing rows unchanged, new rows are zero.
    /// Re-lays bits because row width n is unchanged but total bit count grows.
    pub fn add_zero_rows(bits: u64, old_k: u8, new_k: u8, n: u8) -> u64 {
        debug_assert!(new_k >= old_k);
        // Rows 0..old_k are at the same positions, new rows are zero.
        // Since we store row-major and new rows go at the end, the
        // existing bits are already correct — just mask to old_k*n.
        let used = (old_k as u32) * (n as u32);
        if used >= 64 {
            bits
        } else {
            bits & ((1u64 << used) - 1)
        }
    }

    /// Permute rows: row i of result = row perm[i] of input.
    pub fn permute_rows(bits: u64, perm: &[u8], k: u8, n: u8) -> u64 {
        debug_assert!(perm.len() == k as usize);
        let mut result = 0u64;
        for i in 0..k {
            let row = row_extract(bits, perm[i as usize], n);
            result |= row << ((i as u32) * (n as u32));
        }
        result
    }

    /// Shift: introduce d bound ports. Input is k×n, result is (k+d)×(n+d).
    /// Rows 0..d are zero (bound ports). Row d+i = row i shifted right by d.
    pub fn shift(bits: u64, k: u8, n: u8, d: u8) -> u64 {
        let new_n = n + d;
        let mut result = 0u64;
        // rows 0..d are zero (implicit)
        for i in 0..k {
            let row = row_extract(bits, i, n);
            let shifted = row << (d as u32);
            result |= shifted << (((d + i) as u32) * (new_n as u32));
        }
        result
    }

    /// Delete column j: input is k×n, result is k×(n-1).
    /// Bits above column j shift down by 1.
    pub fn delete_column(bits: u64, j: u8, k: u8, n: u8) -> u64 {
        debug_assert!(n > 0);
        let new_n = n - 1;
        let mut result = 0u64;
        for i in 0..k {
            let row = row_extract(bits, i, n);
            // Remove bit j: keep low bits, shift high bits down
            let lo = row & ((1u64 << j) - 1);
            let hi = (row >> (j + 1)) << j;
            result |= (lo | hi) << ((i as u32) * (new_n as u32));
        }
        result
    }
}

// ---------------------------------------------------------------------------
// Static size assertions + tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn zst_child_edge_same_size_as_g() {
        assert_eq!(
            core::mem::size_of::<Edge<u32, ()>>(),
            core::mem::size_of::<u32>(),
        );
    }

    #[test]
    fn child_edge_sizes() {
        // u16 director pads to 8 due to u32 alignment
        assert_eq!(core::mem::size_of::<Edge<u32, u16>>(), 8);
        assert_eq!(core::mem::size_of::<Edge<u32, u32>>(), 8);
        assert_eq!(core::mem::size_of::<Edge<u32, u64>>(), 16);
    }

    #[test]
    fn inline_roundtrip() {
        let m = Director::<u32>::new_inline(0b0110_1001);
        assert!(m.is_inline());
        assert_eq!(m.inline_bits(), 0b0110_1001);
    }

    #[test]
    fn spill_roundtrip() {
        let m = Director::<u32>::new_spilled(42);
        assert!(!m.is_inline());
        assert_eq!(m.pool_index(), 42);
    }

    #[test]
    fn zero_matrix() {
        let m = Director::<u64>::zero();
        assert!(m.is_inline());
        assert_eq!(m.inline_bits(), 0);
    }

    #[test]
    fn zst_always_inline() {
        let m = Director::<()>::zero();
        assert!(m.is_inline());
    }

    #[test]
    #[should_panic(expected = "cannot spill")]
    fn zst_cannot_spill() {
        Director::<()>::new_spilled(0);
    }

    #[test]
    fn dir_word_u16_limits() {
        // max inline value: 15 bits set
        let m = Director::<u16>::new_inline(0x7FFF);
        assert!(m.is_inline());
        assert_eq!(m.inline_bits(), 0x7FFF);
    }

    #[test]
    fn dir_word_u64_limits() {
        // max inline value: 63 bits set
        let m = Director::<u64>::new_inline(0x7FFF_FFFF_FFFF_FFFF);
        assert!(m.is_inline());
    }

    #[test]
    fn ground_child_edge() {
        let e = Edge::<u32, u32>::ground(7);
        assert_eq!(e.class, 7);
        assert_eq!(e.director.inline_bits(), 0);
    }

    #[test]
    fn pool_word_size() {
        assert_eq!(core::mem::size_of::<PoolDirector>(), 8);
    }

    #[test]
    fn pool_word_roundtrip() {
        let w = PoolDirector::new(0x7FFF_FFFF_FFFF_FFFF);
        assert_eq!(w.bits(), 0x7FFF_FFFF_FFFF_FFFF);
    }

    #[test]
    fn pool_word_tagged() {
        let mut w = PoolDirector::new(42);
        assert!(!PoolDirector::tag(&w));
        PoolDirector::set_tag(&mut w);
        assert!(PoolDirector::tag(&w));
        // bits() strips the tag
        assert_eq!(PoolDirector::from_repr(&w).bits(), 42);
        PoolDirector::clear_tag(&mut w);
        assert!(!PoolDirector::tag(&w));
        assert_eq!(w.bits(), 42);
    }

    #[test]
    fn dir_pool_append_read() {
        let mut pool = DirectorPool::<false, false>::new();
        let data = [PoolDirector::new(0b1010101), PoolDirector::new(0b1100110)];
        let start = pool.append(126, &data);
        let (len, words) = pool.read(start);
        assert_eq!(len, 126);
        assert_eq!(words.len(), 2);
        assert_eq!(words[0].bits(), 0b1010101);
        assert_eq!(words[1].bits(), 0b1100110);
    }

    #[test]
    fn dir_pool_mark_restore() {
        let mut pool = DirectorPool::<true, false>::new();
        let token = pool.mark(crate::containers::ShrinkPolicy::Never);
        pool.append(63, &[PoolDirector::new(0xFF)]);
        pool.append(63, &[PoolDirector::new(0xAA)]);
        assert_eq!(pool.len(), 4);
        pool.restore(token);
        assert!(pool.is_empty());
    }

    #[test]
    fn dir_pool_mutate_in_place() {
        let mut pool = DirectorPool::<false, false>::new();
        let start = pool.append(63, &[PoolDirector::new(0xFF)]);
        assert_eq!(pool.get((start + 1) as u32).bits(), 0xFF);
        pool.set((start + 1) as u32, PoolDirector::new(0xAB));
        assert_eq!(pool.get((start + 1) as u32).bits(), 0xAB);
    }

    #[test]
    fn dir_pool_proof_snapshot() {
        let mut pool = DirectorPool::<false, true>::new();
        let start = pool.append(63, &[PoolDirector::new(0x42)]);
        let proof_start = pool.snapshot_to_proof(start);
        // mutate working copy
        pool.set((start + 1) as u32, PoolDirector::new(0x99));
        // proof copy unchanged
        let (len, data) = pool.read_proof(proof_start);
        assert_eq!(len, 63);
        assert_eq!(data[0].bits(), 0x42);
        // working copy changed
        let (_, wdata) = pool.read(start);
        assert_eq!(wdata[0].bits(), 0x99);
    }

    // -- Typed Director<W> API tests -------------------------------------------

    #[test]
    fn typed_api_inline() {
        let mut pool = DirectorPool::<false, false>::new();
        // 2×3 identity via typed API
        let m = Director::<u32>::identity(2, 3, &mut pool);
        assert!(m.is_inline());
        assert_eq!(m.row_extract(0, 3, &pool), 0b001);
        assert_eq!(m.row_extract(1, 3, &pool), 0b010);
        assert_eq!(m.embed_bitset(2, 3, &pool), 0b011);
        assert!(m.col_present(0, 2, 3, &pool));
        assert!(m.col_present(1, 2, 3, &pool));
        assert!(!m.col_present(2, 2, 3, &pool));
    }

    #[test]
    fn typed_api_compose() {
        let mut pool = DirectorPool::<false, false>::new();
        let id = Director::<u32>::identity(2, 2, &mut pool);
        let m = Director::<u32>::new_inline(0b10_01); // 2×2: row0=01, row1=10
        let c = Director::compose(&id, &m, 2, 2, 2, &mut pool);
        assert_eq!(c.inline_bits(), m.inline_bits());
    }

    #[test]
    fn typed_api_shift_delete_roundtrip() {
        let mut pool = DirectorPool::<false, false>::new();
        let m = Director::<u32>::identity(2, 2, &mut pool);
        let shifted = m.shift(2, 2, 1, &mut pool);
        // 3×3: row0=000, row1=010, row2=100
        assert_eq!(shifted.row_extract(0, 3, &pool), 0b000);
        assert_eq!(shifted.row_extract(1, 3, &pool), 0b010);
        assert_eq!(shifted.row_extract(2, 3, &pool), 0b100);
        // delete col 0, then remove row 0 manually
        let del = shifted.delete_column(0, 3, 3, &mut pool);
        // del is 3×2: row0=00, row1=01, row2=10
        assert_eq!(del.row_extract(0, 2, &pool), 0b00);
        assert_eq!(del.row_extract(1, 2, &pool), 0b01);
        assert_eq!(del.row_extract(2, 2, &pool), 0b10);
    }

    #[test]
    fn typed_api_spill_and_read() {
        // Use u16 (15 inline bits) and force a matrix that needs > 15 bits
        let mut pool = DirectorPool::<false, false>::new();
        // 4×4 identity = 16 bits, exceeds u16 inline (15 bits)
        let m = Director::<u16>::identity(4, 4, &mut pool);
        assert!(!m.is_inline(), "4×4 should spill with u16");
        // reads still work through pool
        assert_eq!(m.row_extract(0, 4, &pool), 0b0001);
        assert_eq!(m.row_extract(1, 4, &pool), 0b0010);
        assert_eq!(m.row_extract(2, 4, &pool), 0b0100);
        assert_eq!(m.row_extract(3, 4, &pool), 0b1000);
        assert_eq!(m.embed_bitset(4, 4, &pool), 0b1111);
    }

    // -----------------------------------------------------------------------
    // Matrix operation unit tests
    // -----------------------------------------------------------------------

    use super::ops::*;

    #[test]
    fn identity_2x3() {
        // 2×3: row 0 = 001, row 1 = 010
        let m = identity(2, 3);
        assert_eq!(row_extract(m, 0, 3), 0b001);
        assert_eq!(row_extract(m, 1, 3), 0b010);
    }

    #[test]
    fn identity_embed() {
        let m = identity(3, 4);
        assert_eq!(embed_bitset(m, 3, 4), 0b0111);
    }

    #[test]
    fn compose_identity_left() {
        // compose(identity, M) == M
        let m = 0b010_001u64; // 2×3: row0=001, row1=010
        let id = identity(3, 3);
        assert_eq!(compose(id, m, 2, 3, 3), m);
    }

    #[test]
    fn compose_identity_right() {
        // compose(M, identity) == M
        let m = 0b010_001u64; // 2×3
        let id = identity(2, 2);
        assert_eq!(compose(m, id, 2, 2, 3), m);
    }

    #[test]
    fn compose_swap() {
        // swap = [[0,1],[1,0]], applied to identity 2×2 = swap
        let swap = 0b01_10u64; // 2×2: row0=10, row1=01
        let id = identity(2, 2);
        let result = compose(id, swap, 2, 2, 2);
        assert_eq!(result, swap);
    }

    #[test]
    fn widen_preserves_rows() {
        let m = 0b10_01u64; // 2×2: row0=01, row1=10
        let w = widen_columns(m, 2, 2, 4);
        assert_eq!(row_extract(w, 0, 4), 0b0001);
        assert_eq!(row_extract(w, 1, 4), 0b0010);
    }

    #[test]
    fn add_zero_rows_preserves() {
        let m = 0b10_01u64; // 2×2
        let r = add_zero_rows(m, 2, 4, 2);
        assert_eq!(row_extract(r, 0, 2), 0b01);
        assert_eq!(row_extract(r, 1, 2), 0b10);
        // new rows are zero (they're beyond the original bits)
    }

    #[test]
    fn shift_1() {
        // 1×1 matrix [1], shift by 1 → 2×2 matrix [[0,0],[0,1]]
        let m = 0b1u64; // 1×1: row0=1
        let s = shift(m, 1, 1, 1);
        // result is 2×2: row0=00 (bound), row1=10 (shifted)
        assert_eq!(row_extract(s, 0, 2), 0b00);
        assert_eq!(row_extract(s, 1, 2), 0b10);
    }

    #[test]
    fn shift_preserves_structure() {
        // 2×2 identity, shift by 1 → 3×3
        let m = identity(2, 2);
        let s = shift(m, 2, 2, 1);
        // row 0: zero (bound)
        assert_eq!(row_extract(s, 0, 3), 0b000);
        // row 1: original row 0 shifted: bit 0 → bit 1
        assert_eq!(row_extract(s, 1, 3), 0b010);
        // row 2: original row 1 shifted: bit 1 → bit 2
        assert_eq!(row_extract(s, 2, 3), 0b100);
    }

    #[test]
    fn delete_column_middle() {
        // 2×3: row0=010 (port 1), row1=100 (port 2)
        let m = 0b100_010u64;
        // delete column 0 → 2×2: row0=01 (port 0, was 1), row1=10 (port 1, was 2)
        let d = delete_column(m, 0, 2, 3);
        assert_eq!(row_extract(d, 0, 2), 0b01);
        assert_eq!(row_extract(d, 1, 2), 0b10);
    }

    #[test]
    fn delete_column_removes_reference() {
        // 2×3: row0=001 (port 0), row1=010 (port 1)
        let m = 0b010_001u64;
        // delete column 1 → 2×2: row0=01 (port 0), row1=00 (was port 1, deleted)
        let d = delete_column(m, 1, 2, 3);
        assert_eq!(row_extract(d, 0, 2), 0b01);
        assert_eq!(row_extract(d, 1, 2), 0b00);
    }

    #[test]
    fn permute_swap() {
        // 2×2 identity, permute with [1,0] → swap
        let m = identity(2, 2);
        let p = permute_rows(m, &[1, 0], 2, 2);
        // row 0 of result = row 1 of input = 10
        assert_eq!(row_extract(p, 0, 2), 0b10);
        // row 1 of result = row 0 of input = 01
        assert_eq!(row_extract(p, 1, 2), 0b01);
    }

    // -----------------------------------------------------------------------
    // Property-based tests
    // -----------------------------------------------------------------------

    /// Properties tested:
    ///
    /// P1 (identity left):  compose(identity(k_mid, n), M) == M
    /// P2 (identity right): compose(M, identity(k, k_mid)) == M
    /// P3 (associativity):  compose(A, compose(B, C)) == compose(compose(A, B), C)
    /// P4 (embed subset):   embed_bitset(compose(A, B)) ⊆ embed_bitset(A)
    /// P5 (widen idempotent): widen(widen(m, k, a, b), k, b, c) == widen(m, k, a, c)
    /// P6 (shift zero rows): row_extract(shift(m,k,n,d), i, n+d) == 0 for i < d
    /// P7 (shift preserves): row_extract(shift(m,k,n,d), d+i, n+d) == row_extract(m,i,n) << d
    /// P8 (permute embed):   embed_bitset(permute(m,p,k,n)) == embed_bitset(m,k,n)
    /// P9 (permute inverse): permute(permute(m,p,k,n), inv(p), k, n) == m
    /// P10 (delete shrinks): total bits of result == k*(n-1)
    /// P11 (injection):      each row has at most one bit set (for identity, compose, shift)
    mod prop {
        use super::*;
        use proptest::prelude::*;

        // -- Strategies -------------------------------------------------------

        /// Random injection matrix: k rows of n bits, at most one bit per row.
        fn arb_matrix(k: u8, n: u8) -> impl Strategy<Value = u64> {
            proptest::collection::vec(0..=(n as usize), k as usize).prop_map(move |cols| {
                let mut bits = 0u64;
                for (i, &c) in cols.iter().enumerate() {
                    if c < n as usize {
                        bits |= 1u64 << (i * n as usize + c);
                    }
                }
                bits
            })
        }

        fn arb_perm(k: u8) -> impl Strategy<Value = Vec<u8>> {
            Just((0..k).collect::<Vec<u8>>()).prop_shuffle()
        }

        fn dims_and_matrix() -> impl Strategy<Value = (u8, u8, u64)> {
            (1u8..=5, 1u8..=5)
                .prop_filter("fits", |&(k, n)| (k as u32) * (n as u32) <= 63)
                .prop_flat_map(|(k, n)| arb_matrix(k, n).prop_map(move |m| (k, n, m)))
        }

        fn two_composable() -> impl Strategy<Value = (u8, u8, u8, u64, u64)> {
            (1u8..=4, 1u8..=4, 1u8..=4)
                .prop_filter("fits", |&(ki, km, no)| {
                    [
                        ki as u32 * km as u32,
                        km as u32 * no as u32,
                        ki as u32 * no as u32,
                    ]
                    .iter()
                    .all(|&x| x <= 63)
                })
                .prop_flat_map(|(ki, km, no)| {
                    (arb_matrix(km, no), arb_matrix(ki, km))
                        .prop_map(move |(o, i)| (ki, km, no, o, i))
                })
        }

        fn three_composable() -> impl Strategy<Value = (u8, u8, u8, u8, u64, u64, u64)> {
            (1u8..=3, 1u8..=3, 1u8..=3, 1u8..=3)
                .prop_filter("fits", |&(ka, kb, kc, nd)| {
                    [kb * nd, ka * kb, kc * ka, ka * nd, kc * kb, kc * nd]
                        .iter()
                        .all(|&x| (x as u32) <= 63)
                })
                .prop_flat_map(|(ka, kb, kc, nd)| {
                    (arb_matrix(kb, nd), arb_matrix(ka, kb), arb_matrix(kc, ka))
                        .prop_map(move |(a, b, c)| (ka, kb, kc, nd, a, b, c))
                })
        }

        fn shift_args() -> impl Strategy<Value = (u8, u8, u8, u64)> {
            (1u8..=4, 1u8..=4, 1u8..=3)
                .prop_filter("fits", |&(k, n, d)| {
                    (k as u32 + d as u32) * (n as u32 + d as u32) <= 63
                })
                .prop_flat_map(|(k, n, d)| arb_matrix(k, n).prop_map(move |m| (k, n, d, m)))
        }

        fn delete_args() -> impl Strategy<Value = (u8, u8, u8, u64)> {
            (1u8..=5, 2u8..=6)
                .prop_filter("fits", |&(k, n)| (k as u32) * (n as u32) <= 63)
                .prop_flat_map(|(k, n)| {
                    (0..n, arb_matrix(k, n)).prop_map(move |(j, m)| (k, n, j, m))
                })
        }

        fn widen_args() -> impl Strategy<Value = (u8, u8, u8, u8, u64)> {
            (1u8..=4, 1u8..=4, 0u8..=3, 0u8..=3)
                .prop_filter("fits", |&(k, a, d1, d2)| {
                    (k as u32) * ((a + d1 + d2) as u32) <= 63
                })
                .prop_flat_map(|(k, a, d1, d2)| {
                    arb_matrix(k, a).prop_map(move |m| (k, a, a + d1, a + d1 + d2, m))
                })
        }

        fn add_rows_args() -> impl Strategy<Value = (u8, u8, u8, u64)> {
            (1u8..=4, 1u8..=3, 1u8..=5)
                .prop_filter("fits", |&(k, extra, n)| {
                    ((k + extra) as u32) * (n as u32) <= 63
                })
                .prop_flat_map(|(k, extra, n)| arb_matrix(k, n).prop_map(move |m| (k, extra, n, m)))
        }

        fn perm_args() -> impl Strategy<Value = (u8, u8, u64, Vec<u8>)> {
            (1u8..=5, 1u8..=5)
                .prop_filter("fits", |&(k, n)| (k as u32) * (n as u32) <= 63)
                .prop_flat_map(|(k, n)| {
                    (arb_matrix(k, n), arb_perm(k)).prop_map(move |(m, p)| (k, n, m, p))
                })
        }

        // -- Properties -------------------------------------------------------

        proptest! {
            // P1: identity is left unit for compose
            #[test]
            fn prop_identity_left((k, n, m) in dims_and_matrix()) {
                let id = identity(n, n);
                prop_assert_eq!(compose(id, m, k, n, n), m);
            }

            // P2: identity is right unit for compose
            #[test]
            fn prop_identity_right((k, n, m) in dims_and_matrix()) {
                let id = identity(k, k);
                prop_assert_eq!(compose(m, id, k, k, n), m);
            }

            // P3: compose is associative
            #[test]
            fn prop_compose_associative((ka, kb, kc, nd, a, b, c) in three_composable()) {
                let ab = compose(a, b, ka, kb, nd);
                let bc = compose(b, c, kc, ka, kb);
                prop_assert_eq!(compose(ab, c, kc, ka, nd), compose(a, bc, kc, kb, nd));
            }

            // P4: compose can't introduce parent ports not in outer
            #[test]
            fn prop_compose_embed_subset((ki, km, no, outer, inner) in two_composable()) {
                let composed = compose(outer, inner, ki, km, no);
                prop_assert_eq!(embed_bitset(composed, ki, no) & !embed_bitset(outer, km, no), 0);
            }

            // P5: widen is transitive
            #[test]
            fn prop_widen_transitive((k, a, b, c, m) in widen_args()) {
                let step = widen_columns(widen_columns(m, k, a, b), k, b, c);
                prop_assert_eq!(step, widen_columns(m, k, a, c));
            }

            // P6+P7: shift structure — bound rows zero, free rows shifted
            #[test]
            fn prop_shift_structure((k, n, d, m) in shift_args()) {
                let s = shift(m, k, n, d);
                let nn = n + d;
                for i in 0..d {
                    prop_assert_eq!(row_extract(s, i, nn), 0);
                }
                for i in 0..k {
                    prop_assert_eq!(row_extract(s, d + i, nn), row_extract(m, i, n) << d);
                }
            }

            // P8: permute preserves embed_bitset
            #[test]
            fn prop_permute_preserves_embed((k, n, m, p) in perm_args()) {
                prop_assert_eq!(embed_bitset(permute_rows(m, &p, k, n), k, n), embed_bitset(m, k, n));
            }

            // P9: permute is reversible
            #[test]
            fn prop_permute_inverse((k, n, m, p) in perm_args()) {
                let mut inv = vec![0u8; k as usize];
                for (i, &pi) in p.iter().enumerate() { inv[pi as usize] = i as u8; }
                prop_assert_eq!(permute_rows(permute_rows(m, &p, k, n), &inv, k, n), m);
            }

            // P10: delete preserves injection
            #[test]
            fn prop_delete_preserves_injection((k, n, j, m) in delete_args()) {
                let d = delete_column(m, j, k, n);
                for i in 0..k {
                    prop_assert!(row_extract(d, i, n - 1).count_ones() <= 1);
                }
            }

            // P11: compose preserves injection
            #[test]
            fn prop_compose_preserves_injection((ki, km, no, outer, inner) in two_composable()) {
                let c = compose(outer, inner, ki, km, no);
                for i in 0..ki {
                    prop_assert!(row_extract(c, i, no).count_ones() <= 1);
                }
            }

            // P12: delete remaps columns correctly
            #[test]
            fn prop_delete_column_remaps((k, n, j, m) in delete_args()) {
                let d = delete_column(m, j, k, n);
                for jp in 0..n-1 {
                    let orig = if jp < j { jp } else { jp + 1 };
                    prop_assert_eq!(col_present(d, jp, k, n-1), col_present(m, orig, k, n));
                }
            }

            // P13: add_zero_rows preserves existing, new rows zero
            #[test]
            fn prop_add_rows_structure((k, extra, n, m) in add_rows_args()) {
                let r = add_zero_rows(m, k, k + extra, n);
                for i in 0..k {
                    prop_assert_eq!(row_extract(r, i, n), row_extract(m, i, n));
                }
                for i in k..k+extra {
                    prop_assert_eq!(row_extract(r, i, n), 0);
                }
            }

            // P14: shift then peel bound ports recovers original
            #[test]
            fn prop_shift_delete_roundtrip((k, n, d, m) in shift_args()) {
                let mut s = shift(m, k, n, d);
                let mut ck = k + d;
                let mut cn = n + d;
                for _ in 0..d {
                    s = delete_column(s, 0, ck, cn);
                    cn -= 1;
                    let mut rebuilt = 0u64;
                    for i in 1..ck {
                        rebuilt |= row_extract(s, i, cn) << (((i-1) as u32) * (cn as u32));
                    }
                    s = rebuilt;
                    ck -= 1;
                }
                prop_assert_eq!(s, m);
            }
        }
    }
}
