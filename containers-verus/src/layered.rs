// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! The layered frame (goal F2.2): ONE frame whose index layer {plain, runs}
//! composes with any [`ValueCompressor`] value layer. The index layer stores
//! either the verbatim index column or `(start, len)` runs (the index column
//! dropped); the value layer codes the SAME entry order's value column. The
//! seven composed modes of the goal are instantiations: index arm x codec,
//! with the sorted-runs variant entering through
//! [`LayeredFrame::compress_runs_sorted`] (the only reordering path, so the
//! only multiset-not-sequence contract).
//!
//! The frame carries its ghost model (`pairs`), the same shape as `RunCol`:
//! `wf` ties the stored columns to the model entry by entry, `decode()` is
//! the model, and every compressor proves the model against its input.

use crate::diff_compress::{RunCol, RunEntry};
use crate::index_like::IndexLike;
use crate::value_compressor::ValueCompressor;
use vstd::prelude::*;

verus! {

/// The index layer: verbatim column, or `(start, len)` runs with the column
/// dropped.
pub enum IdxCol<I> {
    Plain(Vec<I>),
    Runs(Vec<(I, usize)>),
}

/// The cell indices (as nats) a run list expands to, in order.
pub open spec fn runs_idx_seq<I: IndexLike>(rs: Seq<(I, usize)>) -> Seq<nat>
    decreases rs.len(),
{
    if rs.len() == 0 {
        Seq::empty()
    } else {
        runs_idx_seq(rs.drop_last())
            + Seq::new(rs.last().1 as nat, |k: int| (rs.last().0.as_nat() + k) as nat)
    }
}

/// Appending a run extends the expansion by that run's indices.
pub proof fn lemma_runs_idx_snoc<I: IndexLike>(rs: Seq<(I, usize)>, r: (I, usize))
    ensures
        runs_idx_seq(rs.push(r)) == runs_idx_seq(rs)
            + Seq::new(r.1 as nat, |k: int| (r.0.as_nat() + k) as nat),
{
    let pushed = rs.push(r);
    assert(pushed.drop_last() =~= rs);
    assert(runs_idx_seq(pushed) =~= runs_idx_seq(rs)
        + Seq::new(r.1 as nat, |k: int| (r.0.as_nat() + k) as nat));
}

/// Prefix expansion length grows by run `j`'s length, and prefix expansions
/// are prefixes of the whole (the same induction as the RLE lemmas).
pub proof fn lemma_runs_idx_prefix<I: IndexLike>(rs: Seq<(I, usize)>, j: int)
    requires 0 <= j <= rs.len(),
    ensures
        runs_idx_seq(rs.subrange(0, j)).len() <= runs_idx_seq(rs).len(),
        runs_idx_seq(rs.subrange(0, j)) =~= runs_idx_seq(rs).subrange(
            0, runs_idx_seq(rs.subrange(0, j)).len() as int),
    decreases rs.len() - j,
{
    if j == rs.len() {
        assert(rs.subrange(0, j) =~= rs);
    } else {
        lemma_runs_idx_prefix(rs, j + 1);
        assert(rs.subrange(0, j + 1).drop_last() =~= rs.subrange(0, j));
        assert(runs_idx_seq(rs.subrange(0, j + 1))
            == runs_idx_seq(rs.subrange(0, j))
                + Seq::new(rs[j].1 as nat, |k: int| (rs[j].0.as_nat() + k) as nat));
    }
}

/// Position `off` inside run `j` expands to `start_j + off`.
pub proof fn lemma_runs_idx_at<I: IndexLike>(rs: Seq<(I, usize)>, j: int, off: int)
    requires
        0 <= j < rs.len(),
        0 <= off < rs[j].1,
    ensures
        runs_idx_seq(rs).len()
            >= runs_idx_seq(rs.subrange(0, j)).len() + rs[j].1,
        runs_idx_seq(rs)[runs_idx_seq(rs.subrange(0, j)).len() + off]
            == (rs[j].0.as_nat() + off) as nat,
{
    lemma_runs_idx_prefix(rs, j);
    lemma_runs_idx_prefix(rs, j + 1);
    let pfx = runs_idx_seq(rs.subrange(0, j)).len() as int;
    assert(rs.subrange(0, j + 1).drop_last() =~= rs.subrange(0, j));
    assert(runs_idx_seq(rs.subrange(0, j + 1))
        == runs_idx_seq(rs.subrange(0, j))
            + Seq::new(rs[j].1 as nat, |k: int| (rs[j].0.as_nat() + k) as nat));
    assert(runs_idx_seq(rs.subrange(0, j + 1))[pfx + off]
        == (rs[j].0.as_nat() + off) as nat);
}

impl<I: IndexLike> IdxCol<I> {
    /// The cell indices (as nats) this layer holds, in entry order.
    pub open spec fn idx_seq(&self) -> Seq<nat> {
        match self {
            IdxCol::Plain(v) => Seq::new(v@.len(), |j: int| v@[j].as_nat()),
            IdxCol::Runs(rs) => runs_idx_seq(rs@),
        }
    }
}

/// The value part of a `crate::diff_compress::run_seq` (parallel to `runs_idx_seq` on the index
/// side): what the flattened value column must equal.
pub open spec fn seq_vals<T>(s: Seq<(nat, T)>) -> Seq<T> {
    Seq::new(s.len(), |j: int| s[j].1)
}

/// The index part of a `crate::diff_compress::run_seq`.
pub open spec fn seq_idxs<T>(s: Seq<(nat, T)>) -> Seq<nat> {
    Seq::new(s.len(), |j: int| s[j].0)
}

/// ONE frame, index layer x value layer, with the ghost model.
pub struct LayeredFrame<T: Copy, I, VC: ValueCompressor<T>> {
    pub pairs: Ghost<Seq<(T, I)>>,
    pub idx: IdxCol<I>,
    pub vals: VC::Compressed,
}

impl<T: Copy, I: IndexLike, VC: ValueCompressor<T>> LayeredFrame<T, I, VC> {
    /// The stored columns reconstruct the model entry by entry.
    pub open spec fn wf(&self) -> bool {
        let dec = VC::decode(&self.vals);
        &&& VC::cwf(&self.vals)
        &&& self.pairs@.len() <= usize::MAX as nat
        &&& dec.len() == self.pairs@.len()
        &&& self.idx.idx_seq().len() == self.pairs@.len()
        &&& forall|j: int| 0 <= j < self.pairs@.len() ==> {
            &&& (#[trigger] self.pairs@[j]).0 == dec[j]
            &&& self.pairs@[j].1.as_nat() == self.idx.idx_seq()[j]
            &&& self.idx.idx_seq()[j] < I::max_nat()
        }
    }

    /// The write set this frame holds.
    pub open spec fn decode(&self) -> Seq<(T, I)> {
        self.pairs@
    }

    /// Plain index layer + coded value layer. EXACT: preserves the sequence.
    pub fn compress_plain(diffs: &Vec<(T, I)>) -> (r: Self)
        ensures r.wf(), r.decode() == diffs@,
    {
        let n = diffs.len();
        let mut idxs: Vec<I> = Vec::new();
        let mut flat: Vec<T> = Vec::new();
        let mut i: usize = 0;
        while i < n
            invariant
                i <= n,
                n == diffs@.len(),
                idxs@.len() == i,
                flat@.len() == i,
                forall|j: int| 0 <= j < i ==> (#[trigger] idxs@[j]) == diffs@[j].1,
                forall|j: int| 0 <= j < i ==> (#[trigger] flat@[j]) == diffs@[j].0,
                forall|j: int| 0 <= j < i
                    ==> (#[trigger] diffs@[j].1).as_nat() < I::max_nat(),
            decreases n - i,
        {
            let (v, ix) = diffs[i];
            proof { ix.lemma_as_nat_bounded(); }
            idxs.push(ix);
            flat.push(v);
            i += 1;
        }
        let vals = VC::compress(&flat);
        let r = LayeredFrame { pairs: Ghost(diffs@), idx: IdxCol::Plain(idxs), vals };
        proof {
            assert(diffs@.len() == n as nat);
            assert(VC::decode(&r.vals) =~= flat@);
            assert forall|j: int| 0 <= j < r.pairs@.len() implies {
                &&& (#[trigger] r.pairs@[j]).0 == VC::decode(&r.vals)[j]
                &&& r.pairs@[j].1.as_nat() == r.idx.idx_seq()[j]
                &&& r.idx.idx_seq()[j] < I::max_nat()
            } by {
                assert(flat@[j] == diffs@[j].0);
            }
        }
        r
    }

    /// Convert a proven `RunCol` (whatever encoder built it) into the layered
    /// shape: `(start, len)` runs plus the flattened, coded value column.
    fn from_run_col(rc: RunCol<T, I>) -> (r: Self)
        requires rc.wf(),
        ensures r.wf(), r.decode() == rc.decode(),
    {
        proof { reveal_with_fuel(crate::diff_compress::run_seq, 1); }
        let m = rc.runs.len();
        let mut rs: Vec<(I, usize)> = Vec::new();
        let mut flat: Vec<T> = Vec::new();
        let mut j: usize = 0;
        proof {
            assert(rc.runs@.subrange(0, 0) =~= Seq::<RunEntry<T, I>>::empty());
            assert(crate::diff_compress::run_seq::<T, I>(Seq::empty()) =~= Seq::<(nat, T)>::empty());
            assert(runs_idx_seq::<I>(Seq::empty()) =~= Seq::<nat>::empty());
        }
        while j < m
            invariant
                j <= m,
                m == rc.runs@.len(),
                rs@.len() == j,
                forall|k: int| 0 <= k < j
                    ==> (#[trigger] rs@[k]).0 == rc.runs@[k].start
                        && rs@[k].1 == rc.runs@[k].vals@.len(),
                runs_idx_seq(rs@) =~= seq_idxs(crate::diff_compress::run_seq(rc.runs@.subrange(0, j as int))),
                flat@ =~= seq_vals(crate::diff_compress::run_seq(rc.runs@.subrange(0, j as int))),
            decreases m - j,
        {
            let ghost pre_rs = rs@;
            let ghost pre_flat = flat@;
            let ghost prefix = rc.runs@.subrange(0, j as int);
            let start = rc.runs[j].start;
            let rl = rc.runs[j].vals.len();
            rs.push((start, rl));
            // Append this run's values.
            let mut k: usize = 0;
            while k < rl
                invariant
                    k <= rl,
                    rl == rc.runs@[j as int].vals@.len(),
                    j < m,
                    m == rc.runs@.len(),
                    flat@ =~= pre_flat + rc.runs@[j as int].vals@.subrange(0, k as int),
                decreases rl - k,
            {
                let v = rc.runs[j].vals[k];
                flat.push(v);
                proof {
                    assert(rc.runs@[j as int].vals@.subrange(0, k as int + 1)
                        =~= rc.runs@[j as int].vals@.subrange(0, k as int)
                            .push(rc.runs@[j as int].vals@[k as int]));
                }
                k += 1;
            }
            proof {
                let r_j = rc.runs@[j as int];
                assert(rc.runs@.subrange(0, j as int + 1) =~= prefix.push(r_j));
                crate::diff_compress::lemma_run_seq_snoc(prefix, r_j);
                lemma_runs_idx_snoc(pre_rs, (r_j.start, r_j.vals@.len() as usize));
                assert(rs@ =~= pre_rs.push((r_j.start, r_j.vals@.len() as usize)));
                let newpart = Seq::new(r_j.vals@.len(),
                    |k: int| ((r_j.start.as_nat() + k) as nat, r_j.vals@[k]));
                assert(crate::diff_compress::run_seq(rc.runs@.subrange(0, j as int + 1))
                    == crate::diff_compress::run_seq(prefix) + newpart);
                assert(rc.runs@[j as int].vals@.subrange(0, rl as int)
                    =~= rc.runs@[j as int].vals@);
                assert(seq_idxs(crate::diff_compress::run_seq(prefix) + newpart)
                    =~= seq_idxs(crate::diff_compress::run_seq(prefix)) + seq_idxs(newpart));
                assert(seq_vals(crate::diff_compress::run_seq(prefix) + newpart)
                    =~= seq_vals(crate::diff_compress::run_seq(prefix)) + seq_vals(newpart));
                assert(seq_idxs(newpart)
                    =~= Seq::new(r_j.vals@.len(), |k: int| (r_j.start.as_nat() + k) as nat));
                assert(seq_vals(newpart) =~= r_j.vals@);
                assert(runs_idx_seq(rs@)
                    =~= seq_idxs(crate::diff_compress::run_seq(rc.runs@.subrange(0, j as int + 1))));
                assert(flat@ =~= seq_vals(crate::diff_compress::run_seq(rc.runs@.subrange(0, j as int + 1))));
            }
            j += 1;
        }
        proof { assert(rc.runs@.subrange(0, m as int) =~= rc.runs@); }
        let ghost cap = rc.len;
        proof { assert(rc.pairs@.len() == cap as nat); }
        let vals = VC::compress(&flat);
        let r = LayeredFrame { pairs: Ghost(rc.pairs@), idx: IdxCol::Runs(rs), vals };
        proof {
            assert(r.pairs@.len() <= usize::MAX as nat);
            let full = crate::diff_compress::run_seq(rc.runs@);
            assert(VC::decode(&r.vals) =~= seq_vals(full));
            assert(r.idx.idx_seq() =~= seq_idxs(full));
            // rc.wf ties pairs to crate::diff_compress::run_seq entry by entry; transfer.
            assert forall|t: int| 0 <= t < r.pairs@.len() implies {
                &&& (#[trigger] r.pairs@[t]).0 == VC::decode(&r.vals)[t]
                &&& r.pairs@[t].1.as_nat() == r.idx.idx_seq()[t]
                &&& r.idx.idx_seq()[t] < I::max_nat()
            } by {
                assert(r.pairs@[t].0 == full[t].1);
                assert(r.pairs@[t].1.as_nat() == full[t].0);
            }
        }
        r
    }

    /// Write-order runs + coded values. EXACT: preserves the sequence.
    pub fn compress_runs(diffs: &Vec<(T, I)>) -> (r: Self)
        ensures r.wf(), r.decode() == diffs@,
    {
        Self::from_run_col(RunCol::compress(diffs))
    }

    /// Sort-first runs + coded values: the strongest index compressor for
    /// scattered writes landing in a contiguous set. REORDERS, so the
    /// contract is the write multiset (and unique-index preservation), the
    /// same shape as `RunCol::compress_sorted` (which needs only `IndexLike`:
    /// sorting compares indices, and the runs store their `start` verbatim).
    pub fn compress_runs_sorted(diffs: &Vec<(T, I)>) -> (r: Self)
        ensures
            r.wf(),
            r.decode().to_multiset() == diffs@.to_multiset(),
            crate::diff_compress::unique_idx(diffs@)
                ==> crate::diff_compress::unique_idx(r.decode()),
    {
        let rc = RunCol::compress_sorted(diffs);
        Self::from_run_col(rc)
    }

    /// Entry count.
    pub fn entry_len(&self) -> (n: usize)
        requires self.wf(),
        ensures n == self.decode().len(),
    {
        VC::decoded_len(&self.vals)
    }

    /// Write this frame's set back onto a live column: scattered stores,
    /// decoding each value through the codec. Matches the reference
    /// `crate::diff_compress::apply_all` exactly (the F2.2 restore contract).
    pub fn restore_to(&self, target: &mut Vec<T>)
        requires self.wf(),
        ensures final(target)@ == crate::diff_compress::apply_all::<T, I>(old(target)@, self.decode()),
    {
        let ghost base = target@;
        match &self.idx {
            IdxCol::Plain(idxs) => {
                let n = idxs.len();
                let mut t: usize = 0;
                while t < n
                    invariant
                        t <= n,
                        self.wf(),
                        n == self.decode().len(),
                        n == idxs@.len(),
                        self.idx == IdxCol::Plain(*idxs),
                        target@ == crate::diff_compress::apply_all::<T, I>(
                            base, self.decode().subrange(0, t as int)),
                    decreases n - t,
                {
                    let v = VC::decode_at(&self.vals, t);
                    let u = idxs[t].as_usize();
                    proof {
                        crate::diff_compress::lemma_apply_all_snoc::<T, I>(base, self.decode(), t as int);
                        assert(self.decode()[t as int].1.as_nat()
                            == self.idx.idx_seq()[t as int]);
                    }
                    if u < target.len() {
                        target.set(u, v);
                    }
                    t += 1;
                }
                proof {
                    assert(self.decode().subrange(0, n as int) =~= self.decode());
                }
            }
            IdxCol::Runs(rs) => {
                let m = rs.len();
                let mut j: usize = 0;
                let mut p: usize = 0;
                proof {
                    assert(rs@.subrange(0, 0) =~= Seq::<(I, usize)>::empty());
                    assert(runs_idx_seq::<I>(Seq::empty()) =~= Seq::<nat>::empty());
                }
                while j < m
                    invariant
                        j <= m,
                        self.wf(),
                        m == rs@.len(),
                        self.idx == IdxCol::Runs(*rs),
                        p as nat == runs_idx_seq(rs@.subrange(0, j as int)).len(),
                        p <= self.decode().len(),
                        target@ == crate::diff_compress::apply_all::<T, I>(
                            base, self.decode().subrange(0, p as int)),
                    decreases m - j,
                {
                    proof { lemma_runs_idx_prefix(rs@, j as int); }
                    let (start, rl) = rs[j];
                    let ghost p0 = p as int;
                    let su = start.as_usize();
                    let mut k: usize = 0;
                    proof {
                        lemma_runs_idx_prefix(rs@, j as int + 1);
                        assert(rs@.subrange(0, j as int + 1).drop_last()
                            =~= rs@.subrange(0, j as int));
                        assert(runs_idx_seq(rs@.subrange(0, j as int + 1))
                            == runs_idx_seq(rs@.subrange(0, j as int))
                                + Seq::new(rs@[j as int].1 as nat,
                                    |k: int| (rs@[j as int].0.as_nat() + k) as nat));
                    }
                    while k < rl
                        invariant
                            k <= rl,
                            j < m,
                            self.wf(),
                            m == rs@.len(),
                            self.idx == IdxCol::Runs(*rs),
                            (start, rl) == rs@[j as int],
                            su as nat == start.as_nat(),
                            p as int == p0 + k,
                            p0 == runs_idx_seq(rs@.subrange(0, j as int)).len(),
                            p0 + rl <= self.decode().len(),
                            target@ == crate::diff_compress::apply_all::<T, I>(
                                base, self.decode().subrange(0, p as int)),
                        decreases rl - k,
                    {
                        proof {
                            lemma_runs_idx_at(rs@, j as int, k as int);
                            assert(self.decode()[p as int].1.as_nat()
                                == self.idx.idx_seq()[p as int]);
                            assert(self.idx.idx_seq()[p as int]
                                == (start.as_nat() + k) as nat);
                            assert(self.idx.idx_seq()[p as int] < I::max_nat());
                            <I as IndexLike>::lemma_max_nat_fits_usize();
                        }
                        let v = VC::decode_at(&self.vals, p);
                        let u = su + k;
                        proof {
                            crate::diff_compress::lemma_apply_all_snoc::<T, I>(base, self.decode(), p as int);
                        }
                        if u < target.len() {
                            target.set(u, v);
                        }
                        p += 1;
                        k += 1;
                    }
                    j += 1;
                }
                proof {
                    assert(rs@.subrange(0, m as int) =~= rs@);
                    assert(self.decode().subrange(0, p as int) =~= self.decode());
                }
            }
        }
    }

    /// Random access to entry `i`. The index is reconstructed from the run
    /// arithmetic through `try_from_usize` and pinned to the model's index by
    /// `as_nat` injectivity, so plain `IndexLike` suffices (no `IndexFromNat`).
    pub fn decode_at(&self, i: usize) -> (e: (T, I))
        requires self.wf(), i < self.decode().len(),
        ensures e == self.decode()[i as int],
    {
        let v = VC::decode_at(&self.vals, i);
        proof {
            assert(self.decode()[i as int].0 == v);
            assert(self.decode()[i as int].1.as_nat() == self.idx.idx_seq()[i as int]);
            assert(self.idx.idx_seq()[i as int] < I::max_nat());
        }
        let ix: I = match &self.idx {
            IdxCol::Plain(idxs) => {
                let ix = idxs[i];
                proof {
                    assert(self.idx.idx_seq()[i as int] == idxs@[i as int].as_nat());
                    I::lemma_as_nat_injective(ix, self.decode()[i as int].1);
                }
                ix
            }
            IdxCol::Runs(rs) => {
                // Locate the run containing position `i` (linear scan with a
                // running total, the RLE pattern).
                let m = rs.len();
                let mut seen: usize = 0;
                let mut j: usize = 0;
                proof {
                    assert(rs@.subrange(0, 0) =~= Seq::<(I, usize)>::empty());
                    assert(runs_idx_seq::<I>(Seq::empty()) =~= Seq::<nat>::empty());
                }
                loop
                    invariant
                        j <= m,
                        self.wf(),
                        m == rs@.len(),
                        self.idx == IdxCol::Runs(*rs),
                        (i as nat) < self.decode().len(),
                        seen as nat == runs_idx_seq(rs@.subrange(0, j as int)).len(),
                        seen <= i,
                        v == self.decode()[i as int].0,
                    decreases m - j,
                {
                    proof {
                        if j == m {
                            assert(rs@.subrange(0, m as int) =~= rs@);
                        }
                    }
                    assert(j < m);
                    proof { lemma_runs_idx_prefix(rs@, j as int); }
                    proof {
                        assert(rs@.subrange(0, j as int + 1).drop_last()
                            =~= rs@.subrange(0, j as int));
                        assert(runs_idx_seq(rs@.subrange(0, j as int + 1))
                            == runs_idx_seq(rs@.subrange(0, j as int))
                                + Seq::new(rs@[j as int].1 as nat,
                                    |k: int| (rs@[j as int].0.as_nat() + k) as nat));
                        lemma_runs_idx_prefix(rs@, j as int + 1);
                    }
                    let (start, rl) = rs[j];
                    if i - seen < rl {
                        proof {
                            lemma_runs_idx_at(rs@, j as int, (i - seen) as int);
                            assert(self.idx.idx_seq()[i as int]
                                == (start.as_nat() + (i - seen)) as nat);
                            <I as IndexLike>::lemma_max_nat_fits_usize();
                        }
                        let su = start.as_usize();
                        proof {
                            assert(su as nat == start.as_nat());
                            assert(su as nat + (i - seen) as nat
                                == self.idx.idx_seq()[i as int]);
                            // Re-fire the wf quantifier at `i` in this context.
                            assert((#[verifier::trigger] self.pairs@[i as int]).1.as_nat()
                                == self.idx.idx_seq()[i as int]);
                            assert(self.idx.idx_seq()[i as int] < I::max_nat());
                            assert((su as nat + (i - seen) as nat) < I::max_nat());
                            assert((su as nat + (i - seen) as nat)
                                <= usize::MAX as nat);
                        }
                        let u = su + (i - seen);
                        proof {
                            assert((u as nat) < I::max_nat());
                        }
                        let ix = match I::try_from_usize(u) {
                            Some(x) => x,
                            None => {
                                proof { assert(false); }
                                start
                            }
                        };
                        proof {
                            I::lemma_as_nat_injective(ix, self.decode()[i as int].1);
                            let e = self.decode()[i as int];
                            assert(e == (e.0, e.1));
                            assert(ix == self.decode()[i as int].1);
                            assert(v == self.decode()[i as int].0);
                            assert((v, ix) == self.decode()[i as int]);
                        }
                        return (v, ix);
                    }
                    seen = seen + rl;
                    j += 1;
                }
            }
        };
        (v, ix)
    }

    /// Executable decode: materialize the flat diff sequence (what the
    /// diff-log integration calls to bring a compressed frame back to plain).
    pub fn decode_exec(&self) -> (r: Vec<(T, I)>)
        requires self.wf(),
        ensures r@ == self.decode(),
    {
        let n = self.entry_len();
        let mut out: Vec<(T, I)> = Vec::new();
        let mut t: usize = 0;
        while t < n
            invariant
                t <= n,
                self.wf(),
                n == self.decode().len(),
                out@.len() == t,
                forall|k: int| #![auto] 0 <= k < t ==> out@[k] == self.decode()[k],
            decreases n - t,
        {
            let e = self.decode_at(t);
            out.push(e);
            t += 1;
        }
        proof { assert(out@ =~= self.decode()); }
        out
    }

    /// Length-based encoded byte count: index layer + value layer.
    pub fn byte_len(&self) -> usize {
        let idx_bytes = match &self.idx {
            IdxCol::Plain(v) => crate::compression_stats::sat_mul(v.len(), core::mem::size_of::<I>()),
            IdxCol::Runs(rs) => crate::compression_stats::sat_mul(rs.len(),
                crate::compression_stats::sat_add(core::mem::size_of::<I>(), core::mem::size_of::<usize>())),
        };
        crate::compression_stats::sat_add(idx_bytes, VC::byte_len(&self.vals))
    }
}



} // verus!
