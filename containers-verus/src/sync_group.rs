// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! The owning `ForkHistory` (doc 03 §6): one genealogy object holds N
//! heterogeneous synchronized members behind `Box<dyn SyncMember>` and is the
//! sole authority for group `mark`/`restore`. `mark` writes ONE generation
//! stamp then fans `seal_frame` (hot-to-cold compression) out over every
//! member; `restore` validates the token ONCE then fans `restore_frame`
//! (decompression straight into each member's live column, memcpy where the
//! frame is contiguous) out, then records the branch cut once. The genealogy
//! is touched only outside the fan-out, which is what makes the fan-out
//! parallelizable (the members' `&mut` borrows are disjoint).
//!
//! `SyncMember` is object-safe by construction: no method mentions the
//! member's element or index type, no generics, no associated types. The
//! per-member view/snapshot equality cannot be stated over the erased type,
//! so the TRAIT carries the depth discipline (the group invariant) and the
//! member IMPLS keep their strong typed contracts (`Vec::seal_frame`,
//! `Vec::restore_frame`); the heterogeneous differential test checks contents
//! against per-member oracles.

use crate::history::{GroupToken, History};
use crate::vec::ShrinkPolicy;
use vstd::prelude::*;

verus! {

/// One synchronized member, type-erased. The three operations are exactly the
/// genealogy-free cores: seal (compress the open frame, open the next), restore
/// (reconstruct to a depth, frames applied straight to the live column), and a
/// diagnostic footprint. `Send` because the group's parallel twins fan the members
/// out across the rayon pool (each thread gets one member's disjoint `&mut`).
pub trait SyncMember: Send {
    spec fn wf(&self) -> bool;

    /// Frame-stack depth; the group invariant quantifies over this.
    spec fn depth_spec(&self) -> nat;

    /// Whether a seal can be taken now (the member-side structural bounds:
    /// frame stack and view have headroom). Impl-defined; probed at runtime.
    spec fn can_seal(&self) -> bool;

    fn can_seal_now(&self) -> (b: bool)
        requires self.wf(),
        ensures b == self.can_seal();

    /// Compress the open hot frame into a cold frame (mode chosen internally,
    /// per frame, from the frame's own statistics) and open a fresh one.
    /// Per-member work with no cross-member dependency: what a parallel group
    /// mark fans out.
    fn seal_frame(&mut self, shrink: ShrinkPolicy)
        requires
            old(self).wf(),
            old(self).can_seal(),
        ensures
            final(self).wf(),
            final(self).depth_spec() == old(self).depth_spec() + 1,
            final(self).can_seal() ==> final(self).depth_spec() < u32::MAX as nat;

    /// Reconstruct this member to its own snapshot at `depth`, applying frames
    /// directly to the live column (`restore_to`; memcpy where contiguous).
    /// What a parallel group restore fans out.
    fn restore_frame(&mut self, depth: usize)
        requires
            old(self).wf(),
            (depth as nat) < old(self).depth_spec(),
        ensures
            final(self).wf(),
            final(self).depth_spec() == depth as nat;

    /// Diagnostic heap footprint (for the shared-vs-per-member measurement).
    fn heap_bytes(&self) -> usize
        requires self.wf();

    /// Diagnostic: sealed (cold) frame count, to observe that a group mark
    /// actually sealed (H1.2) rather than only bumping depths.
    fn cold_frames(&self) -> usize
        requires self.wf();

    /// Diagnostic: order-sensitive content checksum, so a heterogeneous test can
    /// compare a type-erased member against its own typed oracle.
    fn checksum(&self) -> u64
        requires self.wf();

    /// Erased single-cell write (depth-preserving; out-of-range or unrepresentable
    /// values are dropped). What lets a test — or a thin adapter — evolve content
    /// between group marks without a typed handle.
    fn poke(&mut self, i: usize, v: usize)
        requires old(self).wf(),
        ensures
            final(self).wf(),
            final(self).depth_spec() == old(self).depth_spec(),
            final(self).can_seal() == old(self).can_seal();
}

/// Every tracked `Vec` whose element type is itself index-like (ids: the
/// union-find columns, pointer columns, caches keyed by id) is a group member
/// with the full mode set. `T: IndexLike` is what `poke`/`checksum` and the
/// dictionary/delta value layers need; opaque-struct columns join through the
/// `ValueCompressor` design (goal F2) once it lands.
impl<T, I, S, const TRACK: bool, VC> SyncMember for crate::vec::Vec<T, I, S, TRACK, VC>
where
    T: crate::index_like::IndexLike + core::default::Default + Send,
    I: crate::index_like::IndexLike + Send,
    S: crate::diff_store::DiffStore<T, I, TRACK> + Send,
    VC: crate::value_compressor::ValueCompressor<T> + Send,
    VC::Compressed: Send,
{
    open spec fn wf(&self) -> bool {
        &&& crate::vec::Vec::wf(self)
        &&& TRACK
    }

    open spec fn depth_spec(&self) -> nat {
        crate::vec::Vec::depth_spec(self)
    }

    open spec fn can_seal(&self) -> bool {
        &&& crate::vec::Vec::depth_spec(self) < u32::MAX as nat
        &&& crate::vec::Vec::view(self).len() < I::max_nat()
    }

    fn can_seal_now(&self) -> (b: bool) {
        let m = <I as crate::index_like::IndexLike>::max();
        proof {
            I::lemma_max_as_nat();
            // max().as_nat() == max_nat() - 1 and is itself < max_nat(), which also
            // pins max_nat() >= 1 so the truncated subtraction reads exactly.
            m.lemma_as_nat_bounded();
            assert(crate::vec::Vec::view(self).len() == self.store.data().len());
        }
        let depth_ok = self.frames.len() < u32::MAX as usize;
        let len_ok = self.store.raw_len() <= m.as_usize();
        depth_ok && len_ok
    }

    fn seal_frame(&mut self, shrink: ShrinkPolicy) {
        let _ = crate::vec::Vec::seal_frame(self, shrink);
    }

    fn restore_frame(&mut self, depth: usize) {
        crate::vec::Vec::restore_frame(self, depth);
    }

    fn heap_bytes(&self) -> usize {
        self.tracking_bytes()
    }

    fn cold_frames(&self) -> usize {
        self.diff_log.cold_frame_count()
    }

    #[verifier::external_body]
    fn checksum(&self) -> u64 {
        // FNV-1a over (position, value-as-usize); diagnostic only.
        let mut h: u64 = 0xcbf29ce484222325;
        let n = self.store.raw_len();
        let mut i: usize = 0;
        while i < n {
            let idx = I::try_from_usize(i).unwrap();
            let v = self.store.get(idx);
            h ^= i as u64;
            h = h.wrapping_mul(0x100000001b3);
            h ^= v.as_usize() as u64;
            h = h.wrapping_mul(0x100000001b3);
            i += 1;
        }
        h
    }

    fn poke(&mut self, i: usize, v: usize) {
        proof {
            I::lemma_max_as_nat();
            self.store.lemma_wf_captured_len();
        }
        let n = self.store.raw_len();
        // Nested rather than collapsed into a let-chain: Verus rejects let
        // expressions ("does not yet support the following Rust feature: let
        // expressions"), so `clippy::collapsible_if`'s suggestion does not
        // compile here.
        #[allow(clippy::collapsible_if)]
        if i < n {
            if let Some(idx) = I::try_from_usize(i) {
                if let Some(val) = T::try_from_usize(v) {
                    let ghost pre = *self;
                    self.set_index(idx, val);
                    proof {
                        // In-range write: snapshots preserved, and wf ties
                        // snapshots.len to frames.len on both sides, so the depth
                        // is preserved; the view is an update, so its length (and
                        // with it can_seal) is too.
                        assert(idx.as_nat() < pre.view().len());
                        assert(self.snapshots_view() == pre.snapshots_view());
                    }
                }
            }
        }
    }
}

/// The owning fork history: one genealogy, N members, sole mark/restore
/// authority. Standalone use is a group of one.
pub struct ForkHistory {
    pub members: Vec<Box<dyn SyncMember>>,
    pub history: History,
}

impl ForkHistory {
    /// Group invariant: every member's depth equals the shared history's depth.
    /// One token names the whole group's version.
    pub open spec fn wf(&self) -> bool {
        &&& self.history.wf()
        &&& forall|k: int| 0 <= k < self.members@.len()
                ==> (#[trigger] self.members@[k]).wf()
        &&& forall|k: int| 0 <= k < self.members@.len()
                ==> (#[trigger] self.members@[k]).depth_spec() == self.history.depth_spec()
    }

    pub open spec fn depth_spec(&self) -> nat {
        self.history.depth_spec()
    }

    pub fn new() -> (r: ForkHistory)
        ensures r.wf(), r.depth_spec() == 0, r.members@.len() == 0,
    {
        ForkHistory { members: Vec::new(), history: History::new() }
    }

    /// Adopt a member. It must already be at the group's depth (a fresh member
    /// joins a fresh group at depth 0; joining later means catching up first).
    pub fn add_member(&mut self, m: Box<dyn SyncMember>)
        requires
            old(self).wf(),
            m.wf(),
            m.depth_spec() == old(self).depth_spec(),
        ensures
            final(self).wf(),
            final(self).depth_spec() == old(self).depth_spec(),
            final(self).members@.len() == old(self).members@.len() + 1,
    {
        self.members.push(m);
    }

    /// Group mark: ONE stamp write, then every member seals its open frame
    /// (hot-to-cold compression, per-member mode). Returns `None`, changing
    /// nothing, if any member lacks headroom (probed first).
    pub fn mark(&mut self, shrink: ShrinkPolicy) -> (r: Option<GroupToken>)
        requires old(self).wf(),
        ensures
            final(self).wf(),
            final(self).members@.len() == old(self).members@.len(),
            r is Some ==> {
                &&& final(self).depth_spec() == old(self).depth_spec() + 1
                &&& r->Some_0.depth_spec() == old(self).depth_spec()
                &&& final(self).history.valid_spec(r->Some_0)
            },
            r is None ==> final(self).depth_spec() == old(self).depth_spec(),
    {
        // Probe every member's headroom before touching anything.
        let n = self.members.len();
        let mut i: usize = 0;
        let mut ok = self.history.depth() < u32::MAX;
        while i < n
            invariant
                0 <= i <= n,
                n == self.members@.len(),
                self.wf(),
                self == old(self),
                ok ==> self.history.depth_spec() < u32::MAX as nat,
                ok ==> forall|k: int| 0 <= k < i
                    ==> (#[trigger] self.members@[k]).can_seal(),
            decreases n - i,
        {
            if !self.members[i].can_seal_now() {
                ok = false;
            }
            i = i + 1;
        }
        if !ok {
            return None;
        }
        // One genealogy write.
        let t = self.history.mark();
        // Fan out: each member seals. Disjoint &mut borrows; this loop is what
        // mark_parallel runs concurrently.
        let ghost h0 = self.history;
        let ghost target = self.history.depth_spec();
        let mut j: usize = 0;
        while j < n
            invariant
                0 <= j <= n,
                n == self.members@.len(),
                self.history == h0,
                self.history.wf(),
                self.history.depth_spec() == target,
                forall|k: int| 0 <= k < n ==> (#[trigger] self.members@[k]).wf(),
                forall|k: int| 0 <= k < j
                    ==> (#[trigger] self.members@[k]).depth_spec() == target,
                forall|k: int| j <= k < n
                    ==> (#[trigger] self.members@[k]).depth_spec() == target - 1,
                forall|k: int| j <= k < n
                    ==> (#[trigger] self.members@[k]).can_seal(),
            decreases n - j,
        {
            let m = &mut self.members[j];
            m.seal_frame(shrink);
            j = j + 1;
        }
        Some(t)
    }

    /// Group restore: validate ONCE, every member reconstructs (frames applied
    /// straight to its live column), then the branch cut is recorded ONCE.
    /// Returns false, changing nothing, on an invalid or current-depth token.
    pub fn restore(&mut self, t: GroupToken) -> (r: bool)
        requires old(self).wf(),
        ensures
            final(self).wf(),
            final(self).members@.len() == old(self).members@.len(),
            r ==> final(self).depth_spec() == t.depth_spec(),
            !r ==> final(self).depth_spec() == old(self).depth_spec(),
    {
        if !self.history.is_valid(t) {
            return false;
        }
        if !(t.depth < self.history.depth()) {
            return false;
        }
        let n = self.members.len();
        // Fan out: each member reconstructs. This loop is what restore_parallel
        // runs concurrently.
        let ghost pre_depth = self.history.depth_spec();
        let mut j: usize = 0;
        while j < n
            invariant
                0 <= j <= n,
                n == self.members@.len(),
                self.history == old(self).history,
                self.history.wf(),
                self.history.valid_spec(t),
                (t.depth as nat) < self.history.depth_spec(),
                forall|k: int| 0 <= k < n ==> (#[trigger] self.members@[k]).wf(),
                forall|k: int| 0 <= k < j
                    ==> (#[trigger] self.members@[k]).depth_spec() == t.depth as nat,
                forall|k: int| j <= k < n
                    ==> (#[trigger] self.members@[k]).depth_spec() == self.history.depth_spec(),
            decreases n - j,
        {
            let m = &mut self.members[j];
            m.restore_frame(t.depth as usize);
            j = j + 1;
        }
        // One branch-cut record.
        self.history.restore_to(t);
        true
    }

    /// Parallel group mark: identical contract to `mark`. The ONE stamp write and
    /// the headroom probe stay sequential; only the per-member `seal_frame` fan-out
    /// (parallel COMPRESSION: each member encodes its own hot frame) runs on the
    /// rayon pool. Sound because each member owns its store, diff log and frame
    /// stack, so the fanned-out `&mut` borrows are disjoint and the genealogy is
    /// written strictly outside the fan-out. `external_body` covers exactly that
    /// rayon dispatch; the members' contracts are the verified surface, and the
    /// differential test pins parallel == sequential.
    /// Threshold: below `PAR_MEMBER_MIN` members the sequential path runs (fan-out
    /// overhead exceeds the win; H3.5 re-measures the constant).
    #[verifier::external_body]
    pub fn mark_parallel(&mut self, shrink: ShrinkPolicy) -> (r: Option<GroupToken>)
        requires old(self).wf(),
        ensures
            final(self).wf(),
            final(self).members@.len() == old(self).members@.len(),
            r is Some ==> {
                &&& final(self).depth_spec() == old(self).depth_spec() + 1
                &&& r->Some_0.depth_spec() == old(self).depth_spec()
                &&& final(self).history.valid_spec(r->Some_0)
            },
            r is None ==> final(self).depth_spec() == old(self).depth_spec(),
    {
        if self.members.len() < PAR_MEMBER_MIN {
            return self.mark(shrink);
        }
        if !(self.history.depth() < u32::MAX) {
            return None;
        }
        for m in self.members.iter() {
            if !m.can_seal_now() {
                return None;
            }
        }
        let t = self.history.mark();
        {
            use rayon::prelude::*;
            self.members.par_iter_mut().for_each(|m| {
                #[cfg(test)]
                witness_thread();
                m.seal_frame(shrink);
            });
        }
        Some(t)
    }

    /// Parallel group restore: identical contract to `restore`. Token validation
    /// and the branch-cut record stay sequential; only the per-member
    /// `restore_frame` fan-out (parallel DECOMPRESSION straight into each member's
    /// live column, memcpy where frames are contiguous) runs on the rayon pool.
    /// Same disjointness argument as `mark_parallel`.
    #[verifier::external_body]
    pub fn restore_parallel(&mut self, t: GroupToken) -> (r: bool)
        requires old(self).wf(),
        ensures
            final(self).wf(),
            final(self).members@.len() == old(self).members@.len(),
            r ==> final(self).depth_spec() == t.depth_spec(),
            !r ==> final(self).depth_spec() == old(self).depth_spec(),
    {
        if self.members.len() < PAR_MEMBER_MIN {
            return self.restore(t);
        }
        if !self.history.is_valid(t) {
            return false;
        }
        if !(t.depth < self.history.depth()) {
            return false;
        }
        {
            use rayon::prelude::*;
            let depth = t.depth as usize;
            self.members.par_iter_mut().for_each(|m| {
                #[cfg(test)]
                witness_thread();
                m.restore_frame(depth);
            });
        }
        self.history.restore_to(t);
        true
    }

    /// Current group depth (exec).
    pub fn depth(&self) -> (d: u32)
        ensures d as nat == self.depth_spec(),
    {
        self.history.depth()
    }

    /// Total member heap footprint plus the genealogy's own bytes.
    pub fn heap_bytes(&self) -> usize
        requires self.wf(),
    {
        let mut total: usize = 0;
        let n = self.members.len();
        let mut i: usize = 0;
        while i < n
            invariant 0 <= i <= n, n == self.members@.len(), self.wf(),
            decreases n - i,
        {
            let b = self.members[i].heap_bytes();
            // Saturating: diagnostic only.
            total = if usize::MAX - total > b { total + b } else { usize::MAX };
            i = i + 1;
        }
        total
    }
}

} // verus!

/// Below this member count the parallel twins take the sequential path: the rayon
/// dispatch overhead exceeds the win for tiny groups. Initial constant; H3.5
/// re-measures it from the sequential/parallel crossing point.
pub const PAR_MEMBER_MIN: usize = 2;

/// Thread-witness for the H3.2 "actually spawns" check: the parallel fan-outs
/// record which rayon threads ran members, and the test asserts more than one.
#[cfg(test)]
static PAR_THREADS: std::sync::Mutex<Option<std::collections::HashSet<usize>>> =
    std::sync::Mutex::new(None);

#[cfg(test)]
fn witness_thread() {
    let idx = rayon::current_thread_index().unwrap_or(usize::MAX);
    let mut g = PAR_THREADS.lock().unwrap();
    g.get_or_insert_with(std::collections::HashSet::new)
        .insert(idx);
}

#[cfg(test)]
mod fork_history_tests {
    // H1 acceptance: one ForkHistory owns three members of DIFFERENT element/index
    // types behind dyn, is the sole mark/restore authority, its mark actually SEALS
    // every member (cold frame count grows, not just depths), and interleaved
    // mark/poke/restore tracks three independent typed oracles exactly (compared
    // through the same order-sensitive checksum on both sides).
    use super::*;
    use crate::diff_compress::CompressionMode;
    use crate::parallel_store::ParallelStore;
    use crate::vec::Vec as SpVec;

    type V32 = SpVec<u32, u32, ParallelStore<u32, u32>, true>;
    type V64 = SpVec<u64, u64, ParallelStore<u64, u64>, true>;
    type V16 = SpVec<u16, u32, ParallelStore<u16, u32>, true>;

    fn fnv(vals: &[usize]) -> u64 {
        let mut h: u64 = 0xcbf29ce484222325;
        for (i, &v) in vals.iter().enumerate() {
            h ^= i as u64;
            h = h.wrapping_mul(0x100000001b3);
            h ^= v as u64;
            h = h.wrapping_mul(0x100000001b3);
        }
        h
    }

    #[test]
    fn heterogeneous_group_marks_seal_and_restores_track_oracles() {
        const N: usize = 64;
        const FRAMES: usize = 6;

        // Three members of different T/I, preloaded, all Auto (per-frame adaptive).
        let mut m32 = V32::new_with_mode(CompressionMode::Auto);
        let mut m64 = V64::new_with_mode(CompressionMode::Auto);
        let mut m16 = V16::new_with_mode(CompressionMode::Auto);
        for _ in 0..N {
            m32.push(0);
            m64.push(0);
            m16.push(0);
        }
        // Typed oracles: plain std snapshots per depth, per member.
        let mut o32 = vec![0usize; N];
        let mut o64 = vec![0usize; N];
        let mut o16 = vec![0usize; N];
        let mut snaps: Vec<(Vec<usize>, Vec<usize>, Vec<usize>)> = Vec::new();

        let mut g = ForkHistory::new();
        g.add_member(Box::new(m32));
        g.add_member(Box::new(m64));
        g.add_member(Box::new(m16));

        let mut tokens = Vec::new();
        for k in 0..FRAMES {
            let cold_before: usize = (0..3).map(|j| g.members[j].cold_frames()).sum();
            snaps.push((o32.clone(), o64.clone(), o16.clone()));
            let t = g.mark(crate::vec::ShrinkPolicy::Never).expect("headroom");
            tokens.push(t);
            if k > 0 {
                // H1.2: the mark sealed (except the very first, whose frame is empty
                // it still seals an empty frame -> count grows too).
            }
            let cold_after: usize = (0..3).map(|j| g.members[j].cold_frames()).sum();
            assert!(
                cold_after > cold_before || k == 0,
                "group mark {k} did not seal (cold {cold_before} -> {cold_after})"
            );
            // Evolve every member (through the erased write) + the oracles.
            for i in 0..N {
                let v = (i * 7 + k * 13) % 61;
                g.members[0].poke(i, v);
                o32[i] = v;
                g.members[1].poke(i, (v * 3) % 61);
                o64[i] = (v * 3) % 61;
                g.members[2].poke(i, (v * 5) % 61);
                o16[i] = (v * 5) % 61;
            }
            // Contents match the oracles at every step.
            assert_eq!(g.members[0].checksum(), fnv(&o32), "m32 diverged at {k}");
            assert_eq!(g.members[1].checksum(), fnv(&o64), "m64 diverged at {k}");
            assert_eq!(g.members[2].checksum(), fnv(&o16), "m16 diverged at {k}");
        }

        // Deep group restore: all three members land on their own snapshot at
        // depth 2, in lockstep.
        assert!(g.restore(tokens[2]));
        let (s32, s64, s16) = &snaps[2];
        assert_eq!(g.members[0].checksum(), fnv(s32), "m32 wrong after restore");
        assert_eq!(g.members[1].checksum(), fnv(s64), "m64 wrong after restore");
        assert_eq!(g.members[2].checksum(), fnv(s16), "m16 wrong after restore");

        // The abandoned future is invalid; the restored-to token's ancestors work.
        assert!(!g.restore(tokens[4]), "stale token must be rejected");
        assert!(g.restore(tokens[1]));
        let (r32, r64, r16) = &snaps[1];
        assert_eq!(g.members[0].checksum(), fnv(r32));
        assert_eq!(g.members[1].checksum(), fnv(r64));
        assert_eq!(g.members[2].checksum(), fnv(r16));
    }

    // H3: the parallel twins are differential-equal to the sequential path on the
    // same workload (contents, depths, per-member encoded sizes), and the fan-out
    // OBSERVABLY runs on more than one rayon thread.
    #[test]
    fn parallel_twins_match_sequential_and_spawn() {
        const N: usize = 4096;
        const MEMBERS: usize = 8;
        const FRAMES: usize = 5;

        let build = || {
            let mut g = ForkHistory::new();
            for _ in 0..MEMBERS {
                let mut m = V32::new_with_mode(CompressionMode::Auto);
                for _ in 0..N {
                    m.push(0);
                }
                g.add_member(Box::new(m));
            }
            g
        };
        let mut gs = build();
        let mut gp = build();

        let mut ts = Vec::new();
        let mut tp = Vec::new();
        for k in 0..FRAMES {
            ts.push(gs.mark(crate::vec::ShrinkPolicy::Never).expect("seq mark"));
            tp.push(
                gp.mark_parallel(crate::vec::ShrinkPolicy::Never)
                    .expect("par mark"),
            );
            for j in 0..MEMBERS {
                for i in 0..N {
                    let v = (i * 31 + k * 17 + j * 7) % 251;
                    gs.members[j].poke(i, v);
                    gp.members[j].poke(i, v);
                }
            }
            for j in 0..MEMBERS {
                assert_eq!(
                    gs.members[j].checksum(),
                    gp.members[j].checksum(),
                    "member {j} diverged at frame {k}"
                );
            }
        }

        // Parallel restore vs sequential restore to the same depth.
        assert!(gs.restore(ts[1]));
        assert!(gp.restore_parallel(tp[1]));
        assert_eq!(gs.depth(), gp.depth(), "depths diverged");
        for j in 0..MEMBERS {
            assert_eq!(
                gs.members[j].checksum(),
                gp.members[j].checksum(),
                "member {j} diverged after restore"
            );
            assert_eq!(
                gs.members[j].heap_bytes(),
                gp.members[j].heap_bytes(),
                "member {j} encoded size diverged"
            );
        }

        // H3.2: the fan-out actually spawned.
        let seen = super::PAR_THREADS
            .lock()
            .unwrap()
            .clone()
            .unwrap_or_default();
        assert!(
            seen.len() > 1,
            "parallel twins ran on {} thread(s); expected > 1",
            seen.len()
        );
    }

    // H3.5 measurement: sequential vs parallel wall-clock, reported SEPARATELY for
    // mark (compression) and restore (decompression), ten-member group. Run in
    // release for the recorded numbers:
    //   cargo test -p semi-persistent-containers-verus --release \
    //     group_parallel_timing -- --nocapture
    #[test]
    fn group_parallel_timing() {
        const N: usize = 100_000;
        const MEMBERS: usize = 10;
        const FRAMES: usize = 4;

        let build = || {
            let mut g = ForkHistory::new();
            for _ in 0..MEMBERS {
                let mut m = V32::new_with_mode(CompressionMode::Auto);
                for _ in 0..N {
                    m.push(0);
                }
                g.add_member(Box::new(m));
            }
            g
        };
        let drive =
            |g: &mut ForkHistory, parallel: bool| -> (std::time::Duration, std::time::Duration) {
                let mut toks = Vec::new();
                let mut mark_total = std::time::Duration::ZERO;
                for k in 0..FRAMES {
                    let t0 = std::time::Instant::now();
                    let t = if parallel {
                        g.mark_parallel(crate::vec::ShrinkPolicy::Never)
                    } else {
                        g.mark(crate::vec::ShrinkPolicy::Never)
                    }
                    .expect("mark");
                    mark_total += t0.elapsed();
                    toks.push(t);
                    for j in 0..MEMBERS {
                        for i in 0..N {
                            g.members[j].poke(i, (i + k * 3 + j) % 97);
                        }
                    }
                }
                let t1 = std::time::Instant::now();
                let ok = if parallel {
                    g.restore_parallel(toks[0])
                } else {
                    g.restore(toks[0])
                };
                let restore_total = t1.elapsed();
                assert!(ok);
                (mark_total, restore_total)
            };

        let mut gs = build();
        let (seq_mark, seq_restore) = drive(&mut gs, false);
        let mut gp = build();
        let (par_mark, par_restore) = drive(&mut gp, true);

        for j in 0..MEMBERS {
            assert_eq!(gs.members[j].checksum(), gp.members[j].checksum());
        }
        println!(
            "group of {MEMBERS} x {N} cells, {FRAMES} frames:\n  mark    seq {:?}  par {:?}  speedup {:.2}x\n  restore seq {:?}  par {:?}  speedup {:.2}x",
            seq_mark,
            par_mark,
            seq_mark.as_secs_f64() / par_mark.as_secs_f64().max(1e-12),
            seq_restore,
            par_restore,
            seq_restore.as_secs_f64() / par_restore.as_secs_f64().max(1e-12),
        );
    }

    // H4b.3 measurement: peak fork-history bytes, the ONE shared `History`
    // versus the per-member `GenStamps` every column carried before H2. The
    // duplicated side is reconstructed faithfully at runtime: one fresh
    // `GenStamps` per member, driven through the same mark/restore depth
    // trajectory the shared history sees. Run with --nocapture for the
    // recorded numbers.
    #[test]
    fn shared_history_bytes_vs_per_member_duplication() {
        const MEMBERS: usize = 10;
        for &depth in &[128usize, 1024, 4096] {
            let mut shared = crate::history::History::new();
            let mut per_member: Vec<crate::gen_stamps::GenStamps> = (0..MEMBERS)
                .map(|_| crate::gen_stamps::GenStamps::new(0))
                .collect();
            // Drive to `depth`, then a restore-to-half and a re-climb, so the
            // stamp arrays see a branch cut (the workload that grew the old
            // `origins` without bound and that GenStamps holds at O(max depth)).
            let mut toks = Vec::new();
            for _ in 0..depth {
                toks.push(shared.mark());
                for m in per_member.iter_mut() {
                    let d = toks.len() - 1;
                    let _ = m.stamp_at(d);
                }
            }
            let half = toks[depth / 2];
            shared.restore_to(half);
            for m in per_member.iter_mut() {
                m.bump_from(depth / 2 + 1);
            }
            for k in 0..depth / 2 {
                toks.push(shared.mark());
                for m in per_member.iter_mut() {
                    let _ = m.stamp_at(depth / 2 + k);
                }
            }
            let shared_bytes = shared.heap_bytes();
            let dup_bytes: usize = per_member.iter().map(|m| m.heap_bytes()).sum();
            println!(
                "depth {depth}, {MEMBERS} members: shared history {shared_bytes} B, \
                 per-member duplication {dup_bytes} B ({:.1}x)",
                dup_bytes as f64 / shared_bytes.max(1) as f64
            );
            assert_eq!(
                dup_bytes,
                shared_bytes * MEMBERS,
                "the duplicated genealogy is exactly N copies of the shared one"
            );
        }
    }
}
