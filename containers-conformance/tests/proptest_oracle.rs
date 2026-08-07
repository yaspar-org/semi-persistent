// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Three-way property-based conformance: production vs verus vs an independent
//! oracle, over proptest-generated operation programs with shrinking.
//!
//! This is the migration gate. `tests/differential.rs` runs the same containers
//! against fixed seeds, which is a good regression net but a weak search: five
//! hardcoded seeds explore five paths, and a failure reports a 2000-step trace
//! with no indication of which step mattered. Here proptest *searches* the
//! program space and, on failure, shrinks to a minimal counterexample.
//!
//! ## Why a third implementation
//!
//! Two-way differential testing has a blind spot: if production and verus share
//! a misconception, they agree and the test passes. That is not hypothetical
//! here -- verus was ported *from* production, so a semantic misreading is
//! exactly the kind of bug that would be copied rather than caught.
//!
//! The oracle (`oracle::SnapStack`) is therefore written from the *semantics*,
//! not from either implementation: it keeps a plain `Vec<T>` of the current
//! state plus a stack of full deep copies, one per live mark. `mark` pushes a
//! clone; `restore(i)` truncates the stack to `i` and adopts copy `i` wholesale.
//! No diff log, no capture flags, no first-write-wins, no frames -- the entire
//! mechanism the two real implementations share is absent. It is O(n) per mark
//! and would be useless in production, which is the point: it cannot replicate a
//! diff-log bug because it has no diff log.
//!
//! Token validity is modeled the same way, from the fork-tree semantics rather
//! than from `ForkHistory`: the oracle tracks a branch genealogy as an explicit
//! tree of (parent, depth) origins and answers "is this token on the current
//! path within its depth bound", which is the *definition* the verus
//! `fork_valid` spec formalizes.
//!
//! ## What is asserted
//!
//! After **every** operation (not just at the end of a trace):
//!   - `len` agrees across all three;
//!   - the full element sequence agrees across all three (a complete sweep,
//!     so a wrong element anywhere is caught at the step that wrote it, not
//!     hundreds of steps later);
//!   - `depth` agrees between prod and verus;
//!   - `is_valid_token` matches the oracle for every token ever issued, live or
//!     stale -- the verdict differential -- with each implementation checked
//!     against *its own* documented meaning. The two meanings differ on purpose:
//!     verus's is "restorable now" (frame liveness AND genealogy), production's
//!     is genealogy only, with a consumed token trapped structurally inside
//!     `restore` instead. The oracle models both (`is_restorable` / `on_branch`)
//!     so neither side is held to the other's contract, and the two are asserted
//!     to agree on the tokens where the contracts do coincide. Stale tokens are
//!     checked *before* any mutation is attempted, so a wrongly-accepted token
//!     is caught by the verdict rather than by a panic.
//!
//! ## Configuration matrix
//!
//! `differential.rs` pins `TRACK=true` and `ShrinkPolicy::Never`. Here both
//! shrink policies are generated (verus proves shrink observably inert; this
//! checks production agrees), `TRACK=false` gets its own no-tracking property,
//! and the index/id widths are instantiated at u32 and u64 (`DenseId31` /
//! `DenseId63` for the id-keyed containers) so the niche-packing boundaries are
//! exercised rather than assumed.
//!
//! Restores deliberately target *arbitrary* live marks, not just the newest, so
//! restore-to-ancestor cuts a branch and invalidates a suffix of tokens -- the
//! case where the fork-history genealogy actually does work.

use proptest::prelude::*;
use semi_persistent_containers as prod;
use semi_persistent_containers_verus as verus;

// ---------------------------------------------------------------------------
// The independent oracle
// ---------------------------------------------------------------------------

mod oracle {
    /// A branch origin in the fork tree: which branch we forked from, and at
    /// what depth the fork happened.
    #[derive(Clone, Copy, Debug)]
    struct Origin {
        parent: u32,
        depth: u32,
    }

    /// A token as the oracle sees it: a (branch, depth, frame) coordinate.
    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub struct Tok {
        pub branch: u32,
        pub depth: u32,
        pub frame: u32,
    }

    /// Semi-persistence by brute force: the current state plus one full deep
    /// copy per live mark.
    ///
    /// Generic over the state `S` so that ONE genealogy implementation serves
    /// every container -- `S = Vec<u32>` for the vectors, `Vec<(u32, u32)>` for
    /// the map's log, `BTreeMap<u32, u32>` for the sparse set. Per-container
    /// frame bookkeeping was tried first and got the branch-cut case wrong
    /// (frame *indices are reused* after a cut, so "find the token with this
    /// frame index" can find a stale token from the abandoned branch); the
    /// genealogy is subtle enough to be worth writing exactly once.
    ///
    /// Shares no mechanism with either real implementation -- that independence
    /// is the whole value. `restore` here is "throw the current state away and
    /// adopt the saved copy", which is the *meaning* of restore; the real
    /// implementations reconstruct that same state by replaying a diff log
    /// backwards, and this is what says they got it right.
    #[derive(Clone, Debug)]
    pub struct SnapStack<S: Clone + std::fmt::Debug> {
        pub cur: S,
        snaps: Vec<S>,
        // Fork genealogy, modeled from the semantics rather than from
        // `ForkHistory`: origins[b-1] is where branch b came from.
        cur_branch: u32,
        origins: Vec<Origin>,
    }

    impl<S: Clone + std::fmt::Debug + Default> SnapStack<S> {
        pub fn new() -> Self {
            Self {
                cur: S::default(),
                snaps: Vec::new(),
                cur_branch: 0,
                origins: Vec::new(),
            }
        }
    }

    impl<S: Clone + std::fmt::Debug> SnapStack<S> {
        pub fn depth(&self) -> usize {
            self.snaps.len()
        }

        /// Snapshot: a full clone. O(n), deliberately.
        pub fn mark(&mut self) -> Tok {
            let t = Tok {
                branch: self.cur_branch,
                depth: self.snaps.len() as u32,
                frame: self.snaps.len() as u32,
            };
            self.snaps.push(self.cur.clone());
            t
        }

        /// Adopt snapshot `t.frame` wholesale and fork the branch.
        ///
        /// Forking on restore is what makes tokens for the abandoned future
        /// invalid: the state we just discarded is unreachable, so any token
        /// that pointed into it must stop validating.
        pub fn restore(&mut self, t: Tok) {
            let idx = t.frame as usize;
            assert!(idx < self.snaps.len(), "oracle: token beyond frame stack");
            self.cur = self.snaps[idx].clone();
            self.snaps.truncate(idx);
            self.origins.push(Origin {
                parent: t.branch,
                depth: t.depth,
            });
            self.cur_branch = self.origins.len() as u32;
        }

        /// Restorable now: the frame is still live AND the token's branch is on
        /// the current path within its depth bound. This is the *verus*
        /// `is_valid_token` meaning.
        ///
        /// Frame liveness is a separate condition from genealogy: a consumed
        /// token's branch can still be on-path while its frame is gone. That
        /// gap is exactly where the two implementations' `is_valid_token`
        /// deliberately differ -- see `on_branch` below.
        pub fn is_restorable(&self, t: Tok) -> bool {
            if (t.frame as usize) >= self.snaps.len() {
                return false;
            }
            self.on_current_path(t)
        }

        /// Genealogy only, ignoring frame liveness. This is the *production*
        /// `is_valid_token` meaning.
        ///
        /// The two notions are intentionally different (migration plan phase
        /// 2.2: the verus meaning "strengthens to restorable-now"). Production
        /// answers "is this token's branch on the current path", and catches a
        /// consumed token structurally instead -- `restore` asserts
        /// `frame_index < frames.len()`, so reusing a token traps in `restore`
        /// rather than being reported by `is_valid_token`. See
        /// `containers-verus/doc/design/08-token-reuse-and-restore.md` section 3.
        ///
        /// Modeling both notions is what lets this harness assert each
        /// implementation against its own contract, and separately assert that
        /// the two agree wherever their contracts agree.
        pub fn on_branch(&self, t: Tok) -> bool {
            self.on_current_path(t)
        }

        /// Pick a token that is restorable *right now*, from a list of every
        /// token ever issued, scaling `ratio` over the live ones.
        ///
        /// Every container's `Restore` arm goes through this. Selecting a
        /// restore target is the one place the branch-cut semantics bite: frame
        /// indices are reused after a cut, so filtering by frame index (rather
        /// than by full genealogy) can pick a token from an abandoned branch
        /// that the implementations correctly reject. Centralizing it means that
        /// mistake can only be made once.
        pub fn pick_restorable(&self, toks: &[Tok], ratio: u16) -> Option<usize> {
            let live: Vec<usize> = (0..toks.len())
                .filter(|&i| self.is_restorable(toks[i]))
                .collect();
            if live.is_empty() {
                return None;
            }
            Some(live[super::scale(ratio, live.len()).unwrap()])
        }

        /// Walk from the current branch toward the root looking for the token's
        /// branch. If we reach it, the token is on our ancestry and is valid up
        /// to the depth at which we forked away from it.
        fn on_current_path(&self, t: Tok) -> bool {
            let cur_depth = self.snaps.len() as u32;
            if t.branch == self.cur_branch {
                return t.depth <= cur_depth;
            }
            let mut b = self.cur_branch;
            while b != t.branch {
                if b == 0 {
                    return false; // hit the root without finding it: cut branch
                }
                let o = self.origins[(b - 1) as usize];
                if o.parent == t.branch {
                    return t.depth <= o.depth;
                }
                b = o.parent;
            }
            t.depth <= cur_depth
        }
    }

    /// Sequence-shaped state: the element accessors the vector properties use.
    impl<T: Clone + std::fmt::Debug> SnapStack<Vec<T>> {
        pub fn len(&self) -> usize {
            self.cur.len()
        }
        pub fn push(&mut self, v: T) {
            self.cur.push(v);
        }
        pub fn pop(&mut self) -> Option<T> {
            self.cur.pop()
        }
        pub fn set(&mut self, i: usize, v: T) {
            self.cur[i] = v;
        }
        pub fn get(&self, i: usize) -> &T {
            &self.cur[i]
        }
    }
}

use oracle::SnapStack;

// ---------------------------------------------------------------------------
// Generated programs
// ---------------------------------------------------------------------------

/// One step of a generated program. Indices are generated as fractions of the
/// live length (`Set`/`Get` carry a 0..=u16::MAX ratio, scaled at execution
/// time) because absolute indices would almost always be out of bounds once
/// restores start shrinking the container.
#[derive(Clone, Copy, Debug)]
enum Op {
    Push(u32),
    Pop,
    Set {
        at: u16,
        val: u32,
    },
    Get {
        at: u16,
    },
    /// `shrink` picks the policy, exercising both variants.
    Mark {
        shrink: bool,
    },
    /// Restore to an *arbitrary* live mark (`which` scaled over live marks),
    /// so restore-to-ancestor and its branch cut are covered.
    Restore {
        which: u16,
    },
}

fn op_strategy() -> impl Strategy<Value = Op> {
    prop_oneof![
        6 => any::<u32>().prop_map(Op::Push),
        2 => Just(Op::Pop),
        4 => (any::<u16>(), any::<u32>()).prop_map(|(at, val)| Op::Set { at, val }),
        2 => any::<u16>().prop_map(|at| Op::Get { at }),
        2 => any::<bool>().prop_map(|shrink| Op::Mark { shrink }),
        2 => any::<u16>().prop_map(|which| Op::Restore { which }),
    ]
}

fn program() -> impl Strategy<Value = Vec<Op>> {
    prop::collection::vec(op_strategy(), 1..300)
}

/// Scale a generated ratio onto `0..n`. Returns `None` when `n == 0`.
fn scale(ratio: u16, n: usize) -> Option<usize> {
    if n == 0 {
        None
    } else {
        Some((ratio as usize * n) / (u16::MAX as usize + 1))
    }
}

/// Case count, overridable with `PROPTEST_CASES` for deep/nightly runs.
///
/// `ProptestConfig::default()` already reads `PROPTEST_CASES`, but naming
/// `cases:` explicitly in a config literal *overrides* it -- so a
/// `PROPTEST_CASES=4000` run would silently still do 256 and look like a pass.
/// Reading the env var here keeps the local default cheap while letting CI turn
/// the search depth up for real.
fn cases() -> u32 {
    std::env::var("PROPTEST_CASES")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(256)
}

fn config() -> ProptestConfig {
    ProptestConfig {
        cases: cases(),
        ..ProptestConfig::default()
    }
}

fn policy(shrink: bool) -> (prod::ShrinkPolicy, verus::vec::ShrinkPolicy) {
    if shrink {
        (
            prod::ShrinkPolicy::IfOverallocated {
                factor: 2,
                headroom: 1,
            },
            verus::vec::ShrinkPolicy::IfOverallocated {
                factor: 2,
                headroom: 1,
            },
        )
    } else {
        (prod::ShrinkPolicy::Never, verus::vec::ShrinkPolicy::Never)
    }
}

// ---------------------------------------------------------------------------
// Vec: the full three-way check, both stores, both index widths
// ---------------------------------------------------------------------------

/// Every token ever issued, paired across the three implementations, kept
/// forever (never pruned) so stale tokens keep being checked after the branch
/// cut that invalidated them.
type Toks = Vec<(prod::VecToken, verus::vec::VecToken, oracle::Tok)>;

macro_rules! vec_property {
    ($name:ident, $prod:ty, $verus:ty, $ix:ty) => {
        fn $name(ops: &[Op]) -> Result<(), TestCaseError> {
            let mut p: $prod = <$prod>::new();
            let mut v: $verus = <$verus>::new();
            let mut o: SnapStack<Vec<u32>> = SnapStack::new();
            let mut toks: Toks = Vec::new();

            for (step, op) in ops.iter().enumerate() {
                match *op {
                    Op::Push(val) => {
                        p.push(val);
                        v.push(val);
                        o.push(val);
                    }
                    Op::Pop => {
                        let gp = p.pop();
                        let gv = v.pop();
                        let go = o.pop();
                        prop_assert_eq!(gp, gv, "step {}: prod/verus pop diverged", step);
                        prop_assert_eq!(gp, go, "step {}: prod/oracle pop diverged", step);
                    }
                    Op::Set { at, val } => {
                        if let Some(i) = scale(at, o.len()) {
                            p.set(i as $ix, val);
                            v.set(i as $ix, val);
                            o.set(i, val);
                        }
                    }
                    Op::Get { at } => {
                        if let Some(i) = scale(at, o.len()) {
                            let gp = p.get(i as $ix);
                            let gv = v.get(i as $ix);
                            prop_assert_eq!(gp, gv, "step {}: prod/verus get diverged", step);
                            prop_assert_eq!(
                                &gp,
                                o.get(i),
                                "step {}: prod/oracle get diverged",
                                step
                            );
                        }
                    }
                    Op::Mark { shrink } => {
                        // Bound the frame stack: unbounded marks would make the
                        // O(n)-per-mark oracle the bottleneck, not the test.
                        if o.depth() >= 8 {
                            continue;
                        }
                        let (pp, vp) = policy(shrink);
                        let tp = p.mark(pp);
                        let tv = v.mark(vp);
                        let to = o.mark();
                        toks.push((tp, tv, to));
                    }
                    Op::Restore { which } => {
                        // Restore needs a LIVE frame. Collect the tokens the
                        // oracle still considers restorable and pick among
                        // those, so the mutating path stays in-contract; the
                        // stale ones are covered by the verdict sweep below.
                        let all: Vec<oracle::Tok> = toks.iter().map(|t| t.2).collect();
                        let Some(pick) = o.pick_restorable(&all, which) else {
                            continue;
                        };
                        let (tp, tv, to) = toks[pick];

                        // Both implementations must AGREE this is restorable
                        // before we mutate: an implementation that wrongly
                        // rejects here is a bug we want reported as a verdict
                        // mismatch, not as a panic inside restore.
                        prop_assert!(
                            p.is_valid_token(&tp),
                            "step {}: prod rejects a token the oracle deems live",
                            step
                        );
                        prop_assert!(
                            v.is_valid_token(&tv),
                            "step {}: verus rejects a token the oracle deems live",
                            step
                        );

                        p.restore(tp);
                        v.restore(tv);
                        o.restore(to);
                    }
                }

                // ---- full-state agreement, after EVERY op ----
                let lp = p.len() as usize;
                let lv = v.len() as usize;
                prop_assert_eq!(lp, lv, "step {}: prod/verus len diverged", step);
                prop_assert_eq!(lp, o.len(), "step {}: prod/oracle len diverged", step);
                prop_assert_eq!(
                    p.depth(),
                    v.depth(),
                    "step {}: prod/verus depth diverged",
                    step
                );
                prop_assert_eq!(
                    p.depth(),
                    o.depth(),
                    "step {}: prod/oracle depth diverged",
                    step
                );

                for i in 0..o.len() {
                    let ep = p.get(i as $ix);
                    let ev = v.get(i as $ix);
                    prop_assert_eq!(ep, ev, "step {}: prod/verus element {} diverged", step, i);
                    prop_assert_eq!(
                        &ep,
                        o.get(i),
                        "step {}: prod/oracle element {} diverged",
                        step,
                        i
                    );
                }

                // ---- token verdict differential, over ALL tokens ever ----
                // Includes tokens invalidated by an earlier branch cut: the
                // interesting direction is a stale token being wrongly accepted.
                //
                // Each side is held to its own documented meaning (see the
                // oracle's `is_restorable` / `on_branch`), and the two are
                // asserted to agree wherever the meanings coincide -- which is
                // every token whose frame is still live.
                for (j, (tp, tv, to)) in toks.iter().enumerate() {
                    let vp = p.is_valid_token(tp);
                    let vv = v.is_valid_token(tv);
                    prop_assert_eq!(
                        vp,
                        o.on_branch(*to),
                        "step {}: token {} prod validity={} vs oracle on-branch",
                        step,
                        j,
                        vp
                    );
                    prop_assert_eq!(
                        vv,
                        o.is_restorable(*to),
                        "step {}: token {} verus validity={} vs oracle restorable",
                        step,
                        j,
                        vv
                    );
                    // Where the contracts coincide (live frame), they must agree.
                    if o.is_restorable(*to) {
                        prop_assert_eq!(
                            vp,
                            vv,
                            "step {}: token {} restorable but prod={} verus={}",
                            step,
                            j,
                            vp,
                            vv
                        );
                    }
                }
            }
            Ok(())
        }
    };
}

type PVecI32 = prod::VecI<u32, u32, true>;
type VVecI32 = verus::vec::Vec<u32, u32, verus::inline_store::InlineStore<u32, u32>, true>;
vec_property!(check_vec_inline_u32, PVecI32, VVecI32, u32);

type PVecP32 = prod::VecP<u32, u32, true>;
type VVecP32 = verus::vec::Vec<u32, u32, verus::parallel_store::ParallelStore<u32, u32>, true>;
vec_property!(check_vec_parallel_u32, PVecP32, VVecP32, u32);

// u64 index width: different niche/packing boundary than u32.
type PVecI64 = prod::VecI<u32, u64, true>;
type VVecI64 = verus::vec::Vec<u32, u64, verus::inline_store::InlineStore<u32, u64>, true>;
vec_property!(check_vec_inline_u64, PVecI64, VVecI64, u64);

type PVecP64 = prod::VecP<u32, u64, true>;
type VVecP64 = verus::vec::Vec<u32, u64, verus::parallel_store::ParallelStore<u32, u64>, true>;
vec_property!(check_vec_parallel_u64, PVecP64, VVecP64, u64);

proptest! {
    #![proptest_config(config())]

    #[test]
    fn prop_vec_inline_u32(ops in program()) {
        check_vec_inline_u32(&ops)?;
    }

    #[test]
    fn prop_vec_parallel_u32(ops in program()) {
        check_vec_parallel_u32(&ops)?;
    }

    #[test]
    fn prop_vec_inline_u64(ops in program()) {
        check_vec_inline_u64(&ops)?;
    }

    #[test]
    fn prop_vec_parallel_u64(ops in program()) {
        check_vec_parallel_u64(&ops)?;
    }
}

// ---------------------------------------------------------------------------
// TRACK = false: the erasure must be observationally invisible
// ---------------------------------------------------------------------------

/// With `TRACK=false` the tracking machinery is monomorphized away and
/// mark/restore are not callable, so the container must behave as a plain
/// `Vec` -- which is exactly what the oracle's `cur` field is. No frames, no
/// tokens; just: does erasure change any observable answer?
#[derive(Clone, Copy, Debug)]
enum PlainOp {
    Push(u32),
    Pop,
    Set { at: u16, val: u32 },
}

proptest! {
    #![proptest_config(config())]

    #[test]
    fn prop_vec_untracked_matches_plain_vec(
        ops in prop::collection::vec(
            prop_oneof![
                6 => any::<u32>().prop_map(PlainOp::Push),
                2 => Just(PlainOp::Pop),
                4 => (any::<u16>(), any::<u32>()).prop_map(|(at, val)| PlainOp::Set { at, val }),
            ],
            1..300,
        )
    ) {
        type P = prod::VecI<u32, u32, false>;
        type V = verus::vec::Vec<u32, u32, verus::inline_store::InlineStore<u32, u32>, false>;
        let mut p: P = P::new();
        let mut v: V = V::new();
        let mut plain: Vec<u32> = Vec::new();

        for (step, op) in ops.iter().enumerate() {
            match *op {
                PlainOp::Push(val) => {
                    p.push(val);
                    v.push_untracked(val);
                    plain.push(val);
                }
                PlainOp::Pop => {
                    let gp = p.pop();
                    let gv = v.pop_untracked();
                    let go = plain.pop();
                    prop_assert_eq!(gp, gv, "step {}: untracked pop prod/verus diverged", step);
                    prop_assert_eq!(gp, go, "step {}: untracked pop prod/plain diverged", step);
                }
                PlainOp::Set { at, val } => {
                    if let Some(i) = scale(at, plain.len()) {
                        p.set(i as u32, val);
                        v.set_untracked(i as u32, val);
                        plain[i] = val;
                    }
                }
            }
            prop_assert_eq!(p.len() as usize, v.len() as usize, "step {}: untracked len", step);
            prop_assert_eq!(p.len() as usize, plain.len(), "step {}: untracked len vs plain", step);
            for (i, &want) in plain.iter().enumerate() {
                let ep = p.get(i as u32);
                let ev = v.get(i as u32);
                prop_assert_eq!(ep, ev, "step {}: untracked element {}", step, i);
                prop_assert_eq!(ep, want, "step {}: untracked element {} vs plain", step, i);
            }
            // Erasure must also be invisible in the memory accounting: with
            // TRACK=false there is nothing to track.
            prop_assert_eq!(p.tracking_bytes(), 0, "step {}: prod tracks under TRACK=false", step);
            prop_assert_eq!(v.tracking_bytes(), 0, "step {}: verus tracks under TRACK=false", step);
        }
    }
}

// ---------------------------------------------------------------------------
// AppendOnlyVec
// ---------------------------------------------------------------------------

/// Append-only: no `set`, no `pop`. `restore` truncates back to the marked
/// length, so the oracle is a plain length-truncation -- an even weaker (hence
/// more independent) model than `SnapStack`.
#[derive(Clone, Copy, Debug)]
enum AovOp {
    Push(u32),
    Mark { shrink: bool },
    Restore { which: u16 },
}

proptest! {
    #![proptest_config(config())]

    #[test]
    fn prop_append_only_vec(
        ops in prop::collection::vec(
            prop_oneof![
                6 => any::<u32>().prop_map(AovOp::Push),
                2 => any::<bool>().prop_map(|shrink| AovOp::Mark { shrink }),
                2 => any::<u16>().prop_map(|which| AovOp::Restore { which }),
            ],
            1..300,
        )
    ) {
        let mut p: prod::AppendOnlyVec<u32, true> = prod::AppendOnlyVec::new();
        let mut v: verus::AppendOnlyVec<u32, true> = verus::AppendOnlyVec::new();
        let mut o: SnapStack<Vec<u32>> = SnapStack::new();
        let mut toks: Vec<(prod::VecToken, verus::vec::VecToken, oracle::Tok)> = Vec::new();

        for (step, op) in ops.iter().enumerate() {
            match *op {
                AovOp::Push(val) => {
                    let ip = p.push(val);
                    let iv = v.push(val);
                    prop_assert_eq!(ip, iv, "step {}: push index diverged", step);
                    prop_assert_eq!(ip, o.len(), "step {}: push index vs oracle", step);
                    o.push(val);
                }
                AovOp::Mark { shrink } => {
                    if o.depth() >= 8 { continue; }
                    let (pp, vp) = policy(shrink);
                    let tp = p.mark(pp);
                    let tv = v.mark(vp);
                    let to = o.mark();
                    toks.push((tp, tv, to));
                }
                AovOp::Restore { which } => {
                    let all: Vec<oracle::Tok> = toks.iter().map(|t| t.2).collect();
                    let Some(pick) = o.pick_restorable(&all, which) else { continue };
                    let (tp, tv, to) = toks[pick];
                    prop_assert!(p.is_valid_token(&tp), "step {}: prod rejects live token", step);
                    prop_assert!(v.is_valid_token(&tv), "step {}: verus rejects live token", step);
                    p.restore(tp);
                    v.restore(tv);
                    o.restore(to);
                }
            }

            prop_assert_eq!(p.len(), v.len(), "step {}: aov len diverged", step);
            prop_assert_eq!(p.len(), o.len(), "step {}: aov len vs oracle", step);
            prop_assert_eq!(p.depth(), v.depth(), "step {}: aov depth diverged", step);
            prop_assert_eq!(p.as_slice(), v.as_slice(), "step {}: aov slice diverged", step);
            for i in 0..o.len() {
                prop_assert_eq!(p.get(i), o.get(i), "step {}: aov element {} vs oracle", step, i);
            }
            for (j, (tp, tv, to)) in toks.iter().enumerate() {
                let vp = p.is_valid_token(tp);
                let vv = v.is_valid_token(tv);
                prop_assert_eq!(
                    vp, o.on_branch(*to),
                    "step {}: aov token {} prod validity vs oracle on-branch", step, j
                );
                prop_assert_eq!(
                    vv, o.is_restorable(*to),
                    "step {}: aov token {} verus validity vs oracle restorable", step, j
                );
                if o.is_restorable(*to) {
                    prop_assert_eq!(vp, vv, "step {}: aov token {} restorable disagreement", step, j);
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// SpMap vs production Map
// ---------------------------------------------------------------------------

/// The map's oracle is a `Vec<(K, V)>` log plus linear search, mirroring the
/// *specified* semantics (last occurrence of a key wins, ids are log positions)
/// with no hash index at all. Since the real implementations' index is a
/// transient accelerator rebuilt on restore, an oracle with no index is exactly
/// the right cross-check: it cannot share an index-rebuild bug.
#[derive(Clone, Copy, Debug)]
enum MapOp {
    Insert { key: u16, val: u32 },
    IdOf { key: u16 },
    Contains { key: u16 },
    Mark { shrink: bool },
    Restore { which: u16 },
}

/// Last occurrence of `k` in a log, scanning backwards. This is the map's
/// specified `id_of` semantics, stated without a hash index.
fn oracle_id_of(log: &[(u32, u32)], k: u32) -> Option<usize> {
    (0..log.len()).rev().find(|&i| log[i].0 == k)
}

proptest! {
    #![proptest_config(config())]

    #[test]
    fn prop_map(
        ops in prop::collection::vec(
            prop_oneof![
                6 => (any::<u16>(), any::<u32>()).prop_map(|(key, val)| MapOp::Insert { key, val }),
                3 => any::<u16>().prop_map(|key| MapOp::IdOf { key }),
                2 => any::<u16>().prop_map(|key| MapOp::Contains { key }),
                2 => any::<bool>().prop_map(|shrink| MapOp::Mark { shrink }),
                2 => any::<u16>().prop_map(|which| MapOp::Restore { which }),
            ],
            1..300,
        )
    ) {
        // Narrow the key domain hard: repeated keys are the interesting case
        // (they make `id_of` depend on last-occurrence, and make the index
        // rebuild after restore observable).
        const KEYS: u32 = 24;

        let mut p: prod::Map<u32, u32, true> = prod::Map::new();
        let mut v: verus::SpMap<u32, u32, true> = verus::SpMap::new();
        // Same genealogy model as the vectors, over the map's log as the state.
        let mut o: SnapStack<Vec<(u32, u32)>> = SnapStack::new();
        let mut toks: Vec<(prod::MapToken, verus::map::MapToken, oracle::Tok)> = Vec::new();

        for (step, op) in ops.iter().enumerate() {
            match *op {
                MapOp::Insert { key, val } => {
                    let k = key as u32 % KEYS;
                    let ip = p.insert(k, val);
                    let iv = v.insert(k, val);
                    o.cur.push((k, val));
                    let io = o.cur.len() - 1;
                    prop_assert_eq!(ip, iv, "step {}: insert id prod/verus diverged", step);
                    prop_assert_eq!(ip, io, "step {}: insert id prod/oracle diverged", step);
                }
                MapOp::IdOf { key } => {
                    let k = key as u32 % KEYS;
                    let gp = p.id_of(&k);
                    let gv = v.id_of(&k);
                    let go = oracle_id_of(&o.cur, k);
                    prop_assert_eq!(gp, gv, "step {}: id_of prod/verus diverged", step);
                    prop_assert_eq!(gp, go, "step {}: id_of prod/oracle diverged", step);
                }
                MapOp::Contains { key } => {
                    let k = key as u32 % KEYS;
                    let gp = p.contains_key(&k);
                    let gv = v.contains_key(&k);
                    prop_assert_eq!(gp, gv, "step {}: contains prod/verus diverged", step);
                    prop_assert_eq!(
                        gp, oracle_id_of(&o.cur, k).is_some(),
                        "step {}: contains prod/oracle diverged", step
                    );
                }
                MapOp::Mark { shrink } => {
                    if o.depth() >= 8 { continue; }
                    let (pp, vp) = policy(shrink);
                    let tp = p.mark(pp);
                    let tv = v.mark(vp);
                    let to = o.mark();
                    toks.push((tp, tv, to));
                }
                MapOp::Restore { which } => {
                    let all: Vec<oracle::Tok> = toks.iter().map(|t| t.2).collect();
                    let Some(pick) = o.pick_restorable(&all, which) else { continue };
                    let (tp, tv, to) = toks[pick];
                    prop_assert!(p.is_valid_token(&tp), "step {}: prod rejects live map token", step);
                    prop_assert!(v.is_valid_token(&tv), "step {}: verus rejects live map token", step);
                    p.restore(tp);
                    v.restore(tv);
                    o.restore(to);
                }
            }

            prop_assert_eq!(p.log_len(), v.log_len(), "step {}: log_len diverged", step);
            prop_assert_eq!(p.log_len(), o.cur.len(), "step {}: log_len vs oracle", step);
            prop_assert_eq!(p.depth(), v.depth(), "step {}: map depth diverged", step);
            prop_assert_eq!(p.depth(), o.depth(), "step {}: map depth vs oracle", step);

            // Sweep the whole key domain: an index left stale by a restore
            // shows up here as a wrong id_of for some key, at the step it broke.
            for k in 0..KEYS {
                let gp = p.id_of(&k);
                let gv = v.id_of(&k);
                prop_assert_eq!(gp, gv, "step {}: key {} id_of prod/verus diverged", step, k);
                prop_assert_eq!(
                    gp, oracle_id_of(&o.cur, k),
                    "step {}: key {} id_of vs oracle", step, k
                );
            }
            // And the log itself, entry by entry.
            for i in 0..o.cur.len() {
                prop_assert_eq!(*p.key(i), o.cur[i].0, "step {}: log key {} vs oracle", step, i);
                prop_assert_eq!(*v.key(i), o.cur[i].0, "step {}: verus log key {} vs oracle", step, i);
                // Production spells the value accessor `get`; under the verus
                // names `get` returns the pair and `get_val` the value. This is
                // the one recorded map interface divergence (plan 5.1-5.3), so
                // each side is called by its own name.
                prop_assert_eq!(*p.get(i), o.cur[i].1, "step {}: log val {} vs oracle", step, i);
                prop_assert_eq!(*v.get_val(i), o.cur[i].1, "step {}: verus log val {} vs oracle", step, i);
            }
            for (j, (tp, tv, to)) in toks.iter().enumerate() {
                let vp = p.is_valid_token(tp);
                let vv = v.is_valid_token(tv);
                prop_assert_eq!(
                    vp, o.on_branch(*to),
                    "step {}: map token {} prod validity vs oracle on-branch", step, j
                );
                prop_assert_eq!(
                    vv, o.is_restorable(*to),
                    "step {}: map token {} verus validity vs oracle restorable", step, j
                );
                if o.is_restorable(*to) {
                    prop_assert_eq!(vp, vv, "step {}: map token {} restorable disagreement", step, j);
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// SparseSet
// ---------------------------------------------------------------------------

/// SparseSet's oracle is the abstract thing a sparse set *is*: a map from live
/// id to value, plus a free-id pool.
///
/// It deliberately does NOT model the dense array, the sparse array, the
/// swap-remove, or the id-recycling order -- those are the mechanism, and the
/// mechanism is what is under test. What it does pin down is the abstract
/// contract: `add` returns an id that was not live and is now live, `remove`
/// makes exactly that id not live, `get(id)` returns what was stored under
/// `id`, and ids stay stable across unrelated operations (the property a plain
/// `Vec` index does *not* have, and the reason a sparse set exists).
///
/// Because ids are recycled, the harness never assumes `id == position`; it
/// tracks the live ids it was handed and only ever queries those.
#[derive(Clone, Copy, Debug)]
enum SetOp {
    Add(u32),
    /// Remove a live id, chosen among the ids the oracle knows are live.
    Remove {
        which: u16,
    },
    Get {
        which: u16,
    },
    Mark {
        shrink: bool,
    },
    Restore {
        which: u16,
    },
}

proptest! {
    #![proptest_config(config())]

    #[test]
    fn prop_sparse_set(
        ops in prop::collection::vec(
            prop_oneof![
                6 => any::<u32>().prop_map(SetOp::Add),
                3 => any::<u16>().prop_map(|which| SetOp::Remove { which }),
                2 => any::<u16>().prop_map(|which| SetOp::Get { which }),
                2 => any::<bool>().prop_map(|shrink| SetOp::Mark { shrink }),
                2 => any::<u16>().prop_map(|which| SetOp::Restore { which }),
            ],
            1..200,
        )
    ) {
        let mut p: prod::SparseSet<u32, u32, prod::ParallelStore<u32, u32>, true> =
            prod::SparseSet::new();
        let mut v: verus::SparseSet<u32, u32, verus::ParallelStore<u32, u32>, true> =
            verus::SparseSet::new();
        // Oracle: live id -> value, under the same genealogy model as the other
        // containers. No dense array, no swap-remove, no pool order. BTreeMap
        // (not HashMap) so `which` picks deterministically.
        let mut o: SnapStack<std::collections::BTreeMap<u32, u32>> = SnapStack::new();
        let mut toks: Vec<(prod::SparseSetToken, verus::SparseSetToken, oracle::Tok)> = Vec::new();

        for (step, op) in ops.iter().enumerate() {
            match *op {
                SetOp::Add(val) => {
                    let ip = p.add(val);
                    let iv = v.add(val);
                    // Both must hand out the SAME id: id allocation (including
                    // which id the free pool recycles) is observable, so it is
                    // part of the parity surface even though the oracle does
                    // not predict which id that will be.
                    prop_assert_eq!(ip, iv, "step {}: add id diverged", step);
                    // Abstract contract: the id was not live, and now is.
                    prop_assert!(!o.cur.contains_key(&ip), "step {}: add reissued live id {}", step, ip);
                    o.cur.insert(ip, val);
                }
                SetOp::Remove { which } => {
                    let ids: Vec<u32> = o.cur.keys().copied().collect();
                    if let Some(i) = scale(which, ids.len()) {
                        let id = ids[i];
                        p.remove(id);
                        v.remove(id);
                        o.cur.remove(&id);
                    }
                }
                SetOp::Get { which } => {
                    let ids: Vec<u32> = o.cur.keys().copied().collect();
                    if let Some(i) = scale(which, ids.len()) {
                        let id = ids[i];
                        let gp = p.get(id);
                        let gv = v.get(id);
                        prop_assert_eq!(gp, gv, "step {}: sparse get diverged", step);
                        prop_assert_eq!(gp, o.cur[&id], "step {}: sparse get vs oracle", step);
                    }
                }
                SetOp::Mark { shrink } => {
                    if o.depth() >= 8 { continue; }
                    let (pp, vp) = policy(shrink);
                    let tp = p.mark(pp);
                    let tv = v.mark(vp);
                    let to = o.mark();
                    toks.push((tp, tv, to));
                }
                SetOp::Restore { which } => {
                    let all: Vec<oracle::Tok> = toks.iter().map(|t| t.2).collect();
                    let Some(pick) = o.pick_restorable(&all, which) else { continue };
                    let (tp, tv, to) = toks[pick];
                    prop_assert!(
                        v.is_valid_token(&tv),
                        "step {}: verus rejects a live sparse-set token", step
                    );
                    p.restore(tp);
                    v.restore(tv);
                    o.restore(to);
                }
            }

            prop_assert_eq!(p.len() as usize, v.len() as usize, "step {}: sparse len diverged", step);
            prop_assert_eq!(p.len() as usize, o.cur.len(), "step {}: sparse len vs oracle", step);
            // Every id the oracle believes live must be live and hold the right
            // value on both sides -- including across a restore, which is where
            // id stability is easiest to get wrong.
            for (&id, &val) in o.cur.iter() {
                prop_assert!(p.contains(id), "step {}: prod lost live id {}", step, id);
                prop_assert!(v.contains(id), "step {}: verus lost live id {}", step, id);
                let ep = p.get(id);
                let ev = v.get(id);
                prop_assert_eq!(ep, ev, "step {}: sparse id {} diverged", step, id);
                prop_assert_eq!(ep, val, "step {}: sparse id {} vs oracle", step, id);
            }
        }
    }
}
