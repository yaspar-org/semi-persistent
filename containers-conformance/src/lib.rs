// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Conformance harness for the containers migration: compliance (differential
//! traces asserting observational equality between `semi-persistent-containers`
//! (production) and `semi-persistent-containers-verus` on identical operation
//! sequences) and performance benchmarks, for every container pair. The only
//! crate that depends on both implementations.
//!
//! Layout parity (same struct sizes, same niche bit-stealing) is asserted by
//! `tests/layout_parity.rs`; behavioral parity by `tests/differential.rs`;
//! performance parity by `benches/retained_containers_bench.rs` (gate: within
//! 10% of production or a reviewed exception).

/// The pre-swap hand-rolled e-class ring, the baseline for the class-ring rows.
pub mod prod_class_ring;

/// Deterministic xorshift64* generator: fixed seeds, exact replay.
pub struct Rng(u64);

#[allow(clippy::should_implement_trait)] // deliberate inherent `next`, matching the harness style
impl Rng {
    pub fn new(seed: u64) -> Self {
        Rng(seed.max(1))
    }
    pub fn next(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.0 = x;
        x.wrapping_mul(0x2545F4914F6CDD1D)
    }
    pub fn below(&mut self, n: u64) -> u64 {
        self.next() % n.max(1)
    }
}

/// Confound-free prod-vs-verus microbenchmark comparison.
///
/// Criterion's `benchmark_group` with a `prod` then a `verus` `bench_function`
/// measures **position, not implementation**: whichever arm runs second inherits
/// a warmed/fragmented glibc `brk` heap and reads ~+18%, and swapping the two
/// moves the penalty to the other. Both `micro/push_only_untracked` and
/// `vec/mark_set_restore` were chased as regressions and turned out to be this
/// artifact — the code is byte-identical or verus-faster once the confound is
/// removed. See `doc/design/11-layout-parity.md` and `examples/onesite*.rs`.
///
/// `compare` removes it two ways at once:
///   1. **Per-sample interleave** — prod and verus alternate every sample, so
///      neither is systematically "the second arm"; the heap state each sees is
///      the average of the two orders, not one fixed order.
///   2. **Min reduction** — the minimum over samples is the least-noise estimate
///      of the true cost (the fastest run is the one least perturbed by the OS),
///      which is also what makes the two arms comparable when their means differ
///      only by scheduling noise.
///
/// Returns `(prod_us, verus_us)`: the min timed cost of `p` and `v` in
/// microseconds. Each closure is one timed unit of work (build your fixture
/// outside the timed region — pass a closure that does setup then times only the
/// hot part, or use `compare_batched`).
pub mod perf {
    use std::hint::black_box;
    use std::time::Instant;

    /// Number of untimed warm iterations before timing begins.
    const WARM: usize = 20;
    /// Number of timed samples per arm.
    const SAMPLES: usize = 60;

    /// Interleaved prod-vs-verus comparison. Returns `(prod_us, verus_us)`.
    ///
    /// The two closures are timed **on the same iteration**, alternating which
    /// runs first each sample, so neither is ever systematically the "second
    /// arm" on a warmed heap — the positional confound that makes criterion's
    /// per-group layout unreliable (see `benches/perf_gate.rs`). Per-sample
    /// interleave is essential: measuring all of prod then all of verus (even
    /// in two rounds) still lets whole-arm heap state diverge. Min over samples
    /// is the least-perturbed estimate. Each closure does its own fixture setup
    /// and `black_box`es its result; for expensive setup use `compare_batched`.
    pub fn compare(mut p: impl FnMut(), mut v: impl FnMut()) -> (f64, f64) {
        let (mut pb, mut vb) = (f64::MAX, f64::MAX);
        for s in 0..(WARM + SAMPLES) {
            // Alternate lead each sample so ordering bias cancels pairwise.
            let (dp, dv) = if s % 2 == 0 {
                let dp = time_once(&mut p);
                let dv = time_once(&mut v);
                (dp, dv)
            } else {
                let dv = time_once(&mut v);
                let dp = time_once(&mut p);
                (dp, dv)
            };
            if s >= WARM {
                pb = pb.min(dp);
                vb = vb.min(dv);
            }
        }
        (pb, vb)
    }

    /// Time one call of `f` in microseconds.
    fn time_once(f: &mut impl FnMut()) -> f64 {
        let t = Instant::now();
        f();
        t.elapsed().as_nanos() as f64 / 1000.0
    }

    /// Like [`compare`] but with a per-sample fixture builder whose cost is NOT
    /// timed — the analogue of criterion's `iter_batched_ref`. `setup` builds a
    /// fresh fixture; `body` is the timed hot path over `&mut fixture`.
    pub fn compare_batched<PF, PS, VF, VS>(
        mut p_setup: impl FnMut() -> PF,
        mut p_body: impl FnMut(&mut PF) -> PS,
        mut v_setup: impl FnMut() -> VF,
        mut v_body: impl FnMut(&mut VF) -> VS,
    ) -> (f64, f64) {
        // Per-sample interleave (see `compare`): build+time prod then verus on
        // the same iteration, alternating lead, so neither is systematically
        // second on a warmed heap. Fixture build is outside the timed region.
        let (mut pb, mut vb) = (f64::MAX, f64::MAX);
        for s in 0..(WARM + SAMPLES) {
            let time_p = |p_setup: &mut dyn FnMut() -> PF,
                          p_body: &mut dyn FnMut(&mut PF) -> PS| {
                let mut fix = p_setup();
                let t = Instant::now();
                black_box(p_body(&mut fix));
                t.elapsed().as_nanos() as f64 / 1000.0
            };
            let time_v = |v_setup: &mut dyn FnMut() -> VF,
                          v_body: &mut dyn FnMut(&mut VF) -> VS| {
                let mut fix = v_setup();
                let t = Instant::now();
                black_box(v_body(&mut fix));
                t.elapsed().as_nanos() as f64 / 1000.0
            };
            let (dp, dv) = if s % 2 == 0 {
                let dp = time_p(&mut p_setup, &mut p_body);
                let dv = time_v(&mut v_setup, &mut v_body);
                (dp, dv)
            } else {
                let dv = time_v(&mut v_setup, &mut v_body);
                let dp = time_p(&mut p_setup, &mut p_body);
                (dp, dv)
            };
            if s >= WARM {
                pb = pb.min(dp);
                vb = vb.min(dv);
            }
        }
        (pb, vb)
    }

    /// The verus/prod ratio as a signed percentage (`+` = verus slower).
    pub fn pct(prod_us: f64, verus_us: f64) -> f64 {
        (verus_us / prod_us - 1.0) * 100.0
    }

    /// The migration plan's absolute ceiling: "RETAINED containers within 10%
    /// of production unless a reviewed exception". No recorded baseline may be
    /// laxer than this, whatever a row once measured.
    pub const MIGRATION_GATE: f64 = 10.0;

    /// Slack added to a row's recorded delta to absorb machine-to-machine and
    /// run-to-run noise. Sized from the observed local spread over seven
    /// consecutive runs (worst row: `mark_set_restore` at 4.9pp; the stable
    /// rows sit under 1pp), then rounded up for shared CI runners, which are
    /// noisier than the developer box the baselines were taken on.
    ///
    /// Widening this — or a row's recorded value — is legitimate ONLY against a
    /// measured spread on the machine that flagged it. Widening to silence a
    /// row that is trending in one direction across commits defeats the point:
    /// that trend is the regression signal this gate exists to catch.
    pub const NOISE_MARGIN: f64 = 6.0;

    /// One row of a perf-ratio report.
    pub struct Row {
        pub name: &'static str,
        pub prod_us: f64,
        pub verus_us: f64,
        /// Ceiling this row must stay at or below, in percent; `None` for a row
        /// that is measured and printed but not gated.
        pub ceiling: Option<f64>,
    }

    impl Row {
        /// A gated row, pinned to its **recorded** delta from `BASELINE.md`.
        ///
        /// `recorded` is the worst (least favourable) delta the row has been
        /// measured at; the ceiling is that plus [`NOISE_MARGIN`], capped by
        /// [`MIGRATION_GATE`]. This is what makes the baselines enforced rather
        /// than documentary: under a blanket `pct <= 10` gate, a row recorded at
        /// −17% could rot all the way to +9% — a 26pp regression — and still
        /// report "ok". Pinning each row near where it actually measures means a
        /// verus-faster row has to *stay* verus-faster.
        pub fn gated(name: &'static str, prod_us: f64, verus_us: f64, recorded: f64) -> Row {
            Row {
                name,
                prod_us,
                verus_us,
                ceiling: Some((recorded + NOISE_MARGIN).min(MIGRATION_GATE)),
            }
        }

        /// A row that is measured and printed but never fails the build; the
        /// caller's `name` should say why (e.g. below the layout-noise floor).
        pub fn ungated(name: &'static str, prod_us: f64, verus_us: f64) -> Row {
            Row {
                name,
                prod_us,
                verus_us,
                ceiling: None,
            }
        }

        pub fn pct(&self) -> f64 {
            pct(self.prod_us, self.verus_us)
        }

        /// One-sided: only verus being **slower** than its recorded baseline is
        /// a failure. A verus win is the goal, not a regression — a symmetric
        /// `abs()` gate once failed the build at −25%, for beating production.
        pub fn within_gate(&self) -> bool {
            match self.ceiling {
                Some(c) => self.pct() <= c,
                None => true,
            }
        }
    }

    /// Print a report and return whether every row is within its ceiling.
    pub fn report(rows: &[Row]) -> bool {
        println!(
            "{:<50} {:>11} {:>11} {:>8} {:>9}  gate",
            "bench", "prod (us)", "verus (us)", "delta", "ceiling"
        );
        let mut all_ok = true;
        for r in rows {
            let ok = r.within_gate();
            all_ok &= ok;
            let ceiling = match r.ceiling {
                Some(c) => format!("{c:>+8.1}%"),
                None => "     n/a".to_string(),
            };
            println!(
                "{:<50} {:>11.2} {:>11.2} {:>+7.1}% {} {}",
                r.name,
                r.prod_us,
                r.verus_us,
                r.pct(),
                ceiling,
                if ok { " ok" } else { "OVER" }
            );
        }
        all_ok
    }
}
