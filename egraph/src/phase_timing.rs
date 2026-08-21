// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Per-phase wall-clock accounting for the saturation round loop.
//!
//! The round loop's cost splits into rebuild, index build, and matching, and the
//! index build splits again into the walk that writes each family's `(key,
//! value)` stream and the container build that turns a stream into a span table.
//! Attributing a regression to one of those needs the split measured in process,
//! not inferred from differences of end-to-end wall times: the E6 cycle costs
//! ~180 ms against a base build of ~750 ms, so a 10 ms phase is inside the noise
//! of any subtraction the runner can do from outside.
//!
//! Off by default and zero cost when off. The `phase-timing` feature selects the
//! recording implementation; without it every entry point below is an empty
//! inline function and the call sites compile away. With it, `EGRAPH_PHASE=1`
//! prints the totals at exit and `EGRAPH_PHASE=rounds` additionally prints one
//! line per round.
//!
//! Call sites stay unconditional so the instrumented and uninstrumented builds
//! are the same source; see `saturate.rs` and `index.rs`.

/// Slot names, in report order. Indented names are sub-phases of the entry above
/// them and are already included in it, so a column of totals double-counts on
/// purpose: the parent is the number the round loop pays and the children say
/// where it went.
pub const SLOTS: &[&str] = &[
    "rebuild",
    "index.full",
    "  full.walk",
    "  full.span.by_op",
    "  full.span.by_repr",
    "  full.span.by_child_pos",
    "  full.span.by_contains",
    "  full.fanouts",
    "index.delta",
    "  delta.sort+dedup",
    "  delta.walk",
    "  delta.span.by_op",
    "  delta.span.by_repr",
    "  delta.span.by_child_pos",
    "  delta.span.by_contains",
    "match+apply",
    "  stats",
];

pub const REBUILD: usize = 0;
pub const FULL: usize = 1;
pub const FULL_WALK: usize = 2;
pub const FULL_SPAN_OP: usize = 3;
pub const FULL_SPAN_REPR: usize = 4;
pub const FULL_SPAN_CHILD_POS: usize = 5;
pub const FULL_SPAN_CONTAINS: usize = 6;
pub const FULL_FANOUTS: usize = 7;
pub const DELTA: usize = 8;
pub const DELTA_DEDUP: usize = 9;
pub const DELTA_WALK: usize = 10;
pub const DELTA_SPAN_OP: usize = 11;
pub const DELTA_SPAN_REPR: usize = 12;
pub const DELTA_SPAN_CHILD_POS: usize = 13;
pub const DELTA_SPAN_CONTAINS: usize = 14;
pub const MATCH: usize = 15;
pub const STATS: usize = 16;

/// Scalar counters, summed over the run. The key/value pairs are the whole
/// question the diagnosis asks: a dense span table costs one `Span` per key
/// whether or not the key occurs, so `keys` far above `values` is the term to
/// remove.
pub const COUNTERS: &[&str] = &[
    "rounds",
    "rounds.with_delta",
    "variants",
    "full.nodes",
    "full.by_child_pos.keys",
    "full.by_child_pos.values",
    "full.by_child_pos.nonempty",
    "delta.ids",
    "delta.by_child_pos.keys",
    "delta.by_child_pos.values",
    "delta.by_child_pos.nonempty",
];

pub const C_ROUNDS: usize = 0;
pub const C_ROUNDS_DELTA: usize = 1;
pub const C_VARIANTS: usize = 2;
pub const C_FULL_NODES: usize = 3;
pub const C_FULL_CP_KEYS: usize = 4;
pub const C_FULL_CP_VALUES: usize = 5;
pub const C_FULL_CP_NONEMPTY: usize = 6;
pub const C_DELTA_IDS: usize = 7;
pub const C_DELTA_CP_KEYS: usize = 8;
pub const C_DELTA_CP_VALUES: usize = 9;
pub const C_DELTA_CP_NONEMPTY: usize = 10;

#[cfg(not(feature = "phase-timing"))]
mod imp {
    /// Zero-cost stand-in: no field, no `Drop`, so the guard and its scope
    /// vanish in the uninstrumented build.
    pub struct Timer;

    impl Timer {
        #[inline(always)]
        pub fn start(_slot: usize) -> Self {
            Timer
        }

        /// End the timed scope early. `drop` would do it, but only in the
        /// recording build does this type implement `Drop`, and clippy reads
        /// `drop` on a type without one as a mistake.
        #[inline(always)]
        pub fn stop(self) {}
    }

    #[inline(always)]
    pub fn count(_c: usize, _v: u64) {}
    #[inline(always)]
    pub fn round_line(_tag: &str) {}
    #[inline(always)]
    pub fn dump() {}
    #[inline(always)]
    pub fn enabled() -> bool {
        false
    }
}

#[cfg(feature = "phase-timing")]
mod imp {
    use std::sync::atomic::{AtomicU64, Ordering};
    use std::sync::{Mutex, OnceLock};
    use std::time::Instant;

    const N: usize = super::SLOTS.len();
    const M: usize = super::COUNTERS.len();

    // `AtomicU64` rather than a thread-local `Cell`: the engine is
    // single-threaded, so this is uncontended and the relaxed add is a plain
    // instruction, and a `static` needs no lazy initialization on the hot path.
    static NANOS: [AtomicU64; N] = [const { AtomicU64::new(0) }; N];
    static CALLS: [AtomicU64; N] = [const { AtomicU64::new(0) }; N];
    static COUNTS: [AtomicU64; M] = [const { AtomicU64::new(0) }; M];

    fn mode() -> &'static str {
        static MODE: OnceLock<String> = OnceLock::new();
        MODE.get_or_init(|| std::env::var("EGRAPH_PHASE").unwrap_or_default())
    }

    pub fn enabled() -> bool {
        !mode().is_empty()
    }

    fn per_round() -> bool {
        mode() == "rounds"
    }

    pub struct Timer {
        slot: usize,
        t0: Instant,
    }

    impl Timer {
        #[inline]
        pub fn start(slot: usize) -> Self {
            Timer {
                slot,
                t0: Instant::now(),
            }
        }

        /// End the timed scope early; see the stand-in's `stop`.
        #[inline]
        pub fn stop(self) {}
    }

    impl Drop for Timer {
        #[inline]
        fn drop(&mut self) {
            let ns = self.t0.elapsed().as_nanos() as u64;
            NANOS[self.slot].fetch_add(ns, Ordering::Relaxed);
            CALLS[self.slot].fetch_add(1, Ordering::Relaxed);
        }
    }

    #[inline]
    pub fn count(c: usize, v: u64) {
        COUNTS[c].fetch_add(v, Ordering::Relaxed);
    }

    fn last() -> &'static Mutex<([u64; N], [u64; M], usize)> {
        static LAST: OnceLock<Mutex<([u64; N], [u64; M], usize)>> = OnceLock::new();
        LAST.get_or_init(|| Mutex::new(([0; N], [0; M], 0)))
    }

    /// One line per round, in milliseconds, of what accumulated since the
    /// previous call. Printed only under `EGRAPH_PHASE=rounds`.
    pub fn round_line(tag: &str) {
        if !per_round() {
            return;
        }
        let mut g = last().lock().unwrap();
        let (prev, prev_c, seq) = &mut *g;
        let mut cells = String::new();
        for i in 0..N {
            let now = NANOS[i].load(Ordering::Relaxed);
            cells.push_str(&format!("\t{:.3}", (now - prev[i]) as f64 / 1e6));
            prev[i] = now;
        }
        for i in 0..M {
            let now = COUNTS[i].load(Ordering::Relaxed);
            cells.push_str(&format!("\t{}", now - prev_c[i]));
            prev_c[i] = now;
        }
        if *seq == 0 {
            let mut hdr = String::from("PHASE_ROUND\tseq\ttag");
            for s in super::SLOTS {
                hdr.push('\t');
                hdr.push_str(s.trim());
            }
            for s in super::COUNTERS {
                hdr.push('\t');
                hdr.push_str(s);
            }
            eprintln!("{hdr}");
        }
        eprintln!("PHASE_ROUND\t{seq}\t{tag}{cells}");
        *seq += 1;
    }

    pub fn dump() {
        if !enabled() {
            return;
        }
        eprintln!("\n=== phase totals ===");
        eprintln!(
            "{:<26} {:>12} {:>10} {:>12}",
            "phase", "ms", "calls", "us/call"
        );
        for i in 0..N {
            let ns = NANOS[i].load(Ordering::Relaxed);
            let c = CALLS[i].load(Ordering::Relaxed);
            if c == 0 {
                continue;
            }
            eprintln!(
                "{:<26} {:>12.3} {:>10} {:>12.3}",
                super::SLOTS[i],
                ns as f64 / 1e6,
                c,
                ns as f64 / 1e3 / c as f64
            );
        }
        eprintln!("--- counters ---");
        for i in 0..M {
            let v = COUNTS[i].load(Ordering::Relaxed);
            if v == 0 {
                continue;
            }
            eprintln!("{:<26} {:>12}", super::COUNTERS[i], v);
        }
    }
}

pub use imp::{Timer, count, dump, enabled, round_line};
