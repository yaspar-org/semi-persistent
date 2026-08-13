// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Confound-free perf-ratio gate (migration plan validation matrix: "RETAINED
//! containers within 10% of production unless a reviewed exception").
//!
//! This is NOT a criterion bench. Criterion's per-group `prod`-then-`verus`
//! layout measures position, not implementation (whichever arm is second
//! inherits a fragmented glibc `brk` heap and reads ~+18%); that artifact is
//! what made `micro/push_only_untracked` and `vec/mark_set_restore` look like
//! regressions when the code is byte-identical or verus-faster. See
//! `doc/design/11-layout-parity.md`.
//!
//! Instead it uses `containers_conformance::perf::{compare, compare_batched}`,
//! which interleaves the two arms per sample and takes the min, so the number
//! reflects the implementation. It prints a table and exits non-zero if any row
//! rises above **its own recorded ceiling** — usable as a CI gate, and wired in
//! as one (`.github/workflows/ci.yml`, job `perf-gate`). A `harness = false`
//! bench with a plain `main`.
//!
//! ## Ceilings are per-row, not a blanket 10%
//!
//! Each gated row is pinned near where it actually measures, via
//! `Row::gated(.., recorded)` = `recorded + perf::NOISE_MARGIN`, capped by the
//! plan's absolute `perf::MIGRATION_GATE`. A single blanket `pct <= 10` would let
//! `mark_set_restore` — recorded at −12…−17% — rot all the way to +9% and still
//! report "ok": a 26pp regression behind a green gate. Pinning per row is what
//! makes `BASELINE.md` enforced rather than documentary. The recorded values come
//! from the measured spread over seven consecutive runs, quoted per row below.
//!
//! The per-row ceilings hold on the machine they were recorded on. On other
//! hardware the ratio itself moves (see `perf::absolute_mode` and
//! `BASELINE.md`), so CI's shared runners set `PERF_GATE_ABSOLUTE=1` and gate
//! on `MIGRATION_GATE` alone.
//!
//! ## Why `push_only` is verified by disassembly, not timed here
//!
//! A tight allocate-and-push loop is the ONE workload no in-process A/B harness
//! can time fairly. Its per-iteration work is a few instructions, so the result
//! is dominated by whether the compiler inlines `Vec::push` into the timing
//! closure and where the loop lands modulo the cache line — and LLVM makes those
//! choices independently for the prod and verus closures (in this binary prod's
//! `push` is out-lined while verus's is inlined, a ~+22% artifact). The push
//! loop, `RawVec::grow_one`, `drop_in_place`, and allocation counts are all
//! **byte-identical** between the crates (`doc/design/11-layout-parity.md`), so
//! parity is established by that disassembly, not by a timing this harness
//! cannot make honest. The single-call-site `examples/onesite.rs` (both arms
//! through one `run(which)`, so identical inlining) reads +0.1% and is the
//! closest a timing gets. `push_only` is therefore NOT a gated row.
//!
//! The gated rows below (`mark_set_restore`, `restore_replay`) do substantial
//! work per timed unit — thousands of set/restore operations and diff-log walks
//! — so call and alignment overhead is negligible and the ratio reflects the
//! algorithm.
//!
//! ## Gate on phases, not cycles; the gate is one-sided
//!
//! `restore_replay` is a separate row from `mark_set_restore` because a whole
//! mark/set/restore cycle is set-phase dominated: it once read −25% while
//! `restore` alone was +30%. A cycle-level row averages away exactly the
//! regression it is supposed to catch. `Row::within_gate` fails only on verus
//! being *slower* — a symmetric gate failed the build for beating production.
use containers_conformance::perf::{self, Row};
use semi_persistent_containers as prod;
use semi_persistent_containers_verus as verus;
use std::hint::black_box;

// The pre-swap hand-rolled ring, shared by every class-ring parity harness so
// they all measure the same baseline (see the module's own doc).
use containers_conformance::prod_class_ring::{self as pring, PNodeId};
// `DenseId::from_usize`/`to_index` on both sides: node ids and the class-key index
// word are always derived from the id type, never cast to a literal width
// (`egraph/src/config.rs` pins every capacity-coupled id to one `Index`, so that a
// wider config gets wider arenas without overflow risk). The production side is
// called fully qualified (`prod::DenseId::from_usize`) because both crates' traits
// would otherwise collide in scope.
use verus::opt::DenseId as _;

const VEC_N: usize = 100_000;
const VEC_TOUCHES: usize = 50_000;

type VerusVecP = verus::vec::Vec<u64, u32, verus::parallel_store::ParallelStore<u64, u32>, true>;

fn xorshift(x: &mut u64) -> u64 {
    *x ^= *x << 13;
    *x ^= *x >> 7;
    *x ^= *x << 17;
    *x
}

/// mark_set_restore: mark, 50k random sets, restore — vec build is untimed.
fn row_mark_set_restore() -> Row {
    let (p, v) = perf::compare_batched(
        || {
            let mut vv: prod::VecP<u64, u32, true> = prod::VecP::new();
            for i in 0..VEC_N {
                vv.push(i as u64);
            }
            vv
        },
        |vv| {
            let tok = vv.mark(prod::ShrinkPolicy::Never);
            let mut x = 0x9E3779B97F4A7C15u64;
            for _ in 0..VEC_TOUCHES {
                let idx = (xorshift(&mut x) % VEC_N as u64) as u32;
                vv.set(idx, x);
            }
            vv.restore(tok);
            vv.len()
        },
        || {
            let mut vv: VerusVecP = VerusVecP::new();
            for i in 0..VEC_N {
                vv.try_push(i as u64).expect("push: within index word");
            }
            vv
        },
        |vv| {
            let tok = vv
                .try_mark(verus::vec::ShrinkPolicy::Never)
                .expect("mark: depth bounded by this harness");
            let mut x = 0x9E3779B97F4A7C15u64;
            for _ in 0..VEC_TOUCHES {
                let idx = (xorshift(&mut x) % VEC_N as u64) as u32;
                vv.set(idx, x);
            }
            vv.try_restore(tok).expect("restore: own token");
            vv.len()
        },
    );
    // Recorded −12.1% … −17.0% over seven consecutive runs; pinned to the least
    // favourable. This row is the noisiest (4.9pp spread) because the timed unit
    // includes the 50k-set phase.
    Row::gated("mark_set_restore", p, v, -12.0)
}

/// restore_replay: the restore phase ALONE (mark + dirty half is untimed setup).
///
/// Isolated because a full mark/set/restore cycle is set-dominated and can read
/// net-faster while restore itself regresses — exactly what happened when
/// `CaptureBits::set_true` regained production's `inline(always)` (cycle −25%,
/// restore +30%). The timed unit is RESTORE_BATCH independent restores: one
/// (~40 µs) proved to be within reach of the per-build layout artifact on a
/// shared runner — the row read +13.0% on ubuntu-latest at a commit that does
/// not touch the restore path, while reading −3.0% locally, the `class_walk`
/// incident's exact signature. Batching scales the work; the ratio is
/// dimensionless and carries over.
fn row_restore_replay() -> Row {
    fn prod_fixture() -> (prod::VecP<u64, u32, true>, prod::VecToken) {
        let mut vv: prod::VecP<u64, u32, true> = prod::VecP::new();
        for i in 0..VEC_N {
            vv.push(i as u64);
        }
        // Steady state: the capture bitmap is already materialized, as it is
        // in every criterion iteration after the first.
        let t0 = vv.mark(prod::ShrinkPolicy::Never);
        for i in 0..VEC_TOUCHES {
            vv.set(i as u32, i as u64);
        }
        vv.restore(t0);
        let tok = vv.mark(prod::ShrinkPolicy::Never);
        for i in 0..VEC_TOUCHES {
            vv.set(i as u32, (i + 999) as u64);
        }
        (vv, tok)
    }
    fn verus_fixture() -> (VerusVecP, verus::vec::VecToken) {
        let mut vv: VerusVecP = VerusVecP::new();
        for i in 0..VEC_N {
            vv.try_push(i as u64).expect("push: within index word");
        }
        let t0 = vv
            .try_mark(verus::vec::ShrinkPolicy::Never)
            .expect("mark: depth bounded by this harness");
        for i in 0..VEC_TOUCHES {
            vv.set(i as u32, i as u64);
        }
        vv.try_restore(t0).expect("restore: own token");
        let tok = vv
            .try_mark(verus::vec::ShrinkPolicy::Never)
            .expect("mark: depth bounded by this harness");
        for i in 0..VEC_TOUCHES {
            vv.set(i as u32, (i + 999) as u64);
        }
        (vv, tok)
    }
    let (p, v) = perf::compare_batched(
        || {
            (0..RESTORE_BATCH)
                .map(|_| prod_fixture())
                .collect::<std::vec::Vec<_>>()
        },
        |fs| {
            let mut total = 0usize;
            for (vv, tok) in fs.iter_mut() {
                vv.restore(*tok);
                total += vv.len() as usize;
            }
            total
        },
        || {
            (0..RESTORE_BATCH)
                .map(|_| verus_fixture())
                .collect::<std::vec::Vec<_>>()
        },
        |fs| {
            let mut total = 0usize;
            for (vv, tok) in fs.iter_mut() {
                vv.try_restore(*tok).expect("restore: own token");
                total += vv.len() as usize;
            }
            total
        },
    );
    // Recorded −1.1% … +1.4% over seven runs. Isolating the restore phase
    // removes the set-phase noise, so this row is tight; pinned at parity.
    Row::gated("restore_replay", p, v, 1.5)
}

/// Restores per timed unit in `restore_replay` — see that row's comment.
const RESTORE_BATCH: usize = 8;

/// vec/try_extend: the total shell's batch path (total-API plan phase 2)
/// against production's plain push loop, 100k u64s, untracked. One capacity
/// check licenses the batch; the loop invariant carries the bound, so the
/// shell adds one branch per BATCH over the partial core. Growth reallocs
/// dominate both arms equally, which is what makes this push-shaped row
/// timeable where per-element `push_only` is not (see that row's exclusion).
fn row_try_extend() -> Row {
    const N: usize = 100_000;
    let (p, v) = perf::compare_batched(
        || (0..N as u64).collect::<std::vec::Vec<u64>>(),
        |src| {
            let mut vv: prod::VecP<u64, u32, false> = prod::VecP::new();
            for &x in src.iter() {
                vv.push(x);
            }
            vv.len()
        },
        || (0..N as u64).collect::<std::vec::Vec<u64>>(),
        |src| {
            let mut vv = verus::vec::Vec::<
                u64,
                u32,
                verus::parallel_store::ParallelStore<u64, u32>,
                false,
            >::new();
            vv.try_extend(src).expect("100k fits a u32 index word");
            vv.len()
        },
    );
    // PROVISIONAL: recorded on the dev arm64 machine, not the EPYC baseline
    // box - re-record there with the spread before treating the margin as a
    // contract (BASELINE.md notes this row as pending).
    Row::gated("vec/try_extend (shell batch path)", p, v, 3.0)
}

const WRITES_PER_FRAME: usize = 64;

/// nested_mark: build `depth` marked frames of WRITES_PER_FRAME sets each, then
/// time one more mark over the deep retained history (the diff-log walk that a
/// shallow bench can't see). Frame build is untimed.
fn row_nested_mark(depth: usize, name: &'static str) -> Row {
    let (p, v) = perf::compare_batched(
        || {
            let mut vv: prod::VecP<u64, u32, true> = prod::VecP::new();
            for i in 0..VEC_N {
                vv.push(i as u64);
            }
            let mut x = 0x9E3779B97F4A7C15u64;
            let mut toks = std::vec::Vec::new();
            for _ in 0..depth {
                toks.push(vv.mark(prod::ShrinkPolicy::Never));
                for _ in 0..WRITES_PER_FRAME {
                    let idx = (xorshift(&mut x) % VEC_N as u64) as u32;
                    vv.set(idx, x);
                }
            }
            (vv, toks)
        },
        |(vv, toks)| {
            let final_tok = vv.mark(prod::ShrinkPolicy::Never);
            black_box(&final_tok);
            vv.restore(toks[0]);
            vv.len()
        },
        || {
            let mut vv: VerusVecP = VerusVecP::new();
            for i in 0..VEC_N {
                vv.try_push(i as u64).expect("push: within index word");
            }
            let mut x = 0x9E3779B97F4A7C15u64;
            let mut toks = std::vec::Vec::new();
            for _ in 0..depth {
                toks.push(
                    vv.try_mark(verus::vec::ShrinkPolicy::Never)
                        .expect("mark: depth bounded by this harness"),
                );
                for _ in 0..WRITES_PER_FRAME {
                    let idx = (xorshift(&mut x) % VEC_N as u64) as u32;
                    vv.set(idx, x);
                }
            }
            (vv, toks)
        },
        |(vv, toks)| {
            let final_tok = vv
                .try_mark(verus::vec::ShrinkPolicy::Never)
                .expect("mark: depth bounded by this harness");
            black_box(&final_tok);
            vv.try_restore(toks[0]).expect("restore: own token");
            vv.len()
        },
    );
    Row::ungated(name, p, v)
}

// ---------------------------------------------------------------------------
// The e-class ring (the consumer swap: `egraph/src/classes.rs`)
// ---------------------------------------------------------------------------
//
// `classes.rs` no longer hand-rolls its class ring; it uses the verified
// `CircularList`. So the production arm for these rows is the hand-rolled ring
// **as it was before the swap** — `containers_conformance::prod_class_ring`,
// reproduced there verbatim from the pre-swap file, i.e.
// `git show origin/main:egraph/src/classes.rs`. That
// is the only honest baseline: the implementation the swap replaced, not some
// other container.
//
// Both arms carry the same payload (a class key with a presence bit) in the same
// 12-byte cell (asserted by `tests/layout_parity.rs`), so these rows are an
// algorithm/codegen comparison, not a layout one.

verus::define_id31! { pub struct VNodeId / StoredVNodeId, "n"; }

/// The ring under test, parameterized exactly as the consumer's is: the payload is
/// `Opt<VNodeId::Index>` derived from the id, not a spelled-out `Opt<u32>`. The
/// index word is what `EGraphConfig::Index` pins (`egraph/src/config.rs`) so a wide
/// e-graph gets wide arenas; a harness that hard-codes it would silently stop
/// measuring the configuration the consumer is actually built for.
type VerusRing<const TRACK: bool> =
    verus::CircularList<verus::Opt<<VNodeId as verus::opt::DenseId>::Index>, VNodeId, TRACK>;

/// The post-swap `splice_classes` (`egraph/src/classes.rs`): the verified
/// `splice_absorb`, which swaps the two `next` words and carries the absorbed
/// class's presence-bit clear through the store the surgery already performs.
///
/// The write count is the whole point of this shape, so the harness has to mirror
/// it exactly: `splice` + a separate `set_payload` writes the absorbed cell twice,
/// and on a tracked ring each `set_index` runs the capture protocol. Two writes
/// per merge is what the pre-swap hand-rolled ring did and what `prod_class_ring`
/// still does.
fn verus_splice<const TRACK: bool>(
    ring: &mut VerusRing<TRACK>,
    survivor: VNodeId,
    absorbed: VNodeId,
) {
    let mut absorbed_payload = ring.payload_of(absorbed);
    absorbed_payload.set_none();
    ring.splice_absorb(survivor, absorbed, absorbed_payload);
}

const RING_N: usize = 20_000;
/// Merges performed per timed unit. `RING_N / 2` merges over `RING_N` singletons
/// leaves `RING_N / 2` two-node rings — a shape the walk row then reuses.
const RING_MERGES: usize = RING_N / 2;
/// Walk passes per timed unit in `class_walk` — see that row's comment: the
/// ratio is layout-noise-limited, not work-limited, so the timed unit is
/// scaled until a constant per-build layout artifact cannot reach the gate.
const WALK_PASSES: usize = 8;

/// The `i`th merge's (survivor, absorbed) pair, on each side. Both go through the
/// id's `DenseId::from_usize` rather than casting an index to a fixed width, so the
/// two arms address the same nodes at any id family.
fn pids(i: usize) -> (PNodeId, PNodeId) {
    (
        prod::DenseId::from_usize(2 * i),
        prod::DenseId::from_usize(2 * i + 1),
    )
}

fn vids(i: usize) -> (VNodeId, VNodeId) {
    (VNodeId::from_usize(2 * i), VNodeId::from_usize(2 * i + 1))
}

fn prod_ring_build<const TRACK: bool>() -> pring::ProdRing<TRACK> {
    pring::build(RING_N)
}

fn verus_ring_build<const TRACK: bool>() -> VerusRing<TRACK> {
    let mut ring: VerusRing<TRACK> = VerusRing::new();
    for i in 0..RING_N {
        // Class key = the node's own index word, via the id.
        ring.try_add_singleton(verus::Opt::some(VNodeId::from_usize(i).to_index()))
            .expect("within id space");
    }
    ring
}

/// class_splice_untracked: `RING_MERGES` ring merges over fresh singletons, no
/// capture. The ring build is untimed. ~50 µs of timed work at RING_N = 20k, so
/// well above the layout-noise floor.
///
/// Untracked because a tracked variant measures `Vec::set`'s capture path (already
/// gated by `mark_set_restore`) on top of the surgery; this row isolates the ring
/// algorithm — where the two arms genuinely differ (two full-cell writes vs. a
/// `next`-swap plus one payload write).
fn row_class_splice() -> Row {
    let (p, v) = perf::compare_batched(
        prod_ring_build::<false>,
        |ring| {
            for i in 0..RING_MERGES {
                let (s, a) = pids(i);
                pring::splice(ring, s, a);
            }
            ring.len()
        },
        verus_ring_build::<false>,
        |ring| {
            for i in 0..RING_MERGES {
                let (s, a) = vids(i);
                verus_splice(ring, s, a);
            }
            ring.len()
        },
    );
    // Recorded +3.9% … +4.7% over seven runs (0.8pp spread). The residual is the
    // extra payload write that clears the absorbed key's presence bit, which the
    // hand-rolled ring folded into its two full-cell writes.
    Row::gated("class_splice", p, v, 4.7)
}

/// class_walk: walk every one of the `RING_MERGES` two-node rings left by
/// `class_splice`, i.e. `RING_N` `next`-pointer hops plus `RING_MERGES`
/// start-comparisons. The build+merge is untimed.
///
/// This is the row that would catch the one exec difference in the swapped
/// iterator: `RingIter` compares `to_usize()` where `ClassIter` compared
/// `PartialEq` (needed because a generic `N`'s `==` has no spec contract). Both
/// are a mask-and-compare on a clean word, so parity is expected — measured
/// rather than argued.
///
/// Both arms must walk the ring the *same way* for that comparison to mean
/// anything: the prod arm goes through `prod_class_ring::ClassIter`, the
/// `Iterator` `origin/main` shipped.
fn row_class_walk() -> Row {
    let (p, v) = perf::compare_batched(
        || {
            let mut ring = prod_ring_build::<false>();
            for i in 0..RING_MERGES {
                let (s, a) = pids(i);
                pring::splice(&mut ring, s, a);
            }
            ring
        },
        |ring| {
            let mut total = 0usize;
            for _ in 0..WALK_PASSES {
                for i in 0..RING_MERGES {
                    total += pring::walk(ring, pids(i).0);
                }
            }
            total
        },
        || {
            let mut ring = verus_ring_build::<false>();
            for i in 0..RING_MERGES {
                let (s, a) = vids(i);
                verus_splice(&mut ring, s, a);
            }
            ring
        },
        |ring| {
            let mut total = 0usize;
            for _ in 0..WALK_PASSES {
                for i in 0..RING_MERGES {
                    total += ring.iter_class(vids(i).0).count();
                }
            }
            total
        },
    );
    // Recorded −0.6% … +0.3%: parity, once both arms walk the ring the same way.
    // The prod arm is `origin/main`'s `ClassIter` (an `Iterator`), not a plain
    // counting loop — see `prod_class_ring::ClassIter`. Measured with a plain
    // loop instead, this row read +16…+31% under `lto = "fat"`, all of it the
    // loop-preamble difference between the two walk styles (a hand loop hoists
    // the vec's ptr+len into one `ldp`; an `Iterator` reloads per `next`). The
    // loop bodies themselves are 9 insns prod / 8 insns verus with the same
    // 3-op loop-carried chain (`mul` → `ldr` → `and`), so the container is not
    // the variable — the harness's walk style was.
    //
    // WALK_PASSES exists because a single pass (~11 µs on a shared runner) is
    // small enough for BINARY-LAYOUT effects to breach even the absolute gate:
    // the Rust 1.97 toolchain bump read +12.9% on ubuntu-latest while the two
    // walk loops were INSTRUCTION-IDENTICAL in the same binary (x86_64, fat
    // LTO — 8 insns each, both 16-aligned, differing only in equality-compare
    // operand order). A layout artifact is constant per build, so per-sample
    // interleave + min cannot remove it; scaling the timed unit shrinks its
    // relative weight instead. Same evidence class as `push_only`'s
    // parity-by-disassembly above.
    Row::gated("class_walk", p, v, 0.5)
}

/// class_merge_restore: the tracked merge path — mark, `RING_MERGES` ring merges
/// with capture, then restore. This is the e-graph's actual rebuild/backtrack
/// shape, and the row where the diff-log entry width matters: both arms log
/// `(cell, u32)` = 16 bytes per captured write, which is the memory-parity claim
/// the `T::Index`-indexed storage exists to keep.
fn row_class_merge_restore() -> Row {
    let (p, v) = perf::compare_batched(
        prod_ring_build::<true>,
        |ring| {
            let tok = ring.mark(prod::ShrinkPolicy::Never);
            for i in 0..RING_MERGES {
                let (s, a) = pids(i);
                pring::splice(ring, s, a);
            }
            ring.try_restore(tok).expect("restore");
            ring.len()
        },
        verus_ring_build::<true>,
        |ring| {
            let tok = ring
                .try_mark(verus::vec::ShrinkPolicy::Never)
                .expect("mark");
            for i in 0..RING_MERGES {
                let (s, a) = vids(i);
                verus_splice(ring, s, a);
            }
            ring.try_restore(tok).expect("restore");
            ring.len()
        },
    );
    // Recorded −7.9% … −8.2% over seven runs — the tightest row of the set
    // (0.3pp). Pinned close, because this is the e-graph's actual
    // rebuild/backtrack shape and the row where diff-log entry width shows up.
    Row::gated("class_merge_restore", p, v, -7.8)
}

fn main() {
    // Both `nested_mark` sizes (0.38 µs and 2.6 µs of timed work) are measured
    // but NOT gated: at single-digit-µs scale the two separately-monomorphized
    // arms' loops land at different offsets modulo the cache line, and that
    // dominates (`doc/design/11-layout-parity.md`). They currently read ~+2.5%.
    //
    // CAUTION, learned the hard way: "it's below the layout floor" is not a
    // licence to dismiss a delta here. These rows once read +7–11% and were
    // written off as layout; the real cause was `CaptureBits::set_true` missing
    // production's `inline(always)`, and the tell was a *gated* row scaling with
    // n. Ungated means "not a build failure", not "not worth explaining".
    let ungated = [
        row_nested_mark(2, "nested_mark/depth2 (ungated: layout-noise floor)"),
        row_nested_mark(32, "nested_mark/depth32 (ungated: layout-noise floor)"),
    ];
    // `restore_replay` is gated separately from `mark_set_restore` on purpose.
    // A whole mark/set/restore cycle is dominated by the `set` phase, so a
    // genuinely slower restore hides inside a net-faster cycle: the cycle reads
    // −25% while restore alone is +30%. Phase-level rows are what actually
    // gate the migration claim; see `examples/phasesplit.rs`.
    // The e-class ring rows gate the consumer swap in `egraph/src/classes.rs`:
    // production's arm is the hand-rolled ring the swap deleted. All three do tens
    // of µs of timed work, so they are gated, not floor-exempt. `splice` and `walk`
    // are separate rows for the phase reason above — a merge-then-walk cycle is
    // hop-dominated and would hide a slower splice.
    let rows = [
        row_try_extend(),
        row_mark_set_restore(),
        row_restore_replay(),
        row_class_splice(),
        row_class_walk(),
        row_class_merge_restore(),
    ];
    if perf::absolute_mode() {
        println!(
            "gate mode: absolute ({}={} in the environment) — every gated row's\n\
             ceiling is the migration criterion, +{:.0}%. The per-row recorded\n\
             ceilings from BASELINE.md are enforced only on the machine they\n\
             were measured on; the prod/verus ratio is machine-dependent, so on\n\
             other hardware they gate the CPU, not the code.\n",
            perf::ABSOLUTE_MODE_ENV,
            std::env::var(perf::ABSOLUTE_MODE_ENV).unwrap_or_default(),
            perf::MIGRATION_GATE,
        );
    }
    perf::report(&ungated);
    let ok = perf::report(&rows);
    if !ok {
        if perf::absolute_mode() {
            eprintln!(
                "\nperf gate FAILED: a row is above the absolute migration\n\
                 ceiling (+{:.0}%) even in absolute mode, which already ignores\n\
                 the per-row recorded ceilings. This is not runner noise at any\n\
                 plausible width; treat it as a real regression and reproduce it\n\
                 on the baseline machine.",
                perf::MIGRATION_GATE,
            );
        } else {
            eprintln!(
                "\nperf gate FAILED: a row is above its recorded ceiling (see the\n\
                 OVER rows above, and `BASELINE.md` for what each was recorded at).\n\
                 Note the ceiling is per-row, not a blanket 10%: a row recorded as\n\
                 verus-faster has to STAY verus-faster. If you believe the new number\n\
                 is legitimate, re-record it in BASELINE.md and in the `Row::gated`\n\
                 call with the measured spread that justifies it — do not just widen\n\
                 the margin, which would discard the signal this gate exists for.\n\
                 If this machine is NOT the one BASELINE.md was recorded on, set\n\
                 {}=1 and gate on the absolute criterion instead.",
                perf::ABSOLUTE_MODE_ENV,
            );
        }
        std::process::exit(1);
    }
    println!(
        "\nperf gate: all rows within their {} ceilings.",
        if perf::absolute_mode() {
            "absolute"
        } else {
            "recorded"
        }
    );
}
