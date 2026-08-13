// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Where does `perf_gate::class_splice`'s +55% live — and why does the answer
//! depend on whether the ring is tracked?
//!
//! The gate's class-ring rows once read: `class_walk` −0.3% (parity),
//! `class_merge_restore` −8.5% (verus faster), but untracked `class_splice`
//! **+55%**. A delta that big on a row whose two arms do the same two stores is
//! not the layout artifact of `doc/design/11-layout-parity.md` — and it is
//! confined to the surgery, since the walk over the same rings is at parity.
//!
//! The consumer's post-swap `splice_classes` was
//!
//!     ring.splice(survivor, absorbed);              // swap the two `next`s
//!     let mut p = ring.payload_of(absorbed);        // re-READ the cell
//!     p.set_none();
//!     ring.set_payload(absorbed, p);                // re-WRITE the cell
//!
//! whereas the pre-swap hand-rolled version did two `Vec::set`s total, each
//! carrying the new `next` **and** the payload in one full-cell store. So the
//! suspicion was store count, not `splice` itself: verus touches the absorbed
//! cell twice (once inside `splice`, once for the presence bit) where production
//! touched it once.
//!
//! This probe separates the two candidate costs by timing `splice` ALONE against
//! the full `splice` + payload-clear sequence, and against `splice_absorb`, which
//! folds the presence-bit clear into the two stores the surgery already performs.
//! It runs both **untracked** and **tracked** (mark → merges → restore), because
//! that distinction turned out to be the whole story.
//!
//! ## What it found
//!
//! The +55% split into two unequal halves:
//!
//!   * **`splice` alone was +23%** — and the cause was NOT the ring code. Verus's
//!     `InlineStore::set_raw` preserved the inline capture flag across every
//!     write (read the old repr's tag, re-set it on the new one) where
//!     production guards that with `TRACK &&` (`containers/src/diff_store.rs:263`)
//!     — dead work in an untracked container. `DiffStore::set_raw`'s
//!     postcondition asserted flag preservation unconditionally, which is what
//!     forced it; weakening that clause to `TRACK ==>` (matching `push`/`pop`,
//!     which were already stated that way) let the guard back in. `splice` alone
//!     went +23% → **−30%**. This is the third time an `inline`/`TRACK` detail of
//!     production's has turned out to be interface rather than incident.
//!
//!   * **The separate payload write was +17% untracked, and folding it in bought
//!     nothing there** (5.58 vs 5.59 µs) — LLVM forwards the redundant load
//!     through the second `payload_of`, so the read-modify-write pair costs about
//!     what the folded store costs. On that evidence a payload-carrying splice was
//!     implemented, verified, measured, and REVERTED as not worth a wider API.
//!
//! **That revert was wrong, and this probe now shows why.** The untracked
//! measurement was not itself mistaken — the untracked table below still shows the
//! three verus arms within noise of each other — but it generalized a store-count
//! question from the one configuration where store count is nearly free. On a
//! **tracked** ring every `set_index` runs the capture protocol — a tag test, plus
//! a diff-log push on a cell's first write after a mark — and LLVM cannot forward
//! across it. Three writes per merge instead of two put `class_merge_restore` at
//! +2.5…+3.2% against its −7.8% recorded baseline; the folded `splice_absorb`
//! returns the row to verus-faster, and in the tracked table below is worth ~12pp
//! (3-write −10…−18%, folded −23…−25% over three runs). The untracked rows are kept
//! so the original negative result stays reproducible rather than becoming folklore
//! in either direction — with the caveat, now printed with them, that at ~5 µs they
//! sit at the layout floor and cannot resolve a few pp either way.
//!
//! Note the diff-log byte totals are equal either way (`tests/differential.rs`'s
//! `class_ring_bytes_trace` asserts exact equality at every step) because capture
//! logs a cell only on its **first** write after a mark: the third write is pure
//! overhead with no memory signature. The byte-parity test therefore cannot see
//! this at all, which is why write count needs its own timed baseline.
//!
//! ## Each variant is timed against prod pairwise, via the shared harness
//!
//! An earlier revision of this probe rotated three or four arms through one
//! hand-rolled min-of-N loop and printed each against a single prod column. That
//! reintroduced exactly the confound `perf::compare` exists to remove: with N arms
//! rotating, each one's fixture lands on a differently-fragmented heap, and the
//! shared prod column is whatever prod happened to measure in *that* rotation. It
//! read prod's tracked cycle at 55.8 µs where the gate — same machine, same
//! profile, pairwise-interleaved — read 76.4 µs, i.e. it disagreed with the gate
//! on the *sign* of the verus/prod ratio while the two harnesses' verus readings
//! agreed to within 3%. Each variant is now its own `perf::compare_batched` pair
//! against a freshly-interleaved prod arm, so every ratio below is comparable with
//! `perf_gate`'s and with the others.
//!
//! Run: `cargo run --release --example splicesplit -p containers-conformance`.
use containers_conformance::perf;
use semi_persistent_containers as prod;
use semi_persistent_containers_verus as verus;
use std::hint::black_box;

// The shared pre-swap baseline (see `prod_class_ring`'s doc for why it is shared).
use containers_conformance::prod_class_ring::{self as pring, PNodeId};
use verus::opt::DenseId as _;

verus::define_id31! { pub struct VNodeId / StoredVNodeId, "n"; }

type ProdRing<const TRACK: bool> = pring::ProdRing<TRACK>;
/// The ring under test. The payload is `Opt<VNodeId::Index>`, derived from the id
/// rather than spelled `Opt<u32>` — the same parameterization
/// `egraph/src/classes.rs`'s `ClassRing<T, TRACK>` uses, so switching the harness
/// to a `define_id63!` family is a type argument and not an edit.
type VerusRing<const TRACK: bool> =
    verus::CircularList<verus::Opt<<VNodeId as verus::opt::DenseId>::Index>, VNodeId, TRACK>;

const RING_N: usize = 20_000;
const MERGES: usize = RING_N / 2;

fn verus_build<const TRACK: bool>() -> VerusRing<TRACK> {
    let mut ring: VerusRing<TRACK> = VerusRing::new();
    for i in 0..RING_N {
        // The class key is the node's own index word, via the id — never a cast to
        // a fixed width.
        ring.try_add_singleton(verus::Opt::some(VNodeId::from_usize(i).to_index()))
            .expect("within id space");
    }
    ring
}

fn ids(i: usize) -> (VNodeId, VNodeId) {
    (VNodeId::from_usize(2 * i), VNodeId::from_usize(2 * i + 1))
}

fn pids(i: usize) -> (PNodeId, PNodeId) {
    (
        prod::DenseId::from_usize(2 * i),
        prod::DenseId::from_usize(2 * i + 1),
    )
}

// Each body `black_box`es the ring's length itself and returns `()`, rather than
// handing a length back for the harness to sink. `len()` is the container's index
// type (`u32` here, `T::Index` in general), and naming it in these signatures would
// pin the probe to one instantiation for no reason — the value is only a
// keep-alive.

/// Production's hand-rolled surgery: two full-cell stores per merge.
fn prod_merges<const TRACK: bool>(ring: &mut ProdRing<TRACK>) {
    for i in 0..MERGES {
        let (s, a) = pids(i);
        pring::splice(ring, s, a);
    }
    black_box(ring.len());
}

/// `CircularList::splice` alone — not what the consumer does, but it isolates the
/// verified surgery's own cost from the presence-bit clear.
fn verus_splice_only<const TRACK: bool>(ring: &mut VerusRing<TRACK>) {
    for i in 0..MERGES {
        let (s, a) = ids(i);
        ring.splice(s, a);
    }
    black_box(ring.len());
}

/// `splice` + a separate payload read-modify-write: **three** writes to the
/// absorbed cell per merge. What `splice_classes` did before `splice_absorb`.
fn verus_splice_and_clear<const TRACK: bool>(ring: &mut VerusRing<TRACK>) {
    for i in 0..MERGES {
        let (s, a) = ids(i);
        ring.splice(s, a);
        let mut p = ring.payload_of(a);
        p.set_none();
        ring.set_payload(a, p);
    }
    black_box(ring.len());
}

/// `splice_absorb`: the presence-bit clear carried through the splice, so the
/// merge costs **two** stores — production's write count. Today's consumer.
fn verus_splice_absorb<const TRACK: bool>(ring: &mut VerusRing<TRACK>) {
    for i in 0..MERGES {
        let (s, a) = ids(i);
        let mut p = ring.payload_of(a);
        p.set_none();
        ring.splice_absorb(s, a, p);
    }
    black_box(ring.len());
}

/// One untracked variant against prod, pairwise-interleaved. Ring builds untimed.
fn pair_untracked(v_body: fn(&mut VerusRing<false>)) -> (f64, f64) {
    perf::compare_batched(
        || pring::build::<false>(RING_N),
        prod_merges::<false>,
        verus_build::<false>,
        v_body,
    )
}

/// One tracked variant against prod — `class_merge_restore`'s shape, where every
/// store runs the capture protocol. Ring builds untimed.
fn pair_tracked(v_body: fn(&mut VerusRing<true>)) -> (f64, f64) {
    perf::compare_batched(
        || pring::build::<true>(RING_N),
        |ring| {
            let tok = ring.mark(prod::ShrinkPolicy::Never);
            prod_merges::<true>(ring);
            ring.restore(tok);
            black_box(ring.len());
        },
        verus_build::<true>,
        move |ring| {
            let tok = ring.mark(verus::vec::ShrinkPolicy::Never);
            v_body(ring);
            ring.restore(tok);
            black_box(ring.len());
        },
    )
}

fn table(title: &str, rows: &[(&str, (f64, f64))]) {
    println!("\n{title}\n");
    println!(
        "{:<44} {:>10} {:>10} {:>10}",
        "variant", "prod us", "verus us", "delta"
    );
    for (label, (p, v)) in rows {
        println!(
            "{:<44} {:>10.2} {:>10.2} {:>+9.1}%",
            label,
            p,
            v,
            perf::pct(*p, *v)
        );
    }
}

fn main() {
    let u_only = pair_untracked(verus_splice_only::<false>);
    let u_clear = pair_untracked(verus_splice_and_clear::<false>);
    let u_absorb = pair_untracked(verus_splice_absorb::<false>);

    table(
        &format!("{MERGES} ring merges over {RING_N} singletons, UNTRACKED:"),
        &[
            ("splice alone (2 writes, no bit clear)", u_only),
            ("splice + separate payload write (3)", u_clear),
            ("splice_absorb, payload folded (2)", u_absorb),
        ],
    );
    println!(
        "\nverus arms, untracked: {:.2} / {:.2} / {:.2} us — all three within noise of\n\
         each other. At ~5 us of timed work this table sits at the layout floor\n\
         (`doc/design/11-layout-parity.md`) and its per-variant deltas move several pp\n\
         run to run, so read it only as \"the fold neither helps nor hurts untracked\":\n\
         LLVM forwards the redundant load. That is the measurement — correct as far as\n\
         it goes — that once justified reverting the fold.",
        u_only.1, u_clear.1, u_absorb.1,
    );

    let t_clear = pair_tracked(verus_splice_and_clear::<true>);
    let t_absorb = pair_tracked(verus_splice_absorb::<true>);

    table(
        &format!("mark + {MERGES} merges + restore, TRACKED (capture protocol live):"),
        &[
            ("splice + separate payload write (3)", t_clear),
            ("splice_absorb, payload folded (2)", t_absorb),
        ],
    );
    println!(
        "\nthe fold is worth {:+.1}pp here, and unlike the untracked table this one is\n\
         stable across runs (~75 us of timed work, well clear of the layout floor;\n\
         3-write reads -10..-18%, folded -23..-25%). Every `set_index` runs the capture\n\
         protocol, so the third write is a third tag test, not a store LLVM can forward.\n\
         This is the inversion the untracked table cannot see, and why the folded form\n\
         is what `class_merge_restore` measures.",
        perf::pct(t_absorb.0, t_absorb.1) - perf::pct(t_clear.0, t_clear.1),
    );
}
