// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Aggregate-level benchmark of the verified `EClasses` kernel: the
//! merge/find/mark-restore workloads the e-graph's saturation loop is made
//! of, isolated from e-matching and instantiation.
//!
//! There is no production-crate counterpart to A/B against (the hand-rolled
//! aggregate lived in the e-graph and is gone); revision-to-revision
//! comparison uses criterion baselines, the same protocol as the e-graph's
//! `saturate_bench` (see its module doc for why two arms in one group would
//! measure code layout instead of code):
//!
//! ```text
//! cargo bench --bench eclasses_bench -- --save-baseline before
//! # ... apply the change ...
//! cargo bench --bench eclasses_bench -- --baseline before
//! ```
//!
//! The end-to-end evidence for the swap itself is the e-graph's
//! `saturate_bench` pre/post comparison, recorded in
//! `containers-verus/doc/future/egraph-wf.md`.

use criterion::{Criterion, criterion_group, criterion_main};
use semi_persistent_containers_verus as verus;
use std::hint::black_box;
use verus::eclasses::EClasses;
use verus::opt::DenseId;
use verus::vec::ShrinkPolicy;

verus::define_id31! { pub struct BE / StoredBE, "e"; }
verus::define_id31! { pub struct BL / StoredBL, "l"; }
verus::define_id31! { pub struct BN / StoredBN, "n"; }

use semi_persistent_containers_verus::union_find::NoJust;
type EC = EClasses<BE, BL, BN, NoJust, true, false>;

fn be(n: usize) -> BE {
    BE::try_new(n).expect("bench id in range")
}

const N: usize = 4096;

/// Fresh aggregate with N singleton classes and one use each.
fn build() -> EC {
    let mut ec = EC::new();
    for i in 0..N {
        let (_, key) = ec.try_add_singleton();
        ec.add_use(key, be(i));
    }
    ec
}

fn bench(c: &mut Criterion) {
    let mut g = c.benchmark_group("eclasses");

    // pairwise merge cascade: N classes down to 1, splicing use-lists as the
    // rebuild loop does.
    g.bench_function("merge_cascade/4096", |b| {
        b.iter_batched(
            build,
            |mut ec| {
                let mut stride = 1;
                while stride < N {
                    let mut i = 0;
                    while i + stride < N {
                        if let Some(mi) = ec.merge(be(i), be(i + stride)) {
                            let sk = ec.repr_id(mi.survivor).unwrap();
                            ec.splice_uses(ec.use_list_id(sk), mi.absorbed_uses);
                        }
                        i += stride * 2;
                    }
                    stride *= 2;
                }
                black_box(ec.num_classes())
            },
            criterion::BatchSize::LargeInput,
        )
    });

    // find-heavy: canonicalization sweeps over a merged structure (the
    // rebuild loop's dominant read pattern).
    g.bench_function("find_sweep/4096", |b| {
        let mut ec = build();
        for i in 1..N {
            ec.merge(be(0), be(i));
        }
        b.iter(|| {
            let mut acc = 0usize;
            for i in 0..N {
                acc ^= ec.find_const(be(i)).to_usize();
            }
            black_box(acc)
        })
    });

    // mark, a burst of merges, restore: the saturation driver's backtrack.
    g.bench_function("mark_merge_restore/4096", |b| {
        b.iter_batched(
            build,
            |mut ec| {
                let tok = ec.mark(ShrinkPolicy::Never);
                for i in 1..256 {
                    ec.merge(be(0), be(i));
                }
                ec.try_restore(tok).expect("own token");
                black_box(ec.num_classes())
            },
            criterion::BatchSize::LargeInput,
        )
    });

    g.finish();
}

criterion_group!(benches, bench);
criterion_main!(benches);
