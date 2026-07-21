// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Manual AU search-space stress tests.
//!
//! These tests are ignored in normal CI because their purpose is to expose
//! scaling and print reproducible counts/timings, not to enforce machine-specific
//! latency thresholds. Run with:
//! `cargo test -p semi-persistent-egraph --test au_adversarial_stress -- --ignored --nocapture`.

use std::time::Instant;

use semi_persistent_egraph::EGraph31;
use semi_persistent_egraph::au::actions::{ActionCache, generate_actions};
use semi_persistent_egraph::au::egraph_api::AuSnapshot;
use semi_persistent_egraph::literal::NiraLitVal;

type Eg = EGraph31<NiraLitVal, false, false>;

fn factorial(n: usize) -> usize {
    (1..=n).product()
}

/// One rewrite-saturated root e-class may contain K same-op members on each
/// side. `A_max` is restarted for every member-node pair, so the class-pair OR
/// state receives K^2*A_max edges. With exact enumeration it receives K^2*n!
/// edges for disjoint n-element ACI members.
#[test]
#[ignore = "manual stress: rewrite-rich ACI classes produce K^2 times the per-member action bound"]
fn rewrite_member_cross_product_multiplies_the_action_cap() {
    const K: usize = 12;
    const ARITY: usize = 6;
    const A_MAX: usize = 32;

    let mut eg = Eg::new();
    let sort = eg.intern_sort("E");
    let set = eg.register_set("set", sort, sort);
    let leaf_ops: Vec<_> = (0..(2 * K * ARITY))
        .map(|i| eg.register_op0(&format!("v{i}"), sort))
        .collect();
    let leaves: Vec<_> = leaf_ops.iter().map(|&op| eg.add(op, &[])).collect();

    let mut left_members = Vec::new();
    let mut right_members = Vec::new();
    for member in 0..K {
        let left_start = member * ARITY;
        let right_start = K * ARITY + member * ARITY;
        left_members.push(eg.add(set, &leaves[left_start..left_start + ARITY]));
        right_members.push(eg.add(set, &leaves[right_start..right_start + ARITY]));
    }
    for &member in &left_members[1..] {
        eg.merge(left_members[0], member);
    }
    for &member in &right_members[1..] {
        eg.merge(right_members[0], member);
    }
    eg.rebuild();

    let snapshot = AuSnapshot::new(&eg).unwrap();
    let left = snapshot.class_of(left_members[0]).unwrap();
    let right = snapshot.class_of(right_members[0]).unwrap();

    let bounded_start = Instant::now();
    let mut bounded = ActionCache::new(A_MAX);
    generate_actions(&snapshot, &mut bounded, left, right);
    let bounded_count = bounded.get(left, right).unwrap().len();
    let bounded_elapsed = bounded_start.elapsed();
    assert_eq!(bounded_count, K * K * A_MAX);

    let exact_start = Instant::now();
    let mut exact = ActionCache::new(usize::MAX);
    generate_actions(&snapshot, &mut exact, left, right);
    let exact_count = exact.get(left, right).unwrap().len();
    let exact_elapsed = exact_start.elapsed();
    assert_eq!(exact_count, K * K * factorial(ARITY));

    eprintln!(
        "K={K}, arity={ARITY}: bounded={bounded_count} actions in {bounded_elapsed:?}; \
         exact={exact_count} actions in {exact_elapsed:?}"
    );
}

/// Padding an n-vs-2 ACI pair creates n-2 virtual columns carrying the same
/// identity class. There are only n*(n-1) unique semantic pairings, but the
/// recursive traversal still visits permutations of the indistinguishable
/// virtual columns (n! leaves before deduplication).
#[test]
#[ignore = "manual stress: identity padding explores factorial duplicate virtual-unit permutations"]
fn identity_padding_has_factorial_internal_work_for_few_unique_actions() {
    const N: usize = 9;

    let mut eg = Eg::new();
    let sort = eg.intern_sort("E");
    let unit_op = eg.register_op0("unit", sort);
    let unit = eg.add(unit_op, &[]);
    let set = eg.register_set("set", sort, sort);
    eg.set_unit_node(set, unit);
    let leaf_ops: Vec<_> = (0..(N + 2))
        .map(|i| eg.register_op0(&format!("v{i}"), sort))
        .collect();
    let leaves: Vec<_> = leaf_ops.iter().map(|&op| eg.add(op, &[])).collect();
    let left = eg.add(set, &leaves[..N]);
    let right = eg.add(set, &leaves[N..N + 2]);
    eg.rebuild();

    let snapshot = AuSnapshot::new(&eg).unwrap();
    let left = snapshot.class_of(left).unwrap();
    let right = snapshot.class_of(right).unwrap();
    let start = Instant::now();
    let mut cache = ActionCache::new(usize::MAX);
    generate_actions(&snapshot, &mut cache, left, right);
    let elapsed = start.elapsed();
    let unique_actions = cache.get(left, right).unwrap().len();

    assert_eq!(unique_actions, N * (N - 1));
    eprintln!(
        "ACI {N}-vs-2 identity padding: {} traversal leaves collapse to \
         {unique_actions} actions in {elapsed:?}",
        factorial(N)
    );
}

/// Reachability stores one C-bit bitset per SCC. A long acyclic chain has C
/// singleton SCCs, therefore the snapshot allocates O(C^2) reachability bits
/// even though the graph has only O(C) edges.
#[test]
#[ignore = "manual stress: acyclic snapshot reachability uses quadratic bitset storage"]
fn acyclic_chain_snapshot_exposes_quadratic_reachability_shape() {
    const CLASSES: usize = 6_000;

    let mut eg = Eg::new();
    let sort = eg.intern_sort("E");
    let leaf_op = eg.register_op0("leaf", sort);
    let step = eg.register_op1("step", sort, sort);
    let leaf = eg.add(leaf_op, &[]);
    let mut node = leaf;
    for _ in 1..CLASSES {
        node = eg.add(step, &[node]);
    }
    eg.rebuild();

    let start = Instant::now();
    let snapshot = AuSnapshot::new(&eg).unwrap();
    let elapsed = start.elapsed();
    assert_eq!(snapshot.num_classes(), CLASSES);
    let root = snapshot.class_of(node).unwrap();
    let leaf = snapshot.class_of(leaf).unwrap();
    assert!(snapshot.reachability().is_reachable(root, leaf));

    let approximate_bytes = CLASSES * CLASSES.div_ceil(64) * size_of::<u64>();
    eprintln!(
        "acyclic classes={CLASSES}: snapshot={elapsed:?}, theoretical reachability blocks≈{} MiB",
        approximate_bytes / (1024 * 1024)
    );
}
