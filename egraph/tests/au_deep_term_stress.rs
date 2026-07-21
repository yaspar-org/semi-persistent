// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Deep/large-term stress tests for anti-unification.
//!
//! Covers: linear unary chains at depth 100 / 1000 / 6000, deep alternating
//! binary trees, wide AC multisets (many distinct children and high
//! multiplicities) exercising transport at scale, deep Seq nesting, a
//! cyclic-class chain versus a deep concrete chain under both `CycleMode`s,
//! and one runtime-bounded case documenting the practical depth limit.
//!
//! Stack budget: none needed. The exact solver, the UCT rollout and
//! certification paths, `build_best_term`, `TermPool::project`/`has_variants`,
//! and the test-side projection helpers below all use explicit heap-allocated
//! stacks, so a depth-n chain needs O(n) heap, not O(n) call-stack frames.
//! One regression deliberately requests a 64 KiB native thread stack to pin
//! that property; the remaining tests run directly on the default harness
//! thread. Depth is runtime-bounded (the O(n²) cost below), not stack-bounded.
//!
//! Cost note: at chain depth n the exact solver evaluates the generalize
//! incumbent at every level, and building the best representative of a
//! depth-k suffix walks k nodes, so total work is O(n²). That quadratic walk
//! is the practical limit documented by
//! `runtime_bounded_practical_limit` (measured: ~6 ms at n=100, ~0.43 s at
//! n=1000, ~15.5 s at n=6000, ~42 s at n=10000; debug build, Apple Silicon).
//!
//! UCT certification note: with the default `lct_and` AND selector (§3.3.5),
//! playout flux is routed to the least-certain child and terminal children
//! are skipped, so certifying a branching spine costs one playout per
//! expansion — proportional to graph size (measured: depth 16 certifies at
//! 17 playouts, depth 300 at 301, depth 400 at 401; the tests use the
//! standard 2000-playout budget for margin). Under the legacy `round_robin`
//! selector the playouts reaching depth k decay like 2^-k and certification
//! needs ~2^depth playouts (measured: depth 8 certifies at 1000 playouts,
//! depth 16 fails at 16000 and certifies at 64000);
//! `deep_branching_spine_certifies_when_shallow` pins that regime.

use std::time::Instant;

use semi_persistent_egraph::EGraph31;
use semi_persistent_egraph::au::egraph_api::AuSnapshot;
use semi_persistent_egraph::au::mcgs::AndSelector;
use semi_persistent_egraph::au::pretty::pretty_print;
use semi_persistent_egraph::au::session::{
    AuAlgorithm, AuConfig, AuResult, Completion, anti_unify,
};
use semi_persistent_egraph::au::space::CycleMode;
use semi_persistent_egraph::au::terms::{TermId, TermOp, TermPool};
use semi_persistent_egraph::id::{ENodeId, OpId};
use semi_persistent_egraph::literal::NiraLitVal;
use semi_persistent_egraph::nodes::LitValId;
use semi_persistent_egraph::registry::AssocDir;

type Eg = EGraph31<NiraLitVal, false, false>;

// ─── Projection helpers (pattern from au_adversarial_correctness.rs) ───

#[derive(Clone, Debug)]
enum OwnedTerm {
    App(OpId, Vec<OwnedTerm>),
    Lit(OpId, LitValId),
}

/// Rebuild an owned tree from a projected (Variants-free) pool term.
/// Iterative post-order fold with an explicit frame stack: children are built
/// left to right, so deep terms need heap, not call-stack frames.
fn own_projected(pool: &TermPool<OpId, LitValId>, id: TermId) -> OwnedTerm {
    struct Frame {
        op: OpId,
        children: Vec<TermId>,
        cursor: usize,
        out: Vec<OwnedTerm>,
    }
    let mut stack: Vec<Frame> = Vec::new();
    let mut pending = id;
    loop {
        // Enter: literals complete immediately; apps get a frame.
        let mut done: Option<OwnedTerm> = None;
        match pool.op(pending) {
            TermOp::EGraph(op) => {
                let children = pool.children(pending).to_vec();
                let capacity = children.len();
                stack.push(Frame {
                    op: *op,
                    children,
                    cursor: 0,
                    out: Vec::with_capacity(capacity),
                });
            }
            TermOp::Literal(op, value) => done = Some(OwnedTerm::Lit(*op, *value)),
            TermOp::Variants => panic!("projection still contains Variants"),
        }
        // Advance: deliver completed subterms upward, descend or compose.
        loop {
            if let Some(term) = done.take() {
                let Some(parent) = stack.last_mut() else {
                    return term;
                };
                parent.out.push(term);
                parent.cursor += 1;
            }
            let top = stack.last_mut().expect("own_projected stack is non-empty");
            if top.cursor < top.children.len() {
                pending = top.children[top.cursor];
                break;
            }
            let frame = stack.pop().expect("own_projected stack is non-empty");
            done = Some(OwnedTerm::App(frame.op, frame.out));
        }
    }
}

/// Re-add an owned tree into the e-graph, returning the root node id.
/// Iterative post-order fold with an explicit frame stack: `eg.add` calls
/// happen children-first, left to right, exactly like the recursive fold.
fn materialize(eg: &mut Eg, term: &OwnedTerm) -> ENodeId {
    struct Frame<'t> {
        op: OpId,
        children: &'t [OwnedTerm],
        cursor: usize,
        out: Vec<ENodeId>,
    }
    let mut stack: Vec<Frame<'_>> = Vec::new();
    let mut pending = term;
    loop {
        let mut done: Option<ENodeId> = None;
        match pending {
            OwnedTerm::App(op, children) => {
                stack.push(Frame {
                    op: *op,
                    children,
                    cursor: 0,
                    out: Vec::with_capacity(children.len()),
                });
            }
            OwnedTerm::Lit(op, value) => done = Some(eg.add_lit(*op, *value)),
        }
        loop {
            if let Some(node) = done.take() {
                let Some(parent) = stack.last_mut() else {
                    return node;
                };
                parent.out.push(node);
                parent.cursor += 1;
            }
            let top = stack.last_mut().expect("materialize stack is non-empty");
            if top.cursor < top.children.len() {
                pending = &top.children[top.cursor];
                break;
            }
            let frame = stack.pop().expect("materialize stack is non-empty");
            done = Some(eg.add(frame.op, &frame.out));
        }
    }
}

fn projected_terms(
    mut result: AuResult<semi_persistent_egraph::nodes::DefaultConfig>,
) -> (OwnedTerm, OwnedTerm) {
    let left = result.pool.project(result.term_id, 0);
    let right = result.pool.project(result.term_id, 1);
    assert!(!result.pool.has_variants(left));
    assert!(!result.pool.has_variants(right));
    (
        own_projected(&result.pool, left),
        own_projected(&result.pool, right),
    )
}

/// Run an anti-unification and assert quality, completion certification, and
/// (optionally) projection membership. Returns the elapsed wall time.
#[allow(clippy::too_many_arguments)]
fn check_pair(
    eg: &mut Eg,
    left: ENodeId,
    right: ENodeId,
    config: &AuConfig,
    expected: (u32, u32),
    certified: bool,
    project: bool,
    label: &str,
) -> std::time::Duration {
    let start = Instant::now();
    let (quality, completion, projections) = {
        let snapshot = AuSnapshot::new(eg).unwrap();
        let result = anti_unify(&snapshot, left, right, config).unwrap();
        let quality = result.pool.quality(result.term_id);
        let completion = result.completion;
        let projections = project.then(|| projected_terms(result));
        (quality, completion, projections)
    };
    let elapsed = start.elapsed();

    assert_eq!(quality, expected, "{label}: quality mismatch");
    if certified {
        assert_eq!(
            completion,
            Completion::Exact,
            "{label}: expected a certified-optimal completion"
        );
    }
    if let Some((left_term, right_term)) = projections {
        let projected_left = materialize(eg, &left_term);
        let projected_right = materialize(eg, &right_term);
        eg.rebuild();
        assert_eq!(
            eg.find_const(projected_left),
            eg.find_const(left),
            "{label}: left projection did not land in its source e-class"
        );
        assert_eq!(
            eg.find_const(projected_right),
            eg.find_const(right),
            "{label}: right projection did not land in its source e-class"
        );
    }
    eprintln!("{label}: quality={quality:?} completion={completion:?} elapsed={elapsed:?}");
    elapsed
}

/// Build the linear unary chain f^n(leaf).
fn build_chain(eg: &mut Eg, f: OpId, leaf: ENodeId, n: usize) -> ENodeId {
    let mut node = leaf;
    for _ in 0..n {
        node = eg.add(f, &[node]);
    }
    node
}

/// Chain fixture: f^n(a) vs f^n(b).
fn chain_fixture(n: usize) -> (Eg, ENodeId, ENodeId) {
    let mut eg = Eg::new();
    let sort = eg.intern_sort("E");
    let a_op = eg.register_op0("a", sort);
    let b_op = eg.register_op0("b", sort);
    let f = eg.register_op1("f", sort, sort);
    let a = eg.add(a_op, &[]);
    let b = eg.add(b_op, &[]);
    let left = build_chain(&mut eg, f, a, n);
    let right = build_chain(&mut eg, f, b, n);
    eg.rebuild();
    (eg, left, right)
}

// ═══════════════════════ Linear unary chains ══════════════════════════

/// Every production path that follows term/search depth must run on the heap,
/// not the native call stack. A depth-2000 chain would overflow a requested
/// 64 KiB stack under the recursive predecessor; the iterative implementation
/// must solve, project, compare, render, roll out, and certify it there.
#[test]
#[cfg_attr(miri, ignore)]
fn iterative_deep_paths_fit_in_64_kib_stack() {
    const DEPTH: usize = 2_000;
    const STACK_BYTES: usize = 64 * 1024;

    std::thread::Builder::new()
        .name("au-small-stack".to_owned())
        .stack_size(STACK_BYTES)
        .spawn(|| {
            let (eg, left, right) = chain_fixture(DEPTH);
            let snapshot = AuSnapshot::new(&eg).unwrap();

            let mut exact = anti_unify(
                &snapshot,
                left,
                right,
                &AuConfig {
                    algorithm: AuAlgorithm::Exact,
                    ..Default::default()
                },
            )
            .unwrap();
            assert_eq!(exact.pool.quality(exact.term_id), (DEPTH as u32 + 2, 2));
            assert_eq!(exact.completion, Completion::Exact);

            let projected_left = exact.pool.project(exact.term_id, 0);
            let projected_right = exact.pool.project(exact.term_id, 1);
            assert!(!exact.pool.has_variants(projected_left));
            assert!(!exact.pool.has_variants(projected_right));
            assert_ne!(
                exact.pool.structural_cmp(projected_left, projected_right),
                std::cmp::Ordering::Equal
            );

            let op_name = |op: &TermOp<OpId, LitValId>| match op {
                TermOp::EGraph(_) => "f".to_owned(),
                TermOp::Literal(_, _) => "literal".to_owned(),
                TermOp::Variants => "Variants".to_owned(),
            };
            let flat = pretty_print(&exact.pool, exact.term_id, op_name, usize::MAX);
            assert!(!flat.contains('\n'));
            let broken = pretty_print(&exact.pool, exact.term_id, op_name, 0);
            assert!(broken.contains('\n'));

            let uct = anti_unify(
                &snapshot,
                left,
                right,
                &AuConfig {
                    algorithm: AuAlgorithm::Uct,
                    playouts: 4_000,
                    ..Default::default()
                },
            )
            .unwrap();
            assert_eq!(uct.pool.quality(uct.term_id), (DEPTH as u32 + 2, 2));
            assert_eq!(uct.completion, Completion::Exact);
        })
        .expect("64 KiB AU stress thread must start")
        .join()
        .expect("iterative AU paths must not overflow a 64 KiB native stack");
}

/// f^100(a) vs f^100(b): the chain factors to full depth with one Variants
/// leaf. f^100(Variants(a,b)): size = 100 + (1+1) = 102, vmass = 2 → (102, 2).
/// Both algorithms find and certify the optimum (the search graph is a single
/// path, so UCT's closure pass resolves it within the playout budget).
#[test]
fn unary_chain_depth_100() {
    let (mut eg, left, right) = chain_fixture(100);
    check_pair(
        &mut eg,
        left,
        right,
        &AuConfig {
            algorithm: AuAlgorithm::Exact,
            ..Default::default()
        },
        (102, 2),
        true,
        true,
        "chain n=100 exact",
    );
    check_pair(
        &mut eg,
        left,
        right,
        &AuConfig {
            algorithm: AuAlgorithm::Uct,
            playouts: 2_000,
            ..Default::default()
        },
        (102, 2),
        true,
        true,
        "chain n=100 uct",
    );
}

/// f^1000(a) vs f^1000(b): (1002, 2). Runs on the default harness stack: all
/// deep paths (solver, projection, and the test-side helpers) use explicit
/// heap stacks, so depth needs no dedicated thread. UCT validity at this
/// depth: the optimum must be found and the projections must land in the
/// source classes (certification is also asserted — the graph is a single
/// path).
#[test]
#[cfg_attr(miri, ignore)]
fn unary_chain_depth_1000() {
    let (mut eg, left, right) = chain_fixture(1000);
    check_pair(
        &mut eg,
        left,
        right,
        &AuConfig {
            algorithm: AuAlgorithm::Exact,
            ..Default::default()
        },
        (1002, 2),
        true,
        true,
        "chain n=1000 exact",
    );
    check_pair(
        &mut eg,
        left,
        right,
        &AuConfig {
            algorithm: AuAlgorithm::Uct,
            playouts: 4_000,
            ..Default::default()
        },
        (1002, 2),
        true,
        true,
        "chain n=1000 uct",
    );
}

/// f^6000(a) vs f^6000(b): (6002, 2), exact only, on the default harness
/// stack. Measured (debug build, Apple Silicon): ~15.5 s — the O(n²)
/// generalize walk is the practical bound at this scale (depth is
/// runtime-bounded, not stack-bounded).
#[test]
#[cfg_attr(miri, ignore)]
fn unary_chain_depth_6000() {
    let (mut eg, left, right) = chain_fixture(6000);
    let elapsed = check_pair(
        &mut eg,
        left,
        right,
        &AuConfig {
            algorithm: AuAlgorithm::Exact,
            ..Default::default()
        },
        (6002, 2),
        true,
        true,
        "chain n=6000 exact",
    );
    assert!(
        elapsed.as_secs() < 90,
        "depth-6000 chain exceeded its runtime bound: {elapsed:?}"
    );
}

/// Runtime-bounded case documenting the practical limit. The exact solver
/// evaluates the generalize incumbent at every chain level, and building the
/// best representative of a depth-k suffix walks k nodes, so total work is
/// O(n²): measured (debug build, Apple Silicon) ~6 ms at n=100, ~0.43 s at
/// n=1000, ~15.5 s at n=6000, ~42 s at n=10000. This test pins the quadratic
/// regime at sizes that stay fast (n=2000 ≈ 1.7 s, n=4000 ≈ 7 s debug) and
/// bounds each run generously for slow CI hosts; five-digit depths remain
/// possible but cost minutes, which is the documented practical ceiling —
/// a runtime limit, not a stack limit, now that every deep path is iterative.
#[test]
#[cfg_attr(miri, ignore)]
fn runtime_bounded_practical_limit() {
    for n in [2_000_u32, 4_000] {
        let (mut eg, left, right) = chain_fixture(n as usize);
        let elapsed = check_pair(
            &mut eg,
            left,
            right,
            &AuConfig {
                algorithm: AuAlgorithm::Exact,
                ..Default::default()
            },
            (n + 2, 2),
            true,
            // Skip projection/materialization: re-adding thousands of
            // nodes into the e-graph is covered at depths 100–6000.
            false,
            &format!("chain n={n} exact (practical limit)"),
        );
        assert!(
            elapsed.as_secs() < 60,
            "practical-limit case n={n} exceeded its runtime bound: {elapsed:?}"
        );
    }
}

// ═══════════════════ Deep alternating binary trees ════════════════════

/// Alternating binary spine g(h(g(...), c), c) of depth 400, differing only
/// at the innermost leaf (a vs b). Each spine level contributes its operator
/// plus the shared c leaf: size = 2·400 + (1+1) = 802, vmass = 2 → (802, 2).
///
/// Certification IS asserted at this depth: the default `lct_and` AND
/// selector (§3.3.5) routes each playout down the still-uncertain spine child
/// (the terminal (c,c) sibling is skipped), so one playout expands one spine
/// level and certification costs ~depth+1 playouts (measured: exactly 401;
/// 2000 gives 5x margin at ~2.4 s debug). Under the legacy `round_robin`
/// selector this test could only assert the optimal quality: flux halves at
/// every 2-child AND level and certification needs ~2^depth playouts.
#[test]
#[cfg_attr(miri, ignore)]
fn deep_alternating_binary_tree() {
    const DEPTH: usize = 400;
    let (mut eg, left, right) = alternating_binary_fixture(DEPTH);
    check_pair(
        &mut eg,
        left,
        right,
        &AuConfig {
            algorithm: AuAlgorithm::Exact,
            ..Default::default()
        },
        (2 * DEPTH as u32 + 2, 2),
        true,
        true,
        "alternating binary depth=400 exact",
    );
    check_pair(
        &mut eg,
        left,
        right,
        &AuConfig {
            algorithm: AuAlgorithm::Uct,
            playouts: 2_000,
            ..Default::default()
        },
        (2 * DEPTH as u32 + 2, 2),
        true, // lct_and certifies at ~depth+1 playouts (measured: 401)
        true,
        "alternating binary depth=400 uct",
    );
}

/// The certified regime for branching spines under the legacy `round_robin`
/// selector: at depth 8 the ~2^depth playout requirement is comfortably
/// within budget, so UCT must certify. Round-robin is pinned explicitly here
/// (the default is `lct_and`, §3.3.5) to keep the selector selectable and
/// tested end to end.
#[test]
fn deep_branching_spine_certifies_when_shallow() {
    const DEPTH: usize = 8;
    let (mut eg, left, right) = alternating_binary_fixture(DEPTH);
    check_pair(
        &mut eg,
        left,
        right,
        &AuConfig {
            algorithm: AuAlgorithm::Uct,
            playouts: 1_000,
            and_selector: AndSelector::RoundRobin,
            ..Default::default()
        },
        (2 * DEPTH as u32 + 2, 2),
        true,
        true,
        "alternating binary depth=8 uct round-robin certified",
    );
}

/// The depth that defeats round-robin certifies cheaply under `lct_and`:
/// depth 16 needs ~2^16 playouts under round-robin (measured: fails at
/// 16000, certifies at 64000) but certifies at depth+1 = 17 playouts under
/// the default selector (100 gives ~6x margin).
#[test]
fn deep_branching_spine_certifies_at_depth_16_with_lct_and() {
    const DEPTH: usize = 16;
    let (mut eg, left, right) = alternating_binary_fixture(DEPTH);
    check_pair(
        &mut eg,
        left,
        right,
        &AuConfig {
            algorithm: AuAlgorithm::Uct,
            playouts: 100,
            ..Default::default() // default and_selector: LctAnd
        },
        (2 * DEPTH as u32 + 2, 2),
        true,
        true,
        "alternating binary depth=16 uct lct_and certified",
    );
}

/// Alternating binary spine fixture: leaves a vs b at the deepest position,
/// shared c elsewhere, alternating ops g/h up the spine.
fn alternating_binary_fixture(depth: usize) -> (Eg, ENodeId, ENodeId) {
    let mut eg = Eg::new();
    let sort = eg.intern_sort("E");
    let a_op = eg.register_op0("a", sort);
    let b_op = eg.register_op0("b", sort);
    let c_op = eg.register_op0("c", sort);
    let g = eg.register_op2("g", sort, sort, sort);
    let h = eg.register_op2("h", sort, sort, sort);
    let a = eg.add(a_op, &[]);
    let b = eg.add(b_op, &[]);
    let c = eg.add(c_op, &[]);
    let mut left = a;
    let mut right = b;
    for i in 0..depth {
        let op = if i % 2 == 0 { g } else { h };
        left = eg.add(op, &[left, c]);
        right = eg.add(op, &[right, c]);
    }
    eg.rebuild();
    (eg, left, right)
}

// ═══════════════════════ Wide AC multisets ════════════════════════════

/// Wide AC multiset with many DISTINCT children: 40 shared leaves plus 20
/// left-only and 20 right-only leaves (equal totals of 60 per side, so no
/// identity is needed). The optimal transport matches every shared leaf with
/// itself (cost 1 each) and pairs the 20 disjoint leaves into Variants
/// (cost 2 each): size = 1 + 40·1 + 20·2 = 81, vmass = 20·2 = 40 → (81, 40).
/// This drives a 60×60 cell matrix through the transport solver.
#[test]
#[cfg_attr(miri, ignore)]
fn wide_ac_multiset_many_distinct_children() {
    const SHARED: usize = 40;
    const DISJOINT: usize = 20;
    let mut eg = Eg::new();
    let sort = eg.intern_sort("E");
    let m = eg.register_mset("m", sort, sort);
    let shared: Vec<_> = (0..SHARED)
        .map(|i| {
            let op = eg.register_op0(&format!("s{i}"), sort);
            eg.add(op, &[])
        })
        .collect();
    let left_only: Vec<_> = (0..DISJOINT)
        .map(|i| {
            let op = eg.register_op0(&format!("l{i}"), sort);
            eg.add(op, &[])
        })
        .collect();
    let right_only: Vec<_> = (0..DISJOINT)
        .map(|i| {
            let op = eg.register_op0(&format!("r{i}"), sort);
            eg.add(op, &[])
        })
        .collect();
    let mut left_children = shared.clone();
    left_children.extend_from_slice(&left_only);
    let mut right_children = shared.clone();
    right_children.extend_from_slice(&right_only);
    let left = eg.add(m, &left_children);
    let right = eg.add(m, &right_children);
    eg.rebuild();

    let expected = (1 + SHARED as u32 + 2 * DISJOINT as u32, 2 * DISJOINT as u32);
    check_pair(
        &mut eg,
        left,
        right,
        &AuConfig {
            algorithm: AuAlgorithm::Exact,
            ..Default::default()
        },
        expected,
        true,
        true,
        "wide AC distinct exact",
    );
    check_pair(
        &mut eg,
        left,
        right,
        &AuConfig {
            algorithm: AuAlgorithm::Uct,
            playouts: 256,
            ..Default::default()
        },
        expected,
        true,
        true,
        "wide AC distinct uct",
    );
}

/// Wide AC multiset with HIGH multiplicities: m{a^64, x^64} vs m{b^64, x^64}.
/// Margins {a:64, x:64} vs {b:64, x:64}; the diagonal vertex matches x↔x (×64,
/// cost 1 each) and a↔b (×64, Variants cost 2 each):
/// size = 1 + 64·2 + 64·1 = 193, vmass = 64·2 = 128 → (193, 128).
/// Transport must move 128 units of flow without enumerating matrices.
#[test]
#[cfg_attr(miri, ignore)]
fn wide_ac_multiset_high_multiplicities() {
    const MULT: usize = 64;
    let mut eg = Eg::new();
    let sort = eg.intern_sort("E");
    let a_op = eg.register_op0("a", sort);
    let b_op = eg.register_op0("b", sort);
    let x_op = eg.register_op0("x", sort);
    let m = eg.register_mset("m", sort, sort);
    let a = eg.add(a_op, &[]);
    let b = eg.add(b_op, &[]);
    let x = eg.add(x_op, &[]);
    let mut left_children = vec![a; MULT];
    left_children.extend(std::iter::repeat_n(x, MULT));
    let mut right_children = vec![b; MULT];
    right_children.extend(std::iter::repeat_n(x, MULT));
    let left = eg.add(m, &left_children);
    let right = eg.add(m, &right_children);
    eg.rebuild();

    let expected = (1 + 3 * MULT as u32, 2 * MULT as u32);
    check_pair(
        &mut eg,
        left,
        right,
        &AuConfig {
            algorithm: AuAlgorithm::Exact,
            ..Default::default()
        },
        expected,
        true,
        true,
        "wide AC multiplicity exact",
    );
    check_pair(
        &mut eg,
        left,
        right,
        &AuConfig {
            algorithm: AuAlgorithm::Uct,
            playouts: 256,
            ..Default::default()
        },
        expected,
        true,
        true,
        "wide AC multiplicity uct",
    );
}

// ═══════════════════════ Deep Seq nesting ═════════════════════════════

/// Deeply nested associative sequences. Two DIFFERENT A ops must alternate:
/// nesting the same A op flattens under canonization, so a self-nested spine
/// would collapse into one wide sequence. Each level is a length-2 zip
/// s(c, t(c, s(...))): size = 2·300 + (1+1) = 602, vmass = 2 → (602, 2).
/// As with the binary spine, certification IS asserted: `lct_and` routes
/// flux to the uncertain spine child, so certification costs ~depth+1
/// playouts (measured: exactly 301; 2000 gives ~6x margin at ~1.7 s debug).
#[test]
#[cfg_attr(miri, ignore)]
fn deep_seq_nesting() {
    const DEPTH: usize = 300;
    let mut eg = Eg::new();
    let sort = eg.intern_sort("E");
    let a_op = eg.register_op0("a", sort);
    let b_op = eg.register_op0("b", sort);
    let c_op = eg.register_op0("c", sort);
    let s = eg.register_a("s", sort, sort, AssocDir::Both);
    let t = eg.register_a("t", sort, sort, AssocDir::Both);
    let a = eg.add(a_op, &[]);
    let b = eg.add(b_op, &[]);
    let c = eg.add(c_op, &[]);
    let mut left = a;
    let mut right = b;
    for i in 0..DEPTH {
        let op = if i % 2 == 0 { s } else { t };
        left = eg.add(op, &[c, left]);
        right = eg.add(op, &[c, right]);
    }
    eg.rebuild();
    check_pair(
        &mut eg,
        left,
        right,
        &AuConfig {
            algorithm: AuAlgorithm::Exact,
            ..Default::default()
        },
        (2 * DEPTH as u32 + 2, 2),
        true,
        true,
        "deep seq nesting exact",
    );
    check_pair(
        &mut eg,
        left,
        right,
        &AuConfig {
            algorithm: AuAlgorithm::Uct,
            playouts: 2_000,
            ..Default::default()
        },
        (2 * DEPTH as u32 + 2, 2),
        true, // lct_and certifies at ~depth+1 playouts (measured: 301)
        true,
        "deep seq nesting uct",
    );
}

// ═══════════ Cyclic class vs deep concrete chain (both modes) ═════════

/// Left class X = {x, f(X)} (a cycle created by merging x with f(x)); right
/// is the concrete chain f^128(b). Cycle contexts bound the unfolding:
///
/// * `AncestorOnly`: a class may appear twice per side on a path (current +
///   child), so X unfolds exactly ONE f level before the (X, f^127(b)) child
///   is blocked and must generalize: f(Variants(x, f^127(b))) has
///   size = 1 + (1 + 128) = 130, vmass = 1 + 128 = 129 → (130, 129).
/// * `CurrentInclusive`: a class may appear only once per side, so even the
///   first unfolding (child left class == current left class) is blocked;
///   only the root generalize survives: Variants(x, f^128(b)) has
///   size = 1 + 129 = 130, vmass = 130 → (130, 130).
///
/// Both modes tie on size (130); they differ in the variant-mass tie-break.
#[test]
#[cfg_attr(miri, ignore)]
fn cyclic_class_vs_deep_chain_under_both_cycle_modes() {
    const DEPTH: usize = 128;
    for (cycle_mode, expected) in [
        (CycleMode::AncestorOnly, (130, 129)),
        (CycleMode::CurrentInclusive, (130, 130)),
    ] {
        let mut eg = Eg::new();
        let sort = eg.intern_sort("E");
        let x_op = eg.register_op0("x", sort);
        let b_op = eg.register_op0("b", sort);
        let f = eg.register_op1("f", sort, sort);
        let x = eg.add(x_op, &[]);
        let fx = eg.add(f, &[x]);
        eg.merge(x, fx); // X = f(X): cyclic class with finite member x
        let b = eg.add(b_op, &[]);
        let right = build_chain(&mut eg, f, b, DEPTH);
        eg.rebuild();

        for (algorithm, playouts) in [(AuAlgorithm::Exact, 0), (AuAlgorithm::Uct, 2_000)] {
            check_pair(
                &mut eg,
                x,
                right,
                &AuConfig {
                    algorithm,
                    cycle_mode,
                    playouts,
                    ..Default::default()
                },
                expected,
                true,
                true,
                &format!("cyclic vs chain {cycle_mode:?} {algorithm:?}"),
            );
        }
    }
}
