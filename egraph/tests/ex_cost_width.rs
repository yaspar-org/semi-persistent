// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! The cost width (`--cost-bits 32|64|big`) and the extraction defects it closes.
//!
//! Each test names the defect of `doc/integer-audit.md` (area C) or of
//! `doc/goal-counted-multiplicities.md` (bugs #1, #5, #6) it is the boundary case of:
//! the input that wrapped, panicked, or reported a wrong `Proved` is now a reported
//! error under a width that cannot hold the value, and the exact result under one
//! that can.

use semi_persistent_egraph::extraction::asp::AspTarget;
use semi_persistent_egraph::extraction::graph::{Graph, Kind, Node, Term};
use semi_persistent_egraph::extraction::oint::{Build, OInt, SumMethod};
use semi_persistent_egraph::extraction::rung::Selection;
use semi_persistent_egraph::extraction::solve::{
    Outcome, Prepared, Solver, Status, cost_of, extract, solve_prepared,
};
use semi_persistent_egraph::extraction::target::{Cmp, CnfTarget, OpbTarget, Target};
use semi_persistent_egraph::extraction::{Cost, CostWidth, Lit};
use std::sync::Arc;

const SOLVER: Solver = Solver::Internal {
    max_solves: 100_000,
    max_conflicts: None,
};

fn node(op: &str, ints: Vec<i64>, children: Vec<usize>, class: usize) -> Node {
    Node {
        op: op.into(),
        ints: ints.into_iter().map(Cost::from).collect(),
        strings: vec![],
        children,
        mults: Vec::new(),
        class,
        kind: Kind::Plain,
        subsumed: false,
    }
}

/// Extract at `width` on `solver`.
fn extract_on(
    g: Arc<Graph>,
    cost: &dyn Fn(&Selection, &mut Build),
    width: CostWidth,
    solver: &Solver,
) -> Result<Outcome, String> {
    let mut prepared = Prepared::for_solver(solver);
    let (sel, rec) = {
        let mut b = Build::with_width(prepared.target(), width);
        let sel = Selection::build(g.clone(), &mut b);
        cost(&sel, &mut b);
        (sel, b.detach())
    };
    solve_prepared(&g, &sel, &rec, prepared, solver)
}

/// Extract at `width`.
fn extract_in(
    g: Arc<Graph>,
    cost: &dyn Fn(&Selection, &mut Build),
    width: CostWidth,
) -> Result<Outcome, String> {
    let mut prepared = Prepared::for_solver(&SOLVER);
    let (sel, rec) = {
        let mut b = Build::with_width(prepared.target(), width);
        let sel = Selection::build(g.clone(), &mut b);
        cost(&sel, &mut b);
        (sel, b.detach())
    };
    solve_prepared(&g, &sel, &rec, prepared, &SOLVER)
}

fn big(s: &str) -> Cost {
    Cost::parse(s).unwrap()
}

#[test]
fn cost_arithmetic_is_exact_across_the_i64_boundary() {
    let max = Cost::from(i64::MAX);
    let one = Cost::ONE;
    assert_eq!(max + one, big("9223372036854775808"));
    assert_eq!(max + one - one, max, "back inline");
    assert_eq!((max + one).to_i64(), None);
    assert_eq!((max + one).to_u64(), Some(1 << 63));
    assert_eq!(-Cost::from(i64::MIN), big("9223372036854775808"));
    assert_eq!(max * max, big("85070591730234615847396907784232501249"));
    assert!(max + one > max && -(max + one + one) < Cost::from(i64::MIN) && Cost::ZERO < max + one);
    assert_eq!((max + one).max(max), max + one);
    // Interned: equal values are equal handles, so hashing agrees.
    let a = max * Cost::from(3);
    let b = max + max + max;
    assert_eq!(a, b);
    let mut s = std::collections::HashSet::new();
    s.insert(a);
    assert!(s.contains(&b));
    assert_eq!(format!("{}", a), "27670116110564327421");
    assert_eq!((max + one).bits(), 64);
    assert!(
        CostWidth::W32.contains(Cost::from(i32::MAX))
            && !CostWidth::W32.contains(Cost::from(1i64 << 31))
    );
    assert!(CostWidth::W64.contains(max) && !CostWidth::W64.contains(max + one));
    assert!(CostWidth::Big.contains(a));
}

/// Bug #1: class 0 holds 4096 leaves of offsets 10000..=14095 and then one of offset
/// 0; the root holds a leaf of offset 5000 and `f(class 0)`. The 4,096-value cap
/// dropped the 0 and reported `Proved 5000` against the optimum 0.
#[test]
fn an_attribute_domain_is_complete_and_a_set_cap_is_an_error() {
    let mut g = Graph {
        nodes: vec![],
        classes: vec![vec![], vec![]],
        root: 1,
    };
    for o in (10000..10000 + 4096).chain([0]) {
        g.classes[0].push(g.nodes.len());
        g.nodes.push(node("x", vec![o], vec![], 0));
    }
    g.classes[1].push(g.nodes.len());
    g.nodes.push(node("y", vec![5000], vec![], 1));
    g.classes[1].push(g.nodes.len());
    g.nodes.push(node("f", vec![0], vec![0], 1));
    let g = Arc::new(g);
    let off = |n: &Node| n.ints[0];
    let cost = |r: &Selection, b: &mut Build| {
        let a = b.rec_max(r, &off);
        b.cost(a[r.graph.root].as_ref().unwrap());
    };
    let out = extract(g.clone(), |s, _| s, cost, &SOLVER).unwrap();
    assert_eq!(
        (out.status, out.cost),
        (Status::Proved, Some(Cost::ZERO)),
        "{:?}",
        out.warnings
    );
    let capped = |r: &Selection, b: &mut Build| {
        b.set_attribute_cap(Some(4096));
        cost(r, b);
    };
    let err = extract(g, |s, _| s, capped, &SOLVER).unwrap_err();
    assert!(err.contains("the cap set on the build"), "{err}");
}

/// Bug #6: `Future[0, i64::MAX]` nested. The u64 `v + off` in `domains` and the i64
/// one in `rec` wrapped (release without overflow checks: `Proved -2`).
#[test]
fn attribute_sums_past_i64_are_errors_at_64_bits_and_exact_unbounded() {
    for depth in [2usize, 3] {
        let mut g = Graph {
            nodes: vec![node("Var", vec![0, 0], vec![], 0)],
            classes: vec![vec![0]],
            root: 0,
        };
        for d in 1..=depth {
            g.classes.push(vec![d]);
            g.nodes
                .push(node("Future", vec![0, i64::MAX], vec![d - 1], d));
            g.root = d;
        }
        let g = Arc::new(g);
        let ub = |n: &Node| {
            if n.op == "Future" {
                n.ints[1]
            } else {
                Cost::ZERO
            }
        };
        let cost = |r: &Selection, b: &mut Build| {
            let a = b.rec_max(r, &ub);
            b.cost(a[r.graph.root].as_ref().unwrap());
        };
        let err = extract_in(g.clone(), &cost, CostWidth::W64).unwrap_err();
        assert!(
            err.contains("attribute") && err.contains("outside the 64-bit"),
            "{err}"
        );
        let out = extract_in(g, &cost, CostWidth::Big).unwrap();
        let want = Cost::from(i64::MAX) * Cost::from(depth);
        assert_eq!(out.cost, Some(want), "depth {depth}");
    }
}

/// Bug #5: the descent's bound plus the largest weight past the totalizer's cap
/// panicked in `WindowedSum::with_shape`; later it stopped `Bounded`. With exact
/// totalizer weights (`doc/goal-arbitrary-precision-costs.md`, step 1) it is proved:
/// the weights total 7 * 2^62 + 1, past u64, and the optimum is `a` at 6 * 2^62.
#[test]
fn an_objective_past_u64_is_proved_on_the_internal_solver() {
    let g = Arc::new(Graph {
        nodes: vec![
            node("a", vec![1 << 62], vec![], 0),
            node("b", vec![(1 << 62) + 1], vec![], 0),
        ],
        classes: vec![vec![0, 1]],
        root: 0,
    });
    let cost = |r: &Selection, b: &mut Build| {
        for (n, nd) in r.graph.nodes.iter().enumerate() {
            b.cost_if(r.node(n), nd.ints[0].to_u64().unwrap());
        }
        // Weights 2^62 each, five times: the total passes u64 as well (C14).
        for _ in 0..5 {
            b.cost_if(r.class(0), 1u64 << 62);
        }
    };
    let out = extract_in(g.clone(), &cost, CostWidth::Big).unwrap();
    assert_eq!(out.status, Status::Proved, "{:?}", out.warnings);
    assert_eq!(out.cost, Some(Cost::from(1u64 << 62) * Cost::from(6)));
    assert_eq!(out.term.unwrap().selection, vec![Some(0)]);
    // At 64 bits the same costs are outside the width: an error, not a wrapped cost.
    assert!(
        extract_in(g.clone(), &cost, CostWidth::W64)
            .unwrap_err()
            .contains("outside the 64-bit")
    );
    // DPW computes in rustsat's 64-bit integers: refused, naming it (must fail).
    let dpw = Solver::Dpw {
        max_solves: 100,
        max_conflicts: None,
    };
    let err = extract_on(g, &cost, CostWidth::Big, &dpw).unwrap_err();
    assert!(
        err.starts_with("dpw:") && err.contains("past the 64-bit"),
        "{err}"
    );
}

fn cost_in(
    g: &Arc<Graph>,
    cost: &dyn Fn(&Selection, &mut Build),
    t: &Term,
    width: CostWidth,
) -> Cost {
    let mut cnf = CnfTarget::default();
    let mut b = Build::with_width(&mut cnf, width);
    let sel = Selection::build(g.clone(), &mut b);
    cost(&sel, &mut b);
    semi_persistent_egraph::extraction::solve::interpret(&b, &sel, t, &|_| false).unwrap()
}

/// C1: two `Global[0, 2^62]` costs summed past i64 panicked with "the cost overflows".
#[test]
fn an_interpreted_cost_outside_the_width_is_an_error() {
    let g = Arc::new(Graph {
        nodes: vec![node("a", vec![], vec![], 0)],
        classes: vec![vec![0]],
        root: 0,
    });
    let cost = |_: &Selection, b: &mut Build| {
        b.cost_base(i64::MAX);
        b.cost_base(1);
    };
    let t = Term {
        selection: vec![Some(0)],
        trees: Default::default(),
    };
    // By default (no cap) the cost is exact; under the 64-bit cap it is an error.
    assert_eq!(
        cost_of(g.clone(), |s, _| s, cost, &t).unwrap(),
        big("9223372036854775808")
    );
    let err = {
        let mut cnf = CnfTarget::default();
        let mut b = Build::with_width(&mut cnf, CostWidth::W64);
        let sel = Selection::build(g.clone(), &mut b);
        cost(&sel, &mut b);
        semi_persistent_egraph::extraction::solve::interpret(&b, &sel, &t, &|_| false).unwrap_err()
    };
    assert!(
        err.starts_with("the cost") && err.contains("outside the 64-bit"),
        "{err}"
    );
    assert_eq!(
        cost_in(&g, &cost, &t, CostWidth::Big),
        big("9223372036854775808")
    );
    // The 32-bit width refuses at 2^31.
    let cost32 = |_: &Selection, b: &mut Build| b.cost_base(1i64 << 31);
    let mut cnf = CnfTarget::default();
    let mut b = Build::with_width(&mut cnf, CostWidth::W32);
    let sel = Selection::build(g.clone(), &mut b);
    cost32(&sel, &mut b);
    assert!(
        semi_persistent_egraph::extraction::solve::interpret(&b, &sel, &t, &|_| false)
            .unwrap_err()
            .contains("outside the 32-bit")
    );
}

/// A build error reaches the caller of `extract`: before, the public API ignored
/// `Detached.errors` and solved over placeholder values.
#[test]
fn extract_returns_the_build_errors() {
    let g = Arc::new(Graph {
        nodes: vec![node("a", vec![], vec![], 0)],
        classes: vec![vec![0]],
        root: 0,
    });
    // An integer with no values is a build error at every width.
    let cost = |_: &Selection, b: &mut Build| {
        let x = b.int::<i64>(&[]);
        b.cost(&x);
    };
    let err = extract(g, |s, _| s, cost, &SOLVER).unwrap_err();
    assert!(
        err.contains("int: an integer needs at least one value"),
        "{err}"
    );
}

/// C8, C6, C15, C12: the operator boundary cases, each a correct result or an error
/// naming the operation, never a wrap or a panic.
#[test]
fn operators_at_the_boundary() {
    let mut cnf = CnfTarget::default();
    let mut b = Build::with_width(&mut cnf, CostWidth::W64);
    let x = b.int(&[0, 5]);
    // `at_most(MAX)` holds of every integer: true, not an overflow.
    assert_eq!(x.at_most(i64::MAX), Lit::True);
    assert_eq!(x.at_least(Cost::from(i64::MAX) + Cost::ONE), Lit::False);
    // `scale` by 2^63 is outside 64 bits, and the values stay sorted.
    let s = b.scale(&x, 1u64 << 63);
    assert!(s.values().windows(2).all(|w| w[0] < w[1]));
    // A network sum near MAX.
    let hi = b.int(&[i64::MAX - 1, i64::MAX]);
    let lo = b.int(&[0, 1]);
    let _ = b.plus_by(&hi.clone().over(), &lo.clone().over(), SumMethod::Network);
    // A span past MAX_UNARY takes the pairwise encoding instead of the network.
    let wide = b.int(&[i64::MIN + 1, i64::MAX]);
    let _: OInt<_> = b.plus_by(&wide, &lo, SumMethod::Network);
    let errors = b.detach().errors;
    assert!(errors.iter().any(|e| e.starts_with("scale")), "{errors:?}");
    assert!(errors.iter().any(|e| e.starts_with("plus")), "{errors:?}");
    assert!(
        !errors.iter().any(|e| e.contains("unit expansion")),
        "{errors:?}"
    );
}

/// C16: a constraint with an `i64::MIN` coefficient negated without overflow, and
/// its models those of brute force.
#[test]
fn a_minimum_coefficient_is_normalized_exactly() {
    let mut cnf = CnfTarget::default();
    let v = cnf.fresh();
    // MIN·v >= 0 holds exactly when v is false.
    cnf.pb(&[(Cost::from(i64::MIN), v)], Cmp::Ge, Cost::ZERO)
        .unwrap();
    assert_eq!(cnf.sink.clauses, vec![vec![v.not()]]);
    // The OPB text of a coefficient past i64 is exact.
    let mut opb = OpbTarget::default();
    let w = opb.fresh();
    opb.pb(&[(Cost::from(i64::MIN), w)], Cmp::Le, Cost::from(i64::MIN))
        .unwrap();
    let text = opb.to_opb(&[]);
    assert!(
        text.contains("+9223372036854775808 x1 >= 9223372036854775808 ;"),
        "{text}"
    );
}

/// C3: a weight past clingo's 32-bit integers was written and wrapped (clingo 5.8.2
/// reports `Proved 3000000000` against the optimum 5). Now the ASP target refuses it.
#[test]
fn the_asp_target_refuses_what_clingo_would_wrap() {
    let mut asp = AspTarget::default();
    let v = asp.fresh();
    let err = asp.objective(Cost::from(3_000_000_000u64), v).unwrap_err();
    assert!(err.contains("clingo's 32-bit"), "{err}");
    assert!(asp.objective(Cost::from(5), v).is_ok());
    let err = asp
        .pb(&[(Cost::from(1i64 << 31), v)], Cmp::Ge, Cost::ONE)
        .unwrap_err();
    assert!(err.contains("clingo's 32-bit"), "{err}");
    // A payload integer past them is refused before clingo runs (C2).
    let g = Graph {
        nodes: vec![node("Global", vec![0, 3_000_000_000], vec![], 0)],
        classes: vec![vec![0]],
        root: 0,
    };
    assert!(
        semi_persistent_egraph::extraction::lp::fits_clingo(&g)
            .unwrap_err()
            .contains("3000000000")
    );
}

/// C17: summed multiplicities past u64 were an overflow panic in `coalesce`.
#[test]
fn coalesce_reports_a_count_past_u64() {
    let mut g = Graph {
        nodes: vec![node("x", vec![], vec![], 0)],
        classes: vec![vec![0], vec![1]],
        root: 1,
    };
    let mut n = node("Add", vec![], vec![0, 0], 1);
    n.kind = Kind::MSet;
    n.mults = vec![u64::MAX, 1];
    g.nodes.push(n);
    assert!(g.coalesce().unwrap_err().contains("past u64"));
}

/// An empty integer was an assert panic (reachable from Roto's `g.int([])`).
#[test]
fn an_integer_with_no_values_is_an_error() {
    let mut cnf = CnfTarget::default();
    let mut b = Build::new(&mut cnf);
    let x = b.int::<i64>(&[]);
    assert_eq!(x.values(), &[0]);
    assert!(b.detach().errors.iter().any(|e| e.starts_with("int")));
}

/// Each solver's integer range, as measured (`tests/data/solver_width/README.md`).
#[test]
fn solver_ranges_are_inferred_from_the_command() {
    use semi_persistent_egraph::extraction::solve::{OpbCommand, SolverRange};
    assert_eq!(
        OpbCommand::new("/home/x/.local/bin/roundingsat").opb_range(),
        SolverRange::Unbounded
    );
    assert_eq!(OpbCommand::new("clasp").opb_range(), SolverRange::I32);
    assert_eq!(
        OpbCommand::new("some-pb-solver").opb_range(),
        SolverRange::I64
    );
    let mzn = |s: &str| {
        OpbCommand::new("minizinc")
            .arg("--solver")
            .arg(s)
            .mzn_range()
    };
    assert_eq!(mzn("chuffed"), SolverRange::I32);
    assert_eq!(mzn("gecode"), SolverRange::I32);
    assert_eq!(mzn("coinbc"), SolverRange::Exact53);
    assert_eq!(mzn("highs"), SolverRange::Exact53);
    assert_eq!(mzn("cp-sat"), SolverRange::I64);
    assert!(
        SolverRange::Exact53.contains(Cost::from(1i64 << 53))
            && !SolverRange::Exact53.contains(Cost::from((1i64 << 53) + 1))
    );
    assert!(
        SolverRange::I32.contains(Cost::from(i32::MIN))
            && !SolverRange::I32.contains(Cost::from(1i64 << 31))
    );
}

/// clasp reads an OPB weight of 2^70 as 0 and reports a wrong optimum without an error
/// (`tests/data/solver_width/opb_big_objective.opb`). The OPB path refuses a weight past
/// the solver's range before writing it; the solver never runs.
#[test]
fn an_opb_weight_past_the_solvers_range_is_refused() {
    use semi_persistent_egraph::extraction::solve::OpbCommand;
    let g = Arc::new(Graph {
        nodes: vec![node("a", vec![], vec![], 0), node("b", vec![], vec![], 0)],
        classes: vec![vec![0, 1]],
        root: 0,
    });
    let cost = |r: &Selection, b: &mut Build| {
        b.cost_if(r.node(0), 1u64 << 40);
        b.cost_if(r.node(1), 5);
    };
    let clasp = Solver::Opb(OpbCommand::new("clasp"));
    let err = extract(g, |s, _| s, cost, &clasp).unwrap_err();
    assert!(
        err.contains("clasp's 32-bit") && err.contains("1099511627776"),
        "{err}"
    );
}

/// Chuffed picks a 2^40 term over one of cost 5 (`tests/data/solver_width/mzn_2_40.mzn`).
/// The MiniZinc dump refuses an integer past the named solver's range.
#[test]
fn a_minizinc_value_past_the_solvers_range_is_refused() {
    use semi_persistent_egraph::extraction::solve::OpbCommand;
    let g = Graph {
        nodes: vec![node("Global", vec![0, 1 << 40], vec![], 0)],
        classes: vec![vec![0]],
        root: 0,
    };
    let chuffed = OpbCommand::new("minizinc").arg("--solver").arg("chuffed");
    let err = semi_persistent_egraph::extraction::mzn::fits_minizinc(&g, &chuffed).unwrap_err();
    assert!(err.contains("chuffed's 32-bit"), "{err}");
    let cpsat = OpbCommand::new("minizinc").arg("--solver").arg("cp-sat");
    assert!(semi_persistent_egraph::extraction::mzn::fits_minizinc(&g, &cpsat).is_ok());
}

/// Step 2 of `doc/goal-arbitrary-precision-costs.md`: attribute offsets are exact. Three
/// nested nodes with offset 2^63 each make the attribute 3 * 2^63, past u64; it is proved
/// on the internal solver, whose totalizer then runs on exact weights.
#[test]
fn attribute_offsets_past_u64_are_proved_exactly() {
    let big = Cost::from(1u64 << 63);
    let mut g = Graph {
        nodes: vec![node("leaf", vec![], vec![], 0)],
        classes: vec![vec![0]],
        root: 0,
    };
    for d in 1..=3 {
        g.classes.push(vec![d]);
        g.nodes.push(node("f", vec![], vec![d - 1], d));
        g.root = d;
    }
    let g = Arc::new(g);
    let off = move |n: &Node| if n.op == "f" { big } else { Cost::ZERO };
    let cost = move |r: &Selection, b: &mut Build| {
        let a = b.rec_max(r, &off);
        b.cost(a[r.graph.root].as_ref().unwrap());
    };
    let out = extract_in(g, &cost, CostWidth::Big).unwrap();
    assert_eq!(
        (out.status, out.cost),
        (Status::Proved, Some(big * Cost::from(3)))
    );
}
