// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! The engine's sequence-rule matches against the reference matcher (`seq_ref`), on
//! random e-graphs and random patterns (`doc/goal-sequence-patterns.md`, steps 2 to 4).
//!
//! Each case is a Semper program: declarations, `let` terms, and one sequence rule.
//! It is parsed and checked by Semper, its terms are added by the interpreter, and
//! then, at every node of the rule's root operator, the engine's matches
//! (`collection::matches_at`) and the reference's (`seq_ref::match_node`, over the
//! same e-graph read back as classes of members) must be the same multiset of
//! bindings. The reference pattern is read from the parser's surface syntax, not
//! from the engine's checked rule.

mod seq_ref;

use semi_persistent_egraph::collection;
use semi_persistent_egraph::interpret::Interpreter;
use semi_persistent_egraph::model::{MachineLit, MachineModel};
use semi_persistent_egraph::multiplicity::MultiplicityLike;
use semi_persistent_egraph::registry::OpKind;
use semi_persistent_egraph::sortcheck::CCommand;
use semi_persistent_egraph::surface_ast::{SurfaceCommand, SurfacePatChild, SurfacePattern};
use seq_ref::{Env, Graph, Item, Kind, Member, Pat, Val};
use std::collections::BTreeMap;

type Cfg = semi_persistent_egraph::nodes::DefaultConfig;
type Interp = Interpreter<Cfg, MachineLit, MachineModel, true, false>;

/// A small deterministic generator, so a failing case is reproducible from its seed.
struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.0 >> 33
    }
    fn below(&mut self, n: usize) -> usize {
        (self.next() % n as u64) as usize
    }
    fn pick<'a, T>(&mut self, xs: &'a [T]) -> &'a T {
        &xs[self.below(xs.len())]
    }
}

/// A multiplicity annotation as the reference's interval: Semper design §7.5's
/// table (`:k` any, `>=`, `>`, `<=`, `<`, `==` bounds; `!=` an excluded value).
fn ref_mult(m: &semi_persistent_egraph::ast::MultSpec) -> seq_ref::Mult {
    use semi_persistent_egraph::ast::{CmpOp, MultSpec};
    match m {
        MultSpec::Exact(n) => seq_ref::Mult::exact(*n),
        MultSpec::Var { name, constraint } => {
            let mut r = seq_ref::Mult::var(name);
            match constraint {
                None => {}
                Some((CmpOp::Ge, n)) => r.lo = r.lo.max(*n),
                Some((CmpOp::Gt, n)) => r.lo = r.lo.max(n.saturating_add(1)),
                Some((CmpOp::Le, n)) => r.hi = *n,
                Some((CmpOp::Lt, n)) => r.hi = n.saturating_sub(1),
                Some((CmpOp::Eq, n)) => {
                    r.lo = r.lo.max(*n);
                    r.hi = *n;
                }
                Some((CmpOp::Ne, n)) => r.ne = Some(*n),
            }
            r
        }
    }
}

/// The surface pattern as the reference's pattern.
fn to_ref(p: &SurfacePattern) -> Pat {
    match p {
        SurfacePattern::Var(v, _) => Pat::Var(v.clone()),
        SurfacePattern::Lit(t, _) => Pat::Lit(t.trim_matches('"').to_string()),
        SurfacePattern::App {
            op,
            prefix,
            children,
            suffix,
            ..
        } => {
            let mut items = Vec::new();
            if let Some((n, _)) = prefix {
                items.push(Item::Bare(n.clone()));
            }
            for c in children {
                items.push(match c {
                    SurfacePatChild::Elem(p) => Item::One(to_ref(p), None),
                    SurfacePatChild::ElemMult(p, m) => Item::One(to_ref(p), Some(ref_mult(m))),
                    SurfacePatChild::Seq(n, _) => Item::Bare(n.clone()),
                    SurfacePatChild::Filter {
                        name,
                        mult,
                        base,
                        except,
                        ..
                    } => Item::Filter {
                        name: name.clone(),
                        base: to_ref(base),
                        except: except.as_ref().map(|(n, _)| n.clone()),
                        mult: mult.as_ref().map(ref_mult),
                    },
                });
            }
            if let Some((n, _)) = suffix {
                items.push(Item::Bare(n.clone()));
            }
            Pat::App(op.clone(), items)
        }
    }
}

/// The interpreter's e-graph read back as the reference's classes of members, each
/// class at the index of its representative.
fn to_graph(it: &Interp, globals: &[&str]) -> Graph {
    let eg = &it.eg;
    let mut g = Graph::default();
    let live = |n| eg.node_flags(n) & semi_persistent_egraph::node_types::FLAG_SUBSUMED == 0;
    for n in eg.node_ids() {
        if !live(n) {
            continue;
        }
        let c = eg.class_repr(n).to_usize();
        if g.classes.len() <= c {
            g.classes.resize(c + 1, Vec::new());
        }
        let mut kids = Vec::new();
        let mut mults = Vec::new();
        eg.for_each_child(n, |k, m| {
            kids.push(eg.class_repr(k).to_usize());
            mults.push(u64::try_from(m.to_usize()).expect("a multiplicity within 64 bits"));
        });
        let op = eg.node_op_name(n).to_string();
        let lit = eg.get_lit_val(n).map(|l| l.to_string());
        let o = eg.node_op(n);
        let kind = match eg.ops().info(o).kind {
            OpKind::Set { .. } => Kind::Aci,
            OpKind::MSet { .. } => Kind::Ac,
            OpKind::A { .. } => Kind::Assoc,
            _ => Kind::Plain,
        };
        if kind != Kind::Ac {
            mults.clear();
        }
        g.kinds.insert(op.clone(), kind);
        if kind != Kind::Plain {
            let l = eg.nary_laws(o);
            g.laws.insert(
                op.clone(),
                semi_persistent_egraph::nary_canon::NaryLaws {
                    kind: l.kind,
                    unit: eg.unit_node(o).map(|u| eg.class_repr(u).to_usize()),
                    inverse: l.inverse.map(|i| eg.ops().info(i).name.clone()),
                },
            );
        }
        g.classes[c].push(Member {
            op,
            kids,
            mults,
            lit,
        });
    }
    for name in globals {
        let (_, _, class) = it.globals().get(name).expect("a declared global");
        g.globals
            .insert(name.to_string(), eg.class_repr(class).to_usize());
    }
    g
}

fn render(g: &Graph, v: &Val) -> String {
    match v {
        Val::Class(c) => match g.classes[*c].iter().find_map(|m| m.lit.clone()) {
            Some(l) => l,
            None => format!("c{c}"),
        },
        Val::Int(n) => n.to_string(),
        Val::Seq(s) => format!(
            "[{}]",
            s.iter()
                .map(|x| render(g, x))
                .collect::<Vec<_>>()
                .join(", ")
        ),
    }
}

/// Runs `program` and compares the engine with the reference at every root node.
/// Returns the number of nodes compared, the number of matches, and the number of
/// nodes with more than one match (where enumeration, not a single choice, decides).
fn compare(program: &str, globals: &[&str]) -> (usize, usize, usize) {
    let cmds = semi_persistent_egraph::parser::parse_program_v2(program)
        .unwrap_or_else(|e| panic!("parse: {e}\n{program}"));
    let (lhs, flatten) = cmds
        .iter()
        .find_map(|c| {
            if let SurfaceCommand::CollectionRewrite(r) = c {
                Some((r.lhs.clone(), r.flatten))
            } else {
                None
            }
        })
        .expect("a sequence rule");
    let mut it: Interp = Interpreter::new(MachineModel);
    let mut sg = semi_persistent_egraph::resolve::GlobalCtx::new();
    let checked =
        semi_persistent_egraph::sortcheck::sortcheck_program(cmds, &mut it.eg, &it.model, &mut sg)
            .unwrap_or_else(|e| panic!("sortcheck: {e}\n{program}"));
    it.run_checked(&checked)
        .unwrap_or_else(|e| panic!("run: {e}\n{program}"));
    let rule = checked
        .iter()
        .find_map(|c| {
            if let CCommand::CollectionRule(r) = c {
                Some(r.clone())
            } else {
                None
            }
        })
        .expect("a checked sequence rule");
    let g = to_graph(&it, globals);
    let Pat::App(op, items) = to_ref(&lhs) else {
        panic!("the left-hand side is an application")
    };
    let (mut nodes, mut total, mut multi) = (0, 0, 0);
    for n in it.eg.node_ids() {
        if it.eg.node_op(n) != rule.root_op()
            || it.eg.node_flags(n) & semi_persistent_egraph::node_types::FLAG_SUBSUMED != 0
        {
            continue;
        }
        nodes += 1;
        let mut engine = collection::matches_at(&it.eg, &it.model, it.globals(), &rule, n);
        let mut kids = Vec::new();
        it.eg.for_each_child(n, |k, m| {
            kids.push((
                it.eg.class_repr(k).to_usize(),
                u64::try_from(m.to_usize()).expect("a multiplicity within 64 bits"),
            ))
        });
        // Under `:flatten` the node's matches are its views' (task 4 of
        // `doc/goal-flatten-and-engine-completion.md`).
        let want = if flatten {
            let flat = seq_ref::match_flattened(&g, &op, &items, &kids, &Env::new());
            if flat != seq_ref::match_children(&g, &op, &items, &kids, &Env::new()) {
                FLAT_CHANGED.set(FLAT_CHANGED.get() + 1);
            }
            flat
        } else {
            seq_ref::match_children(&g, &op, &items, &kids, &Env::new())
        };
        let mut reference: Vec<BTreeMap<String, String>> = want
            .iter()
            .map(|e| e.iter().map(|(k, v)| (k.clone(), render(&g, v))).collect())
            .collect();
        engine.sort();
        reference.sort();
        assert_eq!(
            engine, reference,
            "node {n:?} (children {kids:?})\n{program}"
        );
        // Steps 4 and 5: the relational engine gives the same under every plan: the cost
        // model's choice, the root drive, and the filter drive with each access path;
        // statically and with runtime scheduling (which `Collect` queries decline, so it
        // must not change them). These programs have no guards, so nothing is required
        // non-empty and part 2 always runs: the match *sets* must be equal.
        use semi_persistent_egraph::seq_engine::{Access, Drive, set_plan_override};
        for plan in [
            None,
            Some((Drive::Root, Access::Probe)),
            Some((Drive::Filters, Access::Probe)),
            Some((Drive::Filters, Access::Materialize)),
        ] {
            for runtime in [false, true] {
                set_plan_override(plan);
                semi_persistent_egraph::ematch::set_runtime_scheduling(runtime);
                let mut relational =
                    semi_persistent_egraph::seq_engine::matches_at(&it.eg, it.globals(), &rule, n);
                set_plan_override(None);
                semi_persistent_egraph::ematch::set_runtime_scheduling(false);
                relational.sort();
                assert_eq!(
                    relational, reference,
                    "relational engine, plan {plan:?}, runtime scheduling {runtime}, node {n:?} \
                     (children {kids:?})\n{program}"
                );
            }
        }
        total += engine.len();
        multi += usize::from(engine.len() > 1);
    }
    check_subqueries(&it, &rule, &g, &items);
    (nodes, total, multi)
}

thread_local! {
    /// Root nodes whose flattened matches differ from their stored children's, for the
    /// test running on this thread: the evidence that nesting was exercised.
    static FLAT_CHANGED: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

thread_local! {
    /// Step 3's tallies for the test running on this thread: classes probed, rows.
    static SUBQ: std::cell::Cell<(usize, usize)> = const { std::cell::Cell::new((0, 0)) };
}

/// Step 3 of `doc/goal-sequence-patterns-engine.md`: each filter's sub-query
/// (`crate::seq_query`). At every child class of every root node, the bound-root
/// plan's rows equal the reference's matches of the filter's base at that class; and
/// the free-root plan's rows, grouped by class, equal the bound-root rows of each
/// class they name, and name every class whose bound-root rows are not empty.
fn check_subqueries(
    it: &Interp,
    rule: &collection::Rule<
        <Cfg as semi_persistent_egraph::config::EGraphConfig>::O,
        <Cfg as semi_persistent_egraph::config::EGraphConfig>::S,
        MachineLit,
    >,
    g: &Graph,
    items: &[Item],
) {
    use semi_persistent_egraph::seq_query::RowVal;
    let bases: Vec<&Pat> = items
        .iter()
        .filter_map(|i| {
            if let Item::Filter { base, .. } = i {
                Some(base)
            } else {
                None
            }
        })
        .collect();
    assert_eq!(
        bases.len(),
        rule.filter_queries.len(),
        "one sub-query per filter"
    );
    let store = semi_persistent_egraph::index::IndexStore::build(&it.eg);
    let index = semi_persistent_egraph::index::VariantIndex::naive(&store);
    let mut pool = semi_persistent_egraph::ematch::MatchPool::new();
    let stats = semi_persistent_egraph::schedule::IndexStats::new();
    let lit = |v| it.eg.lits().get(v).to_string();
    let mut children: Vec<usize> = Vec::new();
    for n in it.eg.node_ids() {
        if it.eg.node_op(n) == rule.root_op() {
            it.eg
                .for_each_child(n, |k, _| children.push(it.eg.class_repr(k).to_usize()));
        }
    }
    children.sort_unstable();
    children.dedup();
    let (mut probes, mut rows) = SUBQ.get();
    for (sq, base) in rule.filter_queries.iter().zip(bases) {
        let plans =
            sq.plans::<<Cfg as semi_persistent_egraph::config::EGraphConfig>::Index>(&stats);
        let names: Vec<&String> = sq.vars.iter().map(|(n, _)| n).collect();
        let render_row = |vals: &[RowVal<_, _>]| -> BTreeMap<String, String> {
            names
                .iter()
                .zip(vals)
                .map(|(n, v)| {
                    let s = match *v {
                        RowVal::Class(c) => render(
                            g,
                            &Val::Class(semi_persistent_egraph::containers::DenseId::to_usize(c)),
                        ),
                        RowVal::Lit(l) => lit(l),
                    };
                    ((*n).clone(), s)
                })
                .collect()
        };
        let mut bound_at: BTreeMap<usize, Vec<BTreeMap<String, String>>> = BTreeMap::new();
        let probe = |c: usize,
                     pool: &mut semi_persistent_egraph::ematch::MatchPool<Cfg>|
         -> Vec<BTreeMap<String, String>> {
            let class = it
                .eg
                .node_ids()
                .find(|&m| it.eg.class_repr(m).to_usize() == c)
                .map(|m| it.eg.class_repr(m))
                .expect("a class");
            let mut got: Vec<BTreeMap<String, String>> = plans
                .probe(&it.eg, &index, it.globals(), pool, class)
                .iter()
                .map(|r| render_row(&r.vals))
                .collect();
            got.sort();
            got
        };
        for &c in &children {
            let got = probe(c, &mut pool);
            let mut want: Vec<BTreeMap<String, String>> =
                seq_ref::match_class(g, base, c, &Env::new())
                    .iter()
                    .map(|e| e.iter().map(|(k, v)| (k.clone(), render(g, v))).collect())
                    .collect();
            want.sort();
            want.dedup();
            assert_eq!(got, want, "bound-root rows at c{c}, base {base:?}");
            probes += 1;
            rows += got.len();
            bound_at.insert(c, got);
        }
        let Some(all) = plans.all(&it.eg, &index, it.globals(), &mut pool) else {
            continue;
        };
        let mut by_class: BTreeMap<usize, Vec<BTreeMap<String, String>>> = BTreeMap::new();
        for (c, r) in &all {
            by_class
                .entry(semi_persistent_egraph::containers::DenseId::to_usize(*c))
                .or_default()
                .push(render_row(&r.vals));
        }
        for (c, got) in by_class.iter_mut() {
            got.sort();
            let want = match bound_at.get(c) {
                Some(w) => w.clone(),
                None => probe(*c, &mut pool),
            };
            assert_eq!(*got, want, "free-root rows at c{c}, base {base:?}");
        }
        for (c, b) in &bound_at {
            assert!(
                b.is_empty() || by_class.contains_key(c),
                "free-root rows miss c{c}, base {base:?}"
            );
        }
    }
    SUBQ.set((probes, rows));
}

const DECLS: &str = "(sort E)
(function a () E)
(function b () E)
(function c () E)
(function F (E) E)
(function G (E) E)
(function H (E) E)
(function K (E E) E)
(function And (E) E :assoc-comm-idem)
(let ga a)
";

const TERMS: &[&str] = &[
    "a",
    "b",
    "c",
    "(F a)",
    "(F b)",
    "(F (G b))",
    "(G a)",
    "(G (F a))",
    "(H c)",
    "(H a)",
    "(K a b)",
    "(K b b)",
    "(K a a)",
];

/// Filter patterns by head operator; `{i}` is replaced by the filter's index so
/// that variables are distinct across filters.
const BASES: &[(&str, &[&str])] = &[
    ("F", &["(F x{i})", "(F ga)", "(F (G y{i}))"]),
    ("G", &["(G x{i})", "(G ga)"]),
    ("H", &["(H x{i})"]),
    ("K", &["(K x{i} y{i})", "(K x{i} x{i})", "(K ga y{i})"]),
];

/// Step 2: filters with distinct head operators over classes of one member each, so
/// no child matches two filters and no class has two matching members; with and
/// without a bare sequence. On these the engine's first-match rule and the
/// reference's enumeration must agree.
#[test]
fn step2_distinct_heads_single_members() {
    let mut rng = Rng(0x5e9c_0de2);
    let (mut cases, mut nodes, mut matches, mut multi) = (0, 0, 0, 0);
    for _ in 0..400 {
        let nf = 1 + rng.below(3);
        let mut heads: Vec<usize> = (0..BASES.len()).collect();
        for i in (1..heads.len()).rev() {
            heads.swap(i, rng.below(i + 1));
        }
        let mut lhs = String::from("(And");
        for (i, &h) in heads.iter().take(nf).enumerate() {
            let base = rng.pick(BASES[h].1).replace("{i}", &i.to_string());
            lhs.push_str(&format!(" (..g{i} {base})"));
        }
        let bare = rng.below(2) == 0;
        if bare {
            lhs.push_str(" ..rest");
        }
        lhs.push(')');
        let mut prog = String::from(DECLS);
        for t in 0..4 {
            let k = 1 + rng.below(5);
            let kids: Vec<&str> = (0..k).map(|_| *rng.pick(TERMS)).collect();
            prog.push_str(&format!("(let e{t} (And {}))\n", kids.join(" ")));
        }
        prog.push_str(&format!("(rewrite {lhs} (And ..g0))\n"));
        let (n, m, x) = compare(&prog, &["ga"]);
        cases += 1;
        nodes += n;
        matches += m;
        multi += x;
    }
    eprintln!(
        "step 2: {cases} programs, {nodes} root nodes, {matches} matches ({multi} nodes with several), engine = reference"
    );
    let (probes, rows) = SUBQ.get();
    eprintln!(
        "  sub-queries: {probes} filter probes at child classes, {rows} rows, bound-root = reference = free-root grouped"
    );
    assert!(probes > 0, "no filter probed");
    assert!(matches > 100, "too few matches to mean anything: {matches}");
}

/// Step 3 (AC and ACI): overlapping filters (heads may repeat), classes of several
/// members (`union` merges terms), `:except`, and simple items beside filters, with
/// and without a bare sequence.
#[test]
fn step3_aci_overlap_members_simple_items() {
    let mut rng = Rng(0x5e9c_0de3);
    let (mut cases, mut nodes, mut matches, mut multi) = (0, 0, 0, 0);
    let simple_items = std::env::var_os("SEQ_STEP3_NO_SIMPLE").is_none();
    for _ in 0..2000 {
        let nf = 1 + rng.below(3);
        let mut lhs = String::from("(And");
        let mut names = Vec::new();
        for i in 0..nf {
            let h = rng.below(BASES.len());
            let base = rng.pick(BASES[h].1).replace("{i}", &i.to_string());
            let except = if i > 0 && rng.below(4) == 0 {
                format!(" :except g{}", rng.below(i))
            } else {
                String::new()
            };
            lhs.push_str(&format!(" (..g{i} {base}{except})"));
            names.push(format!("g{i}"));
        }
        if simple_items {
            for j in 0..rng.below(3) {
                let s = *rng.pick(&["s{j}", "(F s{j})", "(G ga)", "(K s{j} t{j})", "a"]);
                lhs.push_str(&format!(" {}", s.replace("{j}", &j.to_string())));
            }
        }
        if rng.below(2) == 0 {
            lhs.push_str(" ..rest");
        }
        lhs.push(')');
        let mut prog = String::from(DECLS);
        for t in 0..4 {
            let k = 1 + rng.below(5);
            let kids: Vec<&str> = (0..k).map(|_| *rng.pick(TERMS)).collect();
            prog.push_str(&format!("(let e{t} (And {}))\n", kids.join(" ")));
        }
        // Merges give classes of several members, and children matching several filters.
        for _ in 0..rng.below(4) {
            prog.push_str(&format!(
                "(union {} {})\n",
                rng.pick(TERMS),
                rng.pick(TERMS)
            ));
        }
        prog.push_str(&format!("(rewrite {lhs} (And ..g0))\n"));
        let (n, m, x) = compare(&prog, &["ga"]);
        cases += 1;
        nodes += n;
        matches += m;
        multi += x;
    }
    eprintln!(
        "step 3: {cases} programs, {nodes} root nodes, {matches} matches ({multi} nodes with several), engine = reference"
    );
    let (probes, rows) = SUBQ.get();
    eprintln!(
        "  sub-queries: {probes} filter probes at child classes, {rows} rows, bound-root = reference = free-root grouped"
    );
    assert!(probes > 0, "no filter probed");
    assert!(
        matches > 1000,
        "too few matches to mean anything: {matches}"
    );
    assert!(
        multi > 200,
        "too few nodes where enumeration decides: {multi}"
    );
}

const A_DECLS: &str = "(sort E)
(function a () E)
(function b () E)
(function c () E)
(function F (E) E)
(function G (E) E)
(function H (E) E)
(function K (E E) E)
(function Mk () E)
(function Cat (E) E :assoc)
(function Lf (E) E :assoc-left)
(function Rf (E) E :assoc-right)
(let ga a)
";

/// Step 4 (A and folds): runs, gaps at the ends, in the middle, and adjacent,
/// simple items beside them, classes of several members; the root is `:assoc`, a
/// left fold, or a right fold.
#[test]
fn step4_assoc_runs_gaps_simple_items() {
    let mut rng = Rng(0x5e9c_0de4);
    let (mut cases, mut nodes, mut matches, mut multi) = (0, 0, 0, 0);
    // Gaps at both ends, a gap in the middle, adjacent gaps, runs beside simple items, a fold root.
    let mut shapes = [0usize; 5];
    for _ in 0..2000 {
        let root = *rng.pick(&["Cat", "Cat", "Lf", "Rf"]);
        let mut lhs = format!("({root}");
        let n_items = 1 + rng.below(4);
        let (mut runs, mut gaps, mut ones) = (0usize, 0usize, 0usize);
        for _ in 0..n_items {
            match rng.below(3) {
                0 => {
                    let h = rng.below(BASES.len());
                    let base = rng.pick(BASES[h].1).replace("{i}", &runs.to_string());
                    lhs.push_str(&format!(" (..g{runs} {base})"));
                    runs += 1;
                }
                1 => {
                    lhs.push_str(&format!(" ..m{gaps}"));
                    gaps += 1;
                }
                _ => {
                    let s = *rng.pick(&["s{j}", "(F s{j})", "(G ga)", "(K s{j} t{j})", "a"]);
                    lhs.push_str(&format!(" {}", s.replace("{j}", &ones.to_string())));
                    ones += 1;
                }
            }
        }
        if rng.below(2) == 0 {
            lhs.push_str(&format!(" ..m{gaps}"));
        }
        lhs.push(')');
        // A pattern whose only gaps are its first or last child and has no run is an
        // ordinary A pattern, which the ordinary matcher handles (the next test).
        let surface = semi_persistent_egraph::parser::parse_program_v2(&format!(
            "{A_DECLS}(rewrite {lhs} ({root} (a) (b)))"
        ))
        .expect("parse");
        if !surface
            .iter()
            .any(|c| matches!(c, SurfaceCommand::CollectionRewrite(_)))
        {
            continue;
        }
        let mut prog = String::from(A_DECLS);
        for t in 0..4 {
            let k = 2 + rng.below(5);
            let kids: Vec<&str> = (0..k).map(|_| *rng.pick(TERMS)).collect();
            prog.push_str(&format!("(let e{t} ({root} {}))\n", kids.join(" ")));
        }
        for _ in 0..rng.below(4) {
            prog.push_str(&format!(
                "(union {} {})\n",
                rng.pick(TERMS),
                rng.pick(TERMS)
            ));
        }
        prog.push_str(&format!("(rewrite {lhs} ({root} (a) (b)))\n"));
        // Which of the shapes the goal names this case has.
        let toks: Vec<&str> = lhs
            .trim_start_matches('(')
            .trim_end_matches(')')
            .split_whitespace()
            .skip(1)
            .collect();
        let gap = |t: &str| t.starts_with("..m");
        let n_t = toks.len();
        if n_t >= 2 && gap(toks[0]) && gap(toks[n_t - 1]) {
            shapes[0] += 1;
        }
        if toks
            .iter()
            .enumerate()
            .any(|(i, t)| gap(t) && i > 0 && i + 1 < n_t)
        {
            shapes[1] += 1;
        }
        if toks.windows(2).any(|w| gap(w[0]) && gap(w[1])) {
            shapes[2] += 1;
        }
        if runs > 0 && ones > 0 {
            shapes[3] += 1;
        }
        if root != "Cat" {
            shapes[4] += 1;
        }
        let (n, m, x) = compare(&prog, &["ga"]);
        cases += 1;
        nodes += n;
        matches += m;
        multi += x;
    }
    eprintln!(
        "step 4: {cases} programs, {nodes} root nodes, {matches} matches ({multi} nodes with several), engine = reference"
    );
    let (probes, rows) = SUBQ.get();
    eprintln!(
        "  sub-queries: {probes} filter probes at child classes, {rows} rows, bound-root = reference = free-root grouped"
    );
    assert!(probes > 0, "no filter probed");
    eprintln!(
        "step 4 shapes: both-end gaps {}, middle gap {}, adjacent gaps {}, runs beside simple items {}, fold roots {}",
        shapes[0], shapes[1], shapes[2], shapes[3], shapes[4]
    );
    assert!(
        shapes.iter().all(|&k| k >= 50),
        "a named shape is under-represented: {shapes:?}"
    );
    assert!(
        matches > 1000,
        "too few matches to mean anything: {matches}"
    );
    assert!(
        multi > 200,
        "too few nodes where enumeration decides: {multi}"
    );
}

/// Step 4: for patterns with gaps only at the ends and no runs (today's A patterns),
/// the sequence engine finds the same match windows as the ordinary matcher. The
/// ordinary rewrite `(Cat ..pre ITEMS ..suf) => (Cat ..pre Mk ITEMS ..suf)` marks
/// each window it matches with `Mk`; after one round, the positions of `Mk` among the
/// new members of each node's class are the ordinary matcher's windows, which must
/// equal the lengths of `pre` over the sequence engine's matches on the same pattern.
#[test]
fn step4_ordinary_a_forms_match_the_ordinary_matcher() {
    let mut rng = Rng(0x5e9c_0de5);
    let (mut cases, mut windows) = (0, 0);
    for _ in 0..600 {
        let pre = rng.below(2) == 0;
        let suf = rng.below(2) == 0;
        let k = 1 + rng.below(3);
        let items: Vec<String> = (0..k)
            .map(|j| {
                rng.pick(&["s{j}", "(F s{j})", "(G ga)", "(K s{j} t{j})"])
                    .replace("{j}", &j.to_string())
            })
            .collect();
        let lhs = format!(
            "(Cat{}{}{})",
            if pre { " ..pre" } else { "" },
            items.iter().map(|i| format!(" {i}")).collect::<String>(),
            if suf { " ..suf" } else { "" }
        );
        let rhs = format!(
            "(Cat{} (Mk){}{})",
            if pre { " ..pre" } else { "" },
            items.iter().map(|i| format!(" {i}")).collect::<String>(),
            if suf { " ..suf" } else { "" }
        );
        let mut prog = String::from(A_DECLS);
        let mut roots = Vec::new();
        for t in 0..3 {
            let n = 2 + rng.below(4);
            let kids: Vec<&str> = (0..n).map(|_| *rng.pick(TERMS)).collect();
            prog.push_str(&format!("(let e{t} (Cat {}))\n", kids.join(" ")));
            roots.push(format!("e{t}"));
        }
        for _ in 0..rng.below(3) {
            prog.push_str(&format!(
                "(union {} {})\n",
                rng.pick(TERMS),
                rng.pick(TERMS)
            ));
        }
        let rule = format!("(rewrite {lhs} {rhs})\n");
        // The sequence engine on the same left-hand side, as a checked sequence rule.
        let cmds = semi_persistent_egraph::parser::parse_program_v2(&prog).expect("parse");
        let mut it: Interp = Interpreter::new(MachineModel);
        let mut sg = semi_persistent_egraph::resolve::GlobalCtx::new();
        let checked = semi_persistent_egraph::sortcheck::sortcheck_program(
            cmds, &mut it.eg, &it.model, &mut sg,
        )
        .expect("sortcheck");
        it.run_checked(&checked).expect("run");
        let lhs_pat =
            match &semi_persistent_egraph::parser::parse_program_v2(&format!("{A_DECLS}{rule}"))
                .expect("parse rule")[..]
            {
                [.., SurfaceCommand::Rewrite { lhs, .. }] => lhs.clone(),
                other => panic!("expected an ordinary rewrite, got {:?}", other.last()),
            };
        let seq_rule = collection::check(
            &collection::SurfaceRule {
                lhs: lhs_pat,
                legacy: None,
                rhs_term: semi_persistent_egraph::ast::RhsTerm::App {
                    op: "Cat".into(),
                    children: vec![],
                    span: Default::default(),
                },
                lets_term: vec![],
                when_term: vec![],
                ruleset: None,
                flatten: false,
                span: Default::default(),
            },
            None,
            &it.eg,
            &it.model,
            &sg,
            0,
        );
        let seq_rule = match seq_rule {
            Ok(r) => r,
            // A right-hand side of no children is a sort-correct `Cat` term but has no value;
            // the check accepts it, so any error here is the left-hand side's.
            Err((m, _)) => panic!("sequence check of {lhs}: {m}"),
        };
        let mut want: BTreeMap<String, Vec<usize>> = BTreeMap::new();
        for r in &roots {
            let (_, _, class) = it.globals().get(r).unwrap();
            let node = it
                .eg
                .node_ids()
                .find(|&n| {
                    it.eg.class_repr(n) == it.eg.class_repr(class) && it.eg.node_op_name(n) == "Cat"
                })
                .unwrap();
            let mut pos: Vec<usize> =
                collection::matches_at(&it.eg, &it.model, it.globals(), &seq_rule, node)
                    .iter()
                    .map(|m| {
                        if pre {
                            m["pre"].matches("c").count()
                        } else {
                            0
                        }
                    })
                    .collect();
            pos.sort();
            pos.dedup();
            want.insert(r.clone(), pos);
        }
        // The ordinary matcher, through its effect.
        let prog2 = format!("{prog}{rule}(run 1)\n");
        let cmds = semi_persistent_egraph::parser::parse_program_v2(&prog2).expect("parse");
        let mut it2: Interp = Interpreter::new(MachineModel);
        let mut sg2 = semi_persistent_egraph::resolve::GlobalCtx::new();
        let checked = semi_persistent_egraph::sortcheck::sortcheck_program(
            cmds,
            &mut it2.eg,
            &it2.model,
            &mut sg2,
        )
        .expect("sortcheck");
        it2.run_checked(&checked).expect("run");
        let mk = it2
            .eg
            .node_ids()
            .find(|&n| it2.eg.node_op_name(n) == "Mk")
            .map(|n| it2.eg.class_repr(n));
        for r in &roots {
            let (_, _, class) = it2.globals().get(r).unwrap();
            let class = it2.eg.class_repr(class);
            let mut got = Vec::new();
            for n in it2.eg.node_ids() {
                if it2.eg.class_repr(n) != class || it2.eg.node_op_name(n) != "Cat" {
                    continue;
                }
                let mut kids = Vec::new();
                it2.eg
                    .for_each_child(n, |k, _| kids.push(it2.eg.class_repr(k)));
                if let Some(p) = kids.iter().position(|&k| Some(k) == mk) {
                    got.push(p);
                }
            }
            got.sort();
            got.dedup();
            assert_eq!(
                got, want[r],
                "{r}: ordinary windows vs sequence engine\n{prog2}"
            );
            windows += got.len();
        }
        cases += 1;
    }
    eprintln!(
        "step 4: {cases} programs with today's A forms, {windows} match windows, sequence engine = ordinary matcher"
    );
    assert!(windows > 200, "too few windows: {windows}");
}

const AC_DECLS: &str = "(sort E)
(function a () E)
(function b () E)
(function c () E)
(function F (E) E)
(function G (E) E)
(function H (E) E)
(function K (E E) E)
(function Plus (E) E :assoc-comm)
(let ga a)
";

/// Step 1 (AC): filters with and without multiplicity annotations, simple items
/// with and without them, repeated children, classes of several members, overlap,
/// `:except`, with and without a bare sequence.
#[test]
fn step1_ac_multiplicities() {
    let mut rng = Rng(0x5e9c_0de6);
    let (mut cases, mut nodes, mut matches, mut multi) = (0, 0, 0, 0);
    let annotations = ["", ":k{i}", ":k{i}>=2", ":2", ":k{i}<3", ":k{i}!=1"];
    for _ in 0..1500 {
        let nf = 1 + rng.below(3);
        let mut lhs = String::from("(Plus");
        for i in 0..nf {
            let h = rng.below(BASES.len());
            let base = rng.pick(BASES[h].1).replace("{i}", &i.to_string());
            let ann = rng.pick(&annotations).replace("{i}", &i.to_string());
            let except = if i > 0 && rng.below(4) == 0 {
                format!(" :except g{}", rng.below(i))
            } else {
                String::new()
            };
            lhs.push_str(&format!(" (..g{i}{ann} {base}{except})"));
        }
        for j in 0..rng.below(3) {
            let s = *rng.pick(&[
                "s{j}",
                "(F s{j})",
                "s{j}:m{j}",
                "(G ga):m{j}>=2",
                "(K s{j} t{j})",
            ]);
            lhs.push_str(&format!(" {}", s.replace("{j}", &j.to_string())));
        }
        if rng.below(2) == 0 {
            lhs.push_str(" ..rest");
        }
        lhs.push(')');
        let mut prog = String::from(AC_DECLS);
        for t in 0..4 {
            let k = 1 + rng.below(6);
            let kids: Vec<&str> = (0..k).map(|_| *rng.pick(TERMS)).collect();
            prog.push_str(&format!("(let e{t} (Plus {}))\n", kids.join(" ")));
        }
        for _ in 0..rng.below(4) {
            prog.push_str(&format!(
                "(union {} {})\n",
                rng.pick(TERMS),
                rng.pick(TERMS)
            ));
        }
        prog.push_str(&format!("(rewrite {lhs} (Plus (a) (b)))\n"));
        let (n, m, x) = compare(&prog, &["ga"]);
        cases += 1;
        nodes += n;
        matches += m;
        multi += x;
    }
    eprintln!(
        "step 1 AC: {cases} programs, {nodes} root nodes, {matches} matches ({multi} nodes with several), engine = reference"
    );
    let (probes, rows) = SUBQ.get();
    eprintln!(
        "  sub-queries: {probes} filter probes at child classes, {rows} rows, bound-root = reference = free-root grouped"
    );
    assert!(probes > 0, "no filter probed");
    assert!(
        matches > 1000,
        "too few matches to mean anything: {matches}"
    );
    assert!(
        multi > 100,
        "too few nodes where enumeration decides: {multi}"
    );
}

/// "§Edge cases 2": two members of one class that match a filter with the same
/// bindings give one match. Congruence makes such members one node after a rebuild,
/// so the case exists between a union and the rebuild: `(W A)` and `(W B)` in one
/// class, and `A`, `B` merged; `(W (A))` matches both and binds nothing.
#[test]
fn equal_binding_members_are_one_match() {
    let prog = "(sort E)
(function A () E)
(function B () E)
(function D () E)
(function W (E) E)
(function And (E) E :assoc-comm-idem)
(let e (And (W A) (D)))
(union (W A) (W B))
(union A B)
(rewrite (And (..gs (W (A))) ..rest) (And ..rest))
";
    let (nodes, matches, _) = compare(prog, &[]);
    assert_eq!((nodes, matches), (1, 1), "one And node, one match");
}

const MIX_DECLS: &str = "(sort E)
(function a () E)
(function b () E)
(function c () E)
(function F (E) E)
(function G (E) E)
(function H (E) E)
(function K (E E) E)
(function N (i64) E)
(function Cat (E) E :assoc)
(function And (E) E :assoc-comm-idem)
(function Plus (E) E :assoc-comm)
(let ga a)
";

/// Step 2: the right-hand side, `:let`, and `:when` evaluated on the same matches by
/// `crate::seq_rhs` and by `collection.rs` give the same verdicts and the same terms
/// (`collection::pass` compares them in debug builds and fails on a difference).
/// The roots are A, ACI, and AC; the right-hand sides splice filters and rests into
/// operators of each kind ("§Edge cases 3"), reduce them, iterate them, and zip them.
#[test]
fn step2_rhs_parity() {
    // `collection::pass` compares the two evaluators in debug builds only.
    if !cfg!(debug_assertions) {
        eprintln!("step 2 parity: skipped outside a debug build");
        return;
    }
    let mut rng = Rng(0x5e9c_0de7);
    let (mut cases, mut legacy, mut fired, mut no_value) = (0, 0, 0, 0);
    for _ in 0..1500 {
        let root = *rng.pick(&["Cat", "And", "Plus"]);
        let nf = 1 + rng.below(2);
        let mut lhs = format!("({root}");
        // (name, node columns, multiplicity column)
        let mut filters: Vec<(String, Vec<String>, Option<String>)> = Vec::new();
        for i in 0..nf {
            let h = rng.below(BASES.len());
            let base = rng.pick(BASES[h].1).replace("{i}", &i.to_string());
            let cols: Vec<String> = [format!("x{i}"), format!("y{i}")]
                .into_iter()
                .filter(|v| base.contains(v.as_str()))
                .collect();
            let k = (root == "Plus" && rng.below(2) == 0).then(|| format!("k{i}"));
            let ann = k.as_ref().map(|k| format!(":{k}")).unwrap_or_default();
            lhs.push_str(&format!(" (..g{i}{ann} {base})"));
            filters.push((format!("g{i}"), cols, k));
        }
        let mut scalars = Vec::new();
        if root != "Cat" && rng.below(2) == 0 {
            lhs.push_str(" (F s0)");
            scalars.push("s0".to_string());
        }
        let rest = root != "Cat" || rng.below(2) == 0;
        if rest {
            lhs.push_str(" ..rest");
        }
        lhs.push(')');
        let seqs: Vec<String> = filters
            .iter()
            .map(|f| f.0.clone())
            .chain(rest.then(|| "rest".to_string()))
            .collect();
        // A reduction over a sequence, as an i64 expression.
        let int = |rng: &mut Rng| -> String {
            let f = rng.pick(&filters);
            match rng.below(4) {
                0 => format!("(count {})", rng.pick(&seqs)),
                1 if f.2.is_some() => format!("(sum {})", f.2.as_ref().unwrap()),
                2 if !f.1.is_empty() => format!("(count {})", rng.pick(&f.1)),
                _ => format!("(+ (count {}) 1)", f.0),
            }
        };
        // A term of sort E.
        fn term(rng: &mut Rng, depth: usize, ctx: &dyn Fn(&mut Rng) -> String) -> String {
            match rng.below(if depth == 0 { 3 } else { 5 }) {
                0 => "(a)".into(),
                1 => format!("(N {})", ctx(rng)),
                2 => "ga".into(),
                3 => format!("(G {})", term(rng, depth - 1, ctx)),
                _ => format!(
                    "(K {} {})",
                    term(rng, depth - 1, ctx),
                    term(rng, depth - 1, ctx)
                ),
            }
        }
        let target = *rng.pick(&["Cat", "And", "Plus", root, root]);
        let mut kids = Vec::new();
        for _ in 0..1 + rng.below(3) {
            match rng.below(5) {
                0 | 1 => kids.push(format!("..{}", rng.pick(&seqs))),
                2 => kids.push(term(&mut rng, 2, &int)),
                3 if !scalars.is_empty() => kids.push("(H s0)".into()),
                _ => {
                    // A comprehension over a filter not of AC children (whose binder
                    // would have to state the multiplicity, which `collection.rs`
                    // cannot parse), in the target's bracket.
                    if root == "Plus" {
                        kids.push("(a)".into());
                        continue;
                    }
                    let (open, close) = if target == "Cat" {
                        ("[", "]")
                    } else {
                        ("{", "}")
                    };
                    let f = rng.pick(&filters).0.clone();
                    let body = *rng.pick(&["(H e)", "(K e e)", "(G (H e))"]);
                    if filters.len() == 2 && rng.below(2) == 0 {
                        kids.push(format!("..{open} (K e d) for (e d) in (zip g0 g1) {close}"));
                    } else {
                        kids.push(format!("..{open} {body} for e in {f} {close}"));
                    }
                }
            }
        }
        let rhs = format!("({target} {})", kids.join(" "));
        let mut tags = String::new();
        if rng.below(2) == 0 {
            tags.push_str(&format!(" :let ((n0 {}))", int(&mut rng)));
            if rng.below(2) == 0 {
                tags.push_str(&format!(" :when ((>= n0 {}))", rng.below(3)));
            }
        } else if rng.below(2) == 0 {
            tags.push_str(&format!(
                " :when ((< {} {}))",
                int(&mut rng),
                1 + rng.below(4)
            ));
        }
        let rhs = if tags.contains("n0") && rng.below(2) == 0 {
            rhs.replacen(&format!("({target} "), &format!("({target} (N n0) "), 1)
        } else {
            rhs
        };
        let mut prog = String::from(MIX_DECLS);
        for t in 0..4 {
            let k = 1 + rng.below(5);
            let kids: Vec<&str> = (0..k).map(|_| *rng.pick(TERMS)).collect();
            prog.push_str(&format!("(let e{t} ({root} {}))\n", kids.join(" ")));
        }
        for _ in 0..rng.below(3) {
            prog.push_str(&format!(
                "(union {} {})\n",
                rng.pick(TERMS),
                rng.pick(TERMS)
            ));
        }
        prog.push_str(&format!("(rewrite {lhs} {rhs}{tags})\n"));
        let cmds = semi_persistent_egraph::parser::parse_program_v2(&prog)
            .unwrap_or_else(|e| panic!("parse: {e}\n{prog}"));
        let mut it: Interp = Interpreter::new(MachineModel);
        let mut sg = semi_persistent_egraph::resolve::GlobalCtx::new();
        let checked = semi_persistent_egraph::sortcheck::sortcheck_program(
            cmds, &mut it.eg, &it.model, &mut sg,
        )
        .unwrap_or_else(|e| panic!("sortcheck: {e}\n{prog}"));
        it.run_checked(&checked)
            .unwrap_or_else(|e| panic!("run: {e}\n{prog}"));
        let rule = checked
            .iter()
            .find_map(|c| {
                if let CCommand::CollectionRule(r) = c {
                    Some(r.clone())
                } else {
                    None
                }
            })
            .expect("a checked sequence rule");
        let globals = it.globals().clone();
        for _ in 0..2 {
            let rep = collection::pass(&mut it.eg, &it.model, &globals, &[&rule])
                .unwrap_or_else(|e| panic!("pass: {e}\n{prog}"));
            fired += rep.changed;
            no_value += rep.no_value;
        }
        cases += 1;
        legacy += usize::from(rule.legacy_checked());
    }
    eprintln!(
        "step 2 parity: {cases} programs ({legacy} checked by collection.rs too), {fired} merges, {no_value} matches without a value"
    );
    assert!(
        legacy * 10 >= cases * 9,
        "collection.rs checked too few rules to compare: {legacy} of {cases}"
    );
    assert!(fired > 1000, "too few firings to mean anything: {fired}");
}

/// The checked rule of a one-rule program.
fn checked_rule(
    prog: &str,
) -> std::sync::Arc<
    collection::Rule<
        <Cfg as semi_persistent_egraph::config::EGraphConfig>::O,
        <Cfg as semi_persistent_egraph::config::EGraphConfig>::S,
        MachineLit,
    >,
> {
    let cmds = semi_persistent_egraph::parser::parse_program_v2(prog)
        .unwrap_or_else(|e| panic!("parse: {e}\n{prog}"));
    let mut it: Interp = Interpreter::new(MachineModel);
    let mut sg = semi_persistent_egraph::resolve::GlobalCtx::new();
    let checked =
        semi_persistent_egraph::sortcheck::sortcheck_program(cmds, &mut it.eg, &it.model, &mut sg)
            .unwrap_or_else(|e| panic!("sortcheck: {e}\n{prog}"));
    checked
        .iter()
        .find_map(|c| {
            if let CCommand::CollectionRule(r) = c {
                Some(r.clone())
            } else {
                None
            }
        })
        .expect("a checked sequence rule")
}

/// Step 2 ("§Edge cases 3" and "§Multiplicities and `zip`"): the plan states each
/// splice across kinds; a zip across two filters under ACI warns, a zip of one
/// filter's columns and a zip under A do not.
#[test]
fn step2_plan_and_zip_warning() {
    let rule = |r: &str| checked_rule(&format!("{MIX_DECLS}{r}\n"));
    let r = rule("(rewrite (Plus (..fs (F x)) ..rest) (Cat ..fs))");
    assert_eq!(
        r.seq_rhs.plan,
        vec!["..fs into 'Cat': AC into A, each child repeated by its multiplicity".to_string()]
    );
    assert_eq!(r.seq_rhs.warnings.len(), 1, "{:?}", r.seq_rhs.warnings);
    let r = rule("(rewrite (And (..fs (F x)) ..rest) (And ..rest ..fs))");
    assert!(r.seq_rhs.plan.is_empty() && r.seq_rhs.warnings.is_empty());
    let r = rule(
        "(rewrite (And (..fs (F x)) (..gs (G y)) ..rest) (And ..{ (K x y) for (x y) in (zip x y) } ..rest))",
    );
    assert_eq!(r.seq_rhs.warnings, vec!["zip across fs and gs pairs AC or ACI children by class id, which is not a function of the e-graph's contents".to_string()]);
    let r = rule(
        "(rewrite (And (..fs (K x y)) ..rest) (And ..{ (K y x) for (x y) in (zip x y) } ..rest))",
    );
    assert!(r.seq_rhs.warnings.is_empty(), "{:?}", r.seq_rhs.warnings);
    let r = rule(
        "(rewrite (Cat (..fs (F x)) (..gs (G y))) (Cat ..[ (K x y) for (x y) in (zip x y) ]))",
    );
    assert!(r.seq_rhs.warnings.is_empty(), "{:?}", r.seq_rhs.warnings);
}

/// Step 3's edge bases: a variable (every class matches; no free-root plan), a
/// global (no atom of its own), a literal and a literal variable below an
/// application, and an application over a class of several members. Each program
/// goes through `compare`, which checks the sub-queries. (A variadic operator's
/// children cannot have a literal sort: its argument sort is its return sort, and
/// no operator returns a literal sort.)
#[test]
fn step3_subquery_bases() {
    let aci = "(sort E)
(function a () E)
(function b () E)
(function F (E) E)
(function G (E) E)
(function N (i64) E)
(function And (E) E :assoc-comm-idem)
(let ga a)
(let e0 (And a (F a) (F b) (G a) (N 3) (N 4)))
(let e1 (And b (F (G a)) (N 3)))
(union (F b) (G a))
";
    let rules = [
        "(rewrite (And (..gs x) ..rest) (And ..rest))",
        "(rewrite (And (..gs ga) ..rest) (And ..rest))",
        "(rewrite (And (..gs (F x)) ..rest) (And ..rest))",
        "(rewrite (And (..gs (N 3)) ..rest) (And ..rest))",
        "(rewrite (And (..gs (N n)) ..rest) (And ..rest))",
    ];
    SUBQ.set((0, 0));
    for r in rules {
        let prog = format!("{aci}{r}\n");
        compare(&prog, &["ga"]);
    }
    let (probes, rows) = SUBQ.get();
    eprintln!("step 3 edge bases: {probes} probes, {rows} rows");
    // 7 child classes (`{(F b), (G a)}` is one) and 5 rules; rows: `x` at every class
    // (7), `ga` at one, `(F x)` at 3 (`x = a`, `x = b`, `x = {(G a), (F b)}`),
    // `(N 3)` at 1, `(N n)` at 2.
    assert_eq!((probes, rows), (35, 14));
}

/// Step 5: the non-emptiness analysis (`SeqRhs::required_nonempty`) and dropping part 2.
///
/// For each random rule: the analysis marks `g0` exactly on the recognized forms whose
/// value at an empty `g0` is false (computed here from the operator's definition on
/// integers, not through the engine); it marks nothing on forms it must answer
/// "unknown" to; wherever it marks `g0`, every match with `g0` empty fails the rule's
/// `:let`s and `:when`s (soundness, checked under the root drive, which keeps them); and
/// the matches that *fire* are the same under every plan, including the filter drives
/// that skip those nodes.
#[test]
fn step5_nonempty_analysis_and_part2() {
    use semi_persistent_egraph::seq_engine::{Access, Drive, firing_at, set_plan_override};
    let mut rng = Rng(0x5e9c_0de9);
    let cmp = |op: &str, a: i64, b: i64| match op {
        ">=" => a >= b,
        ">" => a > b,
        "==" => a == b,
        "!=" => a != b,
        "<" => a < b,
        "<=" => a <= b,
        _ => unreachable!(),
    };
    let (mut cases, mut marked, mut empty_matches_checked, mut fired) = (0, 0, 0, 0);
    let terms = [
        "a",
        "b",
        "(F a)",
        "(F b)",
        "(G a)",
        "(G (N 1))",
        "(N 1)",
        "(N 2)",
        "(N 3)",
        "(K a b)",
    ];
    for _ in 0..600 {
        let root = *rng.pick(&["And", "Plus", "Cat"]);
        let base0 = *rng.pick(&["(N n0)", "(F x0)", "(G (N n0))"]);
        let two = rng.below(2) == 0;
        let mut lhs = format!("({root} (..g0 {base0})");
        if two {
            lhs.push_str(" (..g1 (G x1))");
        }
        lhs.push_str(" ..rest)");
        let has_lit = base0.contains("n0");
        // (guard text, whether the analysis must mark g0; None when it must not claim to)
        let mut forms: Vec<(String, bool)> = Vec::new();
        for op in [">=", ">", "==", "!=", "<", "<="] {
            for k in 0..3 {
                forms.push((format!(":when (({op} (count g0) {k}))"), !cmp(op, 0, k)));
                forms.push((format!(":when (({op} {k} (count g0)))"), !cmp(op, k, 0)));
            }
        }
        if has_lit {
            forms.push((":let ((m (min n0)))".into(), true));
            forms.push((":let ((m (max n0)))".into(), true));
            forms.push((":let ((m (sum n0)))".into(), false));
        }
        if two {
            forms.push((":when ((> (count (zip g0 g1)) 0))".into(), true));
            forms.push((":when ((< (count g0) (count g1)))".into(), false));
        }
        let (guard, expect) = rng.pick(&forms).clone();
        let rhs = format!("({root} (N 0))");
        let mut prog = String::from(MIX_DECLS);
        for t in 0..4 {
            let k = 1 + rng.below(4);
            let kids: Vec<&str> = (0..k).map(|_| *rng.pick(&terms)).collect();
            prog.push_str(&format!("(let e{t} ({root} {}))\n", kids.join(" ")));
        }
        prog.push_str(&format!("(rewrite {lhs} {rhs} {guard})\n"));
        let cmds = semi_persistent_egraph::parser::parse_program_v2(&prog)
            .unwrap_or_else(|e| panic!("parse: {e}\n{prog}"));
        let mut it: Interp = Interpreter::new(MachineModel);
        let mut sg = semi_persistent_egraph::resolve::GlobalCtx::new();
        let checked = semi_persistent_egraph::sortcheck::sortcheck_program(
            cmds, &mut it.eg, &it.model, &mut sg,
        )
        .unwrap_or_else(|e| panic!("sortcheck: {e}\n{prog}"));
        it.run_checked(&checked)
            .unwrap_or_else(|e| panic!("run: {e}\n{prog}"));
        let rule = checked
            .iter()
            .find_map(|c| {
                if let CCommand::CollectionRule(r) = c {
                    Some(r.clone())
                } else {
                    None
                }
            })
            .expect("a checked sequence rule");
        let req = rule.filter_required();
        assert_eq!(
            req.first().copied(),
            Some(expect),
            "analysis of `{guard}` for g0\n{prog}"
        );
        cases += 1;
        marked += usize::from(req[0]);
        let root_op = rule.root_op();
        for n in it.eg.node_ids() {
            if it.eg.node_op(n) != root_op
                || it.eg.node_flags(n) & semi_persistent_egraph::node_types::FLAG_SUBSUMED != 0
            {
                continue;
            }
            set_plan_override(Some((Drive::Root, Access::Probe)));
            let under_root = firing_at(&it.eg, it.globals(), &rule, n, &it.model)
                .unwrap_or_else(|e| panic!("{e}\n{prog}"));
            set_plan_override(None);
            // Soundness: a marked filter's empty matches never fire.
            for (env, fires) in &under_root {
                for (g, &r) in req.iter().enumerate() {
                    if r && env.get(&format!("g{g}")).map(String::as_str) == Some("[]") {
                        assert!(
                            !fires,
                            "g{g} marked non-empty, yet a match with g{g} empty fires: {env:?}\n{prog}"
                        );
                        empty_matches_checked += 1;
                    }
                }
            }
            let fire_set = |v: &[(BTreeMap<String, String>, bool)]| -> std::collections::BTreeSet<BTreeMap<String, String>> {
                v.iter().filter(|(_, f)| *f).map(|(e, _)| e.clone()).collect()
            };
            let want = fire_set(&under_root);
            fired += want.len();
            for plan in [
                (Drive::Filters, Access::Probe),
                (Drive::Filters, Access::Materialize),
            ] {
                set_plan_override(Some(plan));
                let got = firing_at(&it.eg, it.globals(), &rule, n, &it.model)
                    .unwrap_or_else(|e| panic!("{e}\n{prog}"));
                set_plan_override(None);
                assert_eq!(
                    fire_set(&got),
                    want,
                    "firing matches under {plan:?} at {n:?}\n{prog}"
                );
            }
        }
    }
    eprintln!(
        "step 5 analysis: {cases} rules ({marked} with g0 marked), {empty_matches_checked} empty-filter matches confirmed not to fire, {fired} firing matches equal under every plan"
    );
    assert!(
        marked > 100 && cases - marked > 100,
        "both answers must be exercised: {marked} of {cases}"
    );
    assert!(
        empty_matches_checked > 100,
        "the soundness side must see empty matches: {empty_matches_checked}"
    );
}

/// Step 5, on the MLTL rule file: which filters each n-ary rule cannot fire without.
/// Factoring's `gs`/`fs` (its `:let` takes `min l`), narrowing's `fs` (its guard counts
/// `narrowed` rows, which range over `fs`'s columns), and merging's `gs`/`fs` (its guard
/// compares two counts that are both 0 on an empty filter). Narrowing's `ns` and `gs`
/// may be empty and must not be marked: their guards hold at 0 (`0 == 0`).
#[test]
fn step5_mltl_rules_required_filters() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/mltl/rules");
    let rules = std::fs::read_to_string(root.join("mltl_nary_decl.egg")).expect("rule file");
    let nary = &rules[rules
        .find("; --- n-ary collection rules")
        .expect("the n-ary section")..];
    let prog =
        std::fs::read_to_string(root.join("tests/nary_check_1.egg")).expect("a check program");
    // Declarations first, then the rules, as `run_nary_decl_checks.sh` assembles them.
    let at = prog.find("\n(let ").expect("a let");
    let text = format!("{}\n{nary}\n{}", &prog[..at], &prog[at..]);
    let cmds = semi_persistent_egraph::parser::parse_program_v2(&text).expect("parse");
    let mut it: Interp = Interpreter::new(MachineModel);
    let mut sg = semi_persistent_egraph::resolve::GlobalCtx::new();
    let checked =
        semi_persistent_egraph::sortcheck::sortcheck_program(cmds, &mut it.eg, &it.model, &mut sg)
            .expect("sortcheck");
    let got: Vec<(Vec<String>, Vec<bool>)> = checked
        .iter()
        .filter_map(|c| {
            if let CCommand::CollectionRule(r) = c {
                Some(r.clone())
            } else {
                None
            }
        })
        .map(|r| {
            (
                r.spec.filters.iter().map(|f| f.name.clone()).collect(),
                r.filter_required(),
            )
        })
        .collect();
    let want: Vec<(Vec<&str>, Vec<bool>)> = vec![
        (vec!["gs"], vec![true]),                           // merging, And
        (vec!["fs"], vec![true]),                           // merging, Or
        (vec!["gs"], vec![true]),                           // factoring, And
        (vec!["fs"], vec![true]),                           // factoring, Or
        (vec!["ns", "gs", "fs"], vec![false, false, true]), // narrowing
    ];
    let got_ref: Vec<(Vec<&str>, Vec<bool>)> = got
        .iter()
        .map(|(n, r)| (n.iter().map(String::as_str).collect(), r.clone()))
        .collect();
    assert_eq!(got_ref, want);
}

const FLAT_DECLS: &str = "(sort E)
(function a () E)
(function b () E)
(function c () E)
(function F (E) E)
(function G (E) E)
(function H (E) E)
(function K (E E) E)
(function P0 () E)
(function P1 () E)
(function P2 () E)
(function And (E) E :assoc-comm-idem)
(function Plus (E) E :assoc-comm)
(function Cat (E) E :assoc)
(function Lf (E) E :assoc-left)
(let ga a)
";

/// Task 4 of `doc/goal-flatten-and-engine-completion.md`: a sequence rule tagged
/// `:flatten` matches each root node's flattened views, under ACI, AC, A, and a fold.
/// The roots are built over placeholder classes that then gain members of the root's
/// operator by merges, after construction, so the nesting is stored: one member, two
/// members, and cycles (a placeholder merged with a node over itself). Every root node
/// is compared with the reference (`seq_ref::match_flattened`) under route 1 and under
/// the relational engine with every forced plan, statically and with runtime
/// scheduling.
#[test]
fn flatten_nested_roots_every_plan() {
    let mut rng = Rng(0xf1a7_7e45);
    let (mut cases, mut nodes, mut matches, mut multi) = (0, 0, 0, 0);
    FLAT_CHANGED.set(0);
    for _ in 0..600 {
        let op = *rng.pick(&["And", "Plus", "Cat", "Lf"]);
        // A child term: a ground term, or a placeholder numbered `from` or higher. A
        // member merged into placeholder `j` names only placeholders above `j`, so the
        // nesting is acyclic except for the deliberate cycles below, each of which
        // refers to its class once: a class referring to itself several times has
        // exponentially many views, which the view bound caps but this comparison, and
        // the unbounded reference, cannot afford.
        let term = |rng: &mut Rng, from: usize| -> String {
            if from < 3 && rng.below(3) == 0 {
                format!("p{}", from + rng.below(3 - from))
            } else {
                rng.pick(TERMS).to_string()
            }
        };
        let node = |rng: &mut Rng, from: usize| -> String {
            let k = 2 + rng.below(2);
            let mut kids: Vec<String> = Vec::new();
            for _ in 0..k {
                // A repeated child gives an AC multiplicity above 1.
                if op == "Plus" && !kids.is_empty() && rng.below(3) == 0 {
                    let again = kids[0].clone();
                    kids.push(again);
                } else {
                    kids.push(term(rng, from));
                }
            }
            format!("({op} {})", kids.join(" "))
        };
        let mut prog = String::from(FLAT_DECLS);
        for j in 0..3 {
            prog.push_str(&format!("(let p{j} (P{j}))\n"));
        }
        for t in 0..3 {
            let n = node(&mut rng, 0);
            prog.push_str(&format!("(let e{t} {n})\n"));
        }
        for j in 0..3 {
            match rng.below(5) {
                0 => {}
                1 => {
                    // A cycle: the placeholder gains a node over itself.
                    let t = term(&mut rng, 3);
                    prog.push_str(&format!("(union p{j} ({op} {t} p{j}))\n"));
                }
                2 => {
                    let (n1, n2) = (node(&mut rng, j + 1), node(&mut rng, j + 1));
                    prog.push_str(&format!("(union p{j} {n1})\n(union p{j} {n2})\n"));
                }
                _ => {
                    let n = node(&mut rng, j + 1);
                    prog.push_str(&format!("(union p{j} {n})\n"));
                }
            }
        }
        if rng.below(3) == 0 {
            prog.push_str(&format!(
                "(union {} {})\n",
                rng.pick(TERMS),
                rng.pick(TERMS)
            ));
        }
        let nf = 1 + rng.below(2);
        let mut lhs = format!("({op}");
        if op != "And" && op != "Plus" && rng.below(2) == 0 {
            lhs.push_str(" ..pre");
        }
        for i in 0..nf {
            let h = rng.below(BASES.len());
            let base = rng.pick(BASES[h].1).replace("{i}", &i.to_string());
            let mult = if op == "Plus" && rng.below(3) == 0 {
                format!(":k{i}")
            } else {
                String::new()
            };
            lhs.push_str(&format!(" (..g{i}{mult} {base})"));
        }
        if rng.below(3) == 0 {
            let s = *rng.pick(&["s0", "(F s0)", "(G ga)", "a"]);
            lhs.push_str(&format!(" {s}"));
        }
        if rng.below(2) == 0 {
            lhs.push_str(" ..rest");
        }
        lhs.push(')');
        prog.push_str(&format!("(rewrite {lhs} ({op} ..g0) :flatten)\n"));
        let (n, m, x) = compare(&prog, &["ga"]);
        cases += 1;
        nodes += n;
        matches += m;
        multi += x;
    }
    let changed = FLAT_CHANGED.get();
    eprintln!(
        "flatten: {cases} programs, {nodes} root nodes, {matches} matches ({multi} nodes with several), \
         {changed} nodes whose matches flattening changed; engine = route 1 = reference"
    );
    assert!(
        matches > 1000,
        "too few matches to mean anything: {matches}"
    );
    assert!(
        changed > 100,
        "too few nodes where flattening changed the matches: {changed}"
    );
}

/// The upward walk of a flattened filter drive (task 4). The filter's only row is
/// `(F c)`, two levels below the root `R = And{a, K1}`: `K1 ≡ And{b, K2}` and
/// `K2 ≡ And{(F c), (G a)}`. The row's direct parent is the inner conjunction of `K2`,
/// not `R`, so `by_contains` alone proposes the inner node and leaves `R` to part 2,
/// where every filter is empty. Climbing to the parents' classes, then to their
/// parents, makes `R` a candidate, and the filter drive then gives `R` the root drive's
/// matches, which include the row.
#[test]
fn flatten_drive_climbs_to_a_root_two_levels_up() {
    let program = "(sort E)
(function a () E)
(function b () E)
(function c () E)
(function F (E) E)
(function G (E) E)
(function K1c () E)
(function K2c () E)
(function And (E) E :assoc-comm-idem)
(let k1 (K1c))
(let k2 (K2c))
(let r (And (a) k1))
(union k1 (And (b) k2))
(union k2 (And (F (c)) (G (a))))
(rewrite (And (..gs (F x)) ..rest) (And ..rest) :flatten)
";
    let cmds = semi_persistent_egraph::parser::parse_program_v2(program).expect("parse");
    let mut it: Interp = Interpreter::new(MachineModel);
    let mut sg = semi_persistent_egraph::resolve::GlobalCtx::new();
    let checked =
        semi_persistent_egraph::sortcheck::sortcheck_program(cmds, &mut it.eg, &it.model, &mut sg)
            .expect("sortcheck");
    it.run_checked(&checked).expect("run");
    let rule = checked
        .iter()
        .find_map(|c| match c {
            CCommand::CollectionRule(r) => Some(r.clone()),
            _ => None,
        })
        .expect("a checked sequence rule");
    let (_, _, r) = it.globals().get("r").expect("r");
    let root = it
        .eg
        .node_ids()
        .find(|&n| it.eg.node_op(n) == rule.root_op() && it.eg.class_repr(n) == it.eg.class_repr(r))
        .expect("the root conjunction");
    use semi_persistent_egraph::seq_engine::{Access, Drive, set_plan_override};
    let at = |plan| {
        set_plan_override(Some(plan));
        let mut ms =
            semi_persistent_egraph::seq_engine::matches_at(&it.eg, it.globals(), &rule, root);
        set_plan_override(None);
        ms.sort();
        ms
    };
    let by_root = at((Drive::Root, Access::Probe));
    assert!(
        by_root
            .iter()
            .any(|m| m.get("gs").is_some_and(|g| g != "[]")),
        "the root drive finds the nested row: {by_root:?}"
    );
    for access in [Access::Probe, Access::Materialize] {
        assert_eq!(
            at((Drive::Filters, access)),
            by_root,
            "the filter drive ({access:?}) must reach the root through two levels"
        );
    }
}

/// Classes that refer to themselves several times (case 134 of the generator before it
/// was restricted): `p0 ≡ Cat[p0, p0, p2, p0]` and `p2 ≡ Cat[p0, b, p2, b]`. Each
/// occurrence of `p0` is kept or opened, so a root over them has hundreds of views,
/// each with hundreds of parses under the two gaps. Matching such a node used to take
/// longer than the guard allows, because duplicates were removed pairwise; it now
/// either completes, equal to the reference, or is skipped and counted under the
/// node's bound on the matches assembled across views.
#[test]
fn flatten_self_referencing_classes_finish() {
    let program = format!(
        "{FLAT_DECLS}(let p0 (P0))
(let p1 (P1))
(let p2 (P2))
(let e0 (Cat (G a) (G a) (F (G b)) (K a a)))
(let e1 (Cat c (H c) (F a) p0))
(let e2 (Cat (F (G b)) p1 a p1))
(union p0 (Cat (K b b) (G (F a)) (F (G b)) p2))
(union p0 (Cat p0 p0 p2 p0))
(union p1 (Cat (K b b) p0 c))
(union p2 (Cat p0 b p2 b))
(rewrite (Cat ..pre (..g0 (F x0)) (..g1 (F (G y1))) ..rest) (Cat ..g0) :flatten)
"
    );
    let started = std::time::Instant::now();
    let (nodes, matches, _) = compare(&program, &["ga"]);
    eprintln!(
        "self-referencing classes: {nodes} root nodes, {matches} matches, {:?}",
        started.elapsed()
    );
}
