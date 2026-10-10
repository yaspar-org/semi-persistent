// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! MLTL's n-ary rewrites, written as Rust over a live e-graph.
//!
//! Three MLTL rules have a natural n-ary form that Semper's pattern language
//! cannot state: a remainder is a bare name, so a pattern cannot filter the
//! children of a collection by shape, read their bounds, aggregate over them,
//! and rebuild each one. Stated pairwise they fire `k(k-1)/2` times per
//! `k`-ary conjunction per round, which is where the e-graph growth measured in
//! the case study comes from.
//!
//! This driver runs a Semper program with its rules, and between saturation
//! rounds applies the n-ary forms directly:
//!
//! - **merge**: every `G[.,.] phi` child of a conjunction over one `phi` whose
//!   windows form a contiguous union becomes one `G` over that union, and
//!   dually for `F` in a disjunction.
//! - **factor**: all `G` children of a conjunction share one outer window
//!   `[K0, K0 + W]`, `K0 = min l`, `W = min (u - l)`, and dually for `F` in a
//!   disjunction. One firing gives a flat inner conjunction, where the
//!   pairwise rule builds a nested chain one level per firing.
//! - **narrow**: each `F[c,d] phi` in a conjunction is narrowed once against
//!   the union of all `G[.,.] (Not phi)` windows beside it.
//!
//! Each is derivable from rules already in `rules/mltl.egg`: merging and
//! narrowing are their pairwise rules iterated, and factoring is the pairwise
//! rule iterated plus the nesting law `G[a,b] G[c,d] phi = G[a+c, b+d] phi`.
//! So the driver adds no semantic assumption the rule file does not already
//! make; it changes how many firings and intermediate nodes reaching the
//! result costs.
//!
//! The point is to find a working rule before designing the syntax for it.
//! What each rule needs from the e-graph is recorded where it is read, because
//! that list is the requirement a surface language has to meet.
//!
//! Usage: `mltl_nary PROGRAM [--types machine]`. Which rules run is read from
//! `MLTL_NARY`, a comma list of `merge`, `factor`, `narrow`, or `none`, and
//! defaults to all three. Statistics go to stderr.

use semi_persistent_egraph::EGraph;
use semi_persistent_egraph::config::EGraphConfig;
use semi_persistent_egraph::interpret::Interpreter;
use semi_persistent_egraph::model::{MachineLit, MachineModel};
use semi_persistent_egraph::node_types::FLAG_SUBSUMED;
use semi_persistent_egraph::nodes::DefaultConfig;
use semi_persistent_egraph::resolve::GlobalCtx;
use semi_persistent_egraph::sortcheck::{CCommand, sortcheck_program};
use std::collections::BTreeMap;
use std::time::Instant;

type Cfg = DefaultConfig;
type G = <Cfg as EGraphConfig>::G;
type O = <Cfg as EGraphConfig>::O;
type Eg = EGraph<Cfg, MachineLit, true, false>;

#[derive(Clone, Copy, Debug, Default)]
struct Enabled {
    merge: bool,
    factor: bool,
    narrow: bool,
}

impl Enabled {
    fn from_env() -> Self {
        let spec = std::env::var("MLTL_NARY").unwrap_or_else(|_| "merge,factor,narrow".into());
        let mut e = Enabled::default();
        for part in spec.split(',').map(str::trim) {
            match part {
                "merge" => e.merge = true,
                "factor" => e.factor = true,
                "narrow" => e.narrow = true,
                "none" | "" => {}
                other => {
                    eprintln!("MLTL_NARY: unknown rule '{other}' (merge, factor, narrow, none)");
                    std::process::exit(2);
                }
            }
        }
        e
    }

    fn any(self) -> bool {
        self.merge || self.factor || self.narrow
    }
}

/// How many times each rule changed the graph, for the report.
#[derive(Clone, Copy, Debug, Default)]
struct Fired {
    merge: usize,
    factor: usize,
    narrow: usize,
}

/// The operators the rules read and build. Looked up once; a program that does
/// not declare one of them simply never fires the rules that need it.
struct Ops {
    and: Option<O>,
    or: Option<O>,
    not: Option<O>,
    global: Option<O>,
    future: Option<O>,
    interval: Option<O>,
    /// The literal operator for `i64`, taken from an existing bound rather than
    /// looked up by sort name, so the driver does not depend on how the sort is
    /// spelled.
    int: Option<O>,
}

/// A read-only view of the graph, built once per pass.
///
/// Requirement for a surface language, the first one: a rule over a collection
/// reads *members of child classes*, not child nodes. A child of a conjunction
/// is an e-class, and the rule has to ask which of its members is a `G`.
struct View {
    members: BTreeMap<G, Vec<G>>,
}

impl View {
    fn new(eg: &Eg) -> Self {
        let mut members: BTreeMap<G, Vec<G>> = BTreeMap::new();
        for id in eg.node_ids() {
            members.entry(eg.class_repr(id)).or_default().push(id);
        }
        for v in members.values_mut() {
            v.sort_by_key(|id| id.to_usize());
        }
        View { members }
    }

    fn members(&self, class: G) -> &[G] {
        self.members.get(&class).map(Vec::as_slice).unwrap_or(&[])
    }
}

fn children(eg: &Eg, id: G) -> Vec<G> {
    let mut out = Vec::new();
    eg.for_each_child(id, |c, _| out.push(eg.class_repr(c)));
    out
}

fn live(eg: &Eg, id: G) -> bool {
    eg.node_flags(id) & FLAG_SUBSUMED == 0
}

/// The `i64` value a class holds, if it holds one.
fn int_of(eg: &Eg, view: &View, class: G) -> Option<i64> {
    view.members(class)
        .iter()
        .find_map(|&m| match eg.get_lit_val(m) {
            Some(MachineLit::I64(x)) => Some(x),
            _ => None,
        })
        .copied()
}

/// The bounds of an interval class.
fn interval_of(eg: &Eg, view: &View, ops: &Ops, class: G) -> Option<(i64, i64)> {
    let interval = ops.interval?;
    view.members(class).iter().find_map(|&m| {
        if eg.node_op(m) != interval {
            return None;
        }
        let k = children(eg, m);
        Some((
            int_of(eg, view, *k.first()?)?,
            int_of(eg, view, *k.get(1)?)?,
        ))
    })
}

/// The first live `op[l,u] phi` member of a class, as `(l, u, phi)`.
///
/// Requirement, the second: the rule needs a *determined* member. A class may
/// hold `G[0,5] a` and `G[1,3] b` as equal members, and a rule that bound every
/// choice would admit exponentially many matches. The smallest id is taken
/// here, which is stable across runs; the semantics of a surface feature would
/// have to fix a choice in the same way.
fn temporal_of(eg: &Eg, view: &View, ops: &Ops, op: O, class: G) -> Option<(i64, i64, G)> {
    view.members(class).iter().find_map(|&m| {
        if eg.node_op(m) != op || !live(eg, m) {
            return None;
        }
        let k = children(eg, m);
        let (l, u) = interval_of(eg, view, ops, *k.first()?)?;
        Some((l, u, *k.get(1)?))
    })
}

/// The class `phi` when `class` holds a live `Not phi`.
fn negated(eg: &Eg, view: &View, ops: &Ops, class: G) -> Option<G> {
    let not = ops.not?;
    view.members(class).iter().find_map(|&m| {
        if eg.node_op(m) == not && live(eg, m) {
            children(eg, m).first().copied()
        } else {
            None
        }
    })
}

fn mk_int(eg: &mut Eg, ops: &Ops, x: i64) -> Option<G> {
    let v = eg.intern_lit(MachineLit::I64(x));
    Some(eg.add_lit(ops.int?, v))
}

fn mk_temporal(eg: &mut Eg, ops: &Ops, op: O, l: i64, u: i64, phi: G) -> Option<G> {
    debug_assert!(0 <= l && l <= u, "window [{l},{u}] is not an interval");
    let lo = mk_int(eg, ops, l)?;
    let hi = mk_int(eg, ops, u)?;
    let iv = eg.add(ops.interval?, &[lo, hi]);
    Some(eg.add(op, &[iv, phi]))
}

/// Union a set of closed integer windows into maximal contiguous runs.
/// `[0,3]` and `[4,6]` are adjacent over the integers, so they join.
fn union(mut w: Vec<(i64, i64)>) -> Vec<(i64, i64)> {
    w.sort_unstable();
    let mut out: Vec<(i64, i64)> = Vec::new();
    for (l, u) in w {
        match out.last_mut() {
            Some(last) if l <= last.1 + 1 => last.1 = last.1.max(u),
            _ => out.push((l, u)),
        }
    }
    out
}

/// One application of every enabled rule to every live collection node.
///
/// Matches are computed against a snapshot and applied afterwards, as a
/// saturation round does, so the order nodes are visited in cannot change what
/// fires.
fn pass(eg: &mut Eg, ops: &Ops, en: Enabled, fired: &mut Fired) -> usize {
    let view = View::new(eg);
    // (class to merge into, rule, construction)
    enum Build {
        /// A collection node over these children, of which `slots` replace one
        /// original child each.
        Collection {
            op: O,
            keep: Vec<G>,
            add: Vec<(O, i64, i64, G)>,
        },
        /// `outer[K0,K1] (inner_op children)` beside `keep`.
        Factored {
            op: O,
            temporal: O,
            k0: i64,
            k1: i64,
            inner: Vec<(i64, i64, G)>,
            keep: Vec<G>,
        },
    }
    let mut plans: Vec<(G, &'static str, Build)> = Vec::new();

    let collections: Vec<(O, O)> = [(ops.and, ops.global), (ops.or, ops.future)]
        .into_iter()
        .filter_map(|(c, t)| Some((c?, t?)))
        .collect();

    for id in eg.node_ids().collect::<Vec<_>>() {
        if !live(eg, id) {
            continue;
        }
        let op = eg.node_op(id);
        let Some(&(coll, temporal)) = collections.iter().find(|(c, _)| *c == op) else {
            continue;
        };
        let class = eg.class_repr(id);
        let kids = children(eg, id);
        // Requirement, the third: the match is *maximal*. Every child that has
        // a qualifying member is bound, once per node. Binding any subset
        // instead would fire `2^k` times and buy nothing.
        let mut hits: Vec<(G, i64, i64, G)> = Vec::new();
        let mut rest: Vec<G> = Vec::new();
        for &k in &kids {
            match temporal_of(eg, &view, ops, temporal, k) {
                Some((l, u, phi)) => hits.push((k, l, u, phi)),
                None => rest.push(k),
            }
        }

        // --- merge -----------------------------------------------------------
        if en.merge && hits.len() >= 2 {
            let mut by_phi: BTreeMap<G, Vec<(i64, i64)>> = BTreeMap::new();
            for &(_, l, u, phi) in &hits {
                by_phi.entry(phi).or_default().push((l, u));
            }
            if by_phi.values().any(|w| union(w.clone()).len() < w.len()) {
                let mut add = Vec::new();
                for (&phi, w) in &by_phi {
                    for (l, u) in union(w.clone()) {
                        add.push((temporal, l, u, phi));
                    }
                }
                plans.push((
                    class,
                    "merge",
                    Build::Collection {
                        op: coll,
                        keep: rest.clone(),
                        add,
                    },
                ));
                // A node that merges is rebuilt next pass with the merged
                // children; factoring the unmerged form as well would add a
                // second, redundant rendering.
                continue;
            }
        }

        // --- factor ----------------------------------------------------------
        if en.factor && hits.len() >= 2 {
            let k0 = hits.iter().map(|h| h.1).min().expect("nonempty");
            let w = hits.iter().map(|h| h.2 - h.1).min().expect("nonempty");
            // An outer window of `[0,0]` is the identity and factors nothing.
            if !(k0 == 0 && w == 0) {
                let k1 = k0 + w;
                let inner = hits
                    .iter()
                    .map(|&(_, l, u, phi)| (l - k0, u - k1, phi))
                    .collect();
                plans.push((
                    class,
                    "factor",
                    Build::Factored {
                        op: coll,
                        temporal,
                        k0,
                        k1,
                        inner,
                        keep: rest.clone(),
                    },
                ));
            }
        }

        // --- narrow ----------------------------------------------------------
        // Only in a conjunction: an always over the negation is what licenses
        // shrinking the window an eventually searches.
        if en.narrow && Some(coll) == ops.and {
            let (Some(global), Some(future)) = (ops.global, ops.future) else {
                continue;
            };
            let mut forbidden: BTreeMap<G, Vec<(i64, i64)>> = BTreeMap::new();
            for &k in &kids {
                if let Some((l, u, body)) = temporal_of(eg, &view, ops, global, k)
                    && let Some(phi) = negated(eg, &view, ops, body)
                {
                    forbidden.entry(phi).or_default().push((l, u));
                }
            }
            if forbidden.is_empty() {
                continue;
            }
            let forbidden: BTreeMap<G, Vec<(i64, i64)>> =
                forbidden.into_iter().map(|(p, w)| (p, union(w))).collect();
            let mut keep = Vec::new();
            let mut add = Vec::new();
            let mut changed = false;
            for &k in &kids {
                let narrowed = temporal_of(eg, &view, ops, future, k).and_then(|(c, d, phi)| {
                    let windows = forbidden.get(&phi)?;
                    let (mut lo, mut hi) = (c, d);
                    loop {
                        let before = (lo, hi);
                        for &(a, b) in windows {
                            // The pairwise rules' guards: a window covering the
                            // start pushes it past its end, one covering the end
                            // pulls it before its start.
                            if a <= lo && lo <= b + 1 && b < hi {
                                lo = lo.max(b + 1);
                            }
                            if lo < a && a <= hi && hi <= b {
                                hi = hi.min(a - 1);
                            }
                        }
                        if (lo, hi) == before {
                            break;
                        }
                    }
                    ((lo, hi) != (c, d) && lo <= hi).then_some((lo, hi, phi))
                });
                match narrowed {
                    Some((lo, hi, phi)) => {
                        changed = true;
                        add.push((future, lo, hi, phi));
                    }
                    None => keep.push(k),
                }
            }
            if changed {
                plans.push((
                    class,
                    "narrow",
                    Build::Collection {
                        op: coll,
                        keep,
                        add,
                    },
                ));
            }
        }
    }

    let mut merged = 0usize;
    for (class, rule, build) in plans {
        let new = match build {
            Build::Collection { op, mut keep, add } => {
                for (t, l, u, phi) in add {
                    let Some(n) = mk_temporal(eg, ops, t, l, u, phi) else {
                        continue;
                    };
                    keep.push(n);
                }
                if keep.len() == 1 {
                    keep[0]
                } else {
                    eg.add(op, &keep)
                }
            }
            Build::Factored {
                op,
                temporal,
                k0,
                k1,
                inner,
                mut keep,
            } => {
                let mut parts = Vec::with_capacity(inner.len());
                for (l, u, phi) in inner {
                    // `op[0,0] phi` is `phi`; building it directly keeps the
                    // identity out of the graph rather than waiting a round for
                    // the rule file's subsuming rewrite to remove it.
                    let part = if l == 0 && u == 0 {
                        phi
                    } else {
                        match mk_temporal(eg, ops, temporal, l, u, phi) {
                            Some(p) => p,
                            None => continue,
                        }
                    };
                    parts.push(part);
                }
                let body = if parts.len() == 1 {
                    parts[0]
                } else {
                    eg.add(op, &parts)
                };
                let Some(outer) = mk_temporal(eg, ops, temporal, k0, k1, body) else {
                    continue;
                };
                keep.push(outer);
                if keep.len() == 1 {
                    keep[0]
                } else {
                    eg.add(op, &keep)
                }
            }
        };
        if eg.merge(new, class).is_some() {
            merged += 1;
            match rule {
                "merge" => fired.merge += 1,
                "factor" => fired.factor += 1,
                _ => fired.narrow += 1,
            }
        }
    }
    eg.rebuild();
    merged
}

fn main() {
    let path = std::env::args().nth(1).unwrap_or_else(|| {
        eprintln!("usage: mltl_nary PROGRAM [--types machine]");
        std::process::exit(2);
    });
    let src = std::fs::read_to_string(&path).unwrap_or_else(|e| {
        eprintln!("error reading '{path}': {e}");
        std::process::exit(1);
    });
    let enabled = Enabled::from_env();

    let surface = semi_persistent_egraph::parser::parse_program_v2(&src).unwrap_or_else(|e| {
        eprintln!("parse error: {e}");
        std::process::exit(1);
    });
    let mut interp = Interpreter::<Cfg, MachineLit, MachineModel, true, false>::new(MachineModel);
    let mut globals = GlobalCtx::new();
    let checked = sortcheck_program(surface, &mut interp.eg, &interp.model, &mut globals)
        .unwrap_or_else(|e| {
            eprintln!("{}", e.render(&src));
            std::process::exit(1);
        });

    // The program ends `(run R)` then `(dump-egraph ...)`. Everything before the
    // run executes as written; the run is replaced by R single rounds, each
    // followed by one n-ary pass; the rest executes as written.
    let run_at = checked
        .iter()
        .rposition(|c| matches!(c, CCommand::Run { .. }));
    let Some(run_at) = run_at else {
        interp.run_checked(&checked).unwrap_or_else(|e| {
            eprintln!("error: {e}");
            std::process::exit(1);
        });
        return;
    };
    let (ruleset, limit) = match &checked[run_at] {
        CCommand::Run { ruleset, limit, .. } => (*ruleset, *limit),
        _ => unreachable!(),
    };
    let fail = |e| -> ! {
        eprintln!("error: {e}");
        std::process::exit(1);
    };
    interp
        .run_checked(&checked[..run_at])
        .unwrap_or_else(|e| fail(e));

    // Looked up after the declarations have run. The integer literal operator is
    // read off an existing bound, so a program with no bounded operator simply
    // gives the temporal rules nothing to build with.
    let find_int = |eg: &Eg| {
        eg.node_ids().find_map(|id| match eg.get_lit_val(id) {
            Some(MachineLit::I64(_)) => Some(eg.node_op(id)),
            _ => None,
        })
    };
    let ops = Ops {
        and: interp.eg.op("And"),
        or: interp.eg.op("Or"),
        not: interp.eg.op("Not"),
        global: interp.eg.op("Global"),
        future: interp.eg.op("Future"),
        interval: interp.eg.op("Interval"),
        int: find_int(&interp.eg),
    };

    let mut fired = Fired::default();
    let (mut t_semper, mut t_rust) = (0.0f64, 0.0f64);
    let mut rounds = 0u64;
    for _ in 0..limit {
        rounds += 1;
        let t = Instant::now();
        let one = CCommand::Run {
            ruleset,
            limit: 1,
            until: None,
        };
        interp
            .run_checked(std::slice::from_ref(&one))
            .unwrap_or_else(|e| fail(e));
        t_semper += t.elapsed().as_secs_f64();
        let saturated = interp.last_sat().is_some_and(|s| s.saturated);

        let t = Instant::now();
        let changed = if enabled.any() {
            pass(&mut interp.eg, &ops, enabled, &mut fired)
        } else {
            0
        };
        t_rust += t.elapsed().as_secs_f64();
        if saturated && changed == 0 {
            break;
        }
    }
    interp
        .run_checked(&checked[run_at + 1..])
        .unwrap_or_else(|e| fail(e));

    eprintln!(
        "mltl_nary: rounds {rounds}, nodes {}, fired merge {} factor {} narrow {}, \
         semper {t_semper:.3}s, rust {t_rust:.3}s",
        interp.eg.len(),
        fired.merge,
        fired.factor,
        fired.narrow,
    );
}
