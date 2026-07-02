// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Equality saturation driver loop.

use crate::EGraphConfig;
use crate::apply::{PreparedRule, apply_rule};
use crate::canon::{MSetCanon, VarCanon};
use crate::containers::DenseId;
use crate::egraph::EGraph;
use crate::index::IndexStore;
use crate::lit_model::LitModel;
use crate::literal::LitVal;

/// Result of a saturation run.
#[derive(Clone, Debug)]
pub struct SatResult {
    /// Number of iterations executed.
    pub iterations: usize,
    /// Whether a fixpoint was reached (no new merges/insertions).
    pub saturated: bool,
    /// Total e-matching steps (partial-match extensions) across all rounds and
    /// rules — see [`crate::ematch::match_steps`]. This is the direct measure
    /// of match work; comparing it between [`saturate`] and [`saturate_semi`]
    /// quantifies how much rediscovery semi-naive avoids.
    pub match_steps: u64,
}

/// Which saturation algorithm to run.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Default)]
pub enum SaturationStrategy {
    /// Rediscover every match each round (`saturate`).
    #[default]
    Naive,
    /// Match only what changed each round via the k-variant decomposition
    /// (`saturate_semi`). No automatic fallback to naive.
    SemiNaive,
}

/// Run equality saturation for up to `limit` iterations.
pub fn saturate<Cfg, L, M, S, const T: bool, const P: bool>(
    rules: &[PreparedRule<Cfg::O, S, L>],
    eg: &mut EGraph<Cfg, L, T, P>,
    model: &M,
    limit: usize,
    globals: &crate::resolve::GlobalCtx<S, Cfg::G>,
) -> SatResult
where
    Cfg: EGraphConfig,
    S: DenseId,
    L: LitVal,
    M: LitModel<Value = L>,
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
{
    let steps_base = crate::ematch::match_steps();
    for i in 0..limit {
        eg.rebuild();
        let index = IndexStore::build(eg);
        let stats = crate::schedule::IndexStats::from_index(&index);
        let mut changes = 0;
        for rule in rules {
            changes += apply_rule(rule, eg, &index, &stats, model, globals);
        }
        if changes == 0 {
            return SatResult {
                iterations: i + 1,
                saturated: true,
                match_steps: crate::ematch::match_steps() - steps_base,
            };
        }
    }
    SatResult {
        iterations: limit,
        saturated: false,
        match_steps: crate::ematch::match_steps() - steps_base,
    }
}

// ===========================================================================
// Semi-naive saturation
// ===========================================================================

use crate::index::VariantIndex;
use crate::resolve::{RAtom, ResolvedQuery};
use crate::schedule::IndexStats;
use std::hash::Hash;

/// The op a join atom scans, or `None` for atoms that don't scan an index
/// (`Lit`, `Eq`, `EqGlobal`). Atoms with an op are the ones that participate
/// in the semi-naive variant decomposition — see the design doc, "Which Atoms
/// Count as Positions": only relation-scanning atoms generate candidate nodes;
/// built-in constraints have no delta.
fn atom_op<O: Copy, S, V>(atom: &RAtom<O, S, V>) -> Option<O> {
    match atom {
        RAtom::Plain { op, .. }
        | RAtom::AExact { op, .. }
        | RAtom::APrefix { op, .. }
        | RAtom::ASuffix { op, .. }
        | RAtom::ABoth { op, .. }
        | RAtom::ACExact { op, .. }
        | RAtom::ACSub { op, .. }
        | RAtom::ACIExact { op, .. }
        | RAtom::ACISub { op, .. }
        | RAtom::LitBind { op, .. } => Some(*op),
        RAtom::Lit { .. } | RAtom::Eq(..) | RAtom::EqGlobal(..) => None,
    }
}

/// Indices (stable `atom_id`s) of the join atoms in a rule — the atoms the
/// semi-naive variant loop ranges over. Excludes `Lit`/`Eq`/`EqGlobal`.
fn join_atom_indices<O: Copy, S, V>(rq: &ResolvedQuery<O, S, V>) -> Vec<usize> {
    rq.atoms
        .iter()
        .enumerate()
        .filter(|(_, a)| atom_op(a).is_some())
        .map(|(i, _)| i)
        .collect()
}

/// The node variable an atom binds, or `None` for the binary constraint atoms
/// (`Eq`, `EqGlobal`).
#[cfg(test)]
fn atom_node<O, S, V>(atom: &RAtom<O, S, V>) -> Option<crate::ast::VarId> {
    match atom {
        RAtom::Plain { node, .. }
        | RAtom::Lit { node, .. }
        | RAtom::AExact { node, .. }
        | RAtom::APrefix { node, .. }
        | RAtom::ASuffix { node, .. }
        | RAtom::ABoth { node, .. }
        | RAtom::ACExact { node, .. }
        | RAtom::ACSub { node, .. }
        | RAtom::ACIExact { node, .. }
        | RAtom::ACISub { node, .. }
        | RAtom::LitBind { node, .. } => Some(*node),
        RAtom::Eq(..) | RAtom::EqGlobal(..) => None,
    }
}

/// Stats for the semi-naive variant whose delta atom is `delta_atom`.
///
/// Each join atom's driver-scan cardinality is set by its **mode in this
/// flavor**, which is per-atom, not per-op (two atoms with the same op can have
/// different modes — see the design doc "How a Variant Executes"). So we fill
/// `atom_card` per atom rather than clobbering `op_card` by op:
///
/// | atom `j` | mode | base cardinality |
/// |----------|------|------------------|
/// | `j == delta_atom` | delta      | `|delta.by_op[op_j]|` |
/// | `j <  delta_atom` | full∖delta | `|full.by_op[op_j]| − |delta.by_op[op_j]|` |
/// | `j >  delta_atom` | full       | `|full.by_op[op_j]|` |
///
/// `full∖delta` is exact and O(1) because `delta ⊆ full` per key. The scheduler
/// then picks most-selective-first from these real per-flavor numbers; the
/// `VariantIndex` applies the matching modes at execution by `atom_id`.
fn variant_stats<O, S, V, Cfg>(
    rq: &ResolvedQuery<O, S, V>,
    delta_atom: usize,
    full: &IndexStore<Cfg>,
    delta: &IndexStore<Cfg>,
) -> IndexStats<O>
where
    O: DenseId + Hash,
    Cfg: EGraphConfig<O = O>,
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
{
    let mut stats = IndexStats::from_index(full);
    for (j, atom) in rq.atoms.iter().enumerate() {
        let Some(op) = atom_op(atom) else { continue };
        let full_card = full.by_op.get(&op).map(|sv| sv.len()).unwrap_or(0);
        let delta_card = delta.by_op.get(&op).map(|sv| sv.len()).unwrap_or(0);
        let card = match j.cmp(&delta_atom) {
            std::cmp::Ordering::Equal => delta_card,            // delta
            std::cmp::Ordering::Less => full_card - delta_card, // full ∖ delta
            std::cmp::Ordering::Greater => full_card,           // full
        };
        stats.atom_card.insert(j, card);
    }
    stats
}

/// Schedule one (rule, variant) against `vindex` and apply its actions to
/// every match. Returns the number of changes applied.
fn run_rule_variant<Cfg, L, M, S, const T: bool, const P: bool>(
    rule: &PreparedRule<Cfg::O, S, L>,
    eg: &mut EGraph<Cfg, L, T, P>,
    vindex: &VariantIndex<'_, Cfg>,
    stats: &IndexStats<Cfg::O>,
    model: &M,
    globals: &crate::resolve::GlobalCtx<S, Cfg::G>,
) -> usize
where
    Cfg: EGraphConfig,
    S: DenseId,
    L: LitVal,
    M: LitModel<Value = L>,
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
{
    let plan = crate::schedule::schedule_with_stats(&rule.query, stats);
    let mut matches = crate::ematch::run_query(&plan, eg, vindex, globals);
    let mut changes = 0;
    for m in &mut matches {
        for action in &rule.actions {
            changes += crate::apply::apply_action(action, m, eg, model, globals);
        }
    }
    changes
}

/// Semi-naive saturation: equivalent to [`saturate`] but, each round after
/// the first, restricts matching to matches involving at least one node that
/// changed in the previous round (the delta), via the k-variant decomposition.
///
/// Round 0 runs naive (the whole graph is "new"). Rounds ≥ 1 run, per rule,
/// one variant per join atom: variant `i` reads delta for atom `i`, full∖delta
/// for atoms `< i`, and full for atoms `> i`. The touched log feeding the
/// delta is reset each round.
pub fn saturate_semi<Cfg, L, M, S, const T: bool, const P: bool>(
    rules: &[PreparedRule<Cfg::O, S, L>],
    eg: &mut EGraph<Cfg, L, T, P>,
    model: &M,
    limit: usize,
    globals: &crate::resolve::GlobalCtx<S, Cfg::G>,
) -> SatResult
where
    Cfg: EGraphConfig,
    S: DenseId,
    L: LitVal,
    M: LitModel<Value = L>,
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
{
    let steps_base = crate::ematch::match_steps();
    for i in 0..limit {
        eg.rebuild();
        let full = IndexStore::build(eg);
        // delta = everything touched since the previous round's index build
        // (fresh nodes from the last round's apply + this round's recanon).
        let delta = if i == 0 {
            None
        } else {
            Some(IndexStore::build_delta(eg, eg.touched()))
        };
        eg.clear_touched();

        let mut changes = 0;
        match &delta {
            // Round 0: naive — the whole graph is new.
            None => {
                let stats = IndexStats::from_index(&full);
                let vindex = VariantIndex::naive(&full);
                for rule in rules {
                    changes += run_rule_variant(rule, eg, &vindex, &stats, model, globals);
                }
            }
            // Rounds ≥ 1: one variant per join atom.
            Some(delta) => {
                let full_stats = IndexStats::from_index(&full);
                for rule in rules {
                    let jatoms = join_atom_indices(&rule.query);
                    if jatoms.is_empty() {
                        // No scanning atoms (e.g. a bare-literal rule): run it
                        // naive so its matches are never missed.
                        let vindex = VariantIndex::naive(&full);
                        changes += run_rule_variant(rule, eg, &vindex, &full_stats, model, globals);
                        continue;
                    }
                    for &di in &jatoms {
                        let stats = variant_stats(&rule.query, di, &full, delta);
                        let vindex = VariantIndex::variant(&full, delta, di);
                        changes += run_rule_variant(rule, eg, &vindex, &stats, model, globals);
                    }
                }
            }
        }

        if changes == 0 {
            return SatResult {
                iterations: i + 1,
                saturated: true,
                match_steps: crate::ematch::match_steps() - steps_base,
            };
        }
    }
    SatResult {
        iterations: limit,
        saturated: false,
        match_steps: crate::ematch::match_steps() - steps_base,
    }
}

/// Like `saturate`, but prints each match and union when `labels` is provided.
pub fn saturate_trace<Cfg, L, M, S, const T: bool, const P: bool>(
    rules: &[(&str, PreparedRule<Cfg::O, S, L>)],
    eg: &mut EGraph<Cfg, L, T, P>,
    model: &M,
    limit: usize,
    globals: &crate::resolve::GlobalCtx<S, Cfg::G>,
) -> SatResult
where
    Cfg: EGraphConfig,
    S: DenseId,
    L: LitVal,
    M: LitModel<Value = L>,
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
{
    use crate::ematch::run_query;

    let steps_base = crate::ematch::match_steps();
    let mut total_iter = 0;
    for i in 0..limit {
        total_iter = i + 1;
        eg.rebuild();
        let index = IndexStore::build(eg);
        let stats = crate::schedule::IndexStats::from_index(&index);
        let vindex = crate::index::VariantIndex::naive(&index);
        let mut changes = 0;
        for (label, rule) in rules {
            let plan = crate::schedule::schedule_with_stats(&rule.query, &stats);
            let shape = &plan.shape;
            let mut matches = run_query(&plan, eg, &vindex, globals);
            for m in &mut matches {
                // Print node bindings (skip internal ?-prefixed names)
                let binds: Vec<String> = shape
                    .nodes
                    .iter()
                    .enumerate()
                    .filter(|(_, name)| !name.starts_with('?'))
                    .map(|(i, name)| {
                        let vid = crate::ast::VarId::new(i as u16);
                        format!("{name}=e{}", m.get(vid).to_usize())
                    })
                    .collect();
                let lit_binds: Vec<String> = shape
                    .lit_vals
                    .iter()
                    .enumerate()
                    .map(|(i, name)| {
                        let vid = crate::ast::LitValVarId::new(i as u16);
                        let lid = m.get_lit_val(vid);
                        format!("{name}={}", eg.lits().get(lid))
                    })
                    .collect();
                let all_binds = [binds, lit_binds].concat().join(", ");
                eprint!("  [{label}] match: {all_binds}");

                for action in &rule.actions {
                    changes += crate::apply::apply_action(action, m, eg, model, globals);
                }
                eprintln!();
            }
        }
        if changes == 0 {
            eprintln!("-- fixpoint after {total_iter} iterations --");
            return SatResult {
                iterations: total_iter,
                saturated: true,
                match_steps: crate::ematch::match_steps() - steps_base,
            };
        }
        eprintln!("-- iteration {total_iter}: {changes} changes --");
    }
    SatResult {
        iterations: total_iter,
        saturated: false,
        match_steps: crate::ematch::match_steps() - steps_base,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::apply::compile_rewrite;
    use crate::id::{OpId, SortId};
    use crate::literal::{NiraLitVal, NiraModel};
    use crate::nodes::DefaultConfig;
    use crate::registry::{OpRegistry, SortRegistry};
    use crate::test_helpers::{parse_pattern, parse_rhs};

    type EG = EGraph<DefaultConfig, NiraLitVal, false, false>;

    fn make_eg() -> EG {
        let mut eg = EG::from_model(&NiraModel);
        let e = eg.intern_sort("IExpr");
        let ibig = eg.sorts().id_by_name("IBig").unwrap();
        eg.register_op2("f", e, e, e);
        eg.register_op1("g", e, e);
        eg.register_op0("a", e);
        eg.register_op0("b", e);
        eg.register_op0("c", e);
        eg.register_opn("ILit", &[ibig], e);
        eg.register_op2("IAdd", e, e, e);
        eg.register_op2("IMul", e, e, e);
        eg.register_mset("add", e, e);
        eg.register_set("union", e, e);
        eg.register_a("concat", e, e, crate::registry::AssocDir::Right);
        eg
    }

    fn mk_rule<const TRACK: bool>(
        lhs: &str,
        rhs: &str,
        ops: &OpRegistry<OpId, SortId, TRACK>,
        sorts: &SortRegistry<SortId, TRACK>,
        rules: &mut crate::registry::RuleRegistry<TRACK>,
    ) -> PreparedRule<OpId, SortId, NiraLitVal> {
        let model = NiraModel;
        let l = parse_pattern(lhs);
        let r = parse_rhs(rhs);
        compile_rewrite(
            "test",
            lhs,
            rhs,
            &l,
            &r,
            &[],
            false,
            ops,
            sorts,
            rules,
            &model,
            &crate::resolve::GlobalCtx::<_, ()>::new(),
        )
        .unwrap()
    }

    /// Like `mk_rule` but with `when` side-conditions: the LHS plus extra
    /// top-level patterns that flatten into independent atoms sharing vars.
    fn mk_rule_when<const TRACK: bool>(
        lhs: &str,
        when: &[&str],
        rhs: &str,
        ops: &OpRegistry<OpId, SortId, TRACK>,
        sorts: &SortRegistry<SortId, TRACK>,
        rules: &mut crate::registry::RuleRegistry<TRACK>,
    ) -> PreparedRule<OpId, SortId, NiraLitVal> {
        let model = NiraModel;
        let l = parse_pattern(lhs);
        let whens: Vec<_> = when.iter().map(|s| parse_pattern(s)).collect();
        let r = parse_rhs(rhs);
        compile_rewrite(
            "test",
            lhs,
            rhs,
            &l,
            &r,
            &whens,
            false,
            ops,
            sorts,
            rules,
            &model,
            &crate::resolve::GlobalCtx::<_, ()>::new(),
        )
        .unwrap()
    }

    /// Build the `ByContains` scenario at scale `n_distractors`: exactly one
    /// `g`-node binding `x`, one `add` node that contains `x` (the only match),
    /// and `n_distractors` further distinct `add` nodes that do NOT contain
    /// `x`. Returns the egraph + the prepared `when`-clause rule
    /// `(g x)` with side condition `(add x ..rest)`.
    ///
    /// The side-condition variadic atom has its element `x` already bound (by
    /// `(g x)`) but its node unbound — the exact case `IndexLookup::ByContains`
    /// exists to optimize: drive the `add` atom from the few parents that
    /// contain `x`, instead of scanning the whole `by_op[add]` bucket.
    fn build_by_contains_scenario(
        n_distractors: usize,
    ) -> (EG, PreparedRule<OpId, SortId, NiraLitVal>) {
        let mut eg = make_eg();
        let mut rr = crate::registry::RuleRegistry::<false>::new();
        let oadd = eg.ops().id_by_name("add").unwrap();
        let og = eg.ops().id_by_name("g").unwrap();
        let of = eg.ops().id_by_name("f").unwrap();
        let oa = eg.ops().id_by_name("a").unwrap();
        let ob = eg.ops().id_by_name("b").unwrap();

        // Exactly ONE g-node, binding x once.
        let x = eg.add(oa, &[]);
        let _gx = eg.add(og, &[x]);
        // The single matching add: contains x at multiplicity 1.
        let bx = eg.add(ob, &[]);
        let _add_with_x = eg.add(oadd, &[x, bx]);
        // N distinct distractor adds from f-towers (never g, never contain x).
        let mut prev = eg.add(ob, &[]);
        for _ in 0..n_distractors {
            let e1 = eg.add(of, &[prev, prev]);
            let e2 = eg.add(of, &[e1, prev]);
            eg.add(oadd, &[e1, e2]);
            prev = e2;
        }
        eg.rebuild();

        let rule = mk_rule_when(
            "(g x)",
            &["(add x ..rest)"],
            "(g x)",
            eg.ops(),
            eg.sorts(),
            &mut rr,
        );
        (eg, rule)
    }

    /// Measure the e-matching match-steps for the `ByContains` scenario at a
    /// given distractor count, under the naive index view (one round).
    fn by_contains_match_steps(n_distractors: usize) -> (u64, usize) {
        use crate::ematch::{match_steps, reset_match_steps, set_match_step_counting};
        let (eg, rule) = build_by_contains_scenario(n_distractors);
        let full = IndexStore::build(&eg);
        let stats = IndexStats::from_index(&full);
        let plan = crate::schedule::schedule_with_stats(&rule.query, &stats);
        let vindex = VariantIndex::naive(&full);
        let globals = crate::resolve::GlobalCtx::<SortId, crate::id::ENodeId>::new();
        set_match_step_counting(true);
        reset_match_steps();
        let matches = crate::ematch::run_query(&plan, &eg, &vindex, &globals);
        (match_steps(), matches.len())
    }

    // -- Instrumentation: semi-naive does less match work than naive --
    //
    // End-to-end check of the `SatResult.match_steps` counter: over a
    // multi-round saturation, semi-naive must reach the same fixpoint as naive
    // while exploring strictly fewer partial-match extensions, because it
    // rediscovers far fewer already-applied matches each round. This is the
    // headline reason semi-naive exists, made measurable.
    #[test]
    fn semi_naive_does_less_match_work() {
        crate::ematch::set_match_step_counting(true);
        let globals = crate::resolve::GlobalCtx::<SortId, crate::id::ENodeId>::new();
        // A converging saturation with several rounds of growth: commute +
        // project + const-fold-ish AC growth over a non-trivial seed.
        let setup = || -> (EG, Vec<PreparedRule<OpId, SortId, NiraLitVal>>, usize) {
            let mut eg = make_eg();
            let mut rr = crate::registry::RuleRegistry::<false>::new();
            let of = eg.ops().id_by_name("f").unwrap();
            let oa = eg.ops().id_by_name("a").unwrap();
            let ob = eg.ops().id_by_name("b").unwrap();
            let oc = eg.ops().id_by_name("c").unwrap();
            // a small tower of f's so multiple rounds fire.
            let a = eg.add(oa, &[]);
            let b = eg.add(ob, &[]);
            let c = eg.add(oc, &[]);
            let f1 = eg.add(of, &[a, b]);
            let f2 = eg.add(of, &[f1, c]);
            let _f3 = eg.add(of, &[f2, a]);
            let r1 = mk_rule("(f x y)", "(f y x)", eg.ops(), eg.sorts(), &mut rr);
            let r2 = mk_rule(
                "(f (f x y) z)",
                "(f x (f y z))",
                eg.ops(),
                eg.sorts(),
                &mut rr,
            );
            let n = eg.node_count();
            (eg, vec![r1, r2], n)
        };

        let (mut a, rules_a, n) = setup();
        let ra = saturate::<DefaultConfig, _, _, _, false, false>(
            &rules_a, &mut a, &NiraModel, 30, &globals,
        );
        let (mut b, rules_b, n2) = setup();
        let rb = saturate_semi::<DefaultConfig, _, _, _, false, false>(
            &rules_b, &mut b, &NiraModel, 30, &globals,
        );

        // Same fixpoint.
        assert_eq!(n, n2);
        assert_eq!(ra.saturated, rb.saturated, "saturation flag mismatch");
        assert_eq!(
            partition_over(&a, n),
            partition_over(&b, n),
            "naive vs semi-naive partition mismatch"
        );
        // …reached with strictly less match work.
        assert!(
            rb.match_steps < ra.match_steps,
            "semi-naive should explore fewer match steps than naive \
             (naive={}, semi={})",
            ra.match_steps,
            rb.match_steps
        );
    }

    // -- ByContains optimization: variadic atom with a bound element --
    //
    // A variadic side-condition atom whose ELEMENT is bound but whose NODE is
    // not (`(g x)` then `(add x ..rest)`) used to be compiled to drive from the
    // full `by_op[add]` bucket and filter in DecomposeAC — so match-steps
    // scaled with the TOTAL number of `add` nodes even though only one contains
    // `x`. `emit_variadic_join` now intersects `by_op[add]` with
    // `by_contains[x]` (the variadic analogue of `Plain`'s `ByChildPos`), so
    // the driver is the few parents containing `x` and the work is independent
    // of the distractor count.
    //
    // This pins the optimization: match-steps must stay ~constant as the
    // distractor add count grows 10 → 210, while still finding the one match.
    #[test]
    fn by_contains_narrows_variadic_driver() {
        let (small, m_small) = by_contains_match_steps(10);
        let (large, m_large) = by_contains_match_steps(210);

        // Correctness is invariant: exactly one match at either scale.
        assert_eq!(m_small, 1, "scenario should yield exactly one match");
        assert_eq!(m_large, 1, "scenario should yield exactly one match");

        // 210 vs 10 distractors adds 200 more non-matching `add` nodes. With
        // ByContains the driver is `by_contains[x]` (one entry), so the extra
        // 200 nodes cost nothing; match-steps stay within a small constant.
        // (Pre-fix this delta was ~200.) Allow generous slack for incidental
        // per-round bookkeeping while still catching any return to linear scan.
        assert!(
            large <= small + 10,
            "ByContains should make variadic match work independent of the \
             distractor count, but it grew: small={small} large={large} steps"
        );
    }

    // -- Differential check: saturate (naive) vs saturate_semi --

    /// Normalized equivalence partition over the original node id range,
    /// for comparing two saturated e-graphs.
    fn partition_over<const T: bool, const P: bool>(
        eg: &EGraph<DefaultConfig, NiraLitVal, T, P>,
        n: usize,
    ) -> Vec<u32> {
        use crate::containers::DenseId;
        let mut label = std::collections::HashMap::new();
        let mut next = 0u32;
        (0..n)
            .map(|i| {
                let r = eg.class_repr(crate::id::ENodeId::from_usize(i)).to_usize();
                *label.entry(r).or_insert_with(|| {
                    let l = next;
                    next += 1;
                    l
                })
            })
            .collect()
    }

    /// Build the scenario twice, saturate one naive and one semi-naive, and
    /// assert they reach the same fixpoint and the same equalities over the
    /// original nodes.
    fn diff_test(setup: impl Fn() -> (EG, Vec<PreparedRule<OpId, SortId, NiraLitVal>>, usize)) {
        let globals = crate::resolve::GlobalCtx::<SortId, crate::id::ENodeId>::new();

        let (mut a, rules_a, n) = setup();
        let ra = saturate::<DefaultConfig, _, _, _, false, false>(
            &rules_a, &mut a, &NiraModel, 50, &globals,
        );

        let (mut b, rules_b, n2) = setup();
        let rb = saturate_semi::<DefaultConfig, _, _, _, false, false>(
            &rules_b, &mut b, &NiraModel, 50, &globals,
        );

        assert_eq!(n, n2, "setup must be deterministic");
        assert_eq!(ra.saturated, rb.saturated, "saturation flag mismatch");
        assert_eq!(
            partition_over(&a, n),
            partition_over(&b, n),
            "naive vs semi-naive partition over original nodes differs"
        );
    }

    #[test]
    fn diff_commute() {
        diff_test(|| {
            let mut eg = make_eg();
            let mut rr = crate::registry::RuleRegistry::<false>::new();
            let a = eg.add(eg.ops().id_by_name("a").unwrap(), &[]);
            let b = eg.add(eg.ops().id_by_name("b").unwrap(), &[]);
            let _fab = eg.add(eg.ops().id_by_name("f").unwrap(), &[a, b]);
            let r = mk_rule("(f x y)", "(f y x)", eg.ops(), eg.sorts(), &mut rr);
            let n = eg.node_count();
            (eg, vec![r], n)
        });
    }

    #[test]
    fn diff_multi_rule() {
        diff_test(|| {
            let mut eg = make_eg();
            let mut rr = crate::registry::RuleRegistry::<false>::new();
            let a = eg.add(eg.ops().id_by_name("a").unwrap(), &[]);
            let b = eg.add(eg.ops().id_by_name("b").unwrap(), &[]);
            let _fab = eg.add(eg.ops().id_by_name("f").unwrap(), &[a, b]);
            let r1 = mk_rule("(f x y)", "(f y x)", eg.ops(), eg.sorts(), &mut rr);
            let r2 = mk_rule("(f x y)", "(g x)", eg.ops(), eg.sorts(), &mut rr);
            let n = eg.node_count();
            (eg, vec![r1, r2], n)
        });
    }

    #[test]
    fn diff_const_fold() {
        use num_bigint::BigInt;
        diff_test(|| {
            let mut eg = make_eg();
            let mut rr = crate::registry::RuleRegistry::<false>::new();
            let at_ibig = eg.ops().id_by_name("@IBig").unwrap();
            let ilit = eg.ops().id_by_name("ILit").unwrap();
            let iadd = eg.ops().id_by_name("IAdd").unwrap();
            let v3 = eg.intern_lit(NiraLitVal::Int(BigInt::from(3)));
            let n3 = eg.add_lit(at_ibig, v3);
            let lit3 = eg.add(ilit, &[n3]);
            let v5 = eg.intern_lit(NiraLitVal::Int(BigInt::from(5)));
            let n5 = eg.add_lit(at_ibig, v5);
            let lit5 = eg.add(ilit, &[n5]);
            let _add = eg.add(iadd, &[lit3, lit5]);
            let r = mk_rule(
                "(IAdd (ILit x) (ILit y))",
                "(ILit (+ x y))",
                eg.ops(),
                eg.sorts(),
                &mut rr,
            );
            let n = eg.node_count();
            (eg, vec![r], n)
        });
    }

    #[test]
    fn diff_two_level_fold() {
        use num_bigint::BigInt;
        diff_test(|| {
            let mut eg = make_eg();
            let mut rr = crate::registry::RuleRegistry::<false>::new();
            let at_ibig = eg.ops().id_by_name("@IBig").unwrap();
            let ilit = eg.ops().id_by_name("ILit").unwrap();
            let iadd = eg.ops().id_by_name("IAdd").unwrap();
            let imul = eg.ops().id_by_name("IMul").unwrap();
            let mk = |eg: &mut EG, k: i64| {
                let v = eg.intern_lit(NiraLitVal::Int(BigInt::from(k)));
                let n = eg.add_lit(at_ibig, v);
                eg.add(ilit, &[n])
            };
            let l3 = mk(&mut eg, 3);
            let l4 = mk(&mut eg, 4);
            let l5 = mk(&mut eg, 5);
            let add = eg.add(iadd, &[l4, l5]);
            let _mul = eg.add(imul, &[l3, add]);
            let add_rule = mk_rule(
                "(IAdd (ILit x) (ILit y))",
                "(ILit (+ x y))",
                eg.ops(),
                eg.sorts(),
                &mut rr,
            );
            let mul_rule = mk_rule(
                "(IMul (ILit x) (ILit y))",
                "(ILit (* x y))",
                eg.ops(),
                eg.sorts(),
                &mut rr,
            );
            let n = eg.node_count();
            (eg, vec![add_rule, mul_rule], n)
        });
    }

    // -- #1: randomized differential proptest --
    mod prop {
        use super::*;
        use proptest::prelude::*;

        // Rule pool over the f/g/a/b/c signature (fixed-arity; AC/ACI covered
        // separately). Each entry is (lhs, rhs).
        const POOL: &[(&str, &str)] = &[
            ("(f x y)", "(f y x)"), // commute
            ("(f x y)", "(g x)"),   // project
            ("(g x)", "(f x x)"),   // expand
        ];

        /// Build an e-graph from a random node-spec list and a random subset
        /// of the rule pool. Deterministic in its inputs, so it can be run
        /// twice to produce identical e-graphs.
        fn build(
            specs: &[u8],
            rule_mask: u8,
        ) -> (EG, Vec<PreparedRule<OpId, SortId, NiraLitVal>>, usize) {
            let mut eg = make_eg();
            let mut rr = crate::registry::RuleRegistry::<false>::new();
            let oa = eg.ops().id_by_name("a").unwrap();
            let ob = eg.ops().id_by_name("b").unwrap();
            let oc = eg.ops().id_by_name("c").unwrap();
            let og = eg.ops().id_by_name("g").unwrap();
            let of = eg.ops().id_by_name("f").unwrap();

            let mut nodes: Vec<crate::id::ENodeId> = Vec::new();
            for &s in specs {
                let id = match s % 5 {
                    0 => eg.add(oa, &[]),
                    1 => eg.add(ob, &[]),
                    2 => eg.add(oc, &[]),
                    3 => {
                        let c = *nodes.last().unwrap_or(&eg.add(oa, &[]));
                        eg.add(og, &[c])
                    }
                    _ => {
                        let c1 = nodes.first().copied().unwrap_or_else(|| eg.add(oa, &[]));
                        let c2 = nodes.last().copied().unwrap_or_else(|| eg.add(ob, &[]));
                        eg.add(of, &[c1, c2])
                    }
                };
                nodes.push(id);
            }

            let mut rules = Vec::new();
            for (bit, (lhs, rhs)) in POOL.iter().enumerate() {
                if rule_mask & (1 << bit) != 0 {
                    rules.push(mk_rule(lhs, rhs, eg.ops(), eg.sorts(), &mut rr));
                }
            }
            let n = eg.node_count();
            (eg, rules, n)
        }

        proptest! {
            #![proptest_config(ProptestConfig::with_cases(512))]

            /// Random input term + random rule subset: naive and semi-naive
            /// saturation must agree on the equivalence partition over the
            /// original nodes (the observational-equivalence property) and on
            /// the saturation flag.
            ///
            /// Node *count* is deliberately not asserted: it is order-dependent
            /// (the node store is append-only and which representative wins a
            /// merge depends on discovery order), so two equivalent runs may
            /// materialize a different number of congruent transient nodes.
            #[test]
            fn diff_random(specs in proptest::collection::vec(0u8..5, 1..7), mask in 0u8..8) {
                let globals = crate::resolve::GlobalCtx::<SortId, crate::id::ENodeId>::new();

                let (mut a, rules_a, n) = build(&specs, mask);
                let ra = saturate::<DefaultConfig, _, _, _, false, false>(
                    &rules_a, &mut a, &NiraModel, 40, &globals,
                );
                let (mut b, rules_b, _n2) = build(&specs, mask);
                let rb = saturate_semi::<DefaultConfig, _, _, _, false, false>(
                    &rules_b, &mut b, &NiraModel, 40, &globals,
                );

                prop_assert_eq!(ra.saturated, rb.saturated, "saturation flag");
                prop_assert_eq!(
                    partition_over(&a, n),
                    partition_over(&b, n),
                    "partition over original nodes"
                );
            }
        }

        // Nested same-op rule pool. `diff_random`'s POOL is single-level f/g,
        // so deep same-op nesting under multi-round delta propagation — the
        // design's flagship case, where a variant stacks several
        // FullMinusDelta cursors on the SAME op bucket — is never randomly
        // fuzzed there. These rules nest f within f (and g within f) so the
        // flattener emits multiple join atoms sharing an op.
        const NESTED_POOL: &[(&str, &str)] = &[
            ("(f (f x y) z)", "(f x (f y z))"), // re-associate
            ("(f (f x y) z)", "(g x)"),         // project from nested
            ("(f x (g y))", "(f (g y) x)"),     // commute past a g
            ("(g x)", "(f x x)"),               // grow
        ];

        fn build_nested(
            specs: &[u8],
            rule_mask: u8,
        ) -> (EG, Vec<PreparedRule<OpId, SortId, NiraLitVal>>, usize) {
            let mut eg = make_eg();
            let mut rr = crate::registry::RuleRegistry::<false>::new();
            let oa = eg.ops().id_by_name("a").unwrap();
            let ob = eg.ops().id_by_name("b").unwrap();
            let oc = eg.ops().id_by_name("c").unwrap();
            let og = eg.ops().id_by_name("g").unwrap();
            let of = eg.ops().id_by_name("f").unwrap();

            let mut nodes: Vec<crate::id::ENodeId> = Vec::new();
            for &s in specs {
                let id = match s % 5 {
                    0 => eg.add(oa, &[]),
                    1 => eg.add(ob, &[]),
                    2 => eg.add(oc, &[]),
                    3 => {
                        let c = *nodes.last().unwrap_or(&eg.add(oa, &[]));
                        eg.add(og, &[c])
                    }
                    _ => {
                        let c1 = nodes.first().copied().unwrap_or_else(|| eg.add(oa, &[]));
                        let c2 = nodes.last().copied().unwrap_or_else(|| eg.add(ob, &[]));
                        eg.add(of, &[c1, c2])
                    }
                };
                nodes.push(id);
            }

            let mut rules = Vec::new();
            for (bit, (lhs, rhs)) in NESTED_POOL.iter().enumerate() {
                if rule_mask & (1 << bit) != 0 {
                    rules.push(mk_rule(lhs, rhs, eg.ops(), eg.sorts(), &mut rr));
                }
            }
            let n = eg.node_count();
            (eg, rules, n)
        }

        proptest! {
            // Fewer cases + a tight iteration cap: the associativity rule makes
            // saturations blow up combinatorially, and each case runs the same
            // input twice (naive + semi-naive). The cap keeps wall-clock sane
            // while still fuzzing the stacked-FullMinusDelta machinery.
            #![proptest_config(ProptestConfig::with_cases(96))]

            /// Differential equivalence for NESTED same-op rules. Same oracle
            /// as `diff_random` (equivalence partition over the original
            /// nodes) but driving the multi-atom, same-op, stacked-
            /// FullMinusDelta machinery that the flat POOL never reaches.
            #[test]
            fn diff_random_nested(
                specs in proptest::collection::vec(0u8..5, 1..5),
                mask in 0u8..16,
            ) {
                let globals = crate::resolve::GlobalCtx::<SortId, crate::id::ENodeId>::new();

                let (mut a, rules_a, n) = build_nested(&specs, mask);
                let ra = saturate::<DefaultConfig, _, _, _, false, false>(
                    &rules_a, &mut a, &NiraModel, 12, &globals,
                );
                let (mut b, rules_b, _n2) = build_nested(&specs, mask);
                let rb = saturate_semi::<DefaultConfig, _, _, _, false, false>(
                    &rules_b, &mut b, &NiraModel, 12, &globals,
                );

                prop_assert_eq!(ra.saturated, rb.saturated, "saturation flag");
                prop_assert_eq!(
                    partition_over(&a, n),
                    partition_over(&b, n),
                    "nested same-op: partition over original nodes"
                );
            }
        }
    }

    // -- #2: variant disjointness (each new match emitted exactly once) --
    //
    // Final-state equivalence cannot see double-counting (rewrite application
    // is idempotent), so this is tested directly: collect each variant's match
    // set in one round and assert they are pairwise disjoint, and that their
    // union is exactly the naive matches involving >= 1 new (delta) node.
    #[test]
    fn variants_disjoint_and_complete() {
        use std::collections::HashSet;

        let mut eg = make_eg();
        let mut rr = crate::registry::RuleRegistry::<false>::new();
        // 2 join atoms: the outer f and the inner g.
        let rule = mk_rule("(f (g x) y)", "(g y)", eg.ops(), eg.sorts(), &mut rr);

        let of = eg.ops().id_by_name("f").unwrap();
        let og = eg.ops().id_by_name("g").unwrap();
        let oa = eg.ops().id_by_name("a").unwrap();
        let ob = eg.ops().id_by_name("b").unwrap();
        let oc = eg.ops().id_by_name("c").unwrap();

        // Baseline (all old): g(a), f(g(a), b).
        let a = eg.add(oa, &[]);
        let b = eg.add(ob, &[]);
        let ga = eg.add(og, &[a]);
        let _fgab = eg.add(of, &[ga, b]);
        eg.rebuild();
        eg.clear_touched();

        // One round of fresh nodes:
        let c = eg.add(oc, &[]);
        let gc = eg.add(og, &[c]); // new g
        let _fgcc = eg.add(of, &[gc, c]); // new f over NEW g  → match with BOTH atoms new
        let _fac = eg.add(of, &[ga, c]); // new f over OLD g   → match with only f new
        eg.rebuild();

        let touched: Vec<crate::id::ENodeId> = eg.touched().to_vec();
        let tset: HashSet<usize> = touched.iter().map(|g| g.to_usize()).collect();
        let full = IndexStore::build(&eg);
        let delta = IndexStore::build_delta(&eg, &touched);
        let globals = crate::resolve::GlobalCtx::<SortId, crate::id::ENodeId>::new();

        // Canonical key for a match: class-reps of every node variable.
        let key = |m: &crate::ematch::Match<DefaultConfig>| -> Vec<usize> {
            (0..rule.query.shape.nodes.len())
                .map(|i| {
                    let vid = crate::ast::VarId::new(i as u16);
                    eg.class_repr(m.get(vid)).to_usize()
                })
                .collect::<Vec<_>>()
        };

        // Run each variant's query (no application) and collect its match keys.
        let jatoms = join_atom_indices(&rule.query);
        assert!(jatoms.len() >= 2, "scenario needs a multi-atom rule");
        let mut per_variant: Vec<HashSet<Vec<usize>>> = Vec::new();
        for &di in &jatoms {
            let stats = variant_stats(&rule.query, di, &full, &delta);
            let plan = crate::schedule::schedule_with_stats(&rule.query, &stats);
            let vindex = VariantIndex::variant(&full, &delta, di);
            let matches = crate::ematch::run_query(&plan, &eg, &vindex, &globals);
            per_variant.push(matches.iter().map(&key).collect());
        }

        // Pairwise disjoint — no match emitted by two variants.
        for i in 0..per_variant.len() {
            for j in (i + 1)..per_variant.len() {
                let shared: Vec<_> = per_variant[i].intersection(&per_variant[j]).collect();
                assert!(
                    shared.is_empty(),
                    "variants {i} and {j} both emit matches {shared:?}"
                );
            }
        }

        // Completeness: union of variants == naive matches with >= 1 new atom.
        let union: HashSet<Vec<usize>> = per_variant.iter().flatten().cloned().collect();

        let naive_plan =
            crate::schedule::schedule_with_stats(&rule.query, &IndexStats::from_index(&full));
        let naive_vindex = VariantIndex::naive(&full);
        let naive_matches = crate::ematch::run_query(&naive_plan, &eg, &naive_vindex, &globals);
        let naive_new: HashSet<Vec<usize>> = naive_matches
            .iter()
            .filter(|m| {
                // a match is "new" if some join-atom node is in the delta
                rule.query.atoms.iter().any(|atom| match atom_node(atom) {
                    Some(vid) => tset.contains(&m.get(vid).to_usize()),
                    None => false,
                })
            })
            .map(&key)
            .collect();

        assert_eq!(
            union, naive_new,
            "union of variant matches != naive matches involving a new node"
        );
        // sanity: the scenario actually produced new matches
        assert!(!union.is_empty(), "expected at least one new match");
    }

    // -- per-atom cardinality: same op, different mode → different card --
    //
    // The crux of flavor-aware scheduling: in one semi-naive flavor, two atoms
    // sharing an op can have DIFFERENT driver-scan cardinalities because their
    // modes differ (delta vs full∖delta vs full). The old `op_card`-keyed stats
    // could not express this — one number per op. `variant_stats` now fills a
    // per-atom `atom_card`. This pins the three modes to their exact slice
    // sizes for `(f (f x y) z)` (atoms 0 and 1 both op `f`).
    #[test]
    fn variant_stats_per_atom_cardinality() {
        let mut eg = make_eg();
        let mut rr = crate::registry::RuleRegistry::<false>::new();
        let rule = mk_rule("(f (f x y) z)", "(g z)", eg.ops(), eg.sorts(), &mut rr);
        let of = eg.ops().id_by_name("f").unwrap();
        let oa = eg.ops().id_by_name("a").unwrap();
        let ob = eg.ops().id_by_name("b").unwrap();
        let oc = eg.ops().id_by_name("c").unwrap();

        // Baseline: 3 old f-nodes.
        let a = eg.add(oa, &[]);
        let b = eg.add(ob, &[]);
        let c = eg.add(oc, &[]);
        let fab = eg.add(of, &[a, b]);
        let _f1 = eg.add(of, &[fab, c]);
        let _f2 = eg.add(of, &[fab, a]);
        eg.rebuild();
        eg.clear_touched();

        // One round: add 2 fresh f-nodes (delta), leaving the 3 old ones.
        let fac = eg.add(of, &[a, c]);
        let _f3 = eg.add(of, &[fac, b]);
        eg.rebuild();

        let touched: Vec<crate::id::ENodeId> = eg.touched().to_vec();
        let full = IndexStore::build(&eg);
        let delta = IndexStore::build_delta(&eg, &touched);

        let full_f = full.by_op.get(&of).map(|s| s.len()).unwrap();
        let delta_f = delta.by_op.get(&of).map(|s| s.len()).unwrap();
        assert!(delta_f >= 1 && delta_f < full_f, "need a partial delta");

        let jatoms = join_atom_indices(&rule.query);
        assert_eq!(jatoms.len(), 2, "two same-op join atoms expected");
        let (a0, a1) = (jatoms[0], jatoms[1]);

        // Flavor with delta atom = a1: atom a0 is full∖delta, atom a1 is delta.
        // They share op `f` yet must get DIFFERENT per-atom cardinalities.
        let stats = variant_stats(&rule.query, a1, &full, &delta);
        assert_eq!(
            stats.atom_card.get(&a1).copied(),
            Some(delta_f),
            "delta atom should be sized at the delta bucket"
        );
        assert_eq!(
            stats.atom_card.get(&a0).copied(),
            Some(full_f - delta_f),
            "the lower (full∖delta) atom should be sized full − delta"
        );
        assert_ne!(
            stats.atom_card.get(&a0),
            stats.atom_card.get(&a1),
            "same-op atoms in one flavor must get distinct cardinalities"
        );

        // The opposite flavor (delta atom = a0): a0 is delta, a1 is full.
        let stats0 = variant_stats(&rule.query, a0, &full, &delta);
        assert_eq!(stats0.atom_card.get(&a0).copied(), Some(delta_f));
        assert_eq!(stats0.atom_card.get(&a1).copied(), Some(full_f));
    }

    // -- #2b: same-op-at-multiple-positions disjointness --
    //
    // The flagship design example is `mul(add, mul)`: two atoms share the op
    // `mul`. The #2 test above uses distinct ops (f over g), so the shared-op
    // interaction is never exercised: in one variant, two atoms read the SAME
    // `by_op` bucket — one as Delta, one as Difference(full, delta). The
    // scheduler now sizes each by its per-atom mode (see `variant_stats` /
    // `atom_card`), but correctness rests on the atom NUMBERING regardless
    // (mode is `compare(atom_id, i)`), independent of drive order. This pins
    // that down: whatever order the scheduler picks, the variants must stay
    // disjoint and complete.
    //
    // Rule `(f (f x y) z)`: atom 0 = outer f, atom 1 = inner f — both op `f`.
    #[test]
    fn variants_disjoint_same_op() {
        use std::collections::HashSet;

        let mut eg = make_eg();
        let mut rr = crate::registry::RuleRegistry::<false>::new();
        let rule = mk_rule("(f (f x y) z)", "(g z)", eg.ops(), eg.sorts(), &mut rr);

        let of = eg.ops().id_by_name("f").unwrap();
        let oa = eg.ops().id_by_name("a").unwrap();
        let ob = eg.ops().id_by_name("b").unwrap();
        let oc = eg.ops().id_by_name("c").unwrap();

        // Baseline (all old): fab = f(a,b); f(fab, c) — one outer match.
        let a = eg.add(oa, &[]);
        let b = eg.add(ob, &[]);
        let c = eg.add(oc, &[]);
        let fab = eg.add(of, &[a, b]);
        let _outer_old = eg.add(of, &[fab, c]); // old inner, old outer
        eg.rebuild();
        eg.clear_touched();

        // One round of fresh nodes producing a mix of newness profiles:
        let fac = eg.add(of, &[a, c]); // NEW inner f
        let _both_new = eg.add(of, &[fac, b]); // new outer over NEW inner → both atoms new
        let _outer_new = eg.add(of, &[fab, a]); // new outer over OLD inner → only outer new
        eg.rebuild();

        let touched: Vec<crate::id::ENodeId> = eg.touched().to_vec();
        let tset: HashSet<usize> = touched.iter().map(|g| g.to_usize()).collect();
        let full = IndexStore::build(&eg);
        let delta = IndexStore::build_delta(&eg, &touched);
        let globals = crate::resolve::GlobalCtx::<SortId, crate::id::ENodeId>::new();

        let key = |m: &crate::ematch::Match<DefaultConfig>| -> Vec<usize> {
            (0..rule.query.shape.nodes.len())
                .map(|i| {
                    let vid = crate::ast::VarId::new(i as u16);
                    eg.class_repr(m.get(vid)).to_usize()
                })
                .collect::<Vec<_>>()
        };

        let jatoms = join_atom_indices(&rule.query);
        assert!(jatoms.len() >= 2, "scenario needs a multi-atom rule");
        // Both join atoms must scan the SAME op for this test to be meaningful.
        let ops: HashSet<_> = jatoms
            .iter()
            .map(|&i| atom_op(&rule.query.atoms[i]).unwrap().to_usize())
            .collect();
        assert_eq!(ops.len(), 1, "expected both join atoms to share one op");

        let mut per_variant: Vec<HashSet<Vec<usize>>> = Vec::new();
        for &di in &jatoms {
            let stats = variant_stats(&rule.query, di, &full, &delta);
            let plan = crate::schedule::schedule_with_stats(&rule.query, &stats);
            let vindex = VariantIndex::variant(&full, &delta, di);
            let matches = crate::ematch::run_query(&plan, &eg, &vindex, &globals);
            per_variant.push(matches.iter().map(&key).collect());
        }

        // Pairwise disjoint.
        for i in 0..per_variant.len() {
            for j in (i + 1)..per_variant.len() {
                let shared: Vec<_> = per_variant[i].intersection(&per_variant[j]).collect();
                assert!(
                    shared.is_empty(),
                    "same-op variants {i} and {j} both emit {shared:?}"
                );
            }
        }

        // Completeness: union == naive matches involving ≥1 new node.
        let union: HashSet<Vec<usize>> = per_variant.iter().flatten().cloned().collect();
        let naive_plan =
            crate::schedule::schedule_with_stats(&rule.query, &IndexStats::from_index(&full));
        let naive_vindex = VariantIndex::naive(&full);
        let naive_matches = crate::ematch::run_query(&naive_plan, &eg, &naive_vindex, &globals);
        let naive_new: HashSet<Vec<usize>> = naive_matches
            .iter()
            .filter(|m| {
                rule.query.atoms.iter().any(|atom| match atom_node(atom) {
                    Some(vid) => tset.contains(&m.get(vid).to_usize()),
                    None => false,
                })
            })
            .map(&key)
            .collect();

        assert_eq!(
            union, naive_new,
            "same-op: union of variant matches != naive matches involving a new node"
        );
        // The scenario must actually exercise a match where BOTH atoms are new
        // (the case only variant 0 may claim) and one where only the outer is.
        assert!(
            union.len() >= 2,
            "expected ≥2 distinct new matches, got {union:?}"
        );
    }

    // -- #2c: 3-atom same-op — stacked FullMinusDelta cursors --
    //
    // Rule `(f (f (f x y) z) w)`: three nested f's, atoms 0/1/2 all op `f`.
    // Variant 2 puts atoms 0 AND 1 in FullMinusDelta and atom 2 in Delta —
    // two `Difference(full, delta)` cursors active in distinct joins of one
    // plan. Because all three atoms share the op, `variant_stats` collapses
    // `op_card[f]` to the delta size for EVERY atom (the scheduler can't tell
    // them apart by cost), so disjointness can only come from `atom_id` mode.
    #[test]
    fn variants_disjoint_three_atom_same_op() {
        use std::collections::HashSet;

        let mut eg = make_eg();
        let mut rr = crate::registry::RuleRegistry::<false>::new();
        let rule = mk_rule(
            "(f (f (f x y) z) w)",
            "(g w)",
            eg.ops(),
            eg.sorts(),
            &mut rr,
        );

        let of = eg.ops().id_by_name("f").unwrap();
        let oa = eg.ops().id_by_name("a").unwrap();
        let ob = eg.ops().id_by_name("b").unwrap();
        let oc = eg.ops().id_by_name("c").unwrap();

        // Baseline: f(f(f(a,b),c),a) entirely old.
        let a = eg.add(oa, &[]);
        let b = eg.add(ob, &[]);
        let c = eg.add(oc, &[]);
        let inner_old = eg.add(of, &[a, b]);
        let mid_old = eg.add(of, &[inner_old, c]);
        let _top_old = eg.add(of, &[mid_old, a]);
        eg.rebuild();
        eg.clear_touched();

        // One round: a new innermost f drives a fully-new tower, plus a new
        // top over the OLD middle (only-outer-new), exercising several
        // newness profiles across the three positions.
        let inner_new = eg.add(of, &[b, c]); // NEW deepest
        let mid_new = eg.add(of, &[inner_new, a]); // NEW middle over new inner
        let _top_new = eg.add(of, &[mid_new, b]); // all three new
        let _top_over_old = eg.add(of, &[mid_old, c]); // only outermost new
        eg.rebuild();

        let touched: Vec<crate::id::ENodeId> = eg.touched().to_vec();
        let tset: HashSet<usize> = touched.iter().map(|g| g.to_usize()).collect();
        let full = IndexStore::build(&eg);
        let delta = IndexStore::build_delta(&eg, &touched);
        let globals = crate::resolve::GlobalCtx::<SortId, crate::id::ENodeId>::new();

        let key = |m: &crate::ematch::Match<DefaultConfig>| -> Vec<usize> {
            (0..rule.query.shape.nodes.len())
                .map(|i| {
                    eg.class_repr(m.get(crate::ast::VarId::new(i as u16)))
                        .to_usize()
                })
                .collect::<Vec<_>>()
        };

        let jatoms = join_atom_indices(&rule.query);
        assert_eq!(jatoms.len(), 3, "rule must have three join atoms");
        let mut per_variant: Vec<HashSet<Vec<usize>>> = Vec::new();
        for &di in &jatoms {
            let stats = variant_stats(&rule.query, di, &full, &delta);
            let plan = crate::schedule::schedule_with_stats(&rule.query, &stats);
            let vindex = VariantIndex::variant(&full, &delta, di);
            let matches = crate::ematch::run_query(&plan, &eg, &vindex, &globals);
            per_variant.push(matches.iter().map(&key).collect());
        }

        for i in 0..per_variant.len() {
            for j in (i + 1)..per_variant.len() {
                let shared: Vec<_> = per_variant[i].intersection(&per_variant[j]).collect();
                assert!(shared.is_empty(), "variants {i},{j} both emit {shared:?}");
            }
        }

        let union: HashSet<Vec<usize>> = per_variant.iter().flatten().cloned().collect();
        let naive_plan =
            crate::schedule::schedule_with_stats(&rule.query, &IndexStats::from_index(&full));
        let naive_matches =
            crate::ematch::run_query(&naive_plan, &eg, &VariantIndex::naive(&full), &globals);
        let naive_new: HashSet<Vec<usize>> = naive_matches
            .iter()
            .filter(|m| {
                rule.query.atoms.iter().any(|atom| match atom_node(atom) {
                    Some(vid) => tset.contains(&m.get(vid).to_usize()),
                    None => false,
                })
            })
            .map(&key)
            .collect();

        assert_eq!(
            union, naive_new,
            "3-atom same-op: variant union != naive matches with a new node"
        );
        assert!(!union.is_empty(), "scenario produced no new matches");
    }

    // -- #2d: multi-round differential, deep same-op nesting --
    //
    // The randomized proptest's rule POOL is single-level f/g only, so deep
    // same-op nesting under multi-round delta propagation (where round K's
    // recanonicalizations feed round K+1's delta through stacked
    // FullMinusDelta atoms) is never differentially checked. This drives a
    // tower of nested f's with a commute + an associativity-style rewrite so
    // that merges — not just fresh nodes — populate the touched log.
    #[test]
    fn diff_deep_same_op_multiround() {
        diff_test(|| {
            let mut eg = make_eg();
            let mut rr = crate::registry::RuleRegistry::<false>::new();
            let of = eg.ops().id_by_name("f").unwrap();
            let oa = eg.ops().id_by_name("a").unwrap();
            let ob = eg.ops().id_by_name("b").unwrap();
            let oc = eg.ops().id_by_name("c").unwrap();
            // Left-nested tower f(f(f(a,b),c),a).
            let a = eg.add(oa, &[]);
            let b = eg.add(ob, &[]);
            let c = eg.add(oc, &[]);
            let i0 = eg.add(of, &[a, b]);
            let i1 = eg.add(of, &[i0, c]);
            let _i2 = eg.add(of, &[i1, a]);
            // commute drives recanonicalization; the re-association rule
            // rewrites the same op at two depths, repeatedly feeding delta.
            let r_comm = mk_rule("(f x y)", "(f y x)", eg.ops(), eg.sorts(), &mut rr);
            let r_assoc = mk_rule(
                "(f (f x y) z)",
                "(f x (f y z))",
                eg.ops(),
                eg.sorts(),
                &mut rr,
            );
            let n = eg.node_count();
            (eg, vec![r_comm, r_assoc], n)
        });
    }

    // -- #3: AC / ACI differential (variadic decompose paths) --
    // `(f x y) -> (add x y)` creates a fresh AC node in round 0; round 1's
    // delta then drives the AC subset rule, exercising DecomposeAC / by_contains
    // under semi-naive.
    #[test]
    fn diff_ac() {
        diff_test(|| {
            let mut eg = make_eg();
            let mut rr = crate::registry::RuleRegistry::<false>::new();
            let a = eg.add(eg.ops().id_by_name("a").unwrap(), &[]);
            let b = eg.add(eg.ops().id_by_name("b").unwrap(), &[]);
            let _fab = eg.add(eg.ops().id_by_name("f").unwrap(), &[a, b]);
            let r1 = mk_rule("(f x y)", "(add x y)", eg.ops(), eg.sorts(), &mut rr);
            let r2 = mk_rule("(add x y ..rest)", "(g x)", eg.ops(), eg.sorts(), &mut rr);
            let n = eg.node_count();
            (eg, vec![r1, r2], n)
        });
    }

    #[test]
    fn diff_aci() {
        diff_test(|| {
            let mut eg = make_eg();
            let mut rr = crate::registry::RuleRegistry::<false>::new();
            let a = eg.add(eg.ops().id_by_name("a").unwrap(), &[]);
            let b = eg.add(eg.ops().id_by_name("b").unwrap(), &[]);
            let _fab = eg.add(eg.ops().id_by_name("f").unwrap(), &[a, b]);
            let r1 = mk_rule("(f x y)", "(union x y)", eg.ops(), eg.sorts(), &mut rr);
            let r2 = mk_rule("(union x y ..rest)", "(g x)", eg.ops(), eg.sorts(), &mut rr);
            let n = eg.node_count();
            (eg, vec![r1, r2], n)
        });
    }

    // -- #2e: variadic atoms keep their delta mode when driven from a parent --
    //
    // Regression test for a disjointness defect found by bi-abduction: every
    // variant's per-atom mode is realized ONLY through `Step::Join.atom_id`
    // (see ematch::run_join — mode is read off the join step). The implicit
    // precondition is therefore: *every join atom emits a `Step::Join` in
    // every variant's plan.* For variadic atoms (A/AC/ACI) this used to be
    // VIOLATED — `emit_variadic_join` emitted NO `Step::Join` when the atom's
    // node var was already bound, so when a variant drove from an enclosing
    // atom (binding the variadic child via `ExtractChild`) the atom's
    // `FullMinusDelta` exclusion silently never ran. The fix mirrors the
    // fixed-arity `Plain` bound-node path: emit a `ByRepr ∩ ByOp` re-join
    // carrying `atom_id` so the mode is applied.
    //
    // Defect impact had been: redundant re-emission only (the union still
    // equalled the naive new-match set, and application is idempotent, so
    // final state was always correct — which is why diff_ac / diff_aci / the
    // whole .egg corpus stayed green). The fix recovers disjointness, i.e. the
    // lost semi-naive work savings on parent-driven variadic atoms.
    //
    // Asserts BOTH: pairwise-disjoint variant sets AND completeness against
    // naive, for `(f (add x ..r1) (add y ..r2))` (two `add` atoms sharing op).
    #[test]
    fn variadic_atoms_keep_delta_mode_when_parent_driven() {
        use std::collections::HashSet;

        let mut eg = make_eg();
        let mut rr = crate::registry::RuleRegistry::<false>::new();
        let rule = mk_rule(
            "(f (add x ..r1) (add y ..r2))",
            "(g x)",
            eg.ops(),
            eg.sorts(),
            &mut rr,
        );

        let of = eg.ops().id_by_name("f").unwrap();
        let oadd = eg.ops().id_by_name("add").unwrap();
        let oa = eg.ops().id_by_name("a").unwrap();
        let ob = eg.ops().id_by_name("b").unwrap();
        let oc = eg.ops().id_by_name("c").unwrap();

        // Baseline (all old): f(add(a,b), add(b,c)).
        let a = eg.add(oa, &[]);
        let b = eg.add(ob, &[]);
        let c = eg.add(oc, &[]);
        let add_ab = eg.add(oadd, &[a, b]);
        let add_bc = eg.add(oadd, &[b, c]);
        let _f_old = eg.add(of, &[add_ab, add_bc]);
        eg.rebuild();
        eg.clear_touched();

        // One round of fresh nodes: a new add and new f's over old/new adds.
        let add_mset = eg.add(oadd, &[a, c]); // NEW add
        let _f_both_new = eg.add(of, &[add_mset, add_mset]); // both add atoms bind the new add
        let _f_mixed = eg.add(of, &[add_ab, add_mset]); // old add, new add
        eg.rebuild();

        let touched: Vec<crate::id::ENodeId> = eg.touched().to_vec();
        let tset: HashSet<usize> = touched.iter().map(|g| g.to_usize()).collect();
        let full = IndexStore::build(&eg);
        let delta = IndexStore::build_delta(&eg, &touched);
        let globals = crate::resolve::GlobalCtx::<SortId, crate::id::ENodeId>::new();

        let jatoms = join_atom_indices(&rule.query);
        let add_atoms: Vec<_> = jatoms
            .iter()
            .copied()
            .filter(|&i| atom_op(&rule.query.atoms[i]) == Some(oadd))
            .collect();
        assert_eq!(add_atoms.len(), 2, "expected two add atoms sharing the op");

        // Key by the tuple of NODE IDS each join atom binds — exactly the
        // node-tuple the design's leftmost-new-atom partition is defined over.
        let key = |m: &crate::ematch::Match<DefaultConfig>| -> Vec<usize> {
            jatoms
                .iter()
                .map(|&ai| {
                    let vid = atom_node(&rule.query.atoms[ai]).unwrap();
                    m.get(vid).to_usize()
                })
                .collect::<Vec<_>>()
        };

        let mut per_variant: Vec<HashSet<Vec<usize>>> = Vec::new();
        for &di in &jatoms {
            let stats = variant_stats(&rule.query, di, &full, &delta);
            let plan = crate::schedule::schedule_with_stats(&rule.query, &stats);
            let vindex = VariantIndex::variant(&full, &delta, di);
            let matches = crate::ematch::run_query(&plan, &eg, &vindex, &globals);
            per_variant.push(matches.iter().map(&key).collect());
        }

        // Disjointness: with the parent-driven variadic re-join in place, the
        // FullMinusDelta mode is applied, so no node-tuple is emitted twice.
        for i in 0..per_variant.len() {
            for j in (i + 1)..per_variant.len() {
                let shared: Vec<_> = per_variant[i].intersection(&per_variant[j]).collect();
                assert!(
                    shared.is_empty(),
                    "variadic same-op variants {i},{j} both emit {shared:?} — \
                     the parent-driven re-join in emit_variadic_join regressed"
                );
            }
        }

        // Completeness: the union still covers exactly the naive new-match set,
        // so the disjointness fix dropped nothing.
        let union: HashSet<Vec<usize>> = per_variant.iter().flatten().cloned().collect();
        let naive_plan =
            crate::schedule::schedule_with_stats(&rule.query, &IndexStats::from_index(&full));
        let naive_matches =
            crate::ematch::run_query(&naive_plan, &eg, &VariantIndex::naive(&full), &globals);
        let naive_new: HashSet<Vec<usize>> = naive_matches
            .iter()
            .filter(|m| {
                rule.query.atoms.iter().any(|atom| match atom_node(atom) {
                    Some(vid) => tset.contains(&m.get(vid).to_usize()),
                    None => false,
                })
            })
            .map(&key)
            .collect();
        assert_eq!(
            union, naive_new,
            "variadic same-op: variant union != naive matches with a new node"
        );
        assert!(!union.is_empty(), "AC scenario produced no new matches");
    }

    // -- #2e2: parent-driven variadic re-join when the class is NOT a singleton --
    //
    // The fix re-joins a bound variadic node via `ByRepr ∩ ByOp`. That is a
    // singleton in the common case, but if the node's class holds TWO distinct
    // same-op variadic nodes (e.g. two `add`s merged into one class), the
    // re-join's leapfrog iterates BOTH — each then feeds DecomposeAC
    // separately. Bi-abduction target: the re-join must re-bind to *each*
    // congruent node, not silently collapse to the representative, or matches
    // that decompose differently per node would be lost. End-to-end
    // differential under saturation is the oracle.
    #[test]
    fn diff_variadic_parent_driven_nonsingleton_class() {
        diff_test(|| {
            let mut eg = make_eg();
            let mut rr = crate::registry::RuleRegistry::<false>::new();
            let oadd = eg.ops().id_by_name("add").unwrap();
            let of = eg.ops().id_by_name("f").unwrap();
            let oa = eg.ops().id_by_name("a").unwrap();
            let ob = eg.ops().id_by_name("b").unwrap();
            let oc = eg.ops().id_by_name("c").unwrap();
            let a = eg.add(oa, &[]);
            let b = eg.add(ob, &[]);
            let c = eg.add(oc, &[]);
            // Two DISTINCT add nodes, then merge them into one class so the
            // class carries two same-op variadic members.
            let add_ab = eg.add(oadd, &[a, b]);
            let add_bc = eg.add(oadd, &[b, c]);
            eg.merge(add_ab, add_bc);
            // An f over that class drives the parent-driven variadic re-join.
            let _f = eg.add(of, &[add_ab, c]);
            // Rule with a parent-driven AC atom (subset → project a member).
            let r1 = mk_rule("(f (add x ..r) z)", "(g x)", eg.ops(), eg.sorts(), &mut rr);
            let r2 = mk_rule("(g x)", "(f (add x x) x)", eg.ops(), eg.sorts(), &mut rr);
            let n = eg.node_count();
            (eg, vec![r1, r2], n)
        });
    }

    // -- #2f: congruent duplicates via merge — key-faithfulness --
    //
    // Bi-abduction: the disjointness oracle keys matches by CLASS-REPS. That
    // is a faithful proxy for the design's node-tuple partition only if the
    // surviving nodes in each `by_op` bucket have distinct class-rep keys.
    // Congruent duplicates (two nodes, same op + same child-reprs, in the
    // same class) arise from MERGES, not `add` (which hash-conses). None of
    // the other disjointness tests merge to create that situation. Here a
    // merge makes f(a,c) and f(b,c) congruent; the round's delta must still
    // partition the survivors' matches disjointly and completely.
    #[test]
    fn variants_disjoint_with_congruent_dups() {
        use std::collections::HashSet;

        let mut eg = make_eg();
        let mut rr = crate::registry::RuleRegistry::<false>::new();
        // single-atom rule keeps the focus on bucket contents, not nesting
        let rule = mk_rule("(f x y)", "(g x)", eg.ops(), eg.sorts(), &mut rr);

        let of = eg.ops().id_by_name("f").unwrap();
        let og = eg.ops().id_by_name("g").unwrap();
        let oa = eg.ops().id_by_name("a").unwrap();
        let ob = eg.ops().id_by_name("b").unwrap();
        let oc = eg.ops().id_by_name("c").unwrap();

        // Baseline: a, b, c, f(a,c), f(b,c), g(a). All old.
        let a = eg.add(oa, &[]);
        let b = eg.add(ob, &[]);
        let c = eg.add(oc, &[]);
        let _fac = eg.add(of, &[a, c]);
        let _fbc = eg.add(of, &[b, c]);
        let _ga = eg.add(og, &[a]);
        eg.rebuild();
        eg.clear_touched();

        // Round: merge a~b. Now f(a,c) and f(b,c) become congruent — both
        // survive in by_op[f] until congruence closure merges them, and the
        // recanonicalized one lands in `touched`. Add a genuinely fresh node.
        eg.merge(a, b);
        let _fcc = eg.add(of, &[c, c]); // fresh
        eg.rebuild();

        let touched: Vec<crate::id::ENodeId> = eg.touched().to_vec();
        let tset: HashSet<usize> = touched.iter().map(|g| g.to_usize()).collect();
        let full = IndexStore::build(&eg);
        let delta = IndexStore::build_delta(&eg, &touched);
        let globals = crate::resolve::GlobalCtx::<SortId, crate::id::ENodeId>::new();

        // Key by the actual surviving NODE id (not class-rep) so congruent
        // duplicates, if any survive distinctly, are counted separately and a
        // double-emission would be caught.
        let key = |m: &crate::ematch::Match<DefaultConfig>| -> Vec<usize> {
            (0..rule.query.shape.nodes.len())
                .map(|i| m.get(crate::ast::VarId::new(i as u16)).to_usize())
                .collect::<Vec<_>>()
        };

        let jatoms = join_atom_indices(&rule.query);
        let mut per_variant: Vec<HashSet<Vec<usize>>> = Vec::new();
        for &di in &jatoms {
            let stats = variant_stats(&rule.query, di, &full, &delta);
            let plan = crate::schedule::schedule_with_stats(&rule.query, &stats);
            let vindex = VariantIndex::variant(&full, &delta, di);
            let matches = crate::ematch::run_query(&plan, &eg, &vindex, &globals);
            per_variant.push(matches.iter().map(&key).collect());
        }

        for i in 0..per_variant.len() {
            for j in (i + 1)..per_variant.len() {
                let shared: Vec<_> = per_variant[i].intersection(&per_variant[j]).collect();
                assert!(
                    shared.is_empty(),
                    "variants {i},{j} both emit node-tuple {shared:?}"
                );
            }
        }

        // Completeness against naive, keyed identically by node id.
        let union: HashSet<Vec<usize>> = per_variant.iter().flatten().cloned().collect();
        let naive_plan =
            crate::schedule::schedule_with_stats(&rule.query, &IndexStats::from_index(&full));
        let naive_matches =
            crate::ematch::run_query(&naive_plan, &eg, &VariantIndex::naive(&full), &globals);
        let naive_new: HashSet<Vec<usize>> = naive_matches
            .iter()
            .filter(|m| {
                rule.query.atoms.iter().any(|atom| match atom_node(atom) {
                    Some(vid) => tset.contains(&m.get(vid).to_usize()),
                    None => false,
                })
            })
            .map(&key)
            .collect();
        assert_eq!(
            union, naive_new,
            "congruent-dups: variant union (by node id) != naive new matches"
        );
    }

    // -- #2g: subsumption during a round stays sound (differential) --
    //
    // Bi-abduction: `build_delta` skips FLAG_SUBSUMED nodes (index.rs), but
    // `recanonize_node` pushes to `touched` BEFORE collision/subsumption is
    // resolved (caches.rs). So a node can be in `touched` yet absent from the
    // delta because it was subsumed. The claim that survives only if the
    // subsumed node's canonical form is also carried by a NON-subsumed node
    // that the delta still indexes (or the match is genuinely old). A merge
    // that makes two f-nodes congruent exercises exactly this — subsume the
    // loser and confirm semi-naive still matches naive.
    #[test]
    fn semi_subsume_during_round_sound() {
        let globals = crate::resolve::GlobalCtx::<SortId, crate::id::ENodeId>::new();
        let setup = || -> (EG, Vec<PreparedRule<OpId, SortId, NiraLitVal>>, usize) {
            let mut eg = make_eg();
            let mut rr = crate::registry::RuleRegistry::<false>::new();
            let of = eg.ops().id_by_name("f").unwrap();
            let oa = eg.ops().id_by_name("a").unwrap();
            let ob = eg.ops().id_by_name("b").unwrap();
            let oc = eg.ops().id_by_name("c").unwrap();
            let a = eg.add(oa, &[]);
            let b = eg.add(ob, &[]);
            let c = eg.add(oc, &[]);
            let fac = eg.add(of, &[a, c]);
            let fbc = eg.add(of, &[b, c]);
            // Merge a~b so f(a,c) and f(b,c) are congruent, then subsume one.
            eg.merge(a, b);
            eg.rebuild();
            eg.subsume(fac);
            // After subsumption fbc should still carry the f(_,c) form.
            let _ = fbc;
            let r1 = mk_rule("(f x y)", "(g x)", eg.ops(), eg.sorts(), &mut rr);
            let r2 = mk_rule("(g x)", "(f x x)", eg.ops(), eg.sorts(), &mut rr);
            let n = eg.node_count();
            (eg, vec![r1, r2], n)
        };

        let (mut a, rules_a, n) = setup();
        saturate::<DefaultConfig, _, _, _, false, false>(
            &rules_a, &mut a, &NiraModel, 50, &globals,
        );
        let (mut b, rules_b, n2) = setup();
        saturate_semi::<DefaultConfig, _, _, _, false, false>(
            &rules_b, &mut b, &NiraModel, 50, &globals,
        );
        assert_eq!(n, n2);
        assert_eq!(
            partition_over(&a, n),
            partition_over(&b, n),
            "subsumption-in-round: semi-naive diverged from naive"
        );
    }

    // -- #2i: A-sequence (concat) patterns under semi-naive --
    //
    // GAP: every variadic test so far uses AC/ACI (`add`/`union`). The A
    // (associative, ordered) path goes through `ExpandA`, a DIFFERENT decompose
    // routine than DecomposeAC/ACI — and the parent-driven-variadic re-join fix
    // in `emit_variadic_join` applies to A atoms too but was only ever
    // exercised on AC. Differential equivalence over a rule whose LHS nests a
    // `concat` inside an `f` drives `ExpandA` under the variant decomposition.
    #[test]
    fn diff_a_sequence_nested() {
        diff_test(|| {
            let mut eg = make_eg();
            let mut rr = crate::registry::RuleRegistry::<false>::new();
            let oconcat = eg.ops().id_by_name("concat").unwrap();
            let of = eg.ops().id_by_name("f").unwrap();
            let oa = eg.ops().id_by_name("a").unwrap();
            let ob = eg.ops().id_by_name("b").unwrap();
            let oc = eg.ops().id_by_name("c").unwrap();
            let a = eg.add(oa, &[]);
            let b = eg.add(ob, &[]);
            let c = eg.add(oc, &[]);
            let cat = eg.add(oconcat, &[a, b, c]);
            let _f = eg.add(of, &[cat, a]);
            // f over a sliding-window concat → project the middle element;
            // then a rule that rebuilds a concat to keep deltas flowing.
            let r1 = mk_rule(
                "(f (concat ..pre x ..suf) z)",
                "(g x)",
                eg.ops(),
                eg.sorts(),
                &mut rr,
            );
            let r2 = mk_rule("(g x)", "(concat x x)", eg.ops(), eg.sorts(), &mut rr);
            let n = eg.node_count();
            (eg, vec![r1, r2], n)
        });
    }

    // -- #2j: A-sequence top-level (ExpandA as the delta-driven atom) --
    // A bare `(concat ..pre x ..suf)` rule whose only join atom IS the A atom,
    // so in rounds ≥1 ExpandA runs delta-restricted (mode Delta on the A join).
    #[test]
    fn diff_a_sequence_toplevel() {
        diff_test(|| {
            let mut eg = make_eg();
            let mut rr = crate::registry::RuleRegistry::<false>::new();
            let oconcat = eg.ops().id_by_name("concat").unwrap();
            let oa = eg.ops().id_by_name("a").unwrap();
            let ob = eg.ops().id_by_name("b").unwrap();
            let a = eg.add(oa, &[]);
            let b = eg.add(ob, &[]);
            let _cat = eg.add(oconcat, &[a, b]);
            let r1 = mk_rule(
                "(concat x y)",
                "(concat y x)",
                eg.ops(),
                eg.sorts(),
                &mut rr,
            );
            let r2 = mk_rule(
                "(concat ..pre x ..suf)",
                "(g x)",
                eg.ops(),
                eg.sorts(),
                &mut rr,
            );
            let n = eg.node_count();
            (eg, vec![r1, r2], n)
        });
    }

    // -- #2k: sibling atoms sharing a variable (Eq-joined, not parent-child) --
    //
    // GAP: every disjointness/differential test chains atoms parent-to-child
    // (resolved by ExtractChild). `(f (g x) (g x))` instead gives two SIBLING
    // `g` atoms — both children of f — sharing `x`, joined by the nonlinear
    // `CheckEq`/`CopyBinding` path rather than ExtractChild. Under semi-naive
    // each `g` atom gets its own variant, and the cross-atom Eq join must
    // compose with the delta decomposition.
    #[test]
    fn diff_sibling_shared_var() {
        diff_test(|| {
            let mut eg = make_eg();
            let mut rr = crate::registry::RuleRegistry::<false>::new();
            let og = eg.ops().id_by_name("g").unwrap();
            let of = eg.ops().id_by_name("f").unwrap();
            let oa = eg.ops().id_by_name("a").unwrap();
            let ob = eg.ops().id_by_name("b").unwrap();
            let a = eg.add(oa, &[]);
            let b = eg.add(ob, &[]);
            let ga = eg.add(og, &[a]);
            let gb = eg.add(og, &[b]);
            let _f_same = eg.add(of, &[ga, ga]); // matches (f (g x) (g x))
            let _f_diff = eg.add(of, &[ga, gb]); // does not (x≠y)
            // RHS grows new g's so later rounds re-drive the shared-var g atoms.
            let r1 = mk_rule("(f (g x) (g x))", "(g x)", eg.ops(), eg.sorts(), &mut rr);
            let r2 = mk_rule("(f x y)", "(f y x)", eg.ops(), eg.sorts(), &mut rr);
            let n = eg.node_count();
            (eg, vec![r1, r2], n)
        });
    }

    // -- #2l: PROOFS=true under semi-naive --
    //
    // GAP: the design's "Not To Be Confused With has_history" section warns the
    // touched-log push co-locates with the proof-history save in
    // `recanonize_node` but must fire on DIFFERENT conditions (every round vs.
    // once ever). `semi_restore_safety` uses TRACK=true but PROOFS=false, so
    // that co-location is never exercised. Here PROOFS=true: semi-naive must
    // still reach the same partition as naive while the history save runs.
    #[test]
    fn semi_with_proofs_matches_naive() {
        type ProofEg = EGraph<DefaultConfig, NiraLitVal, false, true>;
        let globals = crate::resolve::GlobalCtx::<SortId, crate::id::ENodeId>::new();

        let build = || -> (ProofEg, Vec<PreparedRule<OpId, SortId, NiraLitVal>>, usize) {
            let mut eg = ProofEg::from_model(&NiraModel);
            let e = eg.intern_sort("IExpr");
            eg.register_op2("f", e, e, e);
            eg.register_op1("g", e, e);
            eg.register_op0("a", e);
            eg.register_op0("b", e);
            eg.register_op0("c", e);
            eg.register_mset("add", e, e);
            let mut rr = crate::registry::RuleRegistry::<false>::new();
            let a = eg.add(eg.ops().id_by_name("a").unwrap(), &[]);
            let b = eg.add(eg.ops().id_by_name("b").unwrap(), &[]);
            let c = eg.add(eg.ops().id_by_name("c").unwrap(), &[]);
            let _fab = eg.add(eg.ops().id_by_name("f").unwrap(), &[a, b]);
            let _fbc = eg.add(eg.ops().id_by_name("f").unwrap(), &[b, c]);
            // commute + project + AC growth — multiple rounds of recanon so the
            // history-save path (once per node) and touched-push (per round)
            // both fire and must stay independent.
            let r1 = mk_rule("(f x y)", "(f y x)", eg.ops(), eg.sorts(), &mut rr);
            let r2 = mk_rule("(f x y)", "(add x y)", eg.ops(), eg.sorts(), &mut rr);
            let r3 = mk_rule("(add x y ..rest)", "(g x)", eg.ops(), eg.sorts(), &mut rr);
            let n = eg.node_count();
            (eg, vec![r1, r2, r3], n)
        };

        let (mut a, rules_a, n) = build();
        let ra = saturate::<DefaultConfig, _, _, _, false, true>(
            &rules_a, &mut a, &NiraModel, 50, &globals,
        );
        let (mut b, rules_b, n2) = build();
        let rb = saturate_semi::<DefaultConfig, _, _, _, false, true>(
            &rules_b, &mut b, &NiraModel, 50, &globals,
        );
        assert_eq!(n, n2);
        assert_eq!(
            ra.saturated, rb.saturated,
            "PROOFS: saturation flag mismatch"
        );
        assert_eq!(
            partition_over(&a, n),
            partition_over(&b, n),
            "PROOFS=true: semi-naive diverged from naive"
        );
    }

    // -- #2h: nested-variadic differential under saturation --
    //
    // Guards the soundness claim for the variadic-mode defect above: even
    // though variant sets overlap on the variadic path, the FINAL state must
    // still match naive across multiple rounds (idempotent application makes
    // the extra emissions harmless). Rule nests an AC atom inside an f, so the
    // defect path (drive-from-parent, variadic child via ExtractChild) fires
    // every round, and the const-fold-style AC rule keeps producing deltas.
    #[test]
    fn diff_nested_variadic_saturation() {
        diff_test(|| {
            let mut eg = make_eg();
            let mut rr = crate::registry::RuleRegistry::<false>::new();
            let a = eg.add(eg.ops().id_by_name("a").unwrap(), &[]);
            let b = eg.add(eg.ops().id_by_name("b").unwrap(), &[]);
            let c = eg.add(eg.ops().id_by_name("c").unwrap(), &[]);
            let add_ab = eg.add(eg.ops().id_by_name("add").unwrap(), &[a, b]);
            let _f = eg.add(eg.ops().id_by_name("f").unwrap(), &[add_ab, c]);
            // f over an add subset → project; add subset grows g's; g feeds f.
            let r1 = mk_rule("(f (add x ..r) z)", "(g x)", eg.ops(), eg.sorts(), &mut rr);
            let r2 = mk_rule(
                "(add x y ..rest)",
                "(f (add x y) x)",
                eg.ops(),
                eg.sorts(),
                &mut rr,
            );
            let r3 = mk_rule("(g x)", "(add x x)", eg.ops(), eg.sorts(), &mut rr);
            let n = eg.node_count();
            (eg, vec![r1, r2, r3], n)
        });
    }

    // -- #4: restore-safety (touched cleared on restore; correct afterward) --
    #[test]
    fn semi_restore_safety() {
        type TrackedEg = EGraph<DefaultConfig, NiraLitVal, true, false>;
        let globals = crate::resolve::GlobalCtx::<SortId, crate::id::ENodeId>::new();

        let build = || -> (TrackedEg, Vec<PreparedRule<OpId, SortId, NiraLitVal>>, usize) {
            let mut eg = TrackedEg::from_model(&NiraModel);
            let e = eg.intern_sort("IExpr");
            eg.register_op2("f", e, e, e);
            eg.register_op1("g", e, e);
            eg.register_op0("a", e);
            eg.register_op0("b", e);
            let mut rr = crate::registry::RuleRegistry::<true>::new();
            let a = eg.add(eg.ops().id_by_name("a").unwrap(), &[]);
            let b = eg.add(eg.ops().id_by_name("b").unwrap(), &[]);
            let _fab = eg.add(eg.ops().id_by_name("f").unwrap(), &[a, b]);
            let r1 = mk_rule("(f x y)", "(f y x)", eg.ops(), eg.sorts(), &mut rr);
            let r2 = mk_rule("(f x y)", "(g x)", eg.ops(), eg.sorts(), &mut rr);
            let n = eg.node_count();
            (eg, vec![r1, r2], n)
        };

        let (mut eg, rules, n) = build();
        let tok = eg.mark(crate::containers::ShrinkPolicy::Never);
        let _ = saturate_semi::<DefaultConfig, _, _, _, true, false>(
            &rules, &mut eg, &NiraModel, 50, &globals,
        );
        eg.restore(tok);
        assert!(
            eg.touched().is_empty(),
            "restore must clear the touched log (no stale delta)"
        );

        // Semi-naive after a restore reaches the same fixpoint as a fresh
        // naive run from the same input.
        let rs = saturate_semi::<DefaultConfig, _, _, _, true, false>(
            &rules, &mut eg, &NiraModel, 50, &globals,
        );
        assert!(rs.saturated);

        let (mut egn, rules_n, n2) = build();
        let _ = saturate::<DefaultConfig, _, _, _, true, false>(
            &rules_n, &mut egn, &NiraModel, 50, &globals,
        );
        assert_eq!(n, n2);
        assert_eq!(
            partition_over(&eg, n),
            partition_over(&egn, n),
            "post-restore semi-naive diverged from naive"
        );
    }

    // -- #5: empty delta / fixpoint is a stable no-op --
    #[test]
    fn semi_fixpoint_stable() {
        let globals = crate::resolve::GlobalCtx::<SortId, crate::id::ENodeId>::new();
        let setup = || {
            let mut eg = make_eg();
            let mut rr = crate::registry::RuleRegistry::<false>::new();
            let a = eg.add(eg.ops().id_by_name("a").unwrap(), &[]);
            let b = eg.add(eg.ops().id_by_name("b").unwrap(), &[]);
            let _fab = eg.add(eg.ops().id_by_name("f").unwrap(), &[a, b]);
            let r = mk_rule("(f x y)", "(f y x)", eg.ops(), eg.sorts(), &mut rr);
            (eg, vec![r])
        };

        let (mut eg, rules) = setup();
        let r1 = saturate_semi::<DefaultConfig, _, _, _, false, false>(
            &rules, &mut eg, &NiraModel, 50, &globals,
        );
        assert!(
            r1.saturated,
            "should reach a fixpoint (final round empty-delta)"
        );

        // Re-running on the saturated graph must be a 1-round no-op: round 0
        // re-finds the matches, every application is idempotent → 0 changes.
        let r2 = saturate_semi::<DefaultConfig, _, _, _, false, false>(
            &rules, &mut eg, &NiraModel, 50, &globals,
        );
        assert!(r2.saturated);
        assert_eq!(
            r2.iterations, 1,
            "re-saturating a fixpoint must terminate in one no-op round"
        );
    }

    #[test]
    fn semi_no_match_fixpoint_in_one() {
        // A rule that cannot match → semi-naive saturates immediately.
        let globals = crate::resolve::GlobalCtx::<SortId, crate::id::ENodeId>::new();
        let mut eg = make_eg();
        let mut rr = crate::registry::RuleRegistry::<false>::new();
        eg.add(eg.ops().id_by_name("a").unwrap(), &[]); // only an `a`, no `f`
        let r = mk_rule("(f x y)", "(g x)", eg.ops(), eg.sorts(), &mut rr);
        let res = saturate_semi::<DefaultConfig, _, _, _, false, false>(
            &[r],
            &mut eg,
            &NiraModel,
            10,
            &globals,
        );
        assert!(res.saturated);
        assert_eq!(res.iterations, 1);
    }

    #[test]
    fn saturate_commute() {
        let mut eg = make_eg();
        let mut rules = crate::registry::RuleRegistry::<false>::new();
        let a = eg.add(eg.ops().id_by_name("a").unwrap(), &[]);
        let b = eg.add(eg.ops().id_by_name("b").unwrap(), &[]);
        let fab = eg.add(eg.ops().id_by_name("f").unwrap(), &[a, b]);

        let rule = mk_rule("(f x y)", "(f y x)", eg.ops(), eg.sorts(), &mut rules);
        let res = saturate::<DefaultConfig, _, _, _, false, false>(
            &[rule],
            &mut eg,
            &NiraModel,
            10,
            &crate::resolve::GlobalCtx::<crate::id::SortId, crate::id::ENodeId>::new(),
        );

        assert!(res.saturated);
        let fba = eg.add(eg.ops().id_by_name("f").unwrap(), &[b, a]);
        assert_eq!(eg.find(fab), eg.find(fba));
    }

    #[test]
    fn saturate_fixpoint_in_one() {
        // No matching terms → saturates immediately
        let mut eg = make_eg();
        let mut rules = crate::registry::RuleRegistry::<false>::new();
        eg.add(eg.ops().id_by_name("a").unwrap(), &[]);

        let rule = mk_rule("(f x y)", "(f y x)", eg.ops(), eg.sorts(), &mut rules);
        let res = saturate::<DefaultConfig, _, _, _, false, false>(
            &[rule],
            &mut eg,
            &NiraModel,
            10,
            &crate::resolve::GlobalCtx::<crate::id::SortId, crate::id::ENodeId>::new(),
        );

        assert!(res.saturated);
        assert_eq!(res.iterations, 1);
    }

    #[test]
    fn saturate_constant_fold() {
        use num_bigint::BigInt;

        let mut eg = make_eg();
        let mut rules = crate::registry::RuleRegistry::<false>::new();
        let model = NiraModel;

        let at_ibig = eg.ops().id_by_name("@IBig").unwrap();
        let ilit = eg.ops().id_by_name("ILit").unwrap();
        let iadd = eg.ops().id_by_name("IAdd").unwrap();

        // Build (IAdd (ILit 3) (ILit 5))
        let v3 = eg.intern_lit(NiraLitVal::Int(BigInt::from(3)));
        let n3 = eg.add_lit(at_ibig, v3);
        let lit3 = eg.add(ilit, &[n3]);
        let v5 = eg.intern_lit(NiraLitVal::Int(BigInt::from(5)));
        let n5 = eg.add_lit(at_ibig, v5);
        let lit5 = eg.add(ilit, &[n5]);
        let add_node = eg.add(iadd, &[lit3, lit5]);

        let rule = mk_rule(
            "(IAdd (ILit x) (ILit y))",
            "(ILit (+ x y))",
            eg.ops(),
            eg.sorts(),
            &mut rules,
        );
        let res = saturate::<DefaultConfig, _, _, _, false, false>(
            &[rule],
            &mut eg,
            &model,
            10,
            &crate::resolve::GlobalCtx::<crate::id::SortId, crate::id::ENodeId>::new(),
        );

        assert!(res.saturated);

        // (ILit 8) should be merged with (IAdd (ILit 3) (ILit 5))
        let v8 = eg.intern_lit(NiraLitVal::Int(BigInt::from(8)));
        let n8 = eg.add_lit(at_ibig, v8);
        let lit8 = eg.add(ilit, &[n8]);
        assert_eq!(eg.find(add_node), eg.find(lit8));
    }

    #[test]
    fn saturate_multi_rule_chain() {
        // f(a, b) with commute + distribute: f(x,y)→f(y,x), f(x,y)→g(x)
        let mut eg = make_eg();
        let mut rules = crate::registry::RuleRegistry::<false>::new();
        let a = eg.add(eg.ops().id_by_name("a").unwrap(), &[]);
        let b = eg.add(eg.ops().id_by_name("b").unwrap(), &[]);
        let fab = eg.add(eg.ops().id_by_name("f").unwrap(), &[a, b]);

        let r1 = mk_rule("(f x y)", "(f y x)", eg.ops(), eg.sorts(), &mut rules);
        let r2 = mk_rule("(f x y)", "(g x)", eg.ops(), eg.sorts(), &mut rules);
        let res = saturate::<DefaultConfig, _, _, _, false, false>(
            &[r1, r2],
            &mut eg,
            &NiraModel,
            10,
            &crate::resolve::GlobalCtx::<crate::id::SortId, crate::id::ENodeId>::new(),
        );

        assert!(res.saturated);
        // g(a) and g(b) should both be merged with f(a,b)
        let ga = eg.add(eg.ops().id_by_name("g").unwrap(), &[a]);
        let gb = eg.add(eg.ops().id_by_name("g").unwrap(), &[b]);
        assert_eq!(eg.find(fab), eg.find(ga));
        assert_eq!(eg.find(fab), eg.find(gb));
    }

    #[test]
    fn two_level_constant_fold() {
        // (IMul (ILit 3) (IAdd (ILit 4) (ILit 5)))
        // Step 1: IAdd folds → (ILit 9)
        // Step 2: after rebuild, IMul should see (ILit 3) and (ILit 9) → (ILit 27)
        use num_bigint::BigInt;

        let mut eg = make_eg();
        let mut rules = crate::registry::RuleRegistry::<false>::new();
        let model = NiraModel;

        let at_ibig = eg.ops().id_by_name("@IBig").unwrap();
        let ilit = eg.ops().id_by_name("ILit").unwrap();
        let iadd = eg.ops().id_by_name("IAdd").unwrap();
        let imul = eg.ops().id_by_name("IMul").unwrap();

        let v3 = eg.intern_lit(NiraLitVal::Int(BigInt::from(3)));
        let n3 = eg.add_lit(at_ibig, v3);
        let lit3 = eg.add(ilit, &[n3]);

        let v4 = eg.intern_lit(NiraLitVal::Int(BigInt::from(4)));
        let n4 = eg.add_lit(at_ibig, v4);
        let lit4 = eg.add(ilit, &[n4]);

        let v5 = eg.intern_lit(NiraLitVal::Int(BigInt::from(5)));
        let n5 = eg.add_lit(at_ibig, v5);
        let lit5 = eg.add(ilit, &[n5]);

        let add_node = eg.add(iadd, &[lit4, lit5]);
        let mul_node = eg.add(imul, &[lit3, add_node]);

        let add_rule = mk_rule(
            "(IAdd (ILit x) (ILit y))",
            "(ILit (+ x y))",
            eg.ops(),
            eg.sorts(),
            &mut rules,
        );
        let mul_rule = mk_rule(
            "(IMul (ILit x) (ILit y))",
            "(ILit (* x y))",
            eg.ops(),
            eg.sorts(),
            &mut rules,
        );

        let globals = crate::resolve::GlobalCtx::<crate::id::SortId, crate::id::ENodeId>::new();
        let res = saturate::<DefaultConfig, _, _, _, false, false>(
            &[add_rule, mul_rule],
            &mut eg,
            &model,
            10,
            &globals,
        );
        assert!(res.saturated);

        let v9 = eg.intern_lit(NiraLitVal::Int(BigInt::from(9)));
        let n9 = eg.add_lit(at_ibig, v9);
        let lit9 = eg.add(ilit, &[n9]);
        assert_eq!(
            eg.find(add_node),
            eg.find(lit9),
            "Add should fold to (ILit 9)"
        );

        let v27 = eg.intern_lit(NiraLitVal::Int(BigInt::from(27)));
        let n27 = eg.add_lit(at_ibig, v27);
        let lit27 = eg.add(ilit, &[n27]);
        assert_eq!(
            eg.find(mul_node),
            eg.find(lit27),
            "Mul should fold to (ILit 27)"
        );
    }

    /// Not a real test — run with `cargo test saturate_demo -- --nocapture --ignored` to visualize.
    #[test]
    #[ignore]
    fn saturate_demo() {
        use num_bigint::BigInt;

        let mut eg = make_eg();
        let mut rule_reg = crate::registry::RuleRegistry::<false>::new();
        let model = NiraModel;

        let at_ibig = eg.ops().id_by_name("@IBig").unwrap();
        let ilit = eg.ops().id_by_name("ILit").unwrap();
        let iadd = eg.ops().id_by_name("IAdd").unwrap();
        let f = eg.ops().id_by_name("f").unwrap();
        let g = eg.ops().id_by_name("g").unwrap();
        let a = eg.add(eg.ops().id_by_name("a").unwrap(), &[]);
        let b = eg.add(eg.ops().id_by_name("b").unwrap(), &[]);
        let c = eg.add(eg.ops().id_by_name("c").unwrap(), &[]);

        // f(a, b), f(b, c), g(f(a, b))
        let fab = eg.add(f, &[a, b]);
        let _fbc = eg.add(f, &[b, c]);
        let _gfab = eg.add(g, &[fab]);

        // IAdd(ILit(2), ILit(3))
        let v2 = eg.intern_lit(NiraLitVal::Int(BigInt::from(2)));
        let n2 = eg.add_lit(at_ibig, v2);
        let lit2 = eg.add(ilit, &[n2]);
        let v3 = eg.intern_lit(NiraLitVal::Int(BigInt::from(3)));
        let n3 = eg.add_lit(at_ibig, v3);
        let lit3 = eg.add(ilit, &[n3]);
        let add23 = eg.add(iadd, &[lit2, lit3]);

        eg.show("before_saturation");

        let rules: Vec<(&str, PreparedRule<OpId, SortId, NiraLitVal>)> = vec![
            (
                "commute",
                mk_rule("(f x y)", "(f y x)", eg.ops(), eg.sorts(), &mut rule_reg),
            ),
            (
                "extract",
                mk_rule("(f x y)", "(g x)", eg.ops(), eg.sorts(), &mut rule_reg),
            ),
            (
                "const-fold",
                mk_rule(
                    "(IAdd (ILit x) (ILit y))",
                    "(ILit (+ x y))",
                    eg.ops(),
                    eg.sorts(),
                    &mut rule_reg,
                ),
            ),
        ];

        let res = saturate_trace::<DefaultConfig, _, _, _, false, false>(
            &rules,
            &mut eg,
            &model,
            20,
            &crate::resolve::GlobalCtx::<crate::id::SortId, crate::id::ENodeId>::new(),
        );

        eg.rebuild();
        eg.show("after_saturation");

        eprintln!(
            "Saturated: {}, iterations: {}",
            res.saturated, res.iterations
        );
        eprintln!("E-nodes:  {}", eg.node_count());

        // Verify some expected equalities
        assert!(res.saturated);
        let fba = eg.add(f, &[b, a]);
        assert_eq!(eg.find(fab), eg.find(fba), "f(a,b) = f(b,a)");
        let ga = eg.add(g, &[a]);
        assert_eq!(eg.find(fab), eg.find(ga), "f(a,b) = g(a)");
        let v5 = eg.intern_lit(NiraLitVal::Int(BigInt::from(5)));
        let n5 = eg.add_lit(at_ibig, v5);
        let lit5 = eg.add(ilit, &[n5]);
        assert_eq!(
            eg.find(add23),
            eg.find(lit5),
            "IAdd(ILit(2), ILit(3)) = ILit(5)"
        );
    }
}
