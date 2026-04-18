// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Equality saturation driver loop.

use crate::EGraphConfig;
use crate::apply::{PreparedRule, apply_rule};
use crate::canon::{ACCanon, VarCanon};
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
    ACCanon: VarCanon<Cfg::G, Cfg::C>,
{
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
            };
        }
    }
    SatResult {
        iterations: limit,
        saturated: false,
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
    ACCanon: VarCanon<Cfg::G, Cfg::C>,
{
    use crate::ematch::run_query;

    let mut total_iter = 0;
    for i in 0..limit {
        total_iter = i + 1;
        eg.rebuild();
        let index = IndexStore::build(eg);
        let stats = crate::schedule::IndexStats::from_index(&index);
        let mut changes = 0;
        for (label, rule) in rules {
            let plan = crate::schedule::schedule_with_stats(&rule.query, &stats);
            let shape = &plan.shape;
            let mut matches = run_query(&plan, eg, &index, globals);
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
            };
        }
        eprintln!("-- iteration {total_iter}: {changes} changes --");
    }
    SatResult {
        iterations: total_iter,
        saturated: false,
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
        eg.register_ac("add", e, e);
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
