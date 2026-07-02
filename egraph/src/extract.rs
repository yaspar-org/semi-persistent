// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Optimal term extraction: pull the lowest-cost term from an e-class.

use std::collections::HashMap;

use crate::ast::Span;
use crate::ast::Term;
use crate::canon::{MSetCanon, VarCanon};
use crate::config::EGraphConfig;
use crate::containers::DenseId;
use crate::egraph::EGraph;
use crate::literal::LitVal;

/// Extract the cheapest term from the e-class containing `root`.
/// Cost = AST size (each node costs 1).
pub fn extract_best<Cfg, L, const T: bool, const P: bool>(
    eg: &EGraph<Cfg, L, T, P>,
    root: Cfg::G,
) -> Option<Term>
where
    Cfg: EGraphConfig,
    L: LitVal,
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
{
    let n = eg.len();
    let mut best_cost: HashMap<Cfg::G, usize> = HashMap::new();
    let mut best_node: HashMap<Cfg::G, Cfg::G> = HashMap::new();

    loop {
        let mut changed = false;
        for i in 0..n {
            let id = Cfg::G::from_usize(i);
            let repr = eg.find_const(id);

            let mut total: usize = 1;
            let mut ok = true;
            eg.for_each_child(id, |child, mult| {
                if !ok {
                    return;
                }
                match best_cost.get(&eg.find_const(child)) {
                    Some(&c) => total = total.saturating_add(c * mult as usize),
                    None => ok = false,
                }
            });
            if !ok {
                continue;
            }

            if total < best_cost.get(&repr).copied().unwrap_or(usize::MAX) {
                best_cost.insert(repr, total);
                best_node.insert(repr, id);
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }

    let root_repr = eg.find_const(root);
    best_node
        .get(&root_repr)
        .map(|_| reconstruct(eg, &best_node, root_repr))
}

fn reconstruct<Cfg, L, const T: bool, const P: bool>(
    eg: &EGraph<Cfg, L, T, P>,
    best_node: &HashMap<Cfg::G, Cfg::G>,
    repr: Cfg::G,
) -> Term
where
    Cfg: EGraphConfig,
    L: LitVal,
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
{
    let id = best_node[&repr];
    let name = eg.node_op_name(id).to_string();

    if let Some(val) = eg.get_lit_val(id) {
        return Term::Lit(val.to_string(), Span::Dummy);
    }

    let mut children = Vec::new();
    eg.for_each_child(id, |child, mult| {
        let t = reconstruct(eg, best_node, eg.find_const(child));
        for _ in 0..mult {
            children.push(t.clone());
        }
    });

    Term::App {
        op: name,
        children,
        span: Span::Dummy,
    }
}
