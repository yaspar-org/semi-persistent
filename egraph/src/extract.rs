// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Optimal term extraction: pull the lowest-cost term from an e-class.

use crate::ast::Span;
use crate::ast::Term;
use crate::canon::{MSetCanon, VarCanon};
use crate::config::EGraphConfig;
use crate::containers::DenseId;
use crate::egraph::EGraph;
use crate::literal::LitVal;
use crate::multiplicity::MultiplicityLike;

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
    // Both tables are indexed by class id rather than hashed. Ids here are
    // dense by construction — the scan below is over `eg.node_ids()` and
    // every representative is one of those ids — so a hash map's key storage,
    // hashing and probing all buy nothing over a direct index.
    //
    // `UNSET` doubles as the "no entry yet" marker for *both* tables: they are
    // only ever written together, and a saturated cost of `UNSET` is never
    // recorded (it cannot be `<` the incumbent, `UNSET` included), so
    // `best_cost[i] != UNSET` holds exactly when class `i` has a best node.
    // That is the same condition the previous map-based code expressed as
    // `get(..).unwrap_or(usize::MAX)`.
    const UNSET: usize = usize::MAX;
    let mut best_cost: Vec<usize> = vec![UNSET; n];
    let mut best_node: Vec<Cfg::G> = vec![Cfg::G::default(); n];

    loop {
        let mut changed = false;
        for id in eg.node_ids() {
            let repr = eg.find_const(id);

            let mut total: usize = 1;
            let mut ok = true;
            eg.for_each_child(id, |child, mult| {
                if !ok {
                    return;
                }
                let c = best_cost[eg.find_const(child).to_usize()];
                if c == UNSET {
                    ok = false;
                } else {
                    total = total.saturating_add(c.saturating_mul(mult.to_usize()));
                }
            });
            if !ok {
                continue;
            }

            let slot = repr.to_usize();
            if total < best_cost[slot] {
                best_cost[slot] = total;
                best_node[slot] = id;
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }

    let root_repr = eg.find_const(root);
    if best_cost[root_repr.to_usize()] == UNSET {
        return None;
    }
    Some(reconstruct(eg, &best_node, root_repr))
}

fn reconstruct<Cfg, L, const T: bool, const P: bool>(
    eg: &EGraph<Cfg, L, T, P>,
    best_node: &[Cfg::G],
    repr: Cfg::G,
) -> Term
where
    Cfg: EGraphConfig,
    L: LitVal,
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
{
    let id = best_node[repr.to_usize()];
    let name = eg.node_op_name(id).to_string();

    if let Some(val) = eg.get_lit_val(id) {
        return Term::Lit(val.to_string(), Span::Dummy);
    }

    let mut children = Vec::new();
    eg.for_each_child(id, |child, mult| {
        if mult == Cfg::M::ZERO {
            return;
        }
        let t = reconstruct(eg, best_node, eg.find_const(child));
        // `mult - 1` clones and then move the original in, rather than `mult`
        // clones followed by dropping it. At the overwhelmingly common `mult == 1`
        // that is one deep copy saved per child, and deep copies compound: the
        // previous form made extraction of a depth-`d` chain O(d^2) node copies
        // for a `d`-node result, because each level copied the whole subterm its
        // recursive call had just built and then threw the original away.
        for _ in 1..mult.to_usize() {
            children.push(t.clone());
        }
        children.push(t);
    });

    Term::App {
        op: name,
        children,
        span: Span::Dummy,
    }
}
