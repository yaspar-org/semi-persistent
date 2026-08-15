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

/// Why [`extract_best`] could not produce a term.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ExtractError {
    /// The class has nodes, but every one of them belongs to an op declared
    /// `:unextractable`, so the class denotes no extractable term.
    AllUnextractable {
        /// The class's representative id, as a plain index.
        class: usize,
        /// The op names of the class's nodes, deduplicated, in first-seen order.
        ops: Vec<String>,
    },
    /// No node in the class has a fully costed child set: the class is reachable only
    /// through cycles, or through classes that are themselves not extractable.
    NoGroundTerm {
        /// The class's representative id, as a plain index.
        class: usize,
    },
}

impl std::fmt::Display for ExtractError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ExtractError::AllUnextractable { class, ops } => write!(
                f,
                "e-class {class} has no extractable node: every node is an :unextractable op ({})",
                ops.join(", ")
            ),
            ExtractError::NoGroundTerm { class } => write!(
                f,
                "e-class {class} has no ground term: no node has a fully extractable child set"
            ),
        }
    }
}

impl std::error::Error for ExtractError {}

/// Extract the cheapest term from the e-class containing `root`.
///
/// Cost = the sum of the per-node costs of the term's nodes, where a node costs its op's
/// declared `:cost` (default 1, so an undeclared program keeps the historical AST-size cost
/// model) and an AC child of multiplicity k counts k times. Nodes whose op is declared
/// `:unextractable` are never selected.
pub fn extract_best<Cfg, L, const T: bool, const P: bool>(
    eg: &EGraph<Cfg, L, T, P>,
    root: Cfg::G,
) -> Result<Term, ExtractError>
where
    Cfg: EGraphConfig,
    L: LitVal,
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
{
    let n = eg.len();
    // Per-op cost and extractability, indexed by op id: the fixpoint below revisits every
    // node on every pass, and a registry lookup per visit would pay for the same two fields
    // repeatedly.
    let meta = eg.ops().meta_table();

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
            // `:unextractable` is a filter on candidate nodes, not a cost: an excluded node
            // never becomes a class's best, but the class stays extractable through its
            // other nodes.
            let m = meta[eg.node_op(id).to_usize()];
            if m.unextractable {
                continue;
            }
            let repr = eg.find_const(id);

            let mut total: usize = m.cost as usize;
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
        return Err(diagnose(eg, &meta, root_repr));
    }
    Ok(reconstruct(eg, &best_node, root_repr))
}

/// Explain an empty result: name the class, and say whether it was excluded by
/// `:unextractable` or is simply not grounded. Runs once, only on the failure path.
fn diagnose<Cfg, L, const T: bool, const P: bool>(
    eg: &EGraph<Cfg, L, T, P>,
    meta: &[crate::registry::OpMeta],
    repr: Cfg::G,
) -> ExtractError
where
    Cfg: EGraphConfig,
    L: LitVal,
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
{
    let class = repr.to_usize();
    let mut ops: Vec<String> = Vec::new();
    let mut any = false;
    let mut all_unextractable = true;
    for id in eg.node_ids() {
        if eg.find_const(id) != repr {
            continue;
        }
        any = true;
        if meta[eg.node_op(id).to_usize()].unextractable {
            let name = eg.node_op_name(id);
            if !ops.iter().any(|o| o == name) {
                ops.push(name.to_string());
            }
        } else {
            all_unextractable = false;
        }
    }
    if any && all_unextractable {
        ExtractError::AllUnextractable { class, ops }
    } else {
        ExtractError::NoGroundTerm { class }
    }
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
