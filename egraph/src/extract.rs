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
    Cfg::Policy: crate::config::StorePolicy<Cfg, T>,
{
    let meta = eg.ops().meta_table();
    let (best_cost, best_node) = best_members(eg);
    const UNSET: usize = usize::MAX;
    let root_repr = eg.find_const(root);
    if best_cost[root_repr.to_usize()] == UNSET {
        return Err(diagnose(eg, &meta, root_repr));
    }
    Ok(reconstruct(eg, &best_node, root_repr))
}

/// The additive-cost fixpoint behind [`extract_best`]: per class id, the least cost
/// of a term rooted there (`usize::MAX` when none is grounded) and the member that
/// attains it. Exposed so a caller can score the greedy choice with another cost.
pub fn best_members<Cfg, L, const T: bool, const P: bool>(
    eg: &EGraph<Cfg, L, T, P>,
) -> (Vec<usize>, Vec<Cfg::G>)
where
    Cfg: EGraphConfig,
    L: LitVal,
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
    Cfg::Policy: crate::config::StorePolicy<Cfg, T>,
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
    // Ties on cost are broken by the term's height, then by the node's content colour
    // (`doc/goal-stable-extraction.md`, decision 5), so the choice depends on content,
    // not on the order nodes were allocated in. Height comes before colour because a
    // choice that only ties on cost may close a cycle when operators cost 0 (a class's
    // best reached through a child whose best reaches the class); height strictly grows
    // from child to parent, so no chosen node can lie on a cycle. Cost comes first, so
    // the optimum is unchanged.
    let mut best_height: Vec<usize> = vec![UNSET; n];
    let colouring = eg.canon_colours();
    let mut colour: Vec<crate::canon_colour::Colour> =
        vec![crate::canon_colour::Colour(u128::MAX); n];
    for (ms, cs) in colouring.members.iter().zip(&colouring.node_colour) {
        for (&id, &c) in ms.iter().zip(cs) {
            if let Some(slot) = colour.get_mut(id.to_usize()) {
                *slot = c;
            }
        }
    }

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
            // A congruent duplicate has an unflagged twin of identical content, hence of
            // identical cost, so skipping it cannot change the optimum.
            if eg.node_flags(id) & crate::node_types::FLAG_CONGRUENT_DUP != 0 {
                continue;
            }
            let repr = eg.find_const(id);

            let mut total: usize = m.cost as usize;
            let mut height: usize = 0;
            let mut ok = true;
            eg.for_each_child(id, |child, mult| {
                if !ok {
                    return;
                }
                let k = eg.find_const(child).to_usize();
                let c = best_cost[k];
                if c == UNSET {
                    ok = false;
                } else {
                    total = total.saturating_add(c.saturating_mul(mult.to_usize()));
                    height = height.max(best_height[k].saturating_add(1));
                }
            });
            if !ok {
                continue;
            }
            // A cost too large to count saturates one below `UNSET`, which marks "no
            // best": the term is grounded and ranks last, and is never reported missing.
            let total = total.min(UNSET - 1);

            let slot = repr.to_usize();
            let incumbent = (
                best_cost[slot],
                best_height[slot],
                colour[best_node[slot].to_usize()],
            );
            if (total, height, colour[id.to_usize()]) < incumbent {
                best_cost[slot] = total;
                best_height[slot] = height;
                best_node[slot] = id;
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }

    (best_cost, best_node)
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
    Cfg::Policy: crate::config::StorePolicy<Cfg, T>,
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

/// The term the chosen nodes spell, built bottom-up with an explicit stack: a term's
/// depth is the e-graph's, which a recursion would carry on the call stack. A subterm
/// shared by several parents is built once and copied into each. An AC, ACI, or
/// commutative node's children are stored in class-id order; they are placed in content
/// colour order, so the term's text does not depend on ids either.
fn reconstruct<Cfg, L, const T: bool, const P: bool>(
    eg: &EGraph<Cfg, L, T, P>,
    best_node: &[Cfg::G],
    repr: Cfg::G,
) -> Term
where
    Cfg: EGraphConfig,
    L: LitVal,
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
    Cfg::Policy: crate::config::StorePolicy<Cfg, T>,
{
    let colouring = eg.canon_colours();
    let class_colour = |c: Cfg::G| {
        colouring
            .class_of(eg.class_repr(c))
            .and_then(|i| colouring.class_colour.get(i))
            .copied()
    };
    // A chosen node's children: the child classes, each with its multiplicity.
    let is_unordered = |id: Cfg::G| {
        matches!(
            eg.ops().info(eg.node_op(id)).kind,
            crate::registry::OpKind::MSet { .. }
                | crate::registry::OpKind::Set { .. }
                | crate::registry::OpKind::Commutative { .. }
        )
    };
    let kids_of = |id: Cfg::G| {
        let mut kids: Vec<(Cfg::G, Cfg::M)> = Vec::new();
        eg.for_each_child(id, |child, mult| {
            kids.push((eg.find_const(child), mult));
        });
        if matches!(
            eg.ops().info(eg.node_op(id)).kind,
            crate::registry::OpKind::MSet { .. }
                | crate::registry::OpKind::Set { .. }
                | crate::registry::OpKind::Commutative { .. }
        ) {
            kids.sort_by_key(|&(k, _)| class_colour(k));
        }
        kids
    };
    let mut built: std::collections::BTreeMap<usize, Term> = std::collections::BTreeMap::new();
    let mut stack: Vec<(Cfg::G, bool)> = vec![(repr, false)];
    while let Some((c, expanded)) = stack.pop() {
        if built.contains_key(&c.to_usize()) {
            continue;
        }
        let id = best_node[c.to_usize()];
        if let Some(val) = eg.get_lit_val(id) {
            built.insert(c.to_usize(), Term::Lit(val.to_string(), Span::Dummy));
            continue;
        }
        let kids = kids_of(id);
        if !expanded {
            stack.push((c, true));
            for &(k, _) in kids.iter().rev() {
                if !built.contains_key(&k.to_usize()) {
                    stack.push((k, false));
                }
            }
            continue;
        }
        // Every child was built before this second visit: the chosen nodes form no
        // cycle (their heights strictly decrease toward the leaves).
        // An AC child of count k is written once, `x:k`, as Semper reads it back.
        let mut children: Vec<Term> = kids
            .iter()
            .filter_map(|&(k, m)| {
                let t = built.get(&k.to_usize()).cloned()?;
                Some(if m == Cfg::M::ONE {
                    t
                } else {
                    Term::Counted {
                        term: Box::new(t),
                        count: m.to_biguint(),
                        span: Span::Dummy,
                    }
                })
            })
            .collect();
        // An unordered node's operands print sorted by their own text, as the cost-model
        // printer writes them: fixed by content, and readable.
        if is_unordered(id) {
            children.sort_by_cached_key(|t| t.to_string());
        }
        built.insert(
            c.to_usize(),
            Term::App {
                op: eg.node_op_name(id).to_string(),
                children,
                span: Span::Dummy,
            },
        );
    }
    built
        .remove(&repr.to_usize())
        .unwrap_or_else(|| Term::Lit(String::new(), Span::Dummy))
}
