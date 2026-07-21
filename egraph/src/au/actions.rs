// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Action generation per node kind (§3.4).
//!
//! For a class pair `(l, r)`, structural actions are the ways to factor both classes
//! through a common operator. Every unequal state also has the shared terminal
//! generalize action `Variants(best_term(l), best_term(r))`, evaluated by
//! `terms::evaluate_generalize_action`. It is not cached here because it has no
//! operator or child subproblems. Structural results are cached by `(l, r)` and
//! shared across contexts; cycle filtering happens at the OR node level.

use crate::canon::{MSetCanon, VarCanon};
use crate::config::EGraphConfig;
use crate::containers::{DenseId, Map, MapToken, ShrinkPolicy};
use crate::egraph::EGraph;
use crate::id::ENodeKind;
use crate::literal::LitVal;

use super::AuIds31;
use super::egraph_api::{AuSnapshot, ClassOf};
use crate::config::AuIds;

/// One structural action: an operator plus its paired children with multiplicities.
#[derive(Debug)]
pub struct Action<O: DenseId, A: AuIds = AuIds31> {
    pub op: O,
    pub pairs: Vec<ActionPair<A>>,
}

// Manual impls: derives would demand `A: Clone`, but `A` is a family marker.
impl<O: DenseId, A: AuIds> Clone for Action<O, A> {
    fn clone(&self) -> Self {
        Action {
            op: self.op,
            pairs: self.pairs.clone(),
        }
    }
}

/// A single child-pair in an action. `count` is the multiplicity (>1 for AC repeated children).
#[derive(Debug)]
pub struct ActionPair<A: AuIds = AuIds31> {
    pub left: A::Class,
    pub right: A::Class,
    pub count: u32,
}

impl<A: AuIds> Clone for ActionPair<A> {
    fn clone(&self) -> Self {
        *self
    }
}
impl<A: AuIds> Copy for ActionPair<A> {}
impl<A: AuIds> PartialEq for ActionPair<A> {
    fn eq(&self, other: &Self) -> bool {
        self.left == other.left && self.right == other.right && self.count == other.count
    }
}
impl<A: AuIds> Eq for ActionPair<A> {}

/// Default maximum number of AC matrices to materialize before using lazy chain states.
pub const DEFAULT_A_MAX: usize = 32;

/// The action cache: maps class pair `(l, r)` to a list of actions.
/// Semi-persistent: the `index` map (AppendOnlyVec + Map) is append-only and
/// provides branch genealogy for tokens. The `values` vec grows in lockstep
/// and is truncated on restore. Actions are deterministic from the immutable
/// snapshot, so re-derivation after restore is cheap (cache is a performance
/// optimization, not a correctness requirement).
pub struct ActionCache<O: DenseId, A: AuIds = AuIds31> {
    /// Deduplication map: (l, r) -> typed action-list id into `values`.
    index: Map<(A::Class, A::Class), A::Action>,
    /// Action lists, indexed by the map's stored value.
    values: Vec<Vec<Action<O, A>>>,
    a_max: usize,
    include_ac: bool,
}

/// Token for restoring an `ActionCache`. Wraps the Map's token, which
/// carries container identity and branch genealogy.
#[derive(Clone, Copy, Debug)]
pub struct ActionCacheToken {
    index: MapToken,
    values_len: usize,
}

impl<O: DenseId, A: AuIds> ActionCache<O, A> {
    pub fn new(a_max: usize) -> Self {
        ActionCache {
            index: Map::new(),
            values: Vec::new(),
            a_max,
            include_ac: true,
        }
    }

    /// A cache whose `generate_actions` skips AC/ACI matrix materialization.
    /// Used by the exact solver, which handles those operators by transport.
    pub fn without_ac_actions(a_max: usize) -> Self {
        ActionCache {
            index: Map::new(),
            values: Vec::new(),
            a_max,
            include_ac: false,
        }
    }

    pub fn include_ac(&self) -> bool {
        self.include_ac
    }

    pub fn get(&self, l: A::Class, r: A::Class) -> Option<&[Action<O, A>]> {
        let key = (l, r);
        self.index.id_of(&key).map(|log_idx| {
            let &idx = self.index.get(log_idx);
            self.values[idx.to_usize()].as_slice()
        })
    }

    pub fn insert(&mut self, l: A::Class, r: A::Class, actions: Vec<Action<O, A>>) {
        let idx = A::Action::from_usize(self.values.len());
        self.values.push(actions);
        self.index.insert((l, r), idx);
    }

    pub fn a_max(&self) -> usize {
        self.a_max
    }

    pub fn mark(&mut self) -> ActionCacheToken {
        ActionCacheToken {
            index: self.index.mark(ShrinkPolicy::Never),
            values_len: self.values.len(),
        }
    }

    /// Is this token restorable right now (same instance, live branch)?
    pub fn is_valid_token(&self, token: &ActionCacheToken) -> bool {
        self.index.is_valid_token(&token.index)
    }

    pub fn restore(&mut self, token: ActionCacheToken) {
        self.index.restore(token.index);
        self.values.truncate(token.values_len);
    }
}

impl<O: DenseId, A: AuIds> Default for ActionCache<O, A> {
    fn default() -> Self {
        Self::new(DEFAULT_A_MAX)
    }
}

/// Generate all actions for a class pair `(l, r)` by scanning their common operators.
/// Actions are NOT cycle-filtered here; that is done at the OR-node level.
pub fn generate_actions<Cfg: EGraphConfig, L: LitVal, const T: bool, const P: bool>(
    snap: &AuSnapshot<Cfg, L, T, P>,
    cache: &mut ActionCache<Cfg::O, Cfg::Au>,
    l: ClassOf<Cfg>,
    r: ClassOf<Cfg>,
) where
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
{
    if cache.get(l, r).is_some() {
        return;
    }

    let eg = snap.egraph();
    let members_l = snap.members(l);
    let members_r = snap.members(r);
    let a_max = cache.a_max();
    let include_ac = cache.include_ac();

    let mut actions: Vec<Action<Cfg::O, Cfg::Au>> = Vec::new();

    // Group members by op (they are already sorted by op).
    let mut il = 0;
    let mut ir = 0;

    while il < members_l.len() && ir < members_r.len() {
        let (op_l, _) = members_l[il];
        let (op_r, _) = members_r[ir];

        match op_l.to_usize().cmp(&op_r.to_usize()) {
            std::cmp::Ordering::Less => {
                // Advance l past this op.
                while il < members_l.len() && members_l[il].0 == op_l {
                    il += 1;
                }
            }
            std::cmp::Ordering::Greater => {
                // Advance r past this op.
                while ir < members_r.len() && members_r[ir].0 == op_r {
                    ir += 1;
                }
            }
            std::cmp::Ordering::Equal => {
                // Common operator: collect all l-members and r-members with this op.
                let il_start = il;
                while il < members_l.len() && members_l[il].0 == op_l {
                    il += 1;
                }
                let ir_start = ir;
                while ir < members_r.len() && members_r[ir].0 == op_r {
                    ir += 1;
                }

                let l_nodes = &members_l[il_start..il];
                let r_nodes = &members_r[ir_start..ir];

                let kind = eg.ops().info(op_l).canon_class();
                match kind {
                    ENodeKind::Plain0 => {
                        // Nullary: one action with no children (the op itself matches).
                        actions.push(Action {
                            op: op_l,
                            pairs: Vec::new(),
                        });
                    }
                    ENodeKind::Plain1
                    | ENodeKind::Plain2
                    | ENodeKind::Plain3
                    | ENodeKind::PlainN => {
                        generate_ordered_actions(snap, eg, op_l, l_nodes, r_nodes, &mut actions);
                    }
                    ENodeKind::Seq => {
                        generate_seq_actions(snap, eg, op_l, l_nodes, r_nodes, &mut actions);
                    }
                    ENodeKind::SPair => {
                        generate_spair_actions(snap, eg, op_l, l_nodes, r_nodes, &mut actions);
                    }
                    ENodeKind::MSet => {
                        if include_ac {
                            generate_mset_actions(
                                snap,
                                eg,
                                op_l,
                                l_nodes,
                                r_nodes,
                                a_max,
                                &mut actions,
                            );
                        }
                    }
                    ENodeKind::Set => {
                        if include_ac {
                            generate_set_actions(
                                snap,
                                eg,
                                op_l,
                                l_nodes,
                                r_nodes,
                                a_max,
                                &mut actions,
                            );
                        }
                    }
                    ENodeKind::Lit => {
                        generate_lit_actions(eg, op_l, l_nodes, r_nodes, &mut actions);
                    }
                }
            }
        }
    }

    // Identity expansion for singleton-canonized classes: if one side has AC/ACI
    // members for an op with identity and the other side does not (because the
    // e-graph canonized a single-child application to the bare child), generate
    // actions by treating the bare side as the singleton monomial {class^1}.
    if !include_ac {
        // The exact solver handles all AC/ACI pairs (including identity
        // expansion) through the transport path; skip materialization.
        dedup_and_insert(cache, l, r, actions);
        return;
    }
    for &(op_id, _) in members_l.iter() {
        let kind = eg.ops().info(op_id).canon_class();
        if !matches!(kind, ENodeKind::MSet | ENodeKind::Set) {
            continue;
        }
        let identity = snap.op_identity_class(op_id);
        if identity.is_none() {
            continue;
        }
        // Check if the right side has no members with this op.
        let r_has_op = members_r.iter().any(|&(o, _)| o == op_id);
        if r_has_op {
            continue;
        }
        // Treat right as singleton monomial {r^1}, left as its AC members.
        let l_op_members: Vec<(Cfg::O, Cfg::G)> = members_l
            .iter()
            .filter(|&&(o, _)| o == op_id)
            .copied()
            .collect();
        if kind == ENodeKind::Set {
            // ACI: right is a singleton set {r}.
            let r_children = vec![(r, 1u32)];
            for &(_, l_id) in &l_op_members {
                let mut l_children: Vec<ClassOf<Cfg>> = Vec::new();
                eg.for_each_child(l_id, |child, _| {
                    l_children.push(snap.class_of(child).unwrap());
                });
                let mut l_classes: Vec<(ClassOf<Cfg>, u32)> =
                    l_children.iter().map(|&c| (c, 1)).collect();
                let id_class = identity.unwrap();
                let r_total: u32 = r_children.iter().map(|(_, m)| m).sum();
                let l_total: u32 = l_classes.iter().map(|(_, m)| m).sum();
                let mut r_padded = r_children.clone();
                if l_total > r_total {
                    r_padded.push((id_class, l_total - r_total));
                } else if r_total > l_total {
                    if let Some(entry) = l_classes.iter_mut().find(|(c, _)| *c == id_class) {
                        entry.1 += r_total - l_total;
                    } else {
                        l_classes.push((id_class, r_total - l_total));
                    }
                }
                enumerate_matrices(op_id, &l_classes, &r_padded, a_max, &mut actions);
            }
        } else {
            // AC (MSet): right is singleton {r^1}.
            let mut l_mset_buf: Vec<(Cfg::G, Cfg::M)> = Vec::new();
            for &(_, l_id) in &l_op_members {
                eg.mset_children(l_id, &mut l_mset_buf);
                let l_classes: Vec<(ClassOf<Cfg>, u32)> = l_mset_buf
                    .iter()
                    .map(|(g, m)| (snap.class_of(*g).unwrap(), (*m).into()))
                    .collect();
                let l_total: u32 = l_classes.iter().map(|(_, m)| m).sum();
                let id_class = identity.unwrap();
                let mut r_classes = vec![(r, 1u32)];
                if l_total > 1 {
                    r_classes.push((id_class, l_total - 1));
                }
                enumerate_matrices(op_id, &l_classes, &r_classes, a_max, &mut actions);
            }
        }
    }
    // Symmetric: right has the op, left does not.
    for &(op_id, _) in members_r.iter() {
        let kind = eg.ops().info(op_id).canon_class();
        if !matches!(kind, ENodeKind::MSet | ENodeKind::Set) {
            continue;
        }
        let identity = snap.op_identity_class(op_id);
        if identity.is_none() {
            continue;
        }
        let l_has_op = members_l.iter().any(|&(o, _)| o == op_id);
        if l_has_op {
            continue;
        }
        let r_op_members: Vec<(Cfg::O, Cfg::G)> = members_r
            .iter()
            .filter(|&&(o, _)| o == op_id)
            .copied()
            .collect();
        if kind == ENodeKind::Set {
            let l_children = vec![(l, 1u32)];
            for &(_, r_id) in &r_op_members {
                let mut r_children: Vec<ClassOf<Cfg>> = Vec::new();
                eg.for_each_child(r_id, |child, _| {
                    r_children.push(snap.class_of(child).unwrap());
                });
                let mut r_classes: Vec<(ClassOf<Cfg>, u32)> =
                    r_children.iter().map(|&c| (c, 1)).collect();
                let id_class = identity.unwrap();
                let r_total: u32 = r_classes.iter().map(|(_, m)| m).sum();
                let l_total: u32 = l_children.iter().map(|(_, m)| m).sum();
                let mut l_padded = l_children.clone();
                if r_total > l_total {
                    l_padded.push((id_class, r_total - l_total));
                } else if l_total > r_total {
                    if let Some(entry) = r_classes.iter_mut().find(|(c, _)| *c == id_class) {
                        entry.1 += l_total - r_total;
                    } else {
                        r_classes.push((id_class, l_total - r_total));
                    }
                }
                enumerate_matrices(op_id, &l_padded, &r_classes, a_max, &mut actions);
            }
        } else {
            let mut r_mset_buf: Vec<(Cfg::G, Cfg::M)> = Vec::new();
            for &(_, r_id) in &r_op_members {
                eg.mset_children(r_id, &mut r_mset_buf);
                let r_classes: Vec<(ClassOf<Cfg>, u32)> = r_mset_buf
                    .iter()
                    .map(|(g, m)| (snap.class_of(*g).unwrap(), (*m).into()))
                    .collect();
                let r_total: u32 = r_classes.iter().map(|(_, m)| m).sum();
                let id_class = identity.unwrap();
                let mut l_classes = vec![(l, 1u32)];
                if r_total > 1 {
                    l_classes.push((id_class, r_total - 1));
                }
                enumerate_matrices(op_id, &l_classes, &r_classes, a_max, &mut actions);
            }
        }
    }

    dedup_and_insert(cache, l, r, actions);
}

/// Deduplicate actions by canonical (left, right, count) signature and insert
/// into the cache. Rewrite-derived equivalent members can produce identical
/// actions from different (l_node, r_node) pairs; duplicates would surface as
/// separate statistics edges and bias MCGS selection toward the duplicated
/// action.
fn dedup_and_insert<O: DenseId, A: AuIds>(
    cache: &mut ActionCache<O, A>,
    l: A::Class,
    r: A::Class,
    mut actions: Vec<Action<O, A>>,
) {
    let mut seen: hashbrown::HashSet<Vec<(usize, usize, u32)>> = hashbrown::HashSet::new();
    actions.retain(|action| {
        let mut sig: Vec<(usize, usize, u32)> = action
            .pairs
            .iter()
            .map(|p| (p.left.to_usize(), p.right.to_usize(), p.count))
            .collect();
        sig.sort_unstable();
        seen.insert(sig)
    });
    cache.insert(l, r, actions);
}

/// Ordered operators (fixed arity): positional zip of same-arity member pairs (§3.4.1).
fn generate_ordered_actions<Cfg: EGraphConfig, L: LitVal, const T: bool, const P: bool>(
    snap: &AuSnapshot<Cfg, L, T, P>,
    eg: &EGraph<Cfg, L, T, P>,
    op: Cfg::O,
    l_nodes: &[(Cfg::O, Cfg::G)],
    r_nodes: &[(Cfg::O, Cfg::G)],
    actions: &mut Vec<Action<Cfg::O, Cfg::Au>>,
) where
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
{
    for &(_, l_id) in l_nodes {
        let l_arity = eg.for_each_child(l_id, |_, _| {});
        for &(_, r_id) in r_nodes {
            let r_arity = eg.for_each_child(r_id, |_, _| {});
            if l_arity != r_arity {
                continue;
            }
            // Positional zip.
            let mut pairs = Vec::with_capacity(l_arity);
            let mut l_children = Vec::with_capacity(l_arity);
            let mut r_children = Vec::with_capacity(r_arity);
            eg.for_each_child(l_id, |child, _| l_children.push(child));
            eg.for_each_child(r_id, |child, _| r_children.push(child));

            for i in 0..l_arity {
                let lc = snap.class_of(l_children[i]).unwrap();
                let rc = snap.class_of(r_children[i]).unwrap();
                pairs.push(ActionPair::<Cfg::Au> {
                    left: lc,
                    right: rc,
                    count: 1,
                });
            }
            actions.push(Action { op, pairs });
        }
    }
}

/// Associative operators (sequences): one positional action when lengths
/// are equal, none otherwise (§3.4.3). Unequal-length factoring is future work
/// (doc/future/au-associative-operators.md).
fn generate_seq_actions<Cfg: EGraphConfig, L: LitVal, const T: bool, const P: bool>(
    snap: &AuSnapshot<Cfg, L, T, P>,
    eg: &EGraph<Cfg, L, T, P>,
    op: Cfg::O,
    l_nodes: &[(Cfg::O, Cfg::G)],
    r_nodes: &[(Cfg::O, Cfg::G)],
    actions: &mut Vec<Action<Cfg::O, Cfg::Au>>,
) where
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
{
    // Same logic as ordered: positional zip only when lengths match.
    generate_ordered_actions(snap, eg, op, l_nodes, r_nodes, actions);
}

/// Commutative binary operators (sorted pairs): two orientations per member pair (§3.4.2).
fn generate_spair_actions<Cfg: EGraphConfig, L: LitVal, const T: bool, const P: bool>(
    snap: &AuSnapshot<Cfg, L, T, P>,
    eg: &EGraph<Cfg, L, T, P>,
    op: Cfg::O,
    l_nodes: &[(Cfg::O, Cfg::G)],
    r_nodes: &[(Cfg::O, Cfg::G)],
    actions: &mut Vec<Action<Cfg::O, Cfg::Au>>,
) where
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
{
    for &(_, l_id) in l_nodes {
        let mut l_children = [<ClassOf<Cfg>>::default(); 2];
        let mut li = 0;
        eg.for_each_child(l_id, |child, _| {
            if li < 2 {
                l_children[li] = snap.class_of(child).unwrap();
                li += 1;
            }
        });

        for &(_, r_id) in r_nodes {
            let mut r_children = [<ClassOf<Cfg>>::default(); 2];
            let mut ri = 0;
            eg.for_each_child(r_id, |child, _| {
                if ri < 2 {
                    r_children[ri] = snap.class_of(child).unwrap();
                    ri += 1;
                }
            });

            // Orientation 1: positional (a,c), (b,d).
            let pairs1 = vec![
                ActionPair::<Cfg::Au> {
                    left: l_children[0],
                    right: r_children[0],
                    count: 1,
                },
                ActionPair::<Cfg::Au> {
                    left: l_children[1],
                    right: r_children[1],
                    count: 1,
                },
            ];
            actions.push(Action { op, pairs: pairs1 });

            // Orientation 2: crossed (a,d), (b,c) — skip if same as orientation 1.
            if !(l_children[0] == l_children[1] || r_children[0] == r_children[1]) {
                let pairs2 = vec![
                    ActionPair::<Cfg::Au> {
                        left: l_children[0],
                        right: r_children[1],
                        count: 1,
                    },
                    ActionPair::<Cfg::Au> {
                        left: l_children[1],
                        right: r_children[0],
                        count: 1,
                    },
                ];
                actions.push(Action { op, pairs: pairs2 });
            }
        }
    }
}

/// AC operators (multisets): bounded matrix enumeration, used only by the
/// differential test oracle — both production paths use min-cost transport (§3.4.4).
/// When totals are unequal and the operator has a declared identity element, the
/// shorter side is padded with identity copies to equalize the totals; the resulting
/// anti-unifier pairs unmatched elements against the identity (producing
/// `Variants(element, identity)` at those positions).
fn generate_mset_actions<Cfg: EGraphConfig, L: LitVal, const T: bool, const P: bool>(
    snap: &AuSnapshot<Cfg, L, T, P>,
    eg: &EGraph<Cfg, L, T, P>,
    op: Cfg::O,
    l_nodes: &[(Cfg::O, Cfg::G)],
    r_nodes: &[(Cfg::O, Cfg::G)],
    a_max: usize,
    actions: &mut Vec<Action<Cfg::O, Cfg::Au>>,
) where
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
{
    let identity_class = snap.op_identity_class(op);
    let mut l_mset_buf: Vec<(Cfg::G, Cfg::M)> = Vec::new();
    let mut r_mset_buf: Vec<(Cfg::G, Cfg::M)> = Vec::new();

    for &(_, l_id) in l_nodes {
        eg.mset_children(l_id, &mut l_mset_buf);
        let l_total: u32 = l_mset_buf.iter().map(|(_, m)| Into::<u32>::into(*m)).sum();

        for &(_, r_id) in r_nodes {
            eg.mset_children(r_id, &mut r_mset_buf);
            let r_total: u32 = r_mset_buf.iter().map(|(_, m)| Into::<u32>::into(*m)).sum();

            let mut l_classes: Vec<(ClassOf<Cfg>, u32)> = l_mset_buf
                .iter()
                .map(|(g, m)| (snap.class_of(*g).unwrap(), (*m).into()))
                .collect();
            let mut r_classes: Vec<(ClassOf<Cfg>, u32)> = r_mset_buf
                .iter()
                .map(|(g, m)| (snap.class_of(*g).unwrap(), (*m).into()))
                .collect();

            if l_total != r_total {
                // Pad the shorter side with identity copies if available.
                let Some(id_class) = identity_class else {
                    continue;
                };
                if l_total < r_total {
                    let deficit = r_total - l_total;
                    if let Some(entry) = l_classes.iter_mut().find(|(c, _)| *c == id_class) {
                        entry.1 += deficit;
                    } else {
                        l_classes.push((id_class, deficit));
                    }
                } else {
                    let deficit = l_total - r_total;
                    if let Some(entry) = r_classes.iter_mut().find(|(c, _)| *c == id_class) {
                        entry.1 += deficit;
                    } else {
                        r_classes.push((id_class, deficit));
                    }
                }
            }

            enumerate_matrices(op, &l_classes, &r_classes, a_max, actions);
        }
    }
}

/// ACI operators (sets): bijection enumeration (§3.4.5). When cardinalities
/// differ and the operator has a declared identity, the shorter side is padded
/// with identity elements to equalize; unmatched elements pair against the
/// identity (producing `Variants(element, identity)`).
fn generate_set_actions<Cfg: EGraphConfig, L: LitVal, const T: bool, const P: bool>(
    snap: &AuSnapshot<Cfg, L, T, P>,
    eg: &EGraph<Cfg, L, T, P>,
    op: Cfg::O,
    l_nodes: &[(Cfg::O, Cfg::G)],
    r_nodes: &[(Cfg::O, Cfg::G)],
    a_max: usize,
    actions: &mut Vec<Action<Cfg::O, Cfg::Au>>,
) where
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
{
    let identity_class = snap.op_identity_class(op);

    for &(_, l_id) in l_nodes {
        let mut l_children: Vec<ClassOf<Cfg>> = Vec::new();
        eg.for_each_child(l_id, |child, _| {
            l_children.push(snap.class_of(child).unwrap());
        });

        for &(_, r_id) in r_nodes {
            let mut r_children: Vec<ClassOf<Cfg>> = Vec::new();
            eg.for_each_child(r_id, |child, _| {
                r_children.push(snap.class_of(child).unwrap());
            });

            if l_children.len() != r_children.len() {
                let Some(id_class) = identity_class else {
                    continue;
                };
                // Pad the shorter side with identity elements.
                while l_children.len() < r_children.len() {
                    l_children.push(id_class);
                }
                while r_children.len() < l_children.len() {
                    r_children.push(id_class);
                }
            }

            let l_classes: Vec<(ClassOf<Cfg>, u32)> = l_children.iter().map(|&c| (c, 1)).collect();
            let r_classes: Vec<(ClassOf<Cfg>, u32)> = r_children.iter().map(|&c| (c, 1)).collect();

            enumerate_matrices(op, &l_classes, &r_classes, a_max, actions);
        }
    }
}

/// Literals: same-value pairing only (§3.4.6).
fn generate_lit_actions<Cfg: EGraphConfig, L: LitVal, const T: bool, const P: bool>(
    eg: &EGraph<Cfg, L, T, P>,
    op: Cfg::O,
    l_nodes: &[(Cfg::O, Cfg::G)],
    r_nodes: &[(Cfg::O, Cfg::G)],
    actions: &mut Vec<Action<Cfg::O, Cfg::Au>>,
) where
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
{
    for &(_, l_id) in l_nodes {
        let l_val = eg.get_lit_val_id(l_id);
        for &(_, r_id) in r_nodes {
            let r_val = eg.get_lit_val_id(r_id);
            if l_val == r_val {
                // Terminal action with no children.
                actions.push(Action {
                    op,
                    pairs: Vec::new(),
                });
            }
        }
    }
}

// ---------------------------------------------------------------------------
// AC matrix enumeration
// ---------------------------------------------------------------------------

/// Enumerate all valid matching-count matrices for multisets `M` and `N` with equal
/// total multiplicity. A matrix X has `x[i][j]` copies of pair `(l_i, r_j)`;
/// row i sums to `m_i`, column j sums to `n_j`.
///
/// Enumerate all valid matching-count matrices for multisets with equal total
/// multiplicity, using row-by-row distribution. Used only as a differential test
/// oracle (both production paths use min-cost transport instead). `a_max` bounds
/// the number of emitted actions.
/// The enumeration is complete and greedy-first (diagonal matches tried first).
fn enumerate_matrices<O: DenseId, A: AuIds>(
    op: O,
    l_classes: &[(A::Class, u32)],
    r_classes: &[(A::Class, u32)],
    a_max: usize,
    actions: &mut Vec<Action<O, A>>,
) {
    let rows = l_classes.len();
    let cols = r_classes.len();

    if rows == 0 || cols == 0 {
        return;
    }

    let row_sums: Vec<u32> = l_classes.iter().map(|(_, m)| *m).collect();
    let col_residual: Vec<u32> = r_classes.iter().map(|(_, m)| *m).collect();
    let mut matrix: Vec<Vec<u32>> = vec![vec![0; cols]; rows];
    let mut count = 0;

    enumerate_row(
        op,
        l_classes,
        r_classes,
        &row_sums,
        &mut matrix,
        0,
        &mut col_residual.clone(),
        a_max,
        &mut count,
        actions,
    );
}

#[allow(clippy::too_many_arguments)]
fn enumerate_row<O: DenseId, A: AuIds>(
    op: O,
    l_classes: &[(A::Class, u32)],
    r_classes: &[(A::Class, u32)],
    row_sums: &[u32],
    matrix: &mut [Vec<u32>],
    row: usize,
    col_residual: &mut Vec<u32>,
    a_max: usize,
    count: &mut usize,
    actions: &mut Vec<Action<O, A>>,
) {
    if *count >= a_max {
        return;
    }

    let rows = l_classes.len();
    let cols = r_classes.len();

    if row == rows {
        let mut pairs: Vec<ActionPair<A>> = Vec::new();
        for i in 0..rows {
            for j in 0..cols {
                if matrix[i][j] > 0 {
                    pairs.push(ActionPair::<A> {
                        left: l_classes[i].0,
                        right: r_classes[j].0,
                        count: matrix[i][j],
                    });
                }
            }
        }
        actions.push(Action { op, pairs });
        *count += 1;
        return;
    }

    distribute_row(
        op,
        l_classes,
        r_classes,
        row_sums,
        matrix,
        row,
        0,
        row_sums[row],
        col_residual,
        a_max,
        count,
        actions,
    );
}

#[allow(clippy::too_many_arguments)]
fn distribute_row<O: DenseId, A: AuIds>(
    op: O,
    l_classes: &[(A::Class, u32)],
    r_classes: &[(A::Class, u32)],
    row_sums: &[u32],
    matrix: &mut [Vec<u32>],
    row: usize,
    col: usize,
    remaining: u32,
    col_residual: &mut Vec<u32>,
    a_max: usize,
    count: &mut usize,
    actions: &mut Vec<Action<O, A>>,
) {
    if *count >= a_max {
        return;
    }

    let cols = r_classes.len();

    if col == cols - 1 {
        if remaining <= col_residual[col] {
            matrix[row][col] = remaining;
            col_residual[col] -= remaining;
            enumerate_row(
                op,
                l_classes,
                r_classes,
                row_sums,
                matrix,
                row + 1,
                col_residual,
                a_max,
                count,
                actions,
            );
            col_residual[col] += remaining;
            matrix[row][col] = 0;
        }
        return;
    }

    let max_assign = remaining.min(col_residual[col]);

    // Greedy-first: if l_classes[row] == r_classes[col] (diagonal), try the
    // maximum allocation first (it is usually optimal). Otherwise descend from max.
    let greedy = l_classes[row].0 == r_classes[col].0;
    if greedy {
        // Try max_assign first (the diagonal greedy), then the rest descending.
        for val in (0..=max_assign).rev() {
            matrix[row][col] = val;
            col_residual[col] -= val;
            distribute_row(
                op,
                l_classes,
                r_classes,
                row_sums,
                matrix,
                row,
                col + 1,
                remaining - val,
                col_residual,
                a_max,
                count,
                actions,
            );
            col_residual[col] += val;
            matrix[row][col] = 0;
            if *count >= a_max {
                return;
            }
        }
    } else {
        // Off-diagonal: try from max down (so smaller allocations come later).
        for val in (0..=max_assign).rev() {
            matrix[row][col] = val;
            col_residual[col] -= val;
            distribute_row(
                op,
                l_classes,
                r_classes,
                row_sums,
                matrix,
                row,
                col + 1,
                remaining - val,
                col_residual,
                a_max,
                count,
                actions,
            );
            col_residual[col] += val;
            matrix[row][col] = 0;
            if *count >= a_max {
                return;
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::egraph::EGraph31;
    use crate::literal::NiraLitVal;

    /// Appendix B worked example: AU(and{a,b,c}, and{b,c,d}) produces exactly 6 actions.
    #[test]
    fn appendix_b_six_actions() {
        let mut eg = EGraph31::<NiraLitVal, false, false>::new();
        let int = eg.intern_sort("Int");
        let a_op = eg.register_op0("a", int);
        let b_op = eg.register_op0("b", int);
        let c_op = eg.register_op0("c", int);
        let d_op = eg.register_op0("d", int);
        let and_op = eg.register_set("and", int, int);

        let a = eg.add(a_op, &[]);
        let b = eg.add(b_op, &[]);
        let c = eg.add(c_op, &[]);
        let d = eg.add(d_op, &[]);
        let and_abc = eg.add(and_op, &[a, b, c]);
        let and_bcd = eg.add(and_op, &[b, c, d]);
        eg.rebuild();

        let snap = AuSnapshot::new(&eg).unwrap();
        let l = snap.class_of(and_abc).unwrap();
        let r = snap.class_of(and_bcd).unwrap();

        let mut cache = ActionCache::new(100);
        generate_actions(&snap, &mut cache, l, r);

        let acts = cache.get(l, r).unwrap();
        // 3 distinct children on each side, all mult 1 -> 3! = 6 bijections.
        assert_eq!(acts.len(), 6, "expected 6 actions, got {}", acts.len());

        // Each action should have 3 pairs with count 1.
        for action in acts {
            assert_eq!(action.pairs.len(), 3);
            for pair in &action.pairs {
                assert_eq!(pair.count, 1);
            }
        }
    }

    /// AC with repeated children: AU(plus{a,a}, plus{a,b}) -> matrices with margin (2) and (1,1).
    #[test]
    fn ac_repeated_children() {
        let mut eg = EGraph31::<NiraLitVal, false, false>::new();
        let int = eg.intern_sort("Int");
        let a_op = eg.register_op0("a", int);
        let b_op = eg.register_op0("b", int);
        let plus_op = eg.register_mset("plus", int, int);

        let a = eg.add(a_op, &[]);
        let b = eg.add(b_op, &[]);
        let plus_aa = eg.add(plus_op, &[a, a]);
        let plus_ab = eg.add(plus_op, &[a, b]);
        eg.rebuild();

        let snap = AuSnapshot::new(&eg).unwrap();
        let l = snap.class_of(plus_aa).unwrap();
        let r = snap.class_of(plus_ab).unwrap();

        let mut cache = ActionCache::new(100);
        generate_actions(&snap, &mut cache, l, r);

        let acts = cache.get(l, r).unwrap();
        // L = {a^2}, R = {a^1, b^1}. Row margin = [2], col margins = [1, 1].
        // Only one matrix: x[0][0]=1, x[0][1]=1 (the row of 2 is split across 2 cols).
        assert_eq!(acts.len(), 1, "expected 1 action, got {}", acts.len());
        assert_eq!(acts[0].pairs.len(), 2);
    }

    /// Ordered: f(a,b) and f(c,d) produce one positional action with 2 pairs.
    #[test]
    fn ordered_positional_zip() {
        let mut eg = EGraph31::<NiraLitVal, false, false>::new();
        let int = eg.intern_sort("Int");
        let a_op = eg.register_op0("a", int);
        let b_op = eg.register_op0("b", int);
        let c_op = eg.register_op0("c", int);
        let d_op = eg.register_op0("d", int);
        let f_op = eg.register_op2("f", int, int, int);

        let a = eg.add(a_op, &[]);
        let b = eg.add(b_op, &[]);
        let c = eg.add(c_op, &[]);
        let d = eg.add(d_op, &[]);
        let fab = eg.add(f_op, &[a, b]);
        let fcd = eg.add(f_op, &[c, d]);
        eg.rebuild();

        let snap = AuSnapshot::new(&eg).unwrap();
        let l = snap.class_of(fab).unwrap();
        let r = snap.class_of(fcd).unwrap();

        let mut cache = ActionCache::new(100);
        generate_actions(&snap, &mut cache, l, r);

        let acts = cache.get(l, r).unwrap();
        assert_eq!(acts.len(), 1);
        assert_eq!(acts[0].pairs.len(), 2);
        assert_eq!(acts[0].pairs[0].count, 1);
        assert_eq!(acts[0].pairs[1].count, 1);
    }

    /// Seq preserves order and zips only equal-length members positionally.
    #[test]
    fn seq_equal_length_zips_positionally() {
        let mut eg = EGraph31::<NiraLitVal, false, false>::new();
        let int = eg.intern_sort("Int");
        let a_op = eg.register_op0("a", int);
        let b_op = eg.register_op0("b", int);
        let c_op = eg.register_op0("c", int);
        let d_op = eg.register_op0("d", int);
        let seq_op = eg.register_a("seq", int, int, crate::registry::AssocDir::Both);

        let a = eg.add(a_op, &[]);
        let b = eg.add(b_op, &[]);
        let c = eg.add(c_op, &[]);
        let d = eg.add(d_op, &[]);
        let left = eg.add(seq_op, &[a, b]);
        let right = eg.add(seq_op, &[c, d]);
        eg.rebuild();

        let snap = AuSnapshot::new(&eg).unwrap();
        let left_class = snap.class_of(left).unwrap();
        let right_class = snap.class_of(right).unwrap();
        let mut cache = ActionCache::new(100);
        generate_actions(&snap, &mut cache, left_class, right_class);

        let actions = cache.get(left_class, right_class).unwrap();
        assert_eq!(actions.len(), 1);
        assert_eq!(actions[0].pairs.len(), 2);
        assert_eq!(actions[0].pairs[0].left, snap.class_of(a).unwrap());
        assert_eq!(actions[0].pairs[0].right, snap.class_of(c).unwrap());
        assert_eq!(actions[0].pairs[1].left, snap.class_of(b).unwrap());
        assert_eq!(actions[0].pairs[1].right, snap.class_of(d).unwrap());
    }

    /// Unequal-length Seq factoring is deferred; no identity/end padding is added.
    #[test]
    fn seq_unequal_length_has_no_structural_action() {
        let mut eg = EGraph31::<NiraLitVal, false, false>::new();
        let int = eg.intern_sort("Int");
        let a_op = eg.register_op0("a", int);
        let b_op = eg.register_op0("b", int);
        let c_op = eg.register_op0("c", int);
        let d_op = eg.register_op0("d", int);
        let e_op = eg.register_op0("e", int);
        let seq_op = eg.register_a("seq", int, int, crate::registry::AssocDir::Both);

        let a = eg.add(a_op, &[]);
        let b = eg.add(b_op, &[]);
        let c = eg.add(c_op, &[]);
        let d = eg.add(d_op, &[]);
        let e = eg.add(e_op, &[]);
        let left = eg.add(seq_op, &[a, b]);
        let right = eg.add(seq_op, &[c, d, e]);
        eg.rebuild();

        let snap = AuSnapshot::new(&eg).unwrap();
        let left_class = snap.class_of(left).unwrap();
        let right_class = snap.class_of(right).unwrap();
        let mut cache = ActionCache::new(100);
        generate_actions(&snap, &mut cache, left_class, right_class);

        assert!(cache.get(left_class, right_class).unwrap().is_empty());
    }

    /// SPair: eq(a,b) vs eq(c,d) produces 2 orientations.
    #[test]
    fn spair_two_orientations() {
        let mut eg = EGraph31::<NiraLitVal, false, false>::new();
        let int = eg.intern_sort("Int");
        let a_op = eg.register_op0("a", int);
        let b_op = eg.register_op0("b", int);
        let c_op = eg.register_op0("c", int);
        let d_op = eg.register_op0("d", int);
        let eq_op = eg.register_c("eq", [int, int], int);

        let a = eg.add(a_op, &[]);
        let b = eg.add(b_op, &[]);
        let c = eg.add(c_op, &[]);
        let d = eg.add(d_op, &[]);
        let eq_ab = eg.add(eq_op, &[a, b]);
        let eq_cd = eg.add(eq_op, &[c, d]);
        eg.rebuild();

        let snap = AuSnapshot::new(&eg).unwrap();
        let l = snap.class_of(eq_ab).unwrap();
        let r = snap.class_of(eq_cd).unwrap();

        let mut cache = ActionCache::new(100);
        generate_actions(&snap, &mut cache, l, r);

        let acts = cache.get(l, r).unwrap();
        assert_eq!(acts.len(), 2, "expected 2 orientations");
    }

    /// SPair dedup when a == b: eq(a,a) vs eq(c,d) produces only 1 orientation.
    #[test]
    fn spair_dedup_same_children() {
        let mut eg = EGraph31::<NiraLitVal, false, false>::new();
        let int = eg.intern_sort("Int");
        let a_op = eg.register_op0("a", int);
        let c_op = eg.register_op0("c", int);
        let d_op = eg.register_op0("d", int);
        let eq_op = eg.register_c("eq", [int, int], int);

        let a = eg.add(a_op, &[]);
        let c = eg.add(c_op, &[]);
        let d = eg.add(d_op, &[]);
        let eq_aa = eg.add(eq_op, &[a, a]);
        let eq_cd = eg.add(eq_op, &[c, d]);
        eg.rebuild();

        let snap = AuSnapshot::new(&eg).unwrap();
        let l = snap.class_of(eq_aa).unwrap();
        let r = snap.class_of(eq_cd).unwrap();

        let mut cache = ActionCache::new(100);
        generate_actions(&snap, &mut cache, l, r);

        let acts = cache.get(l, r).unwrap();
        assert_eq!(
            acts.len(),
            1,
            "dedup: only 1 orientation when l children are same"
        );
    }

    /// Identity padding: conj{a, b, c} vs conj{b, c} with identity `tt`.
    /// The shorter side is padded to conj{b, c, tt}, then the bijection pairs
    /// b-b, c-c, a-tt, producing one action with 3 pairs.
    #[test]
    fn identity_padding_unequal_cardinality() {
        let mut eg = EGraph31::<NiraLitVal, false, false>::new();
        let bool_s = eg.intern_sort("Bool");
        let a_op = eg.register_op0("a", bool_s);
        let b_op = eg.register_op0("b", bool_s);
        let c_op = eg.register_op0("c", bool_s);
        let tt_op = eg.register_op0("tt", bool_s);
        let conj_op = eg.register_set("conj", bool_s, bool_s);

        let a = eg.add(a_op, &[]);
        let b = eg.add(b_op, &[]);
        let c = eg.add(c_op, &[]);
        let tt = eg.add(tt_op, &[]);
        eg.set_unit_node(conj_op, tt);

        let left = eg.add(conj_op, &[a, b, c]); // conj{a, b, c}
        let right = eg.add(conj_op, &[b, c]); // conj{b, c}
        eg.rebuild();

        let snap = AuSnapshot::new(&eg).unwrap();
        let lc = snap.class_of(left).unwrap();
        let rc = snap.class_of(right).unwrap();

        let mut cache = ActionCache::new(100);
        generate_actions(&snap, &mut cache, lc, rc);

        let acts = cache.get(lc, rc).unwrap();
        // With identity padding: 3 elements on each side, so 3! = 6 bijections.
        // But b and c are shared, so the greedy diagonal dominates. At minimum
        // there should be actions (not zero, which the old code would produce).
        assert!(
            !acts.is_empty(),
            "identity padding should produce actions for unequal cardinality"
        );
        // The optimal action has 3 pairs (one of which pairs a with tt).
        let has_identity_pair = acts.iter().any(|action| {
            action.pairs.len() == 3
                && action.pairs.iter().any(|p| {
                    let tt_class = snap.class_of(tt).unwrap();
                    (p.left == snap.class_of(a).unwrap() && p.right == tt_class)
                        || (p.right == snap.class_of(a).unwrap() && p.left == tt_class)
                })
        });
        assert!(has_identity_pair, "one action should pair `a` with `tt`");
    }

    /// Complete AC matrix enumeration: plus{a^2, b^2} vs plus{c^2, d^2}
    /// has margins [2,2] and [2,2]. The complete enumerator produces 3 valid
    /// matrices (k=0,1,2 for the (a,c) cell), including the interior one.
    /// The Exact solver is complete; it finds the optimum among all of them.
    #[test]
    fn ac_complete_enumeration_includes_all_matrices() {
        let mut eg = EGraph31::<NiraLitVal, false, false>::new();
        let int = eg.intern_sort("Int");
        let a_op = eg.register_op0("a", int);
        let b_op = eg.register_op0("b", int);
        let c_op = eg.register_op0("c", int);
        let d_op = eg.register_op0("d", int);
        let plus_op = eg.register_mset("plus", int, int);

        let a = eg.add(a_op, &[]);
        let b = eg.add(b_op, &[]);
        let c = eg.add(c_op, &[]);
        let d = eg.add(d_op, &[]);
        let left = eg.add(plus_op, &[a, a, b, b]); // plus{a^2, b^2}
        let right = eg.add(plus_op, &[c, c, d, d]); // plus{c^2, d^2}
        eg.rebuild();

        let snap = AuSnapshot::new(&eg).unwrap();
        let lc = snap.class_of(left).unwrap();
        let rc = snap.class_of(right).unwrap();

        let mut cache = ActionCache::new(100);
        generate_actions(&snap, &mut cache, lc, rc);

        let acts = cache.get(lc, rc).unwrap();
        // 3 valid matrices: k=0, k=1, k=2 for the (a,c) cell.
        assert_eq!(
            acts.len(),
            3,
            "expected 3 complete matrices, got {}",
            acts.len()
        );
    }

    /// Literal: same value matches, different values don't.
    #[test]
    fn literal_same_value() {
        let mut eg = EGraph31::<NiraLitVal, false, false>::new();
        let int = eg.intern_sort("Int");
        let lit_op = eg.register_lit("intlit", int);

        let val1 = eg.intern_lit(crate::literal::NiraLitVal::Int(42.into()));
        let val2 = eg.intern_lit(crate::literal::NiraLitVal::Int(99.into()));

        let l = eg.add_lit(lit_op, val1);
        let r1 = eg.add_lit(lit_op, val1);
        let r2 = eg.add_lit(lit_op, val2);
        eg.rebuild();

        let snap = AuSnapshot::new(&eg).unwrap();
        let lc = snap.class_of(l).unwrap();
        let r1c = snap.class_of(r1).unwrap();
        let r2c = snap.class_of(r2).unwrap();

        // Same value -> 1 action.
        let mut cache = ActionCache::new(100);
        generate_actions(&snap, &mut cache, lc, r1c);
        let acts = cache.get(lc, r1c).unwrap();
        assert_eq!(acts.len(), 1);

        // Different value -> 0 actions.
        generate_actions(&snap, &mut cache, lc, r2c);
        let acts = cache.get(lc, r2c).unwrap();
        assert_eq!(acts.len(), 0);
    }
}
