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
use crate::containers::{DenseId, MapToken, ShrinkPolicy, SpMap};
use crate::egraph::EGraph;
use crate::id::ENodeKind;
use crate::literal::LitVal;
use crate::multiplicity::{Multiplicity, MultiplicityLike};

use super::AuIds31;
use super::egraph_api::{AuSnapshot, ClassOf};
use crate::config::AuIds;

/// One structural action: an operator plus its paired children with multiplicities.
#[derive(Debug)]
pub struct Action<O: DenseId, A: AuIds = AuIds31, M: MultiplicityLike = Multiplicity> {
    pub op: O,
    pub pairs: Vec<ActionPair<A, M>>,
}

// Manual impls: derives would demand `A: Clone`, but `A` is a family marker.
impl<O: DenseId, A: AuIds, M: MultiplicityLike> Clone for Action<O, A, M> {
    fn clone(&self) -> Self {
        Action {
            op: self.op,
            pairs: self.pairs.clone(),
        }
    }
}

/// A single child-pair in an action. `count` is the multiplicity (>1 for AC repeated children).
///
/// `count` is at the configured multiplicity width [`EGraphConfig::M`], not a fixed `u32`.
/// It is a copy of an AC child multiplicity — or, in the matrix enumerator, a sum of
/// several — so `Cfg::M` is the width it already has, and the previous hardcoded `u32`
/// meant a *narrowing* on the way in. At `Multiplicity64` that narrowing dropped members
/// whose multiplicity the e-graph represents fine: a completeness loss with no upside,
/// since the enumerator's arithmetic is checked at whatever width it runs.
///
/// This is not a space argument in either direction. At 4-byte class ids a 2-byte count
/// pads to the same 12-byte pair as a 4-byte one, and at 8-byte ids every width pads to
/// 24 — the same padding fact `multiplicity_width_is_free_at_the_wide_id_width` records
/// for AC children. Every shipped config is byte-for-byte unchanged by this parameter;
/// what it buys is that the field cannot cap a width the e-graph supports.
///
/// [`EGraphConfig::M`]: crate::config::EGraphConfig::M
#[derive(Debug)]
pub struct ActionPair<A: AuIds = AuIds31, M: MultiplicityLike = Multiplicity> {
    pub left: A::Class,
    pub right: A::Class,
    pub count: M,
}

impl<A: AuIds, M: MultiplicityLike> Clone for ActionPair<A, M> {
    fn clone(&self) -> Self {
        *self
    }
}
impl<A: AuIds, M: MultiplicityLike> Copy for ActionPair<A, M> {}
impl<A: AuIds, M: MultiplicityLike> PartialEq for ActionPair<A, M> {
    fn eq(&self, other: &Self) -> bool {
        self.left == other.left && self.right == other.right && self.count == other.count
    }
}
impl<A: AuIds, M: MultiplicityLike> Eq for ActionPair<A, M> {}

/// Default maximum number of AC matrices to materialize before using lazy chain states.
pub const DEFAULT_A_MAX: usize = 32;

/// The action cache: maps class pair `(l, r)` to a list of actions.
/// Semi-persistent: the `index` map (AppendOnlyVec + SpMap) is append-only and
/// provides branch genealogy for tokens. The `values` vec grows in lockstep
/// and is truncated on restore. Actions are deterministic from the immutable
/// snapshot, so re-derivation after restore is cheap (cache is a performance
/// optimization, not a correctness requirement).
pub struct ActionCache<O: DenseId, A: AuIds = AuIds31, M: MultiplicityLike = Multiplicity> {
    /// Deduplication map: (l, r) -> typed action-list id into `values`.
    ///
    /// Index word `A::Index`: the map's log positions are what the `A::Action`s are
    /// minted from, and `A::Action::Index` is that word.
    index: SpMap<(A::Class, A::Class), A::Action, A::Index>,
    /// Action lists, indexed by the map's stored value.
    values: Vec<Vec<Action<O, A, M>>>,
    a_max: usize,
    include_ac: bool,
}

/// Token for restoring an `ActionCache`. Wraps the SpMap's token, which
/// carries container identity and branch genealogy.
#[derive(Clone, Copy, Debug)]
pub struct ActionCacheToken {
    index: MapToken,
    values_len: usize,
}

impl<O: DenseId, A: AuIds, M: MultiplicityLike> ActionCache<O, A, M> {
    pub fn new(a_max: usize) -> Self {
        ActionCache {
            index: SpMap::new(),
            values: Vec::new(),
            a_max,
            include_ac: true,
        }
    }

    /// A cache whose `generate_actions` skips AC/ACI matrix materialization.
    /// Used by the exact solver, which handles those operators by transport.
    pub fn without_ac_actions(a_max: usize) -> Self {
        ActionCache {
            index: SpMap::new(),
            values: Vec::new(),
            a_max,
            include_ac: false,
        }
    }

    pub fn include_ac(&self) -> bool {
        self.include_ac
    }

    pub fn get(&self, l: A::Class, r: A::Class) -> Option<&[Action<O, A, M>]> {
        let key = (l, r);
        self.index.id_of(&key).map(|log_idx| {
            let &idx = self.index.get_val(log_idx);
            self.values[idx.to_usize()].as_slice()
        })
    }

    pub fn insert(&mut self, l: A::Class, r: A::Class, actions: Vec<Action<O, A, M>>) {
        // Checked: `values` is a plain `Vec`, so nothing but this call stands between the
        // action-list count and the `A::Action` id space. Masking would hand the new list
        // the id of an older one, and `get` would then serve the wrong action list for a
        // class pair — a search that expands moves belonging to a different subproblem.
        let idx = crate::id::id_at::<A::Action>(self.values.len());
        self.values.push(actions);
        self.index
            .try_insert((l, r), idx)
            .expect("AU arena sized by its index word");
    }

    pub fn a_max(&self) -> usize {
        self.a_max
    }

    pub fn mark(&mut self) -> ActionCacheToken {
        ActionCacheToken {
            index: self
                .index
                .try_mark(ShrinkPolicy::Never)
                .expect("mark: depth bounded by the search driver"),
            values_len: self.values.len(),
        }
    }

    /// Is this token restorable right now (same instance, live branch)?
    pub fn is_valid_token(&self, token: &ActionCacheToken) -> bool {
        self.index.is_valid_token(&token.index)
    }

    pub fn restore(&mut self, token: ActionCacheToken) {
        self.index
            .try_restore(token.index)
            .expect("restore: token minted by this container's own mark");
        self.values.truncate(token.values_len);
    }
}

impl<O: DenseId, A: AuIds, M: MultiplicityLike> Default for ActionCache<O, A, M> {
    fn default() -> Self {
        Self::new(DEFAULT_A_MAX)
    }
}

/// Generate all actions for a class pair `(l, r)` by scanning their common operators.
/// Actions are NOT cycle-filtered here; that is done at the OR-node level.
pub fn generate_actions<Cfg: EGraphConfig, L: LitVal, const T: bool, const P: bool>(
    snap: &AuSnapshot<Cfg, L, T, P>,
    cache: &mut ActionCache<Cfg::O, Cfg::Au, Cfg::M>,
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

    let mut actions: Vec<Action<Cfg::O, Cfg::Au, Cfg::M>> = Vec::new();

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
            let r_children = vec![(r, Cfg::M::ONE)];
            for &(_, l_id) in &l_op_members {
                let mut l_children: Vec<ClassOf<Cfg>> = Vec::new();
                eg.for_each_child(l_id, |child, _| {
                    l_children.push(snap.class_of(child).unwrap());
                });
                let mut l_classes: Vec<(ClassOf<Cfg>, Cfg::M)> =
                    l_children.iter().map(|&c| (c, Cfg::M::ONE)).collect();
                let id_class = identity.unwrap();
                // A set member's cardinality is bounded by `for_each_child`'s
                // 64·node_count cap, which exceeds `Count` for a wide config, so
                // even these all-ones totals are summed with overflow detection.
                let (Some(r_total), Some(l_total)) =
                    (counts_total(&r_children), counts_total(&l_classes))
                else {
                    continue;
                };
                let mut r_padded = r_children.clone();
                if l_total > r_total {
                    r_padded.push((id_class, l_total.saturating_sub(r_total)));
                } else if r_total > l_total
                    && pad_identity(&mut l_classes, id_class, r_total.saturating_sub(l_total))
                        .is_none()
                {
                    continue;
                }
                enumerate_matrices(op_id, &l_classes, &r_padded, a_max, &mut actions);
            }
        } else {
            // AC (MSet): right is singleton {r^1}.
            let mut l_mset_buf: Vec<(Cfg::G, Cfg::M)> = Vec::new();
            for &(_, l_id) in &l_op_members {
                eg.mset_children(l_id, &mut l_mset_buf);
                let Some((l_classes, l_total)) = mset_counts(snap, &l_mset_buf) else {
                    continue;
                };
                let id_class = identity.unwrap();
                let mut r_classes = vec![(r, Cfg::M::ONE)];
                if l_total > Cfg::M::ONE {
                    r_classes.push((id_class, l_total.saturating_sub(Cfg::M::ONE)));
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
            let l_children = vec![(l, Cfg::M::ONE)];
            for &(_, r_id) in &r_op_members {
                let mut r_children: Vec<ClassOf<Cfg>> = Vec::new();
                eg.for_each_child(r_id, |child, _| {
                    r_children.push(snap.class_of(child).unwrap());
                });
                let mut r_classes: Vec<(ClassOf<Cfg>, Cfg::M)> =
                    r_children.iter().map(|&c| (c, Cfg::M::ONE)).collect();
                let id_class = identity.unwrap();
                // See the mirrored branch above on why these are checked.
                let (Some(r_total), Some(l_total)) =
                    (counts_total(&r_classes), counts_total(&l_children))
                else {
                    continue;
                };
                let mut l_padded = l_children.clone();
                if r_total > l_total {
                    l_padded.push((id_class, r_total.saturating_sub(l_total)));
                } else if l_total > r_total
                    && pad_identity(&mut r_classes, id_class, l_total.saturating_sub(r_total))
                        .is_none()
                {
                    continue;
                }
                enumerate_matrices(op_id, &l_padded, &r_classes, a_max, &mut actions);
            }
        } else {
            let mut r_mset_buf: Vec<(Cfg::G, Cfg::M)> = Vec::new();
            for &(_, r_id) in &r_op_members {
                eg.mset_children(r_id, &mut r_mset_buf);
                let Some((r_classes, r_total)) = mset_counts(snap, &r_mset_buf) else {
                    continue;
                };
                let id_class = identity.unwrap();
                let mut l_classes = vec![(l, Cfg::M::ONE)];
                if r_total > Cfg::M::ONE {
                    l_classes.push((id_class, r_total.saturating_sub(Cfg::M::ONE)));
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
fn dedup_and_insert<O: DenseId, A: AuIds, M: MultiplicityLike>(
    cache: &mut ActionCache<O, A, M>,
    l: A::Class,
    r: A::Class,
    mut actions: Vec<Action<O, A, M>>,
) {
    // The signature holds the pair's own types. Widening the two class ids to `usize` to
    // key a hash set bought nothing — dense ids are already `Hash + Ord` — and cost real
    // bytes in a set that is rebuilt for every class pair the search visits: at the 31-bit
    // family a `(usize, usize, u32)` entry is 24 bytes to this tuple's 12, because the two
    // widened words also raise the tuple's alignment and so its tail padding.
    let mut seen: hashbrown::HashSet<Vec<(A::Class, A::Class, M)>> = hashbrown::HashSet::new();
    actions.retain(|action| {
        let mut sig: Vec<(A::Class, A::Class, M)> = action
            .pairs
            .iter()
            .map(|p| (p.left, p.right, p.count))
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
    actions: &mut Vec<Action<Cfg::O, Cfg::Au, Cfg::M>>,
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
                pairs.push(ActionPair::<Cfg::Au, Cfg::M> {
                    left: lc,
                    right: rc,
                    count: Cfg::M::ONE,
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
    actions: &mut Vec<Action<Cfg::O, Cfg::Au, Cfg::M>>,
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
    actions: &mut Vec<Action<Cfg::O, Cfg::Au, Cfg::M>>,
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
                ActionPair::<Cfg::Au, Cfg::M> {
                    left: l_children[0],
                    right: r_children[0],
                    count: Cfg::M::ONE,
                },
                ActionPair::<Cfg::Au, Cfg::M> {
                    left: l_children[1],
                    right: r_children[1],
                    count: Cfg::M::ONE,
                },
            ];
            actions.push(Action { op, pairs: pairs1 });

            // Orientation 2: crossed (a,d), (b,c) — skip if same as orientation 1.
            if !(l_children[0] == l_children[1] || r_children[0] == r_children[1]) {
                let pairs2 = vec![
                    ActionPair::<Cfg::Au, Cfg::M> {
                        left: l_children[0],
                        right: r_children[1],
                        count: Cfg::M::ONE,
                    },
                    ActionPair::<Cfg::Au, Cfg::M> {
                        left: l_children[1],
                        right: r_children[0],
                        count: Cfg::M::ONE,
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
    actions: &mut Vec<Action<Cfg::O, Cfg::Au, Cfg::M>>,
) where
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
{
    let identity_class = snap.op_identity_class(op);
    let mut l_mset_buf: Vec<(Cfg::G, Cfg::M)> = Vec::new();
    let mut r_mset_buf: Vec<(Cfg::G, Cfg::M)> = Vec::new();

    for &(_, l_id) in l_nodes {
        eg.mset_children(l_id, &mut l_mset_buf);
        // Counts and total come from one checked read, so they cannot disagree.
        let Some((l_read, l_total)) = mset_counts(snap, &l_mset_buf) else {
            continue;
        };

        for &(_, r_id) in r_nodes {
            eg.mset_children(r_id, &mut r_mset_buf);
            let Some((r_read, r_total)) = mset_counts(snap, &r_mset_buf) else {
                continue;
            };

            let mut l_classes = l_read.clone();
            let mut r_classes = r_read;

            if l_total != r_total {
                // Pad the shorter side with identity copies if available.
                let Some(id_class) = identity_class else {
                    continue;
                };
                let padded = if l_total < r_total {
                    pad_identity(&mut l_classes, id_class, r_total.saturating_sub(l_total))
                } else {
                    pad_identity(&mut r_classes, id_class, l_total.saturating_sub(r_total))
                };
                if padded.is_none() {
                    continue;
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
    actions: &mut Vec<Action<Cfg::O, Cfg::Au, Cfg::M>>,
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

            let l_classes: Vec<(ClassOf<Cfg>, Cfg::M)> =
                l_children.iter().map(|&c| (c, Cfg::M::ONE)).collect();
            let r_classes: Vec<(ClassOf<Cfg>, Cfg::M)> =
                r_children.iter().map(|&c| (c, Cfg::M::ONE)).collect();

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
    actions: &mut Vec<Action<Cfg::O, Cfg::Au, Cfg::M>>,
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

/// Read an AC member's child multiset into class counts, together with their total.
///
/// Reading the multiplicities is exact — they are already at the configured width — but
/// the *total* is not: a sum of multiplicities can exceed the width one multiplicity fits
/// in. `None` on that overflow, meaning "enumerate no actions from this member". Actions
/// are candidate generalizations, so dropping one costs search completeness, never
/// soundness — whereas a wrapped total would drive the enumerator over margins the
/// e-graph's multiset does not have, and report the resulting term as a generalization of
/// one it does.
fn mset_counts<Cfg: EGraphConfig, L: LitVal, const T: bool, const P: bool>(
    snap: &AuSnapshot<Cfg, L, T, P>,
    buf: &[(Cfg::G, Cfg::M)],
) -> Option<(Vec<(ClassOf<Cfg>, Cfg::M)>, Cfg::M)>
where
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
{
    let mut out: Vec<(ClassOf<Cfg>, Cfg::M)> = Vec::with_capacity(buf.len());
    let mut total = Cfg::M::ZERO;
    for (g, m) in buf {
        out.push((snap.class_of(*g).unwrap(), *m));
        total = total.checked_add(*m)?;
    }
    Some((out, total))
}

/// Sum of the counts, or `None` on overflow of the multiplicity width.
fn counts_total<C, M: MultiplicityLike>(v: &[(C, M)]) -> Option<M> {
    v.iter()
        .try_fold(M::ZERO, |acc, (_, k)| acc.checked_add(*k))
}

/// Add `deficit` identity copies, merging into an existing identity entry so the
/// vector stays duplicate-free. `None` on overflow of the multiplicity width.
fn pad_identity<C: PartialEq, M: MultiplicityLike>(
    v: &mut Vec<(C, M)>,
    id_class: C,
    deficit: M,
) -> Option<()> {
    match v.iter_mut().find(|(c, _)| *c == id_class) {
        Some(entry) => entry.1 = entry.1.checked_add(deficit)?,
        None => v.push((id_class, deficit)),
    }
    Some(())
}

/// Enumerate all valid matching-count matrices for multisets `M` and `N` with equal
/// total multiplicity. A matrix X has `x[i][j]` copies of pair `(l_i, r_j)`;
/// row i sums to `m_i`, column j sums to `n_j`.
///
/// Row-by-row distribution, complete and greedy-first (diagonal matches tried first).
/// Used only as a differential test oracle — both production paths use min-cost
/// transport instead. `a_max` bounds the number of emitted actions.
///
/// Margins, residuals and cells all carry the configured multiplicity width, the same
/// width the input multisets came in at, so nothing here needs a narrowing check. The
/// arithmetic that *can* leave the width is the summation the caller already did
/// ([`counts_total`], [`pad_identity`], [`mset_counts`]); inside the recursion every
/// value is bounded by a margin, so the subtractions are exact and the descending scans
/// stay in range by construction.
fn enumerate_matrices<O: DenseId, A: AuIds, M: MultiplicityLike>(
    op: O,
    l_classes: &[(A::Class, M)],
    r_classes: &[(A::Class, M)],
    a_max: usize,
    actions: &mut Vec<Action<O, A, M>>,
) {
    let rows = l_classes.len();
    let cols = r_classes.len();

    if rows == 0 || cols == 0 {
        return;
    }

    let row_sums: Vec<M> = l_classes.iter().map(|(_, m)| *m).collect();
    let col_residual: Vec<M> = r_classes.iter().map(|(_, m)| *m).collect();
    let mut matrix: Vec<Vec<M>> = vec![vec![M::ZERO; cols]; rows];
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
fn enumerate_row<O: DenseId, A: AuIds, M: MultiplicityLike>(
    op: O,
    l_classes: &[(A::Class, M)],
    r_classes: &[(A::Class, M)],
    row_sums: &[M],
    matrix: &mut [Vec<M>],
    row: usize,
    col_residual: &mut Vec<M>,
    a_max: usize,
    count: &mut usize,
    actions: &mut Vec<Action<O, A, M>>,
) {
    if *count >= a_max {
        return;
    }

    let rows = l_classes.len();
    let cols = r_classes.len();

    if row == rows {
        let mut pairs: Vec<ActionPair<A, M>> = Vec::new();
        for i in 0..rows {
            for j in 0..cols {
                if matrix[i][j] > M::ZERO {
                    pairs.push(ActionPair::<A, M> {
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
fn distribute_row<O: DenseId, A: AuIds, M: MultiplicityLike>(
    op: O,
    l_classes: &[(A::Class, M)],
    r_classes: &[(A::Class, M)],
    row_sums: &[M],
    matrix: &mut [Vec<M>],
    row: usize,
    col: usize,
    remaining: M,
    col_residual: &mut Vec<M>,
    a_max: usize,
    count: &mut usize,
    actions: &mut Vec<Action<O, A, M>>,
) {
    if *count >= a_max {
        return;
    }

    let cols = r_classes.len();

    if col == cols - 1 {
        if remaining <= col_residual[col] {
            // Save-and-restore rather than subtract-then-add-back: the residual returns to
            // exactly the value it held, with no second arithmetic step that could leave
            // the width. The `saturating_sub` is exact under the guard above.
            let saved = col_residual[col];
            matrix[row][col] = remaining;
            col_residual[col] = saved.saturating_sub(remaining);
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
            col_residual[col] = saved;
            matrix[row][col] = M::ZERO;
        }
        return;
    }

    let max_assign = remaining.min(col_residual[col]);
    let saved = col_residual[col];

    // Greedy-first: if l_classes[row] == r_classes[col] (diagonal), try the
    // maximum allocation first (it is usually optimal). Otherwise descend from max.
    let greedy = l_classes[row].0 == r_classes[col].0;
    if greedy {
        // Try max_assign first (the diagonal greedy), then the rest descending.
        for val in descending_upto(max_assign) {
            matrix[row][col] = val;
            col_residual[col] = saved.saturating_sub(val);
            distribute_row(
                op,
                l_classes,
                r_classes,
                row_sums,
                matrix,
                row,
                col + 1,
                remaining.saturating_sub(val),
                col_residual,
                a_max,
                count,
                actions,
            );
            col_residual[col] = saved;
            matrix[row][col] = M::ZERO;
            if *count >= a_max {
                return;
            }
        }
    } else {
        // Off-diagonal: try from max down (so smaller allocations come later).
        for val in descending_upto(max_assign) {
            matrix[row][col] = val;
            col_residual[col] = saved.saturating_sub(val);
            distribute_row(
                op,
                l_classes,
                r_classes,
                row_sums,
                matrix,
                row,
                col + 1,
                remaining.saturating_sub(val),
                col_residual,
                a_max,
                count,
                actions,
            );
            col_residual[col] = saved;
            matrix[row][col] = M::ZERO;
            if *count >= a_max {
                return;
            }
        }
    }
}

/// `max ..= 0` descending, at the multiplicity width.
///
/// A multiplicity is not an integer literal type, so `(0..=max).rev()` — which needs
/// `Step` — is unavailable; the range is walked at the surface width and narrowed back.
/// Every step is `<= max`, and `max` is a value of this width, so the narrowing cannot
/// fail. It is still spelled as a checked conversion with the reason attached rather than
/// an `as` cast, because that argument is what makes it safe and an `as` would hide it.
fn descending_upto<M: MultiplicityLike>(max: M) -> impl Iterator<Item = M> {
    (0..=max.to_u64()).rev().map(|v| {
        M::try_from_u64(v).expect("a value at or below `max` fits the width `max` came from")
    })
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
                assert_eq!(pair.count, Multiplicity::ONE);
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
        assert_eq!(acts[0].pairs[0].count, Multiplicity::ONE);
        assert_eq!(acts[0].pairs[1].count, Multiplicity::ONE);
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
