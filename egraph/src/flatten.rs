// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! `:flatten`: the flattened views of an n-ary node, enumerated for `Step::Flatten`.
//!
//! A rule tagged `:flatten` matches each n-ary atom against every *view* of its node
//! (`doc/goal-flatten-and-engine-completion.md`, decisions 2 and 3). For a node `n` of
//! operator `f`, each child class `X` contributes one of:
//!
//! - `X` itself, kept whole (always an option);
//! - for each `f` member `m` of `X`, the view of `m`'s children, recursively, unless `X`
//!   is already open on the path from `n`. The root's own class is not on the path, so a
//!   node can be opened once through its own class; the cut is what makes a cyclic class
//!   (`C ∋ f{a, C}`) finite.
//!
//! An opening must be needed (`doc/goal-canonical-flatten-views.md`, decision 2): each
//! view records the leaf groups of every opening tree that gives it ([`Demand`]), and a
//! match is kept when some tree's leaves each directly hold a class an item takes. The
//! decomposition or assembly reading the view applies that check, and the walk prunes a
//! leaf with no takeable element as it closes.
//!
//! "Member" is what the round's index holds: `by_repr[X] ∩ by_op[f]`, computed as the
//! class's bucket filtered by each node's round operator. Nothing is precomputed and
//! nothing stored changes.
//!
//! A view's multiplicities multiply through each opened member. The view is then
//! canonized by the one normalization of an n-ary child list (`crate::nary_canon`):
//! coalescing or deduplication, the identity drop, the nilpotent clamp, and
//! inverse-pair cancellation, with the operator's laws read through the view of the
//! graph the walk uses. A view whose canonical form is not a node (a single class or
//! the unit) is not matched, since the untagged engine never sees such a node
//! (`doc/goal-canonical-flatten-views.md`, decision 2). The distinct canonical views are
//! kept, in sorted order, so the continuation runs once per view.
//!
//! The walk is a depth-first search over an explicit stack, because its depth follows
//! the e-graph's nesting: a chain of 10^5 nested conjunctions is one root with 10^5
//! levels. The state is the pending tasks, the view built so far, the set of classes
//! open on the path, and a trail of undo records; each choice point records the trail
//! length to restore when it takes its next option.
//!
//! Three bounds keep a node's enumeration finite in time and memory. Each is counted
//! with checked arithmetic, and exceeding any of them skips the node with
//! [`OVER_BOUND`]; a view multiplicity the configured width cannot hold skips it with
//! [`MULT_OVERFLOW`]:
//! - [`MAX_VIEWS`] complete combinations (before deduplication, so it also bounds the
//!   distinct views);
//! - [`MAX_WORK`] options taken, which bounds the dead ends that produce no view;
//! - [`MAX_ELEMS`] stored view elements.

use crate::canon::{MSetCanon, VarCanon};
use crate::config::EGraphConfig;
use crate::egraph::EGraph;
use crate::index::VariantIndex;
use crate::literal::LitVal;
use crate::multiplicity::MultiplicityLike;

/// How a flattened node's children are read and its views normalized.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FlatKind {
    /// `:assoc` and the folds: a sequence, in order.
    Assoc,
    /// AC: a multiset.
    Ac,
    /// ACI: a set.
    Aci,
}

/// Complete combinations enumerated at one node.
pub const MAX_VIEWS: usize = 1 << 20;
/// Options taken at one node, views or dead ends.
pub const MAX_WORK: usize = 1 << 24;
/// View elements stored for one node.
pub const MAX_ELEMS: usize = 1 << 24;
/// The outcome of a node over any bound; the node is skipped and counted. The text
/// names the view bound only, but the outcome is reported for all three bounds.
pub const OVER_BOUND: &str = "more than 2^20 flattened views at one node";
/// A view whose multiplicity does not fit the configured width: a nested child's count
/// times its parent's, or the sum of two counts of one class. That view is not
/// representable, so it is skipped; the node's other views, its stored reading among
/// them, are still matched. The first such view is kept as a [`FlattenOverflow`] and
/// reported with its nesting.
pub const MULT_OVERFLOW: &str =
    "multiplicity overflow: a flattened count beyond the configured width";
/// The outcome of a node whose flattened view holds a count beyond 2^64, which the
/// sequence-pattern engine reads at the u64 surface width: the node is skipped and counted.
pub const BEYOND_U64: &str =
    "multiplicity overflow: a flattened count beyond 2^64 in a sequence pattern";

#[derive(Clone, Copy, Debug)]
enum Task<G, M> {
    /// Choose an option for this child class, with this multiplicity, directly under
    /// this opening instance (`None`: the root's own children).
    Child(G, M, Option<usize>),
    /// Every task an opened member pushed is done: the class leaves the path, and the
    /// opening instance is complete.
    Close(G, usize),
}

#[derive(Clone, Copy, Debug)]
enum Undo<G, M> {
    Popped(Task<G, M>),
    Closed(G),
    Opened(G),
    Viewed,
    Pushed(usize),
}

#[derive(Clone, Copy, Debug)]
struct Choice<G, M> {
    class: G,
    mult: M,
    /// The opening instance the class lies directly under.
    parent: Option<usize>,
    /// The class has an `f` member and is not open on the path.
    can_open: bool,
    kept: bool,
    /// The next position of `by_repr[class]` to try opening.
    cursor: usize,
    /// The trail length to restore before taking the next option.
    mark: usize,
}

/// The first view of one enumeration that does not fit the multiplicity width, kept to
/// report how the count arose: the node flattened, and the nesting that produced it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FlattenOverflow<G, M> {
    /// The node whose views were enumerated.
    pub node: G,
    pub cause: OverflowCause<G, M>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum OverflowCause<G, M> {
    /// Opening `class`, a child of count `count`, through its member `member`, multiplies
    /// that member's child `child`, of count `child_count`, past the width.
    Product {
        class: G,
        count: M,
        member: G,
        child: G,
        child_count: M,
    },
    /// The view holds `class` several times, with these counts, and their sum is past
    /// the width.
    Sum { class: G, counts: Vec<M> },
}

/// The enumerator's state, reused across nodes. The views of the last
/// [`enumerate`] are [`FlattenScratch::views`].
#[derive(Debug)]
pub struct FlattenScratch<G, M> {
    pending: Vec<Task<G, M>>,
    trail: Vec<Undo<G, M>>,
    choices: Vec<Choice<G, M>>,
    on_path: std::collections::HashSet<G>,
    view: Vec<(G, M)>,
    kids: Vec<(G, M)>,
    ids: Vec<G>,
    /// Per view element, the opening instance it lies directly under, and whether its
    /// class is takeable (see [`enumerate`]).
    view_parent: Vec<(Option<usize>, bool)>,
    /// Per opening instance, the instance it lies under, the instances opened directly
    /// under it, and its takeable direct elements.
    instances: Vec<(Option<usize>, usize, usize)>,
    elems: Vec<(G, M)>,
    /// One per raw view that canonizes to a node: its canonical span, and its leaf
    /// groups as a span of `groups`.
    recs: Vec<Rec>,
    /// Leaf groups, each a span of `group_elems`.
    groups: Vec<(usize, usize)>,
    group_elems: Vec<G>,
    /// The distinct views: a canonical span, and the span of `recs` (sorted) giving it.
    spans: Vec<(usize, usize, usize, usize)>,
    norm: Vec<(G, M)>,
    /// Views and openings of the last enumeration skipped for [`MULT_OVERFLOW`], and the
    /// first of them.
    overflows: usize,
    first_overflow: Option<FlattenOverflow<G, M>>,
    /// The node being enumerated, for [`FlattenOverflow::node`].
    root: Option<G>,
}

/// A raw view's record: its canonical content and its opening tree's leaf groups.
#[derive(Clone, Copy, Debug)]
struct Rec {
    start: usize,
    len: usize,
    gstart: usize,
    gcount: usize,
}

/// Which matches a view admits (`doc/goal-canonical-flatten-views.md`, decision 2): a
/// match is kept when, for some opening tree giving the view, every leaf of the tree
/// directly holds a class the items take. A view some tree gives with no opening admits
/// every match.
#[derive(Clone, Debug)]
pub struct Demand<G> {
    pub unconditional: bool,
    /// Per opening tree, its leaf groups.
    pub alts: Vec<Vec<Vec<G>>>,
}

impl<G> Default for Demand<G> {
    fn default() -> Self {
        Self {
            unconditional: true,
            alts: Vec::new(),
        }
    }
}

impl<G: PartialEq> Demand<G> {
    /// Whether a match taking the classes `taken` is kept.
    pub fn accepts(&self, taken: &[G]) -> bool {
        self.unconditional
            || self
                .alts
                .iter()
                .any(|leaves| leaves.iter().all(|g| g.iter().any(|c| taken.contains(c))))
    }
}

impl<G, M> Default for FlattenScratch<G, M> {
    fn default() -> Self {
        Self {
            pending: Vec::new(),
            trail: Vec::new(),
            choices: Vec::new(),
            on_path: std::collections::HashSet::new(),
            view: Vec::new(),
            kids: Vec::new(),
            ids: Vec::new(),
            view_parent: Vec::new(),
            instances: Vec::new(),
            elems: Vec::new(),
            recs: Vec::new(),
            groups: Vec::new(),
            group_elems: Vec::new(),
            spans: Vec::new(),
            norm: Vec::new(),
            overflows: 0,
            first_overflow: None,
            root: None,
        }
    }
}

impl<G: Copy + Ord + std::hash::Hash, M: MultiplicityLike> FlattenScratch<G, M> {
    pub fn new() -> Self {
        Self::default()
    }

    /// Views and openings of the last enumeration skipped because a count did not fit
    /// the multiplicity width ([`MULT_OVERFLOW`]).
    pub fn overflows(&self) -> usize {
        self.overflows
    }

    /// The first of them, with the nesting that produced the count.
    pub fn take_first_overflow(&mut self) -> Option<FlattenOverflow<G, M>> {
        self.first_overflow.take()
    }

    fn note_overflow(&mut self, cause: OverflowCause<G, M>) {
        self.overflows = self.overflows.saturating_add(1);
        if let (None, Some(node)) = (&self.first_overflow, self.root) {
            self.first_overflow = Some(FlattenOverflow { node, cause });
        }
    }

    /// The number of distinct views of the last enumeration.
    pub fn len(&self) -> usize {
        self.spans.len()
    }

    pub fn is_empty(&self) -> bool {
        self.spans.is_empty()
    }

    /// The `i`-th distinct view, normalized.
    pub fn view(&self, i: usize) -> &[(G, M)] {
        let (s, n, _, _) = self.spans[i];
        &self.elems[s..s + n]
    }

    /// The `i`-th distinct view's demand, into `out`.
    pub fn demand_into(&self, i: usize, out: &mut Demand<G>) {
        let (_, _, rs, rn) = self.spans[i];
        out.alts.clear();
        out.unconditional = false;
        for r in &self.recs[rs..rs + rn] {
            if r.gcount == 0 {
                out.unconditional = true;
                out.alts.clear();
                return;
            }
            let leaves = self.groups[r.gstart..r.gstart + r.gcount]
                .iter()
                .map(|&(s, n)| self.group_elems[s..s + n].to_vec())
                .collect();
            out.alts.push(leaves);
        }
    }

    fn reset(&mut self) {
        self.pending.clear();
        self.trail.clear();
        self.choices.clear();
        self.on_path.clear();
        self.view.clear();
        self.view_parent.clear();
        self.instances.clear();
        self.elems.clear();
        self.recs.clear();
        self.groups.clear();
        self.group_elems.clear();
        self.spans.clear();
        self.overflows = 0;
        self.first_overflow = None;
        self.root = None;
    }

    /// Canonize the complete view (`crate::nary_canon::normalize`) and record it when
    /// it forms a node; a view naming a class or the unit is dropped.
    fn record<O: Copy>(
        &mut self,
        laws: &crate::nary_canon::NaryLaws<G, O>,
        inverse_class: impl Fn(O, G) -> Option<G>,
    ) -> Result<(), &'static str> {
        use crate::nary_canon::Normal;
        self.norm.clear();
        self.norm.extend_from_slice(&self.view);
        match crate::nary_canon::normalize(laws, &mut self.norm, inverse_class) {
            Normal::Node => {}
            Normal::Unit | Normal::Single(_) | Normal::Empty => return Ok(()),
            Normal::Overflow => {
                // A class whose summed count is past the width: this view is skipped.
                let mut by_class: Vec<(G, M)> = self.view.clone();
                by_class.sort_by_key(|e| e.0);
                let mut cause = None;
                let mut i = 0;
                while i < by_class.len() && cause.is_none() {
                    let c = by_class[i].0;
                    let counts: Vec<M> = by_class[i..]
                        .iter()
                        .take_while(|e| e.0 == c)
                        .map(|e| e.1)
                        .collect();
                    i += counts.len();
                    let fits = counts
                        .iter()
                        .try_fold(M::ZERO, |a, &k| a.checked_add(k))
                        .is_some();
                    if !fits {
                        cause = Some(OverflowCause::Sum { class: c, counts });
                    }
                }
                if let Some(cause) = cause {
                    self.note_overflow(cause);
                } else {
                    // The laws (a clamp, a cancellation) overflowed past the sums.
                    self.overflows = self.overflows.saturating_add(1);
                }
                return Ok(());
            }
        }
        let start = self.elems.len();
        let total = start
            .checked_add(self.norm.len())
            .and_then(|t| t.checked_add(self.group_elems.len()))
            .and_then(|t| t.checked_add(self.view.len()))
            .ok_or(OVER_BOUND)?;
        if total > MAX_ELEMS {
            return Err(OVER_BOUND);
        }
        self.elems.extend_from_slice(&self.norm);
        // The leaf groups: each opened instance no other instance lies under, with the
        // (raw, canonical-class) elements directly under it.
        let gstart = self.groups.len();
        for i in 0..self.instances.len() {
            if self.instances[i].1 > 0 {
                continue;
            }
            let es = self.group_elems.len();
            for (e, p) in self.view.iter().zip(&self.view_parent) {
                if p.0 == Some(i) {
                    self.group_elems.push(e.0);
                }
            }
            self.groups.push((es, self.group_elems.len() - es));
        }
        self.recs.push(Rec {
            start,
            len: self.norm.len(),
            gstart,
            gcount: self.groups.len() - gstart,
        });
        Ok(())
    }

    /// Group the records by canonical content: one span per distinct view, in sorted
    /// order, with the records (opening trees) that give it.
    fn dedup(&mut self) {
        let elems = &self.elems;
        self.recs
            .sort_by(|a, b| elems[a.start..a.start + a.len].cmp(&elems[b.start..b.start + b.len]));
        self.spans.clear();
        let mut i = 0usize;
        while i < self.recs.len() {
            let r = self.recs[i];
            let mut j = i + 1;
            while j < self.recs.len() {
                let q = self.recs[j];
                if elems[q.start..q.start + q.len] != elems[r.start..r.start + r.len] {
                    break;
                }
                j += 1;
            }
            self.spans.push((r.start, r.len, i, j - i));
            i = j;
        }
    }

    fn undo_to(&mut self, mark: usize) {
        while self.trail.len() > mark {
            let Some(u) = self.trail.pop() else { break };
            match u {
                Undo::Popped(t) => self.pending.push(t),
                Undo::Closed(x) => {
                    self.on_path.insert(x);
                }
                Undo::Opened(x) => {
                    self.on_path.remove(&x);
                    if let Some((Some(p), _, _)) = self.instances.pop() {
                        self.instances[p].1 = self.instances[p].1.saturating_sub(1);
                    }
                }
                Undo::Viewed => {
                    self.view.pop();
                    if let Some((Some(p), true)) = self.view_parent.pop() {
                        self.instances[p].2 = self.instances[p].2.saturating_sub(1);
                    }
                }
                Undo::Pushed(n) => {
                    let keep = self.pending.len().saturating_sub(n);
                    self.pending.truncate(keep);
                }
            }
        }
    }
}

/// What the enumerator reads of an e-graph: a class's members, a node's operator, and a
/// node's children, every class canonical in one consistent view of the graph. The
/// matcher reads the round's snapshot ([`Snapshot`]); route 1 of the sequence rules
/// reads the live graph (`collection.rs`). Both walk with [`enumerate`], so both see
/// the same views of the same graph.
pub trait Members<G, O, M> {
    /// The matchable members of `class`.
    fn members(&self, class: G) -> &[G];
    /// `node`'s operator, or `None` if `node` is not a matchable member.
    fn op(&self, node: G) -> Option<O>;
    /// `node`'s children with their multiplicities (1 except under AC), canonical,
    /// into `kids`; `ids` is scratch.
    fn children(&self, node: G, kind: FlatKind, kids: &mut Vec<(G, M)>, ids: &mut Vec<G>);
    /// `op`'s laws, with its unit resolved to a class of this view.
    fn laws(&self, op: O) -> crate::nary_canon::NaryLaws<G, O>;
    /// The class of the node `inv(x)`, if this view holds one.
    fn inverse_class(&self, inv: O, x: G) -> Option<G>;
}

/// The round's snapshot: members are `by_repr` buckets, operators the round's, and
/// children canonical by the round's representatives (`ematch::round_canon`).
pub struct Snapshot<'a, 'i, Cfg: EGraphConfig, L: LitVal, const TRACK: bool, const PROOFS: bool>
where
    Cfg::Policy: crate::config::StorePolicy<Cfg, TRACK>,
{
    pub eg: &'a EGraph<Cfg, L, TRACK, PROOFS>,
    pub index: &'a VariantIndex<'i, Cfg>,
}

impl<Cfg, L, const TRACK: bool, const PROOFS: bool> Members<Cfg::G, Cfg::O, Cfg::M>
    for Snapshot<'_, '_, Cfg, L, TRACK, PROOFS>
where
    Cfg: EGraphConfig,
    L: LitVal,
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
    Cfg::Policy: crate::config::StorePolicy<Cfg, TRACK>,
{
    fn members(&self, class: Cfg::G) -> &[Cfg::G] {
        self.index.full.nodes_by_repr(class)
    }

    fn op(&self, node: Cfg::G) -> Option<Cfg::O> {
        self.index.full.round_op(node)
    }

    fn children(
        &self,
        node: Cfg::G,
        kind: FlatKind,
        kids: &mut Vec<(Cfg::G, Cfg::M)>,
        ids: &mut Vec<Cfg::G>,
    ) {
        read_children(self.eg, node, kind, kids, ids);
        for k in kids.iter_mut() {
            k.0 = crate::ematch::round_canon(self.index, self.eg, k.0);
        }
    }

    fn laws(&self, op: Cfg::O) -> crate::nary_canon::NaryLaws<Cfg::G, Cfg::O> {
        let mut laws = self.eg.nary_laws(op);
        laws.unit = self
            .eg
            .unit_node(op)
            .map(|u| crate::ematch::round_canon(self.index, self.eg, u));
        laws
    }

    /// `by_op[inv] ∩ by_child_pos[x, 0]`: the snapshot's `inv` nodes over `x`.
    fn inverse_class(&self, inv: Cfg::O, x: Cfg::G) -> Option<Cfg::G> {
        use crate::containers::IndexLike;
        let full = self.index.full;
        full.nodes_by_child_pos(x, Cfg::Index::try_from_usize(0)?)
            .iter()
            .find(|&&n| full.round_op(n) == Some(inv))
            .map(|&n| crate::ematch::round_canon(self.index, self.eg, n))
    }
}

/// `node`'s stored children by kind, not canonicalized.
pub fn read_children<Cfg, L, const TRACK: bool, const PROOFS: bool>(
    eg: &EGraph<Cfg, L, TRACK, PROOFS>,
    node: Cfg::G,
    kind: FlatKind,
    kids: &mut Vec<(Cfg::G, Cfg::M)>,
    ids: &mut Vec<Cfg::G>,
) where
    Cfg: EGraphConfig,
    L: LitVal,
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
    Cfg::Policy: crate::config::StorePolicy<Cfg, TRACK>,
{
    kids.clear();
    match kind {
        FlatKind::Assoc => {
            eg.seq_children(node, ids);
            kids.extend(ids.iter().map(|&c| (c, Cfg::M::ONE)));
        }
        FlatKind::Aci => {
            eg.set_children(node, ids);
            kids.extend(ids.iter().map(|&c| (c, Cfg::M::ONE)));
        }
        FlatKind::Ac => eg.mset_children(node, kids),
    }
}

/// `k · j`, or [`MULT_OVERFLOW`] when the product does not fit the multiplicity width.
fn times<M: MultiplicityLike>(k: M, j: M) -> Result<M, &'static str> {
    k.checked_mul(j).ok_or(MULT_OVERFLOW)
}

/// Every distinct flattened view of `node`, an `op` node of `kind`, into `s`. On
/// `Err(OVER_BOUND)` the node is to be skipped; `s` is left reusable either way.
///
/// `takeable(c)` says whether an item could take an element of class `c`. It prunes
/// the walk by the demand rule (`doc/goal-canonical-flatten-views.md`, decision 2): an
/// opening instance that completes with no instance opened under it is a leaf, and a
/// leaf none of whose direct elements is takeable makes no match, so the branch is
/// abandoned there. Counters per instance make the check constant-time, which keeps a
/// chain of 10^5 levels linear when one level's element is the only takeable one.
pub fn enumerate<G, O, M, Src>(
    src: &Src,
    node: G,
    op: O,
    kind: FlatKind,
    takeable: impl Fn(G) -> bool,
    s: &mut FlattenScratch<G, M>,
) -> Result<(), &'static str>
where
    G: Copy + Ord + std::hash::Hash,
    O: Copy + PartialEq,
    M: MultiplicityLike,
    Src: Members<G, O, M> + ?Sized,
{
    s.reset();
    s.root = Some(node);
    let laws = src.laws(op);
    src.children(node, kind, &mut s.kids, &mut s.ids);
    for i in (0..s.kids.len()).rev() {
        let (c, m) = s.kids[i];
        s.pending.push(Task::Child(c, m, None));
    }
    let mut leaves = 0usize;
    let mut work = 0usize;
    loop {
        match s.pending.pop() {
            None => {
                leaves = leaves.checked_add(1).ok_or(OVER_BOUND)?;
                if leaves > MAX_VIEWS {
                    return Err(OVER_BOUND);
                }
                s.record(&laws, |inv, x| src.inverse_class(inv, x))?;
                if !backtrack(src, op, kind, &takeable, s, &mut work)? {
                    break;
                }
            }
            Some(t) => {
                s.trail.push(Undo::Popped(t));
                match t {
                    Task::Close(x, inst) => {
                        s.on_path.remove(&x);
                        s.trail.push(Undo::Closed(x));
                        // A leaf with no takeable element: no match from here.
                        let (_, opened, hits) = s.instances[inst];
                        if opened == 0
                            && hits == 0
                            && !backtrack(src, op, kind, &takeable, s, &mut work)?
                        {
                            break;
                        }
                    }
                    Task::Child(x, k, parent) => {
                        let same = src.members(x).iter().any(|&m| src.op(m) == Some(op));
                        s.choices.push(Choice {
                            class: x,
                            mult: k,
                            parent,
                            can_open: same && !s.on_path.contains(&x),
                            kept: false,
                            cursor: 0,
                            mark: s.trail.len(),
                        });
                        if !advance(src, op, kind, &takeable, s, &mut work)?
                            && !backtrack(src, op, kind, &takeable, s, &mut work)?
                        {
                            break;
                        }
                    }
                }
            }
        }
    }
    s.dedup();
    Ok(())
}

/// Take the top choice's next option. `Ok(false)` when it has none left.
fn advance<G, O, M, Src>(
    src: &Src,
    op: O,
    kind: FlatKind,
    takeable: &impl Fn(G) -> bool,
    s: &mut FlattenScratch<G, M>,
    work: &mut usize,
) -> Result<bool, &'static str>
where
    G: Copy + Ord + std::hash::Hash,
    O: Copy + PartialEq,
    M: MultiplicityLike,
    Src: Members<G, O, M> + ?Sized,
{
    let Some(c) = s.choices.last_mut() else {
        return Ok(false);
    };
    *work = work.checked_add(1).ok_or(OVER_BOUND)?;
    if *work > MAX_WORK {
        return Err(OVER_BOUND);
    }
    // Keeping the class whole is always an option: an opening that no item needs
    // makes no match (decision 2), so the kept view must exist for the refolded match.
    if !c.kept {
        c.kept = true;
        let hit = c.parent.is_some() && takeable(c.class);
        if let (Some(p), true) = (c.parent, hit) {
            s.instances[p].2 = s.instances[p].2.checked_add(1).ok_or(OVER_BOUND)?;
        }
        s.view.push((c.class, c.mult));
        s.view_parent.push((c.parent, hit));
        s.trail.push(Undo::Viewed);
        return Ok(true);
    }
    if !c.can_open {
        return Ok(false);
    }
    let members = src.members(c.class);
    while c.cursor < members.len() {
        let m = members[c.cursor];
        c.cursor += 1;
        if src.op(m) != Some(op) {
            continue;
        }
        let (x, k) = (c.class, c.mult);
        // Opening `m` multiplies each of its children's counts by `k`. A product past the
        // width makes every view through this opening unrepresentable: it is skipped, and
        // the class can still be kept whole or opened through another member.
        src.children(m, kind, &mut s.kids, &mut s.ids);
        if let Some(&(y, j)) = s.kids.iter().find(|&&(_, j)| k.checked_mul(j).is_none()) {
            // Field by field: `c` borrows `s.choices` for the whole loop.
            s.overflows = s.overflows.saturating_add(1);
            if let (None, Some(node)) = (&s.first_overflow, s.root) {
                s.first_overflow = Some(FlattenOverflow {
                    node,
                    cause: OverflowCause::Product {
                        class: x,
                        count: k,
                        member: m,
                        child: y,
                        child_count: j,
                    },
                });
            }
            continue;
        }
        let inst = s.instances.len();
        if let Some(p) = c.parent {
            s.instances[p].1 = s.instances[p].1.checked_add(1).ok_or(OVER_BOUND)?;
        }
        s.instances.push((c.parent, 0, 0));
        s.on_path.insert(x);
        s.trail.push(Undo::Opened(x));
        let base = s.pending.len();
        s.pending.push(Task::Close(x, inst));
        for i in (0..s.kids.len()).rev() {
            let (y, j) = s.kids[i];
            s.pending.push(Task::Child(y, times(k, j)?, Some(inst)));
        }
        s.trail.push(Undo::Pushed(s.pending.len() - base));
        return Ok(true);
    }
    Ok(false)
}

/// Undo to the most recent choice with an option left and take it. `Ok(false)` when
/// every choice is exhausted, which ends the enumeration.
fn backtrack<G, O, M, Src>(
    src: &Src,
    op: O,
    kind: FlatKind,
    takeable: &impl Fn(G) -> bool,
    s: &mut FlattenScratch<G, M>,
    work: &mut usize,
) -> Result<bool, &'static str>
where
    G: Copy + Ord + std::hash::Hash,
    O: Copy + PartialEq,
    M: MultiplicityLike,
    Src: Members<G, O, M> + ?Sized,
{
    loop {
        let Some(mark) = s.choices.last().map(|c| c.mark) else {
            return Ok(false);
        };
        s.undo_to(mark);
        if advance(src, op, kind, takeable, s, work)? {
            return Ok(true);
        }
        s.choices.pop();
    }
}

impl FlatKind {
    /// The kind of a sequence rule's root (`seq_collect::Spec`): `:assoc` and folds,
    /// AC, or else ACI.
    pub fn of(assoc: bool, ac: bool) -> FlatKind {
        if assoc {
            FlatKind::Assoc
        } else if ac {
            FlatKind::Ac
        } else {
            FlatKind::Aci
        }
    }
}

/// The distinct views of `node` as the sequence assembly reads children: classes with
/// 64-bit multiplicities (task 4 of `doc/goal-flatten-and-engine-completion.md`), each
/// with its demand.
#[allow(clippy::type_complexity)]
pub fn views_u64<G, O, M, Src>(
    src: &Src,
    node: G,
    op: O,
    kind: FlatKind,
) -> Result<Vec<(Vec<(G, u64)>, Demand<G>)>, &'static str>
where
    G: Copy + Ord + std::hash::Hash,
    O: Copy + PartialEq,
    M: MultiplicityLike,
    Src: Members<G, O, M> + ?Sized,
{
    let mut s = FlattenScratch::new();
    // Every element is takeable here: which ones a filter takes is the assembly's.
    enumerate(src, node, op, kind, |_| true, &mut s)?;
    // The sequence assembly reports per node, so a view past the width skips the node,
    // which `PassReport::skipped_nodes` counts and the run warns about. The ordinary
    // matcher instead skips only that view and reports its nesting (`apply.rs`).
    if s.overflows() > 0 {
        return Err(MULT_OVERFLOW);
    }
    (0..s.len())
        .map(|i| {
            let mut d = Demand::default();
            s.demand_into(i, &mut d);
            let view = s
                .view(i)
                .iter()
                .map(|&(c, m)| m.to_u64().map(|m| (c, m)).ok_or(BEYOND_U64))
                .collect::<Result<Vec<_>, _>>()?;
            Ok((view, d))
        })
        .collect()
}
