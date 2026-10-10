// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Result-term pool (§4.4): hash-consed arena of anti-unifier terms.
//!
//! Terms are `(TermOp, children)` where children are spans into a shared pool.
//! `Variants` nodes have two children (left, right projections). Size counts 1
//! per ordinary node and 0 for each `Variants` node (its children are counted).

use crate::canon::{MSetCanon, VarCanon};
use crate::config::{AuIds, EGraphConfig};
use crate::containers::group::Member;
use crate::containers::{AppendOnlyVec, DenseId, IndexLike, ShrinkPolicy, SpUniqueMap};
use crate::literal::LitVal;

use super::egraph_api::{AuSnapshot, ClassOf};
use super::{AuIds31, Span};

crate::containers::define_id31! {
    /// Index of a term in the hash-consed term pool.
    pub struct TermId / StoredTermId, "t";
}

/// The operator of a term node.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum TermOp<O: DenseId, V: DenseId> {
    /// An e-graph operator (from the original e-graph).
    EGraph(O),
    /// A literal value.
    Literal(O, V),
    /// A `Variants(left, right)` node: where left and right differ.
    Variants,
}

/// How a term's children are ordered and counted, from its operator's node kind
/// ([`crate::au::egraph_api::AuSnapshot::child_form`]).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ChildForm {
    /// Positional children (plain, sequence): kept as given.
    Ordered,
    /// Unordered children, each counted once (`:comm` pair, ACI): sorted into the
    /// canonical structural order.
    Commutative,
    /// An AC multiset: sorted, and equal children merged into one entry whose count is
    /// the sum, so a child of multiplicity k is one entry.
    Multiset,
}

/// A term without `Variants` nodes, owned outside its pool: each child with its
/// multiplicity, an AC child of count k being one entry. What a projection is read out
/// as, so the pool and the snapshot can be dropped before the term is rebuilt in the
/// e-graph ([`materialize_owned`]).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum OwnedTerm<O, V> {
    App(O, Vec<(OwnedTerm<O, V>, u64)>),
    Lit(O, V),
}

/// Build an owned term in `eg`, children first, with an explicit frame stack: an AC
/// child of count k is one counted child ([`EGraph::add_with_counts`]). `Err` when a
/// count does not fit the configuration.
///
/// [`EGraph::add_with_counts`]: crate::egraph::EGraph::add_with_counts
pub fn materialize_owned<Cfg: EGraphConfig, L: LitVal, const T: bool, const P: bool>(
    eg: &mut crate::egraph::EGraph<Cfg, L, T, P>,
    term: &OwnedTerm<Cfg::O, Cfg::V>,
) -> Result<Cfg::G, String>
where
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
    Cfg::Policy: crate::config::StorePolicy<Cfg, T>,
{
    struct Frame<'t, O, V, G> {
        op: O,
        children: &'t [(OwnedTerm<O, V>, u64)],
        cursor: usize,
        out: Vec<(G, u64)>,
    }
    let mut stack: Vec<Frame<'_, Cfg::O, Cfg::V, Cfg::G>> = Vec::new();
    let mut pending = term;
    loop {
        let mut done = None;
        match pending {
            OwnedTerm::Lit(op, value) => done = Some(eg.add_lit(*op, *value)),
            OwnedTerm::App(op, children) => stack.push(Frame {
                op: *op,
                children,
                cursor: 0,
                out: Vec::with_capacity(children.len()),
            }),
        }
        loop {
            if let Some(id) = done.take() {
                let Some(parent) = stack.last_mut() else {
                    return Ok(id);
                };
                let count = parent.children[parent.cursor].1;
                parent.out.push((id, count));
                parent.cursor += 1;
            }
            let top = stack.last_mut().expect("materialize stack is non-empty");
            if top.cursor < top.children.len() {
                pending = &top.children[top.cursor].0;
                break;
            }
            let frame = stack.pop().expect("materialize stack is non-empty");
            let counts: Vec<Option<num_bigint::BigUint>> = frame
                .out
                .iter()
                .map(|&(_, k)| (k != 1).then(|| num_bigint::BigUint::from(k)))
                .collect();
            let kids: Vec<(Cfg::G, Option<&num_bigint::BigUint>)> = frame
                .out
                .iter()
                .zip(&counts)
                .map(|(&(g, _), k)| (g, k.as_ref()))
                .collect();
            done = Some(eg.add_with_counts(frame.op, &kids)?);
        }
    }
}

/// Hash-consed term pool. Structurally equal terms get the same term id.
/// All fields are semi-persistent (AppendOnlyVec/SpMap); mark/restore truncates.
/// The id family `A` defaults to the 31-bit family; a Config64 session
/// instantiates `TermPool<O, V, AuIds64>` through `Cfg::Au`.
///
/// Every pool here is addressed by an id whose `Index` is `A::Index`, so that word —
/// not `usize` — is the index type: the five term-indexed columns are addressed by
/// `A::Term`, `child_pool` by `A::TermChild`, and `by_structure`'s log positions are
/// what `A::Term`s are minted from. Pinning them keeps each saved frame length and
/// each hash-index value at the configured width instead of 8 bytes.
pub struct TermPool<O: DenseId, V: DenseId, A: AuIds = AuIds31> {
    ops: AppendOnlyVec<TermOp<O, V>, A::Index>,
    child_spans: AppendOnlyVec<Span<A::TermChild>, A::Index>,
    child_pool: AppendOnlyVec<A::Term, A::Index>,
    /// Each child's multiplicity, parallel to `child_pool`: 1 except under an AC
    /// operator, whose child of multiplicity k is one entry with count k.
    child_counts: AppendOnlyVec<u64, A::Index>,
    sizes: AppendOnlyVec<u32, A::Index>,
    vmasses: AppendOnlyVec<u32, A::Index>,
    by_structure: SpUniqueMap<(TermOp<O, V>, Vec<(A::Term, u64)>), A::Term, A::Index>,
    /// Memoized [`build_best_term`] result per snapshot class.
    ///
    /// A class's minimal member is fixed by the snapshot, so its extracted term
    /// is a pure function of the class id; caching it makes `build_best_term`
    /// amortized O(1) per class after the first build instead of re-walking the
    /// member tree on every call (quadratic on deep chains). The cache lives in
    /// the same semi-persistent storage as the term columns and is truncated by
    /// the same token bundle, so a surviving entry always names a surviving
    /// term: the entry was appended after its term was interned, and restore
    /// truncates both logs at the same mark.
    ///
    /// Class ids are snapshot-relative, so the cache assumes every
    /// `build_best_term` call on this pool uses the same snapshot. That holds
    /// by construction: every pool is created next to one snapshot
    /// (`session.rs`, `exact.rs`, `mcgs.rs`) and never outlives it.
    best_terms: SpUniqueMap<A::Class, A::Term, A::Index>,
}

impl<O: DenseId + core::hash::Hash, V: DenseId + core::hash::Hash, A: AuIds> TermPool<O, V, A> {
    pub fn new() -> Self {
        TermPool {
            ops: AppendOnlyVec::new(),
            child_spans: AppendOnlyVec::new(),
            child_pool: AppendOnlyVec::new(),
            child_counts: AppendOnlyVec::new(),
            sizes: AppendOnlyVec::new(),
            vmasses: AppendOnlyVec::new(),
            by_structure: SpUniqueMap::new(),
            best_terms: SpUniqueMap::new(),
        }
    }

    /// Number of interned terms, in the configured index word.
    ///
    /// A term count is a position count — the next term interns at exactly this
    /// index — so it is reported in `A::Index` rather than widened to `usize`.
    pub fn len(&self) -> A::Index {
        self.ops.len()
    }

    pub fn is_empty(&self) -> bool {
        self.ops.is_empty()
    }

    /// Intern a term whose children each count once. Returns the existing id if a
    /// structurally equal term exists.
    pub fn intern(&mut self, op: TermOp<O, V>, children: &[A::Term]) -> A::Term {
        let counted: Vec<(A::Term, u64)> = children.iter().map(|&c| (c, 1)).collect();
        self.intern_counted(op, &counted)
    }

    /// Intern a term from `(child, multiplicity)` entries, as given (no sorting, no
    /// merging). Returns the existing id if a structurally equal term exists.
    pub fn intern_counted(&mut self, op: TermOp<O, V>, children: &[(A::Term, u64)]) -> A::Term {
        // One hash of the structural key (an operator plus a child vector, so a
        // heap key) whether the term is new or not: the map decides membership
        // and claims the id in the same probe, and the columns below are only
        // extended when the id is fresh.
        let key = (op.clone(), children.to_vec());
        let id: A::Term = crate::id::id_at_index(self.ops.len());
        let (found, fresh) = self
            .by_structure
            .try_intern(key, id)
            .expect("AU arena sized by its index word");
        if !fresh {
            return *self.by_structure.get_val(found);
        }

        let start = self.child_pool.len().as_usize();
        for &(c, k) in children {
            self.child_pool
                .try_push(c)
                .expect("AU arena sized by its index word");
            self.child_counts
                .try_push(k)
                .expect("AU arena sized by its index word");
        }

        // Expanded sizes saturate. They do not wrap, and they do not panic.
        //
        // A term is a hash-consed DAG, so the *expanded* size these fields count is
        // exponential in the DAG's depth: a chain of 32 binary nodes already names
        // 2^32 leaves out of 33 stored rows. `u32` is therefore reachable from a
        // pool small enough to build, and no wider word makes it unreachable — `u64`
        // only moves the chain to depth 64. The width is a storage choice; the
        // arithmetic has to be total either way.
        //
        // Saturation rather than a panic because these two fields are read only as
        // the `quality` ranking key, where lower is better. A term too large to
        // count belongs at the *worst* end of that order, which is exactly where
        // `u32::MAX` puts it; two such terms tie, and a tie between candidates
        // nobody can materialize costs nothing. Wrapping put them at the *best*
        // end — a 2^32-node generalization scored 0 and was selected as the minimal
        // one. That was silent: `Iterator::sum` on `u32` panics in debug and wraps
        // in release, so it only ever misbehaved in the configuration that ships.
        //
        // `AuSnapshot::best_size` takes the same view from the other side: it
        // reserves `u32::MAX` as an explicit "no finite representative" sentinel and
        // rejects any total that reaches it (`egraph_api.rs`).
        // A child of multiplicity k counts k times: the expanded size of the term.
        let times = |k: u64, x: u32| x.saturating_mul(u32::try_from(k).unwrap_or(u32::MAX));
        let child_size_sum = children.iter().fold(0u32, |acc, &(c, k)| {
            acc.saturating_add(times(k, *self.sizes.get(c.to_index())))
        });
        let (size, vmass) = match &op {
            TermOp::Variants => (child_size_sum, child_size_sum),
            _ => {
                let vm = children.iter().fold(0u32, |acc, &(c, k)| {
                    acc.saturating_add(times(k, *self.vmasses.get(c.to_index())))
                });
                (child_size_sum.saturating_add(1), vm)
            }
        };

        self.ops
            .try_push(op)
            .expect("AU arena sized by its index word");
        self.child_spans
            .try_push(Span::new(start, children.len()))
            .expect("AU arena sized by its index word");
        self.sizes
            .try_push(size)
            .expect("AU arena sized by its index word");
        self.vmasses
            .try_push(vmass)
            .expect("AU arena sized by its index word");
        id
    }

    /// Intern the result term of one action from `(child, count)` entries.
    ///
    /// `form` is the operator's [`ChildForm`]. Ordered children keep the action's
    /// positional order, which is their meaning. Unordered ones are sorted into the
    /// canonical structural order, so the same result interns identically whatever the
    /// construction order. An AC multiset also merges equal children into one entry with
    /// the summed count: a child of multiplicity k is one entry, never k copies.
    ///
    /// Counts arrive at the *surface* width. Two callers feed this: the structural path,
    /// whose counts are [`EGraphConfig::M`] multiplicities, and the transport path, whose
    /// counts are flow cells at the solver's own narrower capacity. A merged sum
    /// saturates at `u64::MAX`, which no stored multiplicity reaches.
    ///
    /// [`EGraphConfig::M`]: crate::config::EGraphConfig::M
    pub fn intern_action_result(
        &mut self,
        op: TermOp<O, V>,
        children_with_counts: &[(A::Term, u64)],
        form: ChildForm,
    ) -> A::Term {
        let mut kids: Vec<(A::Term, u64)> = children_with_counts
            .iter()
            .copied()
            .filter(|&(_, k)| k > 0)
            .collect();
        if form != ChildForm::Ordered {
            kids.sort_by(|&(a, _), &(b, _)| self.structural_cmp(a, b));
        }
        if form == ChildForm::Multiset {
            kids.dedup_by(|later, earlier| {
                let same = later.0 == earlier.0;
                if same {
                    // Bounded by one node's total, which the snapshot gate keeps within
                    // u64 (`AuError::CountTooWide`).
                    earlier.1 = earlier
                        .1
                        .checked_add(later.1)
                        .expect("merged counts are bounded by a node's total");
                }
                same
            });
        }
        self.intern_counted(op, &kids)
    }

    /// Total structural order on terms, independent of allocation order:
    /// operator variant rank, then operator/value ids, then arity, then children
    /// lexicographically. Equal ids are structurally equal (hash-consing), so this
    /// returns `Equal` only for identical ids.
    ///
    /// Iterative (explicit work stack): the first non-`Equal` comparison in
    /// depth-first, left-to-right order decides, exactly like the recursive
    /// lexicographic definition. Depth is heap-bounded, not call-stack-bounded.
    pub fn structural_cmp(&self, a: A::Term, b: A::Term) -> core::cmp::Ordering {
        use core::cmp::Ordering;
        fn rank<O: DenseId, V: DenseId>(op: &TermOp<O, V>) -> u8 {
            match op {
                TermOp::EGraph(_) => 0,
                TermOp::Literal(_, _) => 1,
                TermOp::Variants => 2,
            }
        }
        let mut stack: Vec<(A::Term, A::Term)> = vec![(a, b)];
        while let Some((a, b)) = stack.pop() {
            if a == b {
                continue;
            }
            let (oa, ob) = (self.op(a), self.op(b));
            let ord = rank(oa).cmp(&rank(ob));
            if ord != Ordering::Equal {
                return ord;
            }
            let ord = match (oa, ob) {
                (TermOp::EGraph(x), TermOp::EGraph(y)) => x.to_usize().cmp(&y.to_usize()),
                (TermOp::Literal(x, v), TermOp::Literal(y, w)) => x
                    .to_usize()
                    .cmp(&y.to_usize())
                    .then(v.to_usize().cmp(&w.to_usize())),
                _ => Ordering::Equal,
            };
            if ord != Ordering::Equal {
                return ord;
            }
            let (ca, cb) = (self.children(a), self.children(b));
            let ord = ca
                .len()
                .cmp(&cb.len())
                .then_with(|| self.counts(a).cmp(self.counts(b)));
            if ord != Ordering::Equal {
                return ord;
            }
            // Push child pairs in reverse so the leftmost pair is compared first.
            for (&x, &y) in ca.iter().zip(cb.iter()).rev() {
                stack.push((x, y));
            }
        }
        Ordering::Equal
    }

    /// Get the size of a term. Saturates at `u32::MAX` for terms whose expanded
    /// size exceeds the counter (see `intern`); such a term is ranked worst, never
    /// best.
    #[inline]
    pub fn size(&self, id: A::Term) -> u32 {
        *self.sizes.get(id.to_index())
    }

    /// Get the variant mass of a term: concrete nodes under `Variants` nodes.
    /// `size - variant_mass` is the backbone (shared structure) size.
    #[inline]
    pub fn variant_mass(&self, id: A::Term) -> u32 {
        *self.vmasses.get(id.to_index())
    }

    /// The lexicographic quality key `(size, variant_mass)`. Lower is better:
    /// primary objective is minimum size; at equal size the term with less
    /// variant mass has more backbone (more factored structure) and wins.
    ///
    /// Both components saturate (`intern`), so the order is total and monotone but
    /// loses discrimination among terms too large to count — they all tie at the
    /// bottom. That is the intended degradation: the alternative, wrapping, inverted
    /// the comparison and made the largest term look like the best one.
    #[inline]
    pub fn quality(&self, id: A::Term) -> (u32, u32) {
        (
            *self.sizes.get(id.to_index()),
            *self.vmasses.get(id.to_index()),
        )
    }

    /// Get the operator of a term.
    #[inline]
    pub fn op(&self, id: A::Term) -> &TermOp<O, V> {
        self.ops.get(id.to_index())
    }

    /// The multiplicity of each child of a term, parallel to [`Self::children`].
    #[inline]
    pub fn counts(&self, id: A::Term) -> &[u64] {
        let span = *self.child_spans.get(id.to_index());
        let (start, len) = (span.start_usize(), span.len_usize());
        &self.child_counts.as_slice()[start..start + len]
    }

    /// Get the children of a term: one entry per distinct AC child, whose multiplicity
    /// is in [`Self::counts`].
    #[inline]
    pub fn children(&self, id: A::Term) -> &[A::Term] {
        let span = *self.child_spans.get(id.to_index());
        let (start, len) = (span.start_usize(), span.len_usize());
        // Verified `as_slice()` instead of `from_raw_parts` — see the counterpart in
        // `space.rs::ContextStore::get`. The children of a term are pushed
        // consecutively when it is interned, so the span is in bounds.
        &self.child_pool.as_slice()[start..start + len]
    }

    /// The memoized minimal term for a snapshot class, if one was built since
    /// the last surviving mark (see `best_terms`).
    #[inline]
    fn cached_best_term(&self, class: A::Class) -> Option<A::Term> {
        self.best_terms.get_by_key(&class).copied()
    }

    /// Record the minimal term extracted for a snapshot class. Callers check
    /// the cache first, so a key is never overwritten (no shadow log entries).
    fn cache_best_term(&mut self, class: A::Class, term: A::Term) {
        // One hash, and the write-once discipline is now enforced rather than
        // asserted: a present key leaves the entry as it was.
        let (_, fresh) = self
            .best_terms
            .try_intern(class, term)
            .expect("AU arena sized by its index word");
        debug_assert!(
            fresh,
            "best-term cache entries are written at most once per class"
        );
    }

    // Structural frame operations: the typed-group member protocol (design doc
    // 10). No tokens — the session's `History` is the only token authority, and
    // it drives these through one forwarding view.
    pub fn push_frame(&mut self, shrink: ShrinkPolicy) {
        Member::push_frame(&mut self.ops, shrink);
        Member::push_frame(&mut self.child_spans, shrink);
        Member::push_frame(&mut self.child_pool, shrink);
        Member::push_frame(&mut self.child_counts, shrink);
        Member::push_frame(&mut self.sizes, shrink);
        Member::push_frame(&mut self.vmasses, shrink);
        Member::push_frame(&mut self.by_structure, shrink);
        Member::push_frame(&mut self.best_terms, shrink);
    }

    pub fn reset_frame(&mut self, depth: usize) {
        Member::reset_frame(&mut self.ops, depth);
        Member::reset_frame(&mut self.child_spans, depth);
        Member::reset_frame(&mut self.child_pool, depth);
        Member::reset_frame(&mut self.child_counts, depth);
        Member::reset_frame(&mut self.sizes, depth);
        Member::reset_frame(&mut self.vmasses, depth);
        Member::reset_frame(&mut self.by_structure, depth);
        Member::reset_frame(&mut self.best_terms, depth);
    }

    pub fn restore_frame(&mut self, depth: usize) {
        Member::restore_frame(&mut self.ops, depth);
        Member::restore_frame(&mut self.child_spans, depth);
        Member::restore_frame(&mut self.child_pool, depth);
        Member::restore_frame(&mut self.child_counts, depth);
        Member::restore_frame(&mut self.sizes, depth);
        Member::restore_frame(&mut self.vmasses, depth);
        Member::restore_frame(&mut self.by_structure, depth);
        Member::restore_frame(&mut self.best_terms, depth);
    }

    pub fn pop_frame(&mut self) {
        Member::pop_frame(&mut self.ops);
        Member::pop_frame(&mut self.child_spans);
        Member::pop_frame(&mut self.child_pool);
        Member::pop_frame(&mut self.child_counts);
        Member::pop_frame(&mut self.sizes);
        Member::pop_frame(&mut self.vmasses);
        Member::pop_frame(&mut self.by_structure);
        Member::pop_frame(&mut self.best_terms);
    }

    pub fn frame_depth(&self) -> usize {
        Member::depth_exec(&self.ops)
    }

    /// Project one side of the anti-unifier: replace every `Variants` node —
    /// at any depth — by its left (side 0) or right (side 1) child, recursively.
    /// The result contains no `Variants` node (§1: variant projection must land
    /// in the source class). New nodes may be interned for rebuilt spines.
    ///
    /// Iterative post-order fold (explicit frame stack): each frame projects
    /// its children left to right, then re-interns only if a child changed, so
    /// the interning order matches the recursive definition exactly. A
    /// `Variants` node is a tail step (follow the chosen arm), so it never
    /// occupies a frame. Depth is heap-bounded, not call-stack-bounded.
    pub fn project(&mut self, id: A::Term, side: usize) -> A::Term {
        debug_assert!(side < 2);
        struct Frame<T, Op> {
            id: T,
            op: Op,
            children: Vec<T>,
            counts: Vec<u64>,
            cursor: usize,
            new_children: Vec<T>,
            changed: bool,
        }
        let mut stack: Vec<Frame<A::Term, TermOp<O, V>>> = Vec::new();
        let mut pending = id;
        loop {
            // Enter: resolve the Variants chain (tail steps), push a frame.
            let mut nid = pending;
            while matches!(self.op(nid), TermOp::Variants) {
                nid = self.children(nid)[side];
            }
            let children = self.children(nid).to_vec();
            let counts = self.counts(nid).to_vec();
            let capacity = children.len();
            stack.push(Frame {
                id: nid,
                op: self.op(nid).clone(),
                children,
                counts,
                cursor: 0,
                new_children: Vec::with_capacity(capacity),
                changed: false,
            });
            // Advance the top frame; complete frames deliver upward.
            loop {
                let top = stack.last_mut().expect("project stack cannot be empty");
                if top.cursor < top.children.len() {
                    pending = top.children[top.cursor];
                    break; // descend into the next child
                }
                let frame = stack.pop().expect("project stack cannot be empty");
                let projected = if frame.changed {
                    // Each child keeps its multiplicity through the projection.
                    let kids: Vec<(A::Term, u64)> = frame
                        .new_children
                        .iter()
                        .copied()
                        .zip(frame.counts.iter().copied())
                        .collect();
                    self.intern_counted(frame.op, &kids)
                } else {
                    frame.id
                };
                let Some(parent) = stack.last_mut() else {
                    return projected;
                };
                let original = parent.children[parent.cursor];
                parent.changed |= projected != original;
                parent.new_children.push(projected);
                parent.cursor += 1;
            }
        }
    }

    /// `id` as an owned tree, each child with its multiplicity, or `None` if it contains
    /// a `Variants` node. Iterative, with an explicit frame stack.
    pub fn own(&self, id: A::Term) -> Option<OwnedTerm<O, V>> {
        struct Frame<O, V, T> {
            op: O,
            children: Vec<(T, u64)>,
            cursor: usize,
            out: Vec<(OwnedTerm<O, V>, u64)>,
        }
        let mut stack: Vec<Frame<O, V, A::Term>> = Vec::new();
        let mut pending = id;
        loop {
            let mut done = None;
            match self.op(pending) {
                TermOp::Literal(op, value) => done = Some(OwnedTerm::Lit(*op, *value)),
                TermOp::EGraph(op) => {
                    let children: Vec<(A::Term, u64)> = self
                        .children(pending)
                        .iter()
                        .copied()
                        .zip(self.counts(pending).iter().copied())
                        .collect();
                    let n = children.len();
                    stack.push(Frame {
                        op: *op,
                        children,
                        cursor: 0,
                        out: Vec::with_capacity(n),
                    });
                }
                TermOp::Variants => return None,
            }
            loop {
                if let Some(t) = done.take() {
                    let Some(parent) = stack.last_mut() else {
                        return Some(t);
                    };
                    let count = parent.children[parent.cursor].1;
                    parent.out.push((t, count));
                    parent.cursor += 1;
                }
                let top = stack.last_mut().expect("own stack is non-empty");
                if top.cursor < top.children.len() {
                    pending = top.children[top.cursor].0;
                    break;
                }
                let frame = stack.pop().expect("own stack is non-empty");
                done = Some(OwnedTerm::App(frame.op, frame.out));
            }
        }
    }

    /// Does this term contain any `Variants` node (at any depth)?
    /// Iterative DFS with an explicit stack; depth is heap-bounded.
    pub fn has_variants(&self, id: A::Term) -> bool {
        let mut stack: Vec<A::Term> = vec![id];
        while let Some(t) = stack.pop() {
            if matches!(self.op(t), TermOp::Variants) {
                return true;
            }
            stack.extend_from_slice(self.children(t));
        }
        false
    }
}

impl<O: DenseId + core::hash::Hash, V: DenseId + core::hash::Hash> Default for TermPool<O, V> {
    fn default() -> Self {
        Self::new()
    }
}

impl<O: DenseId, V: DenseId> core::fmt::Debug for TermPool<O, V> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("TermPool")
            .field("len", &self.ops.len())
            .finish()
    }
}

/// Evaluate the shared terminal generalize action for a class pair.
///
/// Equal classes yield their smallest concrete representative. Unequal classes
/// yield `Variants(best_term(l), best_term(r))` without recursively factoring
/// either representative; operator-aware factoring belongs to structural
/// actions shared by Exact and UCT.
pub(crate) fn evaluate_generalize_action<
    Cfg: EGraphConfig,
    L: LitVal,
    const T: bool,
    const P: bool,
>(
    snap: &AuSnapshot<Cfg, L, T, P>,
    pool: &mut TermPool<Cfg::O, Cfg::V, Cfg::Au>,
    l: ClassOf<Cfg>,
    r: ClassOf<Cfg>,
) -> <Cfg::Au as AuIds>::Term
where
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
    Cfg::Policy: crate::config::StorePolicy<Cfg, T>,
{
    if l == r {
        return build_best_term(snap, pool, l);
    }
    let l_term = build_best_term(snap, pool, l);
    let r_term = build_best_term(snap, pool, r);
    pool.intern(TermOp::Variants, &[l_term, r_term])
}

/// Build the best (smallest) concrete term for a class, interned in the pool.
///
/// Iterative post-order fold (explicit frame stack): each frame resolves its
/// class's best node, evaluates child classes left to right (in
/// `for_each_child` order, repeating AC children per multiplicity), then
/// interns — the same interning order as the recursive definition. Depth is
/// heap-bounded, not call-stack-bounded.
///
/// Memoized per class in the pool: the result is a pure
/// function of `(snap, class)` and the pool binds to one snapshot, so a
/// completed class's term is cached and later builds return it without
/// re-walking the member tree — amortized O(1) per class after the first
/// build. The cache changes nothing observable: interning is idempotent, so
/// the uncached walk would re-intern the identical ids in the identical
/// order; only the redundant walk is skipped. Restore truncates the cache
/// with the pool's other columns, so an entry never outlives its term.
pub fn build_best_term<Cfg: EGraphConfig, L: LitVal, const T: bool, const P: bool>(
    snap: &AuSnapshot<Cfg, L, T, P>,
    pool: &mut TermPool<Cfg::O, Cfg::V, Cfg::Au>,
    class: ClassOf<Cfg>,
) -> <Cfg::Au as AuIds>::Term
where
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
    Cfg::Policy: crate::config::StorePolicy<Cfg, T>,
{
    struct Frame<O, C, M, Term> {
        /// The class this frame extracts, cached when the frame completes.
        class: C,
        op: O,
        /// Child classes with multiplicities, in `for_each_child` order.
        child_classes: Vec<(C, M)>,
        cursor: usize,
        children: Vec<(Term, u64)>,
    }
    let eg = snap.egraph();
    let mut stack: Vec<Frame<Cfg::O, ClassOf<Cfg>, Cfg::M, <Cfg::Au as AuIds>::Term>> = Vec::new();
    let mut pending = class;
    loop {
        // Enter: cached classes complete immediately, as do literals; other
        // nodes resolve the class's best node and get a frame.
        let mut done: Option<<Cfg::Au as AuIds>::Term> = None;
        if let Some(term) = pool.cached_best_term(pending) {
            done = Some(term);
        } else {
            let best_id = snap.best_node(pending);
            let op = eg.node_op(best_id);
            if let Some(val_id) = eg.get_lit_val_id(best_id) {
                let term = pool.intern(TermOp::Literal(op, val_id), &[]);
                pool.cache_best_term(pending, term);
                done = Some(term);
            } else {
                let mut child_classes: Vec<(ClassOf<Cfg>, Cfg::M)> = Vec::new();
                eg.for_each_child(best_id, |child, mult| {
                    child_classes.push((snap.class_of(child).unwrap(), mult));
                });
                stack.push(Frame {
                    class: pending,
                    op,
                    child_classes,
                    cursor: 0,
                    children: Vec::new(),
                });
            }
        }
        // Advance: deliver any completed term upward, then descend or compose.
        loop {
            if let Some(term) = done.take() {
                let Some(parent) = stack.last_mut() else {
                    return term;
                };
                // The child once, with its multiplicity: never k copies.
                let (_, mult) = parent.child_classes[parent.cursor];
                parent.children.push((term, crate::au::au_count(mult)));
                parent.cursor += 1;
            }
            let top = stack
                .last_mut()
                .expect("build_best_term stack cannot be empty");
            if top.cursor < top.child_classes.len() {
                pending = top.child_classes[top.cursor].0;
                break; // descend into the next child class
            }
            let frame = stack.pop().expect("build_best_term stack cannot be empty");
            let term = pool.intern_counted(TermOp::EGraph(frame.op), &frame.children);
            pool.cache_best_term(frame.class, term);
            done = Some(term);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::egraph::EGraph31;
    use crate::id::OpId;
    use crate::literal::NiraLitVal;

    #[test]
    fn term_pool_dedup() {
        let mut pool = TermPool::<OpId, crate::id::ENodeId>::new();
        let op = OpId::from_usize(0);

        let leaf = pool.intern(TermOp::EGraph(op), &[]);
        let leaf2 = pool.intern(TermOp::EGraph(op), &[]);
        assert_eq!(leaf, leaf2);
        assert_eq!(pool.size(leaf), 1);
    }

    #[test]
    fn term_size_variants_zero() {
        let mut pool = TermPool::<OpId, crate::id::ENodeId>::new();
        let op = OpId::from_usize(0);

        let left = pool.intern(TermOp::EGraph(op), &[]);
        let right = pool.intern(TermOp::EGraph(OpId::from_usize(1)), &[]);
        let variants = pool.intern(TermOp::Variants, &[left, right]);

        // Variants costs 0, children cost 1 each.
        assert_eq!(pool.size(variants), 2);
    }

    #[test]
    fn generalize_action_identical_class_returns_best_term() {
        let mut eg = EGraph31::<NiraLitVal, false, false>::new();
        let int = eg.intern_sort("Int");
        let a_op = eg.register_op0("a", int);
        let a = eg.add(a_op, &[]);
        eg.rebuild();

        let snap = AuSnapshot::new(&eg).unwrap();
        let ac = snap.class_of(a).unwrap();

        let mut pool = TermPool::new();
        let result = evaluate_generalize_action(&snap, &mut pool, ac, ac);
        assert_eq!(pool.size(result), 1);
        assert_eq!(*pool.op(result), TermOp::EGraph(a_op));
    }

    #[test]
    fn generalize_action_unequal_classes_returns_best_term_variants() {
        let mut eg = EGraph31::<NiraLitVal, false, false>::new();
        let int = eg.intern_sort("Int");
        let a_op = eg.register_op0("a", int);
        let b_op = eg.register_op0("b", int);
        let a = eg.add(a_op, &[]);
        let b = eg.add(b_op, &[]);
        eg.rebuild();

        let snap = AuSnapshot::new(&eg).unwrap();
        let ac = snap.class_of(a).unwrap();
        let bc = snap.class_of(b).unwrap();

        let mut pool = TermPool::new();
        let result = evaluate_generalize_action(&snap, &mut pool, ac, bc);
        // Variants(a, b) -> size 2 (1+1, Variants itself costs 0).
        assert_eq!(pool.size(result), 2);
        assert_eq!(*pool.op(result), TermOp::Variants);
        assert_eq!(pool.children(result).len(), 2);
    }

    /// P1 regression: projection must descend below ordinary operators.
    /// project(f(a, Variants(b,c)), 0) = f(a, b); side 1 = f(a, c).
    #[test]
    fn projection_is_deep() {
        let mut pool = TermPool::<OpId, crate::id::ENodeId>::new();
        let f = OpId::from_usize(0);
        let a = pool.intern(TermOp::EGraph(OpId::from_usize(1)), &[]);
        let b = pool.intern(TermOp::EGraph(OpId::from_usize(2)), &[]);
        let c = pool.intern(TermOp::EGraph(OpId::from_usize(3)), &[]);
        let v = pool.intern(TermOp::Variants, &[b, c]);
        let root = pool.intern(TermOp::EGraph(f), &[a, v]);

        let left = pool.project(root, 0);
        let right = pool.project(root, 1);

        assert!(!pool.has_variants(left));
        assert!(!pool.has_variants(right));
        assert_eq!(pool.children(left), &[a, b]);
        assert_eq!(pool.children(right), &[a, c]);

        // Nested Variants inside a chosen arm are resolved too.
        let v2 = pool.intern(TermOp::Variants, &[v, a]);
        let root2 = pool.intern(TermOp::EGraph(f), &[v2, a]);
        let l2 = pool.project(root2, 0);
        assert!(!pool.has_variants(l2));
        assert_eq!(pool.children(l2), &[b, a]);
    }

    /// P0 regression: ordered operators preserve positional child order even
    /// when the positional order disagrees with TermId order.
    #[test]
    fn ordered_children_not_sorted() {
        let mut pool = TermPool::<OpId, crate::id::ENodeId>::new();
        let f = OpId::from_usize(0);
        // Allocate `b` FIRST so its TermId sorts before the Variants node.
        let b = pool.intern(TermOp::EGraph(OpId::from_usize(2)), &[]);
        let a = pool.intern(TermOp::EGraph(OpId::from_usize(1)), &[]);
        let c = pool.intern(TermOp::EGraph(OpId::from_usize(3)), &[]);
        let v = pool.intern(TermOp::Variants, &[a, c]);

        // Ordered: f(Variants(a,c), b) must keep the Variants first.
        let ordered =
            pool.intern_action_result(TermOp::EGraph(f), &[(v, 1), (b, 1)], ChildForm::Ordered);
        assert_eq!(pool.children(ordered), &[v, b]);

        // Commutative: children are sorted structurally (EGraph ops rank before
        // Variants), independent of allocation order.
        let comm =
            pool.intern_action_result(TermOp::EGraph(f), &[(v, 1), (b, 1)], ChildForm::Commutative);
        assert_eq!(pool.children(comm), &[b, v]);
    }

    /// A multiset result keeps a child of multiplicity k as one entry with count k: equal
    /// children merge and their counts sum, and the size counts each copy.
    #[test]
    fn a_multiset_child_is_one_entry_with_its_count() {
        let mut pool = TermPool::<OpId, crate::id::ENodeId>::new();
        let f = OpId::from_usize(0);
        let a = pool.intern(TermOp::EGraph(OpId::from_usize(1)), &[]);
        let b = pool.intern(TermOp::EGraph(OpId::from_usize(2)), &[]);
        let t = pool.intern_action_result(
            TermOp::EGraph(f),
            &[(a, 3), (b, 1), (a, 2)],
            ChildForm::Multiset,
        );
        assert_eq!(pool.children(t), &[a, b]);
        assert_eq!(pool.counts(t), &[5, 1]);
        assert_eq!(pool.size(t), 1 + 5 + 1);
        // The same multiset given another way interns to the same term.
        let u =
            pool.intern_action_result(TermOp::EGraph(f), &[(b, 1), (a, 5)], ChildForm::Multiset);
        assert_eq!(t, u);
        // A `:comm` pair keeps two entries.
        let p =
            pool.intern_action_result(TermOp::EGraph(f), &[(a, 1), (a, 1)], ChildForm::Commutative);
        assert_eq!(pool.children(p), &[a, a]);
    }

    /// Variant mass: backbone nodes are excluded; everything under Variants counts.
    #[test]
    fn variant_mass_arithmetic() {
        let mut pool = TermPool::<OpId, crate::id::ENodeId>::new();
        let f = OpId::from_usize(0);
        let x = pool.intern(TermOp::EGraph(OpId::from_usize(1)), &[]);
        let y = pool.intern(TermOp::EGraph(OpId::from_usize(2)), &[]);
        let fy = pool.intern(TermOp::EGraph(f), &[y]);

        // Variants(x, f(y)): size 3, all variant mass.
        let bare = pool.intern(TermOp::Variants, &[x, fy]);
        assert_eq!(pool.quality(bare), (3, 3));

        // f(Variants(x, y)): size 3, variant mass 2 — one backbone node.
        let v = pool.intern(TermOp::Variants, &[x, y]);
        let factored = pool.intern(TermOp::EGraph(f), &[v]);
        assert_eq!(pool.quality(factored), (3, 2));

        // The factored form is strictly better in the lexicographic order.
        assert!(pool.quality(factored) < pool.quality(bare));
    }

    /// A term whose expanded size passes `u32` saturates and stays the *worst*
    /// candidate. 33 stored rows are enough to name 2^32 leaves, so this is not a
    /// hypothetical width: it is what wrapping arithmetic looked like in release,
    /// where the giant term scored 0 and beat every real generalization.
    #[test]
    fn expanded_size_saturates_and_ranks_worst() {
        let mut pool = TermPool::<OpId, crate::id::ENodeId>::new();
        let x = pool.intern(TermOp::EGraph(OpId::from_usize(0)), &[]);
        assert_eq!(pool.size(x), 1);

        // Each level doubles: `size(v_k) == 2^k`, so `v_32` would be 2^32.
        let mut v = x;
        for level in 1..=31u32 {
            v = pool.intern(TermOp::Variants, &[v, v]);
            assert_eq!(pool.size(v), 1u32 << level, "level {level} is exact");
        }

        let over = pool.intern(TermOp::Variants, &[v, v]);
        assert_eq!(pool.size(over), u32::MAX);
        assert_eq!(pool.variant_mass(over), u32::MAX);

        // Saturated, so it ranks below the largest exactly-counted term — and below
        // the leaf. Wrapping would have made it `(0, 0)`: the best score possible.
        assert!(pool.quality(v) < pool.quality(over));
        assert!(pool.quality(x) < pool.quality(over));

        // A backbone node above a saturated child stays saturated (`1 + MAX`).
        let wrapped = pool.intern(TermOp::EGraph(OpId::from_usize(1)), &[over]);
        assert_eq!(pool.size(wrapped), u32::MAX);
    }

    #[test]
    fn generalize_action_does_not_positionally_factor_shared_structure() {
        let mut eg = EGraph31::<NiraLitVal, false, false>::new();
        let int = eg.intern_sort("Int");
        let a_op = eg.register_op0("a", int);
        let b_op = eg.register_op0("b", int);
        let c_op = eg.register_op0("c", int);
        let f_op = eg.register_op2("f", int, int, int);

        let a = eg.add(a_op, &[]);
        let b = eg.add(b_op, &[]);
        let c = eg.add(c_op, &[]);
        let fab = eg.add(f_op, &[a, b]);
        let fac = eg.add(f_op, &[a, c]);
        eg.rebuild();

        let snap = AuSnapshot::new(&eg).unwrap();
        let lc = snap.class_of(fab).unwrap();
        let rc = snap.class_of(fac).unwrap();

        let mut pool = TermPool::new();
        let result = evaluate_generalize_action(&snap, &mut pool, lc, rc);
        // The terminal base action is whole-term generalization, not a
        // positional zipper: Variants(f(a,b), f(a,c)) has size 3 + 3 = 6.
        assert_eq!(pool.size(result), 6);
        assert_eq!(*pool.op(result), TermOp::Variants);
        let arms = pool.children(result);
        assert_eq!(arms.len(), 2);
        assert_eq!(*pool.op(arms[0]), TermOp::EGraph(f_op));
        assert_eq!(*pool.op(arms[1]), TermOp::EGraph(f_op));
    }

    /// The best-term cache must be truncated by restore
    /// exactly like the term columns, so a cache entry never names a truncated
    /// term id. Build (pre-mark entries), mark, build more (post-mark entries),
    /// restore, then re-build both classes: the pre-mark class must return its
    /// surviving id without growing the pool, and the post-mark class must be
    /// rebuilt from scratch into an in-bounds id — identical to the pre-restore
    /// build, because the replayed interning order is identical.
    #[test]
    fn best_term_cache_is_truncated_by_restore() {
        let mut eg = EGraph31::<NiraLitVal, false, false>::new();
        let sort = eg.intern_sort("E");
        let a_op = eg.register_op0("a", sort);
        let f_op = eg.register_op1("f", sort, sort);
        let g_op = eg.register_op1("g", sort, sort);
        let a = eg.add(a_op, &[]);
        let fa = eg.add(f_op, &[a]);
        let gfa = eg.add(g_op, &[fa]);
        eg.rebuild();

        let snap = AuSnapshot::new(&eg).unwrap();
        let fa_class = snap.class_of(fa).unwrap();
        let gfa_class = snap.class_of(gfa).unwrap();

        let mut pool = TermPool::new();
        let t_fa = build_best_term(&snap, &mut pool, fa_class);
        assert_eq!(pool.size(t_fa), 2);

        let len_at_mark = pool.len();
        let token = pool.frame_depth();
        pool.push_frame(ShrinkPolicy::Never);

        // Post-mark: caches the gfa class and interns the g term.
        let t_gfa = build_best_term(&snap, &mut pool, gfa_class);
        assert_eq!(pool.size(t_gfa), 3);
        assert_eq!(pool.children(t_gfa), &[t_fa]);
        assert!(pool.len() > len_at_mark);

        pool.reset_frame(token);
        assert_eq!(pool.len(), len_at_mark);

        // Pre-mark entry survives: cache hit on the surviving id, no growth.
        let t_fa2 = build_best_term(&snap, &mut pool, fa_class);
        assert_eq!(t_fa2, t_fa);
        assert_eq!(pool.len(), len_at_mark);

        // Post-mark entry is gone: the class rebuilds from scratch into an
        // in-bounds id — numerically equal to the pre-restore build, because
        // restore rewound the pool to the same state it was built from.
        let t_gfa2 = build_best_term(&snap, &mut pool, gfa_class);
        assert_eq!(t_gfa2, t_gfa);
        assert!(t_gfa2.to_usize() < pool.len().as_usize());
        assert_eq!(pool.size(t_gfa2), 3);
        assert_eq!(*pool.op(t_gfa2), TermOp::EGraph(g_op));
        assert_eq!(pool.children(t_gfa2), &[t_fa]);
    }
}
