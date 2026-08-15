// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Search-space layer: OR/AND arenas, context interner, node/edge caches (§4.2).
//!
//! The search space is an AND/OR graph where OR nodes are subproblems `AU(l, r)`
//! keyed by `(l, r, ctxL, ctxR)`, and AND nodes are chosen factorings (operator +
//! paired children). Everything here is immutable once pushed (hash-cons semantics).
//! All storage uses semi-persistent containers (AppendOnlyVec for structural fields,
//! SpMap for deduplication caches); mark/restore truncates them as one unit.

use crate::config::AuIds;
use crate::containers::{
    AppendOnlyVec, DenseId, IndexLike, MapToken, ShrinkPolicy, SpMap, VecToken,
};

use super::{AuIds31, Span};

// ---------------------------------------------------------------------------
// Id types
// ---------------------------------------------------------------------------

crate::containers::define_id31! {
    /// Index of an OR node in the search-space layer.
    pub struct OrId / StoredOrId, "or";
}

crate::containers::define_id31! {
    /// Index of a cached action list in the action cache.
    pub struct ActionId / StoredActionId, "act";
}

crate::containers::define_id31! {
    /// Interned context id (a sorted vector of AuClassId).
    pub struct CtxId / StoredCtxId, "ctx";
}

// ---------------------------------------------------------------------------
// CycleMode
// ---------------------------------------------------------------------------

/// How aggressively cycle paths are pruned (§2.3). Both modes produce finite graphs.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
pub enum CycleMode {
    /// Filter actions against ancestor contexts only. A class can occur at most
    /// twice per side on a path (once as the current node, once as a child).
    #[default]
    AncestorOnly,
    /// Also filter against the current (l, r). A class occurs at most once per
    /// side on a path.
    CurrentInclusive,
}

// ---------------------------------------------------------------------------
// Context interner (semi-persistent: AppendOnlyVec + SpMap)
// ---------------------------------------------------------------------------

/// Interns sorted class-id vectors as context ids. Two equal vectors get the
/// same context id; comparison is then a single integer compare.
///
/// Both pools and the dedup map are addressed by ids whose `Index` is `A::Index`
/// (`A::Context` for `spans`, `A::ContextElem` for `classes`, and `index`'s log
/// positions are what `A::Context`s are minted from), so that word is the index type
/// rather than `usize`.
pub struct ContextStore<A: AuIds = AuIds31> {
    /// Each interned context's data as a typed span into `classes`.
    spans: AppendOnlyVec<Span<A::ContextElem>, A::Index>,
    /// Pool of class ids (all interned contexts concatenated).
    classes: AppendOnlyVec<A::Class, A::Index>,
    /// Deduplication map: sorted class vector -> context id.
    index: SpMap<Vec<A::Class>, A::Context, A::Index>,
}

/// Token for restoring a `ContextStore` to a previous state.
#[derive(Clone, Copy, Debug)]
pub struct ContextStoreToken {
    spans: VecToken,
    classes: VecToken,
    index: MapToken,
}

impl<A: AuIds> ContextStore<A> {
    pub fn new() -> Self {
        let mut store = ContextStore {
            spans: AppendOnlyVec::new(),
            classes: AppendOnlyVec::new(),
            index: SpMap::new(),
        };
        store.intern(&[]);
        store
    }

    pub fn empty(&self) -> A::Context {
        // The empty context is interned first in `new`, so id 0 is it. Id 0 exists in every
        // id family, so this mint needs no check.
        A::Context::from_usize(0)
    }

    pub fn intern(&mut self, sorted_classes: &[A::Class]) -> A::Context {
        if let Some(log_idx) = self.index.id_of(&sorted_classes.to_vec()) {
            return *self.index.get_val(log_idx);
        }
        let id: A::Context = crate::id::id_at_index(self.spans.len());
        let start = self.classes.len().as_usize();
        for &c in sorted_classes {
            self.classes
                .try_push(c)
                .expect("AU arena sized by its index word");
        }
        self.spans
            .try_push(Span::new(start, sorted_classes.len()))
            .expect("AU arena sized by its index word");
        self.index
            .try_insert(sorted_classes.to_vec(), id)
            .expect("AU arena sized by its index word");
        id
    }

    #[inline]
    pub fn get(&self, id: A::Context) -> &[A::Class] {
        let span = *self.spans.get(id.to_index());
        let start = span.start_usize();
        let len = span.len_usize();
        // `as_slice()` is the verified accessor for exactly this: its
        // postcondition is `r@ == self.view()`, so the contiguity this used to
        // assert with `from_raw_parts` is now a proof obligation the container
        // discharges. The span was built by `intern`, which pushes the elements
        // consecutively, so `[start, start + len)` is in bounds — and if it ever
        // were not, this panics instead of reading out of bounds.
        &self.classes.as_slice()[start..start + len]
    }

    #[inline]
    pub fn contains(&self, id: A::Context, class: A::Class) -> bool {
        self.get(id).binary_search(&class).is_ok()
    }

    /// Number of interned contexts, in the configured index word (a context count is
    /// a position count: the next context interns at exactly this index).
    pub fn len(&self) -> A::Index {
        self.spans.len()
    }

    pub fn is_empty(&self) -> bool {
        self.spans.is_empty()
    }

    pub fn mark(&mut self) -> ContextStoreToken {
        ContextStoreToken {
            spans: self
                .spans
                .try_mark(ShrinkPolicy::Never)
                .expect("mark: depth bounded by the search driver"),
            classes: self
                .classes
                .try_mark(ShrinkPolicy::Never)
                .expect("mark: depth bounded by the search driver"),
            index: self
                .index
                .try_mark(ShrinkPolicy::Never)
                .expect("mark: depth bounded by the search driver"),
        }
    }

    pub fn is_valid_token(&self, token: &ContextStoreToken) -> bool {
        self.spans.is_valid_token(&token.spans)
            && self.classes.is_valid_token(&token.classes)
            && self.index.is_valid_token(&token.index)
    }

    pub fn restore(&mut self, token: ContextStoreToken) {
        self.index
            .try_restore(token.index)
            .expect("restore: token minted by this container's own mark");
        self.classes
            .try_restore(token.classes)
            .expect("restore: token minted by this container's own mark");
        self.spans
            .try_restore(token.spans)
            .expect("restore: token minted by this container's own mark");
    }
}

impl<A: AuIds> Default for ContextStore<A> {
    fn default() -> Self {
        Self::new()
    }
}

// ---------------------------------------------------------------------------
// OR arena (semi-persistent: AppendOnlyVec + SpMap)
// ---------------------------------------------------------------------------

/// The OR-node arena: each node is a subproblem `AU(l, r)` with cycle contexts.
/// Every column is addressed by `A::Or`, and `by_key`'s log positions are what the
/// `A::Or`s are minted from, so the index word is `A::Index` throughout.
pub struct OrArena<A: AuIds = AuIds31> {
    pub left: AppendOnlyVec<A::Class, A::Index>,
    pub right: AppendOnlyVec<A::Class, A::Index>,
    pub left_ctx: AppendOnlyVec<A::Context, A::Index>,
    pub right_ctx: AppendOnlyVec<A::Context, A::Index>,
    pub terminal: AppendOnlyVec<bool, A::Index>,
    pub left_best_size: AppendOnlyVec<u32, A::Index>,
    pub right_best_size: AppendOnlyVec<u32, A::Index>,
    pub by_key: SpMap<(A::Class, A::Class, A::Context, A::Context), A::Or, A::Index>,
}

/// Token for restoring an `OrArena`.
#[derive(Clone, Copy, Debug)]
pub struct OrArenaToken {
    left: VecToken,
    right: VecToken,
    left_ctx: VecToken,
    right_ctx: VecToken,
    terminal: VecToken,
    left_best_size: VecToken,
    right_best_size: VecToken,
    by_key: MapToken,
}

impl<A: AuIds> OrArena<A> {
    pub fn new() -> Self {
        OrArena {
            left: AppendOnlyVec::new(),
            right: AppendOnlyVec::new(),
            left_ctx: AppendOnlyVec::new(),
            right_ctx: AppendOnlyVec::new(),
            terminal: AppendOnlyVec::new(),
            left_best_size: AppendOnlyVec::new(),
            right_best_size: AppendOnlyVec::new(),
            by_key: SpMap::new(),
        }
    }

    /// Number of OR nodes, in the configured index word (the next node lands at
    /// exactly this index).
    pub fn len(&self) -> A::Index {
        self.left.len()
    }

    pub fn is_empty(&self) -> bool {
        self.left.is_empty()
    }

    pub fn mark(&mut self) -> OrArenaToken {
        OrArenaToken {
            left: self
                .left
                .try_mark(ShrinkPolicy::Never)
                .expect("mark: depth bounded by the search driver"),
            right: self
                .right
                .try_mark(ShrinkPolicy::Never)
                .expect("mark: depth bounded by the search driver"),
            left_ctx: self
                .left_ctx
                .try_mark(ShrinkPolicy::Never)
                .expect("mark: depth bounded by the search driver"),
            right_ctx: self
                .right_ctx
                .try_mark(ShrinkPolicy::Never)
                .expect("mark: depth bounded by the search driver"),
            terminal: self
                .terminal
                .try_mark(ShrinkPolicy::Never)
                .expect("mark: depth bounded by the search driver"),
            left_best_size: self
                .left_best_size
                .try_mark(ShrinkPolicy::Never)
                .expect("mark: depth bounded by the search driver"),
            right_best_size: self
                .right_best_size
                .try_mark(ShrinkPolicy::Never)
                .expect("mark: depth bounded by the search driver"),
            by_key: self
                .by_key
                .try_mark(ShrinkPolicy::Never)
                .expect("mark: depth bounded by the search driver"),
        }
    }

    pub fn restore(&mut self, token: OrArenaToken) {
        self.by_key
            .try_restore(token.by_key)
            .expect("restore: token minted by this container's own mark");
        self.right_best_size
            .try_restore(token.right_best_size)
            .expect("restore: token minted by this container's own mark");
        self.left_best_size
            .try_restore(token.left_best_size)
            .expect("restore: token minted by this container's own mark");
        self.terminal
            .try_restore(token.terminal)
            .expect("restore: token minted by this container's own mark");
        self.right_ctx
            .try_restore(token.right_ctx)
            .expect("restore: token minted by this container's own mark");
        self.left_ctx
            .try_restore(token.left_ctx)
            .expect("restore: token minted by this container's own mark");
        self.right
            .try_restore(token.right)
            .expect("restore: token minted by this container's own mark");
        self.left
            .try_restore(token.left)
            .expect("restore: token minted by this container's own mark");
    }

    pub fn is_valid_token(&self, token: &OrArenaToken) -> bool {
        self.left.is_valid_token(&token.left)
    }
}

impl<A: AuIds> Default for OrArena<A> {
    fn default() -> Self {
        Self::new()
    }
}

// ---------------------------------------------------------------------------
// SearchSpace: combines the above into one structure
// ---------------------------------------------------------------------------

/// Token for restoring the entire search-space layer. Validity is delegated
/// to the inner semi-persistent containers' branch genealogy.
#[derive(Clone, Copy, Debug)]
pub struct SpaceToken {
    or_arena: OrArenaToken,
    contexts: ContextStoreToken,
}

/// The complete search-space layer shared by all algorithms in a session.
pub struct SearchSpace<A: AuIds = AuIds31> {
    pub or_arena: OrArena<A>,
    pub contexts: ContextStore<A>,
    pub cycle_mode: CycleMode,
}

impl<A: AuIds> SearchSpace<A> {
    pub fn new(cycle_mode: CycleMode) -> Self {
        SearchSpace {
            or_arena: OrArena::new(),
            contexts: ContextStore::new(),
            cycle_mode,
        }
    }

    /// Look up or create an OR node for the given state. Returns `(id, is_new)`.
    pub fn get_or_insert_or_node(
        &mut self,
        l: A::Class,
        r: A::Class,
        ctx_l: A::Context,
        ctx_r: A::Context,
        left_best_size: u32,
        right_best_size: u32,
    ) -> (A::Or, bool) {
        let key = (l, r, ctx_l, ctx_r);
        if let Some(log_idx) = self.or_arena.by_key.id_of(&key) {
            return (*self.or_arena.by_key.get_val(log_idx), false);
        }
        let id: A::Or = crate::id::id_at_index(self.or_arena.len());
        self.or_arena
            .left
            .try_push(l)
            .expect("AU arena sized by its index word");
        self.or_arena
            .right
            .try_push(r)
            .expect("AU arena sized by its index word");
        self.or_arena
            .left_ctx
            .try_push(ctx_l)
            .expect("AU arena sized by its index word");
        self.or_arena
            .right_ctx
            .try_push(ctx_r)
            .expect("AU arena sized by its index word");
        self.or_arena
            .terminal
            .try_push(l == r)
            .expect("AU arena sized by its index word");
        self.or_arena
            .left_best_size
            .try_push(left_best_size)
            .expect("AU arena sized by its index word");
        self.or_arena
            .right_best_size
            .try_push(right_best_size)
            .expect("AU arena sized by its index word");
        self.or_arena
            .by_key
            .try_insert(key, id)
            .expect("AU arena sized by its index word");
        (id, true)
    }

    /// Derive the child context for one side (§2.3).
    pub fn derive_child_context(
        &mut self,
        parent_ctx: A::Context,
        parent_class: A::Class,
        is_reachable_from_child: impl Fn(A::Class) -> bool,
    ) -> A::Context {
        let parent_classes = self.contexts.get(parent_ctx);

        let mut result: Vec<A::Class> = Vec::new();
        for &c in parent_classes {
            if is_reachable_from_child(c) {
                result.push(c);
            }
        }
        if is_reachable_from_child(parent_class) && result.binary_search(&parent_class).is_err() {
            result.push(parent_class);
            result.sort_unstable();
        }

        self.contexts.intern(&result)
    }

    /// Intern `ctx` extended with `class` (no-op when already present).
    ///
    /// Identity padding needs this: the injected identity class is not a
    /// structural child of any member, so [`Self::derive_child_context`]'s
    /// reachability filter records nothing for it, and without the extension
    /// a padding-created cell can repeat its ancestor's OR key
    /// `(l, r, ctxL, ctxR)` exactly. Extending the padded cell's contexts
    /// restores the rank argument's "context grows" disjunct (§3.2):
    /// contexts are bounded by the class count, so the recursion terminates.
    pub fn extend_context(&mut self, ctx: A::Context, class: A::Class) -> A::Context {
        if self.contexts.contains(ctx, class) {
            return ctx;
        }
        let mut classes: Vec<A::Class> = self.contexts.get(ctx).to_vec();
        classes.push(class);
        classes.sort_unstable();
        self.contexts.intern(&classes)
    }

    /// Check if an action's child pair is blocked by the cycle mode filter.
    pub fn is_cycle_blocked(&self, or_id: A::Or, child_l: A::Class, child_r: A::Class) -> bool {
        let ctx_l = *self.or_arena.left_ctx.get(or_id.to_index());
        let ctx_r = *self.or_arena.right_ctx.get(or_id.to_index());

        if self.contexts.contains(ctx_l, child_l) {
            return true;
        }
        if self.contexts.contains(ctx_r, child_r) {
            return true;
        }

        if self.cycle_mode == CycleMode::CurrentInclusive {
            let l = *self.or_arena.left.get(or_id.to_index());
            let r = *self.or_arena.right.get(or_id.to_index());
            if child_l == l || child_r == r {
                return true;
            }
        }

        false
    }

    pub fn mark(&mut self) -> SpaceToken {
        SpaceToken {
            or_arena: self.or_arena.mark(),
            contexts: self.contexts.mark(),
        }
    }

    /// Is this token restorable right now (same instances, live branches on
    /// every inner container)?
    pub fn is_valid_token(&self, token: &SpaceToken) -> bool {
        self.or_arena.is_valid_token(&token.or_arena)
            && self.contexts.is_valid_token(&token.contexts)
    }

    pub fn restore(&mut self, token: SpaceToken) {
        self.or_arena.restore(token.or_arena);
        self.contexts.restore(token.contexts);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::au::AuClassId;

    #[test]
    fn context_interner_empty() {
        let store: ContextStore = ContextStore::new();
        assert_eq!(store.empty(), CtxId::from_usize(0));
        assert_eq!(store.get(store.empty()), &[]);
        assert!(!store.contains(store.empty(), AuClassId::from_usize(0)));
    }

    #[test]
    fn context_interner_dedup() {
        let mut store: ContextStore = ContextStore::new();
        let c0 = AuClassId::from_usize(0);
        let c1 = AuClassId::from_usize(1);
        let c2 = AuClassId::from_usize(2);

        let ctx_a = store.intern(&[c0, c1]);
        let ctx_b = store.intern(&[c0, c1]);
        assert_eq!(ctx_a, ctx_b);

        let ctx_c = store.intern(&[c0, c1, c2]);
        assert_ne!(ctx_a, ctx_c);

        assert!(store.contains(ctx_a, c0));
        assert!(store.contains(ctx_a, c1));
        assert!(!store.contains(ctx_a, c2));
        assert!(store.contains(ctx_c, c2));
    }

    #[test]
    fn or_node_dedup() {
        let mut space: SearchSpace = SearchSpace::new(CycleMode::AncestorOnly);
        let c0 = AuClassId::from_usize(0);
        let c1 = AuClassId::from_usize(1);
        let ctx = space.contexts.empty();

        let (id1, new1) = space.get_or_insert_or_node(c0, c1, ctx, ctx, 1, 1);
        assert!(new1);

        let (id2, new2) = space.get_or_insert_or_node(c0, c1, ctx, ctx, 1, 1);
        assert!(!new2);
        assert_eq!(id1, id2);

        let (id3, new3) = space.get_or_insert_or_node(c1, c0, ctx, ctx, 1, 1);
        assert!(new3);
        assert_ne!(id1, id3);
    }

    #[test]
    fn derive_child_context_acyclic() {
        let mut space: SearchSpace = SearchSpace::new(CycleMode::AncestorOnly);
        let parent_ctx = space.contexts.empty();
        let parent_class = AuClassId::from_usize(0);

        let child_ctx = space.derive_child_context(parent_ctx, parent_class, |_| false);
        assert_eq!(child_ctx, space.contexts.empty());
    }

    #[test]
    fn derive_child_context_cyclic() {
        let mut space: SearchSpace = SearchSpace::new(CycleMode::AncestorOnly);
        let c0 = AuClassId::from_usize(0);
        let c1 = AuClassId::from_usize(1);

        let parent_ctx = space.contexts.intern(&[c0]);
        let parent_class = c1;

        let child_ctx =
            space.derive_child_context(parent_ctx, parent_class, |c| c == c0 || c == c1);

        let ctx_classes = space.contexts.get(child_ctx);
        assert_eq!(ctx_classes, &[c0, c1]);
    }

    #[test]
    fn cycle_blocking_ancestor_only() {
        let mut space: SearchSpace = SearchSpace::new(CycleMode::AncestorOnly);
        let c0 = AuClassId::from_usize(0);
        let c1 = AuClassId::from_usize(1);
        let c2 = AuClassId::from_usize(2);

        let ctx_l = space.contexts.intern(&[c0]);
        let ctx_r = space.contexts.empty();
        let (or_id, _) = space.get_or_insert_or_node(c1, c2, ctx_l, ctx_r, 1, 1);

        assert!(space.is_cycle_blocked(or_id, c0, c2));
        assert!(!space.is_cycle_blocked(or_id, c1, c2));
        assert!(!space.is_cycle_blocked(or_id, c1, c2));
    }

    #[test]
    fn cycle_blocking_current_inclusive() {
        let mut space: SearchSpace = SearchSpace::new(CycleMode::CurrentInclusive);
        let c0 = AuClassId::from_usize(0);
        let c1 = AuClassId::from_usize(1);
        let c2 = AuClassId::from_usize(2);

        let ctx_l = space.contexts.empty();
        let ctx_r = space.contexts.empty();
        let (or_id, _) = space.get_or_insert_or_node(c1, c2, ctx_l, ctx_r, 1, 1);

        assert!(space.is_cycle_blocked(or_id, c1, c0));
        assert!(space.is_cycle_blocked(or_id, c0, c2));
        assert!(!space.is_cycle_blocked(or_id, c0, c0));
    }

    #[test]
    fn terminal_when_l_eq_r() {
        let mut space: SearchSpace = SearchSpace::new(CycleMode::AncestorOnly);
        let c0 = AuClassId::from_usize(0);
        let ctx = space.contexts.empty();

        let (or_id, _) = space.get_or_insert_or_node(c0, c0, ctx, ctx, 1, 1);
        assert!(*space.or_arena.terminal.get(or_id.to_index()));
    }

    #[test]
    fn mark_restore_truncates() {
        let mut space: SearchSpace = SearchSpace::new(CycleMode::AncestorOnly);
        let c0 = AuClassId::from_usize(0);
        let c1 = AuClassId::from_usize(1);
        let c2 = AuClassId::from_usize(2);
        let ctx = space.contexts.empty();

        let (id1, _) = space.get_or_insert_or_node(c0, c1, ctx, ctx, 1, 1);
        let token = space.mark();

        let (_id2, _) = space.get_or_insert_or_node(c1, c2, ctx, ctx, 1, 1);
        assert_eq!(space.or_arena.len(), 2);

        space.restore(token);
        assert_eq!(space.or_arena.len(), 1);

        // The first node is still there.
        let (id1b, new) = space.get_or_insert_or_node(c0, c1, ctx, ctx, 1, 1);
        assert!(!new);
        assert_eq!(id1, id1b);

        // The second node was rolled back; re-inserting it is new.
        let (_, new) = space.get_or_insert_or_node(c1, c2, ctx, ctx, 1, 1);
        assert!(new);
    }
}
