// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Search-space layer: OR/AND arenas, context interner, node/edge caches (§4.2).
//!
//! The search space is an AND/OR graph where OR nodes are subproblems `AU(l, r)`
//! keyed by `(l, r, ctxL, ctxR)`, and AND nodes are chosen factorings (operator +
//! paired children). Everything here is immutable once pushed (hash-cons semantics).
//! All storage uses semi-persistent containers (AppendOnlyVec for structural fields,
//! Map for deduplication caches); mark/restore truncates them as one unit.

use crate::containers::{AppendOnlyVec, DenseId, Map, MapToken, ShrinkPolicy, VecToken};

use super::AuClassId;

// ---------------------------------------------------------------------------
// Id types
// ---------------------------------------------------------------------------

crate::containers::define_id31! {
    /// Index of an OR node in the search-space layer.
    pub struct OrId / StoredOrId, "or";
}

crate::containers::define_id31! {
    /// Index of an AND node (realized factoring) in the search-space layer.
    pub struct AndId / StoredAndId, "and";
}

crate::containers::define_id31! {
    /// Index of an action in the action pool.
    pub struct ActionId / StoredActionId, "act";
}

crate::containers::define_id31! {
    /// Index of a child-pair entry in the action pair pool.
    pub struct ActionPairId / StoredActionPairId, "ap";
}

crate::containers::define_id31! {
    /// Index of a child in the AND-node child pool.
    pub struct AndChildId / StoredAndChildId, "andc";
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
// Context interner (semi-persistent: AppendOnlyVec + Map)
// ---------------------------------------------------------------------------

/// Interns sorted `AuClassId` vectors as `CtxId` values. Two equal vectors
/// get the same `CtxId`; comparison is then a single integer compare.
pub struct ContextStore {
    /// Each interned context's data as a range `(start, len)` into `classes`.
    spans: AppendOnlyVec<(u32, u32)>,
    /// Pool of class ids (all interned contexts concatenated).
    classes: AppendOnlyVec<AuClassId>,
    /// Deduplication map: sorted class vector -> CtxId (stored as value in the Map log).
    index: Map<Vec<AuClassId>, CtxId>,
}

/// Token for restoring a `ContextStore` to a previous state.
#[derive(Clone, Copy, Debug)]
pub struct ContextStoreToken {
    spans: VecToken,
    classes: VecToken,
    index: MapToken,
}

impl ContextStore {
    pub fn new() -> Self {
        let mut store = ContextStore {
            spans: AppendOnlyVec::new(),
            classes: AppendOnlyVec::new(),
            index: Map::new(),
        };
        store.intern(&[]);
        store
    }

    pub fn empty(&self) -> CtxId {
        CtxId::from_usize(0)
    }

    pub fn intern(&mut self, sorted_classes: &[AuClassId]) -> CtxId {
        if let Some(log_idx) = self.index.id_of(&sorted_classes.to_vec()) {
            return *self.index.get(log_idx);
        }
        let id = CtxId::from_usize(self.spans.len());
        let start = self.classes.len() as u32;
        for &c in sorted_classes {
            self.classes.push(c);
        }
        let len = sorted_classes.len() as u32;
        self.spans.push((start, len));
        self.index.insert(sorted_classes.to_vec(), id);
        id
    }

    #[inline]
    pub fn get(&self, id: CtxId) -> &[AuClassId] {
        let &(start, len) = self.spans.get(id.to_usize());
        let start = start as usize;
        let len = len as usize;
        if len == 0 {
            return &[];
        }
        // Safety: AppendOnlyVec is backed by a contiguous Vec<T>. The elements
        // at positions [start..start+len] were pushed together and remain
        // contiguous. We get a pointer to the first element and extend it.
        unsafe {
            let ptr = self.classes.get(start) as *const AuClassId;
            std::slice::from_raw_parts(ptr, len)
        }
    }

    #[inline]
    pub fn contains(&self, id: CtxId, class: AuClassId) -> bool {
        self.get(id).binary_search(&class).is_ok()
    }

    pub fn len(&self) -> usize {
        self.spans.len()
    }

    pub fn is_empty(&self) -> bool {
        self.spans.is_empty()
    }

    pub fn mark(&mut self) -> ContextStoreToken {
        ContextStoreToken {
            spans: self.spans.mark(ShrinkPolicy::Never),
            classes: self.classes.mark(ShrinkPolicy::Never),
            index: self.index.mark(ShrinkPolicy::Never),
        }
    }

    pub fn restore(&mut self, token: ContextStoreToken) {
        self.index.restore(token.index);
        self.classes.restore(token.classes);
        self.spans.restore(token.spans);
    }
}

impl Default for ContextStore {
    fn default() -> Self {
        Self::new()
    }
}

// ---------------------------------------------------------------------------
// OR arena (semi-persistent: AppendOnlyVec + Map)
// ---------------------------------------------------------------------------

/// The OR-node arena: each node is a subproblem `AU(l, r)` with cycle contexts.
pub struct OrArena {
    pub left: AppendOnlyVec<AuClassId>,
    pub right: AppendOnlyVec<AuClassId>,
    pub left_ctx: AppendOnlyVec<CtxId>,
    pub right_ctx: AppendOnlyVec<CtxId>,
    pub action_start: AppendOnlyVec<u32>,
    pub action_len: AppendOnlyVec<u32>,
    pub terminal: AppendOnlyVec<bool>,
    pub left_best_size: AppendOnlyVec<u32>,
    pub right_best_size: AppendOnlyVec<u32>,
    pub by_key: Map<(AuClassId, AuClassId, CtxId, CtxId), OrId>,
}

/// Token for restoring an `OrArena`.
#[derive(Clone, Copy, Debug)]
pub struct OrArenaToken {
    left: VecToken,
    right: VecToken,
    left_ctx: VecToken,
    right_ctx: VecToken,
    action_start: VecToken,
    action_len: VecToken,
    terminal: VecToken,
    left_best_size: VecToken,
    right_best_size: VecToken,
    by_key: MapToken,
}

impl OrArena {
    pub fn new() -> Self {
        OrArena {
            left: AppendOnlyVec::new(),
            right: AppendOnlyVec::new(),
            left_ctx: AppendOnlyVec::new(),
            right_ctx: AppendOnlyVec::new(),
            action_start: AppendOnlyVec::new(),
            action_len: AppendOnlyVec::new(),
            terminal: AppendOnlyVec::new(),
            left_best_size: AppendOnlyVec::new(),
            right_best_size: AppendOnlyVec::new(),
            by_key: Map::new(),
        }
    }

    pub fn len(&self) -> usize {
        self.left.len()
    }

    pub fn is_empty(&self) -> bool {
        self.left.is_empty()
    }

    pub fn mark(&mut self) -> OrArenaToken {
        OrArenaToken {
            left: self.left.mark(ShrinkPolicy::Never),
            right: self.right.mark(ShrinkPolicy::Never),
            left_ctx: self.left_ctx.mark(ShrinkPolicy::Never),
            right_ctx: self.right_ctx.mark(ShrinkPolicy::Never),
            action_start: self.action_start.mark(ShrinkPolicy::Never),
            action_len: self.action_len.mark(ShrinkPolicy::Never),
            terminal: self.terminal.mark(ShrinkPolicy::Never),
            left_best_size: self.left_best_size.mark(ShrinkPolicy::Never),
            right_best_size: self.right_best_size.mark(ShrinkPolicy::Never),
            by_key: self.by_key.mark(ShrinkPolicy::Never),
        }
    }

    pub fn restore(&mut self, token: OrArenaToken) {
        self.by_key.restore(token.by_key);
        self.right_best_size.restore(token.right_best_size);
        self.left_best_size.restore(token.left_best_size);
        self.terminal.restore(token.terminal);
        self.action_len.restore(token.action_len);
        self.action_start.restore(token.action_start);
        self.right_ctx.restore(token.right_ctx);
        self.left_ctx.restore(token.left_ctx);
        self.right.restore(token.right);
        self.left.restore(token.left);
    }
}

impl Default for OrArena {
    fn default() -> Self {
        Self::new()
    }
}

// ---------------------------------------------------------------------------
// AND arena (semi-persistent: AppendOnlyVec + Map)
// ---------------------------------------------------------------------------

/// The AND-node arena: each node is a realized factoring (parent OR + action).
pub struct AndArena {
    pub parent: AppendOnlyVec<OrId>,
    pub action: AppendOnlyVec<ActionId>,
    pub children_start: AppendOnlyVec<u32>,
    pub children_len: AppendOnlyVec<u32>,
    pub child_or: AppendOnlyVec<OrId>,
    pub child_count: AppendOnlyVec<u32>,
    pub by_parent_action: Map<(OrId, u32), AndId>,
}

/// Token for restoring an `AndArena`.
#[derive(Clone, Copy, Debug)]
pub struct AndArenaToken {
    parent: VecToken,
    action: VecToken,
    children_start: VecToken,
    children_len: VecToken,
    child_or: VecToken,
    child_count: VecToken,
    by_parent_action: MapToken,
}

impl AndArena {
    pub fn new() -> Self {
        AndArena {
            parent: AppendOnlyVec::new(),
            action: AppendOnlyVec::new(),
            children_start: AppendOnlyVec::new(),
            children_len: AppendOnlyVec::new(),
            child_or: AppendOnlyVec::new(),
            child_count: AppendOnlyVec::new(),
            by_parent_action: Map::new(),
        }
    }

    pub fn len(&self) -> usize {
        self.parent.len()
    }

    pub fn is_empty(&self) -> bool {
        self.parent.is_empty()
    }

    pub fn mark(&mut self) -> AndArenaToken {
        AndArenaToken {
            parent: self.parent.mark(ShrinkPolicy::Never),
            action: self.action.mark(ShrinkPolicy::Never),
            children_start: self.children_start.mark(ShrinkPolicy::Never),
            children_len: self.children_len.mark(ShrinkPolicy::Never),
            child_or: self.child_or.mark(ShrinkPolicy::Never),
            child_count: self.child_count.mark(ShrinkPolicy::Never),
            by_parent_action: self.by_parent_action.mark(ShrinkPolicy::Never),
        }
    }

    pub fn restore(&mut self, token: AndArenaToken) {
        self.by_parent_action.restore(token.by_parent_action);
        self.child_count.restore(token.child_count);
        self.child_or.restore(token.child_or);
        self.children_len.restore(token.children_len);
        self.children_start.restore(token.children_start);
        self.action.restore(token.action);
        self.parent.restore(token.parent);
    }
}

impl Default for AndArena {
    fn default() -> Self {
        Self::new()
    }
}

// ---------------------------------------------------------------------------
// SearchSpace: combines the above into one structure
// ---------------------------------------------------------------------------

/// Token for restoring the entire search-space layer.
#[derive(Clone, Copy, Debug)]
pub struct SpaceToken {
    or_arena: OrArenaToken,
    and_arena: AndArenaToken,
    contexts: ContextStoreToken,
}

/// The complete search-space layer shared by all algorithms in a session.
pub struct SearchSpace {
    pub or_arena: OrArena,
    pub and_arena: AndArena,
    pub contexts: ContextStore,
    pub cycle_mode: CycleMode,
}

impl SearchSpace {
    pub fn new(cycle_mode: CycleMode) -> Self {
        SearchSpace {
            or_arena: OrArena::new(),
            and_arena: AndArena::new(),
            contexts: ContextStore::new(),
            cycle_mode,
        }
    }

    /// Look up or create an OR node for the given state. Returns `(OrId, is_new)`.
    pub fn get_or_insert_or_node(
        &mut self,
        l: AuClassId,
        r: AuClassId,
        ctx_l: CtxId,
        ctx_r: CtxId,
        left_best_size: u32,
        right_best_size: u32,
    ) -> (OrId, bool) {
        let key = (l, r, ctx_l, ctx_r);
        if let Some(log_idx) = self.or_arena.by_key.id_of(&key) {
            return (*self.or_arena.by_key.get(log_idx), false);
        }
        let id = OrId::from_usize(self.or_arena.len());
        self.or_arena.left.push(l);
        self.or_arena.right.push(r);
        self.or_arena.left_ctx.push(ctx_l);
        self.or_arena.right_ctx.push(ctx_r);
        self.or_arena.action_start.push(0);
        self.or_arena.action_len.push(0);
        self.or_arena.terminal.push(l == r);
        self.or_arena.left_best_size.push(left_best_size);
        self.or_arena.right_best_size.push(right_best_size);
        self.or_arena.by_key.insert(key, id);
        (id, true)
    }

    /// Derive the child context for one side (§2.3).
    pub fn derive_child_context(
        &mut self,
        parent_ctx: CtxId,
        parent_class: AuClassId,
        is_reachable_from_child: impl Fn(AuClassId) -> bool,
    ) -> CtxId {
        let parent_classes = self.contexts.get(parent_ctx);

        let mut result: Vec<AuClassId> = Vec::new();
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

    /// Check if an action's child pair is blocked by the cycle mode filter.
    pub fn is_cycle_blocked(&self, or_id: OrId, child_l: AuClassId, child_r: AuClassId) -> bool {
        let ctx_l = *self.or_arena.left_ctx.get(or_id.to_usize());
        let ctx_r = *self.or_arena.right_ctx.get(or_id.to_usize());

        if self.contexts.contains(ctx_l, child_l) {
            return true;
        }
        if self.contexts.contains(ctx_r, child_r) {
            return true;
        }

        if self.cycle_mode == CycleMode::CurrentInclusive {
            let l = *self.or_arena.left.get(or_id.to_usize());
            let r = *self.or_arena.right.get(or_id.to_usize());
            if child_l == l || child_r == r {
                return true;
            }
        }

        false
    }

    pub fn mark(&mut self) -> SpaceToken {
        SpaceToken {
            or_arena: self.or_arena.mark(),
            and_arena: self.and_arena.mark(),
            contexts: self.contexts.mark(),
        }
    }

    pub fn restore(&mut self, token: SpaceToken) {
        self.and_arena.restore(token.and_arena);
        self.or_arena.restore(token.or_arena);
        self.contexts.restore(token.contexts);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn context_interner_empty() {
        let store = ContextStore::new();
        assert_eq!(store.empty(), CtxId::from_usize(0));
        assert_eq!(store.get(store.empty()), &[]);
        assert!(!store.contains(store.empty(), AuClassId::from_usize(0)));
    }

    #[test]
    fn context_interner_dedup() {
        let mut store = ContextStore::new();
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
        let mut space = SearchSpace::new(CycleMode::AncestorOnly);
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
        let mut space = SearchSpace::new(CycleMode::AncestorOnly);
        let parent_ctx = space.contexts.empty();
        let parent_class = AuClassId::from_usize(0);

        let child_ctx = space.derive_child_context(parent_ctx, parent_class, |_| false);
        assert_eq!(child_ctx, space.contexts.empty());
    }

    #[test]
    fn derive_child_context_cyclic() {
        let mut space = SearchSpace::new(CycleMode::AncestorOnly);
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
        let mut space = SearchSpace::new(CycleMode::AncestorOnly);
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
        let mut space = SearchSpace::new(CycleMode::CurrentInclusive);
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
        let mut space = SearchSpace::new(CycleMode::AncestorOnly);
        let c0 = AuClassId::from_usize(0);
        let ctx = space.contexts.empty();

        let (or_id, _) = space.get_or_insert_or_node(c0, c0, ctx, ctx, 1, 1);
        assert!(*space.or_arena.terminal.get(or_id.to_usize()));
    }

    #[test]
    fn mark_restore_truncates() {
        let mut space = SearchSpace::new(CycleMode::AncestorOnly);
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
