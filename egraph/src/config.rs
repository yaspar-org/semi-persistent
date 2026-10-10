// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! E-graph configuration trait — bundles all id types for a concrete e-graph.

use crate::containers::{DenseId, IndexLike, PlainFamily, Tagged, TaggedFamily};
use crate::typed_routing::NodeIds;
use core::hash::Hash;

/// Configuration for an e-graph instance.
/// Bundles all id types so the EGraph struct has a single type parameter.
pub trait EGraphConfig: 'static {
    /// Unsigned machine word backing all capacity-coupled DenseIds.
    ///
    /// DenseIds reserve the most-significant bit for inline tagging, so the
    /// payload capacity is one bit less than the word:
    /// * `u32` gives 31 payload bits (`define_id31!` types),
    /// * `u64` gives 63 payload bits (`define_id63!` types).
    ///
    /// Every id whose capacity must scale with the configured e-graph (node
    /// ids, operator ids, per-kind local ids, AU search/pool ids) is
    /// constrained to this word. Intentionally bounded semantic registries
    /// (e.g. rule ids) may remain narrower; each such exception is documented
    /// at its definition.
    /// `Send` on every id family member: the e-graph's mark/restore fan the
    /// member composites out across the rayon pool on disjoint `&mut` borrows
    /// (`EGraph::mark_with`), which requires the members, and so the ids they
    /// store, to cross threads. Every id is a `Copy` machine-word newtype, so
    /// the bound costs nothing to satisfy.
    type Index: IndexLike + Tagged + Send;

    /// Global e-node id (e.g. 31-bit `ENodeId`).
    type G: DenseId<Index = Self::Index> + Hash + Send;
    /// Recycled key into the packed e-class data store. It has the same
    /// payload width as `G`, because the worst case has one class per node.
    type ClassKey: DenseId<Index = Self::Index> + Send;
    /// Operator id. Its own word, not `Index`: the operator count is the program's
    /// declarations, which do not grow with the graph, so every configuration uses the
    /// 31-bit `OpId` (user's decision, 2026-10-05).
    type O: DenseId + Hash + Send;
    /// Sort id, on its own word for the same reason as `O`.
    type S: DenseId + Send;
    /// Interned literal value id.
    type V: DenseId<Index = Self::Index> + Hash + Send;
    /// Use-list id.
    type UL: DenseId<Index = Self::Index> + Send;
    /// Use-list node id.
    type UN: DenseId<Index = Self::Index> + Send;
    /// AC child type (e.g. `(G, Multiplicity)`).
    type C: Tagged + Clone + Copy + Hash + Eq + core::fmt::Debug + Send;
    /// Multiplicity width for AC multiset nodes: `Multiplicity16`,
    /// `Multiplicity`, or `Multiplicity64`.
    ///
    /// Independent of `Index`. A multiplicity counts occurrences of one child
    /// within one AC node, so its domain is that node's child count (bounded by
    /// `for_each_child`'s `1 + 64 * node_count()` cap, i.e. 64·N) — a different
    /// quantity from the id population, and one a caller may want to size
    /// separately. Conversions to and from the `u64` surface width are checked;
    /// see `MultiplicityLike`.
    type M: crate::multiplicity::MultiplicityLike;
    /// Extract the global id from an AC child.
    fn mset_child_id(c: &Self::C) -> Self::G;
    /// Extract the multiplicity from an AC child.
    fn mset_child_mult(c: &Self::C) -> Self::M;
    /// Create an AC child with multiplicity 1.
    fn mset_child_single(g: Self::G) -> Self::C {
        Self::mset_child_with_mult(g, <Self::M as crate::multiplicity::MultiplicityLike>::ONE)
    }
    /// Create an AC child with a given multiplicity.
    fn mset_child_with_mult(g: Self::G, mult: Self::M) -> Self::C;
    /// Increment the multiplicity of an AC child. Returns true if same group.
    ///
    /// Implementations must use [`MultiplicityLike::checked_add`] — the build path
    /// has no error channel here, and a wrapped increment would silently produce a
    /// multiplicity of zero, which the canonical form says cannot exist.
    ///
    /// [`MultiplicityLike::checked_add`]: crate::multiplicity::MultiplicityLike::checked_add
    fn mset_child_merge(existing: &mut Self::C, new_g: Self::G) -> bool;
    /// Local id bundle for the node store.
    type Ids: NodeIds<Index = Self::Index> + Send;
    /// AU search/snapshot/pool id bundle.
    type Au: AuIds<Index = Self::Index>;
    /// Store policy for every tracked column the e-graph owns — the class
    /// layer's columns and the node caches — one of the verified crate's
    /// [`crate::containers::HotFirst`] (first-capture dedupe: the equality
    /// saturation choice, where rewrite rounds touch the same slots many
    /// times per frame) or [`crate::containers::TrailFirst`] (append-only
    /// ingress: the SMT choice, where marks and restores dominate and each
    /// slot is written about once per level). The bounds a policy must meet
    /// are stated once, per use site, as [`StorePolicy`].
    type Policy: 'static;
}

/// The family bounds the verified class layer (`EClasses`) needs of a
/// policy, instantiated at a config's id types. Blanket-implemented, so a
/// use site states one bound: `Cfg::Policy: ClassFamilies<Cfg, TRACK>`.
pub trait ClassFamilies<Cfg: EGraphConfig, const TRACK: bool>:
    TaggedFamily<
        crate::containers::circular_list::CircularListNode<
            crate::containers::Opt<Cfg::ClassKey>,
            Cfg::G,
        >,
        Cfg::Index,
        TRACK,
    > + TaggedFamily<crate::containers::eclasses::ClassData<Cfg::UL, Cfg::G>, Cfg::Index, TRACK>
    + TaggedFamily<Cfg::Index, Cfg::Index, TRACK>
    + TaggedFamily<Cfg::G, Cfg::Index, TRACK>
    + TaggedFamily<u8, Cfg::Index, TRACK>
    + TaggedFamily<crate::union_find::Justification<Cfg::G>, Cfg::Index, TRACK>
    + TaggedFamily<crate::containers::list::ListHead<Cfg::UN>, Cfg::Index, TRACK>
    + TaggedFamily<crate::containers::list::ListNode<Cfg::G, Cfg::UN>, Cfg::Index, TRACK>
    + PlainFamily<crate::containers::Opt<Cfg::G>, usize, TRACK>
{
}

impl<P, Cfg: EGraphConfig, const TRACK: bool> ClassFamilies<Cfg, TRACK> for P where
    P: TaggedFamily<
            crate::containers::circular_list::CircularListNode<
                crate::containers::Opt<Cfg::ClassKey>,
                Cfg::G,
            >,
            Cfg::Index,
            TRACK,
        > + TaggedFamily<crate::containers::eclasses::ClassData<Cfg::UL, Cfg::G>, Cfg::Index, TRACK>
        + TaggedFamily<Cfg::Index, Cfg::Index, TRACK>
        + TaggedFamily<Cfg::G, Cfg::Index, TRACK>
        + TaggedFamily<u8, Cfg::Index, TRACK>
        + TaggedFamily<crate::union_find::Justification<Cfg::G>, Cfg::Index, TRACK>
        + TaggedFamily<crate::containers::list::ListHead<Cfg::UN>, Cfg::Index, TRACK>
        + TaggedFamily<crate::containers::list::ListNode<Cfg::G, Cfg::UN>, Cfg::Index, TRACK>
        + PlainFamily<crate::containers::Opt<Cfg::G>, usize, TRACK>
{
}

/// The family bounds the node caches need of a policy: one per cache column
/// (the ten `nodes` columns and the four `children` pools), in terms of the
/// node types and the local id bundle. Blanket-implemented.
pub trait CacheFamilies<
    G: DenseId,
    O: DenseId,
    V: DenseId,
    C: Tagged,
    I: NodeIds,
    const TRACK: bool,
>:
    TaggedFamily<crate::node_types::FixedArityNode<G, O, 0>, I::L0, TRACK>
    + TaggedFamily<crate::node_types::FixedArityNode<G, O, 1>, I::L1, TRACK>
    + TaggedFamily<crate::node_types::FixedArityNode<G, O, 2>, I::L2, TRACK>
    + TaggedFamily<crate::node_types::FixedArityNode<G, O, 3>, I::L3, TRACK>
    + TaggedFamily<crate::node_types::FixedArityNode<G, O, 2>, I::LSPair, TRACK>
    + TaggedFamily<crate::node_types::VariableArityNode<G, O>, I::LN, TRACK>
    + TaggedFamily<crate::node_types::VariableArityNode<G, O>, I::LSeq, TRACK>
    + TaggedFamily<crate::node_types::VariableArityNode<G, O>, I::LMSet, TRACK>
    + TaggedFamily<crate::node_types::VariableArityNode<G, O>, I::LSet, TRACK>
    + TaggedFamily<G, usize, TRACK>
    + TaggedFamily<C, usize, TRACK>
    + TaggedFamily<crate::node_types::LitNode<G, O, V>, I::LLit, TRACK>
{
}

impl<P, G: DenseId, O: DenseId, V: DenseId, C: Tagged, I: NodeIds, const TRACK: bool>
    CacheFamilies<G, O, V, C, I, TRACK> for P
where
    P: TaggedFamily<crate::node_types::FixedArityNode<G, O, 0>, I::L0, TRACK>
        + TaggedFamily<crate::node_types::FixedArityNode<G, O, 1>, I::L1, TRACK>
        + TaggedFamily<crate::node_types::FixedArityNode<G, O, 2>, I::L2, TRACK>
        + TaggedFamily<crate::node_types::FixedArityNode<G, O, 3>, I::L3, TRACK>
        + TaggedFamily<crate::node_types::FixedArityNode<G, O, 2>, I::LSPair, TRACK>
        + TaggedFamily<crate::node_types::VariableArityNode<G, O>, I::LN, TRACK>
        + TaggedFamily<crate::node_types::VariableArityNode<G, O>, I::LSeq, TRACK>
        + TaggedFamily<crate::node_types::VariableArityNode<G, O>, I::LMSet, TRACK>
        + TaggedFamily<crate::node_types::VariableArityNode<G, O>, I::LSet, TRACK>
        + TaggedFamily<G, usize, TRACK>
        + TaggedFamily<C, usize, TRACK>
        + TaggedFamily<crate::node_types::LitNode<G, O, V>, I::LLit, TRACK>,
{
}

/// Everything the e-graph needs of `Cfg::Policy` at a given `TRACK`: the
/// class-layer and the node-cache families. The one bound every generic
/// use of `EGraph<Cfg, L, TRACK, PROOFS>` states. Blanket-implemented, so
/// `HotFirst` and `TrailFirst` satisfy it for every config.
pub trait StorePolicy<Cfg: EGraphConfig, const TRACK: bool>:
    ClassFamilies<Cfg, TRACK> + CacheFamilies<Cfg::G, Cfg::O, Cfg::V, Cfg::C, Cfg::Ids, TRACK>
{
}

impl<P, Cfg: EGraphConfig, const TRACK: bool> StorePolicy<Cfg, TRACK> for P where
    P: ClassFamilies<Cfg, TRACK> + CacheFamilies<Cfg::G, Cfg::O, Cfg::V, Cfg::C, Cfg::Ids, TRACK>
{
}

/// The five `mset_child_*` bodies for a config whose `C` is
/// [`MSetChild<G, M>`](crate::node_store::MSetChild) — i.e. any config that stores AC
/// children as an id/multiplicity pair. Emitted rather than hand-written per config so the
/// checked increment in `mset_child_merge` cannot drift between configs: a duplicated
/// hand-written impl is where an unchecked `+ 1` can hide.
#[macro_export]
macro_rules! impl_mset_child_pair {
    () => {
        fn mset_child_id(c: &Self::C) -> Self::G {
            c.a
        }
        fn mset_child_mult(c: &Self::C) -> Self::M {
            c.b
        }
        fn mset_child_with_mult(g: Self::G, mult: Self::M) -> Self::C {
            $crate::containers::Pair { a: g, b: mult }
        }
        fn mset_child_merge(existing: &mut Self::C, new_g: Self::G) -> bool {
            use $crate::multiplicity::MultiplicityLike;
            if existing.a == new_g {
                // Checked, not `+ 1`: the build path has no error channel, and a wrapped
                // increment would produce a multiplicity of zero — an entry the canonical
                // form says cannot exist, which the clamps would then silently delete.
                existing.b = existing.b.checked_add(Self::M::ONE).expect(
                    "multiplicity overflow: a duplicated AC child past EGraphConfig::M \
                     (an API contract: the build path coalesces with checked sums)",
                );
                true
            } else {
                false
            }
        }
    };
}

/// Id bundle for the anti-unification subsystem: search-graph identities,
/// snapshot identities, and typed positions into flattened persistent pools.
/// Selected by `EGraphConfig::Au` so a wide e-graph gets wide AU arenas.
pub trait AuIds: 'static {
    /// Backing word; equals the owning config's `Index`.
    /// `Send` on every id family member: the e-graph's mark/restore fan the
    /// member composites out across the rayon pool on disjoint `&mut` borrows
    /// (`EGraph::mark_with`), which requires the members, and so the ids they
    /// store, to cross threads. Every id is a `Copy` machine-word newtype, so
    /// the bound costs nothing to satisfy.
    type Index: IndexLike + Tagged + Send;

    // --- Direct identities ---
    /// Dense live-class index inside one AU snapshot.
    type Class: DenseId<Index = Self::Index> + Hash;
    /// Strongly connected component index in the snapshot's class graph.
    type Scc: DenseId<Index = Self::Index>;
    /// OR node (subproblem) in the search space.
    type Or: DenseId<Index = Self::Index> + Hash;
    /// Cached action list in the action cache.
    type Action: DenseId<Index = Self::Index>;
    /// Interned cycle context.
    type Context: DenseId<Index = Self::Index> + Hash;
    /// Hash-consed result term.
    type Term: DenseId<Index = Self::Index> + Hash;
    /// MCGS OR-statistics entry.
    type OrStats: DenseId<Index = Self::Index>;
    /// MCGS AND-statistics entry.
    type AndStats: DenseId<Index = Self::Index>;

    // --- Typed positions into flattened persistent pools ---
    /// Position in the snapshot's flattened member pool.
    type SnapshotMember: DenseId<Index = Self::Index>;
    /// Position in the context interner's class pool.
    type ContextElem: DenseId<Index = Self::Index>;
    /// Position in the term pool's child pool.
    type TermChild: DenseId<Index = Self::Index>;
    /// Position in the reachability bit-block pool.
    type ReachBlock: DenseId<Index = Self::Index>;
    /// Position in the flattened MCGS OR-edge statistics pools.
    type OrEdgeStat: DenseId<Index = Self::Index>;
    /// Position in the flattened MCGS AND-child statistics pools.
    type AndChildStat: DenseId<Index = Self::Index>;
}
