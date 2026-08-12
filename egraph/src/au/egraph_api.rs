// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Read-only snapshot of a frozen e-graph for anti-unification (§4.1).
//!
//! Owns: dense class numbering, per-class members grouped by operator, best-term
//! sizes (§A.2), SCC-based reachability bitsets (§2.4).
//! Borrows: the e-graph reference for node-level reads (op, children, flags).

use super::{AuError, Span};
use crate::canon::{MSetCanon, VarCanon};
use crate::config::{AuIds, EGraphConfig};
use crate::containers::{DenseId, IndexLike};
use crate::egraph::EGraph;
use crate::literal::LitVal;
use crate::multiplicity::MultiplicityLike;
use crate::node_types::FLAG_SUBSUMED;

/// Class id projected from a config's AU family.
pub type ClassOf<Cfg> = <<Cfg as EGraphConfig>::Au as AuIds>::Class;
/// SCC id projected from a config's AU family.
pub type SccOf<Cfg> = <<Cfg as EGraphConfig>::Au as AuIds>::Scc;

// `ClassMembers` and `MemberNode` used to sit here, describing per-class membership
// as `Vec<(O, u32)>` plus a `u32` child count. Both were dead — nothing in the crate
// ever constructed or read either one — and both had the wrong widths: the `u32` was
// documented as a *global e-node id*, which is `Cfg::G` and does not fit 32 bits in a
// 63-bit session, and the child count is a node arity (a span in the child pool, so
// `Cfg::Index`-wide). The live path was already correct and stays: `members()` returns
// `&[(Cfg::O, Cfg::G)]` out of `member_pool`, spans into it are `member_spans`, and
// arities are read from the node itself. Removed rather than widened so that nobody
// reaches for the plausible-looking struct instead.

/// Immutable snapshot built once from a frozen e-graph. The search operates on this.
pub struct AuSnapshot<'eg, Cfg: EGraphConfig, L: LitVal, const T: bool, const P: bool>
where
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
{
    pub(crate) eg: &'eg EGraph<Cfg, L, T, P>,
    /// Dense representative -> ClassOf<Cfg> map (representative global ids only).
    repr_to_au: hashbrown::HashMap<Cfg::G, ClassOf<Cfg>>,
    /// ClassOf<Cfg> -> representative global id.
    pub(crate) au_to_repr: Vec<Cfg::G>,
    /// Per-class member list: `members[class]` is a range into `member_pool`.
    member_spans: Vec<Span<<Cfg::Au as AuIds>::SnapshotMember>>,
    /// All admissible members across all classes: (op, global_id).
    member_pool: Vec<(Cfg::O, Cfg::G)>,
    /// Best (minimum) size of any finite member in each class.
    best_size: Vec<u32>,
    /// Global id of the best (cheapest) member per class.
    best_node: Vec<Option<Cfg::G>>,
    /// Reachability data: which class is reachable from which.
    reach: Reachability<Cfg::Au>,
}

/// SCC-condensed reachability (§2.4): Tarjan SCCs, one bitset per SCC.
#[derive(Debug, Clone)]
pub struct Reachability<A: AuIds> {
    /// class -> SCC index.
    class_to_scc: Vec<A::Scc>,
    /// Per-SCC: typed span into `bit_blocks`.
    scc_spans: Vec<Span<A::ReachBlock>>,
    /// Packed bit blocks (one dense bitset per SCC, each `ceil(num_classes/64)` u64s).
    bit_blocks: Vec<u64>,
    /// Number of classes (determines bitset width).
    num_classes: u64,
}

impl<A: AuIds> Reachability<A> {
    /// Does class `target` belong to `reach(source)`?
    #[inline]
    pub fn is_reachable(&self, source: A::Class, target: A::Class) -> bool {
        let scc = self.class_to_scc[source.to_usize()];
        let start = self.scc_spans[scc.to_usize()].start_usize();
        let t = target.to_usize();
        let word = start + t / 64;
        let bit = t % 64;
        (self.bit_blocks[word] >> bit) & 1 != 0
    }

    /// Number of classes in this reachability table.
    pub fn num_classes(&self) -> u64 {
        self.num_classes
    }
}

impl<'eg, Cfg: EGraphConfig, L: LitVal, const T: bool, const P: bool> AuSnapshot<'eg, Cfg, L, T, P>
where
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
{
    /// Build a snapshot from the frozen e-graph. The e-graph must not be mutated
    /// while this snapshot is alive (enforced by the shared reference lifetime).
    pub fn new(eg: &'eg EGraph<Cfg, L, T, P>) -> Result<Self, AuError> {
        // --- Step 1: collect live class representatives ---
        let n = eg.len();
        let mut repr_to_au: hashbrown::HashMap<Cfg::G, ClassOf<Cfg>> =
            hashbrown::HashMap::with_capacity(n / 2);
        let mut au_to_repr: Vec<Cfg::G> = Vec::new();

        // Discover representatives by scanning all nodes. Some nodes may have
        // the same representative; HashMap deduplicates.
        for id in eg.node_ids() {
            let repr = eg.find_const(id);
            repr_to_au.entry(repr).or_insert_with(|| {
                // Checked: this is the one place snapshot class ids are minted, and nothing
                // ties `ClassOf<Cfg>`'s id space to `Cfg::G`'s. One class per distinct
                // representative bounds the count by the node count, but only the shipped
                // configs happen to pair equal-width families (31/31, 63/63) — a config that
                // narrowed the AU family would mask here, and two representatives would
                // answer to one class id for the whole search.
                let au = crate::id::id_at::<ClassOf<Cfg>>(au_to_repr.len());
                au_to_repr.push(repr);
                au
            });
        }

        let num_classes = au_to_repr.len();

        // --- Step 2: per-class members grouped by op (excluding FLAG_SUBSUMED) ---
        // First pass: collect per-class member lists.
        let mut class_members: Vec<Vec<(Cfg::O, Cfg::G)>> = vec![Vec::new(); num_classes];

        for id in eg.node_ids() {
            let flags = eg.node_flags(id);
            if flags & FLAG_SUBSUMED != 0 {
                continue;
            }
            let repr = eg.find_const(id);
            let au_class = repr_to_au[&repr];
            let op = eg.node_op(id);
            class_members[au_class.to_usize()].push((op, id));
        }

        // Sort each class's members by op for grouped access.
        for members in &mut class_members {
            members.sort_by_key(|&(op, _)| op.to_usize());
        }

        // Flatten into member_pool + spans.
        let total_members: usize = class_members.iter().map(|m| m.len()).sum();
        let mut member_pool: Vec<(Cfg::O, Cfg::G)> = Vec::with_capacity(total_members);
        let mut member_spans: Vec<Span<<Cfg::Au as AuIds>::SnapshotMember>> =
            Vec::with_capacity(num_classes);

        for members in &class_members {
            let start = member_pool.len();
            member_pool.extend_from_slice(members);
            member_spans.push(Span::new(start, members.len()));
        }

        // --- Step 3: best-term fixpoint (§A.2) ---
        let (best_size, best_node) = Self::compute_best_terms(eg, &repr_to_au, num_classes)?;

        // --- Step 4: reachability (§2.4) ---
        let reach = Self::compute_reachability(eg, &repr_to_au, &au_to_repr, num_classes);

        Ok(AuSnapshot {
            eg,
            repr_to_au,
            au_to_repr,
            member_spans,
            member_pool,
            best_size,
            best_node,
            reach,
        })
    }

    // --- Public API ---

    /// Number of live classes in this snapshot.
    pub fn num_classes(&self) -> usize {
        self.au_to_repr.len()
    }

    /// SpMap a representative global id to its dense class id.
    /// Returns `None` if the id is not a representative in this snapshot.
    #[inline]
    pub fn class_id(&self, repr: Cfg::G) -> Option<ClassOf<Cfg>> {
        self.repr_to_au.get(&repr).copied()
    }

    /// SpMap a global id (not necessarily a representative) to its dense class id.
    #[inline]
    pub fn class_of(&self, id: Cfg::G) -> Option<ClassOf<Cfg>> {
        let repr = self.eg.find_const(id);
        self.repr_to_au.get(&repr).copied()
    }

    /// The representative global id for a dense class id.
    #[inline]
    pub fn repr(&self, au: ClassOf<Cfg>) -> Cfg::G {
        self.au_to_repr[au.to_usize()]
    }

    /// The best (smallest) member size for class `au`.
    #[inline]
    pub fn best_size(&self, au: ClassOf<Cfg>) -> u32 {
        self.best_size[au.to_usize()]
    }

    /// The global id of the best member for class `au`.
    ///
    /// # Panics
    /// Panics if `au` has no admissible finite member. Callers operating on
    /// auxiliary classes must check [`Self::has_finite_member`] first.
    #[inline]
    pub fn best_node(&self, au: ClassOf<Cfg>) -> Cfg::G {
        self.best_node[au.to_usize()]
            .expect("best_node requested for a class without an admissible finite member")
    }

    /// Iterator over `(op, global_id)` pairs for all admissible members of `au`.
    #[inline]
    pub fn members(&self, au: ClassOf<Cfg>) -> &[(Cfg::O, Cfg::G)] {
        let span = self.member_spans[au.to_usize()];
        &self.member_pool[span.start_usize()..span.end_usize()]
    }

    /// The reachability table.
    #[inline]
    pub fn reachability(&self) -> &Reachability<Cfg::Au> {
        &self.reach
    }

    /// The e-graph reference (for node-level queries like op, children, etc.).
    #[inline]
    pub fn egraph(&self) -> &'eg EGraph<Cfg, L, T, P> {
        self.eg
    }

    /// Operator of a global e-node id.
    #[inline]
    pub fn node_op(&self, id: Cfg::G) -> Cfg::O {
        self.eg.node_op(id)
    }

    /// Whether this class has an admissible finite member (§A.2 fixpoint resolved it).
    /// A class is infinite when every admissible member references the class itself
    /// (e.g. its only finite leaf was subsumed).
    #[inline]
    pub fn has_finite_member(&self, au: ClassOf<Cfg>) -> bool {
        self.best_size[au.to_usize()] != u32::MAX
    }

    /// Validate that `root` and every class reachable from it has a finite member
    /// (§4.1: `AuError::NoFiniteRepresentative` if any class needed by a root has no
    /// admissible finite member). Called once per root before a search starts.
    pub fn validate_finite_from(&self, root: ClassOf<Cfg>) -> Result<(), AuError> {
        if !self.has_finite_member(root) {
            return Err(AuError::NoFiniteRepresentative(root.to_usize() as u64));
        }
        // `au_to_repr` was filled through a checked mint, so its length is inside the
        // class id space and these positions all name a class.
        for c in crate::id::ids_upto::<ClassOf<Cfg>>(self.num_classes()) {
            if self.reach.is_reachable(root, c) && !self.has_finite_member(c) {
                return Err(AuError::NoFiniteRepresentative(c.to_usize() as u64));
            }
        }
        Ok(())
    }

    /// Whether the canonical node kind of `op` is commutative (SPair, MSet, Set):
    /// result-term children for such operators are sorted into canonical order,
    /// while ordered operators preserve positional order.
    /// The identity (unit) element's ClassOf<Cfg> for an operator, if the operator
    /// has a declared identity (e.g. `true` for `and`, `false` for `or`, `0` for `+`).
    /// Returns `None` if no identity is declared, the identity node is not in a live
    /// class, or that class has no admissible finite representative. The last check is
    /// required because identity padding materializes the representative in projections;
    /// a subsumed-only identity class must not be injected as an auxiliary child.
    pub fn op_identity_class(&self, op: Cfg::O) -> Option<ClassOf<Cfg>> {
        let unit_node = self.eg.unit_node(op)?;
        let class = self.class_of(unit_node)?;
        self.has_finite_member(class).then_some(class)
    }

    pub fn op_is_commutative(&self, op: Cfg::O) -> bool {
        matches!(
            self.eg.ops().info(op).canon_class(),
            crate::id::ENodeKind::SPair | crate::id::ENodeKind::MSet | crate::id::ENodeKind::Set
        )
    }

    // --- Private implementation ---

    /// Best-term fixpoint: cost = 1 + sum(mult * cost(class(child))) per node,
    /// minimized per class (§A.2). Returns (best_size, best_node) vectors indexed
    /// by ClassOf<Cfg>.
    ///
    /// `u32::MAX` is the *sentinel* for "this class has no finite representative
    /// yet" ([`has_finite_member`](Self::has_finite_member) tests exactly that), so
    /// no finite cost may ever equal it. The summation therefore runs in `u64` with
    /// checked steps and a node is dropped as a candidate unless its total lands
    /// strictly below the sentinel. Saturating into `u32::MAX` instead would make a
    /// large-but-finite term indistinguishable from an absent one: the class would
    /// report no finite member, and — because `total < best_size` is false when both
    /// are the sentinel — would never even record a `best_node`.
    fn compute_best_terms(
        eg: &EGraph<Cfg, L, T, P>,
        repr_to_au: &hashbrown::HashMap<Cfg::G, ClassOf<Cfg>>,
        num_classes: usize,
    ) -> Result<(Vec<u32>, Vec<Option<Cfg::G>>), AuError> {
        let mut best_size: Vec<u32> = vec![u32::MAX; num_classes];
        let mut best_node: Vec<Option<Cfg::G>> = vec![None; num_classes];

        loop {
            let mut changed = false;
            for id in eg.node_ids() {
                let flags = eg.node_flags(id);
                if flags & FLAG_SUBSUMED != 0 {
                    continue;
                }
                let repr = eg.find_const(id);
                let au_class = match repr_to_au.get(&repr) {
                    Some(&c) => c,
                    None => continue,
                };

                // Widened so the sentinel cannot be reached by arithmetic; an
                // overflow drops the node from consideration, which costs nothing
                // real — a term of more than 2^32 - 2 nodes cannot be materialized.
                let mut total: u64 = 1;
                let mut ok = true;
                eg.for_each_child(id, |child, mult| {
                    if !ok {
                        return;
                    }
                    let child_repr = eg.find_const(child);
                    match repr_to_au.get(&child_repr) {
                        Some(&child_au) => {
                            let child_cost = best_size[child_au.to_usize()];
                            if child_cost == u32::MAX {
                                ok = false;
                            } else {
                                match u64::from(child_cost)
                                    .checked_mul(mult.to_u64())
                                    .and_then(|c| total.checked_add(c))
                                {
                                    Some(t) => total = t,
                                    None => ok = false,
                                }
                            }
                        }
                        None => {
                            ok = false;
                        }
                    }
                });
                // Strictly below the sentinel, so a recorded size always means
                // "finite representative of exactly this many nodes".
                if !ok || total >= u64::from(u32::MAX) {
                    continue;
                }
                let total = total as u32;

                if total < best_size[au_class.to_usize()] {
                    best_size[au_class.to_usize()] = total;
                    best_node[au_class.to_usize()] = Some(id);
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }

        Ok((best_size, best_node))
    }

    /// Compute SCC-based reachability (§2.4):
    /// 1. Tarjan SCC over the class graph (edge = class -> class of each child)
    /// 2. Bitset union in reverse topological order
    fn compute_reachability(
        eg: &EGraph<Cfg, L, T, P>,
        repr_to_au: &hashbrown::HashMap<Cfg::G, ClassOf<Cfg>>,
        au_to_repr: &[Cfg::G],
        num_classes: usize,
    ) -> Reachability<Cfg::Au> {
        let words_per_scc = num_classes.div_ceil(64);

        // Build adjacency: class -> set of successor classes.
        let mut adj: Vec<Vec<ClassOf<Cfg>>> = vec![Vec::new(); num_classes];
        for id in eg.node_ids() {
            let flags = eg.node_flags(id);
            if flags & FLAG_SUBSUMED != 0 {
                continue;
            }
            let repr = eg.find_const(id);
            let src = match repr_to_au.get(&repr) {
                Some(&c) => c,
                None => continue,
            };
            eg.for_each_child(id, |child, _mult| {
                let child_repr = eg.find_const(child);
                if let Some(&dst) = repr_to_au.get(&child_repr) {
                    adj[src.to_usize()].push(dst);
                }
            });
        }

        // Deduplicate adjacency (important for performance and correctness of SCC sizes).
        for neighbors in &mut adj {
            neighbors.sort_unstable();
            neighbors.dedup();
        }

        // --- Tarjan's SCC algorithm ---
        //
        // Every counter below is a position in the class population, so all of them are
        // `Cfg::Index` — the word that population is pinned to — rather than a literal
        // `u32`. At a 63-bit config the class count passes four billion, and each of
        // these was a silent wrap there, not a clean failure: the discovery counter would
        // restart at zero and hand two classes the same discovery index, which makes
        // Tarjan report SCCs that are not SCCs. The reachability bitsets built from them
        // are what admissibility and `validate_finite_from` consult, so the damage would
        // surface as confident, wrong anti-unification results rather than an error.
        //
        // `undefined` is the "not yet visited" marker for `node_index`, kept as a
        // sentinel rather than an `Option` so the column stays one word per class. Its
        // distinctness is checked once, below, instead of being argued from the id family:
        // it holds for any bit-stealing id (whose `id_bound()` is half the word) but a
        // full-range index type would have no value to spare, and that deserves to fail
        // loudly at the top rather than alias a real discovery index at the very end.
        let undefined = <Cfg::Index as IndexLike>::max();
        assert!(
            num_classes < undefined.as_usize(),
            "AU snapshot has {num_classes} classes, leaving EGraphConfig::Index no value \
             to spare for Tarjan's `undefined` marker; configure a wider index word"
        );
        let zero = <Cfg::Index as IndexLike>::min();
        let mut index_counter = zero;
        let mut stack: Vec<ClassOf<Cfg>> = Vec::new();
        let mut on_stack: Vec<bool> = vec![false; num_classes];
        let mut node_index: Vec<Cfg::Index> = vec![undefined; num_classes];
        let mut node_lowlink: Vec<Cfg::Index> = vec![zero; num_classes];
        // Filler until Tarjan assigns each class its real SCC. Id 0 exists in every id
        // family, so this mint cannot be out of range.
        let mut class_to_scc: Vec<SccOf<Cfg>> = vec![<SccOf<Cfg>>::from_usize(0); num_classes];
        let mut scc_members: Vec<Vec<ClassOf<Cfg>>> = Vec::new();

        // One discovery index per class, so the assert above bounds this; the `expect` is
        // unreachable and says which invariant would have to break first.
        let bump = |c: Cfg::Index| {
            crate::containers::index_like::checked_incr(c).expect(
                "Tarjan discovery counter passed EGraphConfig::Index; \
                         it is bounded by the class count, checked above",
            )
        };

        // Iterative Tarjan to avoid stack overflow on deep graphs.
        #[derive(Clone, Copy)]
        struct TarjanFrame<C, I> {
            node: C,
            /// Cursor into the node's deduplicated adjacency, which is bounded by the
            /// class count — hence the config's index word, not a fixed one.
            neighbor_idx: I,
        }

        // Checked once for the whole walk, not per class: the classes were minted checked
        // in `new`, so this only re-states that here rather than trusting it.
        for start_id in crate::id::ids_upto::<ClassOf<Cfg>>(num_classes) {
            let start = start_id.to_usize();
            if node_index[start] != undefined {
                continue;
            }

            let mut call_stack: Vec<TarjanFrame<ClassOf<Cfg>, Cfg::Index>> = Vec::new();
            // Initialize the start node.
            node_index[start] = index_counter;
            node_lowlink[start] = index_counter;
            index_counter = bump(index_counter);
            on_stack[start] = true;
            stack.push(start_id);
            call_stack.push(TarjanFrame {
                node: start_id,
                neighbor_idx: zero,
            });

            while let Some(frame) = call_stack.last_mut() {
                let v = frame.node;
                let vi = v.to_usize();
                let neighbors = &adj[vi];

                if frame.neighbor_idx.as_usize() < neighbors.len() {
                    let w = neighbors[frame.neighbor_idx.as_usize()];
                    frame.neighbor_idx = bump(frame.neighbor_idx);
                    let wi = w.to_usize();

                    if node_index[wi] == undefined {
                        // Not yet visited: push a new frame.
                        node_index[wi] = index_counter;
                        node_lowlink[wi] = index_counter;
                        index_counter = bump(index_counter);
                        on_stack[wi] = true;
                        stack.push(w);
                        call_stack.push(TarjanFrame {
                            node: w,
                            neighbor_idx: zero,
                        });
                    } else if on_stack[wi] {
                        node_lowlink[vi] = node_lowlink[vi].min(node_index[wi]);
                    }
                } else {
                    // All neighbors processed: check if this is a root.
                    if node_lowlink[vi] == node_index[vi] {
                        // Checked: one SCC per class at worst, but `SccOf<Cfg>` is its own
                        // id family and nothing bounds it by the class count. Masking here
                        // would merge two SCCs under one id, and `class_to_scc` feeds the
                        // reachability bitsets — the damage reads as confident wrong AU
                        // results, not an error.
                        let scc_id = crate::id::id_at::<SccOf<Cfg>>(scc_members.len());
                        let mut members = Vec::new();
                        loop {
                            let w = stack.pop().unwrap();
                            on_stack[w.to_usize()] = false;
                            class_to_scc[w.to_usize()] = scc_id;
                            members.push(w);
                            if w == v {
                                break;
                            }
                        }
                        scc_members.push(members);
                    }
                    // Pop and propagate lowlink to parent.
                    let popped = call_stack.pop().unwrap();
                    if let Some(parent) = call_stack.last() {
                        let pi = parent.node.to_usize();
                        node_lowlink[pi] =
                            node_lowlink[pi].min(node_lowlink[popped.node.to_usize()]);
                    }
                }
            }
        }

        let num_sccs = scc_members.len();

        // --- Build SCC DAG adjacency (for reverse topological order) ---
        let mut scc_adj: Vec<Vec<SccOf<Cfg>>> = vec![Vec::new(); num_sccs];
        for (src_class, neighbors) in adj.iter().enumerate() {
            let src_scc = class_to_scc[src_class];
            for &dst_class in neighbors {
                let dst_scc = class_to_scc[dst_class.to_usize()];
                if src_scc != dst_scc {
                    scc_adj[src_scc.to_usize()].push(dst_scc);
                }
            }
        }
        for neighbors in &mut scc_adj {
            neighbors.sort_unstable();
            neighbors.dedup();
        }

        // --- Reverse topological order via Kahn's algorithm ---
        // In-degree in the condensed DAG: bounded by the SCC count, itself bounded by the
        // class count, so this follows `Cfg::Index` for the same reason the Tarjan
        // counters do. The increment is checked; a wrap here would drop an SCC from the
        // topological order and leave its reachability bitset unfilled.
        let mut in_degree: Vec<Cfg::Index> = vec![zero; num_sccs];
        for neighbors in &scc_adj {
            for &dst in neighbors {
                in_degree[dst.to_usize()] = bump(in_degree[dst.to_usize()]);
            }
        }
        let mut topo_order: Vec<SccOf<Cfg>> = Vec::with_capacity(num_sccs);
        let mut queue: std::collections::VecDeque<SccOf<Cfg>> = std::collections::VecDeque::new();
        // Each SCC id came from the checked mint above, so `num_sccs` is inside the id
        // space and every position below it names one.
        for (i, scc) in crate::id::ids_upto::<SccOf<Cfg>>(num_sccs).enumerate() {
            if in_degree[i] == zero {
                queue.push_back(scc);
            }
        }
        while let Some(scc) = queue.pop_front() {
            topo_order.push(scc);
            for &dst in &scc_adj[scc.to_usize()] {
                // Checked: Kahn's only decrements an in-degree it just accounted for by
                // removing an edge, so it is positive here. An underflow would wrap to
                // the top of the word and hang the drain instead of ever reaching zero.
                in_degree[dst.to_usize()] =
                    crate::containers::index_like::checked_decr(in_degree[dst.to_usize()])
                        .expect("Kahn's decremented an in-degree already at zero");
                if in_degree[dst.to_usize()] == zero {
                    queue.push_back(dst);
                }
            }
        }
        // Reverse: leaves first (process in reverse topological = leaves before roots).
        topo_order.reverse();

        // --- Bitset union in reverse topological order ---
        let mut bit_blocks: Vec<u64> = vec![0u64; num_sccs * words_per_scc];
        let mut scc_spans: Vec<Span<<Cfg::Au as AuIds>::ReachBlock>> = Vec::with_capacity(num_sccs);
        for i in 0..num_sccs {
            scc_spans.push(Span::new(i * words_per_scc, words_per_scc));
        }

        // Process in reverse topological order (leaves first).
        for &scc in &topo_order {
            let si = scc.to_usize();

            // If the SCC is cyclic (size > 1), add own members to reach set.
            let is_cyclic = scc_members[si].len() > 1
                || (scc_members[si].len() == 1 && {
                    let c = scc_members[si][0];
                    adj[c.to_usize()].contains(&c)
                });

            if is_cyclic {
                for &member in &scc_members[si] {
                    let bit = member.to_usize();
                    let word = scc_spans[si].start_usize() + bit / 64;
                    bit_blocks[word] |= 1u64 << (bit % 64);
                }
            }

            // Add successor SCCs' classes to this SCC's bitset.
            // First, add successor SCC members (the classes themselves).
            for &dst_scc in &scc_adj[si] {
                for &member in &scc_members[dst_scc.to_usize()] {
                    let bit = member.to_usize();
                    let word = scc_spans[si].start_usize() + bit / 64;
                    bit_blocks[word] |= 1u64 << (bit % 64);
                }
            }

            // Union successor SCCs' reach sets.
            for &dst_scc in &scc_adj[si] {
                let dst_start = scc_spans[dst_scc.to_usize()].start_usize();
                let src_start = scc_spans[si].start_usize();
                for w in 0..words_per_scc {
                    bit_blocks[src_start + w] |= bit_blocks[dst_start + w];
                }
            }
        }

        // Unused variable suppression.
        let _ = au_to_repr;

        Reachability {
            class_to_scc,
            scc_spans,
            bit_blocks,
            num_classes: num_classes as u64,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::egraph::EGraph31;
    use crate::literal::NiraLitVal;

    /// Build a small e-graph with a cycle: f(x) where x = f(x) (via merge).
    /// This creates a self-loop class, letting us test reachability on cycles.
    #[test]
    fn reachability_self_loop() {
        let mut eg = EGraph31::<NiraLitVal, false, false>::new();
        let int = eg.intern_sort("Int");
        let x_op = eg.register_op0("x", int);
        let f_op = eg.register_op1("f", int, int);

        let x = eg.add(x_op, &[]);
        let fx = eg.add(f_op, &[x]);
        // merge x and f(x): now class(x) = class(f(x)), creating a self-loop.
        eg.merge(x, fx);
        eg.rebuild();

        let snap = AuSnapshot::new(&eg).unwrap();
        let x_class = snap.class_of(x).unwrap();

        // x's class reaches itself (self-loop via f).
        assert!(snap.reachability().is_reachable(x_class, x_class));
    }

    /// Linear chain: a -> f(a) -> g(f(a)). No cycles. Reachability is transitive.
    #[test]
    fn reachability_linear_chain() {
        let mut eg = EGraph31::<NiraLitVal, false, false>::new();
        let int = eg.intern_sort("Int");
        let a_op = eg.register_op0("a", int);
        let f_op = eg.register_op1("f", int, int);
        let g_op = eg.register_op1("g", int, int);

        let a = eg.add(a_op, &[]);
        let fa = eg.add(f_op, &[a]);
        let gfa = eg.add(g_op, &[fa]);
        eg.rebuild();

        let snap = AuSnapshot::new(&eg).unwrap();
        let a_class = snap.class_of(a).unwrap();
        let fa_class = snap.class_of(fa).unwrap();
        let gfa_class = snap.class_of(gfa).unwrap();

        // All 3 are different classes.
        assert_ne!(a_class, fa_class);
        assert_ne!(fa_class, gfa_class);

        // gfa reaches fa and a.
        assert!(snap.reachability().is_reachable(gfa_class, fa_class));
        assert!(snap.reachability().is_reachable(gfa_class, a_class));

        // fa reaches a.
        assert!(snap.reachability().is_reachable(fa_class, a_class));

        // a reaches nothing.
        assert!(!snap.reachability().is_reachable(a_class, fa_class));
        assert!(!snap.reachability().is_reachable(a_class, gfa_class));
    }

    /// Two-node cycle: x = f(y), y = g(x). Both reach each other.
    #[test]
    fn reachability_mutual_cycle() {
        let mut eg = EGraph31::<NiraLitVal, false, false>::new();
        let int = eg.intern_sort("Int");
        let x_op = eg.register_op0("x", int);
        let y_op = eg.register_op0("y", int);
        let f_op = eg.register_op1("f", int, int);
        let g_op = eg.register_op1("g", int, int);

        let x = eg.add(x_op, &[]);
        let y = eg.add(y_op, &[]);
        let fx = eg.add(f_op, &[y]); // f(y)
        let gy = eg.add(g_op, &[x]); // g(x)

        // merge: x = f(y), y = g(x)
        eg.merge(x, fx);
        eg.merge(y, gy);
        eg.rebuild();

        let snap = AuSnapshot::new(&eg).unwrap();
        let x_class = snap.class_of(x).unwrap();
        let y_class = snap.class_of(y).unwrap();

        // x reaches y and y reaches x (mutual cycle).
        assert!(snap.reachability().is_reachable(x_class, y_class));
        assert!(snap.reachability().is_reachable(y_class, x_class));
        // Both reach themselves.
        assert!(snap.reachability().is_reachable(x_class, x_class));
        assert!(snap.reachability().is_reachable(y_class, y_class));
    }

    /// Best-size computation: leaf costs 1, f(leaf) costs 2.
    #[test]
    fn best_size_basic() {
        let mut eg = EGraph31::<NiraLitVal, false, false>::new();
        let int = eg.intern_sort("Int");
        let a_op = eg.register_op0("a", int);
        let f_op = eg.register_op1("f", int, int);

        let a = eg.add(a_op, &[]);
        let fa = eg.add(f_op, &[a]);
        eg.rebuild();

        let snap = AuSnapshot::new(&eg).unwrap();
        let a_class = snap.class_of(a).unwrap();
        let fa_class = snap.class_of(fa).unwrap();

        assert_eq!(snap.best_size(a_class), 1);
        assert_eq!(snap.best_size(fa_class), 2);
    }

    /// Best-size with AC multiplicities: plus(a, a) costs 1 + 2*1 = 3.
    #[test]
    fn best_size_ac_multiplicity() {
        let mut eg = EGraph31::<NiraLitVal, false, false>::new();
        let int = eg.intern_sort("Int");
        let a_op = eg.register_op0("a", int);
        let plus_op = eg.register_mset("plus", int, int);

        let a = eg.add(a_op, &[]);
        let plus_aa = eg.add(plus_op, &[a, a]);
        eg.rebuild();

        let snap = AuSnapshot::new(&eg).unwrap();
        let a_class = snap.class_of(a).unwrap();
        let plus_class = snap.class_of(plus_aa).unwrap();

        assert_eq!(snap.best_size(a_class), 1);
        // plus(a^2): 1 + 2*1 = 3
        assert_eq!(snap.best_size(plus_class), 3);
    }

    /// Members exclude FLAG_SUBSUMED nodes.
    #[test]
    fn members_exclude_subsumed() {
        let mut eg = EGraph31::<NiraLitVal, false, false>::new();
        let int = eg.intern_sort("Int");
        let a_op = eg.register_op0("a", int);
        let b_op = eg.register_op0("b", int);

        let a = eg.add(a_op, &[]);
        let b = eg.add(b_op, &[]);
        // merge a and b so they share a class, then subsume b.
        eg.merge(a, b);
        eg.rebuild();
        eg.subsume(b);

        let snap = AuSnapshot::new(&eg).unwrap();
        let class = snap.class_of(a).unwrap();
        let members = snap.members(class);

        // One member should be excluded (the subsumed one).
        assert_eq!(members.len(), 1);
    }

    /// Snapshot provides correct class count.
    #[test]
    fn num_classes_correct() {
        let mut eg = EGraph31::<NiraLitVal, false, false>::new();
        let int = eg.intern_sort("Int");
        let a_op = eg.register_op0("a", int);
        let b_op = eg.register_op0("b", int);
        let c_op = eg.register_op0("c", int);

        let a = eg.add(a_op, &[]);
        let b = eg.add(b_op, &[]);
        let _c = eg.add(c_op, &[]);
        eg.rebuild();
        // 3 distinct classes.
        let snap = AuSnapshot::new(&eg).unwrap();
        assert_eq!(snap.num_classes(), 3);

        // merge a and b -> 2 classes.
        drop(snap);
        eg.merge(a, b);
        eg.rebuild();
        let snap2 = AuSnapshot::new(&eg).unwrap();
        assert_eq!(snap2.num_classes(), 2);
    }
}
