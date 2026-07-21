# Anti-Unification: Associative (Seq) Operators, and Other Remaining Work

**Status**: design for future work. Except where explicitly marked as delivered
(§5), nothing in this document is implemented. The implemented anti-unification
system is documented in
[`doc/design/19-anti-unification.md`](../design/19-anti-unification.md); section
references of the form §N below point into that chapter.

The main body designs structural factoring for associative (Seq) operators with
unequal-length members. A closing section (§5) collects the other deferred
anti-unification work items so they live in one place.

## 1. Current state

Associative operators are stored as variadic ordered sequences (`Seq` canon kind).
Action generation for a Seq member pair (§3.4.3) is the equal-length positional zip
only: for members `seq(a₁…aₖ)` and `seq(b₁…bₖ)` of equal length, one action pairing
`(aᵢ, bᵢ)` positionally; member pairs of unequal length contribute **no** structural
action. The terminal generalize action (§A.3) covers those pairs, so results remain
valid — they just cannot factor the `seq` constructor into the backbone. This behavior
is pinned by `seq_equal_length_zips_positionally` and
`seq_unequal_length_has_no_structural_action` in `egraph/src/au/actions.rs`.

Contrast with AC/ACI (§3.4.4–3.4.5), where unequal totals are already handled by
identity padding and the alignment space is order-free (a transportation polytope).
Seq is harder precisely because order must be preserved: the alignment space is
monotone alignments, not matrices with margins.

## 2. Candidate semantics

Two structural extensions, in increasing power. Both preserve the invariant that every
action's projections land in the source classes.

### 2.1 Order-preserving alignment with identity padding

When the operator declares an identity element `e`, a shorter member may be padded
with identity elements at any positions (not only at the ends): `seq(a, b)` versus
`seq(c, d, f)` becomes, e.g., `seq(a, b, e)` versus `seq(c, d, f)` or
`seq(a, e, b)` versus `seq(c, d, f)`. Padding is sound for the same reason as AC
identity padding: `seq(…, e, …) = seq(…, …)` in the algebra, so the padded sequence
represents the same class and both projections remain valid members. An unmatched
element pairs against the identity as `Variants(element, e)`.

An action is then a **monotone alignment**: a choice of `min(|L|, |R|)`-many matched
index pairs `(i₁ < i₂ < …) ↔ (j₁ < j₂ < …)` with every unmatched position padded.
This is exactly the sequence-alignment / edit-distance search space (match, insert,
delete), and the optimal alignment over fixed per-cell child qualities is a
classic O(|L|·|R|) dynamic program — the order-constrained analogue of the
transport solve: cells are solved once (they are ordinary `AU(aᵢ, bⱼ)` subproblems,
matrix-independent by the same argument as §3.4.4), and the alignment DP selects the
pairing over those fixed qualities.

Without a declared identity there is no order-preserving completion: dropping an
element outright would break projection validity.

### 2.2 Contiguous-block associative alignment

Associativity itself (no identity needed) allows a **contiguous block** of one side
to act as a single child: `seq(a, b, c)` = `seq(a, seq(b, c))` in the algebra, so an
alignment may pair the element `x` on one side against the block `seq(b, c)` on the
other. An action is then an order-preserving partition of both sequences into equal
numbers of nonempty contiguous blocks, pairing blocks positionally; a singleton block
is the element itself, and a longer block denotes the nested `seq` application.

Design points to resolve:

- **Block subproblems are class pairs only if the block exists as a class.** A block
  `seq(b, c)` cut from a longer member need not be materialized in the e-graph.
  Either (a) restrict block actions to blocks whose nested node already exists
  (cheap, incomplete: depends on what saturation materialized), or (b) construct the
  block term directly in the result-term pool, generalizing block-vs-block pairs by a
  recursive sequence alignment rather than by an e-class subproblem (complete for the
  block language, but those subproblems are no longer node-cache states and need
  their own memoization keyed by index ranges).
- **Search-space growth.** The number of two-sided partitions is
  `C(|L|−1, k−1)·C(|R|−1, k−1)` summed over block counts k; a DP over cut positions
  (analogous to the alignment DP of §2.1, with a block-pair quality oracle) avoids
  enumerating partitions explicitly, mirroring how transport avoids enumerating
  matrices.
- **Interaction with §2.1.** With both an identity and associativity, insertions,
  deletions, and blocks combine into one weighted-alignment DP; the two extensions
  should share the DP skeleton rather than being separate action kinds.

The AC analogue — completing unequal totals by nonempty submultiset *blocks* when the
operator has no identity (§3.4.4) — falls out of the same design: it is the order-free
version, and its combiner is a transport instance whose "cells" are block pairs.

## 3. Interaction with cycle filtering and transport

- **Cycle filtering** stays cell-local exactly as in §3.4.4: an aligned element pair
  `(aᵢ, bⱼ)` is a child class pair and is filtered against the OR node's contexts
  before the DP treats it as available; blocked cells are forbidden DP transitions.
  Identity-padding cells `(aᵢ, e)` are filtered like any other pair. Blocks built
  in the term pool (§2.2 option b) recurse over element pairs, so the filter applies
  at the element level and no unroll can hide inside a block.
- **Transport does not apply to Seq**: transport optimizes over matrices with margins
  (order-free); Seq needs the order-preserving alignment DP instead. The MCGS
  integration mirrors transport-AND-nodes (§3.3.1, §4.3): one alignment-AND-node per
  member pair, legal cells as bandit arms, the alignment recomputed from cell Q
  estimates at every backpropagation (a derived attribute, not a search choice), and
  a second alignment solve over lexicographic best-result qualities for witness
  composition — exactly the two-solve pattern the transport path uses.
- **The exact solver** solves each legal cell once and runs one alignment DP per
  member pair, mirroring its one-flow-per-representation-pair structure.
- **Well-formedness** (§4.6) extends with the alignment payload in the AND record
  (cut positions or match/pad trace instead of margins + cell map).

## 4. Acceptance criteria

1. Equal-length behavior is unchanged: the positional zip action remains, byte-for-byte
   deterministic ordering included.
2. With a declared identity, unequal-length Seq pairs produce order-preserving
   alignment actions; projections of every result land in the source classes
   (validity oracle of §2.7).
3. Exact and UCT share the alignment semantics and return equal `(size, variant_mass)`
   quality on instances small enough to exhaust (oracle equality, §8).
4. Without an identity, block alignment (if implemented) factors
   `AU(seq(a,b,c), seq(x,c))` through a block pairing such as
   `seq(Variants(seq(a,b), x), c)`; with neither identity nor blocks, unequal-length
   pairs continue to yield no structural action.
5. Cycle filtering: no alignment action may pair a cycle-blocked class pair; pinned by
   a cyclic-Seq regression test.
6. Determinism (§5.7): the alignment DP breaks ties by fixed index order.
7. No regression in the fixture corpus; new fixtures cover identity-padded and
   block-aligned cases.

## 5. Other deferred anti-unification work

Items specified but not implemented, kept here so they survive as designs:

**Delivered**: the value-guided AND selectors `uct_and` and `lct_and`, formerly
specified here, are now implemented (§3.3.5), selectable via `and_selector` alongside
`round_robin`, with `lct_and` the default. One refinement was delivered beyond the
original formulas: a **terminal-skip gate** — the value-guided selectors skip children
whose OR node is terminal, because a terminal child's Q is exact and immutable and
visiting it cannot change the completion certificate. The gate is necessary, not
cosmetic: the bare formulas do not starve terminal children on near-ties (a converged
spine child's normalized reward approaches the terminal sibling's reward of 1, and the
exploration term then forces near-equal allocation, reproducing round-robin's 2^-depth
flux decay); this is pinned by `lct_and_without_terminal_skip_splits_flux_on_near_ties`
in `egraph/src/au/mcgs.rs`. Fairness (§2.5.1 F) is preserved: the exploration term
diverges for every neglected non-terminal child.

- **PUCT selection.** Given a prior distribution over an OR node's action ids, score
  every action, realized or not; unrealized actions contribute reward 0 and compete on
  their prior alone:

  ```text
  score(a) = reward(a) + C · prior[a] · sqrt(Σ_b N(n,b)) / (1 + N(n,a))
  reward(a) = 1 − normalize(Q(child(n,a)))   if edge a is realized, else 0
  ```

  If the winning action is unrealized, the playout expands it; PUCT therefore realizes
  actions in prior order rather than id order, and may keep descending a strong
  realized edge while low-prior siblings remain unrealized. Every prior must be
  strictly positive for every action, or completeness is lost (a zero-prior unrealized
  action would score 0 forever). Priors change only where exploration goes, never the
  value equations; the search-improvement loop exports the root's normalized
  edge-visit distribution `N(root,a) / Σ_b N(root,b)` as the training target for the
  next prior generation. Extension slots: priors supplying a first value estimate for
  unrealized actions (a virtual sample replacing the reward-0 default), and AND-node
  visit-fraction priors predicting which child needs the most effort.
- **Prior processors.** Uniform: `1/n` over the n actions. Ranked lists: K queries of
  top-N indices; each index at rank k accumulates `1/(k+1)`; normalize; add α = 0.01
  to every action of the node; renormalize. Single votes: a fixed 100 queries;
  `count/100` per index. Full distribution: use the first response and normalize by
  its positive total. Every response is validated (finite, nonnegative, in-range) and
  a positive floor is applied before final normalization so PUCT retains completeness.
- **Non-injective ACI matchings.** Idempotence justifies matching one element against
  several on the other side (`x = op{x, x}`), enlarging the ACI action space beyond
  bijections (§3.4.5).
- **Ancestor-subgraph backpropagation.** Reverse-parent adjacency lists on shared
  statistics nodes and immediate recomputation of every incoming parent (children
  before parents by in-degree counting), replacing path-only updates plus the
  completion-time closure pass (§3.3.3). Sound today; a freshness/cost trade.
- **Incremental completion counter and richer reporting.** A counter of unsolved,
  not-fully-expanded statistics nodes for O(1) completion detection (§3.3.7); periodic
  reporting every K playouts; the exploitation ratio (fraction of selection steps
  where the exploration term did not change the choice); exporting the root edge-visit
  distribution (§3.3.8).
- **Golden traces.** Bit-stable pinned traces for the named configurations,
  generated from the Appendix A reference definitions (§5.7 already guarantees the
  needed determinism).
- **JSON export** of the e-graph and search layers for external analysis and
  visualization.
- **Direct model-generation baseline.** Prompt a model for the anti-unifier and
  validate by variant projection; a quality baseline for the search.
- **Enumerating co-optimal anti-unifiers.** The exact memo stores a set of optimal
  terms per state instead of one (Appendix C.1), with the usual combinatorial
  caveats.
