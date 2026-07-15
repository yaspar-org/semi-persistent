# Anti-Unification Search on the Semi-Persistent E-Graph

**Status**: design proposal (v2); implementation not started.
**Contents**: this document defines the data structures and two algorithms for computing
anti-unifiers over the AC-enabled semi-persistent e-graph: a **reference recursive
anti-unification algorithm with memoization** (dynamic programming), which is exact and
serves as the correctness oracle, and a **Monte-Carlo graph search** (MCGS), which is
anytime and scales to spaces the exact algorithm cannot exhaust. Both operate on the same
graph.

---

## 1. The problem

Given two e-classes l and r of a frozen, saturated e-graph, find a small **anti-unifier**:
a term over the e-graph's operators plus a binary `Variants(t_left, t_right)` node, such
that replacing every `Variants` node by its left child yields a term in l, and replacing
every `Variants` node by its right child yields a term in r. The `Variants` nodes mark
where the two sides differ; everything outside them is common structure ("backbone").
Smaller anti-unifiers have more backbone.

Term size counts 1 per ordinary node and 0 for each `Variants` node (its children are
counted). Quality is measured by the linear compression ratio; see §2.5.

Because the e-graph is saturated with rewrite rules, each e-class can contain many terms
the e-graph equates. Anti-unifying e-classes rather than fixed terms searches all those
variants at once and finds backbones that no syntactic comparison of the two original
terms could find.

## 2. Theory

### 2.1 The search space is an AND/OR graph

Solving `AU(l, r)` means choosing how to factor the two classes:

- An **OR node** is a subproblem `AU(l, r)`. Its actions are factorings: pick an operator
  present in both classes and a way to pair the children of an l-member with the children
  of an r-member.
- An **AND node** is one chosen factoring. All its child subproblems `AU(l_i, r_i)` must
  be solved; the result is the operator applied to the child results.
- `AU(l, l)` is terminal: its result is the smallest concrete term of l.
- An OR node with no surviving action is terminal: its result is the syntactic seed of
  §A.3, which is never worse than bare `Variants(best_term(l), best_term(r))`.

Subproblems repeat massively (the same class pair is reached through many factorings),
so the space is a directed acyclic **graph**, not a tree, and we share nodes.

Our design uses **layered graphs**: the bottom layer contains the nodes and edges that
represent the search space itself; the upper layers contain nodes and edges that store
the statistics used by different search heuristics. Several heuristics (the exact solver,
one or more MCGS instances) can work on the same bottom layer at once, each with its own
statistics layer, and exchange results through a shared best-result table (§4.5).

### 2.2 Cycles, and why we refuse to unroll them

E-graph saturation introduces cycles: a rule like `x = x + 0` makes the class of `x`
reachable from itself. The inputs to saturation are finite terms and never contain
cycles; only rewrite rules create them, and following them denotes infinite unrollings.

A cycle is tempting for anti-unification in a degenerate way. By unrolling `x → x + 0 →
(x + 0) + 0 → …` on one side only, the search can manufacture ever-larger "common"
structure that absorbs the other side into the backbone. The resulting anti-unifier looks
better by the size metric while its backbone is inflated scaffolding with no grounding in
the inputs: neither original term contained those unrollings. We therefore prune any
factoring that revisits an e-class already used **on the same side** of the current
root-to-node path. Backbones then only contain structure genuinely present in finite
members of both classes.

### 2.3 Cycle contexts: pruning without losing sharing

The pruning rule makes the legal actions of `AU(l, r)` depend on the path used to reach
it, which breaks node sharing: a node's value would no longer be a function of the node
(the Markov property fails), and pooling statistics across paths would mix subproblems
with different futures.

Keying nodes by their whole path would fix that but destroy all sharing. The right
quotient keeps exactly the part of the history that can still matter. Of all classes seen
on the path, only those still **reachable** from the current pair can ever be revisited
below it:

```text
ctxL = reach(l) ∩ seen_left        ctxR = reach(r) ∩ seen_right
state = (l, r, ctxL, ctxR)
```

Two occurrences with equal states have identical legal actions and, recursively,
identically-keyed children, so they are one node and may share results and statistics.
On acyclic regions the contexts are empty and sharing is total. The **node cache** is a
hash map from `(l, r, ctxL, ctxR)` to the node id; every child lookup goes through it.

Child contexts derive from the parent's state alone: `reach(child) ⊆ reach(parent)`,
so on each side `ctx_child = reach(child_class) ∩ (ctx_parent ∪ {parent_class})`. No
path information beyond the parent's context is needed.

A session selects one `CycleMode`, which is part of the node-cache namespace:

- `AncestorOnly` filters actions against `ctxL` and `ctxR`. A node's own classes are not
  present yet, so one factoring may reuse the current class as a child; that child's
  context then contains the class and blocks another reuse. A class occurs at most twice
  per side on a path.
- `CurrentInclusive` also filters against the current l and r. It blocks the immediate
  self-step, so a class occurs at most once per side on a path.

Both modes therefore produce finite graphs. MCGS and the exact solver accept either
mode; within one session both use the same mode, so they share one graph and their
results are comparable. The default is `AncestorOnly`.

### 2.4 Reachability: computing and storing reach(e)

Cycle detection, action filtering, and context computation all need `reach(e)`, the set
of e-classes reachable from class e through any member e-node. We compute it once per
frozen e-graph and store it compactly:

1. Number the live classes densely `0..C` (class ids after representative lookup).
2. Compute strongly connected components with Tarjan's algorithm over the class graph
   (edge: class → class of each member child). All classes in an SCC have the same reach
   set; every class on a cycle reaches itself.
3. Process SCCs in reverse topological order; each SCC's reach set is the union of its
   successors' sets plus the successor classes themselves, plus the SCC's own members if
   the SCC is cyclic (size > 1 or self-loop).
4. Store one **bitset per SCC** (C bits, `Vec<u64>` blocks), and a class → SCC index.
   Classes in one SCC share one bitset, so memory is `#SCC × C / 8` bytes, far below the
   naive `C² / 8` on rule-saturated graphs where SCCs are large.

Queries used by the search:

- membership `x ∈ reach(e)`: one bit test;
- context construction `reach(e) ∩ seen`: intersect the bitset with the (small) seen set
  by iterating the seen set, O(|seen|);
- action filtering `child ∈ ctx`: contexts are interned as sorted class-id vectors, so
  this is a binary search.

The table is immutable for the session; a session created from a later e-graph state builds
a new table.

### 2.5 Cost, compression ratio, and selection reward

Both algorithms minimize term size. The reported compression ratio is the linear ratio
used to compare a result with the two smallest root representatives:

```text
compression_ratio(t, l, r) =
    (size(t) − min(best_size(l), best_size(r))) / max(best_size(l), best_size(r))
```

MCGS uses a separate bounded transformation only inside selection. For a node n:

```text
local_cr(n)  = (E[size](n) − min_size(n)) / max_size(n)
normalize(n) = 0                              if local_cr(n) ≤ 0
             = 1 − exp(−λ · local_cr(n)),     λ = −ln(1 − x_target), x_target = 0.8
reward(n)    = 1 − normalize(n)
```

For an OR node, `min_size`/`max_size` are the sizes of the two classes' smallest concrete
terms; for an AND node they are the extrema over its child pairs of
`best_size(l_i) + best_size(r_i) + 1`. We track and backpropagate **sizes**, not rewards:
sums of sizes are meaningful (an AND node's size is 1 plus the sum of its children's),
sums of nonlinear rewards are not. The inverse exponential is applied only at selection
time, to the already-averaged expected size; this computes `normalize(E[size])` rather
than the true `E[normalize(size)]`, which cannot be recovered from expectations of a
nonlinear function. The approximation is deliberate: the normalization is monotone, so
candidate rankings are preserved, and selection needs rankings, not calibrated
expectations. It is also not the reported compression ratio.

### 2.6 Adapting MCTS to graphs

Bandit tree search keeps, per node, a visit count N and a value Q, and repeats: walk down
by a selection formula, add one new leaf, estimate it, walk back up updating N and Q. Its
soundness rests on a fact worth stating: the cumulative counts of the actions selected at
a node converge to a policy that maximizes expected child value under a prior-regularized
bandit objective, and Q can be rewritten recursively as

```text
Q(n) = (U(n) + Σ_a N(n,a) · Q(child(n,a))) / N(n),      N(n) = 1 + Σ_a N(n,a)
```

i.e. Q is a pure function of the node's own action counts and its children's current
values, with U(n) the node's first rollout estimate.

On a shared graph, the naive adaptation breaks twice. If a parent's selection formula
reads the child's total visit count, visits arriving through other paths make the child look
"already explored" and the parent starves its best action. If instead every playout is
credited to all parents of an updated child, parents absorb values at weights their own
policies never chose. Both failures conflate two different numbers: how often *this
parent* chose the action, versus how many visits the child has in total.

The sound formulation, which this design adopts, moves visit statistics to **edges**:

1. Each node stores per-action **edge visits** `N(n,a)`: how often its own selector chose
   a. Selection reads only these. `N(n) = 1 + Σ_a N(n,a)`.
2. Q is **recomputed idempotently** from the children's current values by the formula
   above, never by averaging arriving playout values into a running mean.
3. Statistics are therefore shared soundly at shared nodes: a subproblem improved through
   one path improves for every parent that reads it. Values of parents on non-traversed
   paths go momentarily stale; since selection tries every action infinitely often and
   one recomputation fully repairs a node from its children, updating only the traversed
   path is sound. Updating the whole affected ancestor subgraph (children before parents)
   is equally sound and propagates improvements immediately; the choice is cost versus
   freshness, not correctness.

The statistics layer is thus a **DAG mirroring the search-space layer**, with per-edge
counts and per-node values, not a tree of per-path copies.

Keeping U(n) as one permanent unit-weight sample makes Q total from the node's first
estimate onward; the formula is what golden traces pin.

### 2.7 What correctness means here

- **Anytime validity**: every result stored anywhere is a valid anti-unifier of its
  node's class pair, by construction (§3.1, §A.3).
- **Exactness**: the memoized recursive algorithm (§3.2) returns the minimum-size
  anti-unifier expressible in the action language and cycle policy; this is proved by
  induction over its well-founded recursion.
- **MCGS convergence**: with finite action sets, positive priors, every action selected
  infinitely often, and idempotent value recomputation, node values converge to the exact
  values for the same action model and `CycleMode`; when the search graph has been fully
  expanded, the best stored result equals that exact optimum. Before that point MCGS is a
  heuristic anytime algorithm bounded below by the oracle's optimum.

---

## 3. The two algorithms

When configured with the same `CycleMode`, both algorithms search the same AND/OR graph,
use the same node cache, the same action generators (§3.4), the same term pool (§4.4), and
the same best-result table (§4.5).

### 3.1 Shared building blocks

- `best_term(e)` / `best_size(e)`: the smallest concrete member term of class e,
  precomputed for all classes by the standard fixpoint
  `cost(node) = 1 + Σ multiplicity(child) · cost(class(child))`, minimized per class
  (§A.2).
- `syntactic_seed(l, r)`: the anti-unifier obtained by recursively zipping
  `best_term(l)` and `best_term(r)` and emitting `Variants` at every mismatch (§A.3).
  Every OR node's stored best result is initialized with it (or with `best_term(l)` when
  l = r), so a valid answer exists from the first instant.
- `child(l, r, l2, r2)`: node-cache lookup of the child state, deriving contexts per
  §2.3.
- Results are interned in the term pool; replacement anywhere is strict: a new candidate
  wins only if its size is strictly smaller.

### 3.2 Reference algorithm: eager_with_memo

`eager_with_memo` is dynamic programming over the cycle-context states for one selected
`CycleMode`: an eager recursion that enumerates every surviving action and takes the
minimum, with memoization on states.
Memoization *is* node sharing: the memo table is keyed by the same
`(l, r, ctxL, ctxR)` states as the node cache within that mode's cache namespace, so each
distinct subproblem is solved once no matter how many factorings reach it.

```text
exact(state):                            # returns the minimum-size anti-unifier term
    if memo[state] is Solved(term): return term
    assert memo[state] is Empty           # Visiting would violate the cycle-mode rank
    memo[state] = Visiting
    if state.l == state.r:
        best = best_term(state.l)
    else:
        best = syntactic_seed(state.l, state.r)
        for action in actions(state):                  # §3.4, cycle-filtered
            children = [ exact(child(state, l_i, r_i)) # each pair occurrence
                         for (l_i, r_i) in action.pairs ]
            candidate = apply(action.op, children)     # AC ops: canonical child order
            if size(candidate) < size(best): best = candidate
    memo[state] = Solved(best)
    publish_exact(state, best)             # §4.5, atomically updates all overlays
    return best
```

Termination follows from the selected cycle mode (§2.3): `CurrentInclusive` permits each
class at most once per side on a recursion path; `AncestorOnly` permits it at most twice.
Lazy-AC states additionally strictly shrink their residual multisets. Optimality follows
by induction over this finite graph: every child result is optimal, and the minimum over
all actions plus the seed is optimal.

The seed is always a candidate: it may preserve common structure when all structural
actions are blocked, and it makes the exact solver's objective identical to MCGS's
shared best-result objective.

The exact algorithm doubles as the **correctness oracle**: on instances small enough to
exhaust, MCGS and exact search configured with the same action model and `CycleMode` must
return the same size; every intermediate MCGS result must be valid and no smaller than
the oracle's optimum.

### 3.3 Monte-Carlo graph search

One iteration ("playout"):

```text
playout(root):
    # 1. SELECTION: walk down while nodes are fully expanded
    node = root
    loop:
        if node is terminal or best[node].exact:
            Q(node) = size(stored best result of node)      # terminal value
            backpropagate(node); return
        a = select action at node (§3.3.4)                  # OR node
        N(node, a) += 1                                     # edge visit, then check
        if edge a is unrealized:
            and_node, fresh_children = EXPAND(node, a); break   # §3.3.1
        node = child of AND node on edge a                  # AND selector (§3.3.5)

    # 2. ROLLOUT: first estimate only for newly allocated child statistics nodes
    for child in fresh_children:
        Q(child) = size(greedy_rollout(child))              # §A.4

    # 3. BACKPROPAGATION: from the new AND node, children before parents
    backpropagate(and_node)                                 # §3.3.3
```

Value equations, recomputed idempotently at every update (§2.6):

```text
OR node:   Q(n) = (U(n) + Σ_a N(n,a) · Q(child(n,a))) / (1 + Σ_a N(n,a))
AND node:  Q(n) = 1 + Σ_i pair_count_i · Q(child_i)     # lazy-AC bookkeeping adds no 1
```

and every update also offers the children's stored best results to the node's entry in
the best-result table (strict size improvement only).

The subsections below define each phase precisely.

#### 3.3.1 Fully expanded, and expansion

A node is **fully expanded** when every one of its actions has a realized outgoing edge.
A node whose best-result entry is marked exact is already solved and needs no statistics
edges. UCT selects the next unrealized action in action-index order until one of those
conditions holds; PUCT scores realized and unrealized actions together and may realize
them in another order (§3.3.4).
`EXPAND(node, action)` allocates the AND node for the action (through the edge cache
keyed by `(node, action index)`), looks up or creates **all** its child OR nodes through
the node cache, and obtains all child OR statistics structs from the overlay cache. It
returns only the newly allocated child statistics structs for rollout; existing shared children
keep their current values. The new OR edge starts with visit count 1 (the visit was
counted before the expansion check). The
not-fully-expanded counter is decremented if the expansion completed the parent and
incremented only for newly allocated nonterminal child statistics structs. Expanding
never restructures an existing edge; it fills one fixed action slot and adds reverse
parent links (§4.6).

#### 3.3.2 Rollout

Every newly allocated child statistics struct of the expanded AND node needs a first
value estimate, taken in the same playout. An existing shared child already has one. The
rollout (§A.4) is deterministic and cheap: starting from the child's class pair,
repeatedly take the first action that survives the cycle filter, recursing
on its child pairs; if none survives, return the `Variants` fallback. Its term is also
offered to the best-result table, so even the first playout produces a valid global
answer.

#### 3.3.3 Backpropagation

Backpropagation starts at the new AND node (or the terminal node selection stopped at)
and walks rootward through **parent links**, recomputing each node with the idempotent
equations above. Children are processed before parents by in-degree counting: a node is
recomputed only after every child update that can reach it has arrived. On the shared
DAG this is the ancestor-subgraph policy: every parent of an updated shared node is
recomputed immediately, through all paths. Restricting the walk to the parents on the
selection path (path-only) is the cheaper sound alternative; other parents pick up the
improvement on their next visit (§2.6).

#### 3.3.4 Selection and expansion rules at OR nodes

All rules and formulas are normative. Common to both policies: the chosen edge's visit
count is incremented first, and only then is the edge checked for realization, so a new
edge is born with visit count 1; scores are evaluated in ascending action-id order and
the first maximum wins, so ties choose the smallest id.

**UCT.** Expansion is strictly sequential and unconditional: while any action is
unrealized, the selector returns the lowest unrealized action id and the scoring formula
is not evaluated at all. Scoring begins only at fully expanded nodes:

```text
score(a) = (1 − normalize(Q(child(n,a))))  +  C · sqrt(Σ_b N(n,b)) / (1 + N(n,a))
C = √2
```

The exploration numerator is the node's own total edge visits, never the child's visit
count (§2.6). Exploration is uniform across actions, so UCT always pays one visit to
every sibling (width) before it can revisit anything (depth).

**PUCT.** Given a prior distribution over the node's action ids, every action is scored,
realized or not; unrealized actions contribute reward 0 and compete on their prior alone:

```text
score(a) = reward(a) + C · prior[a] · sqrt(Σ_b N(n,b)) / (1 + N(n,a))
reward(a) = 1 − normalize(Q(child(n,a)))   if edge a is realized, else 0
```

If the winning action is unrealized, the playout expands it; PUCT therefore realizes
actions in prior order rather than id order, and it may keep descending a strong
realized edge while low-prior siblings remain unrealized, spending budget deep instead
of wide. Policy processors return a finite distribution with `prior[a] > 0` for every
action (§A.6); a zero-prior unrealized action would score 0 forever and completeness
would be lost.

#### 3.3.5 Effort allocation at AND nodes

An AND node does not choose an outcome; all children must be solved, so its selector
decides where the next unit of refinement effort goes. Child-edge visits `N(n,i)` are
incremented exactly like OR edge visits. Three selectors are specified; round-robin is
the default:

```text
round_robin:  i = counter mod arity;  counter += 1        # equal effort by rotation
uct_and:      argmax_i (1 − normalize(Q(child_i))) + C · sqrt(Σ_j N(n,j)) / (1 + N(n,i))
lct_and:      argmin_i (1 − normalize(Q(child_i))) − C · sqrt(Σ_j N(n,j)) / (1 + N(n,i))
```

`round_robin` guarantees every child equal visits regardless of values. `uct_and`
refines the currently most promising child. `lct_and` selects by lower confidence
bound, deliberately visiting the weakest child: an AND result's size is a sum, so its
quality is limited by its worst child, and raising the bottleneck is the fair policy
for that objective. The round-robin counter is per AND statistics node and part of the
overlay state (§5.4).

#### 3.3.6 Priors and the search improvement loop

A prior is a pre-existing action policy: a probability distribution over an OR node's
action ids obtained before any exploration of that node. It changes where exploration
goes, not what values are: the prior enters only the exploration term, while rewards
still come from rollouts and backpropagation. Selection then searches around the prior,
and even when the prior favors a mediocre action, the reward term accumulates evidence
that eventually outvotes it.

The loop closes through the visit counts. After a run, the root's normalized edge-visit
distribution `N(root,a) / Σ_b N(root,b)` is a better policy than the prior that guided
the run: visits concentrated where value proved out, not merely where the prior
pointed. That distribution is exported by the main loop (§3.3.8) as the training target
for the prior model, which learns to predict the post-search visit distribution from
the node's description. Each generation of the prior front-loads knowledge the previous
generation had to discover by spending playouts, so the searcher improves across
problem instances rather than starting from zero each time.

Prior processors are specified in §A.6: uniform (default), ranked-list voting with
inverse-rank weights and post-normalization α = 0.01 smoothing, single-vote counting,
and full distributions, each validated and floored to positive probabilities.

Two extension slots are specified but not in the milestone. Priors may additionally
supply a first value estimate for unrealized actions (a virtual sample replacing the
reward-0 default, and the natural place for a learned value estimate in `U(n)`), and
AND nodes may take visit-fraction priors that predict which child needs the most
effort; both plug into the formulas above without changing the update rules.

#### 3.3.7 Complete search

The search is **complete** when every reachable nonterminal OR state is either marked
exact in the shared best-result table or fully expanded in the statistics overlay; a
counter of unsolved, not-fully-expanded statistics nodes tracks this incrementally. At
completion, induction over the acyclic graph gives that the best-result table holds the
exact optimum, and the run reports it with a completion flag. Until then the algorithm
is anytime: the root's
stored result is always valid and only improves.

#### 3.3.8 Main loop and reporting

Run playouts until the budget or completion; report the root's best term (surface
syntax), its size, the linear compression ratio of §2.5, playouts used, the completion
flag,
the exploitation ratio (fraction of selection steps where the exploration term did not
change the choice), and the root's edge-visit distribution (the training signal for
priors). Reporting every K playouts is configurable.

### 3.4 Action generation per node kind

Actions for `AU(l, r)` are computed per operator common to both classes, then filtered
by the node's cycle contexts (drop an action if any pair hits the active `CycleMode`
set). The raw per-operator lists are cached by the class pair `(l, r)` and shared across
contexts. The e-graph stores each operator's nodes in the canonical form of its kind,
and the generator dispatches on that kind. Plain ordered nodes (`Plain0..3`, `PlainK`)
use exactly the classic rule, positional zipping of same-operator, same-arity member
pairs (§3.4.1); the canonical `SPair`, `Seq`, `MSet`, and `Set` kinds are a strict
extension of that action language (§3.4.2–3.4.5).

#### 3.4.1 Ordered operators (fixed arity and ordered variadic)

Children are positional. For every member of l and member of r with the same operator and
arity, emit one action pairing children positionally. Duplicate pairs stay explicit.

#### 3.4.2 Commutative binary operators (sorted pairs)

Children are stored sorted, so the stored order is not an alignment. For members
`f(a,b)` and `f(c,d)` emit two actions, `{(a,c),(b,d)}` and `{(a,d),(b,c)}`, dropping the
second when it equals the first (a = b or c = d).

#### 3.4.3 Associative operators (sequences)

Members are variadic ordered sequences. Milestone rule: one positional action when the
lengths are equal, none otherwise. (Aligning unequal lengths requires grouping
subsequences; specified as an extension.)

#### 3.4.4 AC operators (multisets), and why canonical storage wins

Each AC e-node stores its children as one canonical sorted multiset of
(child class, multiplicity) pairs. An e-class may contain several AC e-nodes for the same
operator when saturation proves distinct multisets equivalent; action generation handles
every pair of such members. For one member pair
`M = {a₁^{m₁}, …}` and `N = {b₁^{n₁}, …}` with equal total multiplicity means choosing
which copies pair with which. An action is a **matching-count matrix** X: rows are M's
distinct children, columns are N's, cell `x_ij ≥ 0` counts the copies of `AU(aᵢ,bⱼ)`;
row i sums to `mᵢ` and column j to `nⱼ`, so both sides are consumed exactly. Each nonzero
cell contributes one child subproblem with multiplicity `x_ij`; a diagonal cell
`AU(x,x)` reduces to x. (The row/column totals are classically called the matrix's
margins.)

**Comparison with explicit rewrites.** Encoding AC by associativity/commutativity rewrite
rules materializes the variants instead. Be precise about what is counted. For n distinct
children:

| n | concrete binary terms `n!·Catalan(n−1)` | concrete term pairs | root e-node pairs `(2ⁿ−2)²` | canonical actions `n!` |
|--:|--:|--:|--:|--:|
| 3 | 12 | 144 | 36 | 6 |
| 5 | 1,680 | 2,822,400 | 900 | 120 |
| 6 | 30,240 | 914,457,600 | 3,844 | 720 |

A term-pair search over explicit variants faces the concrete term-pair counts; a
saturated explicit-rewrite e-graph still exposes the root e-node pair counts, each
zipped positionally and largely redundant modulo AC. For one fixed multiset, canonical
storage collapses that representation orbit to one e-node and the alignment space to the
n! canonical actions. An e-class may still have other canonical multiset members, each
representing different child classes. Repeated children
shrink it further: the number of matrices `T(M,N)` for multisets is far below `n!`
(matching `{a⁵}` against `{a³b²}` gives exactly one matrix). For the worked
`AU(and{a,b,c}, and{b,c,d})` example and its six actions, see §B.

**General multiplicities.** Equal totals with arbitrary per-element multiplicities are
handled by the same matrices: choosing `x_ij = k` subtracts k from the row's remaining
count and from the column's residual multiplicity, and enumeration recurses on the
residual multisets. Unequal totals cannot be consumed by one-to-one pairing; the complete
extension pairs nonempty submultiset *blocks* (associativity lets a block act as one
child), enumerated canonically by a nondecreasing piece key. That extension is specified
but not in the milestone; until then unequal-total member pairs contribute no action and
the syntactic seed covers them.

**Enumeration.** If `T(M,N) ≤ A_max` (default 32), materialize all matrices, ordered
greedy-first: assign `min(M[x], N[x])` to every diagonal cell, complete the residuals in
ascending class order, then the rest in lexicographic order. Otherwise the matrix choice
itself becomes search structure: a chain of row-allocation states (fix the first
remaining row; at each column choose an allocation, greedy value first; commit the row
and recurse on the residual matching state), giving exactly one path per matrix and
branching bounded by the column count. These matching states are ordinary OR nodes in the
graph; their bookkeeping edges add no operator cost.

**Greedy is ordering, not pruning.** Pairing the common submultiset first is usually
best but not always: let class X contain both `f(v1,v1)` and `g(v1,v1)`, Y contain
`f(v1,v2)`, Z contain `g(v1,v2)`. For `AU(op{X,Y}, op{X,Z})`, the greedy diagonal costs
1 + 3 + 6 = 10 (the pair (Y,Z) has no common operator and falls back to `Variants`),
while the crossed matching costs 1 + 4 + 4 = 9 by factoring g inside `AU(X,Z)` and f
inside `AU(Y,X)`. Every matrix must remain reachable.

#### 3.4.5 ACI operators (sets)

Canonical members are sorted duplicate-free sets: the multiset machinery with all
multiplicities 1, so actions are the permutation matrices (bijections) between
equal-cardinality sets. Idempotence would justify non-injective matchings; that extension
is deferred with the unequal-total one.

#### 3.4.6 Literals

A literal member pairs only with a literal member holding the same interned value,
producing a terminal action; different values contribute nothing.

---

### 3.5 Algorithm portfolio and configuration axes

The session exposes four algorithms over the shared graph, plus one search-free
baseline, under these identifiers:

- `syntactic`: the syntactic seed of the two input terms (§A.3). No e-graph search;
  the floor every other algorithm must beat.
- `eager_with_memo`: the exact solver of §3.2. Complete and optimal for the action
  language and `CycleMode`; the correctness oracle for everything else.
- `uct`: MCGS with UCT selection (§3.3.4).
- `puct`: MCGS with prior-guided selection (§3.3.4, §3.3.6).
- A direct model-generation baseline (prompt a model for the anti-unifier, validate by
  variant projection) exists for benchmarking only and is outside this design.

The greedy rollout (§A.4) is not a fifth algorithm but the shared leaf estimator: it is
the same recursion as `eager_with_memo` with the minimum over actions replaced by the
first surviving action, which is why its results are always valid anti-unifiers.

The MCGS algorithms factor into three independent configuration axes:

| Axis | Options | Default |
|---|---|---|
| OR selection (§3.3.4) | `uct`, `puct` | `uct` |
| AND allocation (§3.3.5) | `round_robin`, `uct_and`, `lct_and` | `round_robin` |
| prior processor (§A.6, PUCT only) | `uniform`, `ranked`, `votes`, `full_dist` | `uniform` |

Any combination is legal (24 in total; the prior axis is inert under `uct`). Golden
traces pin the named configurations `uct_round_robin`, `puct_uniform`, and one
model-backed `ranked` variant; the remaining combinations are covered by property
tests only.

## 4. Data structures

We implement the layers of the search graph as **arenas**: `Vec`s of structs,
with integer indexes used as pointers. Arenas are required because these structures have
internal aliasing (many edges reference the same shared node), which Rust references
cannot express, and they grow from the leaves, like appending to linked lists. Every
arena's mutable storage uses semi-persistent containers from the `containers` crate,
and `SearchSession::mark()` / `restore(token)` apply them as one operation across all
layers (§4.7). **Semi-persistent** means the version history is a backtracking stack:
any marked ancestor version can be restored, and doing so abandons the versions created
after that mark; their tokens are rejected from then on. Cost is the sum of the component
containers: a tracked `Vec` restores in O(captured writes), an `AppendOnlyVec` truncates,
and `Map` additionally rebuilds its transient hash index from surviving entries. Each
index type is a distinct newtype (`define_id31!`), so using a node id where an edge id
belongs is a compile error.

### 4.1 Read-only e-graph interface needed by the search algorithm

The search never mutates the e-graph. It is built once per frozen e-graph state from the
public read API (`class_repr`, `node_ref`, `node_op`, `for_each_child`, `child_at`,
`mset_children`, `get_lit_val_id`, `node_flags`, `len`) into an owned snapshot holding:

- a dense numbering of live classes and, per class, its member nodes grouped by operator
  (built by one scan of all node ids, grouping on `class_repr`); nodes carrying
  `FLAG_SUBSUMED` are excluded, matching the e-graph's pattern-matching boundary;
  `FLAG_AC_COLLAPSED` nodes remain included because that flag retires them only from AC
  completion and they remain matchable;
- per class: the smallest concrete member and its size (§A.2);
- the reachability table of §2.4.

Snapshot construction returns `AuError::NoFiniteRepresentative(class)` if any class
needed by either root has no admissible finite member after this filtering.

The constructor borrows the e-graph only while building this owned immutable snapshot.
Later e-graph changes are not observed by an existing search; the search remains a
computation over the captured state. Results and `SearchToken`s belong to that one
`SearchSession` and cannot be used with another snapshot, which is enforced by the
component containers' ids.

### 4.2 The search-space layer

One arena family holds the AND/OR graph, shared by every algorithm:

- **OR nodes**: the state `(l, r, ctxL, ctxR)` (contexts interned as sorted class-id
  vectors), the filtered action list, terminal flag, and the two class's best sizes for
  normalization. The **node cache** maps states to node ids (§2.3).
- **Actions**: immutable payloads per class pair, cached by `(l, r)`: operator plus the
  paired children (positional list, pair list, or matching-count matrix entries with
  multiplicities).
- **AND nodes / edges**: one per realized `(OR node, action index)`, cached by that key;
  stores the child OR node ids with their pair multiplicities. Lazy-AC matching states
  (§3.4.4) are additional OR-node variants with their own keys and residual-multiset
  payloads, interned like contexts.

All structs are immutable once pushed; the layer only ever grows (hash-cons semantics),
and restore truncates it back.

### 4.3 The statistics layers

Each search heuristic owns one statistics overlay: arenas of per-node and per-edge structs
whose fields reference search-space ids. Nothing in the bottom layer points upward, so
any number of overlays can coexist.

The MCGS overlay is a DAG mirroring the reachable search space (§2.6). Each OR
statistics struct has U and Q plus one edge-statistics element per structural action; an
optional AND statistics id says whether that action is realized, and the edge stores its
visit count `N(n,a)`. Each AND statistics struct has Q, a round-robin counter, and one
child-edge element per child (including the AND selector's edge visits). Reverse parent
links support ancestor-subgraph backpropagation. The prior cache is per OR statistics
struct.

Mutable values, visits, realized-edge options, counters, and reverse links use
semi-persistent containers, so a mark/restore frame captures their changes. The exact
solver's overlay is a memo vector indexed by `OrId`, with states `Empty`, `Visiting`, and
`Solved(TermId)`; solved terms are also published to the best-result table.

### 4.4 The result-term pool

The search maintains its current anti-unifier results as terms allocated in a pool: a
hash-consed arena of `(operator, children)` structs, where the operator is an enum over
the e-graph operators, literals, and `Variants`, and children are spans into a shared
child pool. Sizes are cached per term. Structurally equal terms get the same id, so results share
subterms and comparing candidates is an id/size comparison. For AC operators, children
are kept in a canonical structural order, so the same semantic result always interns to
the same id regardless of which algorithm or action order produced it. Variant
projection (§1) is a recursive walk over the pool.

### 4.5 The best-result table

One table, shared by all heuristics of a session, maps each OR node to the best
anti-unifier found for it so far (a term id), and, when the exact solver has finished
that node, an "exact" flag. Updates are strict improvements only, so any interleaving of
writers preserves validity, and MCGS can adopt an exact subresult as a solved leaf when
it first creates the node. If an exact flag is published after a statistics struct
already exists, the session sets its value to the exact term size, excludes it from
further selection, adjusts the overlay's completion counter, and propagates that value
according to the overlay's update policy, all in one operation; the table and overlays
are never exposed between those writes.

### 4.6 Well-formedness, specified with ghost models and frames

Arena ids deliberately bypass the borrow checker, so nothing in the type system rules
out a dangling child id or one edge claimed by two nodes. The `containers-verus` crate
has a worked discipline that buys the guarantee back, dynamic frames over a ghost
model: alongside the executable arenas, the specification carries a ghost description
of the structure as sequences and sets of unique ids, and a well-formedness predicate
`wf` ties the executable fields to that description with four clauses (in-range,
disjoint, coverage, shape). Each graph layer here gets one ghost model, one `wf`, and
per-operation contracts in that style. In milestone 1 the ghost models exist as the
shadow models of property tests (§8); the Verus formalization is the upgrade path.

**Search-space layer.** Ghost model: a finite map from canonical keys (states,
`(l, r)` action lists, `(OR, action)` edges, interned contexts, residual multisets) to
immutable descriptions whose children are canonical keys.

1. in-range: all field vectors of one arena have the same length; every id stored in any
   field is below the length of its target arena; every span is within its payload pool;
2. disjoint: the keys are pairwise distinct, so each cache (node, edge, action,
   context) is injective into ids;
3. coverage: every canonical-key arena element is the image of exactly one key; every
   payload-pool element belongs to exactly one live span; caches are bijections onto their
   keyed live ids, with no dead elements;
4. shape: each struct's fields realize its key's description: an AND node's children
   match its action's pairs in order, with contexts derived by §2.3 from its parent's
   state, and the acyclicity of §2.2–2.3 holds (a class occurs on one side of a path
   at most as §2.3 permits; lazy-AC states strictly shrink their residuals).

**Statistics overlay.** Ghost model: a DAG over the reachable search-space ids with a
visit count per edge and a value per node.

5. in-range: all field vectors of one statistics arena have equal length, and every
   structural, child, action, span, and parent-list id names a live target;
6. disjoint: at most one statistics struct per search-space id per overlay, and each
   realized edge appears once in its node's edge list;
7. coverage and shape: every OR statistics struct has exactly one edge-statistics element
   per structural action; every realized edge points to the matching structural AND node;
   each AND child edge matches the structural child and multiplicity; reverse-parent links
   are the exact inverse adjacency; edge visit counts are defined only by their own
   selector; values are finite; and the not-fully-expanded counter equals the number of
   nonterminal, non-exact OR statistics structs with an unrealized action.

The current Q equation is deliberately not a global `wf` clause. Under path-only
backpropagation, a parent not on the path may hold a value computed before a shared child
improved. Instead, `recompute(n)` has the postcondition that Q(n) equals the §2.6 equation
using the children's values at that call; ancestor-subgraph backpropagation establishes
that postcondition for every node in its affected ancestor subgraph, children first.

**Best-result table.** Ghost model: a map from search-space ids to terms, with a
monotonicity contract instead of a shape clause: entries only improve (strict size
decrease), the exact flag is write-once within a branch, and every entry is a valid
anti-unifier of its state's class pair. Any interleaving of writers preserves this.

Operation contracts take the frame and anti-frame shape of the verified containers.
Every mutation names its **footprint**, the few ids it touches; disjointness makes the
`wf` facts of every untouched id carry across unchanged (the frame), and the remaining
precondition is the operation's genuine correctness condition (the anti-frame):
expansion requires "this action index is unrealized on this node", and an exact-flag
write requires "the solver finished this state". Expansion allocates or finds the AND
statistics struct and its children, writes one previously empty OR edge slot, and appends
one reverse-parent link to each distinct child. Its existing-node footprint is therefore
O(action arity), not O(1), but remains local and never restructures an existing edge.
Selection and backpropagation have statistics-only footprints, so the entire structural
`wf` is frame for them.

Two lessons from the verified exemplars are binding here. Shape is always stated over
the ghost model, never by pointer-chasing: an invariant that correlates arena order
with graph shape ("children have larger ids than parents") is false under this growth,
because a shared node created deep on one path is later linked as a shallow child of
another. And `wf` is a predicate over the arena contents alone, with tokens carrying
only scalars: restore then re-establishes `wf` for free through the containers'
rollback guarantee, since restoring is exact frontier truncation plus replay of the
single-field diffs.

### 4.7 Whole-search marks, restores, and sessions

`SearchSession::mark()` snapshots the entire search in one operation: search-space arenas
and caches, context and residual interners, term pool, best-result table, exact memo state,
every MCGS statistics overlay and prior cache, and all scalar counters. It returns one
opaque `SearchToken`. Layer-specific marks are private implementation details and are not
exposed, so callers cannot restore one overlay while leaving another layer in a later
version.

`SearchSession::restore(token)` first validates every component token, then restores in
reverse dependency order: statistics overlays and exact memo state, best results and term
pool, structural payloads and caches, then routing/interners. Validation happens before
any mutation, so an invalid or abandoned-branch token cannot cause a partial restore. At
every public method boundary all layers name the same logical version and §4.6 holds.
E-graph and search marks are separate: `SearchSession::restore` restores every search
layer to one earlier search version while its owned e-graph snapshot remains immutable.

---

## 5. Rust implementation

### 5.1 Module layout

The feature lives in this crate as `egraph/src/au/`, compiled behind no feature flag:

```text
au/
  egraph_api.rs   read-only snapshot of the e-graph (§4.1): dense class table,
                  members grouped by operator, best terms, reachability
  space.rs        OR/AND arenas, context interner, node/edge/action caches (§4.2)
  actions.rs      action generation per node kind (§3.4), matrix enumeration
  terms.rs        result-term pool (§4.4) and variant projection
  results.rs      best-result table (§4.5)
  exact.rs        memoized exact solver (§3.2)
  stats.rs        MCGS statistics overlay (§4.3)
  mcgs.rs         playout loop, selection, expansion, backpropagation (§3.3)
  policy.rs       prior interface and the processors of §A.6
  session.rs      SearchSession and its single whole-search SearchToken (§4.7)
```

The interpreter gains two `Command` variants for §6; nothing else in the crate changes.

### 5.2 Container primitives

All persistent storage uses this repository's semi-persistent containers:

- semi-persistent `Vec<T, I, S>`: the workhorse. `mark()` pushes a frame (saved
  length, diff-log position) and returns a token; writes below the saved length log
  the old value once per index per frame (first-write-wins, enforced by a capture bit
  per element); `restore(token)` truncates or regrows to the saved length and replays
  the logged old values backward. The capture bit lives in one of two storage
  backends, chosen per field: `InlineStore` places the capture flag in `T::Repr` for
  `Tagged + Copy` types. It has zero extra space only when `Tagged` steals a spare bit,
  as dense ids do; primitive integer implementations use `(bool, T)` and are not
  zero-overhead. `ParallelStore` keeps a separate bitset beside the data and works with
  any `Clone` type. Starting a frame clears one bitset word per 64 elements for
  `ParallelStore`; `InlineStore` clears the tags named by the preceding frame's diff
  entries. Choose between them from the actual field type and benchmark, rather than
  assuming all ids and counters favor one backend. Tokens carry a container id, frame
  depth, and branch id; restore forks the branch genealogy, so a token from an abandoned
  future fails validation instead of corrupting state. All mutable statistics fields
  live in these vectors.
- `AppendOnlyVec<T>`: used push-only for structural elements; restore truncates to the
  saved length. The implementation exposes `get_mut`, but this design never mutates a
  structural element after pushing it.
- `Map`: an `AppendOnlyVec<(K,V)>` source of truth plus a transient
  `hashbrown::HashMap`; restore truncates the log and always rebuilds the hash map from
  the surviving entries. Used for modest caches in §5.4.

### 5.3 Id types

Every AU arena index is a `define_id31!` newtype, so ids from different arenas cannot be
confused and `Option<Id>` is pointer-sized: `AuClassId`, `OrId`, `AndId`, `ActionId`,
`ActionPairId`, `AndChildId`, `OrStatsId`, `AndStatsId`, `OrEdgeStatId`,
`AndEdgeStatId`, `PriorEntryId`, `OrParentListId`, `OrParentLinkId`, `CtxId`,
`TermId`, and `SccId`. The generic e-graph API uses
`Cfg::G` for e-node ids and class representatives, `Cfg::O` for operators, `Cfg::V` for
literal values, and `Cfg::M` for multiplicities; it does not expose separate `ClassId`
and `NodeId` types. The snapshot maps representative `Cfg::G` values to a design-owned
dense `AuClassId` used by contexts and reachability bitsets. Multiplicity is
checked-converted from `Cfg::M` to `u32` while building the snapshot; a value that does
not fit returns a construction error.

### 5.4 Arena schemas

The following Rust-shaped schema shows the enums, structs, and fields explicitly. Arena
structs use one container per field (struct of arrays). `Span<I>` is a typed `(start,
len)`, and the `*Tokens` structs bundle the concrete `VecToken`, `MapToken`, and
`ListArenaToken` values for the fields they cover:

```rust
#[derive(Clone)]
enum TermOp<O, V> {
    EGraph(O),
    Literal(V),
    Variants,
}

#[derive(Clone, Copy, Default)]
enum MemoState {
    #[default]
    Empty,
    Visiting,
    Solved(TermId),
}

struct OrArena {
    left: AppendOnlyVec<AuClassId>,
    right: AppendOnlyVec<AuClassId>,
    left_context: AppendOnlyVec<CtxId>,
    right_context: AppendOnlyVec<CtxId>,
    actions: AppendOnlyVec<Span<ActionId>>,
    terminal: AppendOnlyVec<bool>,
    min_size: AppendOnlyVec<u32>,
    max_size: AppendOnlyVec<u32>,
    by_key: Map<(AuClassId, AuClassId, CtxId, CtxId), OrId>,
}

struct ActionArena<Cfg: EGraphConfig> {
    operator: AppendOnlyVec<Cfg::O>,
    pairs: AppendOnlyVec<Span<ActionPairId>>,
    pair_left: AppendOnlyVec<AuClassId>,
    pair_right: AppendOnlyVec<AuClassId>,
    pair_count: AppendOnlyVec<u32>,
    by_class_pair: Map<(AuClassId, AuClassId), Span<ActionId>>,
}

struct AndArena {
    parent: AppendOnlyVec<OrId>,
    action: AppendOnlyVec<ActionId>,
    children: AppendOnlyVec<Span<AndChildId>>,
    child_or: AppendOnlyVec<OrId>,
    child_count: AppendOnlyVec<u32>,
    min_size: AppendOnlyVec<u32>,
    max_size: AppendOnlyVec<u32>,
    by_parent_action: Map<(OrId, ActionId), AndId>,
}

struct ContextStore {
    spans: AppendOnlyVec<Span<AuClassId>>,
    classes: AppendOnlyVec<AuClassId>,
    by_slice: Map<std::vec::Vec<AuClassId>, CtxId>,
}

struct Reachability {
    class_to_scc: std::vec::Vec<SccId>,
    scc_spans: std::vec::Vec<Span<u64>>,
    bit_blocks: std::vec::Vec<u64>,
}

struct BestResults {
    term: VecP<TermId, OrId>,
    exact: VecP<bool, OrId>,
}

struct TermArena<Cfg: EGraphConfig> {
    operator: AppendOnlyVec<TermOp<Cfg::O, Cfg::V>>,
    children: AppendOnlyVec<Span<TermId>>,
    child_pool: AppendOnlyVec<TermId>,
    size: AppendOnlyVec<u32>,
    by_structure: Map<TermKey<Cfg::O, Cfg::V>, TermId>,
}

struct ExactOverlay {
    memo: VecP<MemoState, OrId>,
}

struct OrStatsArena {
    structural: AppendOnlyVec<OrId>,
    initial_value: VecP<f64, OrStatsId>,
    value: VecP<f64, OrStatsId>,
    edges: AppendOnlyVec<Span<OrEdgeStatId>>,
    parents: AppendOnlyVec<OrParentListId>,
    by_structural: Map<OrId, OrStatsId>,
}

struct OrEdgeStats {
    action: AppendOnlyVec<ActionId>,
    child: VecP<Opt<AndStatsId>, OrEdgeStatId>,
    visits: VecP<u32, OrEdgeStatId>,
}

struct AndStatsArena {
    structural: AppendOnlyVec<AndId>,
    value: VecP<f64, AndStatsId>,
    round_robin_counter: VecP<u32, AndStatsId>,
    children: AppendOnlyVec<Span<AndEdgeStatId>>,
    parent: AppendOnlyVec<OrStatsId>,
    by_structural: Map<AndId, AndStatsId>,
}

struct AndEdgeStats {
    child: AppendOnlyVec<OrStatsId>,
    pair_count: AppendOnlyVec<u32>,
    visits: VecP<u32, AndEdgeStatId>,
}

struct PriorArena {
    by_or: VecP<Opt<Span<PriorEntryId>>, OrStatsId>,
    action: AppendOnlyVec<ActionId>,
    probability: AppendOnlyVec<f64>,
}

struct StatsOverlay {
    or_nodes: OrStatsArena,
    or_edges: OrEdgeStats,
    and_nodes: AndStatsArena,
    and_edges: AndEdgeStats,
    priors: PriorArena,
    or_node_parents: ListArena<AndStatsId, OrParentListId, OrParentLinkId>,
    playouts: u64,
    non_fully_expanded: u32,
    exploitation_count: u64,
    total_choices: u64,
}

struct StatsOverlayToken {
    containers: StatsContainerTokens,
    playouts: u64,
    non_fully_expanded: u32,
    exploitation_count: u64,
    total_choices: u64,
}

struct SearchToken {
    // One private component token for every container above. Callers cannot
    // access or restore these independently.
    structural: StructuralTokens,
    terms_and_results: ResultTokens,
    exact: ExactTokens,
    statistics: std::vec::Vec<StatsOverlayToken>,
}
```

Spans are `(start, len)` into shared pools. When an OR statistics struct is created, it
allocates one `or_edge` element for every structural action; `child = None` means that
action is unrealized, so later expansion mutates a fixed slot rather than trying to
append to a noncontiguous span. An AND statistics struct allocates all of its child-edge
elements at creation. An AND statistics struct has one direct OR parent because its
structural key contains that parent; an OR statistics struct may have many AND parents,
so `ListArena` stores its reverse-parent list. Lazy-AC matching states (§3.4.4) add two
structural enums with residual-multiset payloads and use the same statistics structs.

### 5.5 Restorable hash indices

`hashbrown::HashMap` alone is not semi-persistent. Every `Map` field shown in §5.4 uses
an `AppendOnlyVec` source of truth and rebuilds its transient hash map after restore. If
profiling shows that rebuilding a large insert-only cache dominates restore, that one
field may use the alternative already supported by the same container discipline:
push every inserted key into a tracked `AppendOnlyVec`, validate its token before any
mutation, restore the key log, and remove the abandoned keys from the hash map.

Both forms rely on branch-validated container tokens. A bare length watermark is
insufficient: after restore and regrowth the same length can describe a different future,
so every token carries the containers' branch genealogy.

### 5.6 Token and restore order

`SearchToken` contains the component tokens for every semi-persistent container in the
session plus snapshots of all scalar counters. `SearchSession::mark()` creates those
component marks together and returns only `SearchToken`; component tokens and component
restore methods remain private. `SearchSession::restore()` validates all component tokens
first and then restores them in the reverse dependency order of §4.7. This makes a mark
one coherent version of the complete search and prevents mixed-version states by API
construction.

### 5.7 Determinism

Golden traces require bit-stable runs. All iteration uses dense ids or explicit
sorted orders; hash maps never drive a decision directly; floating-point accumulation
follows ascending action index. Action lists preserve the e-graph's member order
because action indices and first-maximum tie-breaking depend on it. No stochastic
selector is specified; a future one must define its RNG and include its state in
`SearchToken`.

---

## 6. Script commands

Two commands make the whole workflow (build terms, saturate, extract anti-unifiers)
expressible in one `.egg` file, implemented as ordinary interpreter commands next to
`extract`:

```lisp
(anti-unify t1 t2 :playouts 2000 :policy uct)
(check-au   t1 t2 :max-size 9 :playouts 500)     ; asserts like check
```

Each command freezes the current e-graph, builds a session, runs, prints the result
(term, size, compression ratio, playouts, completion flag), and tears down; `push`/`pop`
around it behave as expected. `:algorithm` selects `syntactic`, `eager_with_memo`,
`uct`, or `puct` (§3.5); the remaining options select the AND selector, prior
processor, cycle mode, playout budget, reporting stride, and AC materialization bound.

## 7. Configuration

Defaults: 1000 playouts, report stride 1000, saturation iterations 4,
C = √2, x_target = 0.8, A_max = 32, `CycleMode::AncestorOnly`, UCT OR selection,
round-robin AND selection, shared edge-visit statistics, and path-only updates. If PUCT
is selected, its default prior is uniform and is computed at every OR node.

All constants, orderings, and formulas here are the specification; changing any of them
changes golden traces.

## 8. Testing

1. **Oracle equality**: on small instances, MCGS run to completion equals the exact
   algorithm's size when both use the same action model and `CycleMode`; every
   intermediate result is valid (both projections land in the root classes) and never
   smaller than the oracle's optimum.
2. **Invariants**: property tests drive random playouts and whole-session
   `SearchSession::mark`/`restore` operations, then check §4.6 and complete observable
   state equality against a shadow model; no test or API restores an individual layer.
   The AC counting table, multiplicity subtraction, and the greedy counterexample of
   §3.4.4 are pinned as unit tests.
3. **Conformance corpus**: the anonymized case files under `egraph/tests/` (twenty
   semantic pairs plus policy, projection, conversion, and preprocessing cases) drive
   both algorithms once implemented; the anonymizer script regenerates cases with
   per-case stable `v1, v2, …` naming.

---

## Appendix A. Reference algorithms

Deterministic pseudocode; golden fixtures are generated from these definitions.

### A.1 Reachability

§2.4 is normative: SCC condensation, reverse-topological bitset union, one bitset per
SCC, cyclic SCCs include themselves.

### A.2 Best member term

```text
best(e):  cost[c] = ∞ for all classes; repeat until fixpoint:
              for every e-node n: t = 1 + Σ mult(child)·cost[class(child)]
              if t < cost[class(n)]: cost[class(n)] = t, keep n
          reconstruct by following kept nodes (repeat AC children per multiplicity)
```

The fixpoint scans e-node ids in ascending order on every pass and replaces a kept
member only on strict improvement, so equal-size ties keep the first id.

### A.3 Syntactic seed

```text
seed(t1, t2) = t1                                  if t1 == t2 structurally
             = Variants(t1, t2)                    if operators or arities differ
             = op(seed(c1_i, c2_i) for i)          otherwise (positional zip)
```

### A.4 Greedy rollout

The rollout uses the same state, `CycleMode`, action generator, and child-context
transition as the main search:

```text
greedy_rollout(state):
    if state.l == state.r:
        return best_term(state.l)
    action = first(actions(state))
    if action exists:
        return apply(action.op,
                     [greedy_rollout(child(state, l_i, r_i))
                      for each pair occurrence (l_i, r_i) in action])
    return Variants(best_term(state.l), best_term(state.r))
```

The first surviving action in cached order wins. Through an AC operator that is the
greedy diagonal matching, which is ordering, not pruning (§3.4.4).

### A.5 Exact solver

§3.2 is normative, with the lazy-AC recursion of §3.4.4 for oversized matrix spaces and
piece-bag accumulation for their partial results (canonical term order, counts merged).

### A.6 Prior processors

Uniform: `1/n` over the n actions. Ranked lists: K queries of top-N indices; each index
at rank k accumulates `1/(k+1)`; normalize; add α = 0.01 to every action of the node;
renormalize. Single votes: a fixed 100 queries; `count/100` per index. Full distribution:
use the first response and normalize by its positive total.

Every response is validated (finite, nonnegative, in-range) and a positive floor is
applied before final normalization so PUCT retains completeness.

## Appendix B. Worked AC example

`AU(and{a,b,c}, and{b,c,d})`: totals are equal and all multiplicities 1, so the actions
are the 3! = 6 bijections; after reducing `AU(x,x) → x`:

```text
1. and{ b, c, AU(a,d) }        # greedy diagonal: b,c pair with themselves
2. and{ AU(a,b), AU(b,c), AU(c,d) }
3. and{ AU(a,b), AU(b,d), c }
4. and{ AU(a,c), b, AU(c,d) }
5. and{ AU(a,c), AU(b,d), AU(c,b) }
6. and{ AU(a,d), AU(b,c), AU(c,b) }
```

`AU(b,c)` and `AU(c,b)` are distinct states: `Variants` projections are ordered, so the
two orientations are different subproblems (swapping every Variant arm maps one result to
the other at equal size). Repeated children compress: `AU(or{a,a}, or{b,b})` has exactly
one matrix, one child `AU(a,b)` with count 2. Compare §3.4.4's table for what the same
example costs with explicit rewrite encodings.
