# Chapter 19 — Anti-Unification

[← Ch 18: Semi-Naive Evaluation](18-semi-naive-evaluation.md) · [Table of Contents](00-table-of-contents.md)

**Status**: implemented (`egraph/src/au/`). Both the exact solver and MCGS use
min-cost transportation for AC/ACI (§3.4.4); MCGS uses one transport-AND-node per
feasible representation pair (cells as bandit arms, no matrix enumeration) and
reports a structural completion certificate. AU id widths follow
`EGraphConfig::Au` (31-bit under `DefaultConfig`, 63-bit under `Config64`).
Unequal-length associative (Seq) factoring and other extensions are future work;
see [`doc/future/au-associative-operators.md`](../future/au-associative-operators.md).
**Contents**: this chapter defines the data structures and two algorithms for computing
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
- Every unequal OR node has the terminal generalize action from §A.3,
  `Variants(best_term(l), best_term(r))`; structural actions may improve it.

Subproblems repeat massively (the same class pair is reached through many factorings),
so the space is a directed acyclic **graph**, not a tree, and we share nodes.

The design uses **layered graphs**: the bottom layer contains the nodes and edges that
represent the search space itself; an upper layer contains the nodes and edges that store
the statistics used by a search heuristic. MCGS owns one statistics overlay (§4.3); the
exact solver's overlay is its memo table. Nothing in the bottom layer points upward, so
overlays coexist without interfering. Each algorithm publishes its concrete results to a
best-result table (§4.5).

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

Both algorithms minimize term size as the primary objective, then variant mass as a
secondary tiebreak (see Appendix C.1). The reported compression ratio is the linear
ratio that compares a result against the two smallest root representatives:

```text
compression_ratio(t, l, r) = (size(t) - a) / b

where  a = min(best_size(l), best_size(r))
       b = max(best_size(l), best_size(r))
```

MCGS uses a bounded monotone transformation of the expected size, applied only inside
selection, to map the unbounded range [0, +inf) into [0, 1) for UCT:

```text
local_cr(n)  = (E[size](n) - a_n) / b_n
normalize(n) = 0                              if local_cr(n) <= 0
             = 1 - exp(-lambda * local_cr(n))   lambda = -ln(1 - x_target), x_target = 0.8
reward(n)    = 1 - normalize(n)
```

For a given OR node `n = AU(l, r, ...)`, the constants `a_n` and `b_n` are
`min(best_size(l), best_size(r))` and `max(best_size(l), best_size(r))`: the node's
own class-pair representative sizes. All actions at one parent OR node are normalized
with that single pair; using per-action constants (e.g. child-pair extrema) can invert
the size preference between two sibling actions and is unsound (see below).

The scale is `b_n` (not `b_n - a_n`). With this choice the bare-Variants no-sharing
result (size approximately `a + b`) gives `local_cr` approximately 1, i.e.
`normalize(Variants) = x_target`. A `max - min` scale would give zero whenever both
representatives have equal size (the common case), saturating every non-perfect
candidate at 1 and collapsing the ranking. The `b_n` scale retains strict size ordering
everywhere.

Worked ranking (basis a=5, b=10); the bare-Variants point lands on `x_target`:

```text
size  local_cr  normalize  reward   meaning
  5    0.00      0.0000     1.0000   perfect: AU equals the smaller input
  7    0.20      0.2752     0.7248   good compression
 10    0.50      0.5528     0.4472   moderate: at the larger input's size
 15    1.00      0.8000     0.2000   bare Variants (no sharing)
 25    2.00      0.9600     0.0400   poor: blowup past the inputs
 45    4.00      0.9984     0.0016   degenerate
```

Same formula with equal-size representatives (basis a=5, b=5); the scale stays nonzero:

```text
size  local_cr  normalize  reward
  5    0.00      0.0000     1.0000
  6    0.20      0.2752     0.7248
  8    0.60      0.6193     0.3807
 10    1.00      0.8000     0.2000
```

Per-action normalization inversion example: actions A (expected size 10) and B
(expected size 12) at one OR node with basis a=5, b=10. Shared-basis ranking gives
`normalize(A) = 0.55`, `normalize(B) = 0.68`, so A wins on reward. If instead each
action uses its own child-derived basis (A with a=2, b=2; B with a=11, b=11), then
A normalizes as `(10-2)/2 = 4.0` giving 0.998, while B normalizes as `(12-11)/11 = 0.09`
giving 0.136: the larger action appears better, reversing the true preference.

Statistics are tracked and backpropagated in raw size units. Sums of sizes are
meaningful (an AND node's size is 1 plus the weighted sum of its children's sizes);
sums of nonlinear rewards are not. The exponential normalization is applied only at
selection time, to the already-averaged expected size; this computes
`normalize(E[size])` rather than `E[normalize(size)]`, which cannot be recovered from
expectations of a nonlinear function. The approximation is deliberate: the
normalization is monotone, so candidate rankings are preserved, and selection needs
rankings, not calibrated expectations. It is distinct from the reported compression
ratio.

#### 2.5.1 Normalization and convergence requirements

The search is a deterministic additive-cost decision process: OR states, factoring
actions, AND transitions whose child costs sum, terminal costs fixed by `best_term`.
Per OR state `s`, define `a_s = min(best_size(l), best_size(r))` and
`b_s = max(best_size(l), best_size(r))`. The linear compression ratio is
`CR_s(t) = (size(t) - a_s) / b_s`, and the selection reward is:

```text
R_s(t) = 1 - normalize(CR_s(t)) = exp(-lambda * CR_s(t))      for CR_s(t) > 0
```

Landmarks: perfect compression (size = a_s) gives reward 1; bare no-sharing result
(size = a_s + b_s, CR = 1) gives reward 1 - x_target; unbounded size gives reward
approaching 0. Since a_s and b_s are constants of the state and the map is strictly
increasing, for any two candidates of one state:

```text
size(t1) < size(t2)  <=>  CR_s(t1) < CR_s(t2)  <=>  R_s(t1) > R_s(t2)
```

The compression-optimal policy is therefore the minimum-size policy; the normalizer
exists to satisfy UCT's bounded-reward assumption, not to change the objective.

Expectation must come before normalization. Aggregation needs the additive unit (AND
combination and expectation commute only with linear maps); selection needs a bounded
unit (the exploration term is dimensionless, calibrated against [0,1]). The only safe
placement for a nonlinear map is a comparison after which no further composition
occurs, i.e. the within-node argmax. Since CR is affine, `g(E[CR])` is equivalent to
minimizing `E[size]`. The alternative `E[g(CR)]` (averaging normalized rollout rewards,
as vanilla game MCTS does) is a different, risk-sensitive objective: by Jensen it can
prefer a policy with worse expected size but greater variance. Averaging normalized
rewards is prohibited.

Convergence properties. UCT's policy at every OR node converges to the minimum-size
(maximum-compression) action provided:

- A (objective alignment): all actions of one state are scored through the same
  strictly increasing transform with that state's own (a_s, b_s). Action-dependent
  transforms break `Q_A < Q_B => R_A > R_B`; the §2.5 inversion example is stable at
  every visit count, misdirecting search. State-dependent normalization is safe;
  action-dependent is not.
- B (stationary basis): (a_s, b_s) are immutable for the session; never empirical
  running extrema, never action-specific descendants. A drifting scale makes
  historical statistics incomparable.
- C (denormalized compositionality): the §2.6/§3.3 value equations operate entirely
  in raw size units; no normalized reward enters an AND sum.
- D (consistent estimators): edge estimates converge to true values; idempotent
  recomputation from converging child values (§2.6) satisfies this. The permanent
  first sample U(s) has weight 1/(1 + sum_a N(s,a)), vanishing asymptotically.
- E (infinite exploration, vanishing waste): `C * sqrt(sum_N) / (1 + N(s,a))` diverges
  for any neglected action, so every action is selected infinitely often. A
  suboptimal action with reward gap delta stops being selected once roughly
  `N(s,a) ~ C * sqrt(N(s)) / delta`, giving O(sqrt(N)) suboptimal visits; the optimal
  action's fraction approaches 1 (modulo equal-quality ties).
- F (fair AND refinement): every child of a realized AND node that still needs
  refinement is refined infinitely often. Round-robin (§3.3.5) provides this directly
  by rotation. The value-guided selectors (`uct_and`, `lct_and`, §3.3.5) provide it
  through their exploration term, `C · sqrt(Σ_j N(n,j)) / (1 + N(n,i))`, which
  diverges for any neglected non-terminal child; terminal children are skipped, which
  is admissible because their values are exact and immutable — fairness exists to
  converge child estimates, and a terminal's estimate is already converged. A
  heuristic AND selector without such a guarantee would starve a child and leave the
  additive AND value permanently biased.
- G (complete action language): every action able to contain the optimum stays
  reachable. The implementation satisfies this on the AC/ACI path with transport
  actions (every feasible matrix is implicitly reachable through the flow argmin
  over cell estimates, §3.4.4); no action-count truncation exists in production. The
  bounded row-by-row enumeration survives only as a test oracle.
- H (parent-edge-local counts): selection reads only N(s,a), never a shared child's
  total visits (§2.6); otherwise one parent's exploration suppresses another's action.
- I (eventual propagation): every child improvement eventually reaches every parent.
  Path-only backpropagation suffices given E and F (every path is revisited infinitely
  often); ancestor-subgraph propagation accelerates but is not required (§3.3.3).
- J (monotone publication): the best-result table improves strictly monotonically
  under the contractual order (size, variant_mass) (§4.5, Appendix C.1); it is a
  separate structure from the expected-size search statistics.
- K (valid numerics): best_size > 0; 0 < x_target < 1; all values finite; no NaN or
  infinity reaches a score comparison; ties broken deterministically (§5.7). The
  `CR <= 0` clamp is unreachable for distinct classes (a valid anti-unifier projects
  into both classes, so size >= b_s, and contains at least one Variants); it fires
  only at l = r terminals, whose values are exact.

Convergence argument. On the finite context-quotiented DAG: terminals hold exact sizes;
by E and F every edge is visited infinitely often; by D and induction from the leaves
upward, child estimates converge; by C every AND value converges; by A and B the common
monotone transform preserves the converged ordering, so by E suboptimal visit fractions
vanish and each OR value converges to its minimum child value; by I improvements reach
the root; by J the root entry receives the optimum of the action model. The residual
gap between ranking by E[size] and ranking by minimum achievable size closes by the
same concentration: as the policy concentrates below an action, its expected size
converges toward its minimum.

Equal-size ties. Size-derived metrics cannot separate equal-size candidates (Appendix
C.1); UCT keeps expected size as its value, E guarantees all equal-size actions are
examined, and the best-result table applies the (size, variant_mass) order. A
finite-budget tie-optimization, if ever needed, must be lexicographic; a weighted
scalar blend is inadmissible unless a proven bound shows the secondary term can never
outweigh a one-unit size difference.

#### 2.5.2 Verification properties

The properties A through K above are not design-time prose; they are testable
invariants, numbered 1 through 11:

1. Order preservation (A): for random q1 < q2 and any shared basis (a, b) with b > 0,
   reward(q1) > reward(q2).
2. Common-basis invariant (A, B): every action scored at one OR node within one
   selection call uses the same (a, b) pair.
3. No action-local reversal (A): on the §2.5 inversion example, a shared-basis
   selection prefers the smaller-size action.
4. Landmarks (K): for any a, b with b > 0 and any x_target in (0,1),
   normalize(0) = 0, normalize(1) = x_target (within epsilon), and normalize(x) < 1
   for all finite x.
5. Expectation-order (C): the implementation computes g(E[CR]), never E[g(CR)].
6. AND additivity (C): after every AND recomputation, Q_AND = 1 + sum of
   count_i * Q_child_i.
7. Fairness (E, F): after 1000 playouts, every OR-edge visit count and every
   AND-child visit count is at least 1.
8. Exact-oracle convergence (E, I, J): on randomly generated finite small graphs (at
   most 5 classes, at most 3 members per class), MCGS with increasing budget reaches
   the exact solver's (size, variant_mass).
9. Shared-DAG propagation (H, I): a child improvement reaching a node shared by two
   parent OR nodes eventually becomes visible to both parents.
10. Monotone publication (J): every best-result offer that returns true strictly
    improves the entry's quality.
11. AC completeness qualification (G): MCGS with transport actions and the exact
    solver agree on AC instances whose matrix count would defeat any bounded
    enumeration (both use flow; no truncation).

Properties 1, 3, 4, 6, 7, 8, 10, and 11 are pinned as proptest-driven tests in
`egraph/tests/au_convergence_props.rs` (random e-graphs, random class pairs, random
playout budgets). Properties 2 and 5 hold by construction: the basis is stored once
per OR-statistics node (`min_size`/`max_size`, §5.4) and read from that single place
by the selection formula, and the normalization is applied only in `select_uct` to
the already-averaged Q value. Property 9 is pinned by the shared-DAG closure tests in
`egraph/src/au/mcgs.rs` (`shared_dag_completion_is_exact`,
`completion_closes_values_through_every_shared_parent`).

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
estimate onward.

### 2.7 What correctness means here

- **Anytime validity**: every result stored anywhere is a valid anti-unifier of its
  node's class pair, by construction (§3.1, §A.3).
- **Exactness**: the memoized recursive algorithm (§3.2) returns the minimum-size
  anti-unifier expressible in the action language and cycle policy; this is proved by
  induction over its well-founded recursion.
- **MCGS convergence**: with finite action sets, every action selected infinitely
  often, and idempotent value recomputation, node values converge to the exact
  values for the same action model and `CycleMode`; when the search graph has been fully
  expanded, the best stored result equals that exact optimum. Before that point MCGS is a
  heuristic anytime algorithm bounded below by the oracle's optimum.

---

## 3. The two algorithms

When configured with the same `CycleMode`, both algorithms search the same AND/OR graph,
use the same action generators (§3.4) and node/action-cache structures, intern their
results in the same term-pool structure (§4.4), and publish to a best-result table
(§4.5). Each solver invocation owns its layers: `anti_unify` allocates fresh layers per
call, while `SearchSession::run_uct` reuses the session's layers across UCT runs (§4.7).

### 3.1 Shared building blocks

- `best_term(e)` / `best_size(e)`: the smallest concrete member term of class e,
  precomputed for all classes by the standard fixpoint
  `cost(node) = 1 + Σ multiplicity(child) · cost(class(child))`, minimized per class
  (§A.2).
- `generalize(l, r)`: the shared terminal action yielding `best_term(l)` when
  `l = r`, or `Variants(best_term(l), best_term(r))` otherwise (§A.3). Every OR
  node's stored best result is initialized with it, so a valid answer exists from
  the first instant.
- `child(l, r, l2, r2)`: node-cache lookup of the child state, deriving contexts per
  §2.3.
- Results are interned in the term pool; replacement anywhere is strict under
  `(size, variant_mass)`.

### 3.2 Reference algorithm: eager_with_memo

`eager_with_memo` is dynamic programming over the cycle-context states for one selected
`CycleMode`: an eager recursion that enumerates every surviving action and takes the
minimum, with memoization on states (specified recursively here; implemented with an
explicit frame stack, §5.1).
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
        best = generalize(state.l, state.r)
        for action in actions(state):                  # §3.4, cycle-filtered
            children = [ exact(child(state, l_i, r_i)) # each pair occurrence
                         for (l_i, r_i) in action.pairs ]
            candidate = apply(action.op, children)     # AC ops: canonical child order
            if quality(candidate) < quality(best): best = candidate
    memo[state] = Solved(best)
    publish(state, best)                   # offer to the best-result table, set exact flag
    return best
```

Termination follows from the selected cycle mode (§2.3): `CurrentInclusive` permits each
class at most once per side on a recursion path; `AncestorOnly` permits it at most twice.
A `Visiting` re-entry would violate that rank invariant, so the implementation treats it
as unreachable and fails loudly rather than silently falling back. Optimality follows by
induction over this finite graph: every child result is optimal, and the minimum over
all actions (with AC/ACI operator pairs solved by the transport optimization of §3.4.4)
plus the terminal generalize action is optimal.

The generalize action is always a candidate. It provides a projection-valid whole-term
result when structural actions are absent or blocked and makes the exact solver's
objective identical to MCGS's shared best-result objective.

The exact algorithm doubles as the **correctness oracle**: on instances small enough to
exhaust, MCGS and exact search configured with the same action model and `CycleMode` must
return the same size; every intermediate MCGS result must be valid and no smaller than
the oracle's optimum.

### 3.3 Monte-Carlo graph search

A run first seeds the root: the terminal generalize action is offered as a
projection-valid incumbent, then the action-aware initial rollout (§A.4) supplies the
root's first estimate U(root) and offers its term. Then one iteration ("playout"):

```text
playout(root):
    # 1. SELECTION: walk down while nodes are fully expanded
    path = []                                           # AND nodes, root-side first
    node = root
    loop:
        if node is terminal: break                      # Q(node) is its stored best size
        if node has an unrealized action:               # lowest action index first
            a = that action
            N(node, a) += 1                             # edge visit, then expansion
            and_node, fresh_children = EXPAND(node, a)  # §3.3.1
            path.push(and_node)
            for child in fresh_children:                # 2. ROLLOUT (§3.3.2)
                Q(child) = size(initial_rollout(child)) # §A.4; term offered too
            break
        a = select action at node by UCT (§3.3.4)
        N(node, a) += 1
        and_node = realized AND node of edge a
        path.push(and_node)
        i = AND-selector child of and_node (§3.3.5)     # AND edge visit N(and, i) += 1
        node = child_i

    # 3. BACKPROPAGATION (§3.3.3): deepest AND first, then rootward
    for and_node in reverse(path):
        recompute Q(and_node); compose and offer its result
        recompute Q(parent OR of and_node)
```

Value equations, recomputed idempotently at every update (§2.6):

```text
OR node:            Q(n) = (U(n) + Σ_a N(n,a) · Q(and_a)) / (1 + Σ_a N(n,a))
fixed AND node:     Q(n) = 1 + Σ_i pair_count_i · Q(child_i)
transport AND node: Q(n) = 1 + min_X Σ_ij x_ij · Q(cell_ij)    # X = transport argmin
```

and every update also offers the children's stored best results, composed through the
AND node, to the parent OR node's entry in the best-result table (strict improvement
only). That composition step is what lets the search improve past its initial rollout
and converge to the exact optimum on exhausted graphs.

The subsections below define each phase precisely.

#### 3.3.1 Fully expanded, terminal, and expansion

An OR node's statistics struct is created on first contact (through the OR-to-statistics
index) knowing its cycle-filtered action count, its normalization sizes, and its
terminal flag. A node is **terminal** when `l = r`, when no action survives cycle
filtering, or when its best-result entry is already marked exact; terminal nodes take
their stored best size as their permanent value. A nonterminal node is **fully
expanded** when every one of its actions has a realized outgoing edge.

Selection realizes unrealized actions strictly in ascending action-index order: while
any action is unrealized, the scoring formula is not evaluated at all.
`EXPAND(node, action)` allocates the AND statistics node for the action, looks up or
creates **all** its child OR nodes through the node cache, obtains all child OR
statistics structs through the OR-to-statistics index, and offers each child's
generalize seed to the best-result table. It returns the newly created child statistics
structs for rollout; existing shared children keep their current values. The new OR
edge starts with visit count 1 (the visit is counted before the expansion check).
Expanding never restructures an existing edge; it fills one previously empty action
slot. Each AND statistics node stores its one parent OR id; there are no reverse
parent lists.

For an AC/ACI transport action, expansion creates one child OR node per **legal cell**
of the representation pair (cycle-blocked cells stay `None` in the cell map and are
forbidden transport edges); the AND node stores the row/column margins and the typed
cell map (§4.3, §5.4).

#### 3.3.2 Rollout

Every newly created child statistics struct of the expanded AND node needs a first
value estimate, taken in the same playout. An existing shared child already has one.
The rollout is the deterministic action-aware initialization of §A.4: it scores the
terminal generalize action and every surviving structural and transport action with
static concrete estimates, then recursively follows only the selected action. Its term
is also a valid result and is offered to the best-result table, so even the first
playout produces a valid global answer.

#### 3.3.3 Backpropagation

Backpropagation is **path-only**: it walks the AND nodes collected on the traversed
path, deepest first, then rootward. Each AND node recomputes its value idempotently
from its children's current values (for transport AND nodes, one flow solve over the
current cell Q estimates, which also refreshes the derived child multiplicities),
composes its children's stored best results into a candidate term, offers it to its
parent OR node's best-result entry, and the parent recomputes its value. Children are
thereby processed before parents along the path.

On the shared DAG, a parent not on the traversed path can hold a momentarily stale
value; it picks up the improvement on its next visit (§2.6). Before certifying an
exact completion, one deterministic children-first closure pass over the completed DAG
recomputes every value and recomposes every AND result, propagating final child values
through **every** incoming parent (§3.3.7). Ancestor-subgraph propagation during
playouts (updating all parents of a shared node immediately) is a sound alternative
that trades cost for freshness; the implementation uses path-only updates plus the
closure pass.

#### 3.3.4 Selection and expansion rules at OR nodes

All rules and formulas are normative. The chosen edge's visit count is incremented
first, and only then is the edge checked for realization, so a new edge is born with
visit count 1. Expansion is strictly sequential and unconditional: while any action is
unrealized, the selector returns the lowest unrealized action id and the scoring
formula is not evaluated at all. Scoring begins only at fully expanded nodes:

```text
score(a) = (1 − normalize(Q(and_a)))  +  C · sqrt(Σ_b N(n,b)) / (1 + N(n,a))
C = √2
```

Scores are evaluated in ascending action-id order and the first maximum wins, so ties
choose the smallest id. The exploration numerator is the node's own total edge visits,
never the child's visit count (§2.6). All actions are normalized against the parent OR
node's own `(a_n, b_n)` basis (§2.5.1 property A); per-action bases can invert the size
preference. Exploration is uniform across actions, so UCT always pays one visit to
every sibling (width) before it can revisit anything (depth).

UCT is the only implemented OR-node selection policy. PUCT (prior-guided selection) is
future work; see [`doc/future/au-associative-operators.md`](../future/au-associative-operators.md).

#### 3.3.5 Effort allocation at AND nodes

An AND node does not choose an outcome; all children must be solved, so its selector
decides where the next unit of refinement effort goes. Child-edge visits `N(n,i)` are
incremented exactly like OR edge visits. Three selectors are implemented, chosen by
`and_selector` in the MCGS configuration:

```text
round_robin:  i = counter mod arity;  counter += 1        # equal effort by rotation
uct_and:      argmax_i (1 − normalize(Q(child_i))) + C · sqrt(Σ_j N(n,j)) / (1 + N(n,i))
lct_and:      argmin_i (1 − normalize(Q(child_i))) − C · sqrt(Σ_j N(n,j)) / (1 + N(n,i))
```

For the value-guided selectors, each child's Q is normalized against that child OR
node's own `(a, b)` basis (§2.5.1 property A: per-node basis). Scores are evaluated in
ascending child order with strict improvement, so ties resolve to the smallest scored
child index. `uct_and` refines the most promising child; `lct_and` selects by lower
confidence bound, deliberately visiting the weakest child (an AND result's size is a
sum, so its quality is limited by its worst child).

**`lct_and` is the default.** It routes effort to the least-certain child, so
unexpanded/incomplete subtrees receive nearly all flux until they close, making
structural certification (§3.3.7) cost proportional to graph size instead of
exponential in depth. Round-robin halves flux at every 2-child AND level, so
certifying a depth-d branching spine needs ~2^d playouts (measured: depth 8 certifies
at 1000 playouts, depth 16 fails at 16000 and certifies at 64000); `lct_and` certifies
the same spines at ~depth+1 playouts (measured: 17 at depth 16, 301 at depth 300,
401 at depth 400; pinned in `egraph/tests/au_deep_term_stress.rs`).

**Terminal-skip gate.** The value-guided selectors skip children whose OR node is
terminal. A terminal child can never change the completion certificate and its Q is
exact and immutable, so visiting it refines nothing. The gate is required: the bare
formulas do not starve terminal children on near-ties (a converged spine child's
reward approaches the terminal sibling's reward of 1, and the exploration term then
forces near-equal allocation, reproducing the round-robin 2^-depth decay); pinned by
`lct_and_without_terminal_skip_splits_flux_on_near_ties` in `egraph/src/au/mcgs.rs`.
When every child is terminal the choice is inert and the smallest index is returned.

Fairness (§2.5.1 F): `round_robin` guarantees every child equal visits regardless of
values. `uct_and`/`lct_and` are fair through their exploration term, which diverges
for any neglected non-terminal child; terminal children need no refinement, so
skipping them does not violate F. The round-robin counter is per AND statistics node,
part of the overlay state (§5.4), and is maintained under every selector.

#### 3.3.6 Priors and the visit distribution

A prior is a pre-existing action policy: a probability distribution over an OR node's
action ids obtained before any exploration of that node. No priors are implemented:
UCT explores uniformly, and rewards come only from rollouts and backpropagation. The
root's normalized edge-visit distribution `N(root,a) / Σ_b N(root,b)` is the natural
training target for a future prior model, and PUCT is the selection rule that would
consume such priors; both, together with the prior-processor formats, are specified in
[`doc/future/au-associative-operators.md`](../future/au-associative-operators.md).

#### 3.3.7 Complete search

The search is **complete** when every reachable OR statistics node is terminal or
fully expanded with every expanded AND node complete (an AND node is complete when
every child OR node is complete). The certificate is checked by one memoized
traversal from the root; a node still on the active path (an unresolved cycle in the
statistics DAG) conservatively fails the check. When the certificate holds, the
children-first closure pass of §3.3.3 runs, and the result is reported with
`Completion::Exact`: by induction over the closed acyclic graph, the best-result table
then holds the exact optimum. Otherwise the run reports
`Completion::BudgetExhausted { playouts_used }`. Until completion the algorithm is
anytime: the root's stored result is always valid and only improves.

#### 3.3.8 Main loop and reporting

Run exactly the configured number of playouts (a run on a terminal root runs none),
then check the completion certificate. The result carries the best term (renderable as
surface syntax), its size, the completion flag, and the algorithm that produced it;
the linear compression ratio of §2.5 is computed on demand (`compression_ratio`). The
interpreter commands of §6 print size, compression ratio, completion, and the
pretty-printed term.

### 3.4 Action generation per node kind

Actions for `AU(l, r)` are computed per operator common to both classes, then filtered
by the node's cycle contexts (drop an action if any pair hits the active `CycleMode`
set). The raw per-operator lists are cached by the class pair `(l, r)` and shared across
contexts; after generation, actions are deduplicated by canonical
(left, right, count) pair signature, because rewrite-derived equivalent members of one
class can produce identical actions from different member pairs, and duplicates would
otherwise surface as separate statistics edges, biasing selection toward the duplicated
action. The e-graph stores each operator's nodes in the canonical form of its kind,
and the generator dispatches on that kind. Plain ordered nodes (`Plain0..3`, `PlainK`)
use exactly the classic rule, positional zipping of same-operator, same-arity member
pairs (§3.4.1); the canonical `SPair`, `Seq`, `MSet`, and `Set` kinds are a strict
extension of that action language (§3.4.2–3.4.5). AC/ACI (`MSet`, `Set`) operator
pairs are not materialized as cached actions on the production paths: both solvers
handle them through min-cost transportation over canonical representation pairs
(§3.4.4).

#### 3.4.1 Ordered operators (fixed arity and ordered variadic)

Children are positional. For every member of l and member of r with the same operator and
arity, emit one action pairing children positionally. Duplicate pairs stay explicit.
A nullary member pair emits one action with no children.

#### 3.4.2 Commutative binary operators (sorted pairs)

Children are stored sorted, so the stored order is not an alignment. For members
`f(a,b)` and `f(c,d)` emit two actions, `{(a,c),(b,d)}` and `{(a,d),(b,c)}`, dropping the
second when it equals the first (a = b or c = d).

#### 3.4.3 Associative operators (sequences)

Members are variadic ordered sequences. The implemented rule is: one positional action
when the lengths are equal, none otherwise. Unequal-length member pairs contribute no
structural action; the terminal generalize action covers them. Aligning unequal
lengths requires grouping subsequences and is designed in
[`doc/future/au-associative-operators.md`](../future/au-associative-operators.md).

#### 3.4.4 AC operators (multisets), and why canonical storage wins

Each AC e-node stores its children as one canonical sorted multiset of
(child class, multiplicity) pairs. An e-class may contain several AC e-nodes for the same
operator when saturation proves distinct multisets equivalent; action generation handles
every pair of such members. For one member pair
`M = {a₁^{m₁}, …}` and `N = {b₁^{n₁}, …}` with equal total multiplicity, factoring
means choosing which copies pair with which. An action is a **matching-count matrix**
X: rows are M's distinct children, columns are N's, cell `x_ij ≥ 0` counts the copies
of `AU(aᵢ,bⱼ)`; row i sums to `mᵢ` and column j to `nⱼ`, so both sides are consumed
exactly. Each nonzero cell contributes one child subproblem with multiplicity `x_ij`; a
diagonal cell `AU(x,x)` reduces to x. (The row/column totals are classically called
the matrix's margins.)

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
count and from the column's residual multiplicity.

**Unequal totals and identity padding.** Unequal totals cannot be consumed by one-to-one
pairing. When the operator has a declared identity element `e` (`:identity`), the shorter
side is padded with identity copies to equalize the totals: `op{a, b, c}` versus
`op{b, c}` becomes `op{a, b, c}` versus `op{b, c, e}`, and the standard matrix machinery
applies. The padding is sound because `op{..., e} = op{...}` in the algebra (the identity
drops by canonization), so the padded multiset represents the same class and both
projections remain valid members. Unmatched elements pair against the identity, appearing
as `Variants(element, e)`: present on one side, vacuously absent on the other. The same
mechanism covers the singleton-collapse case: canonization reduces a one-child
application `op(t)` to the bare child `t`, so a class can participate in an `op`
factoring without exposing an `op` member. When the operator declares an identity,
every class therefore also has the **virtual singleton** representation `{class¹}`
(reading `op(x) = x` through the identity collapse), even when the class has explicit
`op` members as well; the padding above then applies. Without a declared identity,
unequal-total member pairs contribute no structural action and the terminal generalize
action remains available. (An alternative completion by nonempty submultiset *blocks*,
where associativity lets a block act as one child, is future work; see
[`doc/future/au-associative-operators.md`](../future/au-associative-operators.md).)

**The matrix space is a transportation polytope.** Fix the margins: row sums
`m₁..m_r` (left multiplicities) and column sums `n₁..n_c` (right multiplicities), with
equal totals. Relax integrality and consider all real matrices with nonnegative entries
and those margins; every constraint is linear, so this set is a convex polytope, the
classical *transportation polytope* (supplies `mᵢ`, demands `nⱼ`, `x_ij` the amount
shipped from supplier i to consumer j; our matching is that problem with copies of
children as the shipped units). Two classical facts connect it to the search:

1. *Linear cost.* The action cost is `1 + Σ_ij x_ij · c_ij`, where `c_ij` is the optimal
   size of the child subproblem `AU(aᵢ, bⱼ)`; `c_ij` is a constant of the parent state
   (child contexts derive from the parent, not from the matrix), so the cost is linear in
   the entries. A linear function over a polytope attains its minimum at a vertex; an
   interior point is a convex combination of vertices and can never beat all of them.
   The same holds for variant mass, and for the lexicographic pair: the minimum of the
   secondary objective over the optimal face of the primary is again at a vertex.
2. *Integer vertices.* The constraint matrix of a transportation polytope is totally
   unimodular, so with integer margins every vertex is an integer matrix: the LP corners
   are exactly valid matching-count matrices.

A feasible matrix is a vertex precisely when its *support* (the bipartite graph with an
edge (i,j) for each nonzero cell) is a forest, i.e. contains no cycle: around any support
cycle, flow can be shifted by ±ε on alternating edges while preserving all margins, which
exhibits the point as a midpoint of two feasible neighbors. A vertex support has at most
`r + c − 1` nonzero cells. Worked instance with margins [2,1] × [2,1]: the feasible set is
the segment `x₀₀ = t, x₀₁ = 2−t, x₁₀ = 2−t, x₁₁ = t−1` for `t ∈ [1,2]`, whose two
endpoints are `[[1,1],[1,0]]` (three-cell forest) and `[[2,0],[0,1]]` (diagonal); the
interior point `t = 1.5` has a four-cell support forming a 4-cycle.

**Enumeration: complete, not vertex-restricted (test oracle only).** In principle only
vertices can be optimal, and a vertex-only enumeration would be smaller. The test
oracle nevertheless
enumerates *all* feasible integer matrices, by row-by-row distribution: fix row i, choose
`x_i1 ∈ [0, min(mᵢ, residual n₁)]`, recurse across the columns (the last column takes the
remainder), then recurse on the next row. This is complete by construction. The reason
for not restricting to vertices is a pitfall worth recording: combining an
all-or-nothing allocation rule with a monotonically increasing row-major cell index
does NOT enumerate all vertices. The vertex
`[[1,1],[1,0]]` above has cell (0,0) holding 1 while both residuals start at 2; a
monotone row-major traversal visits (0,0) first and allocates min(2,2) = 2, making
`[[1,1],[1,0]]` unreachable. A leaf-first activation order such as (0,1), (0,0), (1,0)
does produce it, but implementing a correct leaf-first enumerator is nontrivial. The
min-cost transportation solver sidesteps the problem entirely: it computes the optimal
matrix in polynomial time without enumerating any vertices. Both production paths use
transport: the exact solver runs one flow solve per representation pair, and MCGS
attaches one transport-AND-node per feasible pair (its legal cells are bandit arms;
the flow is recomputed from the cell Q estimates at every backpropagation, so the
matrix is a derived attribute, not a search choice). Complete row-by-row enumeration
survives only as a test oracle for differential checks against the flow solver.

**Why cells can be solved independently of the matrix (the decomposition argument).**
Three facts chain to justify solving each cell (i,j) once and selecting the weights
afterward:

1. A cell's state is matrix-independent. The child state for cell (i,j) is
   `(a_i, b_j, ctxL', ctxR')`, with contexts derived from the parent state and the
   cell classes alone (§2.3); nothing in the derivation mentions the matrix, the other
   cells, or the weight x_ij. Cycle-blocking is likewise cell-local.
2. Child slots do not constrain each other. For a fixed matrix X, the parent term is
   `op` applied to x_ij copies of cell (i,j)'s result term; there is no cross-cell
   coupling. Replacing any single child term by a smaller one strictly improves the
   total, so the best achievable cost under factoring X is `1 + Σ x_ij · s_ij` with
   each s_ij the per-cell optimum (ditto for vmass).
3. The weight optimization is a linear problem over fixed coefficients. Given (1) and
   (2), minimizing over matrices is minimizing a linear function of the x_ij subject
   to margin constraints; the coefficients (the per-cell qualities) are already fully
   determined. This is the transportation problem.

The decomposition: stage (a) computes all per-cell optima (memoized, shared across the
entire search); stage (b) solves one transportation instance over those optima. Stage (b)
never reopens stage (a). The same architecture extends to MCGS: replace exact cell
qualities with evolving estimates, rerun the transport combiner as they improve.

A representation pair with legal cells can still be **Hall-infeasible** (a blocked row
with positive supply that no legal cell can absorb). Feasibility is verified by a flow
solve before a transport action is created, so infeasible pairs never consume an action
slot; in the exact solver an infeasible pair simply contributes no candidate.

One consequence: two feasible matrices with the same support but different weights have
cost difference `δ · (alternating sum of q_ij around a cycle)`. When the alternating sum
is zero the weightings tie on cost; they are co-optimal but produce different terms (the
projections differ). Equal quality, distinct anti-unifiers; the replacement rule keeps
the first found. This degenerate-tie set is what "produce all co-optimal anti-unifiers"
would enumerate if that feature were ever built.

**Enumeration order (test oracle only).** Rows are distributed greedy-first: when the
row and column classes coincide (a diagonal cell), the maximal allocation is tried
first; allocations then descend. This ordering matters only inside the differential
test oracle; production paths use transport and never enumerate.

**Greedy is ordering, not pruning: intersection subtraction is suboptimal.** A tempting
shortcut on canonical multisets is to subtract the intersection first: compute
`I = M ∩ N`, pair every shared element with itself (each self-pair `AU(x,x)` costs
`best_size(x)`, locally unbeatable), and solve only the residuals `(M − I)` vs `(N − I)`.
The intersection of two sorted multisets is cheap, and no single pair can beat a
self-pair, so the shortcut looks safe. It is not, because the objective is the SUM over
all pairs, and banking the locally cheapest pair can strand the residuals: the shared
element may be worth more used crosswise.

The mechanism requires an **operator-polymorphic** class, one holding members under two
different head operators (produced by a merge or by saturation). Let class X contain
both `f(v,v)` and `g(v,v)`, Y contain only `f(v,u)`, Z contain only `g(v,u)`, and take
`AU(op{X,Y}, op{X,Z})`. Intersection-first pairs X with X (cost 3) and strands
`AU(Y,Z)`, which have no common operator: `Variants(f(v,u), g(v,u))`, cost 6; total
1 + 3 + 6 = 10. The crossed matching gives up the free self-pair and spends X's
polymorphism instead: `AU(X,Z)` factors through X's g-member for
`g(v, Variants(v,u))` = 4, and `AU(Y,X)` factors through X's f-member for
`f(v, Variants(u,v))` = 4; total 1 + 4 + 4 = 9. The self-pair was individually optimal
and globally wrong.

The gap is unbounded, not off-by-one. Amplify the leaf arity: `X_k = {f(v^k), g(v^k)}`
(merged), `Y_k = {f(v^{k−1}, u)}`, `Z_k = {g(v^{k−1}, u)}`. The stranded residual is a
bare Variants of two size-(k+1) terms, cost 2(k+1), so intersection-first totals
1 + (k+1) + 2(k+1) = 3k + 4; each crossed child factors its operator, pairing (v,v)
k−1 times plus one `Variants(v,u)`, cost k + 2, so crossed totals 1 + 2(k+2) = 2k + 5.
Intersection-first loses by exactly k − 1, growing linearly in the arity. Conversely,
when the shared element is NOT polymorphic (X has only an f-member), the crossed
`AU(X,Z)` also degenerates to a Variants and intersection-first is optimal; the
polymorphism is precisely the boundary of the phenomenon. All three claims (minimal
instance, linear family, non-polymorphic boundary) are pinned in
`egraph/tests/au_intersection_counterexample.rs`, and this is why every matrix must
remain reachable: the diagonal is a good first try (enumeration order), never a
substitute for the search (pruning).

#### 3.4.5 ACI operators (sets)

Canonical members are sorted duplicate-free sets: the multiset machinery with all
multiplicities 1, so the matchings are the permutation matrices (bijections) between
equal-cardinality sets. Unequal cardinalities use the same identity padding as §3.4.4
when the operator declares an identity (the shorter set is padded with identity
elements; a deficit larger than one adds several identity columns). Idempotence would
additionally justify non-injective matchings; that extension is future work
([`doc/future/au-associative-operators.md`](../future/au-associative-operators.md)).

#### 3.4.6 Literals

A literal member pairs only with a literal member holding the same interned value,
producing a terminal action; different values contribute nothing.

---

### 3.5 Algorithm portfolio and configuration axes

The implementation exposes two algorithms under the `:algorithm` keyword
(`exact`, `uct`); unknown names are rejected:

- `exact` (`eager_with_memo` in §3.2): complete and optimal for the action language
  and `CycleMode`; the correctness oracle for everything else.
- `uct`: MCGS with UCT selection (§3.3.4), a configurable AND-node effort selector
  (§3.3.5), and the structural completion certificate (§3.3.7).

The initialization rollout (§A.4) is not a third algorithm but the shared leaf
estimator. It first scores the eager terminal generalize action and every surviving
structural or transport action with deterministic concrete upper bounds derived from
best representatives. It then recursively follows only the selected action (and only
the selected static transport flow), so initialization is operator-complete without
becoming exhaustive exact search.

The remaining configuration axes are numeric or enumerated knobs on the MCGS
configuration: the playout budget, the `CycleMode`, the exploration constant C, the
normalization target `x_target`, and the AND-node effort selector `and_selector`
(`round_robin`, `uct_and`, or `lct_and`; default `lct_and`, §3.3.5). OR selection is
always UCT. Alternative OR selectors (PUCT with prior processors) and a direct
model-generation baseline are future work; see
[`doc/future/au-associative-operators.md`](../future/au-associative-operators.md).

## 4. Data structures

We implement the layers of the search graph as **arenas**: `Vec`s of structs,
with integer indexes used as pointers. Arenas are required because these structures have
internal aliasing (many edges reference the same shared node), which Rust references
cannot express, and they grow from the leaves, like appending to linked lists. The
structural layers and MCGS statistics use semi-persistent containers from the
`containers` crate. `SearchSession::mark()` / `restore(token)` apply all layers as one
operation (§4.7). **Semi-persistent** means the version history is a backtracking stack:
any marked ancestor version can be restored, and doing so abandons the versions created
after that mark; their tokens are rejected from then on. Cost is the sum of the component
containers: a tracked `VecP` restores in O(captured writes), an `AppendOnlyVec` truncates,
and `Map` additionally rebuilds its transient hash index from surviving entries. Each
index type is a distinct DenseId newtype selected by `EGraphConfig::Au` (31-bit under
DefaultConfig, 63-bit under Config64, §5.3), so using a node id where an edge id belongs
is a compile error and a wide e-graph gets wide AU arenas.

### 4.1 Read-only e-graph interface needed by the search algorithm

The search never mutates the e-graph. `AuSnapshot` is built once per frozen e-graph
state from the public read API (`find_const`, `node_op`, `node_flags`,
`for_each_child`, `mset_children`, `get_lit_val_id`, `len`, the operator registry, and
`unit_node` for identity elements). It borrows the e-graph immutably for its whole
lifetime (node-level reads go through the borrow) and owns the derived tables the
e-graph does not index:

- a dense numbering of live classes and, per class, its member nodes grouped by operator
  (built by one scan of all node ids, grouping on the canonical representative); nodes
  carrying `FLAG_SUBSUMED` are excluded, matching the e-graph's pattern-matching
  boundary; `FLAG_AC_COLLAPSED` nodes remain included because that flag retires them
  only from AC completion and they remain matchable;
- per class: the smallest concrete member and its size (§A.2); a class whose every
  admissible member references the class itself has no finite member and is marked
  infinite;
- the reachability table of §2.4.

Each solver run first validates its roots: it returns
`AuError::NoFiniteRepresentative(class)` if either root, or any class reachable from
one, has no admissible finite member after this filtering.

The shared borrow makes the e-graph immutable while the snapshot is alive, so a search
is a computation over one captured state. Results and `SearchToken`s belong to that one
`SearchSession` and cannot be used with another snapshot, which is enforced by the
component containers' ids.

### 4.2 The search-space layer

One arena family holds the AND/OR graph, shared by every algorithm:

- **OR nodes**: the state `(l, r, ctxL, ctxR)` (contexts interned as sorted class-id
  vectors), a terminal flag (l = r), and the two classes' best sizes for
  normalization. The **node cache** maps states to node ids (§2.3).
- **Actions**: immutable payloads per class pair, cached by `(l, r)` in the action
  cache: operator plus the paired children (positional list or pair list, with
  multiplicities). The production caches materialize only non-AC action kinds; AC/ACI
  pairs become transport actions (§3.4.4), described per OR node by transport
  descriptors in the MCGS overlay and solved directly by flow in the exact solver.
  Cycle filtering is applied per OR node when the cached list is consumed.
- **AND records**: one per realized `(OR node, action index)`, living in the MCGS
  statistics overlay (§4.3) rather than a separate structural arena; each stores the
  child OR-stats ids with their pair multiplicities (fixed actions) or the transport
  data (rows, columns, cell map) from which multiplicities are derived (AC/ACI
  transport actions, §3.4.4). There are no lazy-AC matching states.

All structural structs are immutable once pushed; the layer only ever grows
(hash-cons semantics), and restore truncates it back.

### 4.3 The statistics layers

Each search heuristic owns one statistics overlay: arenas of per-node and per-edge structs
whose fields reference search-space ids. Nothing in the bottom layer points upward, so
any number of overlays can coexist.

The MCGS overlay is a DAG mirroring the reachable search space (§2.6). `OrStatsArena`
stores immutable OR identity, normalization sizes, terminal state, typed edge spans, and
transport descriptors in `AppendOnlyVec`; initial/current Q values and flattened edge
visit/realization pools use `VecP`. Each `Span<OrEdgeStatId>` addresses one OR node's
aligned edge entries. `AndStatsArena` stores immutable parent/operator/commutativity,
typed child spans, child OR ids, and transport payloads in `AppendOnlyVec`; Q values,
child multiplicities, child visits, and round-robin cursors use `VecP`. Each
`Span<AndChildStatId>` addresses aligned child entries, and transport cell maps hold
absolute `AndChildStatId` values rather than untyped offsets. Visit counters and
round-robin cursors are `u64`, matching the `u64` playout budget.

The OR-to-statistics index is `Map<OrId, OrStatsId>`, and transport descriptor vectors
are immutable payloads in an `AppendOnlyVec`. Arena tokens contain only the underlying
`VecToken` values; `McgsToken` combines the two arena tokens with the map token.
Validation checks every component before restore mutates any arena, then restore
delegates to the owning containers in reverse dependency order. The exact solver's
overlay is a local memo vector with states `Empty`, `Visiting`, and `Solved(term)`;
solved terms are also published to the invocation's best-result table with the exact
flag set.

### 4.4 The result-term pool

The search maintains its current anti-unifier results as terms allocated in a pool: a
hash-consed arena of `(operator, children)` structs, where the operator is an enum over
the e-graph operators, literals, and `Variants`, and children are spans into a shared
child pool. Sizes and variant masses are cached per term. Structurally equal terms get
the same id, so results share subterms and comparing candidates is an id/quality
comparison. For commutative operators (SPair, MSet, Set), children are kept in a
canonical structural order, so the same semantic result always interns to the same id
regardless of which algorithm or action order produced it; ordered operators preserve
positional order verbatim. Variant projection (§1) is an iterative (explicit-stack)
walk over the pool.

### 4.5 The best-result table

A best-result table maps each OR node to the best anti-unifier found for it so far
(a term id with its `(size, variant_mass)` quality), and, when the exact solver has
finished that node, a write-once "exact" flag. Updates are strict improvements only, so
any interleaving of writers preserves validity. Each solver invocation owns its table:
`anti_unify` allocates per call, and `SearchSession::run_uct` reuses the session's
table across UCT runs, so within a session MCGS treats an entry marked exact as
terminal when it first creates the node's statistics (§3.3.1). The exact solver never
writes into a live MCGS overlay; MCGS certifies its own optimality through the
structural completion certificate of §3.3.7.

### 4.6 Well-formedness, specified with ghost models and frames

Arena ids deliberately bypass the borrow checker, so nothing in the type system rules
out a dangling child id or one edge claimed by two nodes. The `containers-verus` crate
has a worked discipline that buys the guarantee back, dynamic frames over a ghost
model: alongside the executable arenas, the specification carries a ghost description
of the structure as sequences and sets of unique ids, and a well-formedness predicate
`wf` ties the executable fields to that description with four clauses (in-range,
disjoint, coverage, shape). Each graph layer here gets one ghost model, one `wf`, and
per-operation contracts in that style. Today the ghost models exist as the shadow
models of property tests (§8); the Verus formalization is the upgrade path.

**Search-space layer.** Ghost model: a finite map from canonical keys (states,
`(l, r)` action lists, `(OR, action)` edges, interned contexts) to immutable
descriptions whose children are canonical keys.

1. in-range: all field vectors of one arena have the same length; every id stored in any
   field is below the length of its target arena; every span is within its payload pool;
2. disjoint: the keys are pairwise distinct, so each cache (node, edge, action,
   context) is injective into ids;
3. coverage: every canonical-key arena element is the image of exactly one key; every
   payload-pool element belongs to exactly one live span; caches are bijections onto their
   keyed live ids, with no dead elements;
4. shape: each struct's fields realize its key's description: an AND node's children
   match its action's pairs (fixed actions) or its transport cells (AC/ACI actions)
   in order, with contexts derived by §2.3 from its parent's state, and the
   acyclicity of §2.2–2.3 holds (a class occurs on one side of a path at most as
   §2.3 permits).

**Statistics overlay.** Ghost model: a DAG over the reachable search-space ids with a
visit count per edge and a value per node.

5. in-range: all field vectors of one statistics arena have equal length, and every
   structural, child, action, span, and parent id names a live target;
6. disjoint: at most one statistics struct per search-space id per overlay, and each
   realized edge appears once in its node's edge list;
7. coverage and shape: every OR statistics struct has exactly one edge-statistics element
   per surviving action; every realized edge points to the matching structural AND node;
   each AND child edge matches the structural child (fixed multiplicities for fixed
   actions, flow-derived multiplicities for transport actions); edge visit counts
   are defined only by their own selector; and values are finite or the awaiting-rollout
   infinity. The overlay stores one parent id per AND statistics struct (no reverse
   parent lists); completion is certified by the traversal of §3.3.7.

The current Q equation is deliberately not a global `wf` clause. Under path-only
backpropagation, a parent not on the path may hold a value computed before a shared child
improved. Instead, `recompute(n)` has the postcondition that Q(n) equals the §2.6 equation
using the children's values at that call. The implementation restores global consistency
with a deterministic children-first closure pass over the completed DAG before certifying
`Completion::Exact` (§3.3.3, §3.3.7).

**Best-result table.** Ghost model: a map from search-space ids to terms, with a
monotonicity contract instead of a shape clause: entries only improve (strict
`(size, variant_mass)` decrease), the exact flag is write-once within a branch, and
every entry is a valid anti-unifier of its state's class pair. Any interleaving of
writers preserves this.

Operation contracts take the frame and anti-frame shape of the verified containers.
Every mutation names its **footprint**, the few ids it touches; disjointness makes the
`wf` facts of every untouched id carry across unchanged (the frame), and the remaining
precondition is the operation's genuine correctness condition (the anti-frame):
expansion requires "this action index is unrealized on this node", and an exact-flag
write requires "the solver finished this state". Expansion allocates or finds the AND
statistics struct and its children and writes one previously empty OR edge slot. Its
existing-node footprint is O(action arity), not O(1), but remains local and never
restructures an existing edge. Selection and backpropagation have statistics-only
footprints, so the entire structural `wf` is frame for them.

Two lessons from the verified exemplars are binding here. Shape is always stated over
the ghost model, never by pointer-chasing: an invariant that correlates arena order
with graph shape ("children have larger ids than parents") is false under this growth,
because a shared node created deep on one path is later linked as a shallow child of
another. And `wf` is a predicate over the arena contents alone, with tokens carrying
only scalars: restore then re-establishes `wf` for free through the containers'
rollback guarantee, since restoring is exact frontier truncation plus replay of the
single-field diffs.

### 4.7 Whole-search marks, restores, and sessions

`SearchSession::mark()` snapshots the entire search in one operation across its five
layers: the search space (OR arena and context interner), the term pool, the
best-result table, the action cache, and the MCGS statistics overlay (including its
per-OR transport-descriptor lists). It returns one opaque `SearchToken`, which is
neither `Copy` nor `Clone` (restore consumes it). Layer-specific marks are private
implementation details and are not exposed, so callers cannot restore one layer while
leaving another in a later version. The exact solver allocates its memo locally per
invocation, and there is one MCGS overlay per session.

`SearchSession::restore(token)` first validates every component token against its
container identity and branch genealogy (no mutation), then restores in reverse
dependency order: statistics, action cache, best results, term pool, then the search
space. Validation happens before any mutation, so a foreign or abandoned-branch token
panics with all layers intact rather than causing a partial restore. At every public
method boundary all layers name the same logical version and §4.6 holds. E-graph and
search marks are separate: `SearchSession::restore` restores every search layer to one
earlier search version while its borrowed e-graph snapshot remains immutable.

`SearchSession::run_uct` additionally rejects a config whose `CycleMode` differs from
the mode the session's search space was created with
(`AuError::CycleModeMismatch`): contexts already interned under one mode cannot be
reused under the other.

---

## 5. Rust implementation

### 5.1 Module layout

The feature lives in this crate as `egraph/src/au/`, compiled behind no feature flag:

```text
au/
  mod.rs          AU id families (AuIds31/AuIds64, §5.3), typed Span, AuError
  egraph_api.rs   read-only snapshot of the e-graph (§4.1): dense class table,
                  members grouped by operator, best terms, reachability
  space.rs        OR arena, context interner, cycle filtering (§4.2)
  actions.rs      non-AC action generation per node kind (§3.4); the bounded
                  matrix enumeration survives only as a test oracle
  ac_repr.rs      canonical AC/ACI monomial representations (§3.4.4)
  transport.rs    min-cost transportation solvers (integer lexicographic and
                  native f64) shared by exact and MCGS (§3.4.4)
  terms.rs        result-term pool (§4.4) and variant projection
  results.rs      best-result table (§4.5)
  reward.rs       NCR reward normalization (§2.5)
  exact.rs        memoized exact solver (§3.2)
  mcgs.rs         playout loop, selection, expansion, backpropagation, the
                  MCGS statistics overlay (§3.3, §4.3), transport-AND-nodes,
                  and the completion certificate
  pretty.rs       s-expression pretty-printer with column limits
  session.rs      SearchSession, whole-search SearchToken (§4.7), anti_unify
```

MCGS statistics live in `mcgs.rs`; there is no separate statistics or policy module.
The interpreter exposes the two `Command` variants of §6.

**No call-stack recursion on deep paths.** Every production code path whose depth
follows the term or search-graph depth is implemented iteratively with an explicit
heap-allocated frame stack: the exact solver (`exact.rs`), the initialization
rollout and the structural-completion certificate (`mcgs.rs`), best-member term
construction, variant projection, `has_variants`, and the structural order used for
canonical child sorting (`terms.rs`), and both pretty-printing passes (`pretty.rs`).
The recursive definitions of §3.2 and Appendix A remain the mathematical
specification; the implementations preserve their evaluation order and side-effect
timing exactly. Depth is therefore runtime/heap-bounded, never call-stack-bounded.
The one remaining recursive routine under `au/` is the bounded AC matrix
enumeration in `actions.rs`, which survives only as a test oracle (both production
solvers construct their caches with `without_ac_actions`); its depth is bounded by
the rows × columns of a single node's canonical representation (node width), not by
term depth.

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
  future fails validation instead of corrupting state. MCGS uses `VecP` for every
  mutable value, visit count, realization option, multiplicity, and cursor.
- `AppendOnlyVec<T>`: used push-only for structural elements; restore truncates to the
  saved length. The implementation exposes `get_mut`, but this design never mutates a
  structural element after pushing it.
- `Map`: an `AppendOnlyVec<(K,V)>` source of truth plus a transient
  `hashbrown::HashMap`; restore truncates the log and always rebuilds the hash map from
  the surviving entries. Used for modest caches in §5.4.

### 5.3 Id types

Every AU arena index is a distinct DenseId newtype, so ids from different arenas
cannot be confused and `Option<Id>` is pointer-sized. The id family is selected by
`EGraphConfig::Au` (an `AuIds` bundle): `DefaultConfig` selects the 31-bit family
(`AuClassId`, `OrId`, `ActionId`, `CtxId`, `TermId`, `SccId`, `OrStatsId`,
`AndStatsId`, plus typed pool positions `SnapshotMemberId`, `ContextElemId`,
`TermChildId`, `ReachBlockId`, `OrEdgeStatId`, and `AndChildStatId`), and `Config64`
selects `define_id63!` counterparts, so a wide e-graph gets wide AU arenas end to end.
Every id type in the bundle is backed by a real pool. The
generic e-graph API uses `Cfg::G` for e-node ids and class representatives, `Cfg::O`
for operators, `Cfg::V` for literal values, and `Cfg::M` for multiplicities; it does
not expose separate `ClassId` and `NodeId` types. The snapshot maps representative
`Cfg::G` values to the config-selected dense class id used by contexts and
reachability bitsets. Multiplicity is checked-converted from `Cfg::M` to `u32` while
building the snapshot; a value that does not fit returns
`AuError::MultiplicityOverflow`.

### 5.4 Arena schemas

The MCGS storage has two explicit aligned arenas and one persistent index:

```rust
struct OrStatsArena<A: AuIds, O: DenseId> {
    or_ids: AppendOnlyVec<A::Or>,
    min_size: AppendOnlyVec<f64>,
    max_size: AppendOnlyVec<f64>,
    terminal: AppendOnlyVec<bool>,
    edge_spans: AppendOnlyVec<Span<A::OrEdgeStat>>,
    initial_value: VecP<f64, A::Index>,
    value: VecP<f64, A::Index>,
    edge_visits: VecP<u64, A::Index>,
    edge_and: VecP<Option<A::AndStats>, A::Index>,
    transport_descs: AppendOnlyVec<Vec<TransportActionDesc<O, A::Class>>>,
}

struct AndStatsArena<A: AuIds, O: DenseId> {
    parent: AppendOnlyVec<A::OrStats>,
    op: AppendOnlyVec<O>,
    commutative: AppendOnlyVec<bool>,
    child_spans: AppendOnlyVec<Span<A::AndChildStat>>,
    child_or_stats: AppendOnlyVec<A::OrStats>,
    value: VecP<f64, A::Index>,
    child_counts: VecP<u32, A::Index>,
    child_visits: VecP<u64, A::Index>,
    round_robin: VecP<u64, A::Index>,
    transport_rows: AppendOnlyVec<Vec<u32>>,
    transport_cols: AppendOnlyVec<Vec<u32>>,
    transport_cell_map: AppendOnlyVec<Vec<Option<A::AndChildStat>>>,
}

struct McgsState<A: AuIds, O: DenseId> {
    or_stats: OrStatsArena<A, O>,
    and_stats: AndStatsArena<A, O>,
    or_stats_map: Map<A::Or, A::OrStats>,
}
```

OR edges and AND children are flattened into aligned pools. An OR node owns a
`Span<A::OrEdgeStat>` over visit and realized-AND pools; an AND node owns a
`Span<A::AndChildStat>` over child ids, multiplicities, and visit pools. Transport cell
maps point directly into the AND child pool with `A::AndChildStat`. The 31-bit and
63-bit AU families define real IDs for both pools; no ID exists without storage
behind it.

Structural fields and immutable transport payloads are appended once. Mutable fields
use the standard tracked vector, which captures the first pre-mark write and restores
surviving entries exactly. The persistent `Map` owns OR lookup rollback and rebuilds its
transient hash index from surviving log entries.

`OrStatsToken` and `AndStatsToken` contain only `VecToken` values from their fields.
`McgsToken` contains those arena tokens plus `MapToken`. `is_valid_token` checks every
component. `restore` performs no local replay, truncation, or index reconstruction; it
only delegates to the underlying containers after validation.

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

`SearchToken` contains private component-token bundles for every semi-persistent layer.
The MCGS component contains only `VecToken`/`MapToken` values; there are no independent
owner ids, length watermarks, counters, or genealogy fields. `SearchSession::mark()`
creates all component marks together and returns only `SearchToken`; component tokens
and restore methods remain private. `SearchSession::restore()` validates every component
first and then restores them in the reverse dependency order of §4.7. This makes a mark
one coherent version of the complete search and prevents mixed-version states by API
construction.

### 5.7 Determinism

Runs are deterministic. All iteration uses dense ids or explicit sorted orders; hash
maps never drive a decision directly; floating-point accumulation follows ascending
action index. Action lists preserve the e-graph's member order because action indices
and first-maximum tie-breaking depend on it. The transport solver relaxes nodes and
edges in fixed index order with strict-less updates, so equal-cost ties resolve to the
first candidate and the returned matrix is a deterministic function of the input. The
pinned regression expectations in the test suite rely on this determinism. No
stochastic selector exists; a future one must define its RNG and include its state in
`SearchToken`.

---

## 6. Script commands

Two commands make the whole workflow (build terms, saturate, extract anti-unifiers)
expressible in one `.egg` file, implemented as ordinary interpreter commands next to
`extract` (identifiers cannot contain hyphens, hence the compact names):

```lisp
(antiunify t1 t2 :algorithm uct :playouts 2000)
(checkau   t1 t2 :algorithm exact :max_size 9 :playouts 500)  ; asserts like check
```

Each command builds its two terms (rebuilding the e-graph if that added nodes), builds
a snapshot of the frozen e-graph, runs, and — for `antiunify` — prints the result
(term, size, compression ratio, completion flag); `checkau` instead fails when the
result's size exceeds `:max_size`. `push`/`pop` around the commands behave as
expected. `:algorithm` selects `exact` or `uct`; unknown names are rejected.
`:playouts` sets the UCT budget; `:max_size` (checkau only) is the asserted
bound and must fit in u32 (overflow is a parse error). No other options are accepted.

## 7. Configuration

Defaults: 1000 playouts, C = √2, x_target = 0.8, `CycleMode::AncestorOnly`, UCT OR
selection, `lct_and` AND selection with the terminal-skip gate (`round_robin` and
`uct_and` remain selectable, §3.3.5), shared edge-visit statistics, and path-only
online updates followed by a children-first DAG closure before certifying
`Completion::Exact`. Production has no action-count truncation: the AC test oracle's
enumeration bound exists only in test configurations.

All constants, orderings, and formulas here are the specification; changing any of them
changes the pinned regression expectations.

## 8. Testing

1. **Oracle equality**: on small instances, MCGS run to completion equals the exact
   algorithm's quality when both use the same action model and `CycleMode`; every
   intermediate result is valid (both projections land in the root classes) and never
   smaller than the oracle's optimum. Pinned in `egraph/src/au/mcgs.rs`,
   `egraph/src/au/session.rs`, and the proptest gates of §2.5.2
   (`egraph/tests/au_convergence_props.rs`).
2. **Invariants**: property and adversarial tests drive random playouts and
   whole-session `SearchSession::mark`/`restore` operations, then check §4.6 and
   complete observable state equality; no test or API restores an individual layer
   (`egraph/tests/au_semi_persistence.rs`, `egraph/tests/au_adversarial_props.rs`,
   `egraph/tests/au_transport_props.rs`). The AC counting table, multiplicity
   subtraction, and the greedy counterexample of §3.4.4 are pinned as unit tests
   (`egraph/src/au/actions.rs`, `egraph/tests/au_intersection_counterexample.rs`).
3. **Conformance corpus**: the anonymized case files
   (`egraph/tests/au_reference_fixtures.rs`, twenty semantic pairs plus policy,
   projection, conversion, and preprocessing cases) drive both algorithms end to end;
   the anonymizer script (`egraph/tests/au/anonymize_cases.py`) regenerates cases with
   per-case stable `v1, v2, …` naming. Config64 coverage lives in
   `egraph/tests/au_config64.rs` and `egraph/tests/au_id_width.rs`, including
   cross-width result-quality identity.

---

## Appendix A. Reference algorithms

Deterministic pseudocode; the implementation follows these definitions. The
recursive formulations below are the mathematical specification: the shipped code
implements each one iteratively with an explicit frame stack (§5.1), preserving the
specified evaluation order, so depth is runtime-bounded rather than
call-stack-bounded.

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

### A.3 Terminal generalize action

```text
generalize(l, r) = best_term(l)                              if l == r
                 = Variants(best_term(l), best_term(r))      otherwise
```

This base action is part of the action space shared by Exact and UCT. It does not
positionally inspect or factor the selected representatives.

### A.4 Action-aware initialization rollout

The rollout uses the same state, `CycleMode`, action generator, and child-context
transition as the main search. For each state it computes the concrete quality of the
terminal generalize action and static concrete estimates for every surviving structural
and transport action. Structural estimates generalize each child pair; transport
estimates solve one flow over those child estimates. The lowest estimate wins, with the
eager generalize action winning ties. Recursion then follows only that selected action
and, for transport, only cells carrying its selected static flow:

```text
initial_rollout(state):
    if state.l == state.r:
        return best_term(state.l)
    choice = argmin(generalize_estimate(state),
                    structural_estimates(state),
                    transport_estimates(state))
    if choice is generalize:
        return Variants(best_term(state.l), best_term(state.r))
    if choice is structural action:
        return apply(choice.op,
                     [initial_rollout(child(state, l_i, r_i))
                      for each pair occurrence (l_i, r_i) in choice])
    return apply(choice.op,
                 [initial_rollout(cell(state, i, j))
                  for each positive-flow cell (i, j) in choice.static_flow])
```

This policy completely considers the shared operator/action space during mandatory
initialization, remains deterministic, and cannot be worse than eager generalization.
It is bounded rather than exact: unselected action subtrees and unselected transport
cells are not recursively explored.

### A.5 Exact solver

§3.2 is normative, with the min-cost transportation solve of §3.4.4 for AC/ACI
operator pairs (one flow per representation pair; no matrix space is ever
materialized, so no oversized-space handling is needed).

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

**Size arithmetic.** The terminal generalize action wraps both whole size-4 terms,
so its size is 8. The greedy diagonal (action 1) produces
`and(b, c, Variants(a,d))`, size 1+1+1+0+1+1 = 5. Because 5 < 8, the diagonal
strictly improves over the generalize action. On this instance Exact and UCT both
converge to size 5; the gap is the value of structural AC matching.

## Appendix C. Worked examples: cycle tie-breaking and AC multiplicities

### C.1 Cyclic e-graph tie-break, and the variant-mass secondary objective

Consider `AU(class_x, class_fy)` where `class_x = {x, f(x), f(f(x)), …}` (created by
the rewrite `x → f(x)` and saturation) and `class_fy = {f(y)}`. The best members are
`x` (size 1) and `f(y)` (size 2).

The terminal generalize action is `Variants(x, f(y))`, size 1+2 = 3.

The search also tries pairing the `f(x)` member of `class_x` with `f(y)` from
`class_fy`: same operator `f`, so it factors to `f(AU(class_x, class_y))`. Since
`class_x ≠ class_y` and neither has a common operator, `AU(class_x, class_y) =
Variants(x, y)`, size 2. Thus the candidate is `f(Variants(x, y))`, size 1+0+1+1 = 3.

Both candidates have size 3, so size alone cannot separate them — yet they are not
equally good anti-unifiers: `Variants(x, f(y))` has an empty backbone (everything
diverges), while `f(Variants(x, y))` factors the constructor `f` into shared
structure. The compression ratio (§2.5) is size-derived and identical for both.

**Variant mass.** Define `vmass(t)` as the number of concrete nodes lying under
`Variants` nodes: `vmass(Variants(a,b)) = size(a) + size(b)`, and for an ordinary
node `vmass(op(c₁…cₙ)) = Σ vmass(cᵢ)`. Then `size(t) = backbone(t) + vmass(t)`, so
at equal size, smaller variant mass is exactly larger backbone. Here
`vmass(Variants(x, f(y))) = 3` but `vmass(f(Variants(x,y))) = 2`.

Results are ranked by the lexicographic key `(size, vmass)`; replacement anywhere
requires a strict improvement in that order (§4.5). The primary objective and
reported compression ratio are unchanged; the secondary objective only resolves
equal-size ties, always toward the candidate that factors more constructors into the
backbone. The exact solver remains exact for this order: sizes and vmasses both add
over an AND node's children, so per-child lexicographic minimization composes.
On this example the search therefore returns `f(Variants(x, y))`.

Ties in `(size, vmass)` both — e.g. two different bijections of an AC matching with
symmetric children — remain resolved by first-found (action order), which is
deterministic (§5.7). Enumerating all co-optimal anti-unifiers
is a possible extension: the exact memo would store a set of optimal terms per state
instead of one, with the usual combinatorial caveats.

### C.2 AC multiplicities

`AU(plus{a^2, b^1}, plus{a^1, b^2})`: row margins [2, 1], column margins [1, 2], total 3.
The matching-count matrices are:

```text
Matrix 1 (greedy diagonal):   x[a][a]=1, x[a][b]=1, x[b][b]=1
  → plus(a, AU(a,b), b) = plus(a, Variants(a,b), b)
  → size: 1 + 1 + 0 + 1 + 1 + 1 = 5

Matrix 2 (crossed):           x[a][a]=0, x[a][b]=2, x[b][a]=1
  → plus(AU(a,b), AU(a,b), AU(b,a)) = plus(Variants(a,b), Variants(a,b), Variants(b,a))
  → size: 1 + 0 + 1 + 1 + 0 + 1 + 1 + 0 + 1 + 1 = 7
```

Matrix 1 costs 5, matrix 2 costs 7; the greedy diagonal is optimal. The terminal
generalize action wraps both whole size-4 terms and costs 8. Exact and UCT return 5;
no strictly better factoring exists.

---
[← Ch 18: Semi-Naive Evaluation](18-semi-naive-evaluation.md) · [Table of Contents](00-table-of-contents.md)
