# Graph search, and the hybrid

> Chapter contents: what one playout does, why the search is over a graph rather than
> a tree and what that breaks in ordinary MCTS bookkeeping, how a state key can be
> shared across paths and still be a valid state, the value recomputation that
> replaces accumulation, the pruning that is safe to apply here, and the hybrid that
> hands small subproblems to the exact solver.
>
> Sources: design `19-anti-unification.md` sections 2.6 (adapting MCTS to graphs),
> 2.3 (the sentence on child contexts retaining only independently reachable
> ancestors), 3.3 (Monte-Carlo graph search) and 9.4 to 9.5 (pruning and certificate
> bits). The module header of `egraph/src/au/mcgs.rs` is written for this and is the
> most useful single source.
>
> Examples: `examples/15-uct.egg`. A query under `:algorithm uct` with a stated
> `:playouts` budget, on a problem where the exact answer is known from chapter 14, so
> the reader can see the two agree. State the budget in the file and keep it low
> enough that the test stays fast.
>
> **Level, and this is the instruction that governs the whole chapter.** High level.
> Hand-wavy on purpose. The reader needs to know what the search does, why the graph
> forces three specific departures from textbook MCTS, and roughly why each departure
> is safe. No equations beyond the two value equations, no invariant numbering, no
> reproduction of the certificate argument. Every section ends with a pointer to the
> design section that has the real thing. If a section runs past three paragraphs it
> is too detailed.

## When to use it

> Open with the decision, because most readers need only this section: `exact` is the
> default and is faster on problems the size of a policy, and `uct` exists for inputs
> whose pair graph is too large for exact to finish. It is an anytime algorithm, so it
> returns its best result at whatever `:playouts` allows and reports `:completion`
> accordingly.

## One playout

> The four steps in order, one sentence each: select down from the root (UCT at OR
> nodes, an effort selector at AND nodes), expand a new node, take an initial rollout
> for a first estimate, then back up along the path just traversed, recomputing each
> node's value and composing its children's stored best terms into a candidate that is
> offered to its parent. State that the composition step is what lets the search
> improve past its first rollout.

## The same subproblem, reached many ways

> The reason the search is over a graph: a class pair reached along different paths is
> the same subproblem, and solving it once is the whole point. So a node is keyed by
> the subproblem rather than by the path that reached it.
>
> Then the tension, which is the part the user asked to see explained. If the key
> included the path from the root, no two paths would ever share a node and the search
> would be a tree with no reuse. If the key were the class pair alone, the search
> could not tell that it is already inside a cycle through that pair, and it would
> descend forever. So the key keeps the pair plus a cycle context: the record of which
> classes or pairs are already active on the way in.
>
> The resolution, stated at the level of what it accomplishes: a child's context keeps
> only those active ancestors that the child can still reach, and forgets the rest.
> What is forgotten cannot affect any future decision below that child, because it can
> never be reached again, so dropping it loses nothing. What is kept is exactly what
> could still block an action further down. The state therefore satisfies what the
> search needs of it, that everything relevant to the future is in the state and
> nothing in the past has to be consulted, while still letting two different paths
> that arrive at the same pair with the same live guards land on the same node. Cite
> design 2.3 for the exact rule and 4.2 for how the context is interned.

## Values are recomputed, not accumulated

> The two failures that sharing causes if the ordinary bookkeeping is kept, stated
> plainly: a child accumulates visits from paths its parent never chose, so a parent
> that weights an action by the child's visit count is steered by unrelated traffic and
> explores away from a child other paths already validated; and a parent whose value
> absorbs every update its child receives is dragged toward subproblems it never
> selected.
>
> The fix in two parts. Edge visits are counted per parent per action, so a state's
> policy is its own. A state's value is recomputed from its children's current values
> each time it is visited rather than accumulated, so it is a pure function of the
> present and cannot double count a shared node. Give the two value equations, since
> they are two lines and they make the recomputation concrete.
>
> Say what recomputation costs and what it cannot cost: a stale value can change what
> a finite budget explores and therefore the quality of the answer, and it cannot
> manufacture a term that was never achieved, because candidate terms are assembled
> from real child terms and not from values. Cite design 2.6.

## Pruning and closure

> The rules that discard an arm here, at one line each rather than as a table: an arm
> that cannot come in under the always-available generalize size, an arm whose bound
> exceeds the state's achieved incumbent, and a subtree that is already fully resolved.
> State the shared argument once: each discards an arm and never a term, and each rests
> on comparing against something already achieved.
>
> Then the closed bit, briefly: a node whose subgraph is fully resolved is marked, the
> mark propagates upward through every parent of a shared node rather than only along
> the path just walked, selection skips closed subtrees, and certification reads the
> root's mark instead of walking the graph. Two paragraphs, then point at design 9.5,
> including its point that closure is not the same condition as the bounds meeting.

## The hybrid

> What it is: an OR node small enough by a cheap measure of the class-pair rectangle
> it lives in is handed to the exact solver instead of being explored by playouts, and
> the result comes back marked exact, which makes the node terminal and closed so the
> proof propagates upward with no extra machinery.
>
> What it needs to be sound, in one sentence: the exact call is entered at the same
> class pair, the same context and the same cycle mode, so it solves the identical
> subproblem the node stands for.
>
> Then state the two boundaries the design document is explicit about, because a
> reader should not over-read the mode: the admission tests are workload estimates and
> not complexity bounds, and the soundness argument has finite differential evidence
> rather than a machine-checked proof.
>
> Finally, the practical note the v1 draft had: the hybrid is not reachable from
> `:algorithm` in the surface language, only from the Rust API. Verify that this is
> still true before writing it.

## Configuration

> The options a reader can actually set: `:algorithm uct`, `:playouts`, `:cycles`.
> State that the cycle policy is an input to this algorithm exactly as it is to exact,
> that a hybrid call inherits the node's mode rather than choosing its own, and that
> `:completion` tells the reader which of the two answers they got. Point at design 3.5
> for the configuration axes that are Rust-API only, and do not enumerate them.
