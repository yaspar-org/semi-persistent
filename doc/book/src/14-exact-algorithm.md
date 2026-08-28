# The exact algorithm

> Chapter contents: the search space as an AND/OR graph over class pairs, the actions
> available at a state, the recursion and what memoizes it, why cycles in the e-graph
> need a policy and what the three policies are, the bound that prunes, and what the
> `exact` certificate quantifies over.
>
> Sources: design `19-anti-unification.md`, sections 2.1 (AND/OR graphs), 2.2 (cycles
> as finite derivations), 2.3 (one cycle policy for every algorithm), 3.1 (shared
> building blocks), 3.2 (exact under the selected cycle policy), 3.4 (action
> generation per node kind), 9.1 to 9.4 (feasibility, bound, pruning). Appendix C for
> worked examples.
>
> Examples: `examples/14-exact.egg`, showing a query on a small pair, the same query
> under `:cycles pair`, and the `:completion exact` line in the output. If a
> difference between cycle modes is observable on a small program, show it; the
> adversarial test `cycle_modes_apply_to_exact_uct_and_both_hybrid_paths` in
> `egraph/tests/au_adversarial_correctness.rs` has a case where side filtering returns
> size 9 while the finite derivation has quality `(8, 3)`, which can be reduced to an
> example file.
>
> Level: enough that a reader understands what is being searched and why the answer is
> optimal, not enough to reimplement. No pseudocode longer than the recurrence.

## The search space

> A state is a pair of e-classes: the subproblem "anti-unify these two classes".
> OR nodes are states and choose among actions; AND nodes are actions and require
> every child subproblem to be solved. State the two consequences: the space is a
> graph rather than a tree because the same pair is reached along many paths, and it
> is finite in pairs even when the classes denote infinitely many terms.

## The actions at a state

> The action set, per node kind: generalize, which returns a `Variants` node holding
> the two sides and is always available; and decompose, one action per pair of e-nodes
> with compatible operators, whose children are the paired argument subproblems. For
> AC operators the pairing of children is itself a choice, solved as a transport
> problem, which is where the branching comes from. Cite design 3.4.
>
> State the property that makes bounding work and that chapter 12's cost model rests
> on: generalize is always available at a known size, so no state is ever infeasible.

## The recursion

> The value of a state is the best over its actions, the value of an action is the
> composition of its children's values. Give the recurrence in four lines, no more.
> State that memoization on the state key is what turns the exponential recursion into
> a search over pairs, and that the key is the class pair together with its cycle
> context.

## Cycles

> Why a class can be its own descendant after saturation, and why refusing to revisit
> a class is not the same as refusing to loop. State the case that settles it: one
> side may revisit a class while the ordered pair keeps making progress and later
> reaches a terminal pair, so side-filtering can exclude a valid finite derivation.
>
> The three policies as a table: `:cycles sides` (the default, tracks left and right
> classes independently), `sides-current` (also blocks the current classes), `pair`
> (tracks ordered pairs, blocks only a repeated subproblem). One line each on what it
> admits.
>
> Then the honest part, which the design document states and the book must not soften:
> the side policies are a provenance choice, not an optimality theorem, and they
> certify only the optimum of their filtered graph. Pair mode gives the snapshot's
> grammar its full meaning and is what global optimum evidence is stated in. A
> completion claim has to name its policy.

## Pruning

> Two bounds and what each discards, at one paragraph each: an arm whose lower bound
> exceeds the always-available generalize size can never be optimal, and an arm whose
> bound exceeds the state's current incumbent can be dropped because the incumbent is
> achieved. State that every comparison is strict and on size alone, and why: equality
> cannot prune because variant mass may still improve. Cite design 9.3 and 9.4.
>
> Say once that pruning discards an arm and never a term, which is the invariant that
> keeps the result optimal.

## What `:completion exact` means

> The certificate: the returned term is optimal under the objective of chapter 12,
> within the derivations admitted by the selected cycle policy, over the e-graph as it
> stands. Three qualifiers, each of which matters to a reader who wants to quote the
> result. Point at chapter 16 for the third and at design 9.6 for the current proof
> boundary, and state plainly that the pair-mode optimality argument is a prose
> argument with regression evidence rather than a machine-checked theorem.
