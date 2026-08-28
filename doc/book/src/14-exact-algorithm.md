# The exact algorithm

The exact solver searches the finite action graph induced by two e-classes. Its
answer is exact for a selected cycle policy, the objective from Chapter 12, and
the e-graph snapshot supplied to it.

## The search space

A search state asks how to anti-unify two e-classes. It is an **OR node**
because the solver may choose among several compatible representations of
those classes. Each choice is an **AND node** because all child-class pairs
induced by that representation must be solved.

The same ordered class pair can be reached from several parents, so the search
space is a graph rather than a tree. The graph has finitely many ordered pairs
even when cyclic e-classes represent infinitely many finite terms.

## The actions at a state

Every unequal state has a generalize action:
`Variants(best(left), best(right))`. It provides an achieved result before any
structural action is examined. Compatible e-nodes provide the other actions:

| node kind | structural action |
| --- | --- |
| equal classes | Return the class's smallest admissible term. |
| ordinary ordered operator | Pair children positionally when operator and arity agree. |
| commutative binary operator | Consider the positional and crossed pairings. |
| associative sequence | Pair positions when the two sequences have equal length. |
| AC multiset | Solve a minimum-cost transport problem between child multiplicities; a declared identity may pad unequal totals. |
| ACI set | Solve the corresponding all-one transport problem; a declared identity may pad unequal cardinalities. |
| literal | Pair only equal values; the action then has no children. |
| no compatible structure | Use the always-available generalize action. |

The transport formulation materializes child-pair cells rather than all
complete AC pairings. Multiplicity supplies and demands select how many copies
of each child pair the composed result contains.

The complete action-generation rules are in
[`19-anti-unification.md`, section 3.4](https://github.com/yaspar-org/semi-persistent/blob/main/egraph/doc/design/19-anti-unification.md).

## The recursion

Let `G(q)` be the achieved baseline for state `q`: the smallest admissible term
when the classes agree, and the generalize result otherwise. Pair-mode Exact
starts with `G` and repeatedly evaluates every structural action from the
previous round:

```text
V0(q)     = G(q)
Vd+1(q)   = min(Vd(q), compose(a, Vd(children(a))) for each action a)
```

The minimum uses `(size, variant_mass)`. Pair mode interns each reachable
ordered pair once and performs synchronous rounds until the values stop
changing. Side-policy Exact instead memoizes contextual states because its
cycle filter depends on retained left and right ancestors.

## Cycles

Saturation can merge a class with one of its descendants. Recursion must then
exclude infinite descent without excluding every finite derivation that crosses
the cycle.

| option | filtering rule |
| --- | --- |
| `:cycles sides` | Default. Track left and right ancestors separately and filter a candidate against those side contexts. |
| `:cycles sides-current` | Apply the side filter to the current classes as well, producing a stricter contextual graph. |
| `:cycles pair` | Track ordered class pairs and block only a repeated active pair. |

The side policies are provenance choices. They prevent search from using some
rewrite-created cyclic structure, and an exact result under either policy is
optimal only in the graph that policy retains. Pair mode admits a side revisit
when the other side changes; its pair-cycle-erasure argument says that blocking
a repeated ordered pair still retains a minimum finite derivation.

The fixture below creates the recursive class
`cycle = {f(a), h(a, cycle)}` and queries the same operands under all three
policies:

```lisp
{{#include ../examples/14-exact.egg:exact-cycle-program}}
```

It prints:

```text
(anti-unify :size 9 :cr 1.0000 :completion exact
  (h a (Variants (h (f a) (f a)) (f a))))
(anti-unify :size 9 :cr 1.0000 :completion exact
  (Variants (h a (h (f a) (f a))) (f a)))
(anti-unify :size 8 :cr 0.8571 :completion exact
  (h a (h (Variants (f a) a) (f a))))
```

The hidden qualities are `(9,7)` for `sides`, `(9,9)` for `sides-current`,
and `(8,3)` for `pair`. The size-eight derivation revisits one side class while
its partner changes, then reaches a finite terminal pair. Both side policies
filter that route.

## Pruning

The solver can compute a size lower bound for a structural action by summing
child-pair bounds, or by solving a transport problem over those bounds. Two
implemented comparisons use it:

1. If the bound is greater than the achieved generalize size, the action cannot
   improve the state.
2. If the bound is greater than the current achieved incumbent, the action
   cannot improve that incumbent.

Both comparisons are strict and inspect size only. Equality cannot discard an
action because an equal-size result may still have smaller variant mass. A
discarded structural action loses no achieved term and cannot contain the
lexicographic optimum.

The bound and pruning arguments are in
[`19-anti-unification.md`, sections 9.1-9.4](https://github.com/yaspar-org/semi-persistent/blob/main/egraph/doc/design/19-anti-unification.md).

## What `:completion exact` means

For this algorithm, `:completion exact` says that the returned term is optimal:

1. under Chapter 12's `(size, variant_mass)` objective;
2. among derivations admitted by the selected cycle policy; and
3. over the admissible e-nodes and equalities in the current snapshot.

Chapter 16 measures the consequences of these qualifiers. The pair-mode
cycle-erasure and round-bound argument is a prose argument supported by
regressions and a finite oracle, not a machine-checked theorem for the Rust
solver. The current proof boundary is stated in
[`19-anti-unification.md`, section 9.6](https://github.com/yaspar-org/semi-persistent/blob/main/egraph/doc/design/19-anti-unification.md).
