# Extraction under cost models

[Chapter 8](08-equality-saturation.md) defines extraction under an additive cost:
each node has a fixed price, and a term costs the sum of its nodes. This part
defines extraction under a cost model, a cost written by the user that need not
be additive. The commands are part of the default build; the library that
implements them is the module `semi_persistent_egraph::extraction`.

This chapter explains what extraction under a cost model chooses and how, then covers what
every cost model shares: the two commands, the line Semper prints for each extraction, the
ladder of rungs, and the number ranges.
[Chapter 25](25-cost-functions-in-roto.md) teaches cost scripts in Roto,
[Chapter 26](26-criteria-in-asp.md) criteria in answer-set programming, and
[Chapter 27](27-criteria-in-minizinc.md) criteria in MiniZinc.
[Chapter 28](28-solvers-certificates-and-export.md) covers the solvers, the number
range of each, certificates, cost bands, and the files Semper writes.

## Extraction as a choice

An e-graph holds many terms at once. Each class says "any one of my members", and each
node says "my operator applied to one term of each of my child classes". Extracting a term
is choosing: for the root class one member, then for each child class of that member one
member, and so on down to the leaves. In this e-graph

```text
class 0 (root): { And(c1, c2) }
class 1:        { G[0,9](c3),  F[0,9](c3) }
class 2:        { F[2,3](c4) }
class 3:        { Var "a" }
class 4:        { Var "b" }
```

the only decision is which member of class 1 to take, so there are two terms.

[Chapter 8](08-equality-saturation.md) makes that choice for an additive cost, a fixed
price per node summed over the term, without a solver. Every other cost is solved by
stating the choice as a constraint problem. Semper gives every class a Boolean "class is
chosen" and every node a Boolean "node is chosen", and adds the rules that make a set of
chosen nodes a term:

- the root class is chosen;
- a chosen class chooses exactly one of its members;
- a chosen node chooses each of its child classes.

A solution of these rules is a term, and a term is one solution. A cost is then an
objective over the same Booleans: "this node costs 3 when it is chosen" adds 3 times that
node's Boolean to the sum the solver minimizes. Costs that are not sums of such prices, a
maximum over children or a delay along a path, are built from integers whose value follows
the choice; [Chapter 25](25-cost-functions-in-roto.md) shows how a script writes them.

## When the cost depends on a grouping the e-graph does not store

An `:assoc-comm` or `:assoc-comm-idem` operator ([Chapter 4](04-declaring-algebra.md))
stores every grouping and ordering of its operands as one flat node, and an `:assoc`
operator stores every bracketing of its sequence as one node. That keeps saturation from
enumerating them. A cost that depends on the grouping cannot be read off the flat node, so
the extraction has to choose a grouping too, and return the tree it chose.

The example of this part is the memory of an R2U2 runtime monitor. R2U2 checks a
specification in mission-time LTL (MLTL), a temporal logic whose operators carry an
integer interval: `G[l,u] p` says `p` holds at every step from `l` to `u` steps ahead, and
`F[l,u] p` at some step in that range. The monitor evaluates each subformula as a stream of
verdicts. A subformula's verdict for a step arrives between a best-case and a worst-case
delay: an atom has 0 and 0, and `F[l,u] p` adds `l` and `u` to the delays of `p`. A
conjunction needs all its operands' verdicts for the same step, so an operand that is ready
early has to keep its verdicts in a queue until its slowest sibling catches up. Its queue
holds `(worst delay of its slowest sibling) − (its own best delay)` verdicts, plus one.
Johannsen and Rozier shrink these monitors with equality saturation; see their FMCAD 2026
paper, "Shrinking Mission-time LTL Runtime Monitors with Equality Saturation", whose
specifications this book does not reproduce. The terms are MLTL formulas: atoms
`(Var "p")`, the Boolean connectives, with `And` and `Or` declared `:assoc-comm-idem`, and
`Global`, `Future`, `Until`, and `Release` over an `(Interval l u)`. The rules, ported from
their artifact (`egraph/tests/mltl/rules/mltl.egg`), produce equivalent formulas that need
less memory. The one that saves the most factors a common window out of a conjunction:
`G[2,5] p ∧ G[3,9] q` equals `G[2,5] (p ∧ G[1,4] q)`, and its memory falls from 15 to 10,
because the conjunction inside waits for less. The memory to minimize counts one slot per
subformula and per group, one for the specification, and every queue; the
[design chapter](https://github.com/yaspar-org/semi-persistent/blob/main/egraph/doc/design/11-extraction.md#the-terms-the-rules-and-the-cost)
gives the full definition.

Take `p ∧ q ∧ r`, where `p` and `q` are atoms and `r = F[0,10] s`, so `r` may be 10 steps
late and everything else is on time. A group of operands acts as one operand whose worst
delay is its slowest member's and whose best delay is its fastest member's:

| term | who queues | memory |
| --- | --- | --- |
| `And(p, q, r)` | `p` and `q` each wait 10 for `r` | 26 |
| `And(And(p, q), r)` | only the group `{p, q}` waits 10 for `r` | 17 |
| `And(And(p, r), q)` | `p` waits 10 for `r`, and `q` waits 10 for the group | 27 |

The memory counts one slot per subformula and group as well as the queues. All three terms
are the same flat node in the e-graph. The cheapest one groups the fast operands and leaves
the slow one outside, which no price on the flat node can say. With the cost script of
[Chapter 25](25-cost-functions-in-roto.md#bracketed-nodes):

{{#include ../examples/cost-models/24-three.egg:three}}

```text
{{#include ../examples/cost-models/24-three.out}}
```

## How the grouping becomes part of the choice

Listing every grouping of every flat node would bring back the blow-up the flat nodes
avoid: ten operands have 282,137,824 groupings. Semper instead adds a few Booleans per
operand of each flat node, and rules under which each grouping is exactly one solution. In
outline, every operand of a flat node gets a depth ("how many groups deep it sits") and, at
each depth, a label saying which sub-group it continues into. Operands with the same labels
down to some depth are in one group there. The rules number the groups by their smallest
operand, so a grouping cannot be written twice, and they forbid a group of one. For each
group that may exist, the cost sees an inner node: whether it exists, its members, and its
siblings. An operand repeated `k` times in an AC node is one operand at every rung, so the
number of groupings depends only on the distinct operands.

Different costs need different amounts of this structure, and more structure is a bigger
problem. `:rung` chooses how much to add; the next section lists the rungs.

## A first extraction under a cost model

The program below has two equal terms. `(Twice x)` costs 3, and the rewrite gives
the class a second member, `(Add x x)`, whose two children are one shared class:

{{#include ../examples/cost-models/24-first.egg:first}}

The model `dag` is a Roto script. It charges every chosen node once, whatever the
number of its parents:

```rust
{{#include ../examples/cost-models/24-first.roto:cost}}
```

Run from `doc/book/examples/cost-models/`, the program prints:

```text
{{#include ../examples/cost-models/24-first.out}}
```

The first line is Chapter 8's extraction. It counts the shared subterm
`(F (F (V "a")))` once per use, so `Add` costs 7 against 6 for `Twice`. The model
pays each node of the term once. `(Add x x)` then costs 1 plus 3 for the shared
subterm, which is 4, and the extraction proves that no term costs less. The last
extraction scores the additive choice under the model: 3 for `Twice` plus 3, so 6.

## Declaring a cost model

A cost model is named once and used by any number of `extract` commands:

```text
(cost-model NAME :script "f.roto")
(cost-model NAME :asp "f.lp")
(cost-model NAME :minizinc "f.mzn")
(cost-model NAME :rust "id")
```

Each language works on its own view of the e-graph:

| declaration | the cost is | solved by | chapter |
| --- | --- | --- | --- |
| `:script "f.roto"` | a Roto script, compiled against Semper's binding | the library's encoding, on CaDiCaL, RoundingSat, an OPB solver, or clingo | [25](25-cost-functions-in-roto.md) |
| `:asp "f.lp"` | answer-set rules over the e-graph's facts | clingo | [26](26-criteria-in-asp.md) |
| `:minizinc "f.mzn"` | MiniZinc over the e-graph's data and variables | CP-SAT, Chuffed, Gecode, HiGHS, or CBC | [27](27-criteria-in-minizinc.md) |
| `:rust "id"` | a cost registered in Rust | as `:script` | [25](25-cost-functions-in-roto.md#costs-written-in-rust) |

A path is relative to the working directory, not to the program file. The model
is loaded when the program is checked, before any command runs. A script is
compiled then, so a type error in it is a sort error of the program. An ASP or
MiniZinc file is read then, and a missing file is a sort error too.

## The extract command

```text
(extract TERM :cost NAME [:rung R] [:solver S] [:budget N]
              [:file "f.json"] [:proof "dir"] [:band LO HI] [:count K])
```

The keywords after `TERM` may come in any order. `:cost` is required, and the
others have defaults:

| keyword | default | meaning |
| --- | --- | --- |
| `:cost NAME` | none | the cost model |
| `:rung R` | `selection` | how much of a bracketed node's tree the cost decides ([The ladder of rungs](#the-ladder-of-rungs)) |
| `:solver S` | `internal` | the solver ([Chapter 28](28-solvers-certificates-and-export.md#solvers)) |
| `:budget N` | 3,000,000 | the estimated clauses above which the rung steps down |
| `:file "f.json"` | none | write the term as JSON ([Writing the term](28-solvers-certificates-and-export.md#writing-the-term)) |
| `:proof "dir"` | none | keep a VeriPB certificate ([Certificates](28-solvers-certificates-and-export.md#certificates)) |
| `:band LO HI` | none | list the terms whose cost lies in `[LO, HI]` instead of the cheapest one ([Listing terms in a cost band](28-solvers-certificates-and-export.md#listing-terms-in-a-cost-band)) |
| `:count K` | 10 | the largest number of terms `:band` lists; without `:band` it has no effect |

`LO`, `HI`, `K`, and `N` are non-negative integers. A model, a rung, and a solver
must agree, and the checker rejects a disagreement before the program runs:

| combination | rejected because |
| --- | --- |
| `:band` with a `:solver` other than `internal` | a band runs on the internal solver |
| `:proof` with a `:solver` other than `roundingsat` or `(opb ...)` | a certificate needs a proof-logging pseudo-Boolean solver |
| an `:asp` model with a `:solver` other than `(asp ...)` | ASP criteria are solved by clingo |
| a `:minizinc` model with a `:solver` other than `(minizinc ...)` | MiniZinc criteria are solved through MiniZinc |
| a `(minizinc ...)` solver with any other model | a MiniZinc solver reads only MiniZinc criteria |
| an unknown rung | the rungs are `selection`, `levels`, `splits`, `binary`, `orders` |

The five programs `manual/24-check-*.egg` differ only in their last line. Their
messages are:

```text
{{#include ../examples/cost-models/manual/24-checks.txt}}
```

## The reported cost

The first line of each extraction has the form:

```text
; cost C STATUS at rung R (n solves, m cycle exclusions)
```

`C` is the reported cost, `R` the rung the problem was built at, and `STATUS`
`proved` or `bounded`:

| status | meaning |
| --- | --- |
| `proved` | the solver showed that no term of the rung costs less than `C` |
| `bounded` | a limit ran out (solves, time, or the solver's own limit); the term is an upper bound on the optimum |

When no term exists, or a limit runs out before the first term, the extraction
stops with an error instead: `no term: Infeasible` or `no term: Bounded`.

`m` counts the clauses added to exclude a cyclic solution
([Chapter 28](28-solvers-certificates-and-export.md#solvers)). `n` counts the SAT
calls of the internal solver's descent, the last one included. It is 1 for a
script solved by clingo, and 0 where Semper makes no SAT call: an OPB solver, and
an ASP or MiniZinc model.

The reported cost is not the solver's objective. For a script or a Rust cost, the
library evaluates the cost the script stated on the term it returns, recursive
attributes included. A one-directional encoding lets a solution's objective exceed
its term's true cost, and evaluating on the term removes the difference. For ASP
and MiniZinc, Semper solves a second time with the term fixed: every choice atom or
variable takes the value the term gives it. The reported cost is then the file's
definition evaluated on the term. The
[design chapter](https://github.com/yaspar-org/semi-persistent/blob/main/egraph/doc/design/11-extraction.md#soundness-of-the-reported-cost)
gives the argument.

Some lines can follow the first one, before the term:

| line | printed for |
| --- | --- |
| `; solver objective [v1, v2, ...] (most important first)` | an ASP model: clingo's values, one per priority ([Chapter 26](26-criteria-in-asp.md#several-objectives)) |
| `; solver lower bound B` | a MiniZinc model whose solver reports a bound ([Chapter 27](27-criteria-in-minizinc.md#choosing-a-solver)) |
| `; certificate ...: veripb FILE.opb FILE.pbp` | an extraction with `:proof` ([Certificates](28-solvers-certificates-and-export.md#certificates)) |

`:solver greedy` prints `; cost C greedy at rung selection`, whatever `:rung`
says. It solves nothing: it takes the term Chapter 8's additive extraction
chooses and reports its cost under the model.

## The ladder of rungs

`:rung` chooses how much of a bracketed node's structure the cost can see. A
bracketed node is an AC node (`:assoc-comm`, `:assoc-comm-idem`) or an `:assoc`
sequence. A fold (`:assoc-left`, `:assoc-right`) has one bracketing, its prefixes
or its suffixes, at every rung. Each rung represents every candidate tree
exactly once:

| rung | AC node | `:assoc` sequence | the cost can depend on |
| --- | --- | --- | --- |
| `selection` | flat | flat | which nodes are chosen |
| `levels` | chains of nested blocks | chains of nested intervals | the depth of each operand |
| `splits` | every tree over its operands | every tree over contiguous blocks | the grouping |
| `binary` | every binary tree | every full bracketing | the binary grouping |
| `orders` | every ordered tree | as `splits`: the order is fixed | the grouping and the order |

A sequence of k operands has the little Schröder number of trees at `splits` (3,
11, 45 for k = 3, 4, 5) and the Catalan number at `binary` (2, 5, 14). An operand
of multiplicity k in an AC node is one leaf with all its copies at every rung. The
reconstructed term writes it once with its count, `x:k`, the syntax Semper reads
back. A class at two positions of a sequence is two leaves.

What each rung adds:

- `selection` adds nothing: a flat node is costed as written, each operand's siblings being
  all the other operands.
- `levels` gives each operand a depth. Operands at one depth form one group, and each group
  holds the next, so the trees are chains: `And(And(p, q), r)`, but not
  `And(And(a, b), And(c, d))`.
- `splits` adds the labels that let a group split into several sub-groups: every tree.
- `binary` keeps the labels of `splits` and requires exactly two children per group.
- `orders` adds a position for each operand inside its group, for at most 8 operands.

A cost reads the rung through four views, and each is empty where the rung decides nothing.
Every language has them:

| view | Roto ([Chapter 25](25-cost-functions-in-roto.md#bracketed-nodes)) | ASP ([Chapter 26](26-criteria-in-asp.md#trees)) | MiniZinc ([Chapter 27](27-criteria-in-minizinc.md#trees)) |
| --- | --- | --- | --- |
| the siblings of an operand | `u.siblings()`, each with `present()` | `parent/3` and `bmem/3` | `parent_leaf`, `parent_blk`, `bmem` |
| the groups that may exist | `n.inner_nodes()`: `exists()`, `members()`, `siblings()` | `inner/2`, with members `bmem/3` | `inner[b]`, `bmem[b,p]` |
| an operand's depth | `k.depth()` | `depth/3` | `depth[n,p]` |
| an operand's position | `k.position(d)` | `pos/4` | `pos_leaf`, `pos_blk` |

A cost written over siblings and groups, as the monitor memory is, runs unchanged at every
rung; only `:rung` changes. The monitor memory of the introduction, as a script
([Chapter 25](25-cost-functions-in-roto.md#polarity)), at each rung:

{{#include ../examples/cost-models/24-ladder.egg:ladder}}

```text
{{#include ../examples/cost-models/24-ladder.out}}
```

At `selection` the conjunction stays flat and costs 39. At `levels`, `splits`, and
`orders` the two operands over `a1` are grouped, which removes two slots of queue
memory and costs 37. `binary` allows only two operands per group, and its best
tree costs 40. The last line scores the term additive extraction chooses
(`:solver greedy`) under the same model.

### Choosing a rung

Choose the lowest rung that decides what the cost depends on:

- `selection` when the cost depends only on which nodes the term uses. It builds
  no tree variables, so it is the smallest problem.
- `levels` when the cost depends on how deep each operand sits, as a delay through
  a chain of operators does.
- `splits` when the cost depends on which operands are grouped, as the monitor
  memory does.
- `binary` when the target only has two-operand operators, so every group must
  have two members.
- `orders` when the order of the operands within a group also matters.

`levels` and `splits` each offer every term of the rung before them, and more, and so
does `orders` for nodes of at most 8 operands. `binary` offers only binary trees: it excludes the flat node and every
group of three or more operands, which is why it costs 40 above. A higher rung
builds a larger problem. A rung whose estimated encoding exceeds `:budget` clauses (default
3,000,000) steps down the ladder and says so on standard error:

```text
warning: rung splits estimated above the budget; extracting at selection
```

`orders` steps to `splits`, `splits` to `levels`, `levels` to `selection`, and
`binary` straight to `selection`. The rung printed in the first line is the one
used. A bracketed node with fewer than 3 operands has one tree. One with more than
16 operands (more than 8 at `orders` for an AC node) is kept flat at every rung.
Raise `:budget` for an instance that needs a higher rung and fits in memory.

## Number ranges

Semper's own arithmetic on costs is exact: a value past 64 bits is held exactly,
never wrapped. Two ranges decide whether a cost is computed correctly.

- The cost width, `--cost-bits 32`, `64`, or `big` (the default, no cap). Under a
  cap, every integer of a script or Rust cost and the reported cost must lie in
  that signed width, and one outside it is an error naming the operation.
- The solver's range. Semper checks every number it writes for a solver against
  that solver's range and refuses one outside it with an error naming the solver.

ASP and MiniZinc criteria compute inside the solver, and Semper does not check
that arithmetic. **If you write cost functions that can overflow the solver's
internal number representation, you are on your own.**
[Number ranges](28-solvers-certificates-and-export.md#number-ranges) in Chapter 28
lists each solver's range, as measured, and the recommended choices.
