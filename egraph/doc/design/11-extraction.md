# Chapter 11 — Extraction

[← Ch 10: Literal Model](10-literal-model.md) · [Table of Contents](00-table-of-contents.md) · [Ch 12: Anti-Unification →](12-anti-unification.md)

## 11.1 Term Extraction

### Problem

An e-class represents a potentially infinite set of equivalent terms.
Extraction answers the question: "give me the simplest concrete term
from this class." This is how the user gets results out of the
e-graph after saturation.

Given an e-class (a set of equivalent terms), find the lowest-cost
representable concrete term that belongs to the class.

### Cost Model

Each operator has a per-node cost, declared as `:cost n` on its
declaration and defaulting to 1. The cost of a term is the sum of its
nodes' costs, so an undeclared program pays one per node. For AC
nodes, child multiplicities
are accounted for: a child with multiplicity k contributes k ×
child_cost.

The implementation computes in saturating `usize` arithmetic and reserves
`usize::MAX` as the "unset" sentinel. It therefore optimizes exactly among
terms whose computed cost is below `usize::MAX - 1`; a grounded candidate whose sum
saturates is clamped to `usize::MAX - 1` and recorded, so it ranks last and is never
reported missing (`total.min(UNSET - 1)` in `extract.rs`).
This is a representational boundary, not an unbounded-integer optimality
claim.

Literal values have cost 1. Pattern variables are not runtime e-nodes, so they
are not extraction candidates.

An operator declared `:unextractable` is excluded from the candidate
set: the extractor never selects one of its nodes, though the node
stays in the e-graph and stays matchable. This is a filter, not a large
cost: a cost cannot express "never", and the two behave differently
when the alternative is expensive.

The costs and the exclusion are read from `OpInfo` (`cost`,
`unextractable`), hoisted into a per-op table before the fixpoint so the
inner loop indexes by op id rather than querying the registry per node.
`OpInfo::is_constructor` is registration metadata and stamps
`FLAG_CONSTRUCTOR` on the op's nodes; the extractor does not currently
prefer constructors over other operators.

#### Subsumption is not unextractability

`(subsume …)` hides a node from *matching* only: the matcher's indices
skip `FLAG_SUBSUMED`, but the extractor does not, so a subsumed node is
still extractable and can still be the extracted winner. That is why
`:unextractable` is a separate mechanism rather than sugar for
subsumption. Pinned by `subsumed_node_is_still_extractable` in
`tests/extract_best.rs`. Whether extraction should skip subsumed nodes
is an open question, deliberately left as-is here.

### Ties and the content order

Many classes hold several members of equal cost: `Add(a, b)` and `Add(b, a)` under a
commutative operator, two rewrites of one subterm with the same price, or two equally good
groupings under a cost model. Extraction must still return one term, and the one it returns
should depend only on the e-graph. The e-graph does not fix an order of its own: node and
class ids record allocation order, which follows the order rules fired, and that differs
between naive and semi-naive saturation, between rule orders, and between versions. A tie
broken by id makes the extracted term, and every test and comparison that reads it, depend
on that history. The same holds under a cost model: the variables Semper writes for a
solver are numbered in the order of the graph it converts, and among tied optima a solver
returns whichever its search meets first.

The extractor therefore orders nodes by a colour computed from content alone. Two classes
get the same colour exactly when they cannot be told apart by what they contain, however
they were built.

**Colour refinement.** `EGraph::canon_colours` (`canon_colour.rs`) starts from what each
class holds and refines by its children's colours until nothing changes:

```text
colour[0](c)   = H({ (label(m), arity(m), subsumed(m)) : m in members(c) })
colour[k+1](c) = H({ (label(m), kids(k, m), subsumed(m)) : m in members(c) })
kids(k, m)     = [(colour[k](child), 1)] in order     for plain and `a` operators
                 sorted (colour, count) pairs          for ac, aci, and comm
```

- `label` is the operator name, or a literal's value. A multiset child is one entry
  with its multiplicity, as the node stores it, so `arity` is the total count and an
  unordered node's pairs merge equal colours by summing their counts.
- The members are every node but a congruent duplicate.
- The rounds stop when the partition the colours induce stops changing. Each round before
  the fixpoint splits at least one block, so the class count plus one rounds suffice; the
  result reports `rounds` and whether it `converged`.
- The partition is the coarsest stable one, so two classes share a colour exactly when
  they are bisimilar.
- The hash is two seeded runs of `rapidhash_v3` (128 bits), whose output the crate
  guarantees stable across versions; `tests/canon_colour.rs` pins golden values.
- A node's colour hashes its class's colour with its own signature, so members of one
  class differ, unless their children are classes of one colour.

**Symmetric classes.** In a rebuilt e-graph no two distinct classes share a colour:
every class holds a finite term (a class is created holding the node just built, whose
children's classes hold finite terms, and a merge only adds), and two classes with a
common finite term are one class by hash-consing. A shared colour can therefore arise only
in a graph read before its rebuild, or on a 128-bit collision. Even then it cannot change
an extracted term's text: every choice is a function of colours, and two classes of one
colour have equal coloured structure.

Three users read the colours: the additive extractor's tie-break (below), the
`dump-egraph` export, which names and orders everything by colour, and the conversion for
extraction under a cost model (§11.2), which hands a solver classes, members, and children
in colour order. On the e-graphs of the 1,172 MLTL specifications of [JR26](#references),
naive and semi-naive saturation give byte-identical exports; with node-id names, 173 of the
1,172 pairs differed, and the extractor that read those dumps returned a different term
on 50.

### Algorithm: `extract_best`

Iterative fixed-point relaxation over all e-nodes (`best_members`):

```rust
// Dense arrays indexed by class id: ids are dense, so indexing replaces a hash per
// lookup. `UNSET` in `best_cost` marks "this class has no best node yet".
let colour = node colours from eg.canon_colours();          // see "Ties" above
loop {
    let mut changed = false;
    for each e-node id (not :unextractable, not a congruent duplicate):
        let slot = find(id);
        let total  = op_meta[op_of(id)].cost + Σ best_cost[find(child)] × mult;
        let height = 1 + max best_height[find(child)]      (0 for a leaf);
        if any child class has best_cost == UNSET { continue }   // not grounded yet
        let total = min(total, UNSET - 1);                   // saturated: ranks last
        if (total, height, colour[id]) < (best_cost[slot], best_height[slot], colour[best_node[slot]]):
            record id as the class's best; changed = true;
    if !changed { break }
}
```

The scan repeats until no class's key improves. Cost comes first, so the optimum is
the minimum additive cost representable below `usize::MAX - 1`, as before.
The two later keys decide among equal-cost nodes:

- **Height before colour.** With operators of cost 0, a class can reach itself at
  equal cost (`x = {a, f(x)}`), and a tie-break that may replace an equal-cost
  incumbent could choose a node whose child's best reaches the class: a cycle, which
  no reconstruction terminates on. Height strictly grows from child to parent, so a
  chosen node never lies on a cycle. Removing height from the key makes
  `a_zero_cost_cycle_is_not_chosen` (`tests/stable_extract.rs`) run until the guard
  kills it at 61 s.
- **Colour last.** The node's content colour decides any remaining tie, so the chosen
  node depends on the e-graph's content and not on the order nodes were allocated in.
  One e-graph built in two node orders extracts one term
  (`one_egraph_in_two_node_orders_extracts_one_term`).

The update strictly lowers one class's key in a well-founded order, so the loop
terminates. Focused tests cover cycles, shared classes, multiplicities, exclusions,
cost choice, and ties. This argument has not been refined into a machine-checked
theorem about `extract_best`.

`reconstruct` builds the term from the chosen nodes bottom-up with an explicit stack
(a post-order with a visited table), since a term's depth is the e-graph's: a
recursion would carry it on the call stack. A subterm shared by several parents is
built once and copied into each. An AC, ACI, or commutative node's operands are
placed sorted by their own printed text, an order fixed by content and readable; the
cost-model printer (`cost_models::render`) does the same.

For literal nodes, the extracted term includes the literal value.

### The export: `dump-egraph`

`to_egraph_json` (`dump.rs`) writes the whole saturated graph in the JSON shape
`egglog --to-json` produces, for a tool that runs outside Semper and reads the graph
itself: an extractor written against egglog's serialized e-graphs, or a comparison
script. No solver reads it. Semper's own solvers receive OPB, ASP, or MiniZinc that the
library writes from its in-process conversion (§11.2, §11.3), not this file. Every name and order comes
from the colouring:

- a class is `{sort}-{colour}`, a node `n{colour}-{sort}`, the colour as 32
  hexadecimal digits; classes sharing a colour get a rank suffix by smallest member id;
- nodes and class entries are written in name order, and an AC, ACI, or commutative
  node's children in name order (plain and `a` children keep their order);
- a child entry names the member of the child class whose name sorts first; a
  multiset child of multiplicity k is written once, with k in `"mults"`, parallel to
  `"children"`;
- `class_data` carries each class's `colour`; `op_kinds` says which operators'
  children are unordered; `DumpStats` reports `colour_rounds` and `symmetric_groups`.

Two runs that build the same e-graph therefore write the same bytes.

### Failure

Extraction returns `ExtractError` rather than an empty option, so the
caller can say why:

- `AllUnextractable { class, ops }`: the class has nodes, but every one
  of them is an `:unextractable` op. Reachable, and named: the error
  carries the class and the offending op names.
- `NoGroundTerm { class }`: no node in the class has a fully costed
  child set. This is reachable when every candidate depends on a cycle with no
  extractable base, or when an otherwise extractable parent depends on a class
  whose nodes are all `:unextractable`. A saturated sum does not cause it: such a
  candidate is recorded at `usize::MAX - 1`.

### Limitations

The extractor uses an additive per-node cost. It does not handle:
- Constructor preference (`is_constructor` is stamped but unread here)
- DAG extraction (each subtree is extracted independently)
- Extraction with constraints (e.g., "extract a term of sort X")

A cost that is not additive (one that reads a node's siblings, or which subterms the
term shares) is extracted under a cost model inside Semper (`(extract … :cost …)`,
§11.2).

### Alternatives considered and rejected

- **A strict `<` with ties left to arena order.** The original update replaced the
  incumbent only on a strictly lower cost, so among equal-cost nodes the first in
  allocation order won, and allocation order follows the order rules were applied
  in. Replaced by the (cost, height, colour) key.
- **Colour alone as the second key.** Without height, a zero-cost cycle can be
  chosen and reconstruction does not terminate (above).
- **A recursive `reconstruct`.** It descended the selected term on the call stack and
  could exhaust it on a deep result; replaced by the explicit stack.
- **Node-id names in the dump** (`n{id}-{sort}`, a class named by its smallest
  member id). Stable within a run but not across runs: naive and semi-naive dumps of
  one e-graph differed in bytes on 173 of the 1,172 specifications of [JR26](#references), and since an external
  solver numbers its variables in name order, its choice among tied optima differed
  too, giving different terms on 50 of them. Replaced by content colours.
- **Comparing dumps outside Semper only** (`dump_canon.py`). It was the A/B gate
  from 2026-09-30 and stays as a diagnostic; the canonical export makes byte equality
  the gate.
- **A separate extractor binary** (`memdag`). It read the dump, optimized a flat
  objective, and reported the best of three terms after a grouping post-pass, one of
  them the first node of each class in name order. The reported figure was not the
  proved one, and on 2 of the 1,172 specifications it depended on node ids. Deleted on
  2026-10-03; extraction under a cost runs inside Semper (§11.2).

## 11.2 Extraction Under Cost Models

This section explains extraction under a cost the user writes, from first principles:
what is being chosen, how the choice becomes a constraint problem, why the flat nodes of
§5 hide structure a cost may need, and how that structure is put back without expanding
it. It then records the implementation: where the work is split, what each layer
guarantees, and the decisions with their alternatives. The user view is chapters 24 to 28
of the book. The library is the module `crate::extraction` (`src/extraction/`), in the
default build. Until 2026-10-06 it was four crates in the `ltl-eqsat` repository
(`extract-api`, `extract-script`, `mltl-cost`, `pb-verus`).

### Extraction is a selection problem over an AND/OR graph

An e-graph is an AND/OR graph. A class is an OR node: to produce a term of the class, pick
one of its members. A node is an AND node: to produce a term of the node, produce a term
of every child class. A term of the root class is therefore a selection: a set of classes
and, for each, one member, closed under "a selected node's child classes are selected".

```text
class 0 (root): { And(c1, c2) }          n0
class 1:        { G[0,9] (c3),            n1
                  F[0,9] (c3) }           n2
class 2:        { F[2,3] (c4) }           n3
class 3:        { Var "a" }               n4
class 4:        { Var "b" }               n5
```

This e-graph has two terms, `And(G[0,9] a, F[2,3] b)` and `And(F[0,9] a, F[2,3] b)`; the
choice in class 1 is the only decision. §11.1 extracts under an additive cost, a fixed
price per node, by relaxation. A cost that is not a sum of per-node prices needs the
selection stated as a constraint problem, which a solver then optimizes.

### Selection as constraints

The selection rung (`Selection::build`, `rung.rs`) introduces one literal per reachable
class, `sel_class[c]`, and one per candidate node, `sel_node[n]` (subsumed nodes are not
candidates). The clauses state the closure above:

| rule | clause |
| --- | --- |
| the root is selected | `sel_class[root]` |
| a selected node selects its class | `¬sel_node[n] ∨ sel_class[c]` |
| a selected node selects each child class | `¬sel_node[n] ∨ sel_class[k]` for each distinct child `k` |
| a selected class selects one of its members | `¬sel_class[c] ∨ sel_node[n1] ∨ … ∨ sel_node[nm]` |
| and at most one | the sequential at-most-one, `3m − 4` clauses |

A model is a selection; decoding reads the selected node of each class and keeps the
classes the root reaches. Acyclicity is not encoded: an e-graph has cycles, and a model may
select one. The solve loop checks each decoded term and, when it is cyclic, adds one clause
excluding that cycle's selected nodes and solves again ("Cycles" below). The ASP and
MiniZinc paths rule cycles out natively, by groundedness and by a rank per class.

### Costs over selectors

An additive cost is a pseudo-Boolean objective over the selectors: `Σ w(n) · sel_node[n]`.
The first extraction of book chapter 24 charges each chosen node once, which counts a
shared subterm once, where §11.1 counts it once per use.

A cost that depends on more than which nodes are chosen is stated with integers whose
value depends on the selection. They are order-encoded (`OInt<P>`, `oint.rs`): an integer
over a known, sparse value set `v0 < v1 < …` is one literal per value, `[x ≥ vj]`, chained
`[x ≥ vj+1] → [x ≥ vj]`. Charging it adds `v0 + Σ (vj − vj−1)·[x ≥ vj]` to the objective,
all weights positive. The size follows the number of values, not their magnitude. The
typical integer is a per-class attribute: `rec_max` gives each class the maximum over the
selected node's children plus the node's offset, by the clauses

```text
¬sel_node[n] ∨ [me ≥ off(n)]                          (a leaf)
¬sel_node[n] ∨ ¬[attr(k) ≥ v] ∨ [me ≥ v + off(n)]     (each child k, each value v)
```

With offset 1 on every node it is the term's height. An encoding forced in one direction
is smaller, so every integer carries a polarity in its type: `Exact` (the literals equal
the true value), `Over` (they may say more, which a minimizing solver has no reason to
do), or `Under`. Every operation has one: `max_of` of upward parts is `Over`, `neg` flips,
`minus(a, b)` takes `b` of the flipped polarity, and only an upward integer can be charged.
The Roto binding checks polarity at check time, as a type error. The reported cost never
trusts the encoding: it is the cost evaluated on the returned term ("Soundness of the
reported cost" below).

### Flat nodes hide structure a cost may need

§5 stores every grouping and ordering of an AC operator's operands as one flat node, and
every bracketing of an `:assoc` sequence as one sequence node; that is what keeps
saturation from enumerating them (a conjunction of 10 distinct operands has 282,137,824
groupings, and about 3.7 × 10^11 groupings with orders). A cost that depends on the grouping cannot be evaluated on the
flat node: the extraction has to choose a grouping as well as a node, and return the
reconstructed tree.

#### The motivating cost: the memory of an MLTL runtime monitor

Mission-time LTL (MLTL) is the temporal logic of runtime monitors for flight software.
It is linear temporal logic over finite traces whose temporal operators carry an integer
interval: `G[l,u] p` holds at step `t` when `p` holds at every step from `t+l` to `t+u`,
`F[l,u] p` when it holds at some step in that range, and `U[l,u]` and `R[l,u]` bound until
and release the same way. A specification is a conjunction of such properties over sensor
and command signals, written by engineers, for example "the brake pressure stays below its
limit for the next 10 steps whenever the pedal is released".

R2U2 checks MLTL specifications while the system runs, often on embedded hardware with
little memory. Its compiler, C2PO, turns a formula into a tree of operators, one per
subformula, each producing a stream of verdicts, one per step. A subformula's verdict for
step `t` arrives after a delay that lies between a best case and a worst case, `bpd` and
`wpd`: an atom has 0 and 0, and `G[l,u] p` or `F[l,u] p` adds `l` to the best case and `u`
to the worst case of `p`. An operator over several operands needs all their verdicts for
the same step, so an operand that is ready early keeps its verdicts in a queue until its
slowest sibling catches up. Its queue holds `max(wpd of its siblings) − bpd of itself`
verdicts, plus one. The monitor's memory is the sum of its queues.

Johannsen and Rozier shrink this memory with equality saturation [JR26](#references):
rewrite rules for MLTL produce equivalent specifications (merging `G[0,5] p ∧ G[3,9] p` into
`G[0,9] p`, factoring a common interval out of a conjunction, §7.6), and an extractor picks
the one with the least memory. The memory is not a price per node. It depends on which
siblings each subformula has, so on how every conjunction is grouped, and a subformula
shared by two parents is queued once, for its most demanding use. Conjunction and
disjunction are AC and idempotent, so §5 stores each conjunction flat: every grouping is
the same node.

#### The terms, the rules, and the cost

**The terms.** An MLTL formula is a term over these declarations (the prelude of
`tests/mltl/rules/tests/nary_check_1.egg`):

```lisp
(sort IntervalSort)
(function Interval (i64 i64) IntervalSort)
(sort MLTL)
(function Bool (bool) MLTL)
(function Var (String) MLTL)
(function Not (MLTL) MLTL)
(function Implies (MLTL MLTL) MLTL)
(function Equiv (MLTL MLTL) MLTL)
(function And (MLTL) MLTL :assoc-comm-idem :identity (Bool true))
(function Or (MLTL) MLTL :assoc-comm-idem :identity (Bool false))
(function Global (IntervalSort MLTL) MLTL)        ; G[l,u] p
(function Future (IntervalSort MLTL) MLTL)        ; F[l,u] p
(function Until (IntervalSort MLTL MLTL) MLTL)    ; p U[l,u] q
(function Release (IntervalSort MLTL MLTL) MLTL)  ; p R[l,u] q
```

Conjunction and disjunction are variadic, associative, commutative, and idempotent, with
`true` and `false` as identities, so the algebra of §5 absorbs what egglog needs explicit
rules for (associativity, commutativity, arity variants, idempotence).

**The rules.** `tests/mltl/rules/mltl.egg` ports the rewrite rules of the artifact of
[JR26](#references) (its `temporal.egg` and `const_folding.egg`); a rule over a pair of
conjuncts gains a `..rest`, so it matches the pair inside a conjunction of any size. The
families are:

- negation, implication, and equivalence, De Morgan, and the dualities `¬F[l,u] p =
  G[l,u] ¬p` and `¬(p U[l,u] q) = ¬p R[l,u] ¬q`;
- collapsing nested operators: `G[a,b] G[c,d] p = G[a+c, b+d] p`, and the same for `F`
  and for a point interval inside or outside;
- merging windows over one operand: `G[a,b] p ∧ G[c,d] p = G[a, max(b,d)] p` when the
  windows overlap or touch (`a ≤ c ≤ b + 1`), and dually `F` in a disjunction;
- factoring a common window out of a conjunction: `G[a,b] p ∧ G[c,d] q =
  G[K0,K1] (G[a−K0, b−K1] p ∧ G[c−K0, d−K1] q)` with `K0 = min(a,c)` and
  `K1 = K0 + min(b−a, d−c)`, and dually for `F` in a disjunction;
- narrowing: an always over `¬p` shrinks the window an eventually over `p` searches;
- constant folding and absorption: `p ∧ ¬p = false`, `G[l,u] true = true`, and so on.

The n-ary versions of merging, factoring, and narrowing (`mltl_nary_decl.egg`, §7.6) apply
each to every matching conjunct at once, which keeps the e-graph small: one rule firing per
conjunction instead of one per pair. Factoring is where most of the memory saving comes
from. `G[2,5] p ∧ G[3,9] q` has `K0 = 2` and `K1 = 2 + min(3, 6) = 5`, so it equals
`G[2,5] (p ∧ G[1,4] q)` (an inner window `[0,0]` is the operand itself): the shared part of
the two windows moves outside, and the conjunction inside waits for less.

**The cost.** For a chosen term, each class `c` has a worst-case and a best-case delay,
computed bottom up from the chosen node:

```text
wpd(c) = u + max over children k of wpd(k)        bpd(c) = l + min over children k of bpd(k)
```

with `[l,u]` the node's interval for `G`, `F`, `U`, `R`, and `l = u = 0` for any other
node (a leaf has delay 0). The memory is

```text
memory = 1                                                     the specification's queue
       + Σ over chosen classes c, other than Bool constants:
             1 + max(0, max over siblings s of c of wpd(s) − bpd(c))
       + Σ over groups t of the chosen trees:
             1 + max(0, max over siblings s of t of wpd(s) − min over members m of t of bpd(m))
```

The siblings of `c` are the other operands of every chosen node `c` is an operand of, under
every parent at once, so a shared subformula is charged once, for its most demanding use.
A group is an internal node of a rendered conjunction (§11.2, "Putting the structure back
with selector variables"): it waits as one operand whose best case is its fastest member's
and whose worst case is its slowest member's. In the factoring example, `G[2,5] p ∧
G[3,9] q` costs 15 (5 subformulas and the specification; `G[2,5] p` queues 9 − 2 = 7,
`G[3,9] q` queues 5 − 3 = 2), and `G[2,5] (p ∧ G[1,4] q)` costs 10 (`p` queues 4, nothing
else waits).

The same cost is written in Roto, ASP, MiniZinc, and Rust under `tests/mltl/costs/`
(`mltl_memory.*`), and registered as `:rust "mltl-memory"`.

#### Grouping changes the memory

Take `p ∧ q ∧ r` with `p`, `q` atoms and `r = F[0,10] s`, so `wpd(r) = 10` and every other
delay is 0. A group of operands is itself an operator whose worst case is its members'
largest and whose best case is their smallest.

| grouping | queues | queue slots |
| --- | --- | --- |
| `And(p, q, r)` (flat) | `p` waits for `r`: 10; `q` waits for `r`: 10 | 20 |
| `And(And(p, q), r)` | the group `{p, q}` waits for `r`: 10, plus 1 for the group | 11 |
| `And(And(p, r), q)` | `p` waits for `r`: 10; `q` waits for the group (worst case 10): 10; the group, 1 | 21 |

With one slot per subformula and one for the specification, the memories are 26, 17, and
27. The queue sits on the early producer, and a group shows the outside the widest spread
of its members' delays, so grouping the fast operands together and leaving the slow one
outside is the cheapest. No price per node states this: the same flat node costs 26, 17, or
27 depending on a tree it does not store.

### Putting the structure back with selector variables

Enumerating the trees of every flat node in the encoding would reintroduce the blow-up
canonization removed. Instead, a rung adds, for each candidate flat node with 3 to 16
operands, variables that describe one tree over its operands, and constraints under which
every tree has exactly one model (`TreeVars`, `rung.rs`). The variables are per operand and
per depth, so the encoding grows with the number of operands, not with the number of trees:

- `dep[i][d]`, "operand `i` sits at depth `d` or deeper", as a thermometer over depths;
- `lab[i][d][l]`, the label of the sub-block operand `i` continues into below depth `d`;
- `same[i,s][d]`, "operands `i` and `s` are in one block at depth `d`", defined from the
  depths and labels;
- `pos[i][d][p]`, the position of `i` among its block's children, at the `orders` rung
  only.

A block is a set of operands that share their labels down to some depth; a tree is the
nesting of blocks. Symmetry breaking makes the representation unique: labels are numbered
by the block's smallest operand (a label `l` needs an earlier block-mate with label
`l − 1`), every sub-block has at least two members, and a block with a continuing member has
a second operand, so no internal node is unary. For each block that may exist the rung
names an inner node, `Inner { exists, members, siblings }`: `exists` is true when the flat
node is selected and the block is present, and each member and sibling carries the literals
under which it is one. An operand of multiplicity `k` is one leaf with all its copies at
every rung, so the number of trees depends on the number of distinct operands only.

For the example above, `And(And(p, q), r)` is `p` and `q` at depth 2 with one label, `r` at
depth 1; `And(And(r, p), q)` and `And(And(p, r), q)` are one assignment, since `{p, r}` is
one block.

### The ladder

A rung is a family of trees the constraints admit, and a higher rung admits more and costs
more clauses. The cost is written once and runs at every rung; the rung is an argument of
the `extract` command (`:rung`), not of the cost.

| rung | tree variables | trees over a flat node of `k` operands | `k` = 3, 4, 5 |
| --- | --- | --- | --- |
| `selection` | none | the flat node | 1, 1, 1 |
| `levels` | a depth per operand, one label | chains of nested blocks | 4, 23, 166 |
| `splits` | depths and labels | every unordered tree | 4, 26, 236 |
| `binary` | as `splits`, every block exactly two children | every binary tree, `(2k − 3)!!` | 3, 15, 105 |
| `orders` | as `splits`, plus a position per operand per block | every ordered tree | 18, 264, 5,400 |

- **`selection`** chooses nodes only; a flat node is costed as written, each operand's
  siblings being every other operand. It is the smallest problem.
- **`levels`** gives each operand a depth. Operands at the same depth form one block, and
  each block holds the one below, so the trees are chains: `And(And(p, q), r)` but not
  `And(And(a, b), And(c, d))`. A cost can read each operand's depth.
- **`splits`** adds a label per depth, so a block can split into several sub-blocks: every
  unordered tree. It is the rung a grouping cost needs.
- **`binary`** restricts every block to exactly two children, for a target with only
  binary operators. It excludes the flat node and every group of three or more, so it is
  not above `splits`: in book chapter 24's example it costs 40 against 37.
- **`orders`** adds a position per operand within its block, so the cost can depend on the
  order of the operands, at most 8 of them.

An `:assoc` sequence is bracketed the same way, with intervals instead of blocks: one
literal per interval of at least two positions, no two intervals crossing (`seq.rs`).
`levels` gives chains of nested intervals (3, 10, 34), `splits` every bracketing (the
little Schröder numbers 3, 11, 45), `binary` the full bracketings (the Catalan numbers 2, 5,
14), and `orders` acts as `splits`, since a sequence's order is fixed. A fold
(`:assoc-left`, `:assoc-right`) has one bracketing, its prefixes or suffixes, whose inner
nodes are present at every rung. A `:comm` pair and a flat node of fewer than 3 operands
have one tree.

The tree variables grow with the operands, so a rung's encoding is estimated before it is
built (`RungKind::estimate`), and a rung over `:budget` estimated clauses (default
3,000,000) steps down, `orders` to `splits` to `levels` to `selection`, and `binary` to
`selection`, with a warning. An unguarded run at a tree rung on three saturated e-graphs
reached 8 GB before the estimate existed.

### Choosing the node and the grouping together

The rungs encode the node choice and the tree choice in one problem, so the proved optimum
is the optimum over terms and their groupings at once. Choosing the nodes first, under the
flat cost, and grouping each flat node afterwards is not optimal: on 600 random instances (a
flat conjunction over three to five classes with two candidate intervals each) the
sequential choice landed above the joint optimum on 130 (21.7%), by up to 31%, as
measured with `choosing_the_grouping_after_the_nodes_is_not_optimal`
(`tests/ex_paper_claims.rs`), which prints these figures and asserts that some instance
differs. The
term that is best after grouping is often not the flat optimum, so the first step never
selects it.

### How a cost reads the structure

A cost never names the rung's variables. It reads four views, and each is empty or `None`
where the rung decides nothing:

| view | what it is | at `selection` |
| --- | --- | --- |
| siblings of a child | the other operands of the node or block the child is a direct operand of, each with its gate | every other operand |
| inner nodes of a node | the blocks that may exist, each with `exists`, members, and siblings | a fold's fixed blocks only |
| depth of a child | an `Exact` integer, 1 for a direct operand | `None` |
| position of a child | an `Exact` integer, at `orders` | `None` |

The memory cost above uses only the first two, which is why one definition runs at every
rung. Each language surfaces the views in its own terms:

| view | Rust (`Rung`) | Roto | ASP facts and rules | MiniZinc |
| --- | --- | --- | --- | --- |
| selection | `selection().class(c)`, `.node(n)` | `Class.chosen()`, `Node.chosen()` | `used(C)`, `pick(N)` | `used[c]`, `pick[n]` |
| siblings | `siblings(n, c)` | `Use.siblings()`, `Sibling.present()` | `parent(N,X,G)` and `bmem(N,G,P)` | `parent_leaf`, `parent_blk`, `bmem` |
| inner nodes | `inner_nodes(n)` | `Node.inner_nodes()`, `Inner.exists()`, `.members()`, `.siblings()` | `inner(N,B)`, `bmem(N,B,P)` over candidate blocks `cand/2` | `inner[b]`, `bmem[b,p]` over blocks `bnode`, `blo`, `bhi` |
| depth | `nesting().depth(b, n, c)` | `Child.depth()` | `depth(N,P,D)` | `depth[n,p]` |
| position | `ordering().position(b, n, c, d)` | `Child.position(d)` | `pos(N,G,X,Q)` | `pos_leaf`, `pos_blk` |
| the rung | the `Rung` value | `g.rung()` | `chains(N)`, `binary(N)`, `ordered(N)` | `family[n]` |

In Roto and Rust the views are gated literals and encoded integers: the script states a
rule over a choice it cannot read ("charge 10 if this inner node exists"), and the solver
finds the cheapest choice. In ASP and MiniZinc the rung's choices are the user's
predicates or decision variables, and the criterion computes over them directly. The
memory cost's inner-node term, for example:

```text
Roto:      g.max_over(sibs).minus(g.min_under(mems)).clamp(0).charge();
           // sibs: wpd of each sibling, when t.exists() and it is present
ASP:       own(N,B,M) :- inner(N,B), M = #min{ … : bmem(N,B,Q), … }.
           blatest(N,B,X) :- inner(N,B), parent(N,B,G),
                             X = #max{ A,Q : bmem(N,G,Q), not bmem(N,B,Q), … }.
MiniZinc:  (inner[b] /\ not bmem[b,q] /\ …) -> iqueue[b] >= wpd[…] - own[b]
```


### Layers

| layer | where | responsibility |
| --- | --- | --- |
| commands | `parser.rs`, `sortcheck.rs`, `interpret.rs` | parse, compile the script at check time, run |
| conversion | `cost_models.rs` | e-graph to the library's graph; the term back as text and JSON |
| encoding | `extraction::{rung, oint, pb, dpw, seq, target, totalizer}` | rungs, integers, lowering to CNF, OPB, or ASP |
| solving | `extraction::{solve, asp, lp, mzn}` | the loops, cycle exclusion, interpretation, certificates |
| scripting | `extraction::script` | the Roto binding |

**The script is compiled at check time.** `CostModel` handles are compiled by
`sortcheck_pass` and stored in the ruleset table, so a type error in a script,
a polarity error included, rejects the program before any command runs, with
the command's span and the script's line. The alternative, compiling at the
`extract`, would report the error after saturation.

**Conversion.** `to_graph` takes the classes, each class's members, and an
unordered node's children in content-colour order (`canon_colour.rs`, §11.1),
as `dump-egraph` writes them, so the graph's indices, and with them the solver's
choice among tied optima, do not depend on node ids. A child whose sort is a value
sort becomes payload of its parent;
the value sorts are the least set closed under "every node of the sort has only
value-sort children", less the root's sort. An MSet child of multiplicity k is one
child with count k in `Node::mults`, as in `dump-egraph`, and an MSet or Set node is flat. The conversion is generic: no operator
name is special.

### Soundness of the reported cost

Every cost is stated through operations whose types carry a polarity (exact,
over-, or under-estimate), and the library evaluates the recorded expression
graph on the returned term instead of reporting the solver's objective. An
encoding forced in one direction may let a model's objective exceed its term's
cost; it never lets it fall below, and interpretation reports the term's own
value. `proved` then means: every term has a model whose objective is its cost
(its canonical assignment), and the final solve found none below the reported
one.

### Cycles

The encodings do not exclude cyclic selections. The CNF loop adds a clause over
the selectors of a cycle when a decoded term has one and continues the same
incremental solve; the OPB loop appends the clause and restarts; the ASP program
carries groundedness rules (`ok(c)` holds only through a finite derivation), so
no answer set is cyclic. Lazy exclusion was measured at about 2.4 exclusions per
extraction on the 1,172 MLTL specifications of [JR26](#references).

### Greedy scoring

`:solver greedy` scores §11.1's additive choice under the cost model, in the
same e-graph: `best_members` exposes that fixpoint's member per class, and the
library interprets the cost on the resulting selection. Scoring greedy's printed
term in a fresh e-graph instead was measured to be unfair: rebuilding a written
term flattens nested applications that the saturated e-graph keeps apart, which
gave greedy regroupings no extractor of the saturated graph could return.

### Certificates

`:proof "dir"` gives a proof-logging OPB solver `--proof-log` on every call and
names the last call's instance and proof. VeriPB checks that no model of the final
instance has a lower objective. The instance includes the loop's cycle exclusions
and incumbent bound; both only remove models the reported term does not need. On
64 monitor instances drawn from [JR26](#references), 63 certificates verify and the 126 proofs whose
conclusion is changed by one are all rejected (`tests/ex_paper_claims.rs`,
`every_optimum_is_certified_by_veripb`). On the 64th, RoundingSat aborts
(`std::length_error`) on the clause set the encoder writes; 58 of its clauses
reproduce the abort (`tests/roundingsat_length_error.opb`), and the
internal descent proves that instance's optimum, 2,925.

### Alternatives considered and rejected

- **A separate extractor over the dump, optimizing the flat objective, then the
  grouping.** `memdag` proved the optimum of the flat rendering, chose each flat
  node's grouping afterwards, and reported the best of three terms after that
  post-pass: its own, the greedy one, and the first node of each class in name order.
  Choosing the grouping after the nodes is not optimal: on 600 instances (a flat
  conjunction over three to five classes with two candidate intervals each), the
  sequential pipeline is above the joint optimum on 130 (21.7%), by up to 31%, all of
  it from the choice among tied flat optima
  (`choosing_the_grouping_after_the_nodes_is_not_optimal`). The name-ordered
  candidate made two of those figures depend on node ids. The joint rungs encode the
  grouping, so the proved figure is the reported one; `memdag` was deleted on
  2026-10-03.
- **A lexicographic second objective to break ties.** Rejected before it was built:
  it would change the pseudo-Boolean encoding and the optimality proof of every
  benchmark, and a rank sum is not a total order on terms. The canonical export
  (§11.1) gives identical inputs for identical e-graphs, and a deterministic
  solver then returns identical terms.
- **A choice among enumerated optima.** Considered as the tie-break for the separate
  extractor; void with it.


## 11.3 Backends, APIs, and Criteria

§11.2 says how a cost becomes a proved term. This section says what a user writes and
where it runs: the command, the backends and what each proves, the encoded integers a
cost is stated in, the Rust and Roto APIs, and how a criterion is written in Roto, ASP,
and MiniZinc. The user view is chapters 24 to 28 of the book.

### The command

`(cost-model NAME :script "f.roto" | :rust "id" | :asp "f.lp" | :minizinc "f.mzn")`
names a cost. It is compiled at check time (§11.2, "Layers"): a script is scanned for
native arithmetic, compiled by Roto, and its `cost` function looked up; an ASP or
MiniZinc file is read as text and not parsed until a solver runs it; a `:rust` id is one
of a fixed table of three (`mltl-memory`, `pipeline-registers`, `monitor-history`,
`cost_models.rs`), with no registration from a program.

`(extract TERM :cost NAME …)` takes its options in any order: `:rung` (default
`selection`), `:budget` (default 3,000,000 estimated clauses), `:solver` (default
`internal`), `:file`, `:proof`, and `:band LO HI [:count K]` (K defaults to 10). Sortcheck
refuses the combinations no backend runs: an unknown model or rung, `:band` off the
internal solver, `:proof` off a pseudo-Boolean solver, an ASP criterion without
`(asp …)`, and a MiniZinc criterion without `(minizinc …)` or the converse. The output
line is `; cost C STATUS at rung R (n solves, m cycle exclusions)` with `STATUS` either
`proved` or `bounded`; a run that finds no term is the error `no term: …`.
`--cost-bits 32|64|big` caps the cost width (default `big`, no cap): every encoded
integer and the interpreted total are checked against it, and a value outside is an
error naming the operation.

### Backends

| `:solver` | runs | encoding | how it reaches the optimum |
| --- | --- | --- | --- |
| `internal` | CaDiCaL, linked | CNF, in memory | descent in one incremental instance: after an incumbent, assume `objective ≤ best − 1` through a windowed totalizer, exact `Cost` weights when `u64` does not fit |
| `dpw` | CaDiCaL and rustsat's DPW, linked | CNF | the same descent, bound by `DynamicPolyWatchdog` |
| `roundingsat`, `(opb "p" …)` | an external process | OPB file | restart: each call is a fresh process; the incumbent and the cycle exclusions are restated as constraints |
| `(asp "clingo" …)` | an external process | ASP program | one call; clingo minimizes, and groundedness rules exclude cycles |
| `(minizinc "s" …)` | `minizinc --solver s` | MiniZinc model | only for a MiniZinc criterion; a search, then a re-solve with the term fixed |
| `greedy` | none | none | §11.1's additive choice, scored at `selection` |

The internal and DPW loops stop after 100,000 SAT calls and have no time limit. The OPB
loop stops after 201 calls or 3,600 s, checked between calls, so a running call is never
interrupted. The ASP and MiniZinc paths set no limit; the user passes the solver's own
flags. A missing or crashing OPB binary, or clingo under a script cost, shows only as
`no term: Bounded`; an ASP or MiniZinc criterion names the program in its error.

**What `proved` means.** For the CNF loops: the solve under the incumbent bound is
unsatisfiable, or the incumbent reaches the objective's base. For OPB: an acyclic model
with `s OPTIMUM FOUND`, or `s UNSATISFIABLE` with an incumbent. For clingo: the JSON result
says the optimum was found. For MiniZinc: the search output ends with `==========`; the
reported `objectiveBound` is printed and never decides the status. Each rests on the
argument of §11.2, "Soundness of the reported cost": every term has a model whose
objective is its cost, so a solver's optimum is a lower bound.

**Certificates.** `:proof "dir"` is accepted only with `roundingsat` or `(opb …)`; each
call gets `--proof-log` and keeps its instance (§11.2, "Certificates"). The internal
descent emits no certificate.

### The objective's encoding

The internal descent bounds the objective with a windowed generalized totalizer, which
is pseudo-polynomial: each node holds every partial sum up to the bound. `dpw` bounds it
with rustsat's dynamic polynomial watchdog, whose size grows with the number of terms
and the logarithm of the weights. A native pseudo-Boolean solver needs neither. On Herbie
programs after rewriting, under an 8 GB guard (measured 2026-09-27 with
`examples/diagnose.rs`):

| program, rewritten | internal | RoundingSat |
| --- | --- | --- |
| `Quantum` | 5,993 proved, 558 MB, 1 s | 5,993 proved, 31 MB, 1 s |
| `basilisk` expression | 1,655 proved, 1,057 MB, 3 s | 1,655 proved, 59 MB, 50 s |
| `prospero` | killed at 9.3 GB | 75,765 proved, 45 MB, 1 s |
| `bear` | killed at 7.3 GB | killed at 7.5 GB |

**Pre-sorted blocks rejected.** Giving the totalizer each charged integer as one sorted
leaf was measured with the same tool at the bound below the first model and is not
smaller: 46.6 M clauses against 31.4 M on `Quantum`, 5.2 M against 4.7 M on `basilisk`.
The partial sums, not the leaves, set the size. Revisit only for integers with widely
different steps.

**`bear` exceeds the limit in its cost formula, not its objective.** The formula is
9.4 M clauses, most of them in clamped subtractions between dense sibling domains of
about 2,600 values. A merge network for dense subtractions brought it to 2,295,678
clauses, above the 10^6 target (`doc-draft/goals/goal-cost-algebra.md` in the ltl-eqsat
repository, step 4). Postponed: a coarser encoding of the recursive attributes, or a
lower network threshold; revisit when a cost formula, not its objective, is what exceeds
the memory limit.

### Solver range checks

A backend that reads integers in a fixed width is given only values that fit it, so a
number is refused, never read wrongly (`SolverRange`, `solve.rs`):

| backend | range | checked on |
| --- | --- | --- |
| `internal` | none | nothing (u64 totalizer when it fits, exact otherwise) |
| `dpw` | the objective's weights and their total fit `u64` | the objective |
| OPB | RoundingSat unbounded; clasp or clingo 32-bit; any other program 64-bit | every coefficient, bound, and weight, cycle exclusions and incumbent included, before each call |
| clingo under a script | 32-bit | every PB coefficient, bound, and weight, at build time |
| ASP criteria | 32-bit | every payload integer and multiplicity Semper writes |
| MiniZinc criteria | 32-bit for chuffed and gecode; 2^53 for the MIP solvers; 64-bit otherwise | every payload integer and multiplicity Semper writes |

The criteria checks cover only the numbers Semper writes: an overflow inside the user's
ASP or MiniZinc is the user's to rule out, and the error says so.

### The Rust API

There is no cost trait. A cost is a function over a rung and a builder,
`Fn(&R, &mut Build)` with `R: Rung`, and `solve::extract(graph, make, cost, solver)`
returns an `Outcome { term, cost, status, warnings, stats, solver_costs, certificate }`.
`make` builds the rung from a `Selection` (`Selection`, `Levels`, `Splits`, `Orders`,
`rung.rs`). `solve::cost_of` interprets a cost on a given term without solving, and
`solve::solve_prepared` lets a caller choose the width through `Build::with_width`.
`solve::extract_asp` takes an `AspBuild` cost, which may add rules and `#minimize`
statements of its own; such a cost does not compile against `extract`. The three
registered costs are `fn(&dyn Rung, &mut Build)` (`NativeCost`, `mltl_cost.rs`). The
graph a cost reads (`graph.rs`) has nodes with an operator name, integer and string
payload, children with their counts, and a `Kind` (plain, commutative, sequence with its
fold, multiset, set).

### The Roto API

A script defines `fn cost(g: Graph)`, called once per build. It reads the graph through
`Graph` (`classes`, `root`, `nodes`, `rung`), `Class` (`nodes`, `parents`, `chosen`),
`Node` (`op`, `kind`, `children`, `ints`, `nums`, `strings`, `chosen`, `inner_nodes`), and
`Child` (`class`, `multiplicity`, `count`, `index`, `depth`, `position`). The solver's
values are typed by polarity: `Bool`, `BoolOver`, `BoolUnder`; `Exact`, `Over`, `Under`;
`Pb`, `PbOver`, `PbUnder`. A polarity error is a Roto type error, reported at check time
whether or not its branch would run. The sinks are `charge` (on `Exact`, `Over`, `Pb`,
`PbOver`), `charge_if` (on `Bool`, `BoolOver`), `require` (on `Bool`, `BoolUnder`),
`g.charge_const`, and the cardinality constraints `g.at_most` and `g.at_least`.

**Exact arithmetic in scripts.** Facts known before solving are computed with `IBig`
and `UBig` (`plus`, `minus`, `times`, `div`, `rem`, `neg`, comparisons), and every method
that takes a count or a constant has a `_big` form. A fault (division by zero, a
negative `UBig`) is a build error. Roto's own operators are refused before Roto compiles
the script (`reject_native_arithmetic`, `script.rs`): `+ - * / %`, their compound
assignments, and `--`, because Roto's integers wrap on overflow and abort on division by
zero. A minus sign before a literal, `->`, `=>`, comparisons, comments, and string and
char literals are allowed; an f-string is scanned whole. The error names the file, the
position, and the operator, and points to the exact methods
(`tests/ex_native_arith.rs`). A symbolic reasoning tool cannot report a cost that may
have wrapped: the refusal is lexical so that no script reaches the JIT with one.

### Writing a criterion

**In Roto or Rust**, the criterion is the cost function itself: Semper encodes it for
the chosen backend (CNF clauses and totalizers, OPB constraints, or an ASP program with
`#sum` constraints and `#minimize`) and reports the interpreted cost of the returned
term.

**In ASP** (`:asp "f.lp"`), the user writes clingo rules and `#minimize` statements over
the facts Semper emits for each reachable class and candidate: `root/1`, `class/1`,
`node/3`, `kind/2`, `kid/3`, `operand/2`, `mult/3`, `int/3`, `str/3`, `leaf/3`, and the
rung's tree facts. Semper adds the rung's rules (`pick/1`, `used/1`, `inner/2`, …) and
the groundedness rules, runs clingo, then re-solves with the term fixed. The reported
cost is clingo's value for the highest-priority level on that fixed term; Semper does not
recompute it, and prints every level as `; solver objective […]`.

**In MiniZinc** (`:minizinc "f.mzn"`), the user writes variables, constraints, and one
`solve minimize` item over the data Semper emits (`C`, `N`, `ROOT`, `cls`, `op`, `kind`,
`kid`, `kmult`, `ints`, the rung's family arrays) and its decision variables (`pick`,
`used`, `rank`, `inner`, `bmem`, the position predicates). Integers are not order-encoded
here. The reported cost is the `_objective` of the re-solve with the term fixed, and the
solver's bound is printed as `; solver lower bound B`.


## References

- **[JR26]** Christopher Johannsen and Kristin Y. Rozier, "Shrinking Mission-time LTL
  Runtime Monitors with Equality Saturation", FMCAD 2026. Artifact: Zenodo,
  `10.5281/zenodo.21521555` (CC BY 4.0). The specifications are fetched from the
  artifact for the tests that use them and are not stored in this repository.

---
[← Ch 10: Literal Model](10-literal-model.md) · [Table of Contents](00-table-of-contents.md) · [Ch 12: Anti-Unification →](12-anti-unification.md)
