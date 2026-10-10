# Cost functions in Roto

A `:script` cost model is a file in [Roto](https://github.com/NLnetLabs/roto), a
statically typed scripting language that compiles to native code. Semper compiles
the script against its own binding when the program is checked. This chapter
builds scripts from a first one to the full API; every example runs from
`doc/book/examples/cost-models/`.

## Data and decisions

A script defines `fn cost(g: Graph)`. It does not compute a number. It runs once,
while the problem is built, and never sees a solution. What it reads falls in two
groups, with distinct types.

- **The e-graph is data.** Classes, nodes, operators, children, multiplicities,
  and payloads are fixed before the script runs. The script reads them as
  `String`, `u64`, `i64`, `bool`, and lists, and may branch on them with `if`.
- **The solver's decisions are solver values.** Which node each class takes,
  whether an internal node exists, and an operand's depth are unknown to the
  script. It holds them as `Bool` and integer values, combines them, and charges
  under them. It cannot test them with `if`.

What the script builds is a formula: definitions, constraints, and one objective,
the sum of its charges. The library adds the rung's constraints, encodes the
whole for the chosen solver, and evaluates the objective on the term the solver
returns ([The reported cost](24-extraction-under-cost-models.md#the-reported-cost)).

## A first script

The script of [Chapter 24](24-extraction-under-cost-models.md#a-first-extraction-under-a-cost-model)
charges each chosen node once:

```rust
{{#include ../examples/cost-models/24-first.roto:cost}}
```

`g.nodes()` lists every candidate node of every class reachable from the root.
`n.is("Twice")` reads the operator, a fact the script branches on. `n.chosen()` is
a solver value: the condition that the node's class is in the term and takes this
node. `charge_if(3)` adds 3 to the objective where that condition holds. A node
shared by two parents is chosen once, so it is charged once.

## Reading the e-graph

A cost that depends on context reads more of the e-graph. In this model a `Delay`
node needs a buffer of its operand, as wide as its integer payload. A class shared
by several `Delay` parents is buffered once, over the widest window a chosen
parent needs. A `Hold` keeps its operand without a buffer, at a price of 4:

```rust
{{#include ../examples/cost-models/25-window.roto:cost}}
```

`c.parents()` lists the nodes that have `c` as a child, each as a `Use` whose
`parent()` is the node. `n.int(0)` is the first integer of the node's payload, or
`None` past the end. `g.constant(w)` is the integer `w` as a solver value, and
`.over()` marks it as a value the cost may overstate ([Polarity](#polarity)).
`.when(b)` makes it a part that counts where `b` holds, and `g.max_over(parts)` is
the largest part that holds, 0 when none does. `charge()` adds that maximum to the
objective.

The program offers `(Delay 5 x)` and `(Hold x)` as equal terms, in two contexts:

{{#include ../examples/cost-models/25-window.egg:window}}

```text
{{#include ../examples/cost-models/25-window.out}}
```

In `shared`, a sibling already buffers `x` for 3, so `(Delay 5 x)` widens the
buffer by 2. The term keeps it, at a cost of 5. In `alone`, `x` has no other
buffer, so `(Delay 5 x)` would add 5 and `(Hold x)` adds 4: the term costs 4 plus 3
for `y`. The same node is chosen in one context and not in the other, which no
price per node can state.

The third model, `no-hold`, replaces the price of `Hold` by a requirement:

```rust
{{#include ../examples/cost-models/25-no-hold.roto:cost}}
```

`n.chosen().not()` is the condition that the node is not chosen, and `require()`
makes it hold in every solution. The term of `alone` must then delay `x`, at
5 + 3 = 8.

## Recursive attributes

A cost over the whole chosen term, such as the latency of its critical path, is a
recursive attribute. `g.node_values()` is a table of one `u64` per node, 0 where
unset. `g.attribute_max(offsets)` defines, for each class, the chosen node's offset
plus the largest attribute among its operands, or the offset alone for a leaf:

```rust
{{#include ../examples/cost-models/25-latency.roto:cost}}
```

`ready.of(c)` is class `c`'s attribute, an over-estimate, and the script charges
the root's. The rewrite turns each doubling into an addition:

{{#include ../examples/cost-models/25-latency.egg:latency}}

```text
{{#include ../examples/cost-models/25-latency.out}}
```

The written term takes 3 + 3 + 1 = 7 cycles; the extracted one takes 3, one per
`Add`. `g.attribute_min(offsets)` uses the smallest operand instead, and gives an
under-estimate. `g.attribute_max_under` and `g.attribute_min_over` give the same
attributes with the opposite polarity.

## Polarity

Costs are built from order-encoded integers: a value set `v0 < v1 < ...` with one
literal per value meaning "at least `vj`". Values are signed. A solver can set
some of these literals more freely than the term requires, so each integer has one
of three types, which record how the encoded value relates to the value on the
term.

| type | the encoded value is | used for |
| --- | --- | --- |
| `Exact` | equal to the true value | constants and free integers |
| `Over` | at least the true value | what is minimized |
| `Under` | at most the true value | what is subtracted |

The operations are typed so that every combination is sound:

- `x.when(b)` makes a part that counts where `b` holds.
  `g.max_over(parts)` over over-estimates is an over-estimate, and
  `g.min_under(parts)` over under-estimates is an under-estimate. `g.max_under`
  and `g.min_over` are their duals.
- `a.minus(b)` is `a - b`, unclamped. On an `Over` it accepts only an `Under` and
  gives an `Over`; on an `Under` it accepts only an `Over` and gives an `Under`.
  `max(a - b, 0)` is `a.minus(b).clamp(0)`.
- `x.neg()` exchanges `Over` and `Under`.
- `x.charge()` accepts an `Exact` or an `Over`, never an `Under`.
- A threshold of an `Over` or `Under` is one-sided and has its own type.
  `x.at_least(v)` of an `Over` is a `BoolOver`, which may hold where the true
  value is below `v`. `charge_if` accepts a `Bool` or a `BoolOver`, and `require`
  a `Bool` or a `BoolUnder`.

Subtracting an over-estimate would let the solver report a cost below the true
one. The types make that a compile error, reported when the program is checked,
with the script's line:

```rust
{{#include ../examples/cost-models/25-polarity.roto:cost}}
```

{{#include ../examples/cost-models/25-polarity.egg:polarity}}

```text
{{#include ../examples/cost-models/25-polarity.out}}
```

(The listing is the message with its colour codes removed.) The error does not
depend on the branch being taken: a mistake in a rarely reached case is rejected
like any other.

The MLTL monitor memory of [Chapter 24](24-extraction-under-cost-models.md#the-ladder-of-rungs)
needs both polarities. A producer that finishes early waits for its latest
sibling, so its queue is the latest sibling's worst-case delay (`wpd`, an
over-estimate) less its own best-case delay (`bpd`, an under-estimate):

```rust
{{#include ../examples/cost-models/memory.roto:cost}}
```

`u.siblings()` lists the parent's other operands, each with `present()`, the
condition that the parent is chosen and, where the rung renders a tree, that the
operand is in the same block. The inner loop charges the same queue for every
internal node of a rendered tree ([Bracketed nodes](#bracketed-nodes)).

## Bracketed nodes

At the tree rungs, a bracketed node's tree is a decision. Two parts of the API
read it:

- `n.inner_nodes()` lists the internal nodes a rendering of `n` may contain, each
  with `exists()`, `members()` (the operands that may lie under it), and
  `siblings()`. A fold's internal nodes, its prefixes or suffixes, are listed at
  every rung, with `exists()` true whenever the fold is chosen. For an AC node or
  an `:assoc` sequence the list is empty at `selection`, so the same script runs
  at every rung.
- `k.depth()` is a child's depth in its node's tree, 1 directly under the node,
  where the rung decides the tree, and `None` elsewhere. `k.position(d)` is its
  position within its block at depth `d`, at the `orders` rung only, for `d` from 1 (the
  node itself) to the tree's depth, and `None` for any other `d`.

This script charges the depth of the deepest operand of any chosen node:

```rust
{{#include ../examples/cost-models/25-depth.roto:cost}}
```

{{#include ../examples/cost-models/25-depth.egg:depth}}

```text
{{#include ../examples/cost-models/25-depth.out}}
```

At `selection` and `levels` the flat node keeps every operand at depth 1: a chain
of blocks only deepens some of them. `binary` requires two operands per group, and
the shallowest binary tree over four operands has depth 2.
[Chapter 26](26-criteria-in-asp.md#trees) and
[Chapter 27](27-criteria-in-minizinc.md#trees) state the same cost in ASP and in
MiniZinc.

## Pseudo-Boolean terms

A pseudo-Boolean term is a weighted sum of literals and a constant. It is linear
and needs no encoding until it is compared or sorted. `b.times(k)` is `k` where
`b` holds, `g.count(bs)` the number of `bs` that hold, `g.pb_const(c)` a constant,
and `x.linear()` an integer's linear form. `t.plus(u)`, `t.minus(u)`,
`t.times(c)`, and `t.plus_const(k)` combine terms. `t.charge()` adds a term to the
objective with no integer built. `t.at_least(k)` and `t.at_most(k)` give its
threshold literals, and `t.sorted()` turns it into an order-encoded integer.

Terms carry a polarity as integers do: `Pb`, `PbOver`, and `PbUnder`.
`BoolOver.times` and `Over.linear` give a `PbOver`; `minus` takes a term of the
opposite polarity; `charge` accepts a `Pb` or a `PbOver`.

## Exact integers

Roto's own `i64` and `u64` arithmetic is not checked: `+`, `-`, and `*` wrap
silently, and `/` and `%` by zero abort the process. A cost computed with them
could be wrong without an error, so Semper refuses a cost script that uses any of
these operators, or their compound forms `+=`, `-=`, `*=`, `/=`, `%=`. The script
is refused when the program is checked, before anything runs, with the operator's
line and column. A `-` that starts a negative literal, as in `g.int([-3, 3])`, is
allowed, and so are comparisons, which cannot wrap:

```rust
{{#include ../examples/cost-models/25-wrap.roto:cost}}
```

{{#include ../examples/cost-models/25-wrap.egg:wrap}}

```text
{{#include ../examples/cost-models/25-wrap.out}}
```

All arithmetic in a cost script therefore goes through exact methods. For any
value that can grow, such as
a multiplicity times a weight, a sum over a large e-graph, or an interval bound,
compute with `IBig` (signed) or `UBig` (unsigned) instead. Both are exact at any
size, and a script may branch on their comparisons. This script charges each node
1 plus 4 per operand copy, and a fixed 10^20:

```rust
{{#include ../examples/cost-models/25-exact.roto:cost}}
```

{{#include ../examples/cost-models/25-exact.egg:exact}}

```text
{{#include ../examples/cost-models/25-exact.out}}
```

`(V "a"):3000000000` is one operand with a multiplicity of 3,000,000,000.
`k.count()` reads it as a `UBig`, and the cost, 10^20 + 12,000,000,007, is
reported exactly. The operations:

| operation | |
| --- | --- |
| make | `g.ibig(v)` from an `i64`, `g.ubig(v)` from a `u64`, `g.ibig_str("…")`, `g.ubig_str("…")` from a decimal string (the way to write a constant past `i64`) |
| read from the e-graph | `k.count()` (a child's multiplicity, `UBig`), `n.nums()`, `n.num(j)` (the payload integers, `IBig`, an `IBig` literal past `i64` included) |
| arithmetic | `a.plus(b)`, `a.minus(b)`, `a.times(b)`, `a.div(b)` (truncated toward zero), `a.rem(b)` (with the sign of `a`), `a.max(b)`, `a.min(b)`; on `IBig`, `a.neg()` and `a.abs()` (a `UBig`) |
| compare | `a.lt(b)`, `a.le(b)`, `a.gt(b)`, `a.ge(b)`, `a.eq(b)`: ordinary `bool`s |
| convert | `a.to_ubig()`, `a.to_i64()` (`None` past `i64`), `a.to_string()` on `IBig`; `a.to_ibig()`, `a.to_u64()` (`None` past `u64`), `a.to_string()` on `UBig` |

Division by zero, a `UBig` result below zero, and a malformed decimal string are
build errors that name the operation. A big variant takes the place of each 64-bit
constant:

| 64-bit call | exact call |
| --- | --- |
| `g.constant(v)`, `g.int(values)`, `g.pb_const(c)`, `g.charge_const(w)` | `g.constant_big`, `g.int_big`, `g.pb_const_big`, `g.charge_const_big` (`IBig`) |
| `g.at_most(bs, k)`, `g.at_least(bs, k)` | `g.at_most_big`, `g.at_least_big` (`UBig`) |
| `x.at_least(v)`, `x.at_most(v)`, `x.plus_const(k)`, `x.clamp(lo)`, `x.values()` | `x.at_least_big`, `x.at_most_big`, `x.plus_const_big`, `x.clamp_big` (`IBig`), `x.values_big()` |
| `x.scale(c)` | `x.scale_big` (`UBig`, at least 1) |
| `b.times(k)`, `b.charge_if(w)` | `b.times_big`, `b.charge_if_big` (`UBig`) |
| `t.times(c)`, `t.plus_const(k)`, `t.at_least(k)`, `t.at_most(k)` | `t.times_big` (`UBig`), `t.plus_const_big`, `t.at_least_big`, `t.at_most_big` (`IBig`) |
| `v.set(n, w)`, `v.get(n)` | `v.set_big(n, w)`, `v.get_big(n)` (`UBig`) |

A 64-bit read of a value it cannot hold, such as `x.values()`, `n.int(j)`, or
`v.get(n)` on a value past `i64` or `u64`, is an error that names the exact call
to use.

Every value a script hands to the library, and every value the library computes
(integers, terms, the objective, and the reported cost), is exact. A value outside
the cap `--cost-bits` sets, if one is set, is an error. So is a value outside the
range of the solver the problem goes to
([Number ranges](28-solvers-certificates-and-export.md#number-ranges)).

## Costs written in Rust

`(cost-model NAME :rust "id")` names a cost compiled into Semper. Three are
registered: `mltl-memory`, `pipeline-registers`, and `monitor-history`, the same
costs as the scripts in `egraph/tests/mltl/costs/`. A Rust cost runs on the
same solvers as a script and reports its cost the same way:

{{#include ../examples/cost-models/25-rust.egg:rust}}

```text
{{#include ../examples/cost-models/25-rust.out}}
```

Another name is a sort error that lists the three.

## Script API reference

Every value the API hands out belongs to the part of the e-graph reachable from
the root through candidates, the members that are not subsumed.

### The e-graph

| type | methods |
| --- | --- |
| `Graph` | `classes()` (ascending), `root()`, `nodes()` (every candidate of every class), `rung()` (the rung's name) |
| `Class` | `nodes()` (its candidates), `parents()` (a `Use` per node that has it as a child), `chosen()`, `id()`, `is_root()` |
| `Node` | `op()`, `is(op)`, `kind()`, `children()`, `class()`, `ints()`, `int(j)`, `nat(j)` (clamped below at 0), `nums()`, `num(j)` (exact `IBig`s), `strings()`, `id()`, `chosen()`, `inner_nodes()` |
| `Child` | `class()`, `multiplicity()`, `count()` (exact `UBig`), `index()`, `depth()`, `position(d)` |
| `Use` | `parent()`, `positions()` (where the class occurs among the parent's children), `siblings()` |
| `Sibling`, `Member` | `class()`, `present()` |
| `Inner` | `exists()`, `members()`, `siblings()`, `index()`, `node()` |
| `Kind` | `name()`, `is_plain()`, `is_comm()`, `is_seq()`, `is_mset()`, `is_set()`, `is_flat()`, `is_bracketed()` |

`n.children()` is one `Child` per position, except for a multiset or set node,
where it is one per distinct operand with its multiplicity:

| `n.kind()` | the operator is | `name()` | `n.children()` |
| --- | --- | --- | --- |
| `is_plain()` | declared with positional arguments | `plain` | one per position |
| `is_comm()` | `:comm` | `comm` | its two arguments |
| `is_seq()` | `:assoc`, `:assoc-left`, or `:assoc-right` | `seq`, `seq-left`, `seq-right` | in order |
| `is_mset()` | `:assoc-comm` | `mset` | its distinct operands, each with its multiplicity |
| `is_set()` | `:assoc-comm-idem` | `set` | its distinct operands |

`is_flat()` holds for a multiset or set node. `is_bracketed()` holds for a node
whose tree the rung decides: a flat node, or an `:assoc` sequence.

A child whose sort is a value sort is not a child the script sees: it becomes
payload of its parent. A value sort is one every node of which has only
value-sort children, less the root's sort; literal sorts are value sorts, and so
is `IntervalSort` in the MLTL examples. Its scalars are collected depth first and
left to right: an integer literal goes to `ints`, any other literal to `strings`.
So `(Global (Interval 0 9) p)` is a node with `ints` `[0, 9]` and one child, `p`.
A Boolean literal arrives as the string `"true"` or `"false"`.

### Solver values

| type | is | from |
| --- | --- | --- |
| `Bool` | a conjunction of literals | `c.chosen()`, `n.chosen()`, `s.present()`, `m.present()`, `t.exists()`, thresholds of an `Exact` or a `Pb` |
| `BoolOver`, `BoolUnder` | a condition that may hold where it is false (`Over`) or fail where it is true (`Under`) | the thresholds of `Over` and `Under` integers and terms |
| `Exact`, `Over`, `Under` | an order-encoded integer | `g.constant(v)`, `g.int(values)`, attributes, and the operations below |
| `OverPart`, `UnderPart` | an integer that counts under a condition | `x.when(b)` |
| `Pb`, `PbOver`, `PbUnder` | a weighted sum of literals and a constant | `b.times(k)`, `g.count(bs)`, `x.linear()` |

| group | operations |
| --- | --- |
| `Bool` | `g.bool(v)`, `a.and(b)`, `g.all(list)` (no new variable); `a.or(b)`, `a.not()`, `a.implies(b)`, `g.any(list)` (one defined literal); `b.over()`, `b.under()` widen to `BoolOver`, `BoolUnder`; on a `BoolOver` or `BoolUnder`, `and` and `or` keep the type and `not` exchanges it |
| `Exact` | `g.constant(v)`, `g.int(values)`, `g.int_scaled(values, s)`, `g.unary(n)` (over `0..n`); `x.plus(y)`, `x.minus(y)`, `x.neg()`, `x.scale(c)`, `x.clamp(lo)`, `x.plus_const(k)`; `x.values()`, `x.at_least(v)`, `x.at_most(v)`; `x.over()`, `x.under()` |
| `Over`, `Under` | `x.when(b)`; `g.max_over`, `g.min_over` (over `OverPart`s), `g.min_under`, `g.max_under` (over `UnderPart`s); `a.minus(b)` of opposite polarity; `a.plus(b)`, `a.plus_const(k)`, `a.scale(c)`, `a.clamp(lo)` keep the polarity; `x.neg()` exchanges it; `g.sum(list)` and `g.ite(b, x, y)` over `Over`s give an `Over` |
| attributes | `g.node_values()` filled with `v.set(n, w)` and read with `v.get(n)`; `g.attribute_max(v)`, `g.attribute_min_over(v)` give an `Over` per class, `g.attribute_min(v)`, `g.attribute_max_under(v)` an `Under`; `attr.of(c)` reads class `c`'s |
| `Pb` | `b.times(k)`, `g.count(bs)`, `g.pb_const(c)`, `x.linear()`; `t.plus(u)`, `t.minus(u)`, `t.neg()`, `t.times(c)`, `t.plus_const(k)`; `t.at_least(k)`, `t.at_most(k)`, `t.sorted()`; `t.over()`, `t.under()` |
| sinks | `b.require()` (`Bool`, `BoolUnder`), `g.at_most(bs, k)`, `g.at_least(bs, k)`, `x.charge()` (`Exact`, `Over`, `Pb`, `PbOver`), `b.charge_if(w)` (`Bool`, `BoolOver`), `g.charge_const(w)` |

`b.require()` makes `b` hold in every solution; `g.at_most(bs, k)` and
`g.at_least(bs, k)` bound the number of `bs` that hold. The objective is the sum of
every charge. An operation whose values leave a cap set by `--cost-bits` records
an error, and the extraction then fails with the errors in order instead of
solving. The
[design chapter](https://github.com/yaspar-org/semi-persistent/blob/main/egraph/doc/design/11-extraction.md#layers)
describes how the library encodes these values.
