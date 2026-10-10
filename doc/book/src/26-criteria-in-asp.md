# Criteria in ASP

An `:asp` cost model is a file of clingo rules: a criterion, stated in
answer-set programming over facts that describe the e-graph. This chapter shows how
to write one, lists every predicate Semper defines, and names the pitfalls of
grounding. Every example runs from `doc/book/examples/cost-models/` and needs
clingo on the `PATH`.

## How Semper runs a criterion

`(extract t :cost m :solver (asp "clingo"))` runs four steps:

1. Semper writes the part of the e-graph reachable from `t` as facts, and the
   chosen rung as rules whose answer sets are the candidate terms.
2. It appends the criterion file and runs clingo on the whole program. Each
   answer set is one term, and clingo minimizes the criterion's `#minimize`
   statements.
3. It decodes the best answer set into a term.
4. It runs clingo a second time with that term fixed, and reports the criterion's
   value on it ([The reported cost](24-extraction-under-cost-models.md#the-reported-cost)).

The program itself excludes cyclic terms, so no exclusion loop runs, and the first
line of the output reports 0 solves and 0 cycle exclusions. An ASP model runs only
with an `(asp ...)` solver; any other solver is a sort error.

## A first criterion

The criterion of the first example of [Chapter 24](24-extraction-under-cost-models.md#a-first-extraction-under-a-cost-model),
in ASP:

```prolog
{{#include ../examples/cost-models/26-first.lp:criterion}}
```

`node(N,C,Op)` is a fact: node `N` belongs to class `C` and has operator `Op`, a
string. `pick(N)` holds in an answer set when the term takes node `N` for its
class. The `#minimize` statement pays `P` once for each picked node, so a node
shared by two parents is paid once.

{{#include ../examples/cost-models/26-first.egg:first}}

```text
{{#include ../examples/cost-models/26-first.out}}
```

The cost is 4, as the Roto script gives. The second line lists clingo's
optimization values, one per priority, most important first; this criterion has
one.

## The facts Semper writes

For the program above, at the selection rung, Semper writes these facts before its
rules and the criterion:

```prolog
{{#include ../examples/cost-models/26-first-dump.lp:facts}}
```

Classes and nodes keep the numbers of Semper's extraction graph, which are stable
from run to run but not consecutive within a class. Class 3 has two candidates:
node 1, `Add`, and node 2, `Twice`. `Add` has two positional children, both class
2, so `kid` lists both positions, while `operand` and `leaf` list the class once,
with `mult(1,2,2)`. The predicates, for the reachable classes and their candidates:

| predicate | meaning |
| --- | --- |
| `class(C)`, `root(C)` | a class; the root |
| `node(N,C,Op)` | node `N` of class `C` with operator `Op`, a string |
| `first(C,N)` | `N` is `C`'s first candidate |
| `kind(N,K)` | `K` is `plain`, `comm`, `seq`, `seq_left`, `seq_right`, `mset`, or `set` |
| `kid(N,I,K)` | child `I` of `N`, from 0, is class `K`; a multiset or set node's children are its distinct operands |
| `operand(N,K)` | `K` is a distinct child of `N` |
| `mult(N,K,M)` | operand `K` of `N` occurs `M` times: its stored count under an AC operator, its number of positions otherwise |
| `int(N,J,V)`, `str(N,J,S)` | integer and string payload `J` of `N`, from 0 |
| `leaf(N,P,K)` | leaf `P` of `N`'s tree, from 0, is class `K`: the positions of a sequence or fold, the distinct operands of any other node |

The payload follows the rule of the Roto binding: a child of a value sort, such as
an interval, becomes integers and strings of its parent
([Script API reference](25-cost-functions-in-roto.md#the-e-graph)). So
`(Global (Interval 0 9) p)` has `int(N,0,0)` and `int(N,1,9)`.

## The choice atoms

The rules make each candidate term one answer set. A criterion reads its atoms:

| predicate | holds when |
| --- | --- |
| `used(C)` | class `C` is in the term |
| `pick(N)` | node `N` is its class's choice |
| `inner(N,B)` | block `B`, an internal node of `N`'s tree, exists |
| `bmem(N,G,P)` | leaf `P` lies under `G`, a block or `root` |
| `under(N,G,K)` | class `K` lies under `G` |
| `parent(N,X,G)` | `G` is the innermost block around `X`, which is `leaf(P)` or a block |
| `depth(N,P,D)` | leaf `P` is at depth `D`, 1 directly under the root |
| `pos(N,G,X,Q)` | at `orders`, child `X` of `G` has position `Q`, from 0 (AC only) |

Tree atoms exist only for picked nodes. `bmem(N,root,P)` and `depth(N,P,D)` hold
for every leaf of every picked node, at every rung. `inner` holds only for a
bracketed node with 3 to 16 leaves (8 at `orders` for an AC node) at a tree rung,
and for a fold at every rung, whose blocks are its prefixes or suffixes.

A block is `blk(I,J)` for a sequence or fold, the leaves at positions `I` to `J`.
For an AC node it is `blk(R,S)`, a block of size `S` whose least leaf is `R`;
`bmem` says which other leaves it holds. For an AC node of four operands at
`binary`, the facts include:

```prolog
cand(1,blk(0,2)). least(1,blk(0,2),0). size(1,blk(0,2),2).
```

## Names a criterion must not define

The facts and rules above also define `ac`, `arity`, `binary`, `cand`, `chains`,
`child`, `closer`, `closerb`, `fixed`, `least`, `meet`, `ok`, `ordered`, `out`,
`size`, `span`, `sub`, and `taken`. The second solve, with the term fixed, adds
`free`, `held_inner`, `held_bmem`, and `held_pos`. A criterion must not define any
of these, nor any predicate of the two tables above. Clingo accepts a rule that
adds atoms to one of them without a warning, and the answer sets may then no
longer be the candidate terms. Use names of your own for every derived predicate.

## Trees

The depth cost of [Chapter 25](25-cost-functions-in-roto.md#bracketed-nodes), the
depth of the deepest leaf of any picked node, reads `depth/3`:

```prolog
{{#include ../examples/cost-models/26-depth.lp:criterion}}
```

The `; 0` element makes the maximum 0 when no leaf exists.

{{#include ../examples/cost-models/26-depth.egg:depth}}

```text
{{#include ../examples/cost-models/26-depth.out}}
```

The costs are those of the Roto script: 1, 1, and 2.

## Several objectives

A file may state several `#minimize` statements at different priorities; a higher
priority is more important. This criterion counts the classes of the term first,
and among the terms with the fewest, the `Add` nodes:

```prolog
{{#include ../examples/cost-models/26-priorities.lp:criterion}}
```

{{#include ../examples/cost-models/26-priorities.egg:priorities}}

```text
{{#include ../examples/cost-models/26-priorities.out}}
```

Both terms use 4 classes, and the second priority prefers `Twice`, with no `Add`.
The extraction prints `; solver objective [v1, v2, ...] (most important first)`,
clingo's values in priority order. The reported cost is the first value, here 4.
A file with no `#minimize` statement reports 0.

## Grounding

Clingo grounds the program, instantiating every rule over every value, before it
chooses anything. Three habits keep grounding finite and small.

- **Bound every recursive attribute.** A rule such as
  `wpd(C,O+M) :- pick(N), ..., M = #max { A,K : operand(N,K), wpd(K,A) }` grounds
  without end around a cycle of the e-graph, which no term can take. On an
  acyclic term the value is at most the sum of the offsets. State that bound,
  `utop(S) :- S = #sum { V,N : ub(N,V) }.`, and add `utop(S), O+M <= S` to the
  rule.
- **Aggregate first, subtract after.** An aggregate over siblings in a rule that
  also binds the class's own value is grounded once per value of the class's own
  value. Take the maximum in its own rule, `latest(C,X) :- ..., X = #max { A : sibw(C,A) }.`,
  and subtract in the next: `queue(C,X-B) :- bpd(C,B), latest(C,X), X > B.`
- **Derive a default from facts only.** `lat(N,0) :- node(N,_,_), not haslat(N).`
  with `haslat(N) :- lat(N,_).` has no stable model. Test the explicit facts
  instead, as `has_operand(N) :- operand(N,_).` does below.

The MLTL monitor memory follows all three:

```prolog
{{#include ../examples/cost-models/memory.lp:criterion}}
```

`(V+|V|)/2` is `max(V, 0)`. The criterion charges 1 for the specification, 1 per
counted class, each class's queue, and the same for each internal node of a
rendered tree.

{{#include ../examples/cost-models/26-memory.egg:memory}}

```text
{{#include ../examples/cost-models/26-memory.out}}
```

The costs, 39 at `selection` and 37 at `splits`, are those of the Roto script in
[Chapter 24](24-extraction-under-cost-models.md#the-ladder-of-rungs).

## Solver options and inspection

`(asp "PROG" "ARG" ...)` runs `PROG` with `--outf=2 --quiet=1`, then the given
arguments, then the path of the program. `PROG` is clingo, or any solver that
prints clingo's JSON output. Semper sets no time limit; pass clingo's own, as
`(asp "clingo" "--time-limit=60")`. When clingo stops before it proves its
optimum, the status is `bounded`.

`EXTRACT_API_KEEP_LP=dir` keeps every program clingo is given in `dir`, as
`call000.lp`, `call001.lp`, and so on: two per extraction, the search and the
solve with the term fixed. The directory must exist, and the numbering continues
from the number of files already in it. The kept program is the way
to see the facts of a larger e-graph.

Every integer Semper writes into the facts, a payload integer or a multiplicity,
must be one of clingo's 32-bit integers, and one outside is refused before clingo
runs ([Number ranges](28-solvers-certificates-and-export.md#number-ranges)). The
values the criterion computes, such as a `#sum`, are clingo's arithmetic. Semper
does not check them. **If you write cost functions that can overflow the
solver's internal number representation, you are on your own.**

`egraph/tests/mltl/costs/` holds the three MLTL costs in ASP. The
[lp.rs source](https://github.com/yaspar-org/semi-persistent/blob/main/egraph/src/extraction/lp.rs)
holds the rules Semper writes.
