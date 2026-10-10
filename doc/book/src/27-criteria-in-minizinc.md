# Criteria in MiniZinc

A `:minizinc` cost model is a MiniZinc file: a criterion over arrays and variables
that describe the e-graph. This chapter shows how to write one, lists every name
Semper defines, and compares the solvers. Every example runs from
`doc/book/examples/cost-models/` and needs `minizinc` on the `PATH`.

## How Semper runs a criterion

`(extract t :cost m :solver (minizinc "cp-sat"))` runs four steps:

1. Semper numbers the classes reachable from `t` `1..C` and their candidates
   `1..N`. It writes the e-graph as data, and the chosen rung as variables and
   constraints whose solutions are the candidate terms.
2. It appends the criterion file and runs MiniZinc with the named solver.
   Integers stay integer variables: nothing is order-encoded before the solver
   sees them.
3. It decodes the last solution into a term.
4. It solves a second time with that term fixed, and reports the objective on it
   ([The reported cost](24-extraction-under-cost-models.md#the-reported-cost)).

Every auxiliary variable is determined by the term, so each term is one solution.
The model itself excludes cyclic terms through `rank`, so the first line of the
output reports 0 solves and 0 cycle exclusions. A MiniZinc model runs only with a
`(minizinc ...)` solver, and a `(minizinc ...)` solver only with a MiniZinc model;
any other pairing is a sort error.

## A first criterion

The criterion of the first example of [Chapter 24](24-extraction-under-cost-models.md#a-first-extraction-under-a-cost-model),
in MiniZinc:

```text
{{#include ../examples/cost-models/27-first.mzn:criterion}}
```

`op[n]` is node `n`'s operator, a string, and `pick[n]` is the variable that is
true when the term takes node `n` for its class. The file declares its own names,
here `price` and `cost`, and ends with one `solve minimize` item.

{{#include ../examples/cost-models/27-first.egg:first}}

```text
{{#include ../examples/cost-models/27-first.out}}
```

The cost is 4, as in Roto and in ASP. The second line is the solver's lower bound
on the objective. On a run stopped by a time limit, the bound tells how far the
reported term can be from the optimum.

## The data Semper writes

For the program above, at the selection rung, Semper writes this data before its
variables, its constraints, and the criterion:

```text
{{#include ../examples/cost-models/27-first-dump.mzn:data}}
```

Node 4, `Add`, has two children, both class 3: `kid` and `kmult` list both
positions, and `kids` holds the class once. The names, with `n` a node, `c` a
class, and `b` a block:

| name | meaning |
| --- | --- |
| `C`, `N` | the numbers of classes and candidates |
| `class_id[c]`, `node_id[n]` | the e-graph's numbers, as in the ASP facts |
| `ROOT` | the root class |
| `cls[n]`, `op[n]` | node `n`'s class and operator (a string) |
| `kind[n]` | `PLAIN`, `COMM`, `SEQ`, `SEQ_LEFT`, `SEQ_RIGHT`, `MSET`, or `SET`, integer constants |
| `kids[n]` | the set of `n`'s distinct operand classes |
| `nkid[n]`, `kid[n, i]` | the number of children, and child `i`, in order, 0-padded; a multiset or set node's children are its distinct operands |
| `kmult[n, i]` | child `i`'s multiplicity: its stored count under an AC operator, 1 otherwise |
| `mult(n, k)` | a function: the multiplicity of class `k` among `n`'s children, summed over its positions |
| `nint[n]`, `ints[n, j]` | the integer payload, from `j` = 1 |
| `first[c]` | class `c`'s first candidate |
| `nleaf[n]`, `leaf[n, p]` | the leaves of `n`'s tree: the positions of a sequence or fold, the distinct operands of any other node |
| `MAXK`, `MAXL`, `MAXJ` | the widths of `kid`, `leaf`, and `ints` |
| `family[n]` | `n`'s trees: 0 none, 1 chains, 2 trees, 3 binary trees, 4 ordered trees, 5 a fold |
| `B`, `bnode[b]` | the number of possible blocks, and block `b`'s node |
| `interval[b]`, `blo[b]`, `bhi[b]` | the block is the interval `blo..bhi` of a sequence or fold, or else an AC block of least leaf `blo` and size `bhi` |

The payload is integers only: unlike the ASP facts' `str`, no string payload is
written.

## The variables

| name | meaning |
| --- | --- |
| `used[c]`, `pick[n]` | the class is in the term; the node is its class's choice |
| `rank[c]` | the term's height at `c`, 0 when unused: the chosen term is acyclic |
| `inner[b]` | block `b` exists |
| `bmem[b, p]` | leaf `p` lies under block `b` |
| `parent_leaf[n, p]`, `parent_blk[b]` | the innermost block around a leaf or a block, 0 for the root |
| `depth[n, p]` | leaf `p`'s depth, 1 directly under the root |
| `pos_leaf[n, p]`, `pos_blk[b]` | at `orders`, a child's position in its block, from 0 (AC only) |

Blocks exist only for a bracketed node with 3 to 16 leaves (8 at `orders` for an
AC node) at a tree rung, and for a fold at every rung. `depth[n, p]` is defined
for every node `n` and every `p` in `1..MAXL`; it is 1 for every leaf of a node
with no blocks.

## Names a criterion must not redefine

The dump also defines the function `children` and the predicates `meet` and
`within`. A criterion must not redefine them, nor declare any name of the two
tables above; MiniZinc then stops with an error, such as an ambiguous call for a
second `meet`. A parameter-only
predicate that an `int` function uses is declared with `test`, not `predicate`, as
`bounded` is in [A larger criterion](#a-larger-criterion).

## Trees

The depth cost of [Chapter 25](25-cost-functions-in-roto.md#bracketed-nodes) in
MiniZinc:

```text
{{#include ../examples/cost-models/27-depth.mzn:criterion}}
```

{{#include ../examples/cost-models/27-depth.egg:depth}}

```text
{{#include ../examples/cost-models/27-depth.out}}
```

The costs are 1, 1, and 2, as in Roto and in ASP. At `binary` the term differs:
CP-SAT returns `(And (And a c) (And b d))`, where the internal solver and clingo
return `(And (And a b) (And c d))`. Both cost 2. Among terms of equal cost, each
solver returns the one it finds, and the reported cost is the same.

## A larger criterion

The MLTL monitor memory in MiniZinc:

```text
{{#include ../examples/cost-models/memory.mzn:criterion}}
```

Each attribute is an array of variables with an explicit domain, `0..TOP`, where
`TOP` bounds every delay of an acyclic term. A constraint under `pick[n] -> ...`
defines a node's value only where the term takes it.

{{#include ../examples/cost-models/27-memory.egg:memory}}

```text
{{#include ../examples/cost-models/27-memory.out}}
```

## Choosing a solver

`(minizinc "SOLVER" "ARG" ...)` runs
`minizinc --solver SOLVER ARG ... --output-mode json --output-objective -s -i FILE`.
`SOLVER` is any name `minizinc --solvers` lists, such as `cp-sat`, `chuffed`,
`gecode`, `highs`, or `coin-bc`. Semper sets no time limit; pass MiniZinc's own,
in milliseconds, as an argument:

{{#include ../examples/cost-models/27-solvers.egg:solvers}}

```text
{{#include ../examples/cost-models/27-solvers.out}}
```

Every solver proves 37 at `splits`. HiGHS, COIN-BC, and CP-SAT report a lower
bound; Chuffed and Gecode do not, and print no bound line. When a solve stops
before it proves its optimum, the status is `bounded`, and the bound, when
printed, limits the distance to the optimum.

Each solver reads integers in its own range, and Semper checks the integers it
writes, the payload and the multiplicities, against the range of the named
solver: 32 bits for Chuffed and Gecode, exact to 2^53 for the MIP solvers, 64 bits
for CP-SAT and any other. The values the criterion computes are the solver's
arithmetic, which Semper does not check. **If you write cost functions that can
overflow the solver's internal number representation, you are on your own.**
CP-SAT, whose 64-bit range the MiniZinc compiler also checks, is the recommended
solver for criteria whose values can grow
([Number ranges](28-solvers-certificates-and-export.md#number-ranges)).

`EXTRACT_API_KEEP_MZN=dir` keeps every model MiniZinc is given in `dir`, as
`call000.mzn`, `call001.mzn`, and so on: two per extraction. The directory must
exist. `egraph/tests/mltl/costs/` holds the three MLTL costs in MiniZinc. The
[mzn.rs source](https://github.com/yaspar-org/semi-persistent/blob/main/egraph/src/extraction/mzn.rs)
holds the constraints Semper writes.
