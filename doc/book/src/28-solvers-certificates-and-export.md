# Solvers, certificates, and export

This chapter covers what surrounds an extraction: the solvers and their limits,
the number range of each solver, certificates, listing the terms of a cost band,
and the two JSON files Semper writes. It ends with the alternatives considered and
the limits. Examples run from `doc/book/examples/cost-models/`; those in its
`manual/` directory need RoundingSat or end in an error, so the book test does not
run them.

## Solvers

`:solver` chooses how the problem is solved. The default is `internal`.

| `:solver` | models | backend | cycles |
| --- | --- | --- | --- |
| `internal` | script, Rust | CNF, one incremental CaDiCaL descent, the objective bounded by a windowed generalized totalizer | a clause per cyclic solution, then resume |
| `dpw` | script, Rust | as `internal`, the objective bounded by rustsat's dynamic polynomial watchdog | as `internal` |
| `roundingsat` | script, Rust | the problem as OPB, solved by RoundingSat's cutting planes | added to the file, then restart |
| `(opb "prog" "arg" ...)` | script, Rust | any pseudo-Boolean solver reading OPB | added to the file, then restart |
| `(asp "clingo" "arg" ...)` | script, Rust, ASP | an answer-set program for clingo | excluded by the program's rules |
| `(minizinc "solver" "arg" ...)` | MiniZinc | MiniZinc with `cp-sat`, `chuffed`, `gecode`, `highs`, or `coin-bc` | excluded by `rank` |
| `greedy` | script, Rust | no solving: additive extraction, scored | none arise |

Cycles in the e-graph are excluded by Semper for every solver. An ASP model with a
solver other than `asp`, a MiniZinc model with a solver other than `minizinc`, and
a `minizinc` solver with any other model are sort errors naming the model
([The extract command](24-extraction-under-cost-models.md#the-extract-command)).

The internal solvers on the ladder program's problem:

{{#include ../examples/cost-models/28-solvers.egg:solvers}}

```text
{{#include ../examples/cost-models/28-solvers.out}}
```

`dpw` sums its weights in 64 bits. An objective whose weights total more is
refused with an error that names `internal` and `roundingsat`, which are exact.

`roundingsat` is looked up as `$ROUNDINGSAT`, then `~/.local/bin/roundingsat`,
then on the `PATH`, and run with `--print-sol=1 --verbosity=0`. `(opb "prog" ...)`
runs `prog` with the given arguments and the OPB file's path appended. The program
must print competition output: `s OPTIMUM FOUND` or `s UNSATISFIABLE`, and `v`
lines.

A script also runs on clingo, as its formula written as ASP:

{{#include ../examples/cost-models/28-asp-target.egg:asp-target}}

```text
{{#include ../examples/cost-models/28-asp-target.out}}
```

This backend is slower. On 64 of the MLTL specifications of Johannsen and Rozier (FMCAD 2026), clingo took 15
times longer than the internal solver on the median instance. That measurement
was recorded by a tool since removed from the repository, and the current tree
does not reproduce it.

### Limits on a solve

| solver | limit |
| --- | --- |
| `internal`, `dpw` | 100,000 SAT calls; no time limit |
| `roundingsat`, `(opb ...)` | no new call after 3,600 seconds, and at most 201 calls; a running call is not interrupted |
| `(asp ...)` | none from Semper; pass clingo's `--time-limit=N` |
| `(minizinc ...)` | none from Semper; pass `"--time-limit" "MS"` |
| `:band` | 100,000 SAT calls |

A limit that runs out after a term was found gives the status `bounded`. One that
runs out before gives the error `no term: Bounded`.

### Keeping the solver's input

Each variable names an existing directory, in which Semper keeps a copy of every
file it gives a solver, numbered `call000`, `call001`, and so on:

| variable | keeps |
| --- | --- |
| `EXTRACT_API_KEEP_OPB=dir` | each OPB file, as `callNNN.opb` |
| `EXTRACT_API_KEEP_ASP=dir` | each program of a script solved by clingo, as `callNNN.lp` |
| `EXTRACT_API_KEEP_LP=dir` | each program of an ASP model, as `callNNN.lp` |
| `EXTRACT_API_KEEP_MZN=dir` | each model of a MiniZinc model, as `callNNN.mzn` |

## Number ranges

Semper's own arithmetic on costs is exact: a script's `IBig` and `UBig`, a Rust
cost's integers, the terms, the objective, the totalizer that bounds it, and the
reported cost. Two ranges then decide whether a cost is computed correctly. The
first is an optional cap, which Semper enforces. The second is the range of the
solver, which Semper enforces on every number it writes for that solver.

**The cost width.** `--cost-bits big` (the default) sets no cap. `--cost-bits 32`
or `64` caps every integer of a script or Rust cost, and the reported cost of any
model, at that signed width. A value outside the cap is an error naming the
operation, never a wrapped value. This script charges 2^63:

```rust
{{#include ../examples/cost-models/manual/28-cost-bits.roto:cost}}
```

{{#include ../examples/cost-models/manual/28-cost-bits.egg:cost-bits}}

Run from `manual/` with no flag, it prints:

```text
{{#include ../examples/cost-models/manual/28-cost-bits.txt}}
```

With `--cost-bits 64`, it stops with:

```text
{{#include ../examples/cost-models/manual/28-cost-bits-64.txt}}
```

A Roto literal is still 64-bit, because Roto has no larger integer type. A larger
constant is written as `g.ibig_str("…")`
([Exact integers](25-cost-functions-in-roto.md#exact-integers)).

**The solver's range.** Each solver reads integers in its own representation, and
several read a value past it wrongly without reporting anything. Before a solver
runs, Semper checks every number it writes for that solver against the solver's
range, and refuses one outside it with an error naming the solver. The numbers
checked are the coefficients, bounds, and weights of an OPB file or an ASP
program, and the integers and multiplicities of the ASP and MiniZinc dumps. A
weight of 3,000,000,000 is exact on the internal solver and refused for clingo:

```rust
{{#include ../examples/cost-models/manual/28-solver-range.roto:cost}}
```

{{#include ../examples/cost-models/manual/28-solver-range.egg:solver-range}}

```text
{{#include ../examples/cost-models/manual/28-solver-range.txt}}
```

A payload integer past clingo's range, under an ASP model, is refused the same
way, and the message says what Semper does not check:

{{#include ../examples/cost-models/manual/28-dump-range.egg:dump-range}}

```text
{{#include ../examples/cost-models/manual/28-dump-range.txt}}
```

> **What Semper does not check.** ASP and MiniZinc criteria compute inside the
> solver. A criteria file that computes a value its solver cannot represent, such
> as a `#sum` past 2^31 in clingo, a product past 2^31 in Chuffed, or a sum past
> 2^53 in a MIP solver, can give a wrong optimum, and nothing reports it. **If you
> write cost functions that can overflow the solver's internal number
> representation, you are on your own.** Keep the values your criteria compute
> inside the range of the solver you run them on, or choose a solver whose range
> holds them.

What each solver does with a number past its range, measured on 2026-10-06 with
the inputs in
[`egraph/tests/data/solver_width/`](https://github.com/yaspar-org/semi-persistent/blob/main/egraph/tests/data/solver_width/README.md)
(the README names the solver versions):

| solver | integers it reads | past that range | Semper checks it as |
| --- | --- | --- | --- |
| `internal` (CaDiCaL, Semper's totalizer) | arbitrary precision: the totalizer runs on u64 weights when they fit, on exact ones otherwise | exact at 2^70 | unbounded |
| `dpw` (rustsat's watchdog) | 64-bit | refused | 64-bit total |
| `roundingsat` | arbitrary precision | exact at 2^70 and 2^100 | unbounded |
| `(opb "clasp")` | 32-bit | **wrong, no error**: a weight of 2^70 read as 0, a 2^100 constraint ignored | 32-bit |
| `(opb "...")`, another solver | not measured | not known | 64-bit |
| `(asp "clingo")` | 32-bit per value; sums of values in 64 bits | **wrong, no error**: a weight of 3,000,000,000 read as -1,294,967,296 | 32-bit per value |
| MiniZinc compiler | 64-bit | reports `integer overflow` | 64-bit |
| `cp-sat` | 64-bit | exact at 2^40 and 2^53 | 64-bit |
| `chuffed` | 32-bit | **wrong, no error**: chose a term costing 2^40 over one costing 5 | 32-bit |
| `gecode` | ±2,147,483,646 | reports `out of range` | 32-bit |
| `coin-bc` | doubles, exact to 2^53 | **wrong, no error**: cannot tell 2^53 + 1 from 2^53 | exact to 2^53 |
| `highs` | doubles, exact to 2^53 | reports `Unable to add linear constraint` | exact to 2^53 |
| `scip` | doubles, exact to 2^53 | right on the one test; computes in doubles | exact to 2^53 |

Semper recognizes an OPB solver by its program name: one containing `roundingsat`
is unbounded, one containing `clasp` or `clingo` is 32-bit. A MiniZinc solver
named `chuffed` or `gecode` is 32-bit; `coin`, `cbc`, `highs`, `scip`, `gurobi`,
`cplex`, `xpress`, or `mip` is exact to 2^53; any other is 64-bit.

**Recommended.** For costs that can grow large, state the cost in Rust or as a
script using `IBig` and `UBig`, and solve on `internal` or `roundingsat`, the two
solvers that take numbers of any size. For MiniZinc criteria use `cp-sat`, whose
64-bit range the MiniZinc compiler also checks. Use clasp, clingo, Chuffed, Gecode,
and the MIP solvers only when every value the criteria compute stays inside their
range.

## Certificates

`:proof "dir"` runs a proof-logging pseudo-Boolean solver with `--proof-log`,
RoundingSat's flag, and keeps each call's instance and proof in `dir`, as
`call000.opb` and `call000.pbp`, and so on. It prints the claim of the final call
and the command that checks it. `:proof` needs `:solver roundingsat` or
`(opb ...)`:

{{#include ../examples/cost-models/manual/28-certificate.egg:certificate}}

```text
{{#include ../examples/cost-models/manual/28-certificate.txt}}
```

VeriPB checks the first certificate:

```text
{{#include ../examples/cost-models/manual/28-veripb.txt}}
```

The bound is on the objective in the OPB file, which leaves out the cost's
constant part (here the specification wrapper's 1): the certified cost is 39, the
selection optimum, and 37 at `splits`. The claim is `Bounds { lower: L }` when the
final call found an optimum, and `Unsat { below: ... }` when it refuted a cheaper
term. The certificate covers the solver's reasoning on the final instance: no
model has a lower objective. That every acyclic term has a model whose objective
is its cost is a property of the encodings, established by Semper's tests rather
than by the certificate.

## Listing terms in a cost band

`:band lo hi` lists the terms whose cost lies in `[lo, hi]`, at most `:count n` of
them (default 10), instead of the cheapest one. Both bounds are added to the
objective before solving, and each term found is excluded by its rung literals,
so no term in the band is lost and none is listed twice. A band runs on the
internal solver, with a script or Rust model; any other `:solver` is a sort error.
The second command below asks for `splits` under a budget of 10 clauses, which
steps down:

{{#include ../examples/cost-models/28-band.egg:band}}

```text
{{#include ../examples/cost-models/28-band.out}}
```

The terms come in the order found, each with its cost. Standard error carries
`warning: rung splits estimated above the budget; extracting at selection`. With
the optimum proved, a band gives equivalent terms at a known gap above it:
benchmarks with known answers, variants for differential testing, and pairs of
suboptimal and optimal terms.

## Writing the term

`:file "f.json"` writes the extracted term as JSON. It has one entry per class of
the term, named `c` and the class's number in the extraction graph, with its
operator, its children's entries, and its payload. A multiset node also carries
`"mults"`, each child's count, parallel to `"children"`: a child of multiplicity k
is listed once. Under `:band`, each term goes to `f.json.0.json`,
`f.json.1.json`, and so on.

{{#include ../examples/cost-models/28-file.egg:file}}

```text
{{#include ../examples/cost-models/28-file.out}}
```

The first file, `28-file.json`:

```json
{{#include ../examples/cost-models/28-file.json}}
```

The second, `28-file-mults.json`, with the count of `(V "a")`:

```json
{{#include ../examples/cost-models/28-file-mults.json}}
```

## The exported e-graph

`(dump-egraph t :file "f.json")` writes the whole e-graph, marking `t`'s class as
the root, for a tool that extracts outside Semper. The format is egglog's
`--to-json`, plus a colour per class and the kind of each operator:

{{#include ../examples/cost-models/28-dump-egraph.egg:dump-egraph}}

```json
{{#include ../examples/cost-models/28-dump-egraph.json}}
```

Every name is a content colour: a hash of the class's structure, computed by
refining over the classes until the partition stops changing. A class is
`{sort}-{colour}` and a node `n{colour}-{sort}`. Nodes and classes are written in
name order, and an AC, ACI, or commutative node's children in name order too.
Two runs that build the same e-graph therefore write the same bytes, whatever
node ids they allocated: on the 1,172 MLTL specifications Johannsen and Rozier publish with their FMCAD 2026 paper ([Chapter 24](24-extraction-under-cost-models.md#when-the-cost-depends-on-a-grouping-the-e-graph-does-not-store)), naive and semi-naive
saturation write identical dumps. A child entry names one member of the child
class, the one whose name sorts first; a consumer reads that member's `eclass`. A
multiset child of multiplicity k is written once, with k in `"mults"`, parallel to
`"children"`, as `F` under `Plus` above (count 2). A congruent duplicate node is
omitted. `op_kinds` (`plain`, `comm`, `a`, `ac`, `aci`, or `lit`) tells a consumer
which operators' child order carries no meaning. The
[design chapter on extraction](https://github.com/yaspar-org/semi-persistent/blob/main/egraph/doc/design/11-extraction.md#ties-and-the-content-order)
defines the colouring.

## Alternatives considered

- **Choosing the nodes, then the grouping.** An earlier extractor proved the
  optimum of the flat cost, with every AC node flat, and then chose each node's
  grouping. Sequencing the two is not optimal: on 600 instances of the monitor
  memory problem it is above the joint optimum on 130 (21.7%), by up to 31%
  (`egraph/tests/ex_paper_claims.rs`). The loss comes from the choice among
  flat optima: the best grouping over every flat optimum reaches the joint
  optimum on all 600. The `splits` rung chooses both in one encoding.
- **A separate extractor over the dump.** That extractor read the exported JSON
  and took its candidates in the order of the dump's node names, which were node
  ids. Its result then depended on the order rules were applied in: naive and
  semi-naive saturation built the same e-graph on all of those 1,172 specifications, and their
  extracted terms differed on 50. Extraction now runs inside Semper, and the
  dump's names are content colours.
- **Breaking ties by a second objective.** Making equal-cost terms distinct by a
  lexicographic second cost changes every benchmark's encoding and optimality
  proof, and a rank sum is not a total order on terms. Ties are instead
  resolved by content: the export orders by colour, and the greedy extractor
  breaks a cost tie by term height and then by node colour.

The [design chapter](https://github.com/yaspar-org/semi-persistent/blob/main/egraph/doc/design/11-extraction.md#alternatives-considered-and-rejected-1)
records the others.

## Limits

- A script has no resource bound: it can loop, exhaust memory, or overflow the
  stack, since Roto compiles to native code without an instruction count.
- Costs are exact, within the cap `--cost-bits` sets if any, and within the range
  of the solver they are exported to; what ASP and MiniZinc criteria compute
  inside the solver is the solver's arithmetic ([Number ranges](#number-ranges)).
- Roto's own `i64`/`u64` operators wrap and its division by zero aborts, so a
  cost script that uses `+`, `-`, `*`, `/`, or `%` is refused when the program is
  checked; scripts compute with the exact methods of `IBig`, `UBig`, and the
  encoded integers ([Exact integers](25-cost-functions-in-roto.md#exact-integers)).
- Deciding the binary grouping of a flat node with ten or more operands can take
  CaDiCaL an hour or more.
- A recursive attribute keeps every value it can take per class. A cap can be set
  through the Rust API (`Build::set_attribute_cap`); reaching it is an error, never
  a smaller domain.
- Script, criteria, `:file`, and `:proof` paths are relative to the working
  directory, not to the program file.
- Clingo and MiniZinc run with no time limit from Semper unless the solver's own
  arguments set one.
