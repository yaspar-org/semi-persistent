# A corpus of 100 problems

One example proves that the method can work. A corpus is how you find out
whether it works when you did not hand-pick the case.

[`autoformalization/`](https://github.com/yaspar-org/semi-persistent/tree/main/autoformalization)
holds 100 executable anti-unification problems: 20 policy statements crossed
with five variations of candidate B.

```text
generate.py  ->  100 *.egg  ->  au-corpus --json  ->  results.json
                                                        |
                                    make_page.py  ->  results.html
```

Each `.egg` file carries the natural-language statement as a comment, its
signature, two candidate formalizations, one domain rewrite, a `(run 3)`, a
machine-readable oracle directive, and two anti-unification queries.

## How a problem is built

`generate.py` starts from candidate A as a term and derives candidate B in two
stages.

First, transformations that are semantics preserving *under the emitted
signature and rewrite*, so a correct solver must absorb all of them:

- conjunct reordering and duplication, justified by `:assoc-comm-idem` on `And`;
- `Eq` argument swapping, justified by `:comm`;
- expanding the named approved-zone predicate into its disjunction of concrete
  zones, justified by the `(rewrite ...)` the file emits.

Then exactly one genuine difference, or none as a control:

| suffix | injected difference | oracle |
| --- | --- | --- |
| `connective-drift` | a guarded `And` becomes `Or` | `variants>=1` |
| `threshold-drift` | `Lte` becomes `Lt` | `variants>=1` |
| `missing-requirement` | a required conjunct is dropped | `variants>=1` |
| `branch-drift` | the two `Ite` branches are swapped | `variants>=1` |
| `equivalent-control` | none | `variants=0` |

## Why the variant count is an oracle

A `Variants` node is exactly a position where the two candidates genuinely
disagree. So the count is checkable in both directions:

- `variants=0` on the control asserts that **every** presentation change was
  absorbed. If any of the reordering, duplication, `Eq` swapping or predicate
  expansion leaked through, the control fails.
- `variants>=1` on a mutation asserts that the injected difference **survived**
  congruence closure and the rewrite. A solver that absorbed too much would fail
  here.

Each file states its own expectation as `; :au-expect variants=N`, so the corpus
is self-describing and the runner does not need a separate answer key.

## Running it

```bash
autoformalization/run.sh
```

That checks the committed corpus against its generator, builds the runner,
executes all 100 problems in both modes, builds and checks the results page, and
runs the engine's independent metamorphic generator. Step by step:

```bash
python3 autoformalization/generate.py --check
cargo build --release --manifest-path autoformalization/runner/Cargo.toml
autoformalization/runner/target/release/au-corpus
```

The runner accepts any `.egg` program, not just this corpus. It exists because
the engine's own front end accepts `:algorithm exact` and `:algorithm uct` only,
and the corpus wants the hybrid mode, which is reachable from the Rust API but
not from the surface syntax. The runner drives the same public library pipeline
the front end drives and intercepts the two anti-unification commands so it can
select the solver configuration itself. Its one restriction is that query
operands must be `let`-bound globals.

## Results

All 100 problems complete in both modes, with hybrid matching the exact optimum
on every one:

```text
files: 100 run, 0 failed, 0 unreadable; 100 carried an :au-expect oracle
exact   100 queries, 100 complete, 120 generalization variables
hybrid  100 queries, 100 complete, 120 generalization variables
hybrid delegated 1480 subproblems to the exact solver; 1480 returned an
exactness certificate (divisor 8)
```

Two results worth separating. The runner asserts equal **quality**,
`(size, variant_mass)`, because two distinct terms can both be least general
generalizations. In fact all 100 problems produce a byte-identical term in both
modes. That is not guaranteed in general, so the results page reports it per
problem rather than assuming it: a future divergence shows up as "equal quality,
different term" instead of passing unnoticed.

The 20 `equivalent-control` problems delegate nothing, correctly. The rewrite
and the ACI declarations put both candidates in the *same* e-class, so the pair
is already proved equal and there is no search to do. The runner detects that
case rather than reporting it as a collapse.

## The connective drift, again

Chapter 6 noted that an `And` to `Or` change is reported through two identity
elements rather than one connective-shaped node:

```text
(And (Or ownership (Variants (Lit false) auditedEncryption))
     (Variants auditedEncryption (Lit true)))
```

The corpus is where the crossover point can be stated. With a safeguard conjunct
of size 1, the two forms cost `4 + 2|O|` and `|O| + 8`, where `O` is the shared
operand. The single-node form wins below `|O| = 4`, the two tie in size at
`|O| = 4` with the double form taking the variant-mass tiebreak, and the double
form wins above that. Sharing a large operand once beats copying it into both
branches. This corpus lands above the crossover only because its ownership term
`(Eq (ownerOfAsset asset) (ownerOfActor actor))` is five nodes.

`autoformalization/examples/identity-generalization.egg` demonstrates both sides
of the crossover and then verifies soundness by instantiating the double form by
hand, checking each instance lands in the same e-class as the input it must
reproduce, with a mixed-branch negative control to prove the check is not
vacuous.

The tension is worth naming. The result is sound, but the cost model minimizes
`(size, variant_mass)` and therefore rewards structure sharing, so it prefers
"the safeguard conjunct moved and two units appeared" over "the connective
changed". For explaining a difference to a person, the second reading is the
useful one. **Optimal under the cost model and best for a reader are not the
same objective**, and this corpus is where that shows up as a measurable
disagreement rather than an opinion.

## The results page

`make_page.py` turns the JSON record into a single self-contained
`results.html`: inline CSS and JS, the record embedded as a script tag, no
network fetches, no CDN, no build step. Open it from the filesystem.

```bash
autoformalization/runner/target/release/au-corpus --json autoformalization/results.json
python3 autoformalization/make_page.py autoformalization/results.json
node autoformalization/check_page.js autoformalization/results.html
```

Each problem is two rows read across: `candidateA` against `candidateB`, then
the exact anti-unifier against the hybrid one, each as a tree with `Variants`
nodes called out and both sides labelled. The phrase the injected difference
perturbs is underlined, and hovering a `Variants` node lights up the phrases it
corresponds to.

Both highlight sources are generator ground truth rather than a text match. That
is what the `:nl-seg`, `:nl-ops` and `:nl-focus` comment directives in each file
are for: `generate.py` assembles the English from the same fields it builds the
term from, so every span is exact by construction, and `--check` asserts the
segments reassemble the statement.

`check_page.js` runs the page's own scripts against a DOM stand-in under Node,
so a runtime error or a wrong phrase attribution fails a check instead of
sitting in a browser console.

## An independent generator

The engine also ships a seeded metamorphic anti-unification generator,
independent of `generate.py` and of the corpus runner. It draws a random ground
term, replaces one to four pairwise non-nested positions with fresh nullary
constants, and amplifies the e-graph with merges that add class members without
lowering any class's minimal term size.

That construction fixes two integers about the least general generalization, and
those are the oracles: its size is `|t0| + m`, and it contains exactly `m`
`Variants` nodes.

```bash
cargo test -p semi-persistent-egraph --release --test au_metamorphic \
  metamorphic_default_corpus -- --nocapture
```

```text
300 cases, gap==0 300/300 (100.0%), certified exact 300/300
```

Two things it does not do, worth stating because the name suggests otherwise.
The planted right-hand side of each variation point is a fresh constant, not an
arbitrary foreign term, so no mutation introduces structure. And the variation
applied on top is e-graph merges, not semantics-preserving surface rewrites of
two independently written terms: `t1` is `t0` unchanged and only `t2` is
substituted into.

The full detail of both corpora, including the hybrid-divisor sweep and the 12
cases where the returned term differs from the reference by a permutation of the
planted constants, is in
[`autoformalization/README.md`](https://github.com/yaspar-org/semi-persistent/blob/main/autoformalization/README.md).
