# Choosing a memo strategy and dedup mode

Every call to `fold` and every store you create involves two choices that
affect performance. This document explains both choices, shows benchmark
numbers, and gives guidance for picking among them.

The two choices are orthogonal. Memo strategy controls how a fold caches
intermediate results during a single traversal; dedup controls whether
the store deduplicates nodes as you push them. You can combine any memo
strategy with either dedup mode.

All numbers in this document come from `traversals/benches/fold_bench.rs`,
which folds balanced binary `Add(Lit)` trees at depths 10, 14, and 18
(containing 2,047 / 32,767 / 524,287 nodes).

## Memo strategies

A fold memoizes: when the traversal reaches a node that has already been
folded (because it is shared between parents in a DAG, or because an
earlier phase already visited it), the cached result is reused rather
than recomputed. The memo table is what stores those cached results.
Three strategies ship with the crate.

The default is `Dense`, which allocates a `Vec<Option<A>>` sized to the
full store. Lookup is an array index, so each memo hit is effectively
free. The downside is the allocation: if the store has a million nodes
but a fold only visits a thousand of them, `Dense` still allocates a
million memo slots.

`Sparse` replaces the vector with a hashmap. Allocation grows only with
the nodes actually visited, so folding a small subtree of a large store
costs proportional to the subtree, not the store. Each memo operation
now pays a hash and a probe, so folds that visit most of the store run
slower than under `Dense`.

`memo::None` keeps the dense vector but skips the "have I seen this
node?" checks that both other strategies perform. It is only correct for
trees, not DAGs: a node reached through two parents will be folded
twice, and any side-effecting algebra will fire twice. On trees the
saved branch gives a small but consistent speedup.

### Fold throughput

| Depth | dense | sparse | none |
|-------|------:|-------:|-----:|
| 10 | 189 M/s | 60 M/s | close to dense |
| 14 | 188 M/s | 64 M/s | close to dense |
| 18 | 186 M/s | 61 M/s | close to dense |

Sparse runs about 3× slower than dense on the benchmark. The benchmark
folds the whole tree on each iteration, so sparse pays its hash cost on
every node and gets no compensating memory win. In the opposite regime,
a 1K-node subtree inside a 1M-node store, sparse allocates a hashmap of
around 1K entries while dense still allocates 1M vector slots, and
sparse wins on both time and space.

The rule of thumb is simple. If the fold visits most of the store, use
`Dense`. If it visits a small focused region of a large store, use
`Sparse`. If the input is a pure tree with no shared subterms and
throughput matters, use `memo::None`. The API is the same in all three
cases; only the argument to `with_strategy` changes.

```rust
use semi_persistent_traversals::{Sparse, memo};

let r = s.with_strategy::<Sparse>().fold(root, alg_stmt, alg_expr);
let r = s.with_strategy::<memo::None>().fold(root, alg_stmt, alg_expr);
```

## Deduplicating the store

A plain store (`LangStore::new()`) appends every pushed node, even if it
is structurally identical to an earlier one. A deduplicating store
(`LangStore::new_dedup()`) keeps a per-sort hashmap keyed by node
structure; pushing a node that is already present returns the existing
ID instead of appending a duplicate.

The two constructors return different types. `new()` gives back a
`LangStore<false>` and `new_dedup()` gives back a `LangStore<true>`,
where the boolean is a `const DEDUP: bool` parameter on the store. The
generic impls fold `if DEDUP` branches into monomorphized code, so a
`<false>` store has the same runtime shape as before the refactor and a
`<true>` store pays the hashmap lookups unconditionally. The type
distinction also gates in-place mutation: `set_*` methods and
`ZipperMut::new` only exist on `LangStore<false>`, making mutation on a
deduplicating store a compile error rather than a silent dedup-map
corruption.

Dedup costs roughly 2 to 3× more per push than plain construction,
because each push now computes a hash and probes the hashmap. The cost
is consistent across sizes:

| Depth | Nodes   | plain    | dedup              |
|-------|--------:|---------:|-------------------:|
| 10    |   2,047 | 370 M/s  | 140 M/s (2.6× slower) |
| 14    |  32,767 | 424 M/s  | 146 M/s (2.9× slower) |
| 18    | 524,287 | 270 M/s  | 144 M/s (1.9× slower) |

The reason to pay that cost is memory, not time. Consider the benchmark
input: a balanced binary tree where every leaf is `Lit(1)` and every
internal node is `Add` of two identical subtrees. Without dedup, a
depth-18 tree allocates all 524,287 nodes. With dedup, identical
subtrees collapse: there is one unique `Lit(1)`, one unique
`Add(Lit(1), Lit(1))`, one unique `Add` of that, and so on up the tree.
The depth-18 deduped store contains 19 nodes total.

That extreme compression is specific to this input, but the pattern is
common. Compiler IRs and e-graphs tend to have substantial structural
sharing: the same constant, the same subexpression, or the same type
appears hundreds or thousands of times in a real program. Dedup turns
every one of those occurrences into a single node. Any later fold then
visits each unique node once.

Dedup also interacts correctly with `mark` and `restore`. If you push
new nodes after calling `mark()` and then call `restore(&mark)`, the
dedup entries pointing at the truncated region are pruned. Stale IDs
from the discarded nodes are never returned.

When to turn dedup on:

- The AST has or is expected to develop structural sharing. Compiler IRs,
  e-graphs, canonicalization passes, memoized computation graphs.
- You intend to fold the store more than once. The dedup cost is paid
  at construction; every later traversal benefits from the smaller
  working set.

When to leave it off:

- One-shot pipelines where the store is built, folded once, and
  discarded. The 2-3× construction penalty dominates.
- Inputs with no redundancy, such as a freshly parsed surface syntax
  tree before any canonicalization.

## Picking a combination

A quick flowchart for the common cases.

If you will fold most of the store (single-pass pipeline over a built
AST), use `Dense` memo. If the tree has structural sharing worth
collapsing, pair that with `new_dedup()`; otherwise `new()`.

If you will fold a small focused region of a much larger store
(incremental analysis, focused query), use `Sparse` memo. The dedup
choice is independent and follows the same question as above.

If the input is guaranteed to be a tree (no shared children, no DAG
structure) and fold throughput is a bottleneck, add
`.with_strategy::<memo::None>()` to shave off the dedup check. Never
use `memo::None` on a store built with `new_dedup`, since dedup is
precisely the source of DAG structure that `memo::None` assumes away.

## Reproducing the numbers

```bash
cargo bench -p semi-persistent-traversals --bench fold_bench
```

Benchmark source lives in
[`traversals/benches/fold_bench.rs`](../../benches/fold_bench.rs).
Absolute throughput varies with hardware; the ratios (3× sparse
overhead on full folds, 2.5× dedup construction cost) have been stable
across runs.

## Appendix: scheme signatures

Every scheme generated by `rec_family!` takes one closure per sort, in
the order the sorts were declared. With two sorts (Stmt, Expr), most
schemes take two closures; `fold_with_aux` and `fold_pair` take four,
two per sort.

| Scheme | Closures per sort | Signature per sort |
|--------|-------------------|--------------------|
| `fold` | 1 | `Fn(SortNodeMapped<A_stmt, A_expr, …>) -> A_sort` |
| `fold_short` | 1 | `Fn(SortNodeMapped<A_stmt, A_expr, …>) -> Result<A_sort, A_sort>` |
| `fold_with_history` | 1 | `Fn(SortNodeMapped<Ann<A_stmt>, Ann<A_expr>, …>) -> A_sort` |
| `fold_with_aux` | 2 (aux + main) | aux: `Fn(Mapped<B>) -> B_sort`; main: `Fn(Mapped<(A,B)>) -> A_sort` |
| `fold_with_original` | 1 | `Fn(&SortNode, SortNodeMapped<A, …>) -> A_sort` |
| `fold_pair` | 2 (A + B algebras) | `Fn(Mapped<(A,B)>) -> A_sort` and `Fn(Mapped<(A,B)>) -> B_sort` |
| `prefold` | 2 (pre + alg) | pre: `Fn(SortNode) -> SortNode`; alg: same as `fold` |
| `rewrite` | 1 | `Fn(SortNode, &mut Store) -> SortId` |
| `rewrite_down` | 1 | `Fn(SortNode) -> SortNode` |
| `transform` | 1 | `Fn(SortNode) -> SortNode` |
| `fold_all` | 1 | same as `fold`, returns a per-sort `Cache` |

The return type of `fold` and its relatives is sort-tagged:
`LangStoreFoldResult<A_stmt, A_expr, ...>` is an enum with one variant
per sort. Unwrap with `.unwrap_<sort>()` when the root sort is known at
the call site, or match on the variants otherwise.

Each sort can return a different type. The type inference chapter of
the testorial returns an environment transformer for statements and a
type query for expressions; the bytecode compiler chapter returns
`Vec<Op>` for both.

Mapped enums only mention sort parameters for sorts they actually
reference. If `Stmt` never contains an `Expr` variant, `StmtNodeMapped`
will be generic in `A_stmt` alone rather than in both `A_stmt` and
`A_expr`. In a realistic mutually recursive family that cross-references
both sorts, all sort parameters appear.
