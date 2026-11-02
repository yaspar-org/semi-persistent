# CBMC e-graph corpus

These 214 programs are e-graphs that CBMC built while encoding C verification
benchmarks, converted into Semper programs. Each of the 107 dumps holds two
e-graphs, and each becomes its own program:

- `NAME.base.egg`: commutative canonicalization only;
- `NAME.cong.egg`: the same nodes, with the unions of the SSA equations
  (congruence closure).

`egg_tests.rs` (`cbmc_corpus`) loads, sortchecks and rebuilds every program, under
naive and semi-naive evaluation. The programs build e-graphs and run no rules, so the
test covers term construction, hash-consing, AC canonicalization and the rebuild after
unions, with up to 42,120 `let`s per program. `manifest.json` records, per program,
the number of `let`s and `union`s and the roles CBMC marked in its comments
(`[ASSUME]`, `[ASSERT]`).

## Source

| | |
|---|---|
| Archive | `cbmc-egg-dumps.tar.gz`, provided by Michael Tautschnig |
| sha256 | `fd938667882d4a534661de5bc5c0fad75bd762e6b2782948582875b54f2bdb3a` |
| Content | 107 dumps in egg `SymbolLang` format, from SV-COMP benchmarks, CBMC's regression tests, Collections-C, and small arithmetic programs |
| Licence | Michael Tautschnig cleared the dumps for redistribution in this repository (2026-10-26). The programs they were exported from keep their own licences: the SV-COMP benchmark collection, CBMC's regression tests, and Collections-C. |

The raw dumps do not load in Semper as they are: egg's `SymbolLang` accepts any
operator symbol, and Semper requires declarations. The conversion supplies them.

## Encoding

One sort, `Term`:

| Dump | Semper |
|---|---|
| `leaf_N` with comment `const V` (hexadecimal) | `(Const V N)`: the value is kept, and the leaf id keeps constants of different types apart, since the dump has no widths |
| `leaf_N` with comment `const NULL` | `(Null N)` |
| any other `leaf_N` (SSA symbol, nondet value, or an operator CBMC kept opaque) | `(Leaf N)` |
| `type_N` | `(Type N)` |
| `plus`, `mult`, `bitxor` | `:assoc-comm` |
| `bitand`, `bitor` | `:assoc-comm-idem` |
| `equal` | `:comm` |
| `minus`, `neg`, `bitnot`, `typecast` | positional |

`(let eX expr)` and `(union eA eB)` keep their names, and the comment of every `let`
is kept. Every line of every dump converts; none is skipped.

## Regenerating

```text
tar -xzf cbmc-egg-dumps.tar.gz -C DIR
python3 -I scripts/cbmc-egg-convert.py DIR/egg-dumps egraph/tests/egg/cbmc
```

The script rewrites every program and `manifest.json`, and it does not touch this
README.
