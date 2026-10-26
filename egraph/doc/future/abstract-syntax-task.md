<!--
Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
SPDX-License-Identifier: Apache-2.0
-->
# Task: Surface Syntax for Abstract Domains

**Branch**: `abs-surface-syntax`, PR 1 of 4. **Status**: specified, not implemented.
The acceptance tests exist and are ignored; the code carries
`TODO(abs-surface-syntax)` comments at every change site (§6).

## 1. What the PR delivers

The PR adds the declarations, commands and guards of the design in
[eclass-analysis.md §5](eclass-analysis.md#5-choosing-domains-per-sort) and
[§6](eclass-analysis.md#6-propagation-rules) to the surface language. Every
new form parses, sortchecks and lowers to the resolved IR. No form computes an
abstract value yet: the engine PR (`abs-saturation-engine`) executes them.

| Item | Delivered here | Delivered by a sibling branch |
|---|---|---|
| Domain set per sort (`:interp`, `:domains`) | parse, check, store per sort | storage in `abs-class-storage` |
| Propagator per operator (`:interp OP`) | parse, check signature, store per op | transfers in `abs-saturation-engine` |
| `:range (lo hi)` on a result | parse, check, store per op | the fact in `abs-saturation-engine` |
| `(refine t VALUE)` command and action | parse, check, lower | the meet in `abs-saturation-engine` |
| Guards `within`, `nonzero`, `known-bits` | parse, check, lower | the test in `abs-saturation-engine` |
| Names of carriers, domains, operators | a stub list in `egraph` | the registry in `abs-domain-registry` |

A program that uses none of the new forms behaves exactly as before. Its
outcome, its node count and its warnings do not change.

## 2. Grammar

The forms below are exact. N is a decimal integer; lo, hi, r, m, V and M are
decimal integers of any size, with an optional leading `-` where negative
values make sense.

| Form | Position | Example |
|---|---|---|
| `(sort S :interp C [:domains (D*)])` | top level | `(sort Int :interp int :domains (interval congruence nonzero))` |
| `(sort S :interp C)` | top level | `(sort Bool :interp bool)`: the carrier's default set |
| `(sort S :interp C :domains ())` | top level | the analysis is off for `S` |
| `:interp OP` | tag of `function`, `constructor` | `(function lt (Int Int) Bool :interp <)` |
| `:range (lo hi)` | tag of `function`, `constructor` | `(function hash (BV32) BV32 :range (0 1023))` |
| `:interp embed` | tag of a unary `function` or `constructor` from a literal sort into a sort with `:interp` | `(constructor Num (IBig) Int :interp embed)` |
| `(refine t VALUE)` | top level; `t` is a ground term or a global | `(refine (x) (interval 0 9))` |
| `(refine t VALUE)` | rule action; `t` is a right-hand side | `((refine r (interval 0 99)))` |
| `(within x lo hi)` | rule body, `:when` | `(within y 0 9)` |
| `(nonzero x)` | rule body, `:when` | `(nonzero y)` |
| `(known-bits x V M)` | rule body, `:when` | `(known-bits v 1 254)` |

`C` is `int`, `bool` or `(bitvec N)`. `:interp` and `:domains` follow the
sort name in either order. `:interp OP` and `:range` mix with the algebra and
extraction tags in any order. `OP` is an operator token, so `<` and `+` parse.

| VALUE | Meaning |
|---|---|
| `(interval lo hi)` | the integers from lo to hi, both included |
| `(bits :val V :mask M)` | a Tnum: a bit set in M is unknown, any other bit equals that bit of V |
| `(congruence r m)` | the integers equal to r modulo m |
| `(nonzero)` | every value except 0 |
| `(true)`, `(false)` | one Boolean value |

A guard holds when the abstract value of `x` lies inside the set it names.
It tests inclusion, so a guard never holds on a value that is only compatible.

| Guard | Holds when |
|---|---|
| `(within x lo hi)` | every value of `x` lies in `(interval lo hi)` |
| `(nonzero x)` | no value of `x` is 0 |
| `(known-bits x V M)` | every value of `x` lies in `(bits :val V :mask M)` |

The guards parse today as ordinary patterns (`SurfacePattern::App`). The
sortchecker recognises them by head name, so the parser needs no change for
them. Datatype variants do not accept `:interp` or `:range` in this PR.

### 2.1 Carriers and the literal model

A carrier is the set of concrete values a class of the sort denotes. Every
carrier corresponds to a literal sort of the `LitModel` where one exists, so one
table fixes four things: the concrete values, the abstract domains that
over-approximate them, how a literal enters the analysis, and which primitive
each `:interp` operator abstracts.

| Carrier `C` | Literal sort | Domains (`abstract-domains`) | A literal `k` enters as | `:interp` operators abstract |
|---|---|---|---|---|
| `int` | `IBig` | `interval` (`IntervalZ`), `congruence`, `nonzero` (fields of `FactsZ`) | `[k, k]`, `k mod m`, nonzero iff `k != 0` | the `IBig::` primitives: `+` is `IBig::+`, `<` is `IBig::<` |
| `(bitvec 64)` | `u64`, and `i64` under the signed operators | `ubounds` (`Interval<u64>`), `sbounds`, `congruence`, `bits` (fields of `Facts<u64>`) | `[k, k]`, the Tnum `(k, 0)` | the `u64::` and `i64::` primitives (`bvadd` is `u64::+`, `bvslt` is `i64::<`) |
| `(bitvec N)`, N in 8, 16, 32, 128 | none today | the same fields of `Facts<W>` | no literal until a literal sort of width N exists | no primitive; the transfer exists, the concrete operation does not |
| `(bitvec N)`, any other N | none | top only | no literal | none |
| `bool` | `bool` | `bool` (`Bool4`) | `True` or `False` | the `bool::` primitives |
| none | `RBig` | none | not analysed | none |

The analysis attaches values to classes in three ways:

1. **Literal sorts.** A class of a literal sort (`IBig`, `u64`, `bool`) already
   denotes one concrete value, so it is analysed with no declaration, using the
   carrier of the row above and its default domains. A literal node `k` starts
   at its singleton.
2. **User sorts with `:interp`.** `(sort Int :interp int)` declares that every
   class of `Int` denotes one integer. Its values come from three sources: seeds
   (`refine`), the transfers of its `:interp` operators, and embeddings.
3. **Embeddings.** A constructor tagged `:interp embed` injects a literal sort
   into a user sort with the matching carrier: the class of `(Num k)` gets the
   lifted value of `k`. This is how the literals of a wrapping encoding, such as
   the CBMC corpus's `(Const V N)`, reach the analysis. Sortcheck rejects an
   embedding whose argument sort is not the literal sort of the result's carrier.

The operator names after `:interp` are the SMT-LIB names (`+`, `<`, `bvadd`,
`bvslt`, `ite`); the table fixes the primitive each one abstracts, and the
registry of #148 holds the verified transfer for each. Whether `:interp` also
accepts the primitive's own name (`:interp IBig::+`) is left to the student (§7).

## 3. Sortcheck rules and errors

The stub list below stands in for the registry of `abs-domain-registry`.
When that branch lands, the checks read the registry instead; the messages stay.

| Carrier | Domains available | Default set |
|---|---|---|
| `int` | `interval`, `congruence`, `nonzero` | `(interval congruence nonzero)` |
| `(bitvec N)`, 1 ≤ N ≤ 128 | `ubounds`, `sbounds`, `congruence`, `bits` | `(ubounds sbounds congruence bits)` |
| `bool` | `bool` | `(bool)` |

| Operator | Signature over carriers |
|---|---|
| `+`, `-`, `*` | `(int int) int` |
| `neg` | `(int) int` |
| `<`, `<=` | `(int int) bool` |
| `bvadd`, `bvsub`, `bvmul`, `bvand`, `bvor`, `bvxor` | `((bitvec N) (bitvec N)) (bitvec N)`, one N |
| `bvult`, `bvule`, `bvslt`, `bvsle` | `((bitvec N) (bitvec N)) bool`, one N |
| `and`, `or` | `(bool bool) bool` |
| `not` | `(bool) bool` |
| `ite` | `(bool T T) T`, T any carrier |

A VALUE and a guard each need one domain enabled on the sort of their term.
A sort without `:interp` enables no domain.

| VALUE or guard | Domain it needs |
|---|---|
| `(interval lo hi)`, `(within x lo hi)` | `interval` on `int`, `ubounds` on `(bitvec N)` |
| `(bits :val V :mask M)`, `(known-bits x V M)` | `bits` |
| `(congruence r m)` | `congruence` |
| `(nonzero)`, `(nonzero x)` | `nonzero` |
| `(true)`, `(false)` | `bool` |

An error names the domain of this table, and `interval` on a sort without a
carrier. `nonzero` on a bit-vector and `bits` on `int` are never available,
so those combinations always fail.

The checks and their messages follow. A message is the text after the
`sort error:` prefix; each acceptance program asserts the part shown.

| Rule | Message | Program |
|---|---|---|
| `:domains` needs `:interp` | `sort 'Int': :domains needs :interp` | `err_domains_without_interp` |
| the carrier is known | `sort 'F': unknown carrier 'float'` | `err_unknown_carrier` |
| the width lies in 1..=128 | `sort 'B': bit-vector width 0 is outside 1..=128` | `err_bitvec_width_zero` |
| each domain is known | `sort 'Int': unknown domain 'octagon'` | `err_unknown_domain` |
| each domain fits the carrier | `sort 'Int': domain 'bits' is not available for carrier int` | `err_domain_wrong_carrier` |
| each domain appears once | `sort 'Int': domain 'interval' is listed twice` | `err_domain_listed_twice` |
| the operator is known | `function 'f': unknown interpreted operator 'frob'` | `err_interp_unknown_operator` |
| the signature matches the carriers | `function 'f': :interp bvadd needs signature ((bitvec N) (bitvec N)) (bitvec N), got (int int) int` | `err_interp_signature_mismatch`, `err_interp_width_mismatch`, `err_interp_uninterpreted_sort` |
| no `:interp` with `:assoc` | `function 'add': :interp does not combine with :assoc` | `err_interp_with_assoc` |
| `:range` has a bounds domain | `function 'h': :range needs a bounds domain on sort 'E'` | `err_range_without_bounds`, `err_range_disabled_domain` |
| `:range` is not empty | `function 'h': :range needs lo <= hi` | `err_range_reversed` |
| a VALUE's domain is enabled | `refine: domain 'congruence' is not enabled on sort 'Int'` | `err_refine_domain_not_enabled`, `err_refine_bool_on_int`, `err_refine_uninterpreted`, `err_refine_action_domain` |
| an interval is not empty | `(interval lo hi) needs lo <= hi` | `err_refine_interval_reversed` |
| a congruence is reduced | `(congruence r m) needs m >= 1 and 0 <= r < m` | `err_refine_bad_congruence` |
| a Tnum is well formed | `(bits :val V :mask M) needs V and M to share no bit` | `err_refine_bad_bits` |
| a constant fits the width | `value 256 does not fit (bitvec 8)` | `err_refine_value_too_wide` |
| a guard's domain is enabled | `known-bits: domain 'bits' is not enabled on sort 'Int'` | `err_guard_domain_not_enabled`, `err_when_guard_domain` |
| a guard's variable is bound | `within: 'z' is not bound by an earlier pattern` | `err_guard_unbound_var` |
| the new names stay free | `operator name 'within' is reserved by the abstract-domain syntax` | `err_reserved_guard_name` |

The signature message prints `none` for a sort without a carrier. A guard
variable is a global or a variable that a pattern written before the guard
binds, the rule that applies to primitive guards today (see
[A1-language-guide.md](../design/A1-language-guide.md#predicate-guards)). The
reserved names are `refine`, `within`, `nonzero` and `known-bits`.

## 4. Lowering to the IR

The PR adds one module and extends six types. The names below are the
interface that `abs-saturation-engine` consumes; their fields are the student's
choice (§7).

| Type | Where | Content |
|---|---|---|
| `Carrier`, `Domain`, `DomainMask` | new `egraph/src/abs_syntax.rs` | `Int`, `Bool`, `BitVec(width)`; one bit per domain |
| `AbsValue`, `AbsTest` | `abs_syntax.rs` | checked VALUE and guard, each with its domain |
| `AbsValueLit`, `AbsTestLit` | `abs_syntax.rs` | the unchecked surface forms the parser builds |
| stub registry | `abs_syntax.rs` | the three tables of §3, behind functions that `abs-domain-registry` replaces |
| `Command::Sort` | `ast.rs` | the name plus `Option` carrier and `Option<Vec<String>>` domains |
| `Command::Function` | `ast.rs` | new fields `interp: Option<String>`, `range: Option<(BigInt, BigInt)>` |
| `Command::Refine` | `ast.rs` | `{ term: Term, value: AbsValueLit, span: Span }` |
| `Action::Refine` | `ast.rs` | `(RhsTerm, AbsValueLit)` |
| `Atom::AbsGuard` | `compile.rs` | `{ var: String, test: AbsTestLit, span: Span }` |
| `RAtom::AbsGuard` | `resolve.rs` | `{ node: PatVar, test: AbsTest }` |
| `ResolvedAction::Refine` | `resolve.rs` | `(RRhsTerm, AbsValue)` |
| `CCommand::Refine` | `sortcheck.rs` | `{ term: CTerm, value: AbsValue }` |
| per-sort abstract info | `registry.rs`, `SortRegistry` | `(Option<Carrier>, DomainMask)` for each sort id |
| per-op propagator and range | `registry.rs`, a side table | the resolved operator and the `:range` bounds for each op id |

`OpMeta` stays `Copy`, so the operator and range do not go into it. Sort and
operator declarations keep their path: `exec_decl` registers them during
sortcheck, and `CCommand::Decl` replays nothing at run time.

## 5. Interim semantics

Until `abs-saturation-engine` lands, every abstract value is top.

| Form | Effect in this PR |
|---|---|
| `:interp`, `:domains` on a sort | recorded; no class carries a value |
| `:interp OP` on an operator | recorded; no transfer runs |
| `:range (lo hi)` | recorded; no fact is asserted |
| `(refine t VALUE)`, top level | builds `t` as `let` would, then changes nothing |
| `(refine t VALUE)`, action | builds `t` as an insertion would, then changes nothing |
| `within`, `nonzero`, `known-bits` | never hold, so the match is dropped |

Every row is sound: top over-approximates every set of values, and a guard
that never holds only removes matches. The program raises one warning, with
this exact text, if at least one sort enables at least one domain:

```text
abstract domains are declared, but the analysis is not active: values stay top, abstract guards never hold, and refine and :range have no effect
```

The acceptance runner counts warnings that contain `the analysis is not
active` and requires exactly one. A program whose sorts all have `:domains ()`
raises none (`ok_sort_domains_disabled`).

## 6. Change sites

Each site carries a comment `TODO(abs-surface-syntax)`; `git grep
'TODO(abs-surface-syntax)'` lists them. The line numbers are those of the
handoff commit. The student removes each comment with the change it describes.

| File:line | Item | Change |
|---|---|---|
| `egraph/src/lib.rs:11` | module list | add `pub mod abs_syntax` with the §4 types and the stub list |
| `egraph/src/parser.rs:846` | `parse_action` | `refine` action arm |
| `egraph/src/parser.rs:923` | `parse_rule_tags`, `:when` | none for guards; confirm they parse as patterns |
| `egraph/src/parser.rs:1315` | `parse_command`, `rule` | none for guards; confirm negative and large integers parse |
| `egraph/src/parser.rs:1359` | `parse_command`, `sort` | `:interp` and `:domains` options |
| `egraph/src/parser.rs:1379` | `parse_command`, `function` | carry `:interp` and `:range` into `Command::Function` |
| `egraph/src/parser.rs:1872` | `parse_command`, fallback | top-level `refine` arm before the insertion fallback |
| `egraph/src/parser.rs:1901` | `parse_decl_tags` | read `:interp OP` and `:range (lo hi)` |
| `egraph/src/ast.rs:570` | `Command` | `Sort` carries carrier and domains; add `Refine` |
| `egraph/src/ast.rs:582` | `Command::Function` | `interp` and `range` fields |
| `egraph/src/ast.rs:666` | `Action` | add `Refine` |
| `egraph/src/compile.rs:94` | `Atom` | add `AbsGuard` |
| `egraph/src/registry.rs:121` | `OpMeta` | stays `Copy`; add the per-op side table |
| `egraph/src/registry.rs:179` | `SortRegistry` | per-sort carrier and domain mask |
| `egraph/src/sortcheck.rs:79` | `CCommand` | add `Refine` |
| `egraph/src/sortcheck.rs:606` | `SurfaceFlatCtx::flatten_root` | recognise guards, push `Atom::AbsGuard` |
| `egraph/src/sortcheck.rs:1388` | `sortcheck_pass` | `Command::Refine` arm |
| `egraph/src/sortcheck.rs:1578` | `exec_decl`, `Command::Sort` | check carrier and domains, apply the default, record |
| `egraph/src/sortcheck.rs:1601` | `exec_decl`, `Command::Function` | check `:interp` and `:range` |
| `egraph/src/resolve.rs:132` | `RAtom` | add `AbsGuard` |
| `egraph/src/resolve.rs:1284` | `resolve_atom` | `Atom::AbsGuard` arm |
| `egraph/src/resolve.rs:2492` | `ResolvedAction` | add `Refine` |
| `egraph/src/resolve.rs:2528` | `resolve_action` | `Action::Refine` arm |
| `egraph/src/schedule.rs:1120` | guard scheduling | an `AbsGuard` step that fails while values are top |
| `egraph/src/apply.rs:320` | action compilation | `Refine` builds its term only |
| `egraph/src/interpret.rs:879` | `exec_checked` | the one warning; `CCommand::Refine` builds its term only |
| `egraph/doc/design/A1-language-guide.md:29` | Sorts and Operators | interpreted sorts, propagators, the warning |
| `egraph/doc/design/A1-language-guide.md:276` | Predicate Guards | abstract guards, `refine`, the annex grammar |
| `doc/book/src/B-command-reference.md:16` | declarations | rows for the new options and `refine` |
| `doc/book/src/B-command-reference.md:59` | rules | guards and the `refine` action |
| `doc/book/src/A-full-grammar.md:12` | grammar | the new productions |

Adding a variant to `RAtom` makes the compiler list the other `match` sites in
`schedule.rs`, `saturate.rs` and `ematch.rs`. An `AbsGuard` binds nothing and
scans no relation, so it takes the arm that `RAtom::Pred` takes there.

## 7. Decisions left to the student

| Decision | Constraint |
|---|---|
| Exact fields of the §4 types | the type names exist, and `AbsValue` and `AbsTest` name their domain |
| Integer literal syntax | decimal of any size is required (`ok_refine_values` uses 30 digits); `#x` and `#b` forms are optional |
| `:range` as a table entry or as sugar for a rule | a desugared rule joins the default ruleset only and fires only during `run`; a table entry has neither limit |
| How a guard fails while values are top | the query still sortchecks, resolves and compiles; the guard test is the step that fails |
| Where the warning is raised | once per program, visible through `Interpreter::warnings()` |
| Signed bounds in VALUE | not required; `sbounds` is enabled but has no surface value in this PR |
| `:interp` with a primitive name | whether `:interp IBig::+` is accepted beside the SMT-LIB name `+`, so each operator is written once, next to the primitive it abstracts (§2.1) |

## 8. Acceptance criteria

- `cargo test -p semi-persistent-egraph --test abs_syntax -- --ignored` passes;
  the PR then removes the `#[ignore]` from `egraph/tests/abs_syntax.rs`.
- The 9 `ok_*` programs and the 26 `err_*` programs in `egraph/tests/egg/abs/`
  are unchanged, except where the student and the reviewer agree on a message.
- `cargo test -p semi-persistent-egraph --test egg_tests` and the rest of the
  workspace tests pass with no fixture changed.
- `parser.rs` unit tests cover each form of §2 and the order of `:interp` and
  `:domains`.
- `git grep 'TODO(abs-surface-syntax)'` prints nothing.
- The command reference, the language guide and the full grammar describe
  every form of §2 and the warning of §5.
- `cargo fmt --all --check`, `cargo clippy --workspace --all-targets -- -D
  warnings` and `bash scripts/check-oss-scaffold.sh` pass.

The runner in `abs_syntax.rs` reads the directives of `egg_tests.rs` (`EXPECT`,
`MESSAGE`, `WARNING`) and walks `tests/egg/abs/`. `egg_tests.rs` registers its
programs one by one and walks only `doc/book/examples/`, so it does not run
these programs.

## 9. References

- Design: [eclass-analysis.md §5](eclass-analysis.md#5-choosing-domains-per-sort)
  (domains per sort), [§6](eclass-analysis.md#6-propagation-rules) (the three
  tiers of propagation), [§10](eclass-analysis.md#10-acceptance-criteria) (the
  acceptance criteria of the whole analysis), and
  [§13.4](eclass-analysis.md#134-transfers-for-flat-a-ac-and-aci-nodes) (why
  `:interp` excludes `:assoc`).
- Sibling branches: `abs-domain-registry` (PR 4: the registry of carriers,
  domains and operators that replaces the stub list), `abs-class-storage`
  (PR 2: the class-layer pool in `containers-verus` that stores the values),
  and `abs-saturation-engine` (PR 3: executes what this PR declares).
- Existing guard machinery: `Atom::Pred` in `compile.rs`, `RAtom::Pred` and
  `PredGuard` in `resolve.rs`, `Step::CheckPred` in `schedule.rs`.
