<!--
Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
SPDX-License-Identifier: Apache-2.0
-->
# Surface Syntax for Abstract Values: Design

**Status**: design for the hand-off PR `abs-surface-syntax`; nothing here is
implemented. This document states what each new form means and why it is sound.
[abstract-syntax-task.md](abstract-syntax-task.md) states what to change and where.
The engine that gives the forms their effect is
[eclass-analysis.md](eclass-analysis.md) and the hand-off `abs-saturation-engine`.

## 1. What a program can say

The new syntax lets a program state four kinds of fact:

| Fact | Form | Example |
|---|---|---|
| A sort denotes concrete values, and which domains track them | `:interp` and `:domains` on `sort` | `(sort Int :interp int :domains (interval))` |
| A symbol denotes a concrete operation | `:interp OP` on `function` or `constructor` | `(function add (Int Int) Int :interp +)` |
| A term's value lies in a set | `(refine t VALUE)`, `:range` | `(refine (x) (interval 0 255))` |
| A rule applies only when a value lies in a set | abstract guards in rule bodies and `:when` | `(within y 0 9)` |

Today none of these can be said. A class has no concrete meaning beyond its
literal, and the only conditions a rule can test are patterns and primitive
predicates over literal values (`:when ((IBig::< a b))`).

## 2. The meaning of an analysed class

A program denotes the set of its models: interpretations of every class that
satisfy every asserted equality. The engine keeps, for each class of an analysed
sort, an abstract value `v`, and maintains one invariant:

> In every model, the concrete value of the class lies in γ(v).

γ is the concretization of the domain (`abstract-domains/doc/domain-traits.md`).
Every form below either changes what γ(v) may be (a declaration), or shrinks `v`
(a seed, a transfer, a meet on merge), or reads `v` (a guard). A form that
shrinks `v` must keep the invariant, and the table in §8 says who guarantees it.

Two consequences shape the design:

- **Shrinking is monotone.** Values only shrink during a run, and an empty value
  means the program has no model (a conflict). A guard that holds keeps holding.
- **Top is always sound.** A class whose value is top claims nothing. This is
  why an unanalysed sort, a disabled domain, and the interim semantics of §9 are
  all sound by construction.

## 3. Sorts: carriers and domains

```lisp
(sort Int  :interp int        :domains (interval congruence nonzero))
(sort BV32 :interp (bitvec 32) :domains (ubounds bits))
(sort Bool :interp bool)                 ; the carrier's default domains
(sort Expr)                              ; no :interp: not analysed
```

**`:interp C`** declares the carrier: every class of the sort denotes exactly one
element of `C` in each model. The carrier fixes the concrete operations, the
available domains, and how literals enter the analysis.

**`:domains (D ...)`** selects which components of the sort's abstract value are
tracked. The value is a reduced product of the selected domains
(`abstract-domains/doc/reduced-product.md`). A component that is not selected
stays at top, so any subset is sound; the choice trades precision for cost.
Omitting `:domains` selects the carrier's default set, and `:domains ()` turns
the analysis off for the sort.

### 3.1 Carriers and the literal model

Every carrier corresponds to a literal sort of the `LitModel` where one exists.
This correspondence is what connects abstract values to the literals a program
already writes.

| Carrier | Literal sort | Domains, by name (backing type) | A literal `k` enters as | `:interp` operators abstract |
|---|---|---|---|---|
| `int` | `IBig` | `interval` (`IntervalZ`), `congruence`, `nonzero` (fields of `FactsZ`) | `[k, k]`, residue of `k`, nonzero iff `k != 0` | the `IBig::` primitives |
| `(bitvec 64)` | `u64`; `i64` under signed operators | `ubounds` (`Interval<u64>`), `sbounds`, `congruence`, `bits` (Tnum), fields of `Facts<u64>` | `[k, k]`, Tnum `(k, 0)` | the `u64::` and `i64::` primitives |
| `(bitvec N)`, N in 8, 16, 32, 128 | none yet | the same fields of `Facts<W>` | no literal until a literal sort of width N exists | transfers exist, no primitive |
| `(bitvec N)`, other N | none | none: the value is always top | no literal | none |
| `bool` | `bool` | `bool` (`Bool4`) | `True` or `False` | the `bool::` primitives |
| none | `RBig` | none | not analysed | none |

Classes reach the analysis in three ways:

1. **Literal sorts are analysed implicitly.** A class of sort `IBig`, `u64` or
   `bool` already denotes one concrete value, so it is analysed without a
   declaration, with the default domains of its carrier. A literal node `k`
   starts at its singleton. `:domains` on a literal sort only narrows the set.
2. **User sorts declare a carrier.** `(sort Int :interp int)` makes every class
   of `Int` denote an integer. Its values come from seeds, from transfers of its
   `:interp` operators, and from embeddings.
3. **Embeddings connect the two.** A unary constructor tagged `:interp embed`
   injects a literal sort into a user sort with the same carrier:

   ```lisp
   (sort Int :interp int)
   (constructor Num (IBig) Int :interp embed)   ; the class of (Num k) denotes k
   ```

   The class of `(Num 5)` starts at `[5, 5]`. Without an embedding, the literal
   inside a wrapping constructor is opaque to the analysis. Sortcheck rejects an
   embedding whose argument is not the literal sort of the result's carrier.

## 4. Functions: propagators

```lisp
(function add (Int Int) Int :interp +)
(function lt  (Int Int) Bool :interp <)
(function ite (Bool Int Int) Int :interp ite)
(function bvand (BV32 BV32) BV32 :interp bvand)
```

**`:interp OP`** declares that the symbol denotes the concrete operation `OP` on
the carriers of its signature. For every node `add(a, b)` in a class `c`, every
model satisfies `c = a + b`. Two inferences follow, and the engine applies both:

- **forward**: the value of `c` shrinks to its meet with `add#(val(a), val(b))`;
- **backward**: the values of `a` and `b` shrink by the inverse transfer
  (`val(a) := val(a) ⊓ (val(c) − val(b))`), where the operator has one.

The user does not write the transfers. They are the verified transfers of the
domain registry (hand-off `abs-domain-registry`), and their soundness is proved
in `abstract-domains`. The user's only obligation is that the symbol means the
operation it names, which sortcheck enforces on the signature: `:interp +` on a
function from `(Int Int)` to `Bool` is a sort error.

The operator names are SMT-LIB's (`+`, `<`, `ite`, `bvadd`, `bvslt`). Each
abstracts the primitive in the table of §3.1; `+` on `int` is `IBig::+`.

**A symbol without `:interp`** is uninterpreted. Its classes still carry values,
which they receive from seeds, from merges with other classes, and from rules.
A defined symbol needs no transfer of its own:

```lisp
(function clamp (Int Int Int) Int)
(rewrite (clamp x lo hi) (ite (lt x lo) lo (ite (lt hi x) hi x)))
```

Once the rewrite fires, `clamp(...)` and the `ite` term share a class, and the
transfers of `ite` and `lt` propagate through it in both directions.

**`:range (lo hi)`** on a function states that every result lies in
`[lo, hi]`, whatever the arguments. It is a fact the user asserts, not one the
engine proves, so it is trusted like a rewrite rule. It is shorthand for
`(refine (f x ...) (interval lo hi))` on every node of `f`.

## 5. Seeds: stating a value

```lisp
(constructor Leaf (IBig) BV32)
(refine (Leaf 5) (interval 0 255))         ; leaf 5 is an unsigned char
(refine (Leaf 7) (bits :val 0 :mask 3))    ; leaf 7 is one of 0, 1, 2, 3
(refine (x) (congruence 1 2))              ; x is odd
```

**`(refine t VALUE)`** asserts that, in every model, the value of `t` lies in
γ(VALUE). The engine builds `t` if needed and shrinks its class's value to the
meet. A seed is an assertion in the same sense as `(union a b)`: it constrains
the models, and the user is responsible for it being intended. An empty meet is
a conflict, which reports that the seeds and the equalities have no model.

VALUE is a literal of one of the sort's enabled domains:

| VALUE | γ(VALUE) | Domain it needs |
|---|---|---|
| `(interval lo hi)` | integers `lo` to `hi`, both included | `interval` (Int), `ubounds` (bit-vectors) |
| `(bits :val V :mask M)` | values equal to `V` on every bit outside `M` | `bits` |
| `(congruence r m)` | values equal to `r` modulo `m` | `congruence` |
| `(nonzero)` | every value except 0 | `nonzero` |
| `(true)`, `(false)` | one Boolean | `bool` |

A seed whose domain is not enabled on the sort is a sort error rather than a
silent no-op: the program said something the configuration cannot record.

The CBMC corpus is the first user. Its leaves carry C types in comments
(`unsigned char`, `int`, `_Bool`), and each type becomes a seed: an
`unsigned char` leaf gets `(interval 0 255)`.

## 6. Conditional facts: refine in rule heads

```lisp
(rule ((= r (scale x)) (within x 0 9))
      ((refine r (interval 0 99))))
```

`refine` in a rule head asserts the fact for every match. Its soundness is the
user's, as for any rule head: the rule above is sound if `scale` multiplies by at
most 11 on that range. It goes through the same meet and conflict path as a seed.

## 7. Guards: reading a value

```lisp
(rewrite (Div x x) (One) :when ((nonzero x)))
(rule ((= r (f y)) (within y 0 9)) ((union r (g y))))
```

| Guard | Holds when |
|---|---|
| `(within x lo hi)` | γ(val(x)) ⊆ [lo, hi] |
| `(nonzero x)` | 0 ∉ γ(val(x)) |
| `(known-bits x V M)` | γ(val(x)) ⊆ γ(`(bits :val V :mask M)`) |

A guard holds when every concrete value the class may take satisfies it, so it
is an entailment test, not a possibility test. This has two consequences:

- **Soundness**: a rewrite guarded by `(nonzero x)` fires only where `x ≠ 0` in
  every model, so it adds an equality the models already satisfy.
- **Monotonicity**: values only shrink, so a guard that holds keeps holding.
  A guard that becomes true through a value change, with no node created and no
  class merged, must still re-fire the rule under semi-naive evaluation; the
  engine hand-off records this obligation.

Abstract guards differ from the existing primitive guards. A primitive guard
(`(IBig::< a b)`) evaluates a concrete operation on literal values bound by the
match. An abstract guard tests the abstract value of a class, which may stand
for many values.

## 8. What is verified and what is trusted

| Form | Who guarantees the invariant of §2 |
|---|---|
| `:interp` and `:domains` on a sort | nothing to guarantee: they only select what is tracked |
| `:interp OP` on a symbol | the verified transfers of `abstract-domains`; sortcheck checks the signature |
| `:interp embed` | the singleton lift, verified with the domain; sortcheck checks the sorts |
| merge of two classes | the verified meet |
| `refine` (seed or rule head), `:range` | the user, as for `union` and rule heads |
| guards | the verified inclusion test of the domain |

The new syntax adds no trust beyond what rule heads and `union` already carry.

## 9. Behaviour until the engine exists

This PR implements parsing, sortchecking and lowering only. Until
`abs-saturation-engine` lands, every abstract value stays top: guards never
hold, and `refine` and `:range` record nothing. This is sound, since top claims
nothing, and a program written for the analysis runs today with the same result
it would have with every domain disabled. One warning per program says the
analysis is not active.

## 10. Example

```lisp
(sort Int  :interp int :domains (interval))
(sort Bool :interp bool)
(constructor Num (IBig) Int :interp embed)
(constructor B (bool) Bool :interp embed)
(function add (Int Int) Int :interp +)
(function lt  (Int Int) Bool :interp <)
(constructor x () Int)

(refine (x) (interval 0 9))                 ; seed: x in [0, 9]
(let y (add (x) (Num 1)))                    ; forward: y in [1, 10]
(let c (lt y (Num 11)))                      ; forward: c is true
(rewrite (lt v w) (B true) :when ((within v 0 10) (within w 11 11)))
(run 1)
(check-eq c (B true))
```

Once the engine lands, the check holds twice over. The class of `c` is the
singleton `true`, so it merges with `(B true)` (eclass-analysis.md §8). The
guarded rewrite also fires, because both guards hold. Until then, the guards
never hold, no merge happens, and the check fails: the program shows the
difference the analysis makes.

## 11. References

- [eclass-analysis.md](eclass-analysis.md) §5 (sorts), §6 (propagation tiers),
  §8 (derived merges), §10 (acceptance).
- [abstract-syntax-task.md](abstract-syntax-task.md): grammar, sortcheck errors,
  lowering, change sites, acceptance tests.
- `abstract-domains/doc/domain-traits.md` (γ, `Domain`), `reduced-product.md`.
- Hand-offs: `abs-class-storage` (where values live), `abs-saturation-engine`
  (what propagates them), `abs-domain-registry` (which domains and transfers
  exist).
