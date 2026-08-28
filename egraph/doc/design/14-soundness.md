# Chapter 14: Correctness Claims and Boundaries

[Ch 13: Literal Model](13-literal-model.md) · [Table of Contents](00-table-of-contents.md) · [Ch 15: Proof Logging](15-proof-logging.md)

This chapter states the supported correctness claims and their boundaries. The
engine derives equalities from explicit unions, instantiated user rewrites,
evaluation of externally-defined primitive operations on literals, and closure
under user-declared operator laws. Those laws include structural C/A/AC/ACI
canonization and, when declared, identity, nilpotence, cancellativity, and
explicit inverse-pair cancellation.

## 1. The theory, and the two properties

Fix an input set `S` of asserted ground equations and a set `R` of user rewrite
rules, read as equations. Let `=_T` be the semantic equality relation generated
by `S`, all well-sorted ground instances of `R`, and:

- the algebraic axioms of each user-declared operator: none for a plain operator;
  `f(x,y) = f(y,x)` for a C operator; `f(f(x,y),z) = f(x,f(y,z))` for an A
  operator; both for AC; and AC plus `f(x,x) = x` for ACI;
- each additional declared law: `f(x,e) = x` for an identity, `x^n = e`
  for nilpotence of order `n`, and `f(x,inv(x)) = e` for the shipped
  explicit inverse-pair facet;
- the conditional cancellation inference
  `f(x,z) = f(y,z) implies x = y` for an operator declared cancellative;
- the equational theory of the literal model: for every primitive operation `g`
  with evaluation function `eval_g`, the ground equations
  `g(v_1, ..., v_k) = eval_g(v_1, ..., v_k)` for all literal values `v_i`.

`=_T` contains the ground equalities that follow from those equations, declared
laws, successful literal evaluation, and conditional cancellation, closed
under reflexivity, symmetry, transitivity, and congruence. The engine derives a
mode-dependent subset of `=_T`. For closure claims below, let `E_now` be only
the ground equations already
asserted into the current e-graph: input unions, rewrite instances that have
actually fired, successful primitive evaluations, and completion consequences
already produced. A rebuild closes consequences of `E_now`; it does not by
itself enumerate every semantic instance of every rule in `R`.

**Soundness.** Every equality the engine asserts is in `=_T`. Concretely: at every
point during `rebuild`, the union-find relation is a subset of `=_T`. Nothing the
engine merges is false in the theory.

**Closure (mode- and outcome-dependent).** Every `rebuild()` return is closed
under `rebuild_congruence` over `E_now`. Here "plain congruence" includes
canonical C/A/AC/ACI representations plus local identity and nilpotent
normalization; it excludes the global completion rounds that superpose and
inter-reduce asserted equations. Explicit inverse pairs are canceled when they
are visible during construction, while inverse pairs formed only by later
merges require completion. This default closure is not full closure under all
of `=_T`. For AC/ACI operators, this chapter's stronger
claim is conditional: when opt-in eager completion reports
`CompletionOutcome::Converged`, the paper correspondence argues closure of the
materialized ground AC/ACI consequences of the equations present in the
e-graph, under its stated hypotheses. It does not imply that all user rules have
been saturated. `Disabled`, `GoalMet`, and `AbortedGrowthLimit` do not report
that completion fixpoint. Lazy completion may derive its installed goal and
restore without constructing a full closure.

Completeness is stated over *materialized* terms because the engine decides
equalities, it does not enumerate the (infinite) term universe. The boundary case,
an equality that requires a term no node represents, is the subject of §3.3 and
[Ch 9](09-pattern-matching.md); it is the AC-matching gap, not a congruence-closure
gap.

The two properties are independent, and they are not equally important. The
soundness invariant argued below is state-local: it does not depend on reaching
a fixpoint or on completion running. It is not yet a machine-checked e-graph
theorem (§4). Completeness is a fixpoint property and, for AC operators, the
stronger claim depends on a converged completion pass of the
[AC congruence completeness chapter](ac-congruence-completeness.md).

### 1.1 The trustworthy polarity

The two properties give the e-graph an asymmetric guarantee, and callers must rely
only on the sound direction:

- `find(g_1) = find(g_2)` (same e-class) is intended to mean `g_1 =_T g_2`:
  the terms are equal in the theory under the soundness argument below. This is
  the public contract, supported by finite tests but not yet machine-checked
  end to end.
- `find(g_1) != find(g_2)` (different e-class) does **not** mean `g_1 ≠_T g_2`. It
  means only that the engine has not derived the equality yet. The terms may still
  be `=_T`-equal by a consequence the current state does not witness.

So the only polarity a caller may trust is "same e-class implies equivalent."
"Different e-class" is not a disequality; reading it as "semantically distinct" is
a usage error. This is the standard reading of any congruence-closure or
saturation engine: equalities accumulate monotonically, and an absent equality is
absence of evidence, not evidence of absence. `(check (!= a b))` tests this
current non-membership after whatever work its configured mode performs; it
does not assert or maintain a semantic disequation. Only a separately justified
complete decision procedure for the relevant fragment could turn such a
negative result into semantic disequality.

Under the soundness invariant, incompleteness is a weakening, not an
unsoundness: an incomplete engine derives a subset of the entailed equalities,
never a superset. The AC completion pass enlarges that subset toward the
entailed set; with it off, the engine still decides every equality plain
congruence reaches and merely misses some AC consequences (§3.3). This is why completion
can default off, and why a growth-budget abort mid-completion (the divergence
backstop, reported as `CompletionOutcome::AbortedGrowthLimit`) leaves a sound,
  plain-congruence-closed state, without endangering any consumer that respects the
  polarity above. Before returning from this abort path, `rebuild()` drains the
  pending plain-congruence worklist.

## 2. Soundness

### 2.1 Literal evaluation

A primitive operation is declared by `LitOpDesc`:

```rust
pub struct LitOpDesc<V> {
    pub name: &'static str,
    pub arg_sorts: &'static [&'static str],
    pub ret_sort: &'static str,
    pub eval: fn(&[&V]) -> V,
}
```

`eval` is called during RHS application (Chapter 12) on the interned values of
the argument nodes, and its result is interned to a `LitValId`. Primitive
applications are evaluated directly rather than materialized as ordinary
e-nodes. Semantically, a successful evaluation uses the equation
`g(v_1, ..., v_k) = eval_g(v_1, ..., v_k)`.

This is sound under these conditions on the model and value type:

1. Whenever `eval_g` returns, its result is an extensional, deterministic
   function of the argument values, with no outcome-changing external state.
2. The value type's `Eq` and `Hash` implementations agree, so interning maps
   equal values to one `LitValId` and does not conflate unequal values.
3. `sort_of`, parsing, primitive signatures, and `is_truthy` agree with the
   intended external literal semantics.

Under these conditions the asserted equation is exactly an instance of the literal
model's equational theory, hence in `T` by definition. The conditions are
obligations on the externally-supplied model (`LitModel`), not on the e-graph; the
engine assumes a model that meets them and is sound relative to that model.

Literal nodes carry a `LitValId` and no e-node children. Two literal nodes with the
same `LitValId` are identical by interning, so a literal node never recanonicalizes
during rebuild and never participates in congruence as a parent. Its class can
nevertheless be merged by an explicit union, an instantiated rewrite, or another
justified equality; evaluation is not the only source of equality involving a
literal.

The overflow variants (`checked`, `wrapping`, `saturating` arithmetic in
`MachineModel`) are distinct primitive operations with distinct `eval`
functions. Wrapping and saturating operations return for their declared input
sorts. Checked arithmetic, division by zero, invalid powers, and some string
index arithmetic can panic; the trait does not encode totality. A successful
call is deterministic under the model obligations above, but progress for every
well-sorted input is not guaranteed. `is_truthy`, used by `:when` guards to read
a literal as a boolean, is another external model function covered by those
obligations.

### 2.2 Congruence over plain operators

For plain operators the engine merges `f(a_1, ..., a_k)` and `f(b_1, ..., b_k)`
when `find(a_i) = find(b_i)` for all `i`. This is the congruence inference rule,
which is sound in equational logic: if each argument pair is already `=_T`, the
applications are `=_T`. Recanonicalization performs exactly this: it replaces each
child by its representative and merges nodes that become syntactically identical
(Chapter 5). No equality is asserted that is not a congruence consequence of merges
already performed, so by induction the union-find stays within `=_T`.

### 2.3 Canonicalization for C, A, AC, ACI

For an operator with algebraic axioms, the node stores a canonical form of its
arguments, and two nodes merge when their canonical forms coincide. Soundness
requires that the canonical form is sound for the axioms: if two argument tuples
have the same canonical form, the corresponding applications are equal under the
operator's axioms.

- **C**: the canonical form sorts the two arguments by class id. Two C-nodes with
  the same sorted pair are equal by commutativity.
- **A**: the canonical form is an order-preserving sequence. `AssocDir::Left`
  flattens the first-child spine (the sequence denotes a left fold),
  `AssocDir::Right` flattens the last-child spine (a right fold), and
  `AssocDir::Both` flattens every nested same-op child under full associativity.
  Flattening a selected spine preserves the fold denoted by the source term;
  two A-nodes with the same sequence therefore denote the same application.
- **AC**: the canonical form flattens and represents the arguments as a multiset
  (sorted with multiplicities). Two AC-nodes with the same multiset are equal by
  associativity and commutativity. Flattening on the class summand-form, not the
  union-find representative, is required for this to be a function of the e-graph
  state; see [AC chapter §6c](ac-congruence-completeness.md).
- **ACI**: as AC, with multiplicities collapsed to presence (a set), sound by the
  additional idempotence axiom `f(x,x) = x`.

In each case the canonical form is sound: equal canonical form implies the
applications are provably equal from the axioms. The converse (every axiom-equal
pair reaches the same canonical form) is a completeness statement, treated in §3.

### 2.4 AC completion

The completion pass for AC operators (superposition and collapse, see the
[AC chapter §6](ac-congruence-completeness.md)) asserts additional equalities
beyond direct congruence. Each is sound:

- A superposition merges the two reducts of a critical pair `+AB`. Both reducts
  equal `+AB` modulo the existing rules, so they are `=_T` (AC chapter §6 (B), and
  the soundness invariant of §12 there).
- Collapse (inter-reduction) rewrites a node by a contained smaller rule and merges
  the result into the node's class. The rewrite is an instance of the substitution
  the AC axioms entail, so the merged equality is `=_T`; collapse then retires the
  node from the active rule set without asserting anything further (AC chapter §6b).
- A semantic-axiom critical pair merges two reducts obtained from the same
  overlap between an asserted rule and the declared idempotent or nilpotent
  law. Each reduct is therefore equal to that overlap in `=_T`.
- Cancel-closure removes a common summand only for an operator declared
  cancellative. Its merge is justified by the conditional cancellation
  inference included in `=_T`.
- Inverse-pair normalization removes represented `x`/`inv(x)` pairs only for
  an operator declaring that inverse and its identity, so the removed pair is
  equal to the unit in `=_T`.

The soundness invariant is stated and argued abstractly in
[AC chapter §12](ac-congruence-completeness.md): every rule and every merge
satisfies `=_T`, preserved by each operation, with no appeal to termination or to
reaching a fixpoint. The argument therefore does not depend on whether completion
is enabled or converges. Focused fixtures and invariant checks provide finite
executable evidence for that correspondence; it is not currently a
machine-checked e-graph theorem.

### 2.5 Multiple AC symbols: why the rule-RHS storage is per-op

Completion reads each rule's right-hand side from per-class data: the class's minimal
monomial plus an `atomic` flag (AC chapter §9a). A single `min_monomial` slot per class
would be unsound in the presence of two AC operators: a class may hold monomials of two
different AC operators at once (assert `a+b = a*b` and the class contains both a `+`-node
and a `*`-node), each with its own minimum. One slot cannot hold both minima, so a
`+`-rule could read the `*`-monomial as its RHS: a wrong closure, not merely a weaker
one.

The engine therefore stores the per-class minima as a per-op POOL row: one column per
completion operator (MSet and Set alike, in registration order), merge-folded
element-wise, behind the `min_mono(op, class)` accessor (see
`ac-algebraic-properties.md`, the storage chapter). A `+`-rule can only ever read the
`+` column, so the conflation hazard is structurally unrepresentable. The completion
algorithm itself needs nothing further for multiple symbols: it already runs per-op
(superposition and normalization filter on the rule's op), and the union-find handles
the one cross-operator interaction: a constant equal to monomials in two operators is
just one e-class holding both nodes, with the same `find`, no fresh constant needed
(Kapur's shared-constant case).

## 3. Completeness

### 3.1 Literal evaluation

For literals, the relevant completeness statement is that two successfully
evaluated ground primitive applications returning equal model values intern the
same `LitValId`, so their literal nodes are identical and share a class.
Completeness here is relative to evaluation returning and to the external
`Eq`/`Hash` contract. The engine does not decide equalities that hold in the
model only under quantified laws the model does not expose as evaluation (for
example `x + 0 = x` as a law over symbolic `x`); those require user rewrite
rules.

### 3.2 Plain congruence closure

Plain congruence closure is complete for the ground word problem generated by
the currently asserted ground equations. The argument
([AC chapter §1](ac-congruence-completeness.md)) rests on the materialization
invariant: the input is finitely many equations over finitely many terms, the term
universe is closed under subterms, and every subterm is a materialized node. The
congruence rule therefore never needs a term that does not already exist, so
recanonicalizing to a fixpoint decides every congruence consequence. This is
standard and is the baseline the AC case is measured against.

### 3.3 Flattening alone is incomplete for AC

Flattening an AC application into a multiset node erases the intermediate sub-sum
subterms. The flattened term universe is no longer closed under subterms (the
sub-sums of `+{a,b,c}` under associativity include `+{a,b}`, `+{b,c}`, `+{a,c}`,
none of which is materialized), so the materialization invariant fails and plain
recanonicalization misses AC consequences. The [AC chapter §2–§5](ac-congruence-completeness.md)
develops this in full: recanonicalization propagates equalities on the *atoms* of a
multiset but not on its *sub-multisets*, and the missed equalities are exactly those
that require substituting a known sub-sum.

The same boundary appears on the matching side ([AC chapter §5b](ac-congruence-completeness.md),
[Ch 9](09-pattern-matching.md)): a scalar pattern variable that must bind a sub-sum
with no node of its own is outside the e-matching relation. That residual case
requires materializing a sub-sum no equation justifies and is not claimed; it is the
open term-valued AC-matching extension (AC chapter §11), separate from
congruence completeness. Classical AC unification is a broader problem; the
implemented operation is matching a pattern against a ground e-graph subject.

### 3.4 Conditional completion claims by operator family

C canonicalization is complete on its own relative to the current ground
equations: commutativity is decided by sorting the two arguments, so
commutativity-equivalent applications reach the same canonical form directly,
and no completion pass is needed.

A canonicalization is not complete. Build-time flattening splices a
pure-sequence child into its parents, which erases the class reference, and a
class can never become pure late because merges only add members and an atom
member never leaves. The one escape is therefore two pure-sequence classes
merging: the class then holds two spellings of one sequence, an equation the
parents that spliced different spellings cannot see through congruence. Under
either completion mode the A-only inter-reduction round targets this observed
merged-spellings loss mode, rewriting contiguous occurrences of the larger
spelling to the shortlex-least one
([AC chapter §14](ac-congruence-completeness.md)). Focused tests cover that
case; they do not prove it is the only loss mode. The word problem for finitely
presented monoids is undecidable, so no algorithm can both terminate on every
arbitrary A-only presentation and decide every equality. The implemented round
therefore has no unqualified general decision-procedure claim. What it derives
is sound; the documented repair is not a proof of complete A closure.

AC and ACI require completion for the stronger closure claim. Reading each AC
node as a rewrite rule, the missing
operations are superposition (which derives the cross-rule equalities, AC chapter §6
(B)) and collapse (which keeps the rule set a reduced antichain so the procedure
stays within the intended completion construction, AC chapter §6b). If the
implementation reaches `CompletionOutcome::Converged` and the correspondence
argument's hypotheses hold, the resulting canonical system is argued to make
`nf_R` decide the ground AC consequences of the asserted equations
(AC chapter §10, §12). This is not a claim that unfired user-rule instances
have been enumerated. ACI is AC plus idempotence; Kapur (FSCD 2021
§4) gives the additional critical pair idempotence requires, and the same
completion structure is argued to apply.

Nilpotent operators use the multiset representation with counts reduced modulo
their declared order. Completion additionally generates the semantic-axiom
critical pairs required by that law. Cancellative operators add cancel-closure
and cancellative critical pairs. Those are implemented correspondences to
Kapur's constructions, supported by focused fixtures and finite invariant
checks, not machine-checked completeness theorems. The validation obligation
for cancellative completion when constants enter the pool late remains open.

Inverse support is narrower: the implementation cancels explicit
`x`/`inv(x)` pairs that are represented in the graph. It does not implement
signed coefficients, triangular reduction, or full Abelian-group completion.
`CompletionOutcome::Converged` therefore reports the implementation's
full-round fixpoint, not completeness for the general Abelian-group word
problem.

This completeness is a fixpoint property and, unlike soundness, depends on
completion running and converging. The argument is on paper, adapting Kapur, and not
yet discharged in a proof assistant; the verification plan is in
[Future Work](A3-future-work.md), and the engine-level invariant checks that
confirm the rule set is reduced at a fixpoint are in the
[AC completion spec](ac-completion-spec.md).

## 4. What is proved, argued, and assumed

- **Assumed (model obligation).** Successful `eval` and `is_truthy` calls are
  extensional and deterministic, sort classification is coherent, and the
  literal value's `Eq`/`Hash` implementations agree (§2.1). Totality is not
  guaranteed by the trait. These are conditions on the externally-supplied
  `LitModel` and value type, outside the e-graph.
- **Argued, intended for mechanical proof.** Congruence and canonicalization
  soundness (§2.2, §2.3) and AC completion soundness (§2.4) follow the invariant of
  [AC chapter §12](ac-congruence-completeness.md). Soundness is the first target of
  the Verus verification plan.
- **Argued on paper, open mechanically.** AC/ACI completeness (§3.4) adapts Kapur
  and rests on the critical-pair lemma, Dickson's lemma, and Newman's lemma. It
  applies only to a converged eager completion over the stated model and is not
  yet machine-checked.
- **Standard argument plus finite tests, not a local formal proof.** Literal
  evaluation under the model obligations (§3.1), plain ground congruence closure
  (§3.2), and C canonicalization (§3.4) have the stated completeness arguments
  without a completion pass. A canonicalization has only the documented
  merged-spellings repair under completion; no procedure closes the general
  finitely presented monoid word problem (§3.4).

---
[Ch 13: Literal Model](13-literal-model.md) · [Table of Contents](00-table-of-contents.md) · [Ch 15: Proof Logging](15-proof-logging.md)
