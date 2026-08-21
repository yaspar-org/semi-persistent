# Proof certificates for anti-unification

This specification defines an independently checkable soundness certificate for
an anti-unification result. Generic proof-path export exists today; the
AU-specific projection certificate and checker described here do not.

Optimality is deliberately separate. A projection certificate proves that the
reported term generalizes both inputs. The exact solver's optimality boundary is
documented in [`../design/19-anti-unification.md`](../design/19-anti-unification.md#96-target-optimum-theorem-and-current-proof-boundary).

## 1. Certificate statement

For `anti_unify(t1, t2) = t`, every fresh variable in `t` names a pair of
e-classes `(cl, cr)`. A certificate contains:

```text
AuCertificate {
    result: t,
    left_substitution: s1,
    right_substitution: s2,
    left_chain:  proof(t*s1 = t1),
    right_chain: proof(t*s2 = t2),
}
```

The checker accepts only if both substitutions are total for the variables in
`t` and both equality chains are valid in the declared theory. Its soundness
postcondition is:

```text
check(cert) == true
    ==> eq_e(substitute(cert.result, cert.left_substitution), t1)
     && eq_e(substitute(cert.result, cert.right_substitution), t2)
```

`eq_e` includes registered ground axioms, registered rewrites under
substitution, congruence, and the declared A/AC/ACI/unit/nilpotent/inverse laws.

## 2. Available proof data

With `PROOFS = true`, every merge carries a `Justification`. The proof forest
can explain equality as a sequence of steps and recursively expand ordinary
congruence. `EGraph::dump_all_proofs`, exposed by
`--proofs --dump-proofs FILE`, builds one Euler-tour LCA table and exports paths
from every node to its representative.

That data is not yet a complete AU certificate:

- `Rewrite` identifies a rule but does not carry the matched substitution.
- AC congruence expansion does not carry a multiplicity-preserving child
  matching.
- completion justifications name conclusions but not all inference premises.
- build-time canonization is definitional at hash-consing time and emits no
  proof steps.
- AU currently neither emits projection witnesses nor requests proof paths.

## 3. Canonization boundary

The checker treats canonicalization as a checked equational transformation. It
owns a small term canonizer implementing the declared laws: flattening,
deterministic sorting, multiplicity coalescing, unit removal, nilpotent
reduction, and inverse cancellation.

For every transformation the verified obligation is:

```text
eq_e(canon(term), term)
```

Completeness of canonicalization is not required. An incomplete checker may
reject a valid certificate; it must never accept an invalid one. This avoids
adding trace writes to the e-graph's node-construction path while keeping the
trusted boundary explicit. Differential tests should feed the production and
checker canonizers the same generated terms and require equal normal forms.

## 4. Certificate production

Production requires a scratch or replayable session:

1. Run saturation and AU with proof logging enabled.
2. Read the result term and its variable-to-class-pair map from `TermPool`.
3. Extract one witness term per variable on each side and instantiate both
   projections.
4. Materialize the projections before replaying the equalities that place them
   in the source classes.
5. Replay justified merges, rebuild, and assert that each projection reaches
   its source root.
6. Extract deep proof chains from each materialized projection to its input.
7. Restore the scratch state so certificate probes do not change the session.

Materializing after the graph is already merged is insufficient: child
canonicalization maps the projection directly onto existing representatives,
leaving only a reflexive path. The producer therefore needs the two-phase replay
above or must extract certificates before closure erases those distinctions.

## 5. Required justification content

The producer/checker boundary needs four additions:

| Requirement | Accepted design |
| --- | --- |
| Degenerate AC merges | explicit `UnitDrop`, `NilpotentClamp`, and `SingletonCollapse` justifications |
| Rewrite instance | checker-side rematching, or a logged matched node/substitution |
| Multiset congruence | checker recomputes a multiplicity-preserving bijection, or the log carries one |
| AC-completion inference | justification carries the premise node ids needed to reconstruct the overlap |

Checker-side reconstruction keeps the runtime log compact. Logged witnesses
remain an optional format extension for consumers that cannot or should not
repeat matching.

## 6. Verified checker structure

The checker is a pure Verus program over owned recursive datatypes:

1. A term datatype and a validated signature table.
2. A reified `EqDerivation` datatype with a validity predicate for reflexivity,
   symmetry, transitivity, congruence, axioms, rewrites, and algebraic laws.
3. A verified total order and deterministic child-sequence sort.
4. The checker-side canonizer with one soundness lemma per transformation.
5. Step checkers for ground axioms, congruence, and rewrite matching.
6. A chain fold whose postcondition composes valid adjacent steps.
7. The top-level `AuCertificate` theorem from section 1.

Reifying derivations is important: expressing transitive closure through raw
quantifiers creates unstable matching obligations, while a derivation value
gives each recursive check an explicit decreasing argument.

## 7. Delivery boundary

A first checker may reject completion-specific labels while accepting sessions
that use ordinary axioms, rewrites, congruence, and checker-side canonization.
Support for completion labels is added only after their justifications carry the
premises listed in section 5.

The producer remains untrusted by design. A producer defect yields a rejected
certificate; only the checker's implementation, equational specification, and
Verus trust boundary can affect sound acceptance.
