# Proof certificates for anti-unification

Defines what a proof certificate for an AU result is, inventories what the
existing proof log can and cannot justify, and decides how the untraced AC
canonization steps get discharged: by a checker-side canonizer, not by
instrumenting the canonization paths. It is a design record, not a status
page: nothing in this document is implemented in the AU module today, and
`grep -rn "explain\|Justification" egraph/src/au/` confirms AU neither reads
nor writes the proof log.

## 1. The certificate

A result of `anti_unify(t1, t2)` is a term `t` over the signature extended
with fresh variables, where each variable stands for a pair of e-classes
`(cl, cr)`. The certificate presents the result as

```
proof_AU(t1, t2) = (t, s1, s2, chain1, chain2)
```

where `s1` maps each variable to a witness term extracted from its left
class, `s2` to a witness from its right class, and `chain1`, `chain2` are
equality proofs for `t*s1 ~ t1` and `t*s2 ~ t2` in the e-graph's theory:
ground rewrites, asserted unions, and the AC/ACI/unit/nilpotent/inverse
axioms of the declared operators. Optimality (that `t` is a least general
generalization) is not part of the certificate; the certificate witnesses
soundness only, because soundness is what a consumer of the generalization
needs and optimality has no small witness.

The membership half of this already exists without proofs: the metamorphic
suite materializes both projections of every AU result and asserts they
re-`find` into the source classes (`egraph/tests/au_metamorphic.rs:564-586`).
The certificate adds the equality chains to that check.

## 2. What the proof log records today

Proof mode is the const generic `PROOFS` on `EGraph`; every merge under it
must carry a `Justification` (unjustified `merge` panics,
`containers-verus/src/eclasses.rs:2234`). The variants
(`egraph/src/union_find.rs:9-54`) and what each payload suffices to check:

| variant | payload | independently checkable? |
|---|---|---|
| `Axiom { axiom_id }` | id into the union registry | yes: the registry stores the asserted `(lhs, rhs)` pair (`egraph/src/egraph.rs:298`) |
| `Rewrite { rule_id }` | rule id only | no: no substitution and no matched instance, so the checker must re-run matching to validate the step |
| `Congruence { node_a, node_b }` | the two collided node ids | partially: `explain_deep` recovers pre-canonization children from the copy-on-write history and recurses (`egraph/src/egraph.rs:1022-1061`), but see the AC caveats below |
| `ACSuperposition`, `ACInterReduction`, `ACAxiomCP`, `Cancellative`, `InverseCancel` | the two materialized normal-form node ids | no: the step names its conclusion, not its premises (`egraph/src/egraph.rs:2087-2106`), so checking means re-running the critical-pair inference |

Extraction produces a flat ordered list of `(from, to, justification)`
triples: a path through the proof forest
(`containers-verus/src/union_find.rs:1579-1631`), with `explain_deep`
splicing child-pair sub-chains after each congruence step.

## 3. Canonization is not traced, and the log cannot see it

The question this document exists to answer: does the log trace AC
canonization? No. `canon.rs`, `ac_invariants.rs`, and `multiset.rs` contain
no proof-mode code. On the build path (`EGraph::add`,
`egraph/src/egraph.rs:479-700`) an AC node is flattened, sorted, coalesced,
unit-dropped, nilpotent-clamped, and inverse-cancelled before hash-consing;
two AC-equal terms therefore intern to the same `ENodeId` and their
explanation is the empty chain. The suite pins this as intended:
build-time canonization is definitional equality at the hash-cons level, and
the empty chain is reflexivity (`egraph/tests/ac_matrix.rs:43-51`).

Three consequences follow for certificates, beyond the empty chain itself:

- **Degeneracy merges after rebuild are mislabelled.** When recanonization
  empties a monomial or reduces it to a singleton, the resulting equality is
  pushed through the collision queue and logged as
  `Congruence { node, unit_or_child }` (`egraph/src/egraph.rs:1306-1394`).
  The label is wrong: no congruence happened, an AC unit/nilpotency law did.
  `explain_deep` then tries to pair an MSet node's children against a leaf's
  and emits nothing.
- **AC congruence expansion has no multiset witness.** `explain_grouped`
  (`egraph/src/egraph.rs:1063-1103`) sorts both child lists by `find` and
  merge-joins; unmatched children are skipped silently and multiplicities
  are dropped (`egraph/src/egraph.rs:1112-1117`). The expansion is a
  heuristic for producing sub-goals, not a bijection certificate for
  multiset equality.
- **History recovery is load-bearing.** Child-wise expansion depends on the
  copy-on-first-recanonization history in the node caches
  (`egraph/src/caches.rs:222-228`, `:502-519`); any consumer of chains
  inherits that dependency.

## 4. Decision: discharge canonization in the checker, do not log it

Two designs were on the table.

**Log every canonization step.** Instrument `add` and `recanonize_node` to
emit one step per applied law: an associativity flatten, a commutativity
permutation witness, a unit drop, a nilpotent clamp, an inverse
cancellation. The checker then works over the bare term algebra with purely
syntactic steps. Rejected for now because the cost lands on the hottest path
in the system: `add` canonizes every node ever constructed, the log would
grow with term size for every add rather than with the number of merges, and
the change reaches into `caches.rs`/`node_store.rs` internals that the
verified-kernel parity work just stabilized. Revisit only if a consumer is
measured to need syntactic-only checking, for example export to a proof
assistant whose kernel cannot be extended with a canonizer.

**Checker-side canonization (chosen).** Declare equality of AC-canonical
forms judgmental for the checker: the checker ships its own small canonizer
(flatten, sort, coalesce, unit, nilpotent-clamp, inverse-cancel over an
explicit term representation) and validates a step `(from, to, just)` by
checking `canon(apply(just, from)) == canon(to)`. Silently-canonized
equalities then need no log entries at all, which is exactly why the current
log's silence is a compatible design rather than a defect. The price is
named: the checker's canonizer joins the trusted base, and it must agree
with `EGraph::add` on every law, including `mset_child_merge` coalescing and
the nilpotent modulus. That agreement is testable by construction: feed both
canonizers the same random term corpus and compare interned forms; drift
between them is a test failure, not a latent unsoundness, because the
checker rejects on disagreement.

This is the same argument the user-facing question anticipated: the
canonization and congruence steps are implicit, so someone re-infers them.
The decision is that the checker re-infers them once per step with its own
canonizer, instead of the e-graph logging them at every add.

## 5. Generation pipeline

Certificate generation uses only existing machinery plus one new module:

1. Compile the session with `PROOFS = true`. AU already threads the const
   generic through untouched (`egraph/src/au/egraph_api.rs:34`,
   `exact.rs:40`, `mcgs.rs:918`), so no AU signature changes.
2. Run AU. The result carries the backbone term and the variable-to-class-pair
   map in its `TermPool`.
3. Extract a witness term per variable and side with the existing extractor;
   instantiate `t*s1` and `t*s2`.
4. Roll the e-graph back to a state where the two sides are not yet equal,
   re-add both instances so they mint fresh nodes, replay the equalities,
   and rebuild. The rollback is the load-bearing step; see the correction
   below. Assert `find(t*s1) == find(t1)` and symmetrically: this is the
   metamorphic membership check re-used.
5. Extract `chain1 = explain_deep(add(t*s1), t1)` and `chain2`
   symmetrically.
6. Discard the probe with a final `restore` so the instance nodes do not
   leak into the session; proof-forest restore is covered by
   `proof_restore_test` (`egraph/src/egraph_proof_test.rs:1282`).

**Correction (2026-08-15): adding the instances to the merged graph yields
only empty chains.** The first version of this section ordered step 4 as
"add both instances after AU and let congruence closure merge the spine up
to the roots". The prototype (`egraph/tests/au_proof_certificates.rs`,
`certificate_trace_free_operators` phase A) measures what actually happens:
`add` canonicalizes children by `find` before hash-consing
(`egraph/src/egraph.rs:546-548`), so once the equalities are in, every node
of the instantiated projection interns onto an existing node of its class
and the whole instance collapses to the root's own node id. `add(t*s1)`
returns `t1`'s id, zero fresh nodes are minted, and the chain is
reflexivity. The membership assertion still holds but carries no
information, for the same reason the AC empty chain of section 3 does: the
equality became definitional at the hash-cons level. Do not cite the
original ordering. Non-trivial chains require the two-phase replay the
prototype's phase B performs: `mark` before the equalities are asserted,
run AU on the merged graph, `restore`, materialize the instances against
the still-distinct classes (a fresh spine is minted), re-apply the same
justified merges, rebuild, then extract the chains. A production generator
either runs this replay in a scratch session or interleaves certificate
extraction with saturation before the closure erases the distinctions.

The replayed trace falls short of a
checkable certificate at exactly the four points of section 2 and 3, which
orders the work:

| work item | change | size |
|---|---|---|
| C1 | new `Justification` variants for degeneracy merges (`UnitDrop`, `NilpotentClamp`, `SingletonCollapse`) replacing the mislabelled `Congruence` at `egraph/src/egraph.rs:1242-1314` | small, local |
| C2 | `Rewrite` steps checkable: either extend the payload with the matched node pair, or have the checker re-match the rule's LHS against `from` under its own canonizer | payload change is small; checker re-matching keeps the log unchanged |
| C3 | multiset congruence witness: record the child-class multiplicity matching (the transport assignment already computes one on the AU side) or have the checker recompute the bijection | checker-side recompute first, for the same reason as section 4 |
| C4 | AC completion steps carry premise node ids next to the conclusion pair | small payload change in `cc_round` |

C2 and C3 both have a log-side and a checker-side variant; the section 4
decision applies uniformly: prefer the checker-side variant until a consumer
is measured to need log-side payloads.

## 6. Postponed

- **Batch extraction via the Euler-tour LCA.** `lca.rs` implements O(1) LCA
  over the proof forest but nothing calls it; `explain` walks parent
  pointers with a seen-set (`containers-verus/src/union_find.rs:1598-1608`).
  Irrelevant at certificate-per-query scale; revisit when certificates are
  extracted in bulk, for example for a whole metamorphic corpus.
- **Optimality witnesses.** A certificate that `t` is least general would
  need the full action-space argument and has no compact form; the
  metamorphic oracle (constructed lgg, 2300 seeds) is the standing evidence
  for exact-solver optimality instead.

## 7. A verified checker in Verus: scope and estimate

Verifying the checker upgrades the section 4 decision. Section 4 priced the
checker-side canonizer as an addition to the trusted base; a Verus checker
removes that price, because the canonizer is proven sound against the
equational specification and only the specification itself remains trusted.
The producer (e-graph, AU, chain extraction) stays untrusted by design: a
bug there yields a rejected certificate, not an unsound acceptance.

**The theorem.** Define `eq_e(a, b)` as a specification-level equational
theory over a term datatype: the closure of the declared operator laws
(AC, ACI, unit, nilpotent-mod-n, inverse), the registered ground axioms,
the registered rewrite rules under substitution, congruence, reflexivity,
symmetry, transitivity. The checker is an executable function with the
single postcondition `check(cert) == true ==> eq_e(t*s1, t1) &&
eq_e(t*s2, t2)`.

**The scoping fact that makes this tractable: only soundness of the
canonizer is needed.** The obligation is `eq_e(canon(t), t)` per
transformation, proved by structural induction. Completeness
(`eq_e(a, b) ==> canon(a) == canon(b)`), which is the
confluence-and-termination-modulo-AC theorem and the expensive half of the
literature, is not required: an incomplete checker rejects some valid
certificates, which is a usability defect, not a soundness defect.

**Style note.** This is a different proof style from everything in
`containers-verus` today: the crate's effort went into flat-array
containers with arena aliasing and dynamic frames
(`doc/design/proof-attempts-log.md`, `09-arena-aliasing-dynamic-frames.md`),
and it contains no recursive-datatype structural inductions and no
`vstd::Multiset` use. The checker is the opposite shape: a pure function
over an owned recursive enum, no aliasing, no interior mutation. That is
the style Verus handles with `decreases` and per-constructor lemmas, and
it avoids the failure class the proof-performance playbook documents. One
playbook lesson does carry over: encode `eq_e` as a reified derivation
datatype with a validity predicate rather than a quantified transitive
closure, because symmetry and transitivity as raw quantifiers are a
matching-loop generator.

Work items, assuming the team's current Verus fluency:

| item | content | estimate |
|---|---|---|
| V1 | term datatype, signature attribute table, `eq_e` as derivation datatype + validity predicate | 3-5 days |
| V2 | total order on terms and a verified child-sequence sort (comparator totality and transitivity; insertion sort suffices, child lists are short) | ~1 week |
| V3 | canonizer and its soundness: flatten, sort (permutation-preserves-`eq_e` via adjacent transpositions), multiplicity coalescing over `(child, mult)` pairs, unit drop, nilpotent clamp, inverse cancel; mutual recursion with per-law lemmas | 2-3 weeks, the core |
| V4 | step checkers: ground axiom (canon-equal to the registered pair), congruence (recurse into child chains), rewrite (verified matcher producing a substitution with `canon(lhs*sigma) == canon(from)`) | ~1 week |
| V5 | chain glue (transitivity fold) and the top-level theorem | 2-3 days |
| V6 | untrusted producer side: serialize per-step terms out of the proof forest and node history into the certificate format | ~1 week, no proofs |

Total: five to seven person-weeks to a v1 that checks axiom, congruence,
rewrite, and canonization content. Calibration point: V3 is comparable in
shape to one of this crate's mid-size milestones (the M4 nested-restore
block in the proof-attempts log), and smaller than the B+tree work by an
order of magnitude in lines.

Out of scope for v1: chains containing the AC-completion labels
(`ACSuperposition`, `ACInterReduction`, `ACAxiomCP`, `Cancellative`,
`InverseCancel`). Those steps name conclusions without premises (section
2), so v1 rejects any certificate containing them; sessions that do not
run AC completion never produce them. Checking them needs work item C4
first, and then a verified overlap check per label: estimate another one
to two weeks, deferred until a certificate from a completion-running
session is actually wanted.
