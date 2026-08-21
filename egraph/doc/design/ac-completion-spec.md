# AC Completion: `min_monomial`, a matcher invariant, and implementation correspondence

A focused companion to [ac-congruence-completeness.md](ac-congruence-completeness.md) (the
full specification: e-graph as a rule set §0b, the fix §6, collapse §6b, per-class data §9a,
proof sketch §12). This does not restate it. It adds three things that document leaves
implicit, and fact-checks them against Kapur 2023 (the LMCS journal version of the FSCD'21
algorithm; §, Def, Lemma, Thm numbers below are Kapur's):

1. the intended `min_monomial` invariants and the finite diagnostics that check
   them (§9a defines `min_monomial`) (§1);
2. the binding-restore invariant the `(f (add x ..r1) (add y ..r2))` matcher join must
   maintain, over concrete nodes (§2);
3. a clause-by-clause implementation correspondence with Kapur's algorithm,
   together with the boundary between tests and an unproved theorem (§3).

Read every e-graph fact as a rewrite rule (main-doc §0b, Kapur §2.2): an AC node with
operator `+` and child multiset `M` in class `c` is the rule `+M → r(c)`; the union-find is
the constant-rule layer, where a class merge is a constant rule `d → e` rewriting one class
representative to the other. "Classes `c`, `d` are equal" means `find(c) = find(d)`: one
rewrites to the other under those constant rules.

---

## 1. `min_monomial`: the properties the engine must keep

The main doc §9a defines the per-class data: a class carries `find(c)` (the union-find tag,
not necessarily an AC monomial) and `min_monomial(c)` (the `≫_f`-least `+`-monomial of the
class, the rule RHS; `≫_f` is the admissible monomial order for op `f`: degree-lex,
total size, then lexicographic from the largest class id down, Kapur's deglex), and the rule RHS is: the **empty monomial** if `c` is the op's identity
(unit) class: Kapur's `f({}) = e`; rewriting with the atom `{e}` instead would leak unit
summands into reducts that normalization (which has no `f(x,e) = x` law) can never remove;
else `{c}` if `atomic(c)`, else `monomial_of(min_monomial(c))`. This
section does not re-derive that. It states four intended `min_monomial`
properties and identifies how each is supported. The finite diagnostics in §3
directly check (P2); the emission guard enforces (P3); (P1) and (P4) follow from
the storage construction and have focused regression coverage. They are not
collectively machine-checked invariants or a universal theorem. The section
also identifies the one place maintenance is weaker than Kapur's "reduced".

### 1.1 Properties (`c` has a `+`-node; `mono(g)` is `g`'s canonical child multiset)

- **(P1) Membership.** `min_monomial(c)` is a real AC node `g` with `find(g)=find(c)`, never a
  synthetic monomial.
- **(P2) Leximin (quality, checked property).** At a reported completion
  fixpoint, the intended property is
  `mono(min_monomial(c)) = min_{≫_f}{ mono(g) : g a +-node in c }`. Because rewriting strictly
  decreases `≫_f` and a canonical system gives every class member one shared normal form,
  that normal form should be the `≫_f`-minimum. `cc_min_used_nonminimal`
  checks this on the current finite state; it is not a universal theorem.
- **(P3) Orientation safety.** Completion emits `+M → r` only when the
  read-time `monomial_cmp(M,r)` guard returns `Greater`. Thus every rule the
  implementation actually emits is decreasing. This is weaker than claiming
  that a stored best-effort minimum is globally minimal at every intermediate
  state.
- **(P4) Existing-constant closure.** `mono(min_monomial(c))` is a multiset over existing class
  ids, never a fresh constant, so reading it as a RHS cannot grow the constant pool. Its
  violation (class-as-atom) is the one unbounded divergence (§6b).

### 1.2 Maintenance, and the gap from Kapur's "reduced"

`min_monomial` is updated on merge by scanning every completion-op column. Empty/equal
columns are constant-time; when both classes have distinct candidates in a column,
`fold_min_monomial` reads and compares both monomials. Thus a merge costs
`O(number of completion columns + total elements read from compared monomials)`, using
reusable buffers but not O(1) time. This is **best-effort on (P2) only**:
`monomial_cmp` reads `find` of children, which is mid-cascade during a merge, so the stored
min can be a non-minimal but valid sum until a later merge refreshes it. (P1), (P3), (P4)
are the intended storage properties, while the read-time **orientation
guard** (emit `+M → r` only if `monomial_cmp(M,r)=Greater`) is the executable
protection against a stale ordering decision.

This is precisely where we are weaker than Kapur. Kapur's **reduced** system (§3) requires
that **neither the left nor the right side** of any rule be reducible by the others; his
SingleACCompletion step 4(ii) fully normalizes each RHS. Our option (a) targets the LHS
half (the antichain used by the termination argument) and enforces orientation of the RHS,
but the RHS need not be the global minimum. Named fixtures and the finite diagnostics
exercise LHS collapse; universal preservation of the antichain remains unproved. The
implementation therefore aims for an LHS antichain and keeps a best-effort RHS. The claim
that this realizes the same decision procedure as Kapur is the paper correspondence
argument, not a theorem established by the diagnostics.

---

## 2. The `(f (add x ..r1) (add y ..r2))` matcher invariant, over concrete nodes

Pattern: `(rewrite (f (add x ..r1) (add y ..r2)) (g x))`. The scalar/rest vars may repeat or
differ; the invariant is about node-var binding, not var identity. Regression inputs:
`ac_two_same_op_atoms.egg` (completion off), `ac_complete_nested_match.egg` (completion on).
This is our own e-matching machinery, not from the papers.

### 2.1 The nodes and the plan

`(let t1 (f (add (a) (b)) (add (b) (c))))` builds (class ids bracketed):

```
a,b,c   leaves           add1 = +{a,b} [A1]   add2 = +{b,c} [A2]   f1 = f(add1, add2) [F]
```

`add1`, `add2` are both `add` (same AC op) and both children of one `f`. The planner
schedules `f` first; because its two children are unbound it emits `ExtractChild` steps that
**bind the `add` node-vars** `n1`, `n2`, *before* the two `add` atoms are processed. So each
`add` atom finds its node-var already bound and emits a bound-node **re-join**
`ByRepr{nX} ∩ ByOp{add}` carrying an `atom_id` (keeping the semi-naive variant machinery,
which lives only on `Step::Join`), then a `DecomposeAC`:

```
1 Join nf <- ByOp f             2 ExtractChild n1=child(nf,0)   3 ExtractChild n2=child(nf,1)
4 Join n1 <- ByRepr{n1}∩ByOp{add}   5 DecomposeAC n1,[x],r1
6 Join n2 <- ByRepr{n2}∩ByOp{add}   7 DecomposeAC n2,[y],r2     8 end
```

Steps 2–3 bind `n1`, `n2` in enclosing frames; those bindings must live until subtree 4–8 is
fully enumerated.

### 2.2 The hazard and the invariant

A `leapfrog_join` that does `env.set(target, key)` per key and an unconditional
`env.clear(target)` on exit is wrong here. Step 5 enumerates sibling splits of `+{a,b}` (`x=a`, then
`x=b`), calling `run_step(6)` each time. On the first split, step 6's re-join on `n2` runs,
then clears `n2` on exit (the bug: `n2` was bound upstream by step 3, not by this join). On
the second split, step 6 reads `env.get(n2)` → `Match::get` → `unwrap()` on `None` → panic.
`n1`'s premature clear at step 4 is harmless (nothing re-reads it before step 1 re-extracts
it), which is why it takes *two* same-op AC atoms under one parent to surface; AC completion
exposes it by minting enough `add` nodes for the planner to choose this schedule.

The invariant (`leapfrog_join`): save and restore the prior binding instead of clearing.

```rust
let prev = env.get_opt(target);   // Some(add2) for the re-join; None for a plain join
while join.is_valid() { env.set(target, join.key()); run_step(/* +1 */); join.next(); }
env.set_opt(target, prev);        // restore, not clear
```

Plain join: `prev == None`, equivalent to set/clear. Re-join: the upstream binding
survives. A matcher-soundness invariant, independent of completion (regression
fixtures `ac_two_same_op_atoms.egg`, `ac_complete_nested_match.egg`).

---

## 3. Compliance with Kapur's algorithm

### 3.1 Correspondence table (our code ↔ Kapur 2023)

The table is a code-to-paper mapping. A check mark means that the named
mechanism and focused regressions exist; it does not mean a proof assistant has
established the row or that all rows compose into a correctness/completeness
theorem.

| Our code | Kapur 2023 | Match |
|---|---|---|
| AC node `+M` in class `c` = rule `+M → r(c)` | f-monomial rule `f(A₁) → f(A₂)` (§3) | ✓ |
| `monomial_cmp` (degree-lex: size, then lex from the LARGEST class id down), orientation guard | admissible ordering `≫_f`, orient `f(A₁) ≫ f(A₂)` (§3) | ✓ |
| `ab = multiset_lcm(m,a)`; reducts `(ab−m)⊎rhs_m`, `(ab−a)⊎rhs_a` | `AB = (A₁∪B₁)−(A₁∩B₁)`; critical pair `(f((AB−A₁)∪A₂), f((AB−B₁)∪B₂))` (Def 3.2) | ✓ (lcm = componentwise max = his `AB`) |
| disjoint partners skipped | "if A₁,B₁ disjoint, their critical pair is trivial" (§3) | ✓ |
| trivial-pair filter (normal forms equal ⟹ skip) | "nontrivial iff normal forms ... not the same" (§3) | ✓ |
| close pair = merge both normalized reducts | Lemma 3.3 (joinable critical pairs ⟺ locally confluent) | ✓ |
| `FLAG_AC_COLLAPSED` on LHS reducible by another rule | step 4(i): remove `l→r` whose LHS is reduced by new rule | ✓ (flag, not delete; equality preserved via the merged reduct) |
| dedup reducer/superposition set by (op, LHS) | step 2: "if equal, discard the equation" (keep one) | ✓ (duplicate *nodes* stay in `targets`, so their merges are not lost) |
| incremental (B): superpose only delta rules | step 3 + fn 3: CPs of the new rule vs existing, "incrementally ... instead of all critical pairs" | ✓ |
| LHS collapse plus a separate growth budget | Thm 3.4 (Dickson's Lemma on noncomparable LHSs) | partial evidence: collapse is tested; the budget is a resource exit, not Kapur's termination theorem |
| per-rule axiom critical pairs: idempotent `(f(N⊎{a}), f(N))`, nilpotent `(f(N⊎{a:n−m}), f(M−{a:m}))` | Lemma 4.1(ii); Lemma 4.2(ii)/4.5 (superpose each rule with the op's own axiom) | ✓ (checker `cc_axiom_cps_nonjoinable` under `CHECK_AC_BASIS`) |
| identity-class rule RHS = the empty monomial; unit-drop at build AND recanonize (`CanonMode`) | `f({}) = e` (§2.4); Lemma 4.3's standing normalization `f(x,e) → x` | ✓ |
| (C1) rule cancel-close + (C2) cancelative disjoint superposition + §5.2(iii)(b) per-constant closure over the summand pool | §5.1–§5.3: CancelClose, cancelative disjoint superposition (SC2 / Example 4 fixtures) | ✓ for the named static fixtures; late constants are covered by an implemented full-round net whose focused interleaving regression remains open |
| `:inverse` ⟹ cancelative; inverse-pair cancellation at build + in the round (hash-cons probe) | §5.4's group law at pair level (`x ∘ inv(x) = e`) | partial by design: full §5.4 (Gaussian elimination) is unsupported; completion-off late pairs remain uncancelled (see `../future/ac-completion-limitations.md`) |
| `min_monomial` best-effort RHS | step 4(ii) fully normalizes RHS (reduced) | **partial: §1.2 gap** |

### 3.2 Finite reduced-basis diagnostics

Kapur's output is the *unique reduced* canonical system (Thm 3.6): no rule's LHS or RHS is
reducible by the others. The diagnostic checkers in `ac_invariants.rs` inspect
one finite executable state:

- `cc_min_used_nonminimal`: per (class, op), the true `monomial_cmp`-least same-op monomial,
  compared to the RHS completion actually uses.
- `cc_not_kapur_reduced`: rules whose LHS / RHS is reducible by the *others*
  in the operator's MSet, Set, or nilpotent count domain.
- `cc_axiom_cps_nonjoinable`: per-rule semantic-axiom pairs that do not join
  in the current state.

The checks brute-force superlinearly, so they run only when the per-rebuild **basis-checks switch**
is on: `EGraph::set_basis_checks(true)` (or the `AC_BASIS_DUMP` env var, which seeds it at
construction). Default off; never on the production hot path.

The three features have matching control surfaces at each layer:

| feature | CLI flag | `.egg` directive |
|---|---|---|
| eval algorithm | `--use-semi-naive` / `--use-naive` (default naive) | `;; EVAL: naive\|semi\|both` (default both) |
| derive AC consequences | `--derive-ac-eqs` | `;; DERIVE_AC_EQS: on` |
| check basis properties | `--check-ac-basis` | `;; CHECK_AC_BASIS: on` |

`--derive-ac-eqs` off leaves sub-multiset enumeration in leapfrog matching intact but
skips completion. `--check-ac-basis` needs derive on to have anything to check; in
the egg harness `;; CHECK_AC_BASIS: on` asserts zero nonminimal used RHSs,
zero reducible LHSs, and zero nonjoinable semantic-axiom pairs. It currently
computes but does not assert the RHS-reducibility count, so it must not be
described as a universal or even fixture-level "fully reduced" gate.
`;; EVAL: both` runs the file under naive and semi-naive and asserts the same
outcome.

**Best-effort RHS.** `min_monomial` is maintained on merge, so a rule is
oriented by the read-time guard but global RHS minimality is not established by
construction. `cc_min_used_nonminimal` has returned zero on the maintained
`CHECK_AC_BASIS` fixtures. That is finite evidence only; it does not justify
the former universal claim that merge-only maintenance always computes the
exact minimum.

**Duplicate LHSs.** Congruent nodes can expose the same `(op,LHS)` rule more
than once. The reducer/superposition set deduplicates that key while retaining
the original nodes as collapse/merge targets, so differing RHS equalities are
not lost. Focused fixtures exercise the resulting LHS checks. The remaining
rows in §3.1 are an argued and tested correspondence, not an exactness theorem.

### 3.3 Stress and fixpoint evidence

Three ignored diagnostics remain useful reproducers:

- `completion_divergence_reproducer` exercises a growth-heavy seed and the
  completion backstop;
- `completion_convergence_matrix` samples other generated instances; and
- `completion_reduced_basis_smoke` prints the finite basis diagnostics on one
  converging instance.

They are diagnostic runs, not release gates, a frequency study, or Criterion
benchmarks. Historical node counts, round ratios, and wall times from these
runs must not be presented as current performance or as evidence that growth is
rare. The active `.egg` fixtures with `CHECK_AC_BASIS` are the executable gate:
on those named finite states they assert used-RHS minimality, LHS
irreducibility, and semantic-axiom pair joinability. The harness does not
currently assert RHS irreducibility.

**Conclusion.** The implementation has a detailed, tested correspondence with
Kapur's construction, including explicit partial support for the group facet.
The composition of those rows into soundness, termination, and AC/ACI
completeness remains a paper argument. Only
`CompletionOutcome::Converged` claims the implementation reached its joint
fixpoint; budget and goal exits are intentionally incomplete. Plain mode is the
default, eager completion and basis checks are opt-in, and lazy completion is
the on-demand scoped mode. The proof and validation work remains tracked in
the future-work documents.
