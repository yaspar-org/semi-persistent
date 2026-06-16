# AC Congruence Completeness

This chapter explains why modeling AC nodes as canonical multisets can miss
equalities during congruence closure, what the exact root cause is, and how to
close the gap by extending the machinery we already have.

It is the single design reference for the AC completeness story, and is
self-contained. Part I derives the problem from first principles; Part II gives the
solution and the argument for why it works. For where we stand and what remains,
see [Future Work](A3-future-work.md). For the cost of AC matching (a separate,
matching-side concern), see [Ch 9](09-pattern-matching.md).

---

# Part I, the problem

## 1. Why ordinary congruence closure is complete

Congruence closure (CC) decides the ground word problem: it computes the least
equivalence closed under the congruence rule,

> if `aᵢ ~ bᵢ` for every `i`, then `f(a₁, …, aₖ) ~ f(b₁, …, bₖ)`.

An e-graph realizes this as: two nodes merge iff they have the same operator and
(canonically) the same children. This is complete, but completeness rests on a
precondition that is easy to miss because you normally get it for free; call it the
*materialization invariant*:

> every subterm is a node, and the congruence rule fires on nodes.

It holds automatically because the ground term universe is closed under subterms.
The input is finitely many equations over finitely many terms; every subterm of
every input term is itself a node in the shared DAG. The congruence rule never has
to invent a term ex nihilo, since everything it could fire on already exists in the
e-graph. Stated as two conditions:

```
CC completeness  =  (term universe closed under subterms)
                 +  (congruence fires on materialized nodes)
```

Flattening AC nodes breaks the first condition.

## 2. The problem with set and multiset flattening

Take `a + b + c` with `+` associative-commutative. In a plain binary DAG it is some
bracketing, say `a + (b + c)`:

```
        +
       / \
      a   +     (this inner node is the subterm (b+c), a real node)
         / \
        b   c
```

The inner node `(b+c)` is a subterm, subject to congruence. If we later learn
`b + c = d`, the union-find puts `(b+c)` into class `d`, its parent recanonicalizes
from `a + (b+c)` to `a + d`, and if a node `a + d` exists they merge. That inner
sub-sum node is what the congruence rule fires on. Encoding AC as rewrite rules
materializes all AC-variants of all terms, so all subterm equalities are derivable
through ordinary congruence closure.

Now flatten into a canonical multiset node:

```
   +{a, b, c}     (one node; no inner structure at all)
```

This is the optimization we want: it collapses all `O(3ⁿ)` bracketings of an n-ary
sum into a single node. But the sub-sum node `(b+c)` no longer exists, and neither
does `(a+b)` nor `(a+c)`. The multiset `{a,b,c}` virtually contains those sub-sums
(`{b,c} ⊆ {a,b,c}`, and `+{b,c}` is a legitimate term), but they are no longer
materialized as nodes. This preserves soundness (we will not infer incorrect
equalities), but it breaks completeness of congruence closure.

## 3. The root cause of completeness loss

What does `rebuild` actually do to a multiset node? Recanonicalization of
`+{x₁, …, xₙ}` replaces each element by its union-find representative, then re-sorts
and merges:

```
+{x₁, …, xₙ}   ⟶   +{ find(x₁), …, find(xₙ) }
```

This is congruence on the *direct elements* (the AC analogue of "`f(a)` becomes
`f(b)` when `a ~ b`"); it substitutes equal atoms for equal atoms. That is one of
the two kinds of congruence instance the AC theory produces.

Here is the other kind, which this multiset encoding cannot express. Under AC, for
any sub-multiset `M' ⊆ M`:

```
+M  =  +( M' ⊎ (M − M') )      (commutativity: reorder)
    =  +( (+M') ⊎ (M − M') )   (associativity: group M' into a sub-sum)
```

So if a node `+M' = c` is known (the sub-sum `M'` equals class `c`), then
`+M = +((M − M') ⊎ {c})`. This is substitution of an equal *sub-sum*, not of an
equal *atom*. Recanonicalization does not do it: it only walks the elements of the
multiset and calls `find`. It has no operation that says "when a sub-multiset of my
elements is itself a known sum `+A = a`, substitute the single class `a` in for that
sub-multiset and keep the remainder."

The root cause, in one sentence:

> Flattening erases the intermediate sub-sum subterms, and recanonicalizing
> congruence closure only propagates equalities on the *atoms* of a multiset
> (single-element substitution), never on its *sub-multisets* (sub-sum
> substitution); yet under AC every sub-multiset denotes a real subterm that, in the
> un-flattened representation, would be a materialized node the congruence rule fires
> on.

In terms of §1's two conditions: once you flatten, the AC term universe is no longer
closed under subterms, because the subterms of `+{a,b,c}` under associativity include
all its sub-sums `+{a,b}`, `+{b,c}`, `+{a,c}`, and we materialized none. The first
precondition that made plain CC complete fails; the second still holds; completeness
is lost.

## 4. A concrete trace of the miss

### 4a. Containment: a known sub-sum inside a larger node

This is the §3 root cause directly. Assert:

```
Assert:   +(a, b)    = c       node n₁ = +{a, b}    ∈ class c
          +(a, b, d) = e       node n₂ = +{a, b, d} ∈ class e
```

Here `{a, b} ⊆ {a, b, d}`: the left multiset of n₁ is a sub-multiset of n₂'s. AC
entails, grouping the known sub-sum `+(a,b) = c` out of n₂:

```
+(a, b, d)  =  +( (a,b), d )  =  +( c, d )      using +(a,b) = c
─────────────────────────────────────────────
       ⟹      e  =  +(c, d)
```

The equality is entailed by AC, but our algorithm does not derive it.
Recanonicalization walks n₂'s elements `{a, b, d}` and calls `find` on each (`a, b,
d` unchanged); it does not notice that the sub-multiset `{a, b}` is itself a known
sum equal to `c`, so it does not substitute `c` in to rewrite n₂ to `+{c, d}`. Even
if `+(c, d)` exists from elsewhere, nothing links it to `e`. This is the absent
sub-sum substitution of §3: the sub-sum `+{a,b}` is virtually contained in n₂, but
`c` is never substituted in for it.

### 4b. Overlap: the sub-sum is in no existing node

The harder case is when the two known sums overlap but neither contains the other.

```
Assert:   +(a, b) = c        node n₁ = +{a, b} ∈ class c
          +(b, d) = e        node n₂ = +{b, d} ∈ class e
```

The two left multisets share the element `b`, but neither is a sub-multiset of the
other (`{a,b} ⊄ {b,d}` and `{b,d} ⊄ {a,b}`). The term that exposes the equality is
their superposition (the smallest multiset containing both, `{a, b, d}`), and it is
a node in neither n₁ nor n₂, nor anywhere in the graph. AC entails, by grouping the
shared `b` out of `+(a, b, d)` in two ways:

```
+(a, b, d)  =  +( (a,b), d )  =  +( c, d )      using +(a,b) = c
+(a, b, d)  =  +( a, (b,d) )  =  +( a, e )      using +(b,d) = e
─────────────────────────────────────────────
       ⟹      +(c, d)  =  +(a, e)
```

Again derivable through AC, again missed: there is no node `+{a, b, d}` to
substitute into, so even if `+(c, d)` and `+(a, e)` exist from elsewhere, recanon
maps `{c,d}→{c,d}` and `{a,e}→{a,e}`, finds them syntactically different, and does
not merge.

Note that `+{a, b, d}` is not a sub-sum of anything in the graph; it is a
super-multiset of both n₁ and n₂. A fix that only substitutes into contained
sub-sums (§4a) handles 4a but misses 4b. The fix must also build the superposition
of two overlapping sums and substitute into it both ways (§6).

## 5. Why `rest`-variable matching does not restore completeness

It is tempting to think our `rest` machinery already covers sub-sums. When a
user-rule pattern `(+ ?x ..rest)` matches `+{a,b,c}`, `DecomposeAC`
([Ch 9](09-pattern-matching.md)) does enumerate sub-multisets (`?x=a, rest={b,c}`,
then `?x=b, rest={a,c}`, and so on), so the matcher does encounter the sub-sum
`{b,c}`. But it encounters it as a transient binding, not as a node:

| | `rest` binding during matching | a materialized node |
|---|---|---|
| Exists in the e-graph DAG? | no | yes |
| Visible to the union-find? | no | yes |
| Survives past the current match? | no (discarded on backtrack) | yes |
| Can host a future congruence merge? | no | yes |

Unless a rule's RHS explicitly constructs `+{b,c}`, no node is created, the
union-find never learns it, and the binding is discarded when matching finishes.
`rest`-variable matching enumerates the sub-sums temporarily to produce user-rule
matches; it does not persist them as nodes.

This is how the matcher is simultaneously sound for the e-matching relation (every
binding of pattern variables to existing e-classes is found; see
[Ch 9](09-pattern-matching.md)) while congruence stays incomplete (which would need
those sub-sums to remain as nodes). The matcher can find sub-sums; it does not keep
them to trigger new merges through congruence.

## 5b. The same gap, seen from the matching side

If a term virtually exists (it is an AC sub-sum of a real node but has no node of
its own), does our matcher fail to match it? The answer splits in two.

Case (a): sub-sums reachable by distributing the multiset's own elements are
matched. A pattern `(+ ?x ..rest)` against `+{a,b,c}` enumerates `?x=a,
rest={b,c}`, and so on (§5); every sub-sum obtainable by pulling elements out of the
matched multiset is visited. We expect the majority of real AC rules to be of this
shape and so to fire as expected.

Case (b): a scalar variable that must bind to a compound sub-sum is not matched, and
this can miss a real equality. It arises only when one variable must bind to a
compound sub-sum as a single value, usually because the variable is reused, so its
identity matters. One example is cancellation, `(+ ?x (neg ?x)) ⇒ 0`. Insert
`a + b + (neg (a+b))`. To build `neg(a+b)` at all, the node `+(a,b)` must exist;
call its class `c`. So `a+b` is in fact materialized as `c`, not virtual. But the
outer sum flattens by substituting the child class of each summand, and the two
leaves `a`, `b` are summands in their own right, so the outer node is:

```
+{ a, b, neg(c) }     (not +{ c, neg(c) })
```

Now match `(+ ?x (neg ?x))`: `neg(c)` is a summand, so `(neg ?x)` forces `?x = c`.
The match then needs `c` to also be a summand, but the outer multiset is
`{a, b, neg(c)}`, which contains `a` and `b` separately, not `c`. The match fails,
and the rule that should reduce the term to `0` never fires. A genuine AC
consequence is lost.

It failed not because `a+b` is missing (it is present, as `c`), but because `c` was
never substituted into the outer node to expose it. That is the inter-reduction of
[§6](#6-the-fix-derived-directly-from-the-root-cause): `+(a,b)=c` is known and
`{a,b} ⊆ {a,b,neg(c)}`, so substituting `c` in materializes `+{c, neg(c)}`. Once
that node exists, the existing matcher binds `?x = c` with `rest` empty and the rule
fires.

So the matching boundary and the congruence gap come from the same representation
choice. Enabling matches of the virtually-existing term does not require extending
the matcher to bind scalar variables to virtual sub-sums (that is AC unification,
which requires materializing every sub-sum, the `O(3ⁿ)` blowup the representation
avoids; cf. §9, §11). It requires letting rebuild materialize the finite set of
substituted sub-sum nodes that known equalities imply, after which ordinary
e-matching reaches them.

Part II closes case (b) as well, not by enlarging the matcher but by enlarging the
node set with the demand-driven substitutions. The one residual case neither layer
covers is a sub-sum that is never equal to any named class and never occurs as any
node's child, referenced only by a pattern. Matching that would require
materializing a sub-sum no equation justifies; it is the open AC-unification problem
that Kapur and Conchon (§8) both leave aside, and we do not claim it (§11).

---

# Part II, the fix

## The fix as rewrite-system completion

Our union-find and AC nodes already form a ground AC rewrite system: each AC node
`+M = c` is a rule `+M → c`, and the union-find is the constant-rule layer
(`c → ĉ`). Today that system is not confluent, because rebuild normalizes only child
atoms (`find` each element) and never sub-sums, so two rule orders can drive the
same term to two different normal forms (that divergence is exactly the missed
equality of §4). The fix adds the two operations of §6, which make every such
divergence joinable. A standard rewriting result then applies: a confluent,
terminating system has unique normal forms and therefore decides its equational
theory.

So "restore AC congruence completeness" is "complete the rewrite system to
convergence," and that splits into two separate procedures:

- a completion loop (the rebuild pass, §6–9) that mutates the system to a fixpoint,
  merging classes and materializing critical-pair nodes; its job is to build a
  convergent `R`;
- a pure normal-form function `nf_R` (canonize, then apply `R`'s rules to a normal
  form) that, once `R` is convergent, decides `g₁ =? g₂` by `nf_R(g₁) = nf_R(g₂)`.

`nf_R` is well-defined (single-valued, order-independent) only at the fixpoint;
before convergence it may return different normal forms for different rule orders.
Making it a function is the content of the completeness argument (§10).

## 6. The fix, derived directly from the root cause

The root cause says to re-materialize the erased intermediate terms, but only the
ones that can matter. Not all sub-sums (that is the `O(3ⁿ)` blowup the
representation avoids), only those tied to the left-hand side of a known AC
equality, since those are the only ones a substitution can apply to. That is a
finite, demand-driven set, and it corresponds to Kapur's AC completion (FSCD 2021).
Two operations, matching the two cases of §4:

### (A) Inter-reduction: substitute into a contained known sub-sum (the §4a case)

For an AC node `+M = d` and a known AC node `+A = a` with `A ⊆ M`, the sub-sum `+A`
is virtually contained in `+M` and equals `a`. Substitute `a` in for `A`,
materializing `+((M − A) ⊎ {a})`, and merge it with `d`. This is the missing sub-sum
substitution of §3, performed explicitly.

### (B) Superposition / critical pairs: build the joint term (the §4b case)

Sometimes the term that exposes the equality is in no existing node; it is the
superposition of two overlapping known sums. For `+A = a` and `+B = b` sharing
elements, that term is the lcm multiset

```
AB = (A ⊎ B) − (A ∩ B)         (per-element maximum multiplicity)
```

Materialize `+AB`; it can be rewritten two ways (substitute `a` in for `A`, or `b`
in for `B`):

```
+AB  →  +( (AB − A) ⊎ {a} )       and       +AB  →  +( (AB − B) ⊎ {b} )
```

Both denote `+AB`, so merge them. Disjoint `A, B` need nothing (their critical pair
is trivial, per Kapur), which keeps the work bounded. For §4b, with `A={a,b}, a=c`
and `B={b,d}, b=e`, we get `AB={a,b,d}`, reducts `+{c,d}` and `+{a,e}`, and the
merge yields the missing equality.

## 7. Implementing the substitution from existing machinery

The fix is a new rebuild pass over pairs of existing AC nodes. It reuses two
mechanisms we already have, and it is worth being precise about what each does,
because the search and the arithmetic are separate steps.

The search is rule-driven, not target-driven. It is tempting to picture it the
other way: take a node `+M`, split it into `(part, rest)`, and probe the e-graph
asking "is `+rest` a known node?" That direction forces enumerating sub-multisets of
`M` (up to `2^|M|` splits) and probing each, the blowup we are trying to avoid. We
invert it. Every AC node `+A = a` is already a known sum by construction, so the set
of rules we substitute by is just the set of AC nodes (no probing to discover them).
We only need to find, for each rule `+A`, the nodes it applies to, and that is a
`by_contains` query.

`by_contains` is keyed by a single child class (`by_contains[x]` is every variadic
node containing child `x`), so candidate-finding, per node `+M = d`, is:

```
partners = ⋃_{x ∈ distinct(M)} by_contains[x]  ∩  by_op[+]   # AC nodes sharing ≥1 element with M
for each partner +A = a in partners:
    if A ⊆ M:        # (A) inter-reduction:  A is contained in M
        substitute a in for A
    elif A ∩ M ≠ ∅:  # (B) superposition:    A and M only overlap
        build the lcm node and rewrite it both ways
```

We never look up a multiset, only individual shared elements; disjoint pairs (no
shared element) are skipped, since their critical pair is trivial (§6).

The `rest` machinery is the arithmetic, not the search. Once a (target `+M`, rule
`+A`) pair is chosen, the substitution itself (remove the sub-multiset `A`, keep
`M − A`, drop in `a`) is the same multiset-subtract-and-rebind that `DecomposeAC`
performs when it binds a `rest` variable. We reuse that primitive to compute
`(M − A) ⊎ {a}`. We do not run user-rule pattern matching here, and we do not probe
`rest` bindings during matching: matching enumerates sub-sums transiently for user
rules, whereas this pass pairs existing nodes and keeps the result.

Materialize and merge. With the substituted multiset `M' = (M − A) ⊎ {a}` in hand:

1. probe-or-insert `+M'` in the hashcons, giving class `c'` (materializing a real
   node if it did not exist);
2. `merge(c', d)` in the union-find (this is the equality recanon missed);
3. the new node and the new merge mark the standard rebuild worklist dirty, so `+M'`
   becomes a candidate target/rule next round and the merge re-canonicalizes its
   parents. Iterate to fixpoint.

There is no separate "mark for congruence" flag: materializing `+M'` as a real node
is what lets ordinary recanonicalization and matching reach it from then on, which
restores the missing congruence subterm of §3.

The two reused pieces, at a different time than today:

| Mechanism | Today (user-rule matching) | This rebuild pass |
|---|---|---|
| `by_contains` index | narrow candidates for a pattern with a bound child | pair an AC node with the nodes that share an element (substitution / superposition partners) |
| `DecomposeAC`'s multiset-subtract + `rest` | enumerate sub-sums transiently, then discard | compute `(M − A) ⊎ {a}` for a chosen pair, materialize it, merge |

The two layers stay separate: flattening and recanonicalization keep doing
atom-substitution congruence; this pass adds the sub-sum-substitution congruence.
Together they are full AC congruence closure, at `O(n)` per term plus the finite,
demand-driven set of substituted nodes.

## 8. Our rebuild is Kapur's algorithm minus completion

The data structures map one-to-one onto Kapur's ground AC-CC framework (FSCD 2021),
which flattens AC terms, introduces a constant per subterm, and maintains constant
rules `c → ĉ` and f-monomial rules `f(M) → c`:

| Kapur (FSCD 2021) | Our e-graph |
|---|---|
| Constants (extended signature) | e-class ids |
| Constant rules `c → ĉ`, inter-reduced (Algo 1 step 1, Tarjan Union-Find) | our union-find |
| f-monomial rule `f(M) → c` | an AC e-node: canonical child multiset `M`, class `c` |
| `Sf` (f-monomial equations for `f`) | `by_op[f]` |
| Normalize `Sf` using `RC` (Algo 2 step 2) | `recanonize_node` (have) |
| Propagate constant equalities across symbols (Algo 2 step 4) | rebuild's merge loop (have) |
| Flat uninterpreted rules `h(c₁..) → c` (§4) | non-AC congruence closure (have) |
| Generate critical pairs (Algo 1 step 3) | absent; this is fix (B) |
| Inter-reduce rules by new rule (Algo 1 step 4) | absent; this is fix (A) |

So our rebuild is Kapur's General Congruence Closure (Algorithm 3) with the
per-AC-symbol completion omitted: we have steps 1 and 2, and lack steps 3 and 4. The
fix adds exactly those.

## 9. Implementation

```rust
// In rebuild(), per AC op f, to fixpoint, alongside recanonize_node.
// Treat every AC e-node as the ground rule f(M) -> c (rhs is one class id).

// (B) Superposition critical pairs (Kapur Def. 4). Overlap candidates are
// exactly the AC nodes sharing >= 1 child class, the union of by_contains.
for x in M.distinct() {
    for partner in index.by_contains[x] ∩ index.by_op[f] {
        let (a1, a) = (partner.multiset(), partner.class());   // f(A1) -> a
        if multiset_disjoint(&M, &a1) { continue; }            // disjoint => trivial
        let ab = multiset_lcm(&M, &a1);                        // (M ⊎ A1) − (M ∩ A1)
        let c1 = normalize_ac(f, multiset_union(&msub(&ab, &M),  &[c]));  // (AB−M) ⊎{c}
        let c2 = normalize_ac(f, multiset_union(&msub(&ab, &a1), &[a]));  // (AB−A1)⊎{a}
        if find(c1) != find(c2) { merge(c1, c2); }             // non-trivial, close it
    }
}
// normalize_ac applies (A) inter-reduction by clean nodes + union-find, then
// probes/inserts the resulting AC node. New nodes are marked dirty; the loop runs
// inside the existing rebuild fixpoint, so each merge triggers further substitutions.
```

Index maintenance and round structure. The pass is a semi-naïve worklist fixpoint
(the same shape as the rest of rebuild). Each round runs against a frozen snapshot
of `by_contains`, buffers the new nodes and merges, then refreshes the index and
iterates; a node created in round `k` is dirty and processed in round `k+1`. This
snapshotting loses no critical pair: a pair one partner of which did not yet exist
is caught the round after both exist and the index includes them, and the loop exits
only when a whole round adds nothing (every pair over the final node set has been
considered against the final index). The only requirement is fairness (no pair
starved), which round-based processing gives for free; incremental index maintenance
is a performance option, not a correctness requirement.

We can drop Kapur's monomial ordering (he needs a total admissible `≫_f` to orient
rules into a reduced canonical system): for congruence completeness we materialize
both reducts and merge, and the union-find is our canonical layer. The ordering only
buys a unique reduced presentation (useful for canonical signatures and extraction,
not for deriving equalities).

## 10. Why we conjecture the fix restores completeness

Everything below is a conjecture about the proposed algorithm of §6–9, not an
established property of our code. The argument adapts Kapur's and follows standard
rewriting metatheory, but we have not formally proven that our specific construction
(e-class ids as constants, union-find as the constant-rule layer, `by_contains`-driven
pair finding) satisfies the hypotheses those theorems need. We will know the fix
achieves completeness only once it is implemented and the argument is discharged in
a proof assistant (see the verification plan in [Future Work](A3-future-work.md)).
Until then, treat §10 and the §12 completeness bullet as a plausibility argument, not
a guarantee. None of this affects soundness, which is argued separately and does not
depend on the fix (§12).

The argument has three parts (the search finds every applicable pair, the result is
locally confluent, the loop terminates), and Newman's Lemma then closes it.

- Search completeness (a finite combinatorial lemma, not metatheory). For a node
  `+M`, the only AC nodes that can rewrite-interact with it are those sharing at
  least one child class, and they all lie in
  `⋃_{x ∈ distinct(M)} by_contains[x] ∩ by_op[+]` (§7). Containment partners
  (`A ⊆ M`) and overlap partners (`A ∩ M ≠ ∅`) are both inside this union; disjoint
  partners (`A ∩ M = ∅`) are correctly skipped because non-overlapping rules
  commute, so their critical pair is trivially joinable (firing them in either order
  reaches the same term). So the pass enumerates, via `by_contains`, a candidate set
  that is a superset of the pairs yielding non-trivial critical pairs, and never
  omits one. This reduces to the index's contract: `by_contains[x]` lists every node
  containing `x`.
- Local confluence (conjectured, established by the loop, via Kapur Lemma 5). Local
  confluence is not assumed; it is the postcondition the completion loop establishes,
  by a three-step chain. (1) Kapur's Critical-Pair Lemma reduces "every one-step
  divergence joins" to the finite check "every critical pair joins" (the only way a
  monomial `+C` rewrites two ways is via two rules whose left multisets both fit
  inside `C`, and every such divergence is an instance of the superposition
  `AB = (A⊎B)−(A∩B)`). (2) The search above computes every critical pair. (3) The
  loop merges each pair's two reducts and halts only when a whole round adds nothing,
  so at the fixpoint no critical pair is left un-joined. The chain is: every critical
  pair joinable, therefore (Lemma 5) locally confluent. The step that most needs
  formal checking is that our `normalize_ac` + merge faithfully realizes Kapur's
  reduction and that the joinability test is exactly his.
- Termination (conjectured, via Dickson's Lemma, Kapur Thm 6). There are two
  terminations, with different measures. Normalization (`nf_R` reducing a query to a
  normal form) terminates because every step `+M → +((M−A)⊎{a})` replaces a
  sub-multiset `A` (with `|A| ≥ 1`) by a single class `a`, strictly down in the
  Dickson order (sub-multiset is componentwise `≤`); a total admissible monomial
  order refines that partial order so every rule is orientable. The completion loop
  terminates by a finiteness argument: the loop keeps `R` inter-reduced, so surviving
  rule left-sides are pairwise `⊆`-incomparable (an antichain in `ℕ^{|C|}`), and
  Dickson's Lemma makes every such antichain finite. So only finitely many rules can
  persist, and each merge strictly coarsens the finite class partition.

  (An earlier draft bounded new left-sides as "sub-multisets of lcms of input
  left-sides." That is false: a reduct `(AB−A)⊎{a}` adds the rule's right-hand class
  `a`, which need not lie in `AB`, so reducts can be larger than any input lcm. There
  is no clean size bound; termination rests on Dickson antichain-finiteness over the
  finite class set, not on a multiset-size measure. This is the part most likely to
  need care in a formalization.)

  Scope: AC-CC termination is not saturation termination. The argument bounds a
  single rebuild pass over the AC nodes that exist when it runs. Ground AC congruence
  closure is decidable and terminating (Kapur Thm 6; every ground AC theory has a
  finite canonical system, Narendran-Rusinowitch RTA 1991). It does not claim the
  surrounding equality-saturation loop terminates. A user rule like `a → a + 0` is
  expanding (the right side is a proper super-multiset of the left) and oriented the
  growing way; equality saturation with such productive rules can diverge by design,
  bounded only by iteration limits. Our completion never uses a growing orientation;
  it only ever substitutes a sub-multiset by a single class (strictly reducing). So
  each rebuild over the current finite node set terminates even if saturation as a
  whole does not; divergence is the user rule set's concern, not the AC-CC
  sub-procedure's.
- Cost. Conchon et al. measure this empirically (§7.3): built-in AC is insensitive
  to term depth but processes a quadratic number of critical pairs in the number of
  AC equations. Polynomial, not exponential.

Combining the parts: local confluence and termination give confluence (Newman's
Lemma), hence unique normal forms, hence `nf_R` is a single-valued function and
`g₁ =_{ACCC(S)} g₂ ⟺ nf_R(g₁) = nf_R(g₂)`. The engine then decides the AC word
problem over the ground equations it has been given, the AC congruence closure of
the asserted equalities. This is congruence completeness, not completeness of the
larger AC-unification matching relation of §11, which remains open regardless.

## 11. How the literature handles the §4b example

| Source | Mechanism on `+(a,b)=c, +(b,d)=e` | Where it lives |
|---|---|---|
| Kapur, FSCD 2021 | Def. 4 superposition `AB={a,b,d}`, pair `(+(c,d),+(a,e))`, merge. Terminates by Dickson (Thm 6). | the AC-CC algorithm (= our rebuild) |
| Conchon et al., LMCS 2012 (AC(X)) | `headCP(R)`: shared `aᵘ={b}`, residuals `{a},{d}`, identical pair. For pure AC it is Kapur, plus a Shostak theory X. §8 separately notes the (open) matching gap. | ground AC-completion (= our rebuild) |
| Schifferer/Ullrich/Hack (KBC) | Offline Knuth-Bendix derives a shortcut rule; "use KBC during saturation" is their future work. | precompute, outside rebuild |

The sources converge on the same critical pair. The recipe we implement is Kapur's,
specialized to the e-graph (§6–9).

None of them gives AC unification in matching. Binding a scalar pattern variable to
an un-materialized sub-sum (`?x = a+b` against `+{a,b,c}`) is outside the e-matching
relation every e-graph decides (a variable binds an existing e-class, not a term
with no node), and Kapur and Conchon (§8) leave it aside, because deciding it would
require materializing every sub-sum, the `O(3ⁿ)` blowup this representation avoids.
Two clarifications keep this from being overstated:

- It is the boundary of e-matching, not incompleteness within it; see the precise
  relation in [Ch 9](09-pattern-matching.md).
- Many cases that look like they need it do not: if the sub-sum equals a known class
  (as `a+b = c` does whenever `neg(a+b)` was built), the inter-reduction of §6
  substitutes that class in, materializes the node, and the ordinary matcher reaches
  it (§5b). The unreachable case is a sub-sum equal to no class and occurring as no
  node's child, which we do not claim.

Our `rest` variable already reaches the multiset-valued part of the larger relation
(it binds `{a,b}` as a multiset); a scalar variable does not.

## 12. A proof sketch (abstract model)

Model state `(P, R)`: `P` a partition of a finite set `C` of constants (the
union-find), `R` a finite set of AC rules `f(M) → c` with `M : Multiset C` (the AC
e-nodes). One-step AC rewrite (Kapur Def. 3): `M →_R (M − A₁) ⊎ {a}` when
`f(A₁) → a ∈ R` and `A₁ ⊆ M`. `ACCC(S)` is the least relation containing the input,
reflexive/symmetric/transitive, and closed under
`f(M₁)=f(M₂) ∧ f(N₁)=f(N₂) ⇒ f(M₁⊎N₁)=f(M₂⊎N₂)`. The engine decides `g₁ = g₂` as
`g₁↓_R = g₂↓_R`.

- Soundness (invariant preservation). Invariant `I`: every rule `f(M)→c ∈ R` and
  every merge `c ~_P d` satisfies `=_{ACCC(S)}`. Base: inputs hold trivially.
  Recanon preserves it by congruence (equal child for equal child). A critical-pair
  merge preserves it, since both reducts equal `f(AB)` (Kapur Lemma 5) and so are
  `ACCC(S)`-equal. The union-find is therefore always `⊆ ACCC(S)`: everything
  asserted is a true AC consequence. The argument is finite, local, and
  per-operation, with no metatheory.
- Completeness (confluence at fixpoint, §10). Local confluence is the loop's
  postcondition (search-completeness computes every critical pair, the loop merges
  each, and halts only when none remain, so by Kapur Lemma 5 the fixpoint is locally
  confluent). With termination by Dickson antichain-finiteness over the finite class
  set, Newman's Lemma gives confluence, hence `nf_R` is single-valued, hence the
  engine derives every entailed equality. Note `nf_R` is a function only at the
  fixpoint; before convergence it is multivalued, which is why completeness is a
  fixpoint property and not an invariant.

The verification plan (which proof in Verus, which in Lean, and the staging) is in
[Future Work](A3-future-work.md), since it concerns what remains to be done.

---

## References

- Kapur, "A Modular Associative Commutative (AC) Congruence Closure Algorithm,"
  FSCD 2021, LIPIcs 195, 15:1–15:21. Def. 3 (AC rewrite), Def. 4 (superposition and
  critical pair), Lemma 5 (local confluence), Thm 6 (termination via Dickson), §6
  (Gröbner basis as AC-CC). The basis for the fix.
- Kapur, "Shostak's Congruence Closure as Completion," RTA 1997, LNCS 1232,
  pp. 23–37. The flatten-and-introduce-constants framework FSCD 2021 generalizes.
- Conchon, Contejean, Iguernelala, "Canonized Rewriting and Ground AC Completion
  Modulo Shostak Theories," LMCS 8(3:16), 2012. AC(X), `headCP(R)`, the Hullot
  flatten+sort canonizer (§3), §7.3 quadratic cost, §8 matching gap.
- Schifferer, Ullrich, Hack, "Augmenting Rewrite Rule Sets via Knuth-Bendix
  Completion." The offline alternative (critical pairs as precomputed rules).
- Narendran, Rusinowitch, "Any Ground Associative-Commutative Theory Has a Finite
  Canonical System," RTA 1991, LNCS 488, pp. 423–434.
- Kandri-Rody, Kapur, Narendran, "An Ideal-Theoretic Approach to Word Problems and
  Unification Problems over Finitely Presented Commutative Algebras," RTA 1985,
  LNCS 202, pp. 345–364. The AC-CC / Gröbner correspondence Kapur §6 builds on.
- Peterson, Stickel, "Complete Sets of Reductions for Some Equational Theories,"
  J. ACM 28(2), 1981, pp. 233–264. Extension rules for AC completion; our framework
  stays ground, avoiding AC unification.
- Bachmair, Tiwari, Vigneron, "Abstract Congruence Closure," J. Automated Reasoning
  31(2), 2003, pp. 129–168.
- Newman, "On Theories with a Combinatorial Definition of Equivalence," Annals of
  Mathematics 43(2), 1942. Newman's Lemma (local confluence plus termination gives
  confluence).
- Contejean, "A Certified AC Matching Algorithm," RTA 2004, LNCS 3091, pp. 70–84.
  Defines the AC matching problem `pσ =_AC s` independently of any algorithm (the
  external relation [Ch 9](09-pattern-matching.md) states soundness against), gives
  inference rules proven sound, complete, and terminating in the Coq proof assistant
  (the algorithm is implemented in CiME), and proves AC equality decidable via
  flatten+sort. The Coq precedent for the §12 metatheory.
- Hullot, "Associative Commutative Pattern Matching," IJCAI 1979. The original
  flatten+sort canonizer and AC matching problem.
- Benanav, Kapur, Narendran, "Complexity of Matching Problems," J. Symbolic
  Computation 3(1/2), 1987, pp. 203–216. AC matching is NP-complete (so a complete
  matcher's output is worst-case exponential; [Ch 9](09-pattern-matching.md)).

---
[Table of Contents](00-table-of-contents.md) · [Future Work: status and plan](A3-future-work.md) · [Ch 9: matching cost](09-pattern-matching.md)
