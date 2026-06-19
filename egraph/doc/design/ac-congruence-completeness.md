# AC Congruence Completeness

This chapter explains why modeling AC nodes as canonical multisets can miss
equalities during congruence closure, what the exact root cause is, and how to
close the gap by extending the machinery we already have. At its heart the problem is
maintaining a small *reduced canonical basis* of rewrite rules incrementally, as
saturation feeds facts in — §0 states this in one breath and §5c works it through one
example with no jargon.

It is the single design reference for the AC completeness story, and is
self-contained. Part I derives the problem from first principles (start with §0 for the
one-breath framing); Part II gives the solution and the argument for why it works. For
where we stand and what remains, see [Future Work](A3-future-work.md). For the cost of
AC matching (a separate, matching-side concern), see [Ch 9](09-pattern-matching.md).

---

# Part I, the problem

## 0. The core problem, in one breath

Two AC facts force *infinitely* many equalities. `a+b = p` already entails `a+b+c =
p+c`, `a+b+d = p+d`, … — every bag with `{a,b}` inside it, with the same junk on both
sides. Add a second fact and they *collide*: `a+b = p` and `a+b+c = q` share the bag
`a+b+c`, which forces `p+c = q` — a fact nobody stated, and the only non-padding line
in the whole infinite pile.

So the AC-congruence-closure problem is **not** "store the equalities." You cannot —
there are infinitely many. It is: **maintain, incrementally as facts arrive during
saturation, a tiny finite set of find-and-replace rules that *regenerates* any of those
equalities on demand** — and keep that set *reduced* (no rule's left side contained in
another's), so it stays small. Deciding `g₁ = g₂` is then "rewrite both with the rules
until they stop; equal iff they land in the same place."

Two forces fight each other while saturation runs and new facts keep arriving:

- **Collision (superposition)** *creates* the genuinely-new rules — like `p+c = q` —
  that two overlapping facts force. This is the only source of new equalities; without
  it congruence closure is incomplete (the misses traced in §4).
- **Reduction (collapse / inter-reduction)** *deletes* rules that a smaller rule already
  subsumes — like dropping `a+b+c = q` once `a+b = p` and `p+c = q` are known, because
  `a+b+c` just rewrites to `p+c` first. This is what keeps the set finite.

Get collision without reduction and the rule set explodes — collisions breed redundant
rules that breed more (the divergence we actually hit, §6b). Get reduction without
collision and you never derive the cross-fact equalities (incompleteness, §4). **AC
congruence closure is exactly the discipline of running both, in the right order, to a
fixpoint, so the surviving rules are a reduced canonical basis** — the smallest machine
that decides the theory. The whole of this chapter is how to do that inside an e-graph
where "a rule" is just an AC node and "delete a rule" cannot mean delete a node.

§5c walks this through one concrete example, line by line, before the formal treatment.
Readers who want the intuition first should jump there now.

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
`{b,c}`. But it encounters it only as a transient value bound to `rest` in the
matcher's environment, not as a node in the e-graph. The distinction is what makes
the difference for congruence: a `rest` binding does not exist in the e-graph DAG,
the union-find never learns about it, and it is discarded the moment the match
completes or backtracks, so it can never sit in a class and trigger a later merge.
A materialized node is the opposite on every count: it lives in the DAG, has a
class in the union-find, persists, and so can host future congruence. Unless a
rule's RHS explicitly constructs `+{b,c}`, no such node is created.

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

## 5c. The whole idea in one worked example, no jargon

This section is the core problem (§0) and its solution, worked line by line on one
example, in plain terms — the didactic version of the entire chapter. `+` is a *bag*
(order doesn't matter, no nesting — `a+b+c` is just the bag `{a,b,c}`). We are handed
exactly two facts:

```
FACT 1:   a + b      is the same thing as   p
FACT 2:   a + b + c  is the same thing as   q
```

**The uncompressed version** is everything those two facts force to be true. From
FACT 1, gluing anything onto both sides: `a+b+c = p+c`, `a+b+d = p+d`,
`a+b+c+d = p+c+d`, … (infinite). From FACT 2 likewise: `a+b+c+d = q+d`, … And both
lists contain `a+b+c`, so their right sides must agree, giving `p+c = q`, `p+c+d =
q+d`, … forever. You do not want to store this infinite pile. Almost every line is
just "a fact with junk glued onto both sides." The **one** line that is *not* padding
is

```
p + c = q
```

— genuinely new, because you cannot get it by gluing onto FACT 1 or FACT 2; it falls
out of the two facts *colliding* on the shared term `a+b+c`.

**The compressed version** is two find-and-replace rules:

```
RULE 1:   a + b   →   p
RULE 2:   p + c   →   q
```

The arrow means "wherever you see the left side as a sub-bag, replace it with the
right side." FACT 2 is now *redundant* — recompute it: `a+b+c —RULE1→ p+c —RULE2→ q`.
We dropped FACT 2 and kept the collision fact instead.

**Recovering any line of the infinite pile**: run both sides through the rules until
they stop, check they land in the same place. Is `a+b+c+d = q+d`? Left:
`a+b+c+d → p+c+d → q+d`. Right: `q+d` (stuck). Same place ⇒ true — recovered without
ever storing it. The compressed version is not a lookup table; it is a little machine
that regenerates any line on demand.

**Why keep `p+c` and not `a+b+c`** (this is the "incomparable left-sides" condition
in plain words): `a+b+c` *contains* `a+b`, which is already RULE 1. A rule starting
with `a+b+c` would immediately get chewed by RULE 1 down to `p+c` anyway — it rewrites
itself, so it is dead weight. Store the already-chewed version. The rule of thumb is
just: **never keep a rule whose left side contains another rule's left side.** After
you delete all such dead weight, no left side contains any other — that "antichain"
property is not a goal, it is simply *what is left* once the redundant rules are gone.

**How the machine builds this live — the part that matters for saturation.** This is
the crux: the basis is *not* computed once from a fixed input. Saturation feeds facts
in one at a time (each rewrite firing produces a new equality), and the reduced basis
must be maintained *incrementally* as they arrive — every new fact can both spawn
collisions and make existing rules redundant. Every fact is a rule; on each new rule you
do two chores, then repeat until quiet:

- **Chore A (clean up / collapse):** does the new rule's left side sit *inside* an
  existing rule's left side? Then that existing rule is stale: chew it down with the
  new rule and replace it. Also chew the new rule down by what's already there.
- **Chore B (collision / superposition):** does the new rule's left side *partly
  overlap* an existing one (share atoms, neither inside the other)? Build the smallest
  bag containing both, rewrite it the two ways, and if the results differ, that
  difference is a new fact — add it as a rule. (Disjoint left sides — no shared atom —
  cannot collide; skip them.)

Run it on our example. FACT 1 arrives → `{a+b→p}`, nothing else exists, no chores.
FACT 2 `a+b+c→q` arrives → **Chore A fires**: `a+b` sits inside `a+b+c`, so the new
rule is chewed on arrival into `p+c→q`. We never store `a+b+c→q`. Knowledge is now
`{a+b→p, p+c→q}`. Chore B: `{a,b}` and `{p,c}` share no atom → no collision. Done. The
machine reached the two-rule compressed form by itself, and FACT 2 was swallowed by
Chore A on the way in.

The collision case bare, since it is the part that feels like magic. Suppose instead
the facts were `a+b→p` and `b+c→r` (they share `b`, neither inside the other). Chore A:
neither sits in the other, nothing stale. Chore B: shared `b`, smallest bag containing
both is `a+b+c` (take the shared `b` once); rewrite two ways — `a+b+c —(a+b→p)→ p+c`
and `a+b+c —(b+c→r)→ r+a`; two results of reducing the *same* bag, so `p+c = r+a`, a
fact nobody stated. Chore B is the only way genuinely-new facts are born.

**This is exactly the blowup we hit.** The first implementation **skipped Chore A**:
when FACT 2 arrived it kept `a+b+c→q` *and* derived `p+c→q`, so a rule (`a+b+c`)
containing another rule (`a+b`) stayed live. Next round Chore B built collision bags
off it, breeding more rules that *also* contained `a+b`, which bred more — generating
the infinite pile instead of the two-rule machine. The fix is literally: **on each new
rule, do Chore A first (chew down everything it sits inside, and chew it down by what
exists), and only then Chore B.** Keep the rules chewed-down at all times and the set
cannot blow up — a chewed-down set is one where no rule contains another, and there
simply cannot be many of those (Dickson's Lemma, §10).

The rest of Part II is this mechanism stated precisely against the e-graph: §6 the two
operations, §6b why Chore A (collapse) is load-bearing and how "retire a rule" is
realized without deleting a node, §7–9 the implementation, §10 why it terminates and
is complete.

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

## 6b. Collapse is load-bearing: (A) and (B) alone diverge

(A) and (B) as stated above are *incomplete as an algorithm*, and a naïve
implementation of them does not just run slowly — it **diverges**, minting larger
and larger nodes without bound. This section states the missing operation, because
it is as much part of the fix as (A) and (B) and the rest of the chapter silently
assumed it. It was found the hard way: a first implementation of (B) that
materialized both reducts and merged them, with no collapse, grew the node count
≈4–5× **per round** and the critical-pair count ≈10× per round on the five-constant
§4a example — exponential, OOM within ~15 rounds.

### The missing operation: Collapse / inter-reduction

Reading each AC node `+M = d` as a rule `+M → d`, the active rule set must be kept
**reduced**: no rule's left multiset is a sub-multiset of another's. This is Kapur's
Algorithm 1 **step 4** ("inter-reduce rules by the new rule") and Conchon et al.'s
**Collapse** inference rule, and it is *destructive* — it removes rules:

> When a rule `+A → a` is added and an existing rule `+M → d` has `A ⊊ M` (so `+M` is
> reducible by `+A`), rewrite `+M` via `+A` (this is exactly (A)), merge the reduct
> into `d`, and **retire `+M` from the active set**.

**"Retire" means mark subsumed, not delete.** Kapur and Conchon work over an abstract
rule set they can shrink; an e-graph cannot remove nodes — they are immutable, shared,
and must survive for semi-persistent rollback (`restore`). The realization is to set
the existing **`FLAG_SUBSUMED`** flag on `+M`. The node stays in the DAG and in its
class (so soundness and rollback are untouched, and the equality `+M = d` it
established is preserved), but it is **excluded from the matchable / active set**: the
index builders (`IndexStore::build`/`build_delta`) and the completion's own AC-node
snapshot already skip `FLAG_SUBSUMED` nodes, so a subsumed node is automatically
neither a superposition source nor a user-rule match target from then on. This is the
same flag and the same semantics as user-level `(subsume …)`; collapse is just an
internally-triggered subsumption. So "remove from `active`" throughout this section is
implemented as "mark `FLAG_SUBSUMED`," and the antichain is the set of
*non-subsumed* AC nodes.

The active set is then a **Dickson antichain**: a set of multisets over the finite
class pool `C`, pairwise `⊆`-incomparable. Dickson's Lemma makes every such antichain
finite, and for typical inputs it stays near the input size. Since superposition (B)
ranges over pairs of *active* rules, the work per round is `O(|active|²)` — Conchon's
empirically quadratic cost (§7.3) is a statement about `|active|`, and it holds **only
because collapse keeps `|active|` an antichain**.

Subsuming a rule loses no equality. Before `+M` is marked subsumed, its content is
*already preserved twice*: the merge `reduct(+M) = d` has been performed (so `+M`'s
class is still `d`), and the reduct itself is a live, non-subsumed node carrying the
same class. So every consequence `+M` could contribute as a superposition source is
also derivable from its reduct, which *is* active. Subsumption therefore prunes only
*redundant* sources (the composite superpositions of Kapur–Musser–Narendran), never a
prime one — which is exactly why completeness survives. The subsumed node remains a
legal *child* of other live nodes and keeps its class membership; it simply stops
being enumerated as a rule LHS or a match target.

### Retirement = `FLAG_SUBSUMED`: tombstone two roles, keep two

"Retire a rule" cannot mean "delete a node" here. A node plays **four** roles, and
collapse retires only two of them; getting the split — and its *ordering* — right is
the whole correctness story. The trigger for collapsing a node is precise: **a node is
collapsed when its children can be rewritten by *some other* node.** `+{a,b,c}` with
`+{a,b}=p` known → its sub-bag `{a,b}` reduces to `p`, so it is collapsed. (Note "some
*other* node": a rule's own left side is never reducible by itself — only a smaller,
different rule makes a node reducible.)

**Retire it from the two *active* roles:**

1. **Superposition source.** A collapsed node must never again be the node we build
   overlap-bags *from* (Chore B). It is reducible, so every collision computed off it
   is redundant (a *composite* superposition, Kapur–Musser–Narendran) — and these are
   exactly the copies that bred the divergence. Pull it out of the set Chore B iterates.
2. **Collapse source for others.** It must not be used to rewrite *other* nodes either.
   A reducible rule reducing things only lengthens derivations and adds churn; let
   irreducible nodes do the rewriting. (Not a soundness issue, a termination/effort one.)

**Keep it in the two *passive* roles:**

3. **Its class membership / the merge it caused.** Collapsing `+{a,b,c}` rewrote it to
   `+{p,c}` and merged that into `q`. *That merge is the whole point* — it is the
   equality we set out to derive. Retiring the node must not undo it; the fact did not
   vanish, it relocated to `+{p,c}`, which is live.
4. **Being a child of larger nodes.** If `+{a,b,c}` sits inside some `h(+{a,b,c}, x)`,
   that parent still points at it and needs it to recanonicalize. Hard-erasing it from
   the hash-cons would dangle that pointer.

So collapse is a **`FLAG_SUBSUMED` bit, not a delete**: it removes the node from the
superposition/collapse-source iteration, while leaving it fully hash-consed and in its
class for parents and for matching. (Nodes are immutable and shared, and `mark`/`restore`
rolls the node store back to a token — deleting would corrupt that history. The bit is
itself part of the rolled-back node state, so a node subsumed after a `mark` is
un-subsumed on `restore`.) This is the same flag and semantics as user-level
`(subsume …)`; completion's collapse is just an internally-triggered subsumption.

**The load-bearing ordering — materialize+merge first, mark second, eager before
Chore B.** Three sub-points, each a way to get it wrong:

- **Merge before mark.** Materialize the reduct `+{p,c}`, merge it into the class, and
  *only then* set `FLAG_SUBSUMED` on `+{a,b,c}`. Reverse the order and you have removed
  a node before its equality was re-established elsewhere — deleting information. (This
  is also why hiding from the matcher is safe: by the time the big node is hidden, the
  reduced node carrying the same class is already present. The §5b cancellation case
  depends on this exact ordering — the rule fires only *after* the substituted node
  exists; mark too early and a real match is lost.)
- **Eager within the round.** The bit must gate Chore B *in the same round* the node
  becomes reducible. If a stale snapshot still lets this round's superposition pass see
  it, it breeds anyway. (Our round structure rebuilds the snapshot each round and skips
  subsumed, which gives this.)
- **Matcher exclusion is a free *consequence*, not the mechanism.** Because the matcher
  reads e-nodes exclusively through `IndexStore` (`by_op`/`by_repr`/`by_child_pos`/
  `by_contains` via `VariantIndex`), never the raw node store, and the index builders
  skip `FLAG_SUBSUMED`, a collapsed node is automatically unmatchable. Usually this
  changes nothing observable (the reduced node in the same class is matched instead),
  but it must not happen *before* step 3. Standing obligation on future work: **any new
  matching path must respect `FLAG_SUBSUMED`**, or it silently re-opens divergence and
  breaks user `(subsume …)`. The completion tests (naive+semi-naive differential plus a
  subsumed-non-matchable check) guard this; flag it in any review touching the matcher
  or index.

### Why omitting collapse diverges (and why hash-consing does not save it)

Drop collapse and the "antichain" stops being one. The reduct `(AB − A) ⊎ {a}`
injects the rule's right-hand class `a`, which need not lie in `AB` (the §10
correction). So a reduct can be a **proper superset** of an existing rule's
left side — i.e. itself reducible — yet, materialized raw, it survives as a live node
and therefore as a superposition source for the next round. Round 1 superposes `n`
rules into `~n²` reducts; each becomes a partner; round 2 superposes `~n²` into
`~n⁴`; cascade. Dickson still guarantees eventual termination, but over a growing
*chain*, not the antichain, so the bound is astronomical — the observed exponential.

It is tempting to think hash-consing already handles this: "materialize the reduct
and let the hash-cons merge it with whatever exists." It does not. **Hash-consing
resolves only *syntactic* collisions — identical multisets — which is the atom-level
congruence we already have.** AC completion is about *sub-multiset* congruence (§3),
which hash-consing structurally cannot see. Inserting `+{a,b,s}` when `+{a,b} → t`
exists produces a *fresh* class (no identical multiset is present); the node is
semantically reducible (`{a,b} ⊊ {a,b,s}`, so `+{a,b,s} = +{t,s}`) but the e-graph
does not know it, and it now drives superpositions. The reducible form must be
**normalized away before it becomes a node** — equivalently, reducible nodes must
never be superposition sources (the *prime superposition* criterion,
Kapur–Musser–Narendran 1988: a superposition whose overlap term is reducible
elsewhere is *composite*, and its critical pair is redundant).

### Superposition is bounded; substituting a class-as-atom is what explodes

It looks paradoxical that the algorithm superposes rule left-hand sides — which are,
by orientation, the *larger* (non-minimal) monomials — yet does not blow up. If the
sources are the big sides, why don't bigger and bigger terms cascade? Three facts make
superposition bounded, and locate the real explosion elsewhere.

1. **A critical pair is bounded by the lcm of two existing left sides.** Superposing
   `A₁ → B₁` and `A₂ → B₂` builds `AB = lcm(A₁, A₂)` — the component-wise max of two
   left sides already present — and the two reducts `(AB − Aᵢ) ⊎ Bᵢ` are each
   **strictly smaller than `AB`** in the degree-lex order, because each rule is
   oriented `Bᵢ ≺ Aᵢ`. The output of a superposition is bounded by its inputs. There is
   no upward pressure *from superposition itself* — provided the constant pool does not
   grow.

2. **The explosion comes from introducing a new atom, not from superposition.** It is
   the right-hand side of the closing merge that matters. When the critical pair
   `+{c,d} = +{a,e}` is closed, the merged class must be substituted back into other
   monomials. Substitute the **bare class id** `κ` of that class and `κ` becomes a
   *new constant* used as a single summand: `+{b,d,c}` reduces to `+{b, κ}` instead of
   to `+{b} ⊎ {a,e} = +{a,b,e}`. Now lcms range over `{a,b,c,d,e,κ,…}`, the pool grows
   every round, and *that* is the runaway — not the superposition, the fresh atom.
   The fix is to orient the critical pair as a rule between **two monomials** over the
   *existing* constants (`larger → smaller`, never `→ κ`), and to substitute a class by
   its **minimal monomial** (its degree-lex-least representative), never by a
   class-as-atom. Then `+{b,c,d} → +{a,b,e} → +{c,e}` (via `+{a,b}→c`) joins the other
   reduct `+{c,e}`: the pair is trivial, nothing new is added, and the §4b system
   converges to three rules over `{a,b,c,d,e}` with no new constant ever introduced.

3. **Collapse keeps the count finite even though sizes are bounded.** Bounded-size
   monomials could still accumulate in *number*; collapse (above) retires every left
   side that becomes reducible, so the surviving left sides are a Dickson antichain —
   finite. Narendran–Rusinowitch (RTA 1991): every ground AC theory has a finite
   canonical system, and this is the construction of it.

So "superpose only non-minimal monomials" is not an extra trick — a rule's left side
*is* the non-minimal side, and the minimal monomial of a class is its normal form, has
no rule on its left, and is therefore never a redex nor a superposition source. The two
load-bearing choices are the ones above: **orient critical pairs between monomials over
the existing constants (minimal-monomial RHS, no fresh atom), and collapse.** Get those
right and superposition is `O(|active|²)` per round over a finite antichain; get the RHS
wrong (substitute the class id as an atom) and it diverges regardless of collapse.

### Worked example: two rules, hand-checkable

`+` AC, atoms `a, b, c`, right-hand classes `s, t`. Input:

```
R1:  +{a, b, c} → s        R2:  +{a, b} → t
```

The only structural fact: `{a,b} ⊊ {a,b,c}`, so **R1 is reducible by R2** (no order
needed — collapse fires on containment alone). The reduced canonical system is the
two-rule antichain

```
+{a, b} → t        +{c, t} → s        ( a+b = t ; a+b+c = c+t = s )
```

whose left sides are `⊆`-incomparable and share no element, so there is no critical
pair: confluent, complete, done.

**Correct run (collapse eager).** R1 reducible by R2 → rewrite `{a,b,c}` via R2 to
`{c,t}`, merge into `s`, **retire R1**. Active set `{ {a,b}, {c,t} }`; the two share
no element → fixpoint in one round. Collapsing R1 *deletes the partner carrying `s`
on its RHS*, which is exactly what stops `s` from re-entering as a summand.

**Buggy run (no collapse).** Materialize `+{c,t} → s` but keep R1. Now `{c,t}` and
`{a,b,c}` overlap on `c` → superpose: `AB = {a,b,c,t}`, reducts `{s,t}` and
`{a,b,s}`, merge as a new class `w`. **`s`, a right-hand class, has re-entered as a
summand** — and `{a,b,s}` is reducible by R2 but, inserted raw, survives as a
partner. Round 3 superposes the new nodes against everything sharing an element,
`w` re-enters as a summand, the constant pool grows `{a,b,c,s,t,w,…}`, and each round
mints `O(current nodes)` new classes. That is the divergence.

Note the two distinct mistakes this run makes, matching the two preceding subsections:
it never collapses R1 (so the reducible `+{a,b,s}` persists as a partner), **and** it
closes the critical pair into a fresh class `w` used as a summand (the class-as-atom
explosion). Either alone diverges; the fix needs both.

The correct run *decides* `{a,b,s} = {s,t}` by normalising (`{a,b,s} → {t,s}` via R2,
same as the other side, both over existing constants) and stores neither — collapse
plus normalize-into-minimal-monomial is the step that cannot be skipped.

### What this requires of the implementation

1. **Maintain an `active` set of irreducible AC nodes** per op (those with no
   containment partner) — concretely, the non-`FLAG_SUBSUMED` AC nodes, which the
   index/snapshot builders already isolate. Superpose (B) only over `active`.
2. **On adding `+A → a`**, find its containment supersets via `by_contains`; for each
   active `+M` with `A ⊊ M`, reduce (A), merge, and **mark `+M` `FLAG_SUBSUMED`** (the
   non-deletable form of "retire"; the node and its equality persist for rollback).
3. **Normalize every reduct against *all* current rules** (including those minted this
   round) to a fixpoint before comparing — see the `normalize_ac` correction in §9.
   If the two reducts land in one class, add nothing.
4. **Orient rules and substitute minimal monomials, never class-as-atom.** Pick a total
   admissible monomial order `≫_f` (degree-lex: size, then class-id lex). Every rule is
   `larger-monomial → its-class's-minimal-monomial`; closing a critical pair substitutes
   that minimal monomial (over existing constants), never a bare class id used as a fresh
   summand. This is what keeps the constant pool fixed and superposition bounded
   (preceding subsection).

Instrument `|active|` against the total AC-node count per round: missing-collapse (or
class-as-atom) divergence shows both curves growing together every round; with both fixes
in place, `|active|` plateaus near the input size while total nodes may be larger but inert.

### Hard prerequisite: nested same-op flattening (`WF_flat`)

There is a precondition the completion pass cannot establish on its own and that the
rest of the engine silently assumes: **AC terms are flattened** — an `f`-node never has
an `f`-class child. Call it `WF_flat`. The matcher relies on it: the parent-driven
variadic re-join (`ByRepr ∩ ByOp`, the semi-naive variadic-mode machinery) dereferences
a node's repr while `DecomposeAC` walks its children, and if a child is itself an
`f`-monomial the recursion reaches an unbound plan variable and the matcher panics
(`Option::unwrap()` on `None`).

Completion routinely violates `WF_flat`: a Kapur reduct `(AB − A) ⊎ {class(+A)}` keeps
`class(+A)` — itself an `f`-monomial — as an element, so materializing it builds
`+f(+f(…), …)`. Confirmed end-to-end: a rule `(f (add x ..r1) (add y ..r2))` over
`f(add(a,b), add(b,c))` (the two sums overlap, completion superposes them) crashes the
matcher under **both** naive and semi-naive saturation — it is a genuine engine
precondition, not a test artifact. (The §4a/§4b/§5b examples pass only because none of
them matches a rule that decomposes two same-op atoms against a completion-built node.)

So **AC completion cannot be enabled by default until nested same-op flattening lands**
(build side: the AC arm of `add`; pattern side: the flatten passes). This is the
[ac-flattening TODO] — previously framed as a canonical-form nicety and a scoped
completeness caveat; the completion work promotes it to a hard blocker. Until it lands,
completion stays gated/WIP. There is no in-completion shortcut: flattening only at
materialization time either reintroduces reducible nodes (breaking convergence) or fails
to flatten children built earlier, so the invariant has to hold globally.

## 7. Implementing the substitution from existing machinery

The fix is a new rebuild pass over pairs of existing AC nodes. It reuses two
mechanisms we already have, and it is worth being precise about what each does,
because the search and the arithmetic are separate steps.

First, the reading that makes the rest of this section work: an AC node records a
rewrite rule, and the rule is recovered by **two separate `find`s in two different
places**. A node has no `find` of its own — only a *class* does. So:

```
rule of a node  =  +{ find(child₁), find(child₂), … }  →  find(class the node sits in)
                   └─────────── left side ──────────┘     └──── right side ────┘
```

`find` on the **children** builds the left side (the canonical sub-bag); `find` on the
**class** builds the right side (the single class the node reduces to). The set of
rules is exactly the set of AC nodes — we build no separate rule store.

A correction worth stating outright, because an earlier draft implied otherwise:
**which representative the union-find picks for a class does not matter.** Rank-based,
arbitrary, whatever — it washes out completely; the equalities the procedure decides
are identical regardless of which class member is the rep. Representative *selection*
is not a thing to be careful about here. (It would matter only if we later wanted one
canonical *printed* form for extraction — not for deriving equalities.) What *does*
need care is firing a kind of rule the union-find never fires; that is the next point.

Recanonicalization already fires the node-rules — but only the *single-child* kind.
When a child's class moves, recanon swaps that one child for its `find` and rehashes;
that is exactly rule-firing on `+{ find each child }`. What it never does is notice
that a whole **sub-bag** of a node's children is itself a known node equal to some
class, and substitute *that*. Concretely: node `+{a,b,c}` with `+{a,b}` in class `p`.
Recanon runs `find` on `a`, on `b`, on `c` — all atoms, nothing moves — and walks away;
it never sees that the sub-bag `{a,b}` equals `p`, so it never reaches `+{p,c}`. No
choice of representative fixes this: the union-find simply has no operation that
substitutes a *group* of children at once. **That missing operation — substitute an
equal sub-bag, not just an equal single child — is the entire fix** (§6 (A)/(B)).

The search is rule-driven, not target-driven. It is tempting to picture it the
other way: take a node `+M`, split it into `(part, rest)`, and probe the e-graph
asking "is `+rest` a known node?" That direction forces enumerating sub-multisets of
`M` (up to `2^|M|` splits) and probing each, the blowup we are trying to avoid. We
invert it. Since every AC node `+A` is already such a rule by construction, no
probing is needed to discover the rules; we only need to find, for each rule `+A`,
the nodes it applies to, and that is a `by_contains` query.

`by_contains` is keyed by a single child class (`by_contains[x]` is every variadic
node containing child `x`), so candidate-finding, per node `+M = d`, is:

```
# by_contains/by_op range over NON-SUBSUMED (active) AC nodes only (§6b).
partners = ⋃_{x ∈ distinct(M)} by_contains[x]  ∩  by_op[+]   # active AC nodes sharing ≥1 element with M
for each partner +A = a in partners:
    if A ⊊ M:        # (A) inter-reduction:  A properly contained in M
        substitute a in for A, merge, and mark +M FLAG_SUBSUMED  # collapse (§6b)
    elif A ∩ M ≠ ∅:  # (B) superposition:    A and M only overlap
        build the lcm node, normalize both reducts to normal form, merge if distinct
```

We never look up a multiset, only individual shared elements; disjoint pairs (no
shared element) are skipped, since their critical pair is trivial (§6). The collapse
on `A ⊊ M` (marking `+M` subsumed) and the normalize-before-merge in (B) are the
non-optional steps §6b derives — without them this loop diverges.

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
| `DecomposeAC`'s multiset-subtract + `rest` | enumerate sub-sums transiently, then discard | compute `(M − A) ⊎ {a}` for a chosen pair, normalize, materialize, merge — and on `A ⊊ M` mark `+M` subsumed (collapse, §6b) |
| `FLAG_SUBSUMED` + index/snapshot skip | user-level `(subsume …)` | collapse: retire a reducible rule without deleting the node (§6b) |

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
| Inter-reduce rules by new rule (Algo 1 step 4) | absent; this is fix (A)-substitution **+ Collapse** (§6b) |

So our rebuild is Kapur's General Congruence Closure (Algorithm 3) with the
per-AC-symbol completion omitted: we have steps 1 and 2, and lack steps 3 and 4. The
fix adds exactly those. Note step 4 is *two* things — substituting the reduct (fix
(A)) **and** retiring the now-reducible source rule (Collapse, §6b, realized by
marking it `FLAG_SUBSUMED`). An early draft of this chapter described only the
substitution half; the collapse half is what makes the rule set a Dickson antichain
and is non-optional for termination (§6b, §10).

## 9. Implementation

```rust
// In rebuild(), per AC op f, to fixpoint, alongside recanonize_node.
// Each ACTIVE AC e-node is the ground rule f(M) -> f(minmono(class(M))), oriented
// larger -> smaller by the degree-lex monomial order ≫_f. The RHS is the class's
// MINIMAL MONOMIAL (a multiset over existing constants), NOT the bare class id —
// substituting a class-as-atom reintroduces a fresh constant each round and diverges (§6b).
// INVARIANT: `active` holds only IRREDUCIBLE rules (no LHS ⊊ another LHS) — a
// Dickson antichain. Collapse (below) maintains it; without it, diverges (§6b).

// (B) Superposition critical pairs (Kapur Def. 4), over ACTIVE rules only.
// Overlap candidates share >= 1 child class: the union of by_contains.
for x in M.distinct() {
    for partner in active.by_contains[x] ∩ active.by_op[f] {
        let (a1, ra) = (partner.multiset(), partner.rhs_monomial());  // f(A1) -> f(ra)
        let rm = M.rhs_monomial();                             // f(M)  -> f(rm)
        if multiset_disjoint(&M, &a1) { continue; }            // disjoint => trivial
        let ab = multiset_lcm(&M, &a1);                        // (M ⊎ A1) − (M ∩ A1)
        let c1 = normalize_ac(f, multiset_union(&msub(&ab, &M),  &rm)); // (AB−M) ⊎ rm
        let c2 = normalize_ac(f, multiset_union(&msub(&ab, &a1), &ra)); // (AB−A1)⊎ ra
        if find(c1) != find(c2) { merge(c1, c2); }             // non-trivial, close it
    }
}

// (A)+Collapse — the destructive step that keeps `active` an antichain (§6b).
// When rule f(A1) -> f(ra) is added, retire every active rule it makes reducible.
for parent in active.by_contains-supersets(A1) {              // f(M) -> d with A1 ⊆ M
    if proper_subset(&A1, &parent.multiset()) {
        let red = normalize_ac(f, substitute(parent.multiset(), A1 => ra));  // (A)
        merge(red, parent.class());
        set_flag(parent, FLAG_SUBSUMED);   // <-- COLLAPSE: retire +M (not delete; §6b).
        //                                     index/snapshot builders skip subsumed, so
        //                                     +M is no longer a partner nor a match target;
        //                                     node + its equality +M=d stay for rollback.
    }
}

// normalize_ac reduces a monomial to its NORMAL FORM (a multiset over existing
// constants) by rewriting with EVERY applicable active rule f(A)->f(rA) (A ⊆ current,
// substitute rA) to a fixpoint — every rule is oriented ≫_f so each step strictly
// shrinks in degree-lex and it terminates. It must use ALL current rules (clean AND
// just-minted this round): a reduct still reducible by a same-round rule would persist
// as a partner and re-open the divergence (§6b). Then probe/insert the normal form.
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

A correction to an earlier draft of this section, which claimed "we can drop Kapur's
monomial ordering because the union-find is our canonical layer." That is **wrong**,
and §6b is why. The union-find canonicalizes *classes* (the right-hand sides); it says
nothing about *which left-hand multiset survives* when two rules are comparable, and
that choice is exactly what collapse needs and what keeps `active` a finite antichain.
Two distinct roles:

- **Orientation of each rule `+M = d`** (which side is the LHS): the union-find gives
  this for free — the LHS is the multiset `+M`, the RHS is the canonical class `find(d)`.
  Here the original claim holds.
- **Orientation *between* two rules** (when `+A` and `+M` are containment-comparable,
  which collapses): this needs a total admissible monomial order `≫_f` — concretely
  **degree-lexicographic** (compare multiset size, ties broken by the total order on
  class ids), which satisfies Kapur's subterm + compatibility properties. The larger
  LHS is always the one retired (marked subsumed). Without this the active set is not
  kept reduced, and completion diverges (§6b).

So we still drop the *machinery* Kapur needs for a unique reduced canonical
presentation across AC symbols (we do not need canonical signatures to derive
equalities), but we cannot drop the monomial order itself: it is what orients collapse.

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
  persist, and each merge strictly coarsens the finite class partition. **This step is
  load-bearing and conditional on collapse actually being performed** (§6b): "the loop
  keeps `R` inter-reduced" is not automatic — it is the Collapse/subsumption operation
  doing it. An implementation that skips collapse has no antichain, and Dickson bounds
  nothing observable; it diverges in practice (§6b gives the trace). The termination
  conjecture is a conjecture *about the algorithm with collapse*, not about (A)+(B) alone.

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
