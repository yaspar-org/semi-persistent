# AC Congruence Completeness

This chapter is a self-contained account of how the engine decides equalities over
associative-commutative operators. It develops three ideas in order: (1) why
recanonicalizing AC nodes as flattened multisets, on its own, misses real equalities
(Part I); (2) that the cure is to read the e-graph as a set of rewrite rules and complete
that rule set, tracking each class's minimal monomial `min_monomial` as the rule right-hand side
(Part II, §5c–§9); and (3) that keeping the rule set a *reduced canonical basis*, by
collapsing rules whose left side another rule already covers, is what makes the procedure
both correct and terminating (§6b, §10). The recurring discipline is maintaining a small
reduced basis incrementally as saturation feeds facts in; §0 states it and §5d works it
through one example.

This is the single design reference for the AC completeness story. Part I derives the
problem from first principles (§0 is the short framing); Part II gives the algorithm and the
argument for why it works. For where we stand and what remains, see
[Future Work](A3-future-work.md); for the engine-specific invariants, the matcher details,
and the conformance-to-Kapur review, see the companion
[AC Completion spec](ac-completion-spec.md). For the cost of AC matching (a separate,
matching-side concern), see [Ch 9](09-pattern-matching.md).

---

# Part I, the problem

## 0. The core problem

Two AC facts force *infinitely* many equalities. `a+b = p` already entails `a+b+c =
p+c`, `a+b+d = p+d`, and so on for every multiset with `{a,b}` inside it, with the same
junk on both sides. Add a second fact and they *collide*: `a+b = p` and `a+b+c = q` share
the multiset `a+b+c`, which forces `p+c = q`, a fact nobody stated and the only
non-padding line in the whole infinite pile.

So the AC-congruence-closure problem is **not** "store the equalities"; there are
infinitely many. It is to **maintain, incrementally as facts arrive during saturation, a
tiny finite set of find-and-replace rules that *regenerates* any of those equalities on
demand**, keeping that set *reduced* (no rule's left side contained in another's) so it
stays small. Deciding `g₁ = g₂` is then "rewrite both with the rules until they stop;
equal iff they land in the same place."

Two forces fight each other while saturation runs and new facts keep arriving:

- **Collision (superposition)** *creates* the genuinely-new rules (like `p+c = q`) that
  two overlapping facts force. This is the only source of new equalities; without it
  congruence closure is incomplete (the misses traced in §4).
- **Reduction (collapse / inter-reduction)** *deletes* rules that a smaller rule already
  subsumes. For instance, drop `a+b+c = q` once `a+b = p` and `p+c = q` are known,
  because `a+b+c` just rewrites to `p+c` first. This is what keeps the set finite.

Collision without reduction explodes the rule set: collisions breed redundant rules that
breed more (the divergence we actually hit, §6b). Reduction without collision never
derives the cross-fact equalities (incompleteness, §4). **AC congruence closure is the
discipline of running both, in the right order, to a fixpoint, so the surviving rules
are a reduced canonical basis**, the smallest machine that decides the theory. The rest
of this chapter is how to do that inside an e-graph, where "a rule" is just an AC node
and "delete a rule" cannot mean delete a node.

§5d works this through one concrete example before the formal treatment.

## 0a. Glossary

The chapter uses a fixed vocabulary. Each concept has one word.

- **node** (AC e-node): the stored structure, an operator `f` plus a flattened
  **multiset** of child classes. Hash-consed, immutable, shared. When we mean the data
  in the graph, we say node.
- **rule**: the same node read as a rewrite rule `+M → find(class)`. Every AC node *is* a
  rule (§7); "the e-graph is a set of rules" is the central framing (§0, §5d, §7). When
  we mean the node in its rewrite capacity, we say rule.
- **monomial** / **left side**: the multiset of child classes of a rule, the rule's LHS.
  Kapur's term is monomial; we use monomial and "left side" interchangeably for the LHS.
- **class** (e-class): what `find` returns, the rule's RHS. Always called class. (Kapur
  calls e-classes "constants"; that word appears only in the explicit Kapur mapping of
  §8, where "constant = e-class id in our setting".)
- **superposition** / **critical pair**: the smallest monomial containing two overlapping
  left sides (the lcm, §6 (B)), and the pair of terms it reduces to two ways. Defined in
  §6 (B); used in §6b, §7–§10.
- **collapse** / **inter-reduction**: retiring a rule whose left side contains another
  rule's left side (§6b). Realized by `FLAG_AC_COLLAPSED` (§6b), never by deleting a node.
- **antichain** / **reduced canonical basis**: a rule set in which no left side is a
  sub-multiset of another (an antichain under `⊆`), and which is minimal and confluent.
  Dickson's Lemma (§10) bounds every such antichain to a finite size.

## 0a-bis. Naming convention: representation vs. completion vs. theory

The code uses "AC" in three unrelated senses; conflating them in identifiers caused real
confusion, so the names are split along three axes and "AC" is reserved for exactly one of
them. When reading or extending the code, classify a name by which axis it belongs to.

1. **Representation (`MSet` / `Set`).** How a variadic node stores its children. `MSet` =
   multiset, children `(G, mult)` with counts in ℕ (`+`, `*`); `Set` = set, children bare `G`
   with counts bounded to {0,1} (`and`, `or`, and later `xor`). This is the axis the storage
   and routing layers care about, so the *representation* names appear there: `OpKind::MSet` /
   `OpKind::Set`, `ENodeKind::MSet` / `Set`, `NodeRef::MSet` / `Set`, `nodes.mset` / `nodes.set`,
   `MSetCanon` / `SetCanon`, `register_mset` / `register_set`, `is_mset`, `mset_ops`,
   `mset_child_*`, `mset_buf`. A name carrying `mset`/`set` is about *layout*, never about the
   algorithm. (Why not keep "AC"/"ACI"? "AC" named the multiset representation, but it also
   names the algorithm and the theory below; and "ACI" baked the idempotent *clamp* into the
   representation name, when in fact idempotent and nilpotent ops share one `Set` layout and
   differ only by a clamp field. The representation axis is `{MSet, Set}`; the clamp is separate.
   See `doc/future/multi-ac-aci-completion-plan.md`, "three independent axes".)

2. **Completion procedure (`cc`).** The congruence-closure *completion* this chapter adds
   (superposition + inter-reduction). It is not tied to one representation: it runs over MSet
   today and Set later, so its names use `cc`, never `ac`: `cc` / `set_cc` (the enable flag),
   `cc.rs` (the module), `cc_round`, `CcSnapshot`, `completion_node_ids`, `fold_min_monomial`,
   `min_monomial` (the per-class normal-form representative the round reads as a rule RHS),
   `cc_basis_dump` / `cc_basis_report` and the `cc_*` invariant diagnostics.

3. **Theory name (`AC` / `AC-CC`).** "Associative-commutative congruence closure" is the
   property being established and the literature's term (Kapur, §8, §11, References). It stays
   "AC" in prose and in genuinely theory-level names (`ac_invariants.rs`, the "AC node",
   "AC-CC", "AC congruence" wording). It also stays "AC" for the *matcher* (`ematch`'s
   `ac_find_first` / `ac_scan` / `ac_advance`), which is AC *matching*, a distinct concern from
   completion. A bare "AC" in code should mean the theory or the matcher; if it means a
   representation or the completion procedure, it is misnamed.

The one-line test: layout → `mset`/`set`; the completion procedure → `cc`; the property/theory
or AC matching → `AC`.

## 0b. The e-graph state is a set of rewrite rules

This frames what §6 onward operates on; the mechanics are §5d, §7, and §9a.

An e-graph state denotes a rewrite system in two layers.

- **The AC nodes are the f-monomial rules.** Each AC node with operator `f`, child
  multiset `M`, sitting in class `c`, is the rule `+M → find(c)`: its monomial is the LHS,
  its class the RHS (§7 recovers this by two `find`s). The set of rules is exactly the set
  of AC nodes; there is no separate rule store (§9a).
- **The union-find is the constant/class-rule layer.** It rewrites a class to its
  representative, `c → find(c)`, the analogue of Kapur's constant rules (§8).

Rebuild optimizes that rule set toward a *reduced canonical basis* (§0): the smallest rule
set that decides the same equalities. Three properties define the target.

- **Minimal**: no redundant rule. A rule whose LHS rewrites under the others is dropped
  (collapse, §6b).
- **Inter-reduced / disjoint** (an antichain): no rule's left side is contained in
  another's. Collapse enforces this on each new rule; the surviving left sides are pairwise
  `⊆`-incomparable (§0, §5d, §6b), and Dickson's Lemma keeps that set finite (§10).
- **Confluent**: every two-way rewrite of one term joins. Superposition (§6 (B)) closes
  the divergences that block this; at the fixpoint the basis is convergent and `nf_R`
  decides the theory (§10, §12).

Today's rebuild has only the constant layer and atom-level recanonicalization, so the rule
set is not confluent (§3, §4); the fix (§6) adds superposition and collapse to drive it to
a reduced canonical basis. "Restore AC congruence completeness" is "optimize the rule set
to convergence," worked concretely in §5d and stated against the e-graph in §6–§9.

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

The children form a **multiset**, not a set: multiplicities matter in general. `a + a + b`
flattens to the multiset `{a:2, b:1}`, distinct from `a + b = {a:1, b:1}`, and a rule's
left side carries those counts. The worked examples below (§4, §5d, §6b) all happen to use
multiplicity-1 children, so they read like sets; the data structure is a multiset
throughout.

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

## 5c. The fix as rewrite-system completion

Our union-find and AC nodes form a ground AC rewrite system: each AC node `+M = c` is a rule
`+M → c`, and the union-find is the constant-rule layer (`c → ĉ`). Atom-level
recanonicalization alone (`find` each element, never sub-sums) leaves that system
non-confluent, so two rule orders can drive the same term to two different normal forms
(that divergence is exactly the missed equality of §4). The two operations of §6
(superposition and collapse) make every such divergence joinable, and a standard rewriting
result then applies: a confluent, terminating system has unique normal forms and therefore
decides its equational theory. That is what makes AC congruence closure complete.

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

## 5d. A worked example

`+` flattens to a multiset (order doesn't matter, no nesting; `a+b+c` is just the
multiset `{a,b,c}`). This example uses distinct children, so every multiset is also a set;
multiplicities (e.g. `a+a+b = {a:2, b:1}`) are handled the same way but do not arise here.
We are handed exactly two facts:

```
FACT 1:   a + b      is the same thing as   p
FACT 2:   a + b + c  is the same thing as   q
```

**The uncompressed version** is everything those two facts force to be true. From
FACT 1, gluing anything onto both sides: `a+b+c = p+c`, `a+b+d = p+d`,
`a+b+c+d = p+c+d`, and so on (infinite). From FACT 2 likewise: `a+b+c+d = q+d`, and so
on. Both lists contain `a+b+c`, so their right sides must agree, giving `p+c = q`,
`p+c+d = q+d`, forever. You do not want to store this infinite pile. Almost every line
is just "a fact with junk glued onto both sides." The **one** line that is *not* padding
is

```
p + c = q
```

It is genuinely new: you cannot get it by gluing onto FACT 1 or FACT 2; it falls out of
the two facts *colliding* on the shared term `a+b+c`.

**The compressed version** is two find-and-replace rules:

```
RULE 1:   a + b   →   p
RULE 2:   p + c   →   q
```

The arrow means "wherever you see the left side as a sub-multiset, replace it with the
right side." FACT 2 is now *redundant*; recompute it as `a+b+c —RULE1→ p+c —RULE2→ q`.
We dropped FACT 2 and kept the collision fact instead.

**Recovering any line of the infinite pile:** run both sides through the rules until
they stop, check they land in the same place. Is `a+b+c+d = q+d`? Left:
`a+b+c+d → p+c+d → q+d`. Right: `q+d` (stuck). Same place, so it is true, recovered
without ever storing it. The compressed version is not a lookup table; it is a small
machine that regenerates any line on demand.

**Why keep `p+c` and not `a+b+c`** (the "incomparable left-sides" condition): `a+b+c`
*contains* `a+b`, which is already RULE 1. A rule starting with `a+b+c` would
immediately get chewed by RULE 1 down to `p+c` anyway, so it rewrites itself and is dead
weight. Store the already-chewed version. The rule of thumb: **never keep a rule whose
left side contains another rule's left side.** After you delete all such dead weight, no
left side contains any other. That "antichain" property is not a goal; it is simply
*what is left* once the redundant rules are gone.

**How the machine builds this live.** The basis is not computed once from a fixed
input. Saturation feeds facts in one at a time (each rewrite firing produces a new
equality), and the reduced basis is maintained incrementally as they arrive, since every
new fact can both spawn collisions and make existing rules redundant. Every fact is a
rule; on each new rule you do two chores, then repeat until quiet:

- **Chore A (clean up / collapse):** does the new rule's left side sit *inside* an
  existing rule's left side? Then that existing rule is stale: chew it down with the
  new rule and replace it. Also chew the new rule down by what's already there.
- **Chore B (collision / superposition):** does the new rule's left side *partly
  overlap* an existing one (share atoms, neither inside the other)? Build the smallest
  multiset containing both, rewrite it the two ways, and if the results differ, that
  difference is a new fact: add it as a rule. (Disjoint left sides, sharing no atom,
  cannot collide; skip them.)

Run it on our example. FACT 1 arrives, giving `{a+b→p}`; nothing else exists, no chores.
FACT 2 `a+b+c→q` arrives, and **Chore A fires**: `a+b` sits inside `a+b+c`, so the new
rule is chewed on arrival into `p+c→q`. We never store `a+b+c→q`. Knowledge is now
`{a+b→p, p+c→q}`. Chore B: `{a,b}` and `{p,c}` share no atom, so no collision. Done. The
machine reached the two-rule compressed form by itself, and FACT 2 was swallowed by
Chore A on the way in.

The collision case on its own. Suppose instead the facts were `a+b→p` and `b+c→r` (they
share `b`, neither inside the other). Chore A: neither sits in the other, nothing stale.
Chore B: shared `b`, smallest multiset containing both is `a+b+c` (take the shared `b`
once); rewrite two ways, `a+b+c —(a+b→p)→ p+c` and `a+b+c —(b+c→r)→ r+a`; two results of
reducing the *same* multiset, so `p+c = r+a`, a fact nobody stated. Chore B is the only
way genuinely-new facts are born.

**This is exactly where the blowup comes from.** Skip Chore A, and when FACT 2 arrives the
set keeps `a+b+c→q` *and* derives `p+c→q`, so a rule (`a+b+c`) containing another rule
(`a+b`) stays live. Next round Chore B builds collision multisets off it, breeding more
rules that *also* contain `a+b`, which breed more, generating the infinite pile instead of
the two-rule machine. So the order is fixed: **on each new rule, do Chore A first (chew down
everything it sits inside, and chew it down by what exists), and only then Chore B.** Keep
the rules chewed-down at all times and the set cannot blow up, since a chewed-down set is one
where no rule contains another, and there
simply cannot be many of those (Dickson's Lemma, §10).

The rest of Part II is this mechanism stated precisely against the e-graph: §6 the two
operations, §6b why Chore A (collapse) is required for termination and how "retire a rule" is
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

## 6b. Collapse is required: (A) and (B) alone diverge

(A) and (B) by themselves are *incomplete as an algorithm*. Run them without a third
operation and the pass does not merely slow down; it **diverges**, minting larger and
larger nodes without bound. Concretely, superposition that materializes both reducts and
merges them with no collapse grows the node count ≈4–5× **per round** and the critical-pair
count ≈10× per round on the five-constant §4a example (exponential, OOM within ~15 rounds).
So collapse is as much part of the algorithm as (A) and (B); this section states it.

### The missing operation: Collapse / inter-reduction

Reading each AC node `+M = d` as a rule `+M → d`, the active rule set must be kept
**reduced**: no rule's left multiset is a sub-multiset of another's. This is Kapur's
Algorithm 1 **step 4** ("inter-reduce rules by the new rule") and Conchon et al.'s
**Collapse** inference rule, and it is *destructive*; it removes rules:

> When a rule `+A → a` is added and an existing rule `+M → d` has `A ⊊ M` (so `+M` is
> reducible by `+A`), rewrite `+M` via `+A` (this is exactly (A)), merge the reduct
> into `d`, and **retire `+M` from the active set**.

**"Retire" means flag, not delete** (the realization is the next subsection,
"Retirement = `FLAG_AC_COLLAPSED`"). Kapur and Conchon work over an abstract rule set
they can shrink; an e-graph cannot remove nodes (they are immutable, shared, and must
survive for semi-persistent rollback, `restore`). So we mark `+M` with `FLAG_AC_COLLAPSED`,
which drops it from completion's active set while leaving it hash-consed, in its class
(the equality `+M = d` is preserved), and matchable. "Remove from `active`" throughout
this section means "mark `FLAG_AC_COLLAPSED`," and the antichain is the set of AC nodes
carrying neither that flag nor `FLAG_SUBSUMED`.

The active set is then a **Dickson antichain**: a set of multisets over the finite
class pool `C`, pairwise `⊆`-incomparable. Dickson's Lemma makes every such antichain
finite, and for typical inputs it stays near the input size. Since superposition (B)
ranges over pairs of *active* rules, the work per round is `O(|active|²)`. Conchon's
empirically quadratic cost (§7.3) is a statement about `|active|`, and it holds **only
because collapse keeps `|active|` an antichain**.

Collapsing a rule loses no equality. Before `+M` is collapsed, its content is *already
preserved twice*: the merge `reduct(+M) = d` has been performed (so `+M`'s class is still
`d`), and the reduct itself is a live, non-collapsed node carrying the same class. So
every consequence `+M` could contribute as a superposition source is also derivable from
its reduct, which *is* active. Collapse therefore prunes only *redundant* sources (the
composite superpositions of Kapur–Musser–Narendran), never a prime one, which is exactly
why completeness survives. The collapsed node remains a legal *child* of other live nodes,
keeps its class membership, and stays matchable; it simply stops being enumerated as a
completion rule LHS.

### Retirement = `FLAG_AC_COLLAPSED`: tombstone two roles, keep two

"Retire a rule" cannot mean "delete a node" here. A node plays **four** roles, and
collapse retires only two of them; getting the split, and its *ordering*, right is the
whole correctness story. The trigger for collapsing a node is precise: **a node is
collapsed when its children can be rewritten by *some other* node.** `+{a,b,c}` with
`+{a,b}=p` known has its sub-multiset `{a,b}` reduce to `p`, so it is collapsed. (Note
"some *other* node": a rule's own left side is never reducible by itself; only a smaller,
different rule makes a node reducible.)

**Retire it from the two *active* roles** (both completion-internal):

1. **Superposition source.** A collapsed node must never again be the node we build
   overlap multisets *from* (Chore B). It is reducible, so every collision computed off
   it is redundant (a *composite* superposition, Kapur–Musser–Narendran), and these are
   exactly the copies that bred the divergence. Pull it out of the set Chore B iterates.
2. **Collapse source for others.** It must not be used to rewrite *other* nodes either.
   A reducible rule reducing things only lengthens derivations and adds churn; let
   irreducible nodes do the rewriting. (Not a soundness issue, a termination/effort one.)

**Keep it in the two *passive* roles:**

3. **Its class membership / the merge it caused.** Collapsing `+{a,b,c}` rewrote it to
   `+{p,c}` and merged that into `q`. That merge is the point: it is the equality we set
   out to derive. Retiring the node must not undo it; the fact did not vanish, it
   relocated to `+{p,c}`, which is live.
4. **Being a child of larger nodes, and being matchable.** If `+{a,b,c}` sits inside some
   `h(+{a,b,c}, x)`, that parent still points at it and needs it to recanonicalize.
   Hard-erasing it from the hash-cons would dangle that pointer. It also stays a legal
   match target: it is a real node in a real class, and the matcher binding it is
   harmless (its reduced form `+{p,c}` is in the same class).

So collapse sets **`FLAG_AC_COLLAPSED`, a flag distinct from `FLAG_SUBSUMED`, not a
delete.** It removes the node from completion's active set (the superposition / collapse
sources), while leaving it fully hash-consed, in its class for parents, and **matchable**.
(Nodes are immutable and shared, and `mark`/`restore` rolls the node store back to a
token; deleting would corrupt that history. The flag is part of the rolled-back node
state, so a node collapsed after a `mark` is un-collapsed on `restore`.)

**Two distinct flags, two distinct concepts.** It is tempting to reuse `FLAG_SUBSUMED`
for collapse, but they mean different things and the conflation hides a bug:

| flag | meaning | matchable? | a completion rule? |
|---|---|---|---|
| `FLAG_SUBSUMED` (user `(subsume …)`) | "do not match this node" | **no** (indices skip it) | no |
| `FLAG_AC_COLLAPSED` (completion) | "not a completion rule" (LHS reducible) | **yes** | no |

Completion's active set is the AC nodes with *neither* flag; the matcher's visible set is
the nodes without `FLAG_SUBSUMED`. **Matcher visibility is irrelevant to completion's
termination**: the matcher never superposes, so a collapsed-but-visible node cannot
breed critical pairs. Divergence is caused only by a collapsed node staying a
*superposition source*, which `FLAG_AC_COLLAPSED` prevents directly. Hiding a collapsed
node from the matcher would be a *separate, optional* choice (usually a no-op, since its
reduced form is in the same class), and forcing it via `FLAG_SUBSUMED` would wrongly
couple completion to user-subsume semantics.

**The critical ordering: materialize+merge first, mark second, eager before
Chore B.** Two ways to get it wrong:

- **Merge before mark.** Materialize the reduct `+{p,c}`, merge it into the class, and
  *only then* set `FLAG_AC_COLLAPSED` on `+{a,b,c}`. Reverse the order and you have
  retired a node before its equality was re-established elsewhere, losing information.
  (Because collapse keeps the node matchable this is less dangerous than under subsume,
  but the merge must still land first so the reduced form exists. The §5b cancellation
  case depends on the reduced node existing before matching proceeds.)
- **Eager within the round.** The flag must gate Chore B *in the same round* the node
  becomes reducible. If this round's superposition pass still sees it, it breeds anyway.
  (Our round structure rebuilds the active set each round and skips `FLAG_AC_COLLAPSED`,
  which gives this.)

### Why omitting collapse diverges (and why hash-consing does not save it)

Drop collapse and the "antichain" stops being one. The reduct `(AB − A) ⊎ {a}`
injects the rule's right-hand class `a`, which need not lie in `AB` (the §10
correction). So a reduct can be a **proper superset** of an existing rule's
left side (i.e. itself reducible), yet, materialized raw, it survives as a live node
and therefore as a superposition source for the next round. Round 1 superposes `n`
rules into `~n²` reducts; each becomes a partner; round 2 superposes `~n²` into
`~n⁴`; cascade. Dickson still guarantees eventual termination, but over a growing
*chain*, not the antichain, so the bound is astronomical: the observed exponential.

It is tempting to think hash-consing already handles this: "materialize the reduct
and let the hash-cons merge it with whatever exists." It does not. **Hash-consing
resolves only *syntactic* collisions (identical multisets), which is the atom-level
congruence we already have.** AC completion is about *sub-multiset* congruence (§3),
which hash-consing structurally cannot see. Inserting `+{a,b,s}` when `+{a,b} → t`
exists produces a *fresh* class (no identical multiset is present); the node is
semantically reducible (`{a,b} ⊊ {a,b,s}`, so `+{a,b,s} = +{t,s}`) but the e-graph
does not know it, and it now drives superpositions. The reducible form must be
**normalized away before it becomes a node**; equivalently, reducible nodes must
never be superposition sources (the *prime superposition* criterion,
Kapur–Musser–Narendran 1988: a superposition whose overlap term is reducible
elsewhere is *composite*, and its critical pair is redundant).

### Superposition is bounded; substituting a class-as-atom is what explodes

It looks paradoxical that the algorithm superposes rule left-hand sides (which are,
by orientation, the *larger* (non-minimal) monomials) yet does not blow up. If the
sources are the big sides, why don't bigger and bigger terms cascade? Three facts make
superposition bounded, and locate the real explosion elsewhere.

1. **A critical pair is bounded by the lcm of two existing left sides.** Superposing
   `A₁ → B₁` and `A₂ → B₂` builds `AB = lcm(A₁, A₂)` (the component-wise max of two
   left sides already present), and the two reducts `(AB − Aᵢ) ⊎ Bᵢ` are each
   **strictly smaller than `AB`** in the degree-lex order, because each rule is
   oriented `Bᵢ ≺ Aᵢ`. The output of a superposition is bounded by its inputs. There is
   no upward pressure *from superposition itself*, provided the constant pool does not
   grow.

2. **The explosion comes from introducing a new atom, not from superposition.** It is
   the right-hand side of the closing merge that matters. When the critical pair
   `+{c,d} = +{a,e}` is closed, the merged class must be substituted back into other
   monomials. Substitute the **bare class id** `κ` of that class and `κ` becomes a
   *new constant* used as a single summand: `+{b,d,c}` reduces to `+{b, κ}` instead of
   to `+{b} ⊎ {a,e} = +{a,b,e}`. Now lcms range over `{a,b,c,d,e,κ,…}`, the pool grows
   every round, and *that* is the runaway: not the superposition, the fresh atom.
   The fix is to orient the critical pair as a rule between **two monomials** over the
   *existing* constants (`larger → smaller`, never `→ κ`), and to substitute a class by
   its **minimal monomial** (its degree-lex-least representative), never by a
   class-as-atom. Then `+{b,c,d} → +{a,b,e} → +{c,e}` (via `+{a,b}→c`) joins the other
   reduct `+{c,e}`: the pair is trivial, nothing new is added, and the §4b system
   converges to three rules over `{a,b,c,d,e}` with no new constant ever introduced.

3. **Collapse keeps the count finite even though sizes are bounded.** Bounded-size
   monomials could still accumulate in *number*; collapse (above) retires every left
   side that becomes reducible, so the surviving left sides are a Dickson antichain,
   hence finite. Narendran–Rusinowitch (RTA 1991): every ground AC theory has a finite
   canonical system, and this is the construction of it.

So "superpose only non-minimal monomials" is not an extra trick: a rule's left side
*is* the non-minimal side, and the minimal monomial of a class is its normal form, has
no rule on its left, and is therefore never a redex nor a superposition source. The two
essential choices are the ones above: **orient critical pairs between monomials over
the existing constants (minimal-monomial RHS, no fresh atom), and collapse.** Get those
right and superposition is `O(|active|²)` per round over a finite antichain; get the RHS
wrong (substitute the class id as an atom) and it diverges regardless of collapse.

### Worked example: two rules, hand-checkable

`+` AC, atoms `a, b, c`, right-hand classes `s, t`. Input:

```
R1:  +{a, b, c} → s        R2:  +{a, b} → t
```

The only structural fact: `{a,b} ⊊ {a,b,c}`, so **R1 is reducible by R2** (no order
needed; collapse fires on containment alone). The reduced canonical system is the
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
summand**, and `{a,b,s}` is reducible by R2 but, inserted raw, survives as a
partner. Round 3 superposes the new nodes against everything sharing an element,
`w` re-enters as a summand, the constant pool grows `{a,b,c,s,t,w,…}`, and each round
mints `O(current nodes)` new classes. That is the divergence.

Note the two distinct mistakes this run makes, matching the two preceding subsections:
it never collapses R1 (so the reducible `+{a,b,s}` persists as a partner), **and** it
closes the critical pair into a fresh class `w` used as a summand (the class-as-atom
explosion). Either alone diverges; the fix needs both.

The correct run *decides* `{a,b,s} = {s,t}` by normalising (`{a,b,s} → {t,s}` via R2,
same as the other side, both over existing constants) and stores neither: collapse
plus normalize-into-minimal-monomial is the step that cannot be skipped.

### What this requires of the implementation

1. **Maintain an `active` set of irreducible AC nodes** per op (those with no
   containment partner), concretely the AC nodes carrying neither `FLAG_AC_COLLAPSED`
   nor `FLAG_SUBSUMED`. Superpose (B) only over `active`.
2. **On adding `+A → a`**, find its containment supersets via `by_contains`; for each
   active `+M` with `A ⊊ M`, reduce (A), merge, and **mark `+M` `FLAG_AC_COLLAPSED`** (the
   non-deletable form of "retire"; the node, its class, and its matchability persist).
3. **Normalize every reduct against *all* current rules** (including those minted this
   round) to a fixpoint before comparing (see the `normalize_ac` correction in §9).
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

### Flattening (`WF_flat`) and the matcher-crash gate

The engine requires **AC terms to be flattened** (`WF_flat`): an `f`-node never has an
`f`-class child. This is a canonicalization invariant, not a completion-specific one: the
materialization invariant of §1 needs every summand to be a real summand, and a nested
`+f(+f(…),…)` hides one. §6c states exactly what to flatten (the class summand-form), why it
runs at build only (recanonicalization-time flattening is provably vacuous, by the lemma
there), and why keying the flatten on the union-find representative is the wrong choice.

### 6c. Continuous flattening: what to flatten, and the representative trap

The naive build-time flatten ("splice a child whose representative is an `f`-node") is
**wrong**, for a reason that is the heart of the difficulty. During recanonicalization of
`+{a, b, c}`, the elements `a, b, c` are **e-class ids**, not terms. A class is equivalent
to many syntactic forms at once: class `a` may contain a node `+{x, y}` *and* a leaf node
*and* an `h(...)` node, all merged. "Is `a` a sum to splice?" has no syntactic answer, and
asking "is `find(a)` an `f`-node?" answers it by whichever representative the union-find
happened to pick. That representative depends on merge order, so a flatten keyed on it is
**not a function of the e-graph state**: the same class flattens or not depending on
history. A canonical form that depends on merge order is not canonical. This is the trap.

The resolution is to flatten on a **representative-independent, per-class property**: the
class's *canonical summand form*, which is exactly what the completion machinery already
maintains in the per-class slot (§9a) and reads via the rule-RHS function:

```
summand_form(class) = if atomic(class) { {class} }            // a single atom
                      else              { min_monomial(class) }      // its minimal f-monomial
```

`atomic` and `min_monomial` are merge-folded class properties (§9a), independent of which node
is the representative. So flattening becomes: **when canonicalizing an `f`-node, replace
each child `c` by `summand_form(c)`; if that is a multi-element monomial, splice it in
(recursively); if it is the single atom `{c}`, keep `c` as a summand.** This is a function
of the e-graph state, not of the representative, so the flattened node is genuinely
canonical.

Why this is the *right* predicate, and what it does to the worked examples:

- **A class is "a sum to splice" iff it is non-`atomic`.** `atomic` (§9a) means "referenced
  as a child of some node, or holding a non-AC node": the size-1 monomial `{class}`
  is itself a legitimate, present term, so the class *is* a valid atom and must be kept as
  one. A non-`atomic` class is a pure `f`-sum that exists only as a sub-expression of larger
  sums; it has no standalone atom form, so it must be spliced. This is the same `atomic`
  distinction that orients completion's rule RHS; flattening and completion agree by
  construction.

- **§5b is preserved.** In §5b, `c = +{a,b}` is a child of `neg(c)`, so its class is
  `atomic`. Canonicalizing `+{c, neg(c)}` therefore expands `c` to `summand_form(c) = {c}`
  (atomic), *keeping* `c` as one summand: the node stays `+{c, neg(c)}`, two summands, and
  the cancellation rule `(+ ?x (neg ?x))` fires, so §5b's `t = 0` survives flattening. Note
  the representative-keyed predicate would *wrongly* splice `c` (because some representative
  of its class is `+{a,b}`); the summand-form predicate does not, precisely because the class
  is `atomic`. This is the representative trap again, and why the predicate must be
  `summand_form`, not `find`.

- **§4b's nested node is flattened.** A pure intermediate sum (e.g. a critical-pair reduct's
  inner `+{a,b}` that is *not* referenced as a standalone atom anywhere) is non-`atomic`, so
  `summand_form` returns its monomial and it is spliced. The matcher never meets it.

So `atomic` is the decisive distinction in *both* directions: it tells completion when
an RHS may be the bare class id (§9a), and it tells flattening when a child is a real atom
to keep versus a pure sum to splice. There is no separate "exempt atomic from flattening"
hack; flattening simply reads `summand_form`, which is `atomic`-aware by definition.

**Why inlining a non-atomic child is sound.** Consider the parent being built, `+{…, c, …}`,
and ask what the class id `c` denotes *as one summand*. If `c` is non-atomic, then by
definition `c` holds no non-AC node and is referenced by no node, so nothing in the graph
grounds `c`-as-a-single-element; the only term `c` is equal to is its own sum
`min_monomial(c) = +{p, q}`. Associativity then gives `+{…, c, …} = +{…, p, q, …}`: spelling the
child as the class id and spelling it as the inlined summands `p, q` denote the *same* AC
term. So splicing is meaning-preserving. It is also *forced*, not merely allowed: keeping
`{c}` would assert that `c` is a standalone element, which no node witnesses, and feeding
that bare class id back as a rule RHS is exactly the class-as-atom divergence (§6b). For an
atomic `c` the inverse holds: some node *does* ground `{c}` (a non-AC member, or `c`'s
occurrence as a child elsewhere), so `{c}` is a real element and must be kept, on pain of
destroying a shape another rule needs (the §5b `+{c, neg(c)}` case). Inlining is sound for
non-atomic and unsound for atomic, which is precisely what the `summand_form` predicate
encodes.

**The inlined class does not disappear.** Flattening rewrites the *child list of the new
node*, never the inlined class. When `add(+, [c, d])` splices `c`'s sum to build
`+{p, q, d}`, the class of `c` (its node `+{p, q}`, its `min_monomial`, its use-list, its
membership) is left untouched: it stays in the union-find, stays hash-consed, stays found by
`find`. Nodes are immutable and are never deleted (rollback depends on it; "retire" elsewhere
means a flag, §6b, not removal). The only effect is that the new node never *holds* `c` as a
child; since `c` was non-atomic, no other node held it as a child either, so afterward `c` may
simply be a live class that nothing uses as a summand, fully intact, not gone. Inlining is a
choice the parent makes about how to spell its own children, not an operation on `c`.

**Where flattening runs: build only, and that is complete.** A child is spliced exactly
when it is non-atomic, i.e. a pure `+`-sum that contains no non-AC node and is referenced
by no node (§9a). Flattening therefore needs to run only at the one place a non-atomic
class can appear as a candidate child: `add`. Before the AC arm sorts and coalesces,
`flatten_ac_children` replaces each child by its `summand_form` (`{c}` if atomic, else
`min_monomial(c)`) and splices the non-atomic ones, to a fixpoint.

Recanonicalization does **not** need a flattening pass. This is a lemma, not an omission.

> **Lemma (stored children are atomic).** Every class stored in an AC node's child multiset
> is atomic, from the node's creation onward.
>
> *Proof.* At creation, `add` flattens first, so it splices exactly the non-atomic children;
> every surviving stored child is atomic at that instant. `add` then `add_use`s each
> survivor, which sets its class atomic regardless. `atomic` is monotone (set on `add_use`
> and on gaining a non-AC member, never cleared) and is OR-combined on merge. Recanon only
> ever replaces a stored child `c` by `find(c)`, the survivor of `c`'s class, whose atomic
> bit is the OR of the merged classes' bits, hence still true. So a stored child is atomic at
> creation and stays atomic through every merge and recanon. ∎

> **Corollary.** Recanon-flatten is vacuous. Its trigger is a stored child that is
> non-atomic, which by the lemma never occurs: recanon `find`s each element, re-sorts, and
> coalesces, and `summand_form` of every (atomic) element is `{element}`, so nothing is
> spliced. A recanon-time flatten pass would scan, find every child atomic, and splice
> nothing.

The intuition: the act of *using* a class as an AC child is exactly what makes it atomic,
permanently, so by the time a class is stored in a multiset it can never again be a splice
candidate. Inlining is fundamentally a build-time operation, on a child that is non-atomic
*at the moment its parent is built*; building the parent then makes it atomic forever after.

A worked trace (watch `atomic([S])`):

```
1. add a, b, d, p             leaves; each class atomic (contains a non-AC node)
2. s := add(+, [a,b])         node S0 = +{a,b}, class [S].  add_use(a,S0), add_use(b,S0).
                              [S] contains only S0 and is nobody's child  ⇒  atomic([S]) = FALSE
3. u := add(+, [s,d])         summand_form([S]) non-atomic ⇒ SPLICE min_monomial {a,b};  d atomic ⇒ keep
                              node U = +{a,b,d}.  U never stores [S]; [S] is not add_use'd here.
```

The only inline fired in step 3, at build, while `[S]` was non-atomic. To make `[S]` a
*stored* child (so recanon could even see it), it must be atomic when its parent is built,
otherwise step-3 flatten splices it:

```
4. n := add(neg, [s])         add_use([S], n)  ⇒  atomic([S]) = TRUE  (now and forever)
5. w := add(+, [s,p])         find(s)=[S] atomic ⇒ summand_form = {[S]} ⇒ keep
                              node W = +{[S], p}   (W stores [S], because [S] is atomic)
6. union([S],[M])             survivor.atomic = atomic([S]) ∨ atomic([M]) = true
7. recanon W                  find([S]) = survivor (atomic) ⇒ KEEP, no splice  ⇒  W' = +{survivor, p}
```

At step 7 recanon does exactly what it always does, `find` and keep; the child is atomic so
nothing inlines, even though its class just merged. There is no sequence that makes a stored
child non-atomic; that is the lemma.

The trap this rules out (the representative-keyed mistake): at step 7, `survivor`'s
*representative node* might be the sum `+{a,b}`, so a flatten keyed on "is `find(c)` a
`+`-node?" would wrongly splice it, destroying the `+{c, neg(c)}` shape the §5b cancellation
rule needs. Keying on `atomic` (not on `find`) refuses that splice. So the condition that
*can* hold during recanon is "the representative is a sum", and keying on `atomic` rather
than the representative is exactly what makes recanon-flatten correctly do nothing there.

Conchon et al. (AC(X), LMCS 2012) is the precedent: §3 flattens in the canonizer
syntactically, and §4.1 Def 4.1 re-applies the canonizer after **every** rewrite. Our
twist is that "syntactic head symbol" becomes "the class's `atomic`-determined summand
form", because in an e-graph a child is a class, not a term. And under that change the
"re-apply after every rewrite" obligation discharges for free: by the lemma above, the
re-applied flatten is a no-op, because keying on `atomic` (a monotone class property)
rather than on the current syntactic head means a child that was flattened once cannot
un-flatten. The §8 instantiation issue
Conchon leaves open (a rule needing a variable to bind an un-materialized sub-sum) is a
genuinely separate AC-matching problem (§11) and does **not** include §5b, whose sub-sum
`c` *is* materialized and *is* atomic.

## 7. Implementing the substitution from existing machinery

The fix is a new rebuild pass over pairs of existing AC nodes. It reuses two
mechanisms we already have, and it is worth being precise about what each does,
because the search and the arithmetic are separate steps.

First, the reading that makes the rest of this section work: an AC node records a
rewrite rule, and the rule is recovered by **two separate `find`s in two different
places**. A node has no `find` of its own; only a *class* does. So:

```
rule of a node  =  +{ find(child₁), find(child₂), … }  →  find(class the node sits in)
                   └─────────── left side ──────────┘     └──── right side ────┘
```

`find` on the **children** builds the left side (the canonical sub-multiset); `find` on the
**class** builds the right side (the single class the node reduces to). The set of
rules is exactly the set of AC nodes; we build no separate rule store.

One point worth stating outright, because it is easy to assume otherwise:
**which representative the union-find picks for a class does not matter.** Rank-based,
arbitrary, whatever: it washes out completely; the equalities the procedure decides
are identical regardless of which class member is the rep. Representative *selection*
is not a thing to be careful about here. (It would matter only if we later wanted one
canonical *printed* form for extraction, not for deriving equalities.) What *does*
need care is firing a kind of rule the union-find never fires; that is the next point.

Recanonicalization already fires the node-rules, but only the *single-child* kind.
When a child's class moves, recanon swaps that one child for its `find` and rehashes;
that is exactly rule-firing on `+{ find each child }`. What it never does is notice
that a whole **sub-multiset** of a node's children is itself a known node equal to some
class, and substitute *that*. Concretely: node `+{a,b,c}` with `+{a,b}` in class `p`.
Recanon runs `find` on `a`, on `b`, on `c` (all atoms, nothing moves) and walks away;
it never sees that the sub-multiset `{a,b}` equals `p`, so it never reaches `+{p,c}`. No
choice of representative fixes this: the union-find simply has no operation that
substitutes a *group* of children at once. **That missing operation, substitute an
equal sub-multiset, not just an equal single child, is the entire fix** (§6 (A)/(B)).

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
# by_contains/by_op range over ACTIVE AC nodes only: no FLAG_AC_COLLAPSED, no FLAG_SUBSUMED (§6b).
partners = ⋃_{x ∈ distinct(M)} by_contains[x]  ∩  by_op[+]   # active AC nodes sharing ≥1 element with M
for each partner +A = a in partners:
    if A ⊊ M:        # (A) inter-reduction:  A properly contained in M
        substitute a in for A, merge, and mark +M FLAG_AC_COLLAPSED  # collapse (§6b)
    elif A ∩ M ≠ ∅:  # (B) superposition:    A and M only overlap
        build the lcm node, normalize both reducts to normal form, merge if distinct
```

We never look up a multiset, only individual shared elements; disjoint pairs (no
shared element) are skipped, since their critical pair is trivial (§6). The collapse
on `A ⊊ M` (marking `+M` `FLAG_AC_COLLAPSED`) and the normalize-before-merge in (B) are
the non-optional steps §6b derives; without them this loop diverges.

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
| `DecomposeAC`'s multiset-subtract + `rest` | enumerate sub-sums transiently, then discard | compute `(M − A) ⊎ {a}` for a chosen pair, normalize, materialize, merge, and on `A ⊊ M` mark `+M` `FLAG_AC_COLLAPSED` (collapse, §6b) |
| per-node flag + skip in the active-set scan | `FLAG_SUBSUMED` hides a node from the matcher (user `(subsume …)`) | `FLAG_AC_COLLAPSED` retires a reducible rule from completion without deleting it or hiding it from the matcher (§6b) |

The two layers stay separate: flattening and recanonicalization keep doing
atom-substitution congruence; this pass adds the sub-sum-substitution congruence.
Together they are full AC congruence closure, at `O(n)` per term plus the finite,
demand-driven set of substituted nodes.

## 8. Our rebuild is Kapur's ground AC-CC algorithm

The data structures map one-to-one onto Kapur's ground AC-CC framework (FSCD 2021),
which flattens AC terms, introduces a constant per subterm, and maintains constant
rules `c → ĉ` and f-monomial rules `f(M) → c`. Kapur's "constant" is our e-class id;
the word "constant" in this section and §12 means e-class id throughout.

| Kapur (FSCD 2021) | Our e-graph |
|---|---|
| Constants (extended signature) | e-class ids |
| Constant rules `c → ĉ`, inter-reduced (Algo 1 step 1, Tarjan Union-Find) | our union-find |
| f-monomial rule `f(M) → c` | an AC e-node: canonical child multiset `M`, class `c` |
| `Sf` (f-monomial equations for `f`) | `by_op[f]` |
| Normalize `Sf` using `RC` (Algo 2 step 2) | `recanonize_node` (have) |
| Propagate constant equalities across symbols (Algo 2 step 4) | rebuild's merge loop (have) |
| Flat uninterpreted rules `h(c₁..) → c` (§4) | non-AC congruence closure |
| Generate critical pairs (Algo 1 step 3) | superposition (B), §6 |
| Inter-reduce rules by new rule (Algo 1 step 4) | substitute the reduct (A) **+ Collapse** (§6b) |

So rebuild *is* Kapur's General Congruence Closure (Algorithm 3): step 1 (constant rules) is
the union-find, step 2 (normalize `Sf`) is `recanonize_node`, step 3 (critical pairs) is
superposition (B), and step 4 is the two halves of inter-reduction, substituting the reduct
(A) **and** retiring the now-reducible source rule (Collapse, §6b, realized by marking it
`FLAG_AC_COLLAPSED`). Step 4 being *two* things is the essential subtlety: the collapse
half is what makes the rule set a Dickson antichain and is what termination rests on (§6b,
§10); substitution alone would diverge.

## 9. Implementation

```rust
// In rebuild(), per AC op f, to fixpoint, alongside recanonize_node.
// Each ACTIVE AC e-node is the ground rule f(M) -> f(minmono(class(M))), oriented
// larger -> smaller by the degree-lex monomial order ≫_f. The RHS is the class's
// MINIMAL MONOMIAL (a multiset over existing constants), NOT the bare class id:
// substituting a class-as-atom reintroduces a fresh constant each round and diverges (§6b).
// INVARIANT: `active` holds only IRREDUCIBLE rules (no LHS ⊊ another LHS), a
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

// (A)+Collapse: the destructive step that keeps `active` an antichain (§6b).
// When rule f(A1) -> f(ra) is added, retire every active rule it makes reducible.
for parent in active.by_contains-supersets(A1) {              // f(M) -> d with A1 ⊆ M
    if proper_subset(&A1, &parent.multiset()) {
        let red = normalize_ac(f, substitute(parent.multiset(), A1 => ra));  // (A)
        merge(red, parent.class());
        set_flag(parent, FLAG_AC_COLLAPSED);  // <-- COLLAPSE: retire +M (not delete; §6b).
        //                                       completion's active scan skips collapsed,
        //                                       so +M is no longer a partner; it stays
        //                                       matchable, a child, and in class d, for
        //                                       rollback. (FLAG_AC_COLLAPSED, not subsume.)
    }
}

// normalize_ac reduces a monomial to its NORMAL FORM (a multiset over existing
// constants) by rewriting with EVERY applicable active rule f(A)->f(rA) (A ⊆ current,
// substitute rA) to a fixpoint; every rule is oriented ≫_f so each step strictly
// shrinks in degree-lex and it terminates. It must use ALL current rules (clean AND
// just-minted this round): a reduct still reducible by a same-round rule would persist
// as a partner and re-open the divergence (§6b). Then probe/insert the normal form.
```

Index maintenance and round structure. The pass is a worklist fixpoint (the same shape
as the rest of rebuild). The pseudocode above is written as a batch round against a
frozen `by_contains` snapshot, which is the simplest correctness model: a round buffers
new nodes and merges, refreshes the index, and iterates, so a node created in round `k`
is processed in `k+1`; this loses no critical pair, because a pair one partner of which
did not yet exist is caught the round after both exist, and the loop exits only when a
whole round adds nothing. The only requirement is fairness (no pair starved). §9a
describes the intended *incremental* realization (a completion worklist interleaved with
the congruence worklist, no per-round rebuild of any index or rule store); the batch round
is a correctness-equivalent, allocating stand-in for it.

It is tempting to think the union-find lets us drop Kapur's monomial ordering entirely,
since it is already our canonical layer. It does not, and §6b is why. The union-find
canonicalizes *classes* (the right-hand sides); it says nothing about *which left-hand
multiset survives* when two rules are comparable, and that choice is exactly what collapse
needs and what keeps `active` a finite antichain. Two distinct roles:

- **Orientation of each rule `+M = d`** (which side is the LHS): the union-find gives
  this for free: the LHS is the multiset `+M`, the RHS is the canonical class `find(d)`.
- **Orientation *between* two rules** (when `+A` and `+M` are containment-comparable,
  which collapses): this needs a total admissible monomial order `≫_f`, concretely
  **degree-lexicographic** (compare multiset size, ties broken by the total order on
  class ids), which satisfies Kapur's subterm + compatibility properties. The larger
  LHS is always the one retired (marked `FLAG_AC_COLLAPSED`). Without this the active set
  is not kept reduced, and completion diverges (§6b).

So we still drop the *machinery* Kapur needs for a unique reduced canonical
presentation across AC symbols (we do not need canonical signatures to derive
equalities), but we cannot drop the monomial order itself: it is what orients collapse.

## 9a. Data structures and the incremental architecture

§9's pseudocode reads as a batch round for clarity, but the engine constraint is that
this runs inside `rebuild`, a hot loop, so two rules govern the real implementation: no
heap allocation per round, and no parallel rule store. Both follow from the principle
already stated in §7 (*the AC nodes are the rule set*) and from the existing `rebuild`
scratch discipline.

**The rule set is the nodes; there is no separate store.** The tempting shortcut is to scan
every node each round and build `HashMap`s of monomials, atomicity, and a `Vec<Rule>` of
owned left/right multisets, but that is the "store the equalities" mistake of §0 in
miniature: recomputing the whole basis every round instead of maintaining it. The active
rules *are* the AC nodes carrying
neither `FLAG_AC_COLLAPSED` nor `FLAG_SUBSUMED`; a rule's left side is read on demand as
`+{find each child}`, its right side from the per-class minimum (below). Partner-finding
(`by_contains[x]`) is a filtered walk of child class `x`'s **use-list**, the same
`classes.uses()` arena that ordinary congruence already maintains, not a rebuilt index.

**Per-class minimum monomial lives in the e-class sparse set, maintained O(1) on merge
(not recomputed).** The rule right-hand side is the class's `≫_f`-least monomial (§9), and
completion reads it constantly: once per rule's RHS and once per `normalize_ac` step. It
must therefore be O(1) to read. Recomputing it on demand (walk the class's use-list,
filter to AC monomials, take the min) is correct and needs no storage, but it turns every
read into an O(class-size) scan, exactly the per-query work this section exists to remove.
So we **store** it and maintain it on merge.

`EClasses` already stores per-class data in a `SparseSet` keyed by the class's `repr_id`:
today the value is the use-list id. We **widen that value** to a small `Copy` struct
`{ use_list, min_monomial }` (two `DenseId`s) rather than adding a second sparse set, so the two
per-class facts share one slot and cannot desync. The struct derives `Tagged` by
delegating the tag to its first field (the precedent is `ListNode` in `containers/list.rs`,
`Repr = (L::Repr, T::Repr)`), so `InlineStore` works unchanged at both id widths, with no
bit-packing constraint. `min_monomial` seeds to the node itself in `add_singleton`, is dropped
with the absorbed class in `splice_classes`, and rides the existing `SparseSetToken` in
`EClassesToken`, so **`mark`/`restore` roll it back for free**, with no change to
`EGraphToken` or `EGraph::mark`/`restore`. On merge, the survivor's `min_monomial` becomes the
`monomial_cmp`-smaller of the two classes' minima: O(1), no search. `EClasses` has no AC
knowledge, so the comparison is done by the `EGraph::merge` wrapper (which sees both the
classes and the node store) and the result is written into the survivor's slot;
`MergeInfo` carries the absorbed class's `min_monomial` out for that.

**The rule RHS is not always `min_monomial`: an `atomic` flag rounds out the slot.** The right
side of a rule `+M → R` is the class's normal-form representative, its `≫_f`-least
*usable* monomial. The smallest candidate is the size-1 monomial `{classid}`, the class
used as a single summand, smaller than any multi-element sum. But `{classid}` is a legal
monomial only if the class is **atomic-usable**.

A class `c` is **atomic-usable** when the term "`c` as one summand" is grounded by an
actual node, so that writing `c` inside a monomial denotes something real. Equivalently:
`c` can stand on its own as an element of a larger AC term. That holds in exactly two
situations:

- the class holds a **non-AC node** (a leaf constant, a `Plain`/`Lit` node, or a node of
  another operator); then `c` directly denotes that term, so `{c}` is a real one-element
  monomial; or
- the class is **referenced as a child of some node**; then `c` already occurs as an
  element inside some existing monomial `+{… c …}`, so using `c` as a summand denotes the
  same element that node already uses.

If neither holds, the class is a pure AC-sum that occurs as nobody's child (for example a
class created only by a critical-pair merge): no node grounds `{c}`, so `c` is **not**
atomic-usable, and its representative must be the smallest actual `+`-monomial, `min_monomial`.
Writing `{c}` for such a class would name an element no node denotes, which is the
class-as-atom divergence of §6b: it injects a fresh constant every round.

Concretely. `+{a,b}` in class `c`: if `neg(c)` exists (so `c` is a child of `neg`), then
`c` is atomic-usable and the rule is `+{a,b} → {c}`, which lets `c` substitute into other
sums. If instead `c` arose only as a critical-pair reduct and nothing references it, it is
not atomic-usable, and its rule RHS stays `min_monomial`, the least `+`-monomial in the class.
"Atomic-usable" is thus a property of how the class is *used*, not of what it contains: a
compound sum becomes atomic-usable the moment something takes its class as a child.

**Why this matters.** The rules `+{a,b} → {c}` in §4b and §5b exist precisely
because `c` is atomic-usable there (`c` is a child of other nodes). The `{c}` right side is
what lets those rules superpose (§4b) and inter-reduce (§5b). If `c`'s RHS were instead its
own monomial `{a,b}`, the rule would be the trivial `+{a,b} → +{a,b}` and those critical
pairs would never fire; completion would silently lose the equalities it exists to derive.

**Why it needs a stored flag.** "Atomic-usable" cannot be recovered from `min_monomial` (a single
stored node id): no node in a pure-sum class has the monomial `{classid}`, so the slot has
no way to encode the atom representative. And "becomes referenced as a child" flips on
`add_use` (when a parent node is built over the class), an add-time event, not a merge, so
merge-only maintenance of `min_monomial` cannot observe it either. We therefore store a third
field in the slot, `atomic: bool`, and the rule RHS is:

```
rhs(class) = if atomic(class) { {classid} }      // size-1 atom, atomic-usable
             else             { monomial_of(min_monomial(class)) }
```

`atomic` is set when the class gains a non-AC node and on every `add_use` (any child
reference grounds `{classid}`, matching the old `child_set` semantics), OR-combined on merge
(`survivor.atomic |= absorbed.atomic`), and rolls back with the slot via the existing token.
So the slot is `{ use_list, min_monomial, atomic }`; `atomic` rides the same `Tagged`/token
machinery, and the RHS read stays O(1).

One subtlety: at merge time the children of these candidate nodes are mid-cascade, so
their canonical multisets can be momentarily stale. We therefore treat the stored slot as
a *candidate hint*: completion confirms it on read, where it re-`find`s the children and
canonicalizes anyway (it does this for every rule LHS regardless). This keeps the merge
path O(1) and places the only exactness requirement at the read site, which already pays
for canonicalization.

**Scope: one AC symbol now; multiple via a pool later.** A single `min_monomial` slot assumes one
AC op per e-graph, because the minimum monomial is per-(class, *op*): a class may hold both
a `+`-monomial and a `*`-monomial (assert `a+b = a*b`), and a `+`-rule's normal form must be
a `+`-monomial. This is no harder *algorithmically*: Kapur's multi-symbol algorithm is just
the single-symbol loop run independently per op, sharing only constants, and the e-graph's
union-find already dissolves his one cross-symbol case (a constant with two normal forms is
simply one e-class holding a `+`-node and a `*`-node, both with the same `find` as their RHS;
no fresh constant needed). The only thing single-op gives up is *storage generality*: one
slot holds one op's minimum. The vectorized form keeps `min_monomial` as an offset into a flat
`pool` of `nb_ac_op`-wide rows (one structure, backtracked whole; merge does an element-wise
min of two rows), recovering per-(class, op) minima without a per-class heap allocation. It
slots in behind the same `min_mono(op, class)` accessor, so callers do not change. The engine
uses the single-op slot (one AC symbol per e-graph); the pool is the upgrade for a
multi-AC-symbol e-graph.

**Reusable buffers, destination-passing, like the rest of `rebuild`.** `rebuild` already
threads scratch `Vec`s (`g_buf`, `mset_buf`, `collisions`, `touched`) by `&mut` into
`recanonize_node` rather than allocating per call. Completion follows the same rule: the
multiset primitives have destination-passing forms (`multiset_subtract_into`,
`_union_into`, `_lcm_into`, `normalize_ms_into`) that `clear()` and refill caller-owned
buffers, and the working multisets, the child-expansion buffer for materialize, and the
partner-id scratch are fields on the e-graph, cleared and reused. No function on the hot
path returns an owned `Vec`; a small fixed set of ping-pong buffers avoids read/write
aliasing. So a completion round allocates nothing that grows with the work.

**Worklist, not nested rounds.** The batch "loop the whole round to a fixpoint" becomes a
completion worklist interleaved with the congruence worklist `rebuild` already drains: a
node enters it when materialized or when its class changes, and draining one node runs its
two chores (§5d) for that node only, pushing the resulting new nodes and merges back. The
fixpoint is the single shared worklist emptying, not an outer round counter. Fairness
(no pair starved) is automatic, as before. The earlier batch round and its frozen
`by_contains` snapshot were a correctness-equivalent but allocating stand-in for this;
the incremental form is the intended one.

## 9b. Design alternatives (recorded so we do not re-derive them)

Two **orthogonal** axes came up while designing the `min_monomial` storage. They are
independent: pick one option from each. This subsection records all of them, with why,
so the choice is not re-litigated later.

### Axis 1: how the per-(class, op) minimum monomial is stored

The rule RHS is a class's `≫_f`-least monomial, read O(1)-often by completion. The
minimum is per *(class, op)* because a class can hold monomials of several AC symbols
(`a+b = a*b`).

| Option | Storage | Reads | Multi-op? | Verdict |
|---|---|---|---|---|
| **1. Single-op slot** | one extra `DenseId` widened into the e-class `SparseSet` value (`{use_list, min_monomial}`) | O(1) | no (one slot holds one op's min) | **Ship now.** Covers every test and all of §0/§5d. |
| **2. Multi-op, use-list walk** | none (recompute) | O(class size) per read | yes, for free (filter the walk by op) | Rejected. Correct, zero storage, but turns each RHS/normalize read into a class scan, reintroducing the per-query cost §9a exists to remove. |
| **3. Multi-op, pool** | `min_monomial` is an offset into a flat `pool` of `nb_ac_op`-wide rows; merge does an element-wise min of two rows | O(1) | yes | **Later.** The vectorization of option 1; one structure, backtracked whole, no per-class heap alloc. Slots behind the same `min_mono(op, class)` accessor, so callers do not change. Add when a multi-AC-symbol e-graph is actually needed. |

Multi-op is **not** algorithmically harder than single-op (Kapur's multi-symbol
algorithm is the single-symbol loop run independently per op, sharing only constants; the
union-find dissolves his one cross-symbol "shared constant with two normal forms" case,
that being just one e-class holding a `+`-node and a `*`-node with the same `find`). So the
axis is purely *storage*: 1 and 3 differ only in whether the slot holds one op's min or a
row of per-op minima; 2 trades all storage for a scan. Distributivity (`*` over `+`) is a
user rewrite rule (Kapur §6, Gröbner), **not** AC-CC, and is out of scope for all three.

### Axis 2: how minimal the stored RHS is guaranteed to be

`monomial_cmp` depends on `find()` of a node's children, which are mid-flight during a
merge cascade, so an O(1)-on-merge `min_monomial` can be momentarily **non-minimal**. What that
does, precisely (a rule is `+M → R` with `R = min_monomial`):

- A non-minimal `R` is **not** a soundness, termination, or blowup risk. Termination rests
  on the **LHS** antichain (collapse keeps no LHS ⊆ another), which does not involve `R`;
  and a non-minimal `R` is still a monomial over **existing** constants, so it cannot grow
  the constant set (the divergence mode is *class-as-atom*, injecting a fresh constant, which
  is a different thing). A non-minimal basis is *larger than ideal* (more
  rules, longer reducts, more inert collapsed nodes), but it **converges**.
- The one genuine hazard is **mis-orientation**: if the stored `R` is *bigger* than `M`
  (`M ≺ R`), the rule points the growing way and normalization loops. This is prevented
  by a **mandatory O(1) read-time orientation guard**: emit `+M → R` only if `M ≫ R`
  (else `M` is itself the smaller one: it is the normal form, not a rule). The guard runs
  at the read site, where finds are settled, so it is exact regardless of slot staleness.

| Option | Guarantee | Cost | Verdict |
|---|---|---|---|
| **(a) Best-effort + orientation guard** | RHS may be non-minimal, but every rule is correctly oriented (`M ≫ R`) | O(1) merge update; O(1) guard per read | **Ship now.** Termination-safe; at worst a slightly larger basis. |
| **(b) Exact minimum** | RHS is always the true class minimum (fully reduced basis) | refresh `min_monomial` at **recanonicalization** too, not just merge: merging a class changes the canonical multiset of nodes that had it as a *child* (reached via use-list), one of which may become its own class's new min. | Unnecessary under the degree-first order: a child merge preserves a monomial's degree, so it cannot create a new degree-minimum, and (a) already holds the exact degree-minimum. |

The orientation guard in (a) is **mandatory, not optional**: it is what makes the merge-time
hint safe. The basis is reduced in the LHS (collapse keeps the antichain) and oriented in the
RHS, which is what termination and the decision procedure need; the companion
(`ac-completion-spec.md` §1, §3) records the runtime checks that confirm `min_monomial` is the true
minimum at the point of use.

## 10. Why the algorithm is complete

This section gives the completeness argument for the algorithm of §6–9. It adapts Kapur's
and follows standard rewriting metatheory. The argument is on paper, not yet discharged in a
proof assistant: it has not been mechanically checked that our specific construction (e-class
ids as constants, union-find as the constant-rule layer, `by_contains`-driven pair finding)
satisfies every hypothesis those theorems need, so treat §10 and the §12 completeness bullet
as a rigorous paper argument, not a machine-checked guarantee (the verification plan is in
[Future Work](A3-future-work.md)). Soundness is separate, argued in §12, and does not depend
on this argument.

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
- Local confluence (established by the loop, via Kapur Lemma 5). Local
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
- Termination (via Dickson's Lemma, Kapur Thm 6). There are two
  terminations, with different measures. Normalization (`nf_R` reducing a query to a
  normal form) terminates because every step `+M → +((M−A)⊎{a})` replaces a
  sub-multiset `A` (with `|A| ≥ 1`) by a single class `a`, strictly down in the
  Dickson order (sub-multiset is componentwise `≤`); a total admissible monomial
  order refines that partial order so every rule is orientable. The completion loop
  terminates by a finiteness argument: the loop keeps `R` inter-reduced, so surviving
  rule left-sides are pairwise `⊆`-incomparable (an antichain in `ℕ^{|C|}`), and
  Dickson's Lemma makes every such antichain finite. So only finitely many rules can
  persist, and each merge strictly coarsens the finite class partition. **This step is
  essential and conditional on collapse actually being performed** (§6b): "the loop
  keeps `R` inter-reduced" is not automatic; it is the Collapse/subsumption operation
  doing it. An implementation that skips collapse has no antichain, and Dickson bounds
  nothing observable; it diverges in practice (§6b gives the trace). Termination holds
  *for the algorithm with collapse*, not for (A)+(B) alone.

  One subtlety the measure must respect: new left-sides are **not** bounded by
  "sub-multisets of lcms of input left-sides." A reduct `(AB−A)⊎{a}` adds the rule's
  right-hand class `a`, which need not lie in `AB`, so reducts can be larger than any input
  lcm. There is no clean size bound; termination rests on Dickson antichain-finiteness over
  the finite class set, not on a multiset-size measure. This is the part most likely to need
  care in a formalization.

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
