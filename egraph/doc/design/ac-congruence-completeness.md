# AC Congruence Completeness

This chapter is a self-contained account of the engine's opt-in attempt to close
equalities over associative-commutative operators. It develops three ideas in order: (1) why
recanonicalizing AC nodes as flattened multisets, on its own, misses real equalities
(Part I); (2) that the cure is to read the e-graph as a set of rewrite rules and complete
that rule set, using a per-class `min_monomial` candidate as the rule right-hand side
(Part II, §5c–§9); and (3) that the paper construction keeps a *reduced canonical basis*, by
collapsing rules whose left side another rule already covers, is what makes the procedure
correct and terminating (§6b, §10). The implementation has focused tests and diagnostics
for the corresponding mechanisms, but the correspondence and its composition into
termination/completeness remain a paper argument rather than a verified theorem.

This is the single design reference for the AC completeness story. Part I derives the
problem from first principles (§0 is the short framing); Part II gives the algorithm and the
argument for why it works. For where we stand and what remains, see
[Future Work](A3-future-work.md); for the engine-specific invariants, the matcher details,
and the implementation correspondence with Kapur, see the companion
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
infinitely many. The abstract completion construction maintains a finite set of
find-and-replace rules that can regenerate those equalities on demand, keeping that set
reduced (no rule's left side contained in another's). Finite does not mean small:
ground AC completion has severe worst cases, and the production pass has an explicit
growth-budget exit. At a converged canonical system, deciding `g₁ = g₂` is "rewrite
both with the rules until they stop; equal iff they land in the same place."

Two forces fight each other while saturation runs and new facts keep arriving:

- **Collision (superposition)** *creates* cross-rule consequences (like `p+c = q`) that
  two overlapping facts force. Without it, the abstract plain-AC construction misses
  the overlap cases traced in §4.
- **Reduction (collapse / inter-reduction)** *deletes* rules that a smaller rule already
  subsumes. For instance, drop `a+b+c = q` once `a+b = p` and `p+c = q` are known,
  because `a+b+c` just rewrites to `p+c` first. This is what keeps the set finite.

Collision without reduction explodes the rule set: collisions breed redundant rules that
breed more (the divergence we actually hit, §6b). Reduction without collision never
derives the cross-fact equalities (incompleteness, §4). **AC congruence closure is the
discipline of running both, in the right order, to a fixpoint, so the surviving rules
are the intended reduced canonical basis**. Whether the production representation
satisfies every hypothesis of that statement is the open proof obligation in §10. The
rest of this chapter maps the construction into an e-graph, where "a rule" is just an
AC node and "delete a rule" cannot mean delete a node.

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
- **antichain**: a rule set in which no left side is a sub-multiset of another.
  Dickson's Lemma (§10) bounds every such antichain over a fixed finite signature.
- **reduced canonical basis**: the stronger abstract target: an inter-reduced,
  terminating, confluent system. An antichain alone does not establish those properties.

## 0a-bis. Naming convention: representation vs. completion vs. theory

The code uses "AC" in three unrelated senses; conflating them in identifiers caused real
confusion, so the names are split along three axes and "AC" is reserved for exactly one of
them. When reading or extending the code, classify a name by which axis it belongs to.

1. **Representation (`MSet` / `Set`).** How a variadic node stores its children. `MSet` =
   multiset, children `(G, mult)` with counts in the configured unsigned `Cfg::M`
   (`+`, `*`, and nilpotent ops like `xor`, which need run lengths before the mod-n
   clamp); `Set` = set, children bare `G`
   with counts bounded to {0,1} (`and`, `or`, idempotent only). This is the axis the storage
   and routing layers care about, so the *representation* names appear there: `OpKind::MSet` /
   `OpKind::Set`, `ENodeKind::MSet` / `Set`, `NodeRef::MSet` / `Set`, `nodes.mset` / `nodes.set`,
   `MSetCanon` / `SetCanon`, `register_mset` / `register_set`, `is_mset`, `mset_ops`,
   `mset_child_*`, `mset_buf`. A name carrying `mset`/`set` is about *layout*, never about the
   algorithm. (Why not keep "AC"/"ACI"? "AC" named the multiset representation, but it also
   names the algorithm and the theory below; and "ACI" baked the idempotent *clamp* into the
   representation name. The clamp is a separate axis: idempotent is the one `Set` case
   (dedup IS its clamp), while nilpotent lives in `MSet` (dedup would destroy the run-lengths
   the mod-n clamp needs: see `ac-algebraic-properties.md`, "nilpotent must be MSet"). The
   representation axis is `{MSet,
   Set}`; the clamp is separate.
   See `doc/design/ac-algebraic-properties.md`, "three independent axes".)

2. **Completion procedure (`cc`).** The congruence-closure *completion* this chapter adds
   (superposition + inter-reduction). It is not tied to one representation: it runs over
   BOTH MSet and Set, so its names use
   `cc`, never `ac`: `cc` / `set_cc` (the enable flag),
   `cc.rs` (the module), `cc_round`, `CcSnapshot`, `completion_node_ids`, `fold_min_monomial`,
   `min_monomial` (the per-class candidate the round reads as a rule RHS),
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

Completion transforms that rule set toward a *reduced canonical basis* (§0). Three
properties define the abstract target.

- **Minimal**: no redundant rule. A rule whose LHS rewrites under the others is dropped
  (collapse, §6b).
- **Inter-reduced / disjoint** (an antichain): no rule's left side is contained in
  another's. Collapse enforces this on each new rule; the surviving left sides are pairwise
  `⊆`-incomparable (§0, §5d, §6b), and Dickson's Lemma keeps that set finite (§10).
- **Confluent**: every two-way rewrite of one term joins. In the abstract construction,
  superposition (§6 (B)) closes the divergences that block this; if the §10 obligations
  hold, the resulting basis is convergent and `nf_R` decides the stated theory.

Plain rebuild has only the constant layer and atom-level recanonicalization, so
its rule set need not be confluent (§3, §4). The implemented opt-in completion
pass adds the superposition and collapse steps of §6 and drives toward that
target. `CompletionOutcome::Converged` reports only that a full implementation
round made no change; it is not a certificate that the abstract reduced-basis
conditions hold. Default-off, goal-directed, and budget-aborted returns retain
the plain-completeness boundary.

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
sub-sum node is what the congruence rule fires on. A binary encoding with explicit
associativity/commutativity rewrites can expose intermediate variants as nodes,
allowing ordinary congruence to act on those materialized subterms, at potentially
severe saturation cost.

Now flatten into a canonical multiset node:

```
   +{a, b, c}     (one node; no inner structure at all)
```

The children form a **multiset**, not a set: multiplicities matter in general. `a + a + b`
flattens to the multiset `{a:2, b:1}`, distinct from `a + b = {a:1, b:1}`, and a rule's
left side carries those counts. The worked examples below (§4, §5d, §6b) all happen to use
multiplicity-1 children, so they read like sets; the data structure is a multiset
throughout.

This is the optimization we want: it canonicalizes the many binary bracketings
and permutations of an n-ary sum to a single node. But the sub-sum node `(b+c)`
no longer exists, and neither
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

The equality is entailed by AC, but plain recanonicalization does not derive it.
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

This is how the intended maximum-partition e-matching relation and the
congruence boundary differ. Focused tests support matcher soundness, while
completeness for that relation remains open ([Ch 9](09-pattern-matching.md)).
Rest bindings can represent residual multisets transiently; they do not keep
sub-sums as nodes that can trigger later congruence merges.

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
choice. Closing this particular gap does not require extending the matcher to bind
scalar variables to virtual sub-sums. That would be a term-valued classical AC
matching extension against a ground subject, not AC unification. Eagerly
materializing every sub-multiset is one possible integration strategy, but it
has up to `2^d` candidates for `d` distinct summands (more generally
`product_i (m_i + 1)` for multiplicities `m_i`). Instead, completion lets rebuild
materialize the finite set of substituted sub-sum nodes that known equalities
imply, after which ordinary e-matching reaches them.

Part II closes case (b) as well, not by enlarging the matcher but by enlarging the
node set with the demand-driven substitutions. The one residual case neither layer
covers is a sub-sum that is never equal to any named class and never occurs as any
node's child, referenced only by a pattern. Matching that would require representing
a sub-sum no equation justifies as a scalar value; it is the open term-valued
AC-matching extension that Kapur and Conchon (§8) both leave aside, and we do not
claim it (§11). General AC unification is broader still.

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
decides its equational theory. This is the abstract conditional argument; §10 lists
the obligations still needed to transfer it to production.

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

**How the abstract machine builds this live.** The basis is not computed once from a fixed
input. Saturation feeds facts in one at a time (each rewrite firing produces a new
equality), and the construction updates the basis incrementally as they arrive, since every
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

**This is one source of blowup.** Skip Chore A, and when FACT 2 arrives the
set keeps `a+b+c→q` *and* derives `p+c→q`, so a rule (`a+b+c`) containing another rule
(`a+b`) stays live. Next round Chore B builds collision multisets off it, breeding more
rules that *also* contain `a+b`, which breed more, generating the infinite pile instead of
the two-rule machine on known reproducers. So the construction orders the work:
**on each new rule, do Chore A first (chew down
everything it sits inside, and chew it down by what exists), and only then Chore B.** Keep
the surviving rules chewed-down so their left sides form an antichain. Dickson's
Lemma establishes finiteness for the abstract fixed-signature construction; it
does not give a small bound or make the implementation cheap.

The rest of Part II is this mechanism stated precisely against the e-graph: §6 the two
operations, §6b why Chore A (collapse) is required by the abstract termination argument and
how "retire a rule" is realized without deleting a node, §7–9 the implementation,
and §10 the conditional termination/completeness argument and open obligations.

## 6. The fix, derived directly from the root cause

The root cause says to re-materialize the erased intermediate terms, but only the
ones that can matter. Not all sub-multisets (up to `2^d` for `d` distinct
summands, or `product_i (m_i + 1)` with multiplicities), only those tied to the left-hand side of a known AC
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

(A) and (B) without collapse are not the completion algorithm whose termination
argument is cited here. The no-collapse form diverges on committed reproducers by
minting reducible rules that become new superposition sources. Historical growth
ratios and out-of-memory points are machine- and revision-specific diagnostics, not
current complexity evidence. Collapse is therefore a required algorithmic operation,
not an optional optimization.

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

The intended active set is then a **Dickson antichain**: a set of multisets over the finite
class pool `C`, pairwise `⊆`-incomparable. Dickson's Lemma makes every such antichain
finite, but supplies no practically small cardinality bound. The plain pair scan is
quadratic in `|active|`; semantic-property generators, normalization,
materialization, and repeated rounds add further work. This is not a polynomial
whole-algorithm claim.

In the paper correspondence, collapsing a rule loses no equality. Before `+M` is collapsed, its content is *already
preserved twice*: the merge `reduct(+M) = d` has been performed (so `+M`'s class is still
`d`), and the reduct itself is a live, non-collapsed node carrying the same class. So
every consequence `+M` could contribute as a superposition source is also derivable from
its reduct, which *is* active. Collapse therefore prunes only *redundant* sources (the
composite superpositions of Kapur–Musser–Narendran), never a prime one, which is exactly
why the abstract completeness argument survives. Focused tests exercise this
implementation ordering; no machine-checked refinement theorem currently proves it
for all states. The collapsed node remains a legal *child* of other live nodes,
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
injects the rule's right-hand class `a`, which need not lie in `AB` (§10). So a reduct can be a **proper superset** of an existing rule's
left side (i.e. itself reducible), yet, materialized raw, it survives as a live node
and therefore as a superposition source for the next round. A pair scan can turn
`n` rules into quadratically many candidates, and retaining those candidates can
repeat that expansion in later rounds. Dickson's antichain argument no longer
applies to this no-collapse process.

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
   The abstract fix orients the critical pair as a rule between **two monomials** over the
   *existing* constants (`larger → smaller`, never `→ κ`), and substitutes a class by
   its degree-lex-minimal monomial, never by a class-as-atom. Production uses the
   maintained class-member candidate only when the read-time orientation guard
   makes a decreasing rule; exact minimality is the §9b proof gap. Then, in the
   abstract example, `+{b,c,d} → +{a,b,e} → +{c,e}` (via `+{a,b}→c`) joins the other
   reduct `+{c,e}`: the pair is trivial, nothing new is added, and the §4b system
   converges to three rules over `{a,b,c,d,e}` with no new constant ever introduced.

3. **Collapse is the finiteness mechanism in the abstract construction.** Bounded-size
   monomials could still accumulate in *number*; collapse (above) retires every left
   side that becomes reducible, so the surviving left sides are a Dickson antichain,
   hence finite for the fixed-signature model. Narendran–Rusinowitch (RTA 1991)
   proves existence of a finite canonical system for every ground AC theory. The
   claim that this implementation realizes the construction is the §10 obligation.

In the abstract construction, a rule's left side is the non-minimal side and the
class minimum is its normal form, so that minimum is not a superposition source.
The two essential choices are to orient critical pairs between monomials over
existing constants and to collapse reducible sources. Production approximates
the minimum as described above. Under the abstract invariants, the plain pair
scan is `O(|active|²)` per round over a finite
antichain; get the RHS wrong (substitute the class id as an atom) and known
reproducers grow without reaching the intended fixpoint.

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

whose left sides are `⊆`-incomparable and share no element, so this finite
abstract example has no remaining critical pair.

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
growth mechanism). The construction avoids both; this worked trace does not prove
that either defect independently diverges on every input.

The abstract correct run *decides* `{a,b,s} = {s,t}` by normalising (`{a,b,s} → {t,s}` via R2,
same as the other side, both over existing constants) and stores neither: collapse
plus normalization against the oriented rule set is the step that cannot be skipped.

### What this requires of the implementation

1. **Maintain an `active` set of irreducible AC nodes** per op (those with no
   containment partner), concretely the AC nodes carrying neither `FLAG_AC_COLLAPSED`
   nor `FLAG_SUBSUMED`. Superpose (B) only over `active`.
2. **On adding `+A → a`**, find its containment supersets via `by_contains`; for each
   active `+M` with `A ⊊ M`, reduce (A), merge, and **mark `+M` `FLAG_AC_COLLAPSED`** (the
   non-deletable form of "retire"; the node, its class, and its matchability persist).
3. **Normalize every reduct against *all* current rules** (including those minted this
   round) to a fixpoint before comparing (see the `normalize_ms` requirement in §9).
   If the two reducts land in one class, add nothing.
4. **Orient rules and avoid synthetic class-as-atom RHSs.** The abstract algorithm picks a total
   admissible monomial order `≫_f` (degree-lex: size, then lex from the **largest**
   class id downward: see "the tie-break direction is load-bearing" below) and uses
   the class minimum. Production instead reads a class-member candidate and emits a
   rule only when it is decreasing; proving that this weaker representation preserves
   the abstract termination/completeness argument is open (§9b). It never invents a
   fresh class id solely as a synthetic RHS summand.

Diagnostic traces can compare `|active|`, total AC nodes, generated critical pairs,
and the reported completion outcome. Such traces are reproducers, not evidence that
the active set generally plateaus near the input size.

### Flattening (`WF_flat`) and the matcher-crash gate

The engine requires **AC terms to be flattened** (`WF_flat`): an `f`-node never has an
`f`-class child. This is a canonicalization invariant, not a completion-specific one: the
materialization invariant of §1 needs every summand to be a real summand, and a nested
`+f(+f(…),…)` hides one. §6c states exactly what to flatten (the class summand-form), gives
the implementation argument that recanonicalization-time flattening is vacuous, and
explains why keying the flatten on the union-find representative is the wrong choice.

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
summand_form(class, f) = if atomic(class)               { {class} }   // a real atom: keep
                         else if min_monomial(class, f) { it }        // splice the maintained candidate
                         else                           { {class} }   // no f-monomial: keep opaque
```

Three cases, not two, and the second argument matters:

1. **Atomic** (referenced as a child anywhere, or holding a non-completion node): kept as
   one summand, even if the class *also* contains one or more `f`-sum nodes. The atom is
   the ≺-least representative, and splicing a sum member would rewrite uphill; completion's
   rules `M → {class}` reconcile spelled-out occurrences downward instead.
2. **Non-atomic with `f`-monomials**: the class's maintained `min_monomial` candidate for
   `f`'s pool column is re-canonicalized and spliced. Other members remain in the class and
   can contribute oriented completion rules. The candidate is a deterministic field of the
   implementation state, but §9b explains why production has not proved that it is always
   the globally least same-op member or that the resulting system has a unique normal form.
3. **Non-atomic with only other-op monomials** (a `*`-sum used inside a `+`-sum): the `f`
   column is empty, the class id is kept opaque: Kapur's purification, the class id playing
   the fresh-constant role shared between the two AC theories.

Both completion representations flatten this way at build (`MSet` and `Set`: an
MSet-only gate would silently leave ACI terms nested; regression `set_flatten_build.egg`).

`atomic` and `min_monomial` are merge-folded class properties (§9a), rather than properties
looked up through whichever node is the union-find representative. So flattening becomes:
**when canonicalizing an `f`-node, replace
each child `c` by `summand_form(c)`; if that is a multi-element monomial, splice it in
(recursively); if it is the single atom `{c}`, keep `c` as a summand.** This is a function
of the stored e-graph state, not a branch on representative node kind. The stronger
canonical-basis and history-independence claims remain among §9b and §10's proof
obligations.

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
grounds `c`-as-a-single-element. Its selected candidate is an actual same-class sum,
for example `min_monomial(c) = +{p, q}`. The e-class equality and associativity then justify
`+{…, c, …} = +{…, p, q, …}` in the paper model: spelling the child through that witnessed
sum is meaning-preserving. It is also *forced* by the implemented representation, not merely
allowed: keeping
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
`find`. On a live branch, existing nodes are immutable; completion "retirement" is a flag
(§6b), not physical deletion. A restore can truncate the post-mark arena suffix, so this is
not a claim that every allocated node survives rollback. The only effect of inlining is that
the new node never *holds* `c` as a child; since `c` was non-atomic, no other node held it as
a child either, so afterward `c` may simply be a live class that nothing uses as a summand,
fully intact, not gone. Inlining is a choice the parent makes about how to spell its own
children, not an operation on `c`.

**Where flattening runs: build only, with a stated sufficiency argument.** A child is spliced exactly
when it is non-atomic, i.e. a pure `+`-sum that contains no non-AC node and is referenced
by no node (§9a). Flattening therefore needs to run only at the one place a non-atomic
class can appear as a candidate child: `add`. Before the AC arm sorts and coalesces,
`flatten_ac_children` replaces each child by its `summand_form` (`{c}` if atomic, else
`min_monomial(c)`) and splices the non-atomic ones, to a fixpoint.

The implementation argument says recanonicalization does **not** need a
flattening pass. The following lemma and proof are on paper, not machine checked.

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
form", because in an e-graph a child is a class, not a term. Under that change, the
"re-apply after every rewrite" obligation follows from the stated invariant: by the lemma above, the
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

Representative choice is intended not to change the unbounded abstract equality
relation, because class payloads are merge-folded. It does change dense ids,
monomial order, basis shape, and operational work; budgeted or otherwise incomplete
runs may therefore expose different intermediate outcomes. Finite differential
tests compare the survivor policies, but there is no end-to-end equivalence theorem.
What matters next is a kind of rule the union-find never fires.

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
For a converged pass, the paper argument in §10 says the two layers provide full
ground AC congruence closure over the stated model. No linear or polynomial
whole-procedure bound follows: pair generation, normalization, repeated rounds,
and basis growth can dominate.

## 8. Correspondence with Kapur's ground AC-CC algorithm

The data structures have the following intended mapping to Kapur's ground AC-CC
framework (FSCD 2021),
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

Under this correspondence, rebuild realizes the roles in Kapur's General
Congruence Closure (Algorithm 3): step 1 (constant rules) is
the union-find, step 2 (normalize `Sf`) is `recanonize_node`, step 3 (critical pairs) is
superposition (B), and step 4 is the two halves of inter-reduction, substituting the reduct
(A) **and** retiring the now-reducible source rule (Collapse, §6b, realized by marking it
`FLAG_AC_COLLAPSED`). Step 4 being *two* things is the essential subtlety: the collapse
half is what makes the rule set a Dickson antichain and is what the abstract
termination argument rests on (§6b, §10). This table is not itself a refinement
proof; `ac-completion-spec.md` records the partial rows and finite diagnostics.

The table above maps the **plain-AC** framework. The semantic-property
extensions of the LMCS 2023 journal version add pair generators beyond step 3: the per-rule
AXIOM critical pairs (§4: idempotent, nilpotent order n), the cancelative closure (§5.1–5.3:
rule cancel-close, cancelative disjoint superposition, the per-constant closure), and
inverse-pair cancellation. Their code↔paper correspondence lives in the normative table of
`ac-completion-spec.md` §3.1.

## 9. Implementation

```rust
// In rebuild(), per AC op f, to fixpoint, alongside recanonize_node.
// Each ACTIVE AC e-node can yield a ground rule f(M) -> f(rhs(class(M))).
// Production reads a class-member candidate and keeps the rule only when the
// degree-lex guard proves M > rhs. Exact global minimality is not assumed here.
// EXCEPTION: a class that IS the op's identity has the EMPTY monomial as RHS
// (Kapur's f({}) = e) — the atom form {e} would leak unit summands into reducts that
// normalization (no f(x,e)=x law) can never remove. See ac-completion-spec.md §1.
// TARGET INVARIANT: `active` holds only irreducible rules (no LHS strictly
// contains another LHS). The production correspondence is an open obligation.

// (B) Superposition critical pairs (Kapur Def. 4), over ACTIVE rules only.
// Overlap candidates share >= 1 child class: the union of by_contains.
for x in M.distinct() {
    for partner in active.by_contains[x] ∩ active.by_op[f] {
        let (a1, ra) = (partner.multiset(), partner.rhs_monomial());  // f(A1) -> f(ra)
        let rm = M.rhs_monomial();                             // f(M)  -> f(rm)
        if multiset_disjoint(&M, &a1) { continue; }            // disjoint => trivial
        let ab = multiset_lcm(&M, &a1);                        // (M ⊎ A1) − (M ∩ A1)
        let c1 = normalize_ms(f, multiset_union(&msub(&ab, &M),  &rm)); // (AB−M) ⊎ rm
        let c2 = normalize_ms(f, multiset_union(&msub(&ab, &a1), &ra)); // (AB−A1)⊎ ra
        if find(c1) != find(c2) { merge(c1, c2); }             // non-trivial, close it
    }
}

// (A)+Collapse: the destructive step that keeps `active` an antichain (§6b).
// When rule f(A1) -> f(ra) is added, retire every active rule it makes reducible.
for parent in active.by_contains-supersets(A1) {              // f(M) -> d with A1 ⊆ M
    if proper_subset(&A1, &parent.multiset()) {
        let red = normalize_ms(f, substitute(parent.multiset(), A1 => ra));  // (A)
        merge(red, parent.class());
        set_flag(parent, FLAG_AC_COLLAPSED);  // <-- COLLAPSE: retire +M (not delete; §6b).
        //                                       completion's active scan skips collapsed,
        //                                       so +M is no longer a partner; it stays
        //                                       matchable, a child, and in class d, for
        //                                       rollback. (FLAG_AC_COLLAPSED, not subsume.)
    }
}

// normalize_ms reduces a monomial to a fixpoint under the current round's
// snapshotted, decreasing rules. Rules materialized while applying the batch enter
// the next round; the final unchanged full round is the operational stopping test.
```

**Round structure.** Production uses batch rounds. Each round first drains ordinary
congruence, snapshots active rules into owned `rules` and `targets` vectors, generates
an owned `crit` vector, applies inter-reduction and critical-pair closures, then repeats.
Round 0 and a final confirmation round inspect all eligible pairs; intermediate rounds
restrict ordinary superposition to pairs with at least one touched endpoint. A full
unchanged confirmation round is the condition for
`CompletionOutcome::Converged`. This incremental-pair optimization has regressions and
a prose coverage argument; it is not yet a proved fairness theorem.

It is tempting to think the union-find lets us drop Kapur's monomial ordering entirely,
since it is already our canonical layer. It does not, and §6b is why. The union-find
canonicalizes *classes* (the right-hand sides); it says nothing about *which left-hand
multiset survives* when two rules are comparable, and that choice is exactly what collapse
needs and what keeps `active` a finite antichain. Two distinct roles:

- **Projection of each rule `+M = d`**: union-find supplies class equality, while
  `class_rhs_into` chooses an existing class representation and `monomial_cmp`
  emits the node as a rule only when `M` is strictly larger.
- **Orientation *between* two rules** (when `+A` and `+M` are containment-comparable,
  which collapses): this needs a total admissible monomial order `≫_f`, concretely
  **degree-lexicographic** (compare multiset size; break ties comparing the
  `(class id, count)` entries from the **largest class id downward**), which satisfies
  Kapur's subterm + compatibility properties. The larger
  LHS is the one retired (marked `FLAG_AC_COLLAPSED`). Without the required
  orientation/reduction properties the Dickson argument does not apply; known
  reproducers exhibit explosive growth.

### The tie-break direction is load-bearing

The tie-break must compare monomials **from the largest class id downward**, Kapur's
degree-lex: at equal size, the side owning the largest constant of the symmetric
difference is greater. Comparing the *ascending* sequences looks equally natural but
is **not** compatible with multiset sum (`{b:2} ≫ {a,c}` yet `{a,b:2} ≺ {a:2,c}`):
under an incompatible order, a rule can *raise* the host monomial it rewrites and
exhaust the defensive guard. Guard exhaustion panics in every build rather than
returning a partial "normal form"; debug builds additionally assert strict decrease
after every step. In either case the termination/uniqueness arguments (Kapur
Thm 3.4 / 3.6) do not apply to a mis-oriented table. `monomial_cmp`
implements the descending comparison (see `ac-completion-spec.md` §3), with
randomized admissibility tests.

So we still drop the *machinery* Kapur needs for a unique reduced canonical
presentation across AC symbols (we do not need canonical signatures to derive
equalities), but we cannot drop the monomial order itself: it is what orients collapse.

## 9a. Data structures and the batch-round architecture

Production implements the batch model shown in §9. `rebuild` alternates ordinary
worklist congruence with `cc_round`; each completion round takes an owned projection of
the current rule state and applies the buffered work before the next round. It is not a
single completion worklist and it is not allocation-free.

**The nodes are the source of truth; a round builds an owned projection.** Active rules
are MSet/Set nodes carrying neither `FLAG_AC_COLLAPSED` nor `FLAG_SUBSUMED`.
`cc_round` scans `completion_node_ids()` and constructs:

- `rules`, with owned canonical LHS and RHS monomials;
- `targets`, with every active completion node's owned monomial;
- `crit`, with owned reduct pairs;
- a sorted delta-node vector on incremental rounds; and
- per-op normalization tables and indices for critical-pair closure.

The implementation reuses several local scratch buffers inside a round, but those
owned vectors can allocate and grow with the work. Plain superposition finds candidate
partners through class use-lists and binary-searches the round's `rules` projection.
Cancelative disjoint pairs use an explicit same-op all-pairs loop. There is no
persistent parallel rule database, but there is a transient per-round rule table.

**Per-class candidate monomials live in a semi-persistent per-op pool.** `EClasses`
stores `ClassData` in a `SparseSet`; `ClassData::min_row` points into a flat pool with
one optional node id per completion op, and the class also stores `atomic`. On a merge,
`fold_min_monomial` walks every populated completion column, canonicalizes the two
candidate nodes into reusable buffers, and retains the `monomial_cmp`-smaller
candidate. Its cost is `O(number of completion columns + monomial elements compared)`,
not `O(1)`.

The pool is part of `EClassesToken`, so mark/restore rolls its logical contents back
without a separate field in `EGraphToken`. That does not make rollback free: the
container's normal diff replay, capture-flag maintenance, and any transient-index
reconstruction still apply.

**The rule RHS is not always the stored `min_monomial`: an `atomic` flag rounds out the
slot.** The implementation selects a usable representative for the class. The
size-1 monomial `{classid}` is smaller than any multi-element sum, but it is a legal
monomial only if the class is **atomic-usable**; otherwise the selected per-op pool
candidate is used. Global leastness is the diagnostic/open obligation described below.

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
atomic-usable, and the implementation uses its maintained actual `+`-monomial candidate,
`min_monomial`.
Writing `{c}` for such a class would name an element no node denotes, which is the
class-as-atom divergence of §6b: it injects a fresh constant every round.

Concretely. `+{a,b}` in class `c`: if `neg(c)` exists (so `c` is a child of `neg`), then
`c` is atomic-usable and the rule is `+{a,b} → {c}`, which lets `c` substitute into other
sums. If instead `c` arose only as a critical-pair reduct and nothing references it, it is
not atomic-usable, and its rule RHS stays the maintained `min_monomial` candidate.
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
reference grounds `{classid}`), OR-combined on merge
(`survivor.atomic |= absorbed.atomic`), and rolls back with the slot via the existing token.
So the class data contains `{ use_list, min_row, atomic, ... }`; `atomic` and the pool
ride the class-layer token machinery. Selecting the slot is O(1), while reconstructing
its current monomial is linear in that node's distinct child entries.

One subtlety: at merge time the children of these candidate nodes are mid-cascade, so
their canonical multisets can be momentarily stale. The stored slot is therefore a
*candidate hint*. Completion re-`find`s and canonicalizes that selected node on read,
then emits a rule only if the read-time orientation guard sees `LHS ≫ RHS`. This
confirms the selected candidate's current monomial and its orientation; it does **not**
compare it with every same-op member of the class or prove that it is the global
minimum. `cc_min_used_nonminimal` performs that finite diagnostic when basis checks are
enabled.

**Why the slot is a per-op pool, not a single slot.** The candidate monomial is
per-(class, *op*): a class may hold both
a `+`-monomial and a `*`-monomial (assert `a+b = a*b`), and a `+`-rule's normal form must be
a `+`-monomial. A single `min_monomial` slot per class would therefore support only one
AC op per e-graph, a real but strictly narrower design: multi-symbol completion is no
harder *algorithmically* (Kapur's multi-symbol algorithm is just
the single-symbol loop run independently per op, sharing only constants, and the e-graph's
union-find already dissolves his one cross-symbol case: a constant with two normal forms is
simply one e-class holding a `+`-node and a `*`-node, both with the same `find` as their RHS;
no fresh constant needed), so the only thing a single slot gives up is *storage
generality*. The shipped design is the vectorized form: `min_monomial` is an offset into a
flat `pool` of `nb_completion`-wide rows (one structure, backtracked whole; merge does an
element-wise candidate selection from two rows), retaining one per-(class, op) candidate
without a per-class heap allocation, behind one `min_mono(op, class)` accessor (see
`ac-algebraic-properties.md`, the storage chapter).

**Scratch reuse is local, not a zero-allocation contract.** Destination-passing
multiset operations reuse `ab_buf`, `sub_buf`, normalization ping-pong buffers, and the
materialization buffer within one call. The `rules`, `targets`, `crit`, delta, and
per-op index vectors are nevertheless rebuilt as owned values each round. Any
allocation-performance claim must come from the maintained allocation/Criterion
benchmarks at the revision under test.

**Nested rounds with a delta optimization.** Round 0 and a would-be-convergence
confirmation round inspect the full eligible pair set. Intermediate rounds restrict
ordinary superposition to pairs with at least one endpoint in the touched-node delta;
inter-reduction and reducibility checks remain full scans. Convergence is reported only
after an unchanged full round. Focused regressions exercise missed-delta cases, but the
fairness/refinement argument for this optimization is not machine-checked.

## 9b. Design alternatives (recorded so we do not re-derive them)

Two **orthogonal** axes came up while designing the `min_monomial` storage. They are
independent: pick one option from each. This subsection records all of them, with why,
so the choice is not re-litigated later.

### Axis 1: how the per-(class, op) candidate monomial is stored

The abstract rule RHS is a class's `≫_f`-least monomial. Production reads one maintained
candidate from a constant-time slot and checks orientation; exact leastness is Axis 2.
The candidate is per *(class, op)* because a class can hold monomials of several AC
symbols (`a+b = a*b`).

| Option | Storage | Reads | Multi-op? | Verdict |
|---|---|---|---|---|
| **1. Single-op slot** | one extra `DenseId` widened into the e-class `SparseSet` value (`{use_list, min_monomial}`) | O(1) slot read | no (one slot holds one op's min) | Historical alternative; not shipped. |
| **2. Multi-op, use-list walk** | none (recompute) | O(class size) per read | yes, for free (filter the walk by op) | Rejected. Correct, zero storage, but turns each RHS/normalize read into a class scan, reintroducing the per-query cost §9a exists to remove. |
| **3. Multi-op, pool** | `min_row` indexes a flat pool of `nb_completion`-wide rows; merge folds columns element-wise | O(1) slot read; merge is O(columns + compared monomial elements) | yes | **Shipped.** Covers MSet and Set completion ops without a per-class heap allocation. |

Multi-op is **not** algorithmically harder than single-op (Kapur's multi-symbol
algorithm is the single-symbol loop run independently per op, sharing only constants; the
union-find dissolves his one cross-symbol "shared constant with two normal forms" case,
that being just one e-class holding a `+`-node and a `*`-node with the same `find`). So the
axis is purely *storage*: 1 and 3 differ only in whether the slot holds one op's candidate
or a row of per-op candidates; 2 trades all storage for a scan. Distributivity (`*` over `+`) is a
user rewrite rule (Kapur §6, Gröbner), **not** AC-CC, and is out of scope for all three.

### Axis 2: how minimal the stored RHS is guaranteed to be

`monomial_cmp` depends on `find()` of a node's children, which are mid-flight during a
merge cascade, so an O(1)-on-merge `min_monomial` can be momentarily **non-minimal**. What that
does, precisely (a rule is `+M → R` with `R = min_monomial`):

- A selected `R` is a monomial of the same e-class, so using it as a reduct has the
  intended equality justification. This supports the local soundness argument.
  However, the effect of a globally non-minimal RHS on the implementation-level
  termination and completeness correspondence has not been proved. The fact that it
  uses existing class ids rules out the specific fresh-class-as-atom mechanism; it
  does not establish convergence by itself.
- The one genuine hazard is **mis-orientation**: if the stored `R` is *bigger* than `M`
  (`M ≺ R`), the rule points the growing way and normalization loops. This is prevented
  by a **mandatory O(1) read-time orientation guard**: emit `+M → R` only if `M ≫ R`
  (else `M` is itself the smaller one: it is the normal form, not a rule). The guard runs
  at the read site, where finds are settled, so it is exact regardless of slot staleness.

| Option | Guarantee | Cost | Verdict |
|---|---|---|---|
| **(a) Best-effort + orientation guard** | Selected RHS may be non-minimal; each emitted rule is decreasing (`M ≫ R`) | merge folds all completion columns; one comparison guard per read | **Shipped.** Prevents a growing normalization step; universal termination/completeness remains an open refinement obligation. |
| **(b) Exact minimum** | RHS is the true current same-op class minimum | rescan or incrementally maintain all affected class members after recanonicalization | Not shipped. Basis diagnostics compute this independently on finite test states. |

The orientation guard in (a) is mandatory: without it normalization could apply a
growing rule. Collapse and duplicate-LHS filtering target an LHS antichain, while the
guard targets per-step decrease. The companion (`ac-completion-spec.md` §1, §3)
records finite diagnostics for global RHS minimality and LHS reducedness; those
diagnostics are evidence, not universal proofs.

## 10. Conditional completeness argument and open obligations

This section gives the completeness argument for the algorithm of §6–9. It adapts Kapur's
and follows standard rewriting metatheory. The argument is on paper, not yet discharged in a
proof assistant: it has not been mechanically checked that our specific construction (e-class
ids as constants, union-find as the constant-rule layer, `by_contains`-driven pair finding)
satisfies every hypothesis those theorems need, so treat §10 and the §12 completeness bullet
as a proof plan and conditional paper argument, not a verified guarantee (the verification plan is in
[Future Work](A3-future-work.md)). Soundness is separate, argued in §12, and does not depend
on this argument.

The intended argument has three obligations. If all three hold for the production
state relation, Newman's Lemma closes the abstract result.

- **Search coverage.** The required finite combinatorial lemma is that every
  non-trivial applicable pair is generated before `Converged`. *(Scope note:
  this lemma is for the plain-AC pass: the shared-child union is where all
  PLAIN superposition partners live. The semantic-property facets deliberately generate
  pairs OUTSIDE this union through their own generators: a rule's axiom critical pairs
  (Kapur §4) are self-pairs needing no partner, and the cancelative disjoint superposition
  (§5.3) pairs same-op rules that may share no child at all: its generator is an explicit
  all-pairs loop over the op's antichain, so the search-completeness claim for those
  facets is by construction in the abstract loop, not by this index argument.)* For a node
  `+M`, the only AC nodes that can rewrite-interact with it are those sharing at
  least one child class, and they all lie in
  `⋃_{x ∈ distinct(M)} by_contains[x] ∩ by_op[+]` (§7). Containment partners
  (`A ⊆ M`) and overlap partners (`A ∩ M ≠ ∅`) are both inside this union; disjoint
  partners (`A ∩ M = ∅`) are correctly skipped because non-overlapping rules
  commute, so their critical pair is trivially joinable (firing them in either order
  reaches the same term). So the pass enumerates, via `by_contains`, a candidate set
  intended to be a superset of the pairs yielding non-trivial critical pairs.
  The implementation obligation also includes duplicate-LHS filtering, touched-delta
  rounds, use-list coverage after merges, and the final full confirmation round. Tests
  cover finite cases; no theorem yet establishes this composition.
- **Local confluence at the reported fixpoint.** Kapur's Critical-Pair Lemma reduces "every one-step
  divergence joins" to the finite check "every critical pair joins" (the only way a
  monomial `+C` rewrites two ways is via two rules whose left multisets both fit
  inside `C`, and every such divergence is an instance of the superposition
  `AB = (A⊎B)−(A∩B)`). (2) The search above computes every critical pair. (3) The
  loop is intended to merge each pair's two reducts and report convergence only when
  a full round adds nothing. To transfer the lemma, a proof must show that
  `normalize_*` plus materialization/merge faithfully realizes Kapur's reduction in
  every supported count domain and that budget/goal exits are excluded.
- **Termination of the unbudgeted completion relation.** There are two
  terminations, with different measures. Normalization (`nf_R` reducing a query to a
  normal form) terminates because every step `+M → +((M−A)⊎{a})` replaces a
  sub-multiset `A` (with `|A| ≥ 1`) by a single class `a`, strictly down in the
  Dickson order (sub-multiset is componentwise `≤`); a total admissible monomial
  order refines that partial order so every emitted rule is decreasing. Kapur's
  completion theorem uses inter-reduction and Dickson's Lemma over a fixed finite
  signature. A production proof must additionally establish that the live rule
  projection remains the required reduced set across duplicate nodes, class merges,
  best-effort RHS selection, semantic-property generators, and incremental rounds.
  Merely observing that one round's surviving LHSs form a finite antichain does not
  prove that the sequence of production rounds terminates.

  One subtlety the measure must respect: new left-sides are **not** bounded by
  "sub-multisets of lcms of input left-sides." A reduct `(AB−A)⊎{a}` adds the rule's
  right-hand class `a`, which need not lie in `AB`, so reducts can be larger than any input
  lcm. There is no clean size bound; termination rests on Dickson antichain-finiteness over
  the finite class set, not on a multiset-size measure. This is the part most likely to need
  care in a formalization.

  Scope: AC-CC termination is not saturation termination. The argument bounds a
  fixed-signature abstract completion problem. Ground AC congruence closure is
  decidable and has finite canonical presentations under the cited results. It does not claim the
  surrounding equality-saturation loop terminates. A user rule like `a → a + 0` is
  expanding (the right side is a proper super-multiset of the left) and oriented the
  growing way; equality saturation with such productive rules can diverge by design,
  bounded only by iteration limits. Each rule the implementation emits passes a
  decreasing-orientation guard, but that fact alone does not prove termination of
  the sequence of completion rounds. The implementation also has a
  node-growth budget precisely because the refinement-level termination obligation
  is open and finite abstract termination does not imply a practical bound.
- **Cost.** A single plain all-pairs scan is quadratic in the number of active
  rules, but that is not the complexity of completion. Basis size, generated
  critical pairs, normalization, semantic-property closure, materialization, and
  repeated rounds can be exponential; the literature contains doubly-exponential
  worst cases for closely related ground equational completion problems. No
  polynomial whole-procedure bound is claimed. Performance statements require
  Criterion measurements for the current implementation.

Conditionally, search coverage plus local confluence plus termination gives
confluence (Newman's Lemma), unique normal forms, and the desired equivalence
`g₁ =_{ACCC(S)} g₂ ⟺ nf_R(g₁) = nf_R(g₂)`. The production code and tests do not
yet establish those premises universally. `CompletionOutcome::Converged` means an
unchanged full implementation round, not a formally verified decision-procedure
certificate. This question is separate from completeness of the larger
term-valued AC-matching relation of §11.

## 11. How the literature handles the §4b example

| Source | Mechanism on `+(a,b)=c, +(b,d)=e` | Where it lives |
|---|---|---|
| Kapur, FSCD 2021 | Def. 4 superposition `AB={a,b,d}`, pair `(+(c,d),+(a,e))`, merge. Terminates by Dickson (Thm 6). | abstract AC-CC algorithm; production correspondence is §8/§10 |
| Conchon et al., LMCS 2012 (AC(X)) | `headCP(R)`: shared `aᵘ={b}`, residuals `{a},{d}`, identical pair. For pure AC it is Kapur, plus a Shostak theory X. §8 separately notes the (open) matching gap. | ground AC-completion; production correspondence remains to prove |
| Schifferer/Ullrich/Hack (KBC) | Offline Knuth-Bendix derives a shortcut rule; "use KBC during saturation" is their future work. | precompute, outside rebuild |

The sources converge on the same critical pair. Production implements the mapped
mechanisms in §6–9; equivalence to Kapur's full procedure is the §10 obligation.

None of them integrates term-valued AC matching into this e-matcher. Binding a scalar
pattern variable to
an un-materialized sub-sum (`?x = a+b` against `+{a,b,c}`) is outside the e-matching
relation every e-graph decides (a variable binds an existing e-class, not a term
with no node), and Kapur and Conchon (§8) leave it aside, because deciding it would
require representing candidate sub-sums. Eagerly materializing all of them produces up
to `2^d` sub-multisets for `d` distinct summands, or more generally
`product_i (m_i + 1)` for multiplicities `m_i`, before accounting for matcher search.
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
`g₁↓_R = g₂↓_R` in the conditional abstract decision procedure.

- **Intended soundness invariant.** Invariant `I`: every rule `f(M)→c ∈ R` and
  every merge `c ~_P d` satisfies `=_{ACCC(S)}`. Base: inputs hold trivially.
  Recanon preserves it by congruence (equal child for equal child). A critical-pair
  merge preserves it, since both reducts equal `f(AB)` (Kapur Lemma 5) and so are
  `ACCC(S)`-equal. This is a local paper argument and focused tests reconstruct
  representative proof paths; no Verus theorem currently establishes it for every
  production transition.
- **Conditional completeness.** If the three §10 obligations hold, Kapur's
  critical-pair lemma and Newman's Lemma yield confluence and unique normal forms.
  Neither an unchanged full round nor the finite basis diagnostics by themselves
  prove those premises.

The verification plan (which proof in Verus, which in Lean, and the staging) is in
[Future Work](A3-future-work.md), since it concerns what remains to be done.

## 13. Lazy completion: on-demand search paid per query

Three ways to run an AC workload, selected on the CLI:

- **plain** (default): canonization and plain congruence; the Part I
  completeness gap stands.
- **eager** (`--derive-ac-eqs`): every rebuild attempts completion. It returns
  `Converged` after an unchanged full round or `AbortedGrowthLimit` after the
  configured growth backstop. Interleaving saturation rules grows the term/class
  pool, so neither the abstract fixed-signature argument nor the implementation
  currently proves termination or completeness of the combined loop.
- **lazy** (`--lazy-ac-eqs`): saturation runs plain; an equality check that
  plain congruence cannot derive runs the search inside a **semi-persistent
  transaction** (mark, enable completion, decide, restore). The logical graph
  state is restored, while the transaction does mutate storage and may retain
  capacity or rebuild transient indices. Restore is not `O(1)` or simply
  `O(touched)`; its cost is the sum of the underlying containers' diff replay,
  regrowth, capture-flag maintenance, and transient reconstruction.

The lazy search has two phases. Phase 1 is one completion rebuild on the
frozen graph (no user-rule rounds interleave, matching the fixed-input scope of
the §10 proof target). Phase 2, when
the pair is still apart and the program has rules, hands the pair to the
saturation driver as an `:until` goal with completion enabled: rounds alternate
rule matching with completion fixpoints and stop the moment the pair joins,
bounded by an alternation budget (default 32 rounds) and the completion
node-growth budget. A budget stop is reported as inconclusive. An unchanged
operational joint round means the selected ruleset and implemented completion
passes found no more work; it is not, without the §10 theorem, a proof of
non-derivability in the abstract AC theory. Phase 2 runs the default ruleset
only.

Three properties of the lazy mode:

- **One transaction across consecutive checks.** The mark is taken at the
  first failing check and the restore happens at the first non-equality-check
  command (or program end), so a run of checks accumulates completion and
  alternation state instead of each re-deriving from scratch. A bare
  `(check t)` closes the transaction too: it materializes its term
  permanently, which an open transaction would discard.
- **Goal polling inside the completion loop.** The queried pair is installed
  as the e-graph's completion goal; the loop polls it between passes *and
  inside a round's two apply loops*, and stops with
  `CompletionOutcome::GoalMet` mid-closure the moment the pair joins. Every
  completion pass inside the alternation is goal-directed the same way.
- **In-round budget check.** The node-growth budget is consulted
  inside a round's apply loops, so a single blown-up round stops mid-apply
  instead of waiting for the between-rounds check.

Focused lazy-mode tests cover transaction sharing, goal polling, growth aborts,
and restoration. This chapter makes no fixed timing, node-count, or speedup
claim; such results belong in a same-revision Criterion campaign with confidence
intervals.

**One consumer the lazy mode does not serve: anti-unification.** The trigger is
an equality check, and `antiunify`/`checkau` are not equality checks, so the
command loop closes the transaction and restores the graph before
`AuSnapshot::new` reads it. The solver therefore searches the plain graph in lazy
mode and reports the same, larger, anti-unifier it reports in plain mode. Only
eager completion changes the relation the solver reasons over. The measurement,
the reason a goal-directed search cannot be adapted to a solver with one OR node
per reachable class pair, and the pinned regression are in
[`19-anti-unification.md`](19-anti-unification.md) §2.8 and
`tests/au_ac_completion_modes.rs`.

## 14. The A-only transfer: inter-reduction for sequences, and where it must stop

An analogous erased-reference gap exists for associativity-only (`Seq`) operators:
build-time flattening splices a pure-`op`-sequence child into its parents, so
the class reference disappears and congruence can no longer connect two
parents that spliced different spellings. The implemented repair targets the
observed case where two pure-sequence classes merge and the resulting class
holds distinct `op`-sequence spellings that flattened parents cannot see. The
tests establish this case; they do not prove it is the only possible loss mode.

The repair (`a_round`, run inside the completion loop, so only when
completion is enabled; plain mode is untouched):
orient each such equation shortlex (longer to shorter, ties by element ids)
and rewrite contiguous occurrences of the larger spelling inside other
`op`-sequences, adding the rewritten sequence and merging with its source
(justification `ACInterReduction`, the same substitute-for-class shape).
Each generated rewrite is checked/oriented shortlex-decreasing; the paper
termination argument for one finite round follows that measure. Rounds run
under the same budget and goal polls as the AC pass. The three
`a_interreduction_*` fixtures pin the gap (plain mode fails, by design) and
the repair under both eager and lazy completion.

**Where it must stop, and why this is a boundary rather than a debt.** The AC
pass has a completeness theorem to aim for because ground AC completion is
Gröbner-shaped: left sides are multisets over a finite pool, Dickson's Lemma
makes the reduced antichain finite (§10), and Narendran-Rusinowitch gives the
finite canonical system. The A-only analogue is completion of a **ground
string rewriting system** (a semi-Thue presentation of a finitely presented
monoid), and there the word problem is undecidable (Markov, Post): no
algorithm decides all A-entailed equalities, and a critical-pair chase can
run forever without a bound to point to. So `a_round` deliberately closes the
single-substitution gap above and does not chase critical pairs. Its merges have
the intended equality-substitution justification and focused proof-log tests;
there is no machine-checked soundness theorem for every production transition.
A complete solver for arbitrary finitely presented monoids is not attainable in
general, and the contrast (ground AC decidability versus the monoid word problem)
is a property of the theories, not of this implementation.

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
