# Anti-Unification with Equality Saturation

This document demonstrates why anti-unification over e-graphs (with rewrite
rules) produces better results than anti-unification over fixed syntax trees.
Saturation discovers semantic equivalences between syntactically different
subterms, reducing the number of `Variants` nodes (spurious differences) in
the anti-unifier without affecting the genuine differences.

Two categories of examples are shown:
1. Full equivalence: saturation merges the entire input pair into one class
   (compression ratio goes to 0, zero Variants).
2. Partial improvement: saturation merges one spurious subterm difference while
   leaving a genuine difference intact (compression ratio improves but stays
   nonzero, Variants count decreases by one).

## Setup: the theory

```lisp
(sort Bool)
(sort Int)

(function impl (Bool Bool) Bool)
(function neg (Bool) Bool)
(function lti (Int Int) Bool)
(function lei (Int Int) Bool)
(function eqi (Int Int) Bool :comm)
(function conj2 (Bool Bool) Bool :comm)
(function disj2 (Bool Bool) Bool :comm)
```

The rewrite rules available to saturation:
```lisp
; DeMorgan: neg(conj2(a, b)) = disj2(neg(a), neg(b))
(rewrite (neg (conj2 a b)) (disj2 (neg a) (neg b)))

; comparison decomposition: lei(a, b) = disj2(lti(a, b), eqi(a, b))
(rewrite (lei a b) (disj2 (lti a b) (eqi a b)))

; double negation elimination: neg(neg(a)) = a
(rewrite (neg (neg a)) a)
```

## Full equivalence examples

These show saturation discovering that the two input formulas are semantically
identical, collapsing the anti-unifier to the shared term (zero Variants, CR = 0).

### DeMorgan

```
Formula A: impl(neg(conj2(p, q)), r)
Formula B: impl(disj2(neg(p), neg(q)), r)
```

Before saturation (pure syntactic comparison):
```
(impl (Variants (neg (conj2 p q)) (disj2 (neg p) (neg q))) r)
  size 11, CR 0.71
```
The entire antecedent is a Variants: structurally `neg(conj2(...))` vs
`disj2(neg(...), neg(...))` are different operators at the root.

After `(run 3)` with DeMorgan:
```
(impl (neg (conj2 p q)) r)
  size 6, CR 0.00
```
Saturation applied `neg(conj2(p,q)) => disj2(neg(p), neg(q))` to A's
antecedent, placing both forms in the same e-class. The anti-unifier sees one
class (not two), so it returns the concrete term directly with no Variants.

### Comparison decomposition

```
Formula A: impl(lei(x, y), p)
Formula B: impl(disj2(lti(x, y), eqi(x, y)), p)
```

Before: size 12, CR 0.78. After: size 5, CR 0.00 (perfect).

### Double negation

```
Formula A: impl(p, neg(neg(q)))
Formula B: impl(p, q)
```

Before: size 6, CR 0.60. After: size 3, CR 0.00 (perfect).

## Partial improvement examples

These show saturation reducing the Variants count by one (merging a spurious
syntactic difference) while leaving a genuine semantic difference intact.

### DeMorgan + differing consequent

```
Formula A: impl(neg(conj2(p, q)), conj2(r, s))
Formula B: impl(disj2(neg(p), neg(q)), conj2(r, neg(s)))
```

The antecedents are equivalent (DeMorgan). The consequents genuinely differ:
`conj2(r, s)` vs `conj2(r, neg(s))` (one conjunct is negated).

Before saturation:
```
(impl
  (Variants (neg (conj2 p q)) (disj2 (neg p) (neg q)))
  (conj2 r (Variants s (neg s))))
  size 15, CR 0.70, 2 Variants
```
Both the antecedent mismatch and the consequent mismatch show as Variants.
The search cannot tell which is a true semantic difference and which is just a
syntactic encoding choice.

After `(run 3)` with DeMorgan:
```
(impl (neg (conj2 p q)) (conj2 r (Variants s (neg s))))
  size 10, CR 0.22, 1 Variant
```
The antecedent merged (DeMorgan equivalence discovered); only the genuine
consequent difference remains. The compression ratio dropped from 0.70 to 0.22.

### Comparison decomposition + differing consequent

```
Formula A: impl(conj2(lei(x,y), lti(y,z)), p)
Formula B: impl(conj2(disj2(lti(x,y), eqi(x,y)), lti(y,z)), q)
```

Both preconditions have `conj2(?, lti(y,z))`. In A the first conjunct is
`lei(x,y)`, in B it is `disj2(lti(x,y), eqi(x,y))` (the expanded form of <=).
The consequents genuinely differ: `p` vs `q`.

Before:
```
(impl
  (conj2 (lti y z) (Variants (lei x y) (disj2 (lti x y) (eqi x y))))
  (Variants p q))
  size 17, CR 0.62, 2 Variants
```

After `(run 3)` with the lei-expansion rule:
```
(impl (conj2 (lei x y) (lti y z)) (Variants p q))
  size 10, CR 0.11, 1 Variant
```
The precondition fully merged (lei and its expansion are now the same class);
only the consequent difference `p` vs `q` remains.

### Double negation + differing sibling

```
Formula A: impl(p, conj2(neg(neg(q)), r))
Formula B: impl(p, conj2(q, neg(r)))
```

In the consequent `conj2(?, ?)`: one child is `neg(neg(q))` vs `q` (semantically
the same), the other is `r` vs `neg(r)` (genuinely different).

Before:
```
(impl p (conj2 (Variants r q) (neg (Variants (neg q) r))))
  size 9, CR 0.43
```
The commutative matching is confused by the surface form; both children appear
as Variants with entangled subterms.

After `(run 3)` with double-negation elimination:
```
(impl p (conj2 q (Variants r (neg r))))
  size 7, CR 0.33, 1 Variant
```
`neg(neg(q))` merged with `q`; the commutative matching now correctly pairs
`q` with `q` (shared) and isolates `r` vs `neg(r)` as the sole difference.

## Why this matters

Pure syntactic anti-unification (without an e-graph) would always produce the
"before" results: every syntactic difference becomes a Variants node regardless
of whether it represents a genuine semantic divergence or just an encoding choice.
Saturation lets the e-graph absorb the encoding choices as equivalences within
a class, and the anti-unifier operates on classes rather than fixed terms. The
result: fewer Variants, lower compression ratios, and the surviving Variants
correspond to actual semantic differences between the inputs.

This is the fundamental advantage of doing anti-unification over e-graphs:
the search explores all equivalent representations simultaneously, finding
alignments that no comparison of two fixed syntax trees could discover.
