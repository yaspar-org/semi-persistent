# Anti-Unification Example: Contract Pair with Three Atomic Differences

This document walks through a concrete anti-unification run on two structured
formulas (conjunctions of implications) that differ in exactly three atomic
positions. Every algebraic annotation in the system is exercised: conjunct
order, equality argument order, and addition argument order are all deliberately
scrambled between the two inputs to demonstrate that canonization makes them
invisible to the search.

## Operator declarations

```lisp
; plain ordered operators (positional semantics, argument order matters)
(function impl (Bool Bool) Bool)
(function neg (Bool) Bool)
(function lti (Int Int) Bool)
(function lei (Int Int) Bool)
(function gti (Int Int) Bool)
(function gtr (Real Real) Bool)
(function ger (Real Real) Bool)

; commutative equality: (eqi x y) and (eqi y x) are the same node
(function eqi (Int Int) Bool :comm)

; AC addition with neutral element: (addr w t) = (addr t w), (addr x (zero)) = x
(function zero () Real)
(function addr (Real) Real :assoc-comm :identity (zero))

; ACI conjunction with neutral element: unordered set, duplicates collapse, tt drops
(function tt () Bool)
(function conj (Bool) Bool :assoc-comm-idem :identity (tt))

; ACI disjunction with neutral element
(function ff () Bool)
(function disj (Bool) Bool :assoc-comm-idem :identity (ff))
```

The annotations determine how the anti-unifier treats each operator:
- `conj`, `disj` (`:assoc-comm-idem :identity`): elements form an unordered set;
  the search finds the optimal bijection regardless of storage order; the identity
  element absorbs absent elements when cardinalities differ.
- `eqi` (`:comm`): arguments are interchangeable; `(eqi x y)` and `(eqi y x)` are
  the same e-graph node.
- `addr` (`:assoc-comm :identity`): arguments are interchangeable, the operator
  flattens associatively, and `(addr x (zero))` reduces to `x`.
- `impl`, `neg`, comparisons (no annotation): positional semantics; argument order
  matters; `(lti x y)` and `(lti y x)` are distinct nodes.

## The two inputs

Each contract is a conjunction of five implications. Two clauses are identical
(modulo commutative argument reordering); three differ in one atom each. The
conjuncts appear in completely different orders at every nesting level.

```
Contract A (top-level order: c1, c3, c5, c2, c4):
  (x = y)                             => neg p
  (y <= z) and r                      => (w > v) and (neg q)
  p and (x = z)                       => neg r
  (y = 0) and (w > v)                 => x < y
  (w > v) and (t > v)                 => (w + t) > v

Contract B (top-level order: c4, c2, c1, c5, c3):
  (w > v) and (0 = y)                 => x <= y           [<= instead of <]
  r and (y <= z)                      => (neg q) and (w >= v)    [>= instead of >]
  (y = x)                             => neg p            [eqi args flipped]
  (t > v) and (w > v)                 => (t + w) > v      [addr/conj args flipped]
  (z = x) and q                       => neg r            [eqi args flipped; q not p]
```

Scrambled elements (canonized away by the algebraic annotations):
- Clause 1: `(eqi x y)` in A vs `(eqi y x)` in B (`:comm` makes them identical)
- Clause 3: `(eqi x z)` in A vs `(eqi z x)` in B (same)
- Clause 4: `(eqi y izero)` in A vs `(eqi izero y)` in B (same)
- Clause 5: `(addr w t)` in A vs `(addr t w)` in B (`:assoc-comm` makes them identical)
- All inner `conj` atoms appear in different orders between A and B

The three genuine differences (not removed by canonization):
1. Clause 2 postcondition: `(gtr w v)` vs `(ger w v)` (different operators)
2. Clause 3 precondition: `p` vs `q` (different atoms)
3. Clause 4 postcondition: `(lti x y)` vs `(lei x y)` (different operators)

## The .egg script

```lisp
(sort Bool)
(sort Int)
(sort Real)

(function x () Int)
(function y () Int)
(function z () Int)
(function w () Real)
(function v () Real)
(function t () Real)
(function p () Bool)
(function q () Bool)
(function r () Bool)
(function tt () Bool)
(function ff () Bool)

(function impl (Bool Bool) Bool)
(function neg (Bool) Bool)
(function lti (Int Int) Bool)
(function lei (Int Int) Bool)
(function gti (Int Int) Bool)
(function gtr (Real Real) Bool)
(function ger (Real Real) Bool)
(function eqi (Int Int) Bool :comm)
(function zero () Real)
(function addr (Real) Real :assoc-comm :identity (zero))
(function izero () Int)
(function conj (Bool) Bool :assoc-comm-idem :identity (tt))
(function disj (Bool) Bool :assoc-comm-idem :identity (ff))

; clause 1: A writes (eqi x y), B writes (eqi y x) -- canonize to same node
(let c1a (impl (eqi (x) (y)) (neg (p))))
(let c1b (impl (eqi (y) (x)) (neg (p))))

; clause 2: conj atoms in different order; difference in postcond operator
(let c2a (impl (conj (lei (y) (z)) (r)) (conj (gtr (w) (v)) (neg (q)))))
(let c2b (impl (conj (r) (lei (y) (z))) (conj (neg (q)) (ger (w) (v)))))

; clause 3: conj atoms flipped; eqi args flipped; p vs q difference
(let c3a (impl (conj (p) (eqi (x) (z))) (neg (r))))
(let c3b (impl (conj (eqi (z) (x)) (q)) (neg (r))))

; clause 4: conj atoms flipped; eqi args flipped; postcond operator differs
(let c4a (impl (conj (eqi (y) (izero)) (gtr (w) (v))) (lti (x) (y))))
(let c4b (impl (conj (gtr (w) (v)) (eqi (izero) (y))) (lei (x) (y))))

; clause 5: conj atoms flipped; addr args flipped -- canonizes to same node
(let c5a (impl (conj (gtr (w) (v)) (gtr (t) (v))) (gtr (addr (w) (t)) (v))))
(let c5b (impl (conj (gtr (t) (v)) (gtr (w) (v))) (gtr (addr (t) (w)) (v))))

; top-level conjuncts in completely different orders:
(let contractA (conj c1a c3a c5a c2a c4a))
(let contractB (conj c4b c2b c1b c5b c3b))

(antiunify contractA contractB :algorithm exact)
(antiunify contractA contractB :algorithm uct :playouts 5000)
```

Run with:
```
cargo run -p semi-persistent-egraph -- egraph/examples/au_contract_pair.egg
```

## Output

```
(anti-unify size 58 cr 0.1373 ...)
```

Both algorithms (exact and UCT) find the same optimum.

## The anti-unifier (structured)

```
(conj
  ; clause 1: fully shared (eqi canonized the argument flip away)
  (impl (eqi x y) (neg p))

  ; clause 2: one difference in the postcondition comparison
  (impl (conj (lei y z) r)
        (conj (neg q)
              (Variants (gtr w v) (ger w v))))

  ; clause 3: one difference in the precondition atom
  (impl (conj (Variants p q) (eqi x z))
        (neg r))

  ; clause 4: one difference in the postcondition comparison
  (impl (conj (gtr w v) (eqi y izero))
        (Variants (lti x y) (lei x y)))

  ; clause 5: fully shared (addr and conj canonized the argument flips away)
  (impl (conj (gtr w v) (gtr t v))
        (gtr (addr w t) v)))
```

## What each annotation contributes

`:comm` on `eqi`: clauses 1, 3, and 4 use `eqi` with arguments written in
opposite order between contracts A and B. The commutative canonization makes
`(eqi x y)` and `(eqi y x)` the same node in the e-graph before anti-unification
even begins. Without `:comm`, each such flip would appear as a spurious Variants.

`:assoc-comm` on `addr`: clause 5 writes `(addr w t)` in A and `(addr t w)` in
B. These canonize to the same node. Without the annotation, the anti-unifier
would report `(Variants (addr w t) (addr t w))` (a false difference).

`:assoc-comm-idem` on `conj`: the outer conjunction has its 5 clauses in
order (1,3,5,2,4) in contract A and (4,2,1,5,3) in contract B. The inner
conjunctions also have their atoms scrambled. The ACI vertex enumeration
explores all 5! = 120 bijections at the top level (and smaller bijections at
each inner conjunction) and finds the pairing that maximizes backbone. Without
set semantics, a positional zip at the top level would misalign clauses and
produce a much larger anti-unifier with many more Variants.

`:identity (tt)` on `conj`: when one contract has more clauses than the other
(the second example in the script), the shorter side is padded with `tt` (the
neutral element). The missing clause appears as `Variants(clause, tt)`, meaning
"present in one contract, absent (= trivially true) in the other."

## Second example: unequal clause counts

The script also runs:
```lisp
(let contractC (conj c1a c2a c3a c5a))    ; 4 clauses
(let contractD (conj c5b c1b c2a))         ; 3 clauses

(antiunify contractC contractD :algorithm exact)
```

Output:
```
(anti-unify size 41 cr 0.2250
  (conj
    (impl (eqi x y) (neg p))
    (impl (conj (lei y z) r) (conj (gtr w v) (neg q)))
    (impl (conj (gtr w v) (gtr t v)) (gtr (addr w t) v))
    (Variants (impl (conj p (eqi x z)) (neg r)) tt)))
```

Three clauses are fully shared. The fourth clause (present in C, absent in D)
appears as `Variants(clause3, tt)`: the identity `tt` on the right side means
"this conjunct is vacuously true in contract D" (since `conj{..., tt} = conj{...}`
in the algebra).

## Metrics

- Input size (each contract): ~51 nodes
- Anti-unifier size: 58 nodes
- Compression ratio: 0.137 (14% overhead; 86% shared backbone)
- Variant mass: 6 (two concrete nodes per Variants, three differences)
- Backbone: 52 nodes of shared structure
