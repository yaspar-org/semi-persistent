# E-Class Analysis: A Worked Example

**Status**: design for future work; nothing in this document is implemented.
This document follows one program through the e-class analysis and shows the
value stored for each e-class after every command. It is not a specification:
[eclass-analysis.md](eclass-analysis.md) states the design,
`abstract-domains/doc/reduced-product.md` states the reduction protocol, and
the four hand-off tasks (surface syntax #145, class storage #146, saturation
engine #147, domain registry #148) state the interfaces. Where this document
and those disagree, they are right and this document is out of date.

## 1. Domains, records and the stored entry

Three layers hold an abstract value, and only the last one is stored in the
e-graph.

| Layer | What it is | Example |
|---|---|---|
| Domain | one type with lattice operations (`meet`, `join`, `le`) and transfers (`add`, `sub`, ...), each proved sound in `abstract-domains` | `Interval<u8>`, a value `[0, 10]`; `Congruence<u8>`, a value `3 mod 4` |
| Fact record | a struct with one field per domain of a carrier, and a `normalize` that tightens each field using the others | `Facts<u8> { u: Interval<u8>, c: Congruence<u8>, ... }` |
| Stored entry | the encoded record of one e-class, in a semi-persistent pool of the class layer | `ClassData.abs`, a handle into the pool |

A record is not a second kind of information beside the domains. It is one
value of each domain, kept together and normalized together. Each domain is
canonical on its own, but a product of domains is not: `[3, 10] × 3 mod 4` and
`[3, 7] × 3 mod 4` denote the same set. `normalize` returns the one
representation of that set, or `Bot` when the set is empty, so the engine
detects a change with `==` on the stored entry and a conflict as `Bot`
(reduced-product.md, "Canonical facts").

The engine stores one record per e-class and nothing per e-node. An e-node
determines which domain operations run on the records of its class and its
children: a node of a symbol with `:interp` runs that operator's forward and
backward transfers (eclass-analysis.md §6, tier 1).

The registry (#148, §5) wraps the record of each carrier in one type:

```rust
pub enum Value { Bool(Bool4), Int(FactsZ), Bv8(Facts<u8>), Bv16(Facts<u16>),
                 Bv32(Facts<u32>), Bv64(Facts<u64>), Bv128(Facts<u128>), Top }
```

The class-layer pool (#146) stores a `Value` encoded as fixed-width bytes and
never inspects it. `push` and `pop` restore the pool with the classes.

This example uses `Facts<u8>` with two fields: `u`, the unsigned bounds, which
exists today, and `c`, the congruence, which the registry lists as missing and
#129 adds. The congruence `r mod m` denotes the values equal to `r` modulo `m`;
its top is `0 mod 1`.

## 2. The program

```lisp
(sort B8 :interp (bitvec 8) :domains (ubounds congruence))
(function bvadd (B8 B8) B8 :interp bvadd)
(constructor X () B8)
(constructor Y () B8)
(constructor Z () B8)

(refine (X) (interval 0 10))     ; 1
(refine (Y) (congruence 3 4))    ; 2
(refine (Y) (interval 0 20))     ; 3
(let s (bvadd (X) (Y)))          ; 4
(refine (Z) (interval 4 6))      ; 5
(union s (Z))                    ; 6
(union (Y) (Z))                  ; 7
```

## 3. The trace

Each step shows the records it reads, the domain operations it runs, and the
record it stores.

**Command 1.** `(X)` enters a new class `cX` with the top record. The seed
becomes a record with only `u` set, and the engine meets it into `cX` field by
field (interval meet on `u`, congruence meet on `c`), then normalizes.

```
cX before:  { u: [0, 255], c: 0 mod 1 }
seed:       { u: [0, 10],  c: 0 mod 1 }
cX stored:  { u: [0, 10],  c: 0 mod 1 }
```

**Command 2.** `(Y)` enters a new class `cY`. After the meet, `normalize`
rounds the lower bound up to the grid of `c`: 0 becomes 3, the least value
congruent to 3 modulo 4. The upper bound 255 is already on the grid.

```
cY before:  { u: [0, 255], c: 0 mod 1 }
meet:       { u: [0, 255], c: 3 mod 4 }
cY stored:  { u: [3, 255], c: 3 mod 4 }
```

**Command 3.** A second seed on `cY`. `normalize` rounds 20 down to 19. The
interval domain alone cannot do this; the congruence field and the reduction
between the two fields do.

```
meet:       { u: [3, 20], c: 3 mod 4 }
cY stored:  { u: [3, 19], c: 3 mod 4 }
```

**Command 4.** The node `bvadd(cX, cY)` enters a new class `cS`. Because
`bvadd` has `:interp`, the engine runs its forward transfer, which is the
transfer of each enabled domain on that domain's fields. No sum wraps, since
10 + 19 < 256. The congruence of a sum has the modulus `gcd(1, 4) = 1`, so it
is top.

```
interval add:    [0, 10] + [3, 19]   = [3, 29]
congruence add:  0 mod 1 + 3 mod 4   = 0 mod 1
cS stored:       { u: [3, 29], c: 0 mod 1 }
```

**Command 5.** `(Z)` enters a new class `cZ`.

```
cZ stored:  { u: [4, 6], c: 0 mod 1 }
```

**Command 6.** `cS` and `cZ` merge. The surviving class stores the meet of the
two records, normalized.

```
cS:              { u: [3, 29], c: 0 mod 1 }
cZ:              { u: [4, 6],  c: 0 mod 1 }
merged stored:   { u: [4, 6],  c: 0 mod 1 }
```

The value of `cS` changed, so the `bvadd` node runs its backward transfer
(parent refinement, reduced-product.md "How the domains plug into the
e-graph"): `val(X) := val(X) ⊓ (val(S) −
val(Y))` and the same for `Y`. Both differences wrap for some inputs and not
for others (`[4, 6] − [3, 19]` spans −15 to 3), and `Interval<W>::sub` returns
top in that case, so the meets change nothing and no class is scheduled again.
The backward transfer is sound and here it is not precise; a signed-bounds
field `s` would recover the information.

**Command 7.** `cY` merges with the class of `Z`. The intervals `[3, 19]` and
`[4, 6]` overlap, so the meet of the `u` fields alone is not empty.
`normalize` rounds 4 up to 7 and 6 down to 3, and returns `Bot` because 7 > 3.

```
cY:              { u: [3, 19], c: 3 mod 4 }
class of Z:      { u: [4, 6],  c: 0 mod 1 }
meet:            { u: [4, 6],  c: 3 mod 4 }
normalize:       Bot
```

`Bot` is a conflict: no assignment of values to `X`, `Y` and `Z` satisfies the
seeds and the unions. The engine reports it as #147 §5 specifies.

## 4. What each step used

| Command | Event | Domain operations |
|---|---|---|
| `refine` | seed | build a record from the literal, `meet`, `normalize` |
| `(let s (bvadd ...))` | make | forward transfer of each enabled domain |
| `union` | merge | `meet`, `normalize`; `Bot` is a conflict |
| a class value changes | parent refinement | backward transfer of each node in the class |
| a child value changes | child refinement | forward transfer of each parent node |

Every change to a stored record is a domain operation. The record is what the
domains compute on, and the class is where the result is kept.

## 5. A domain that is not a field

`StridedInterval<W>`, `Wrapped<W>` and `Sign` are domains with no field in
`Facts<W>` or `FactsZ`. They take part only inside one computation: through
`Refine`, a domain reads a record (`refine`) and writes what it knows into a
record (`to_channel`), so it can sit in a `Product` while a transfer runs, and
the e-graph keeps only the record that the product's `to_channel` returns
(reduced-product.md, "Product details"). What such a domain knows beyond what
the record can express is lost after the step. The rule follows from this: a
domain is exact in the analysis only once its facts are a field of the record
(reduced-product.md, "The limit, and why fields matter").

## 6. What the example leaves out

- Derived merges: a class whose record is a singleton merges with the literal
  of that value (eclass-analysis.md §8). No class in the example becomes a
  singleton.
- The per-class budget of strict changes per `run` iteration
  (eclass-analysis.md §7).
- Abstract guards in rule bodies, which read a record and never write one
  (abstract-syntax.md §7, on #145).
- `:range`, which is a seed on every node of a function.
