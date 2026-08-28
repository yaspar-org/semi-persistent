# Canonization and the node kinds

> Chapter contents: the five child representations an operator can have, what
> canonization does to the children on the way in, which declaration selects which
> representation, how multiplicity clamping implements idempotence, nilpotence and
> identity, and what canonization does not do.
>
> Chapter 4 gives the user-facing declaration contract. This chapter explains the
> representations and canonization mechanism that implement it.
>
> Examples: `examples/10-node-kinds.egg`, `examples/10-clamping.egg`,
> `examples/04-illegal-clamp.egg` all exist. Read them first and build the chapter
> around them.
>
> Sources: design `04-canonization.md` is the specification.
> `ac-algebraic-properties.md` for the attribute-to-representation mapping.
> `egraph/src/registry.rs` for `OpKind`, `egraph/src/canon.rs` for the procedure,
> `egraph/src/multiplicity.rs` and `multiset.rs` for the clamps.

## The five child representations

> Table with four columns: representation, the `OpKind` variant that carries it,
> what the children are stored as, and what is consequently not representable.
> The variants are `Normal`, `Commutative`, `A`, `MSet`, `Set`. Give each a name the
> book can use in prose (an ordered tuple, an unordered pair, a sequence, a sorted
> multiset, a sorted set) and use that name consistently everywhere after.
>
> The column that earns the table is the last one: an unordered pair cannot
> represent argument order, a multiset cannot represent order, a set cannot represent
> repetition. State that this is why the corresponding law needs no rule.

## What canonization does

> The procedure on the way in, in order: replace each child by its canonical class,
> then apply the representation's normal form (sort, dedup or clamp), then hash-cons
> the result. State that it runs on build and again on rebuild after a merge, and
> that this is the reason two spellings of an AC term are one e-node rather than two
> nodes plus a rule.
>
> Show it with `print-size`: build `(Add x y)` and `(Add y x)` and account for the
> single node.

## Multiplicity clamping

> The one mechanism behind three attributes, which is why they share a chapter.
> Children of an AC operator are stored with multiplicities, and each attribute is a
> rule on those multiplicities:
>
> - `:idempotent` bounds every multiplicity at 1, which is the `Set` representation;
> - `:nilpotent n` takes multiplicities modulo `n`;
> - `:identity t` drops children equal to `t`.
>
> Show each with a term whose canonized form the reader can predict, then check it.
> `examples/10-clamping.egg` already does some of this.
>
> State what happens when clamping empties a monomial: the term is the unit, which is
> why `:nilpotent` requires `:identity`, and refer back to chapter 4 for the
> legality table rather than restating it.

## Flattening

> Whether a nested application of the same associative operator is flattened into its
> parent, and if so where. Verify this before writing: build `(And (And a b) c)` and
> print the sizes. As of the last check, canonization normalized children (find, sort,
> dedup) without flattening a nested same-operator term, and flattening had to happen
> when the term is built and when a pattern is compiled. Confirm the current
> behaviour, state it plainly, and if a nested term is not flattened say what the
> reader must do about it.

## What canonization does not do

> State positively what the reader gets and where the boundary is. Canonization
> normalizes the children of one node under the declared representation. It does not
> derive consequences that need two nodes to interact: that is congruence closure
> (chapter 6), rewrite rules (chapter 8), or AC completion (chapter 11). Give the
> smallest instance where the difference shows, which is the pair of AC terms that
> plain mode leaves distinct in `examples/11-cc-plain.egg`.
