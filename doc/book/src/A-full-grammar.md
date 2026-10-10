# Annex A. Complete surface-language grammar

This annex collects the complete surface grammar in one place. The grammar
describes source forms; the chapters that introduce each form define its
behavior.

Braces mean zero or more repetitions, brackets mark an optional item, and `|`
separates alternatives. Quoted words and punctuation are literal tokens.
Whitespace and comments may appear between tokens unless a production states
otherwise.

```text
alphabetic       = any alphabetic character
alphanumeric     = any alphabetic character or decimal digit
digit            = "0" | "1" | "2" | "3" | "4"
                 | "5" | "6" | "7" | "8" | "9"

identifier       = identifier-start { identifier-rest }
identifier-start = alphabetic | "_"
identifier-rest  = alphanumeric | "_"

symbol           = "<<" | ">>" | "<=" | ">=" | "!=" | "==" | "=>"
                 | "+" | "-" | "*" | "/" | "%" | "<" | ">"
                 | "&" | "|" | "^" | "~"

operator         = identifier
                 | identifier "::" ( identifier | symbol )
                 | symbol

comment          = ";" { any character except newline } [ newline ]

unsigned-integer = digit { digit }
integer          = [ "-" ] unsigned-integer
rational         = integer "/" integer
exponent         = ( "e" | "E" ) [ "+" | "-" ] unsigned-integer
floating-point   = [ "-" ] unsigned-integer
                   ( "." { digit } [ exponent ] | exponent )
boolean          = "true" | "false"
quote            = character U+0022
backslash        = character U+005C
string           = quote { string-character | escape } quote
string-character = any character except quote and backslash
escape           = backslash any character
literal          = rational | floating-point | integer | boolean | string


program          = { command }

command          = declaration
                 | rule-command
                 | term-command
                 | control-command
                 | query-command


declaration      = sort-declaration
                 | operator-declaration
                 | datatype-declaration

sort-declaration = "(" "sort" identifier ")"

operator-declaration
                 = "(" ( "function" | "constructor" ) identifier
                   "(" { identifier } ")" identifier
                   { declaration-tag } ")"

datatype-declaration
                 = "(" "datatype" identifier { variant } ")"

variant          = "(" identifier { identifier }
                   { declaration-tag } ")"

declaration-tag  = algebraic-tag | extraction-tag

algebraic-tag    = ":assoc"
                 | ":comm"
                 | ":assoc-comm"
                 | ":assoc-comm-idem"
                 | ":assoc-left"
                 | ":assoc-right"
                 | ":idempotent"
                 | ":nilpotent" [ unsigned-integer ]
                 | ":identity" term
                 | ":cancellative"
                 | ":inverse" identifier

extraction-tag   = ":cost" unsigned-integer
                 | ":unextractable"


term             = literal
                 | identifier
                 | "(" operator { term-child } ")"

term-child       = term [ ":" unsigned-integer ]


pattern          = literal
                 | identifier
                 | "(" "=" pattern pattern ")"
                 | "(" operator [ rest ] { pattern-item } [ rest ] ")"

pattern-item     = pattern-child
                 | rest
                 | sequence-filter

pattern-child    = pattern [ ":" multiplicity-spec ]
rest             = ".." identifier

sequence-filter  = "(" ".." identifier [ ":" multiplicity-spec ]
                   pattern [ ":except" identifier ] ")"

multiplicity-spec
                 = unsigned-integer
                 | identifier [ comparison unsigned-integer ]

comparison       = ">=" | "<=" | "==" | "!=" | ">" | "<"


rhs              = literal
                 | identifier
                 | "(" operator { rhs-child } ")"

rhs-child        = rhs [ ":" multiplicity-expression ]
                 | splice

splice           = ".." identifier
                 | set-comprehension
                 | multiset-comprehension
                 | sequence-comprehension
                 | row-comprehension

set-comprehension
                 = ".." "{" rhs "for" identifier "in" identifier
                   [ filter ] "}"

multiset-comprehension
                 = ".." "{" rhs ":" multiplicity-expression
                   "for" identifier ":" identifier "in" identifier
                   [ filter ] "}"

sequence-comprehension
                 = ".." "[" rhs "for" identifier "in" identifier
                   [ filter ] "]"

row-comprehension
                 = ".." ( "{" | "[" ) rhs [ ":" multiplicity-expression ]
                   "for" binders "in" source [ filter ] ( "}" | "]" )

binders          = binder
                 | "(" binder { binder } ")"

binder           = identifier [ ":" ( identifier | "_" ) ]

source           = identifier
                 | rhs

filter           = "if" rhs

multiplicity-expression
                 = unsigned-integer
                 | identifier
                 | "(" multiplicity-operator
                   multiplicity-expression multiplicity-expression ")"

multiplicity-operator
                 = "u64::+" | "u64::-" | "u64::*" | "u64::/"
                 | "u64::%" | "u64::min" | "u64::max"


rule-command     = ruleset-declaration
                 | rewrite
                 | birewrite
                 | rule

ruleset-declaration
                 = "(" "ruleset" identifier ")"

rewrite          = "(" "rewrite" pattern rhs { rewrite-tag } ")"
                 | "(" "rewrite" pattern rhs { sequence-rewrite-tag } ")"

birewrite        = "(" "birewrite" pattern pattern
                   { birewrite-tag } ")"

rule             = "(" "rule"
                   "(" { pattern } ")"
                   "(" { action } ")"
                   { ruleset-tag | ":flatten" } ")"

rewrite-tag      = when-clause | ":subsume" | ":flatten" | ruleset-tag
sequence-rewrite-tag
                 = sequence-when-clause | let-clause | ":flatten"
                 | ruleset-tag
birewrite-tag    = when-clause | ":flatten" | ruleset-tag
when-clause      = ":when" "(" { pattern } ")"
sequence-when-clause
                 = ":when" "(" { rhs } ")"
let-clause       = ":let" "(" { "(" identifier rhs ")" } ")"
ruleset-tag      = ":ruleset" identifier

action           = "(" "union" rhs rhs ")"
                 | "(" "set" "(" identifier { rhs } ")" rhs ")"
                 | "(" operator { insert-child } ")"

insert-child     = rhs | splice


term-command     = "(" "let" identifier term ")"
                 | "(" "union" term term ")"
                 | "(" identifier { term } ")"


control-command  = run
                 | push
                 | pop

run              = "(" "run" [ identifier ] unsigned-integer
                   [ until-clause ] ")"

until-clause     = ":until"
                   "(" ( "=" | "!=" ) term term ")"

push             = "(" "push" [ ":shrink" ] ")"
pop              = "(" "pop" ")"


query-command    = check
                 | extract
                 | cost-model
                 | dump-egraph
                 | print-size
                 | print-stats
                 | antiunify
                 | checkau

check            = "(" "check" check-body ")"

check-body       = term
                 | "(" "=" term term ")"
                 | "(" "!=" term term ")"

extract          = "(" "extract" term { extract-option } ")"

extract-option   = ":cost" cost-name
                 | ":rung" ( "selection" | "levels" | "splits"
                           | "binary" | "orders" )
                 | ":budget" unsigned-integer
                 | ":solver" ( "internal" | "dpw" | "roundingsat" | "greedy"
                             | "(" ( "opb" | "asp" | "minizinc" )
                               string { string } ")" )
                 | ":file" string
                 | ":proof" string
                 | ":band" unsigned-integer unsigned-integer
                 | ":count" unsigned-integer

cost-model       = "(" "cost-model" cost-name
                   ( ":script" | ":rust" | ":asp" | ":minizinc" ) string ")"

cost-name        = identifier-start { identifier-rest | "-" }

dump-egraph      = "(" "dump-egraph" term ":file" string ")"

print-size       = "(" "print-size" [ operator ] ")"

print-stats      = "(" "print-stats"
                   [ ":file" string ] ")"

antiunify        = "(" "antiunify" term term
                   { antiunify-option } ")"

checkau          = "(" "checkau" term term
                   { checkau-option } ")"

antiunify-option = ":playouts" unsigned-integer
                 | ":algorithm" ( "exact" | "uct" )
                 | ":cycles" cycle-mode

checkau-option   = antiunify-option
                 | ":max_size" unsigned-integer

cycle-mode       = "sides" | "sides-current" | "pair"
```

The `symbol` tokens are lexical. No predeclared primitive is named `<<` or
`>>`, so Semper has no shift operators.

## Restrictions checked after parsing

The grammar gives the shape of each form. Name resolution and sortchecking add
constraints that depend on earlier declarations and therefore cannot be
expressed in the productions above.

- Declarations are processed in source order. Sorts, operators, rulesets, and
  names introduced by `let` must exist before a command refers to them.
- A bare top-level application is an insertion. Its head must be a declared
  operator name that is not one of the command keywords. Its direct children
  carry no counts.
- A `term-child` count is written with no space before the colon. It is at
  least 1 and is accepted only on the children of an `:assoc`, `:assoc-comm`,
  or `:assoc-comm-idem` application.
- Pattern rest variables are legal only on variadic operators. An ordinary
  pattern permits a prefix rest, a suffix rest, or both, on any variadic
  operator. A sequence rewrite (below) permits any number of bare sequences
  between children under `:assoc`, and at most one under AC or ACI.
- Multiplicity specifications in patterns apply only to AC multiset elements;
  sequence and set pattern elements do not carry them. An RHS multiplicity
  expression may annotate a child of an AC or associative application: under
  `:assoc` the child is repeated. An ACI operator stores a set, so a count on its
  child is rejected in a ground term, a pattern, and a right-hand side.
- `(= p q)` is the reserved root-binding pattern. In a pattern, a primitive
  expression is accepted only as a predicate guard rooted at a top-level
  conjunct in a rule body or `:when` clause, and the guard must return `bool`.
- A splice or comprehension must consume a rest variable of the corresponding
  sequence, set, or multiset kind. A right-hand-side name must be bound on the
  left-hand side, introduced by its comprehension, or refer to an earlier
  `let` binding.
- `birewrite` rejects `:subsume`, multiplicity annotations, and sequence
  patterns on either side.
  A `rule` accepts `:ruleset`, but not `:when` or `:subsume`; guard patterns go
  directly in its body.
- Declaration tag combinations, operator arities, term sorts, and literal
  spellings are validated during sortchecking. Available literals depend on
  the selected literal model.
- A sequence rewrite is a `rewrite` whose root pattern has a sequence filter or
  a bare sequence between children. It takes `sequence-rewrite-tag`s; an
  ordinary rewrite takes `rewrite-tag`s. Its root operator is `:assoc`,
  `:assoc-comm`, or `:assoc-comm-idem`; under `:comm` it is rejected, since two
  simple patterns already match both orders. Filters appear at the root only: a
  filter inside a filter, and a filter or bare sequence outside the left-hand
  side of a `rewrite`, are rejected. A multiplicity on a filter is accepted under
  AC, and under ACI only if 1 satisfies it. `:except` is accepted under AC and
  ACI only. It names another filter of the same pattern, and a cycle of
  `:except` is rejected. Every variable of a
  filter's pattern names a sequence; where a scalar is expected, a sequence is
  rejected unless it is under a reduction (`min`, `max`, `sum`, `count`), a
  sequence primitive (`zip`, `concat`, `union-by`, `narrow`, `narrowed`), a
  splice, or a comprehension. A comprehension binding k names needs a source of
  k columns, and a column of a multiset sequence is bound as `x:k` or `x:_`.
  `:let` is accepted on sequence rewrites. `:subsume` is not. A multiplicity
  expression in a sequence rewrite uses `+`, `-`, `*`, `min`, or `max`, with or
  without the `u64::` prefix.
- `extract` with options needs `:cost`, naming an earlier `cost-model`. The
  rung defaults to `selection` and the solver to `internal`. A `cost-model`
  with `:script` compiles the Roto script when the program is checked, so an
  error in the script, a polarity error included, rejects the program. An `:asp`
  model needs an `asp` solver. A `:minizinc` model needs a `minizinc` solver,
  and a `minizinc` solver needs a `:minizinc` model. `:band` needs the internal
  solver, and `:count` defaults to 10. `:proof` needs an `opb` or `roundingsat`
  solver. [Part V](24-extraction-under-cost-models.md) defines these options.
- A `:nilpotent` order is between 2 and 255. Values for `:cost` and
  `checkau :max_size` must fit in an unsigned 32-bit integer. Run limits,
  playout counts, and parsed multiplicities use unsigned 64-bit integers.
