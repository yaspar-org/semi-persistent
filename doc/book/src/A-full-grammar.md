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
                 | "(" operator { term } ")"


pattern          = literal
                 | identifier
                 | "(" "=" pattern pattern ")"
                 | "(" operator [ rest ] { pattern-child } [ rest ] ")"

pattern-child    = pattern [ ":" multiplicity-spec ]
rest             = ".." identifier

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

birewrite        = "(" "birewrite" pattern pattern
                   { birewrite-tag } ")"

rule             = "(" "rule"
                   "(" { pattern } ")"
                   "(" { action } ")"
                   { ruleset-tag } ")"

rewrite-tag      = when-clause | ":subsume" | ruleset-tag
birewrite-tag    = when-clause | ruleset-tag
when-clause      = ":when" "(" { pattern } ")"
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
                 | print-size
                 | print-stats
                 | antiunify
                 | checkau

check            = "(" "check" check-body ")"

check-body       = term
                 | "(" "=" term term ")"
                 | "(" "!=" term term ")"

extract          = "(" "extract" term ")"

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

## Restrictions checked after parsing

The grammar gives the shape of each form. Name resolution and sortchecking add
constraints that depend on earlier declarations and therefore cannot be
expressed in the productions above.

- Declarations are processed in source order. Sorts, operators, rulesets, and
  names introduced by `let` must exist before a command refers to them.
- A bare top-level application is an insertion. Its head must be a declared
  operator name that is not one of the command keywords.
- Pattern rest variables are legal only on variadic operators. Associative
  sequence operators permit a prefix rest, a suffix rest, or both. AC and ACI
  operators permit only a suffix rest.
- Multiplicity specifications and RHS multiplicity expressions apply only to
  AC multiset elements. Sequence and set elements do not carry multiplicities.
- `(= p q)` is the reserved root-binding pattern. A primitive expression is
  accepted only as a predicate guard rooted at a top-level conjunct in a rule
  body or `:when` clause, and the guard must return `bool`.
- A splice or comprehension must consume a rest variable of the corresponding
  sequence, set, or multiset kind. A right-hand-side name must be bound on the
  left-hand side, introduced by its comprehension, or refer to an earlier
  `let` binding.
- `birewrite` rejects `:subsume` and multiplicity annotations on either side.
  A `rule` accepts `:ruleset`, but not `:when` or `:subsume`; guard patterns go
  directly in its body.
- Declaration tag combinations, operator arities, term sorts, and literal
  spellings are validated during sortchecking. Available literals depend on
  the selected literal model.
- A `:nilpotent` order is between 2 and 255. Values for `:cost` and
  `checkau :max_size` must fit in an unsigned 32-bit integer. Run limits,
  playout counts, and parsed multiplicities use unsigned 64-bit integers.
