# Repair by disagreement

This chapter computes a diff between two candidate Dogwood policies produced
from the same natural-language requirement. The diff ignores known language
equivalences, locates the remaining variation points, and presents the
alternatives at each point. These localized alternatives drive clarification
of the original intent.

## Dogwood and temporal policies

[Dogwood](https://github.com/dogwood-policy/dogwood) is a Cedar-derived policy
language for authorization over event histories. Its
[temporal sublanguage](https://dogwood-policy.github.io/dogwood/guide/04-temporal-expressions.html)
is a bounded, past-only fragment of Metric First-Order Temporal Logic (MFOTL).
It provides event predicates, `formerly`, `previous`, `since`, and the `count`
and `sum` aggregations. Every temporal operator has a bounded look-back window.

A `when temporal { phi }` clause evaluates `phi` at the current decision
timepoint against the recorded event history. The
[event schema](https://dogwood-policy.github.io/dogwood/guide/03-event-schema.html)
determines the fields carried by each action and event kind. Request events
carry inputs. Response events can additionally carry outputs such as an HTTP
status code.

The original requirement is:

> The agent may POST to `/deploy`, but only if a health check has already come
> back 200 in the last 15 minutes.

There is no reference policy against which to compare a generated answer. We
instead compare two independently produced candidates and use their localized
differences to formulate review questions.

## The two candidates

Candidate A retains both current-request guards. Its temporal predicate,
however, reads `output.status_code` from a `request` event:

```text
@id("deploy_after_health_check")
permit (
    principal,
    action == Strands::Action::"http:request",
    resource
)
when { context.input.method == "POST" && context.input.path == "/deploy" }
when temporal {
    (count for (t: Timepoint). where (
        formerly within 15m (
            Strands::Action::"http:request"::request{
                callerPrincipal: principal,
                output.status_code: 200
            }
            && tp(t)
        )
    )) >= 1
};
```

Candidate B uses the `response` event kind but omits the `/deploy` guard:

```text
@id("deploy_after_health_check")
permit (
    principal,
    action == Strands::Action::"http:request",
    resource
)
when { "POST" == context.input.method }
when temporal {
    1 <= (count for (t: Timepoint). where (
        formerly within 900s (
            tp(t)
            && Strands::Action::"http:request"::response{
                 output.status_code: 200,
                 callerPrincipal:    principal
               }
        )
    ))
};
```

The missing guard is a fail-open behavior. After a matching 200 response,
candidate B permits a `POST` to `/admin/purge-all` as well as a `POST` to
`/deploy`.

The candidates also contain six presentational differences:

| difference | representation in Semper |
| --- | --- |
| Cedar condition order | `eAnd :assoc-comm-idem` |
| temporal conjunction order | `tAnd :assoc-comm-idem` |
| predicate field order | `args :assoc-comm-idem` |
| `method == "POST"` versus `"POST" == method` | `eEq :comm` |
| `15m` versus `900s` | rewrite `mins` through `secsTimes`, then constant-fold its product |
| `count >= 1` versus `1 <= count` | `(birewrite (tLte a b) (tGte b a))` |

## Encoding Dogwood in Semper

Semper does not evaluate Dogwood policies. It represents their abstract syntax
as sorted first-order terms so that policies can be compared modulo the
declared algebraic properties of the language operators and rewrite rules
encoding known identities in the language. Dogwood remains responsible for
validating and replaying completed policies.

The model retains the policy head, Cedar conditions, temporal conditions,
aggregation binders, field paths, and request and response event kinds. The
main correspondences are:

| Dogwood construct | Semper representation |
| --- | --- |
| `permit (...) when ...` | `rule`, `permit`, and `head` |
| Cedar conditions and multiple `when` clauses | `Expr` terms under `eAnd` |
| `when temporal { phi }` | `(temporal phi)` |
| `formerly within 15m phi` | `(formerly (mins 15) phi)` |
| `formerly within 900s phi` | `(formerly (secs 900) phi)` |
| `Action::"..."::response{...}` | `(pred action response args)` |
| predicate field assignments | `arg` terms collected by `args` |
| `count for (t: Timepoint)` | `count`, `bcons`, and `(bvar 0)` |
| `count(...) >= 1` | `(tGte (agg ...) (tInt 1))` |

Here is the complete executable model:

```lisp
{{#include ../examples/20-dogwood-simple.egg}}
```

The encoding retains each candidate's original time unit. The rewrite from
`mins` to `secs` states the conversion inside the comparison theory:

```lisp
{{#include ../examples/20-dogwood-simple.egg:dogwood-identity}}
```

The first rule builds `(secsTimes 15 60)`. The second rule binds both operands
as `IBig` literal values and evaluates the eager `IBig::*` primitive, reducing
the intermediate term to `(secs 900)`. The equality is therefore derived by
visible rewrite rules rather than imposed while translating the policies.

The identity of `eAnd` represents an omitted condition. It lets the
anti-unifier align candidate A's path guard with `eTrue` instead of replacing
the complete condition with one large variation. Treating Cedar conjunction
as commutative assumes its operands have passed validation and cannot produce
order-dependent errors. Temporal conjunction is set intersection and does not
have that short-circuiting qualification.

## The policy diff

The model runs the exact anti-unifier after applying the comparison identity:

```lisp
{{#include ../examples/20-dogwood-simple.egg:dogwood-main-query}}
```

The measured result has size 61, compression ratio 0.1864, and two variation
points:

```text
(anti-unify :size 61 :cr 0.1864 :completion exact
  (rule
    permit
    (head anyPrincipal (actionEq aHttpRequest) anyResource)
    (eAnd
      (eEq (eCtx (fld fInput (fld fMethod fnil))) (eStr vPOST))
      (temporal
        (tGte
          (agg
            (count
              (bcons tyTimepoint bnil)
              (formerly
                (mins 15)
                (tAnd
                  (tp (bvar 0))
                  (pred
                    aHttpRequest
                    (Variants request response)
                    (args
                      (arg (fld fCallerPrincipal fnil) scopePrincipal)
                      (arg
                        (fld fOutput (fld fStatusCode fnil))
                        (tInt 200))))))))
          (tInt 1)))
      (Variants
        (eEq (eCtx (fld fInput (fld fPath fnil))) (eStr vDeploy))
        eTrue))))
```

The first variation asks whether the historical event is a `request` or a
`response`. The second asks whether the current request must target `/deploy`
or whether the corresponding conjunction slot is `eTrue`.

All six presentational differences have disappeared. No rewrite equates either
of the two reported alternatives.

## Checking the four completions

Two binary variation points produce four complete policies:

| event kind | path guard | source | validation | off-target replay |
| --- | --- | --- | --- | --- |
| `request` | retained | candidate A | fails | not run |
| `request` | omitted | neither candidate | fails | not run |
| `response` | omitted | candidate B | passes | allows |
| `response` | retained | repaired policy | passes | denies |

Dogwood validation rejects both `request` completions:

```text
predicate `Strands::Action::"http:request"::request` mentions field
`output.status_code`, which is not declared on that event
```

The event schema therefore settles the first variation without a policy
reviewer. Request events contain inputs but do not contain response outputs.

Both `response` completions validate. A replay contains a 200 response,
`POST /deploy`, and then `POST /admin/purge-all`:

```text
--- candB ---
@60 (time point 0): ALLOW
@120 (time point 1): ALLOW
--- repaired ---
@60 (time point 0): ALLOW
@120 (time point 1): DENY
```

The validator cannot infer whether `/deploy` was intended. The requirement
settles that variation: retain the path guard. Combining candidate B's event
kind with candidate A's guard produces a policy written by neither candidate:

```text
@id("deploy_after_health_check")
permit (
    principal,
    action == Strands::Action::"http:request",
    resource
)
when { context.input.method == "POST" && context.input.path == "/deploy" }
when temporal {
    1 <= (count for (t: Timepoint). where (
        formerly within 900s (
            tp(t)
            && Strands::Action::"http:request"::response{
                 output.status_code: 200,
                 callerPrincipal:    principal
               }
        )
    ))
};
```

Anti-unification localizes the decisions but does not adjudicate them. Dogwood's
schema settles one decision mechanically; the original statement and replay
settle the other. A mistake shared by both candidates would remain in their
common skeleton, so the correlated-error limitation from Chapter 17 still
applies.
