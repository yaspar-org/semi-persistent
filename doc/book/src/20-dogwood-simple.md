# A simple Dogwood policy

This chapter applies clustering and anti-unification to three encodings of one
small agent policy. The complete fixture models only the fragment needed to
separate an event-kind error from presentation differences.

## The rule

[Dogwood](https://github.com/dogwood-policy/dogwood) is a policy language for
runtime verification of agent actions. The example starts from this rule:

> The agent may POST to `/deploy`, but only if a health check has already come
> back 200 in the last 900 seconds.

The event kind determines whether the policy observes an outgoing request or
the response that came back.

## A first-order model

The fixture represents a condition as `Formula` and the phase of an HTTP event
as `EventKind`. `successfulHealth` records the phase, status code, and window;
the two numbers use the default model's built-in `IBig` sort. `All` is ACI with
Boolean true as its identity.

This is a first-order model of the relevant policy fragment, not an
implementation of Dogwood semantics. It omits principals, temporal binders,
field paths, and policy evaluation. Those omissions keep the comparison on the
three facts named in the sentence.

```lisp
{{#include ../examples/20-dogwood-simple.egg:dogwood-simple}}
```

## Three samples

`sampleA` records the three conditions in sentence order. `sampleB` reorders
them and repeats `methodPost`. `sampleC` preserves the guards but changes
`response` to `request`.

The pair checks produce two clusters:

```text
{sampleA, sampleB}  {sampleC}
```

Commutativity absorbs the reordered conditions and idempotence removes the
duplicate. Neither property equates the event kinds.

## The remaining disagreement

The query prints one localized result:

```text
(anti-unify :size 8 :cr 0.1429 :completion exact
  (All
    methodPost
    pathDeploy
    (successfulHealth (Variants response request) 200 900)))
```

The skeleton retains the method, path, status, and window. Only the event kind
requires review. In Dogwood's event schema, response output fields such as a
status code belong to response events; attempting to bind that output on a
request is schema-invalid. Validation can therefore settle this disagreement.

The textual renderings contained ordering, repetition, and event-kind changes.
Clustering absorbed the first two categories, leaving one question with both
readings shown at its source position.
