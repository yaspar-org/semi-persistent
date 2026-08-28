# A larger Dogwood policy

Five samples produce three clusters and three representative-pair queries.
This chapter groups recurring alternatives across those queries so the review
list grows with distinct decisions rather than with cluster pairs.

## The expanded model

The fixture retains Chapter 20's deploy and health-check vocabulary. It adds
`Lte`, `Ite`, `directCopy`, and `multipartCopy` for a shared ground
conditional. All five samples contain
`(Ite (Lte 100 100) (directCopy) (multipartCopy))`. It supplies more shared
structure but creates no disagreement.

The samples vary along two dimensions:

| sample | health event | `/deploy` guard | presentation |
| --- | --- | --- | --- |
| `sampleA1` | response | present | baseline |
| `sampleA2` | response | present | reordered, repeated guard |
| `sampleB` | request | present | baseline |
| `sampleC1` | response | absent | baseline |
| `sampleC2` | response | absent | reordered, repeated method |

## Three clusters

The complete pair grid records the partition:

```lisp
{{#include ../examples/21-dogwood-larger.egg:larger-partition}}
```

Its result is

```text
{sampleA1, sampleA2}  {sampleB}  {sampleC1, sampleC2}
```

The two presentation-only variants join their corresponding classes during
construction. Event kind and the missing guard remain separate.

## Three pairwise explanations

One representative from each cluster gives these queries:

```lisp
{{#include ../examples/21-dogwood-larger.egg:larger-queries}}
```

The measured results are:

| pair | size | `:cr` | marked alternatives |
| --- | ---: | ---: | --- |
| A, B | 14 | 0.0769 | `response` / `request` |
| A, C | 15 | 0.2308 | `pathDeploy` / `(Lit true)` |
| B, C | 16 | 0.3077 | both pairs above |

The identity in the second row means that cluster C omitted one conjunct. It
does not mean that `pathDeploy` and true are equal.

## Deduplicating recurring decisions

Reading each query independently would present four marker occurrences across
the table. Grouping the same position and alternatives produces two review
items:

| review item | cluster pairs | what settles it |
| --- | --- | --- |
| request versus response event | A/B and B/C | the Dogwood event schema |
| require `/deploy` versus omit the path guard | A/C and B/C | the requirement and a policy-owner review |

Semper does not compute this aggregate table. The fixture executes all three
queries, and the reader groups repeated alternative pairs by their position in
the shared skeleton. Chapter 19's speculative scope can test either resolution;
this chapter only reduces the repeated outputs to the distinct decisions.
