# Repair by disagreement

Chapter 6 localized two bugs. This chapter does something stronger: it derives a
policy that is correct and that **neither candidate wrote**.

The setting is [Dogwood](https://github.com/dogwood-policy/dogwood), a runtime
verification language for AI agents. A Dogwood policy is a Cedar policy plus a
`when temporal { ... }` clause holding a metric first-order temporal logic
condition over the agent's event history. It has a real validator and a real
replay tool, which matters here: the two tools settle one of the two decisions
and demonstrably cannot settle the other.

The files are in
[`autoformalization/dogwood/`](https://github.com/yaspar-org/semi-persistent/tree/main/autoformalization/dogwood).

## The requirement

> The agent may POST to `/deploy`, but only if a health check has already come
> back 200 in the last 15 minutes.

## The two candidates

Candidate A gets the Cedar guard right and the event kind wrong:

```text
when { context.input.method == "POST" && context.input.path == "/deploy" }
when temporal {
    (count for (t: Timepoint). where (
        formerly within 15m (
            Strands::Action::"http:request"::request{      // wrong phase
                callerPrincipal: principal,
                output.status_code: 200
            }
            && tp(t)
        )
    )) >= 1
};
```

Candidate B gets the event kind right and drops a Cedar conjunct:

```text
when { "POST" == context.input.method }                    // no path guard
when temporal {
    1 <= (count for (t: Timepoint). where (
        formerly within 900s (
            tp(t)
            && Strands::Action::"http:request"::response{  // right phase
                 output.status_code: 200,
                 callerPrincipal:    principal
               }
        )
    ))
};
```

B's mistake is not cosmetic. With the path guard gone, any POST to any path is
permitted once a single 200 has been seen in the window, so the agent may POST
to `/admin/purge-all`.

They also differ in six places that carry no meaning, and each one is absorbed
by a specific declaration in the signature:

| difference | absorbed by |
| --- | --- |
| Cedar conjunct order | `eAnd :assoc-comm-idem` |
| temporal conjunct order | `tAnd :assoc-comm-idem` |
| predicate field order | `args :assoc-comm-idem` |
| `"POST" ==` versus `== "POST"` | `eEq :comm` |
| `>= 1` versus `1 <=` | a `birewrite` |
| `within 15m` versus `within 900s` | normalizing the window to seconds at encoding time |

Eight differences in total, six of them noise. Chapter 8 measures what happens
when each of those six absorptions is withheld.

## The query

```bash
target/release/semi-persistent autoformalization/dogwood/repair.egg
```

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
                (win 900)
                (tAnd
                  (tp (bvar 0))
                  (pred
                    aHttpRequest
                    (Variants request response)
                    (args
                      (arg (fld fCallerPrincipal fnil) scopePrincipal)
                      (arg (fld fOutput (fld fStatusCode fnil)) (tInt 200))))))))
          (tInt 1)))
      (Variants (eEq (eCtx (fld fInput (fld fPath fnil))) (eStr vDeploy)) eTrue))))
```

Exactly two `Variants` nodes, one per real mistake, and all six presentational
differences absorbed.

- **Decision 1**, the event kind: `request` or `response`. A one-word subterm.
- **Decision 2**, the path guard: A's `eEq` on `context.input.path`, or `eTrue`,
  the unit of `eAnd`. The dropped conjunct is reported as a decision because the
  unit gave it something to pair against.

## Four completions, and the repair is one of them

Two independent binary decisions give four ways to complete the skeleton. Two of
them are the input candidates. The other two were written by nobody.

| kind | guard | which policy | validator | replay of `POST /admin/purge-all` |
| --- | --- | --- | --- | --- |
| `request` | keep | candidate A | FAILED | not runnable |
| `request` | drop | neither candidate | FAILED | not runnable |
| `response` | drop | candidate B | OK | **allows** |
| `response` | keep | **the repair** | OK | denies |

The repair is `response` with the path guard kept: candidate B's temporal
condition and candidate A's Cedar guard. It is
[`strandsbox/repaired.dw`](https://github.com/yaspar-org/semi-persistent/blob/main/autoformalization/dogwood/strandsbox/repaired.dw),
and it is the only one of the four that both validates and enforces the
sentence.

This is why the method is worth more than localization alone. The two candidates
had one mistake each, in different places, so the correct answer was already
present in the pair; it just was not present in either member of the pair.
Anti-unification is what makes the recombination well defined: the skeleton is
shared, so a choice at each `Variants` node yields a whole term.

## Who decides each decision

The two decisions are not the same kind of question, and the difference is the
practical point.

**Decision 1 is settled mechanically, with no human involved.** The Dogwood
schema declares `status_code` as a response field. A `request` event does not
carry outputs, so `request{ output.status_code: 200 }` names a field that does
not exist on that event:

```text
error: predicate `Strands::Action::"http:request"::request` mentions field
`output.status_code`, which is not declared on that event (declared fields:
callerPrincipal, callerResource, input.host, input.method, input.path,
input.transport, requestId, sessionId)
```

Both `request` completions fail validation. Candidate A is eliminated by
`dogwood validate` before anybody reads it.

**Decision 2 is not settled by any tool.** Both spellings validate cleanly.
Whether the policy should mention `/deploy` is a fact about the English
sentence, and no amount of type checking recovers it. Replay makes the
consequence visible, on a trace of a 200 health check followed by
`POST /deploy` and then `POST /admin/purge-all`:

```text
--- candB ---
@60  (time point 0): ALLOW
@120 (time point 1): ALLOW      <- the off-target POST
--- repaired ---
@60  (time point 0): ALLOW
@120 (time point 1): DENY
```

So the reviewer's actual job on this policy is: answer one question, about a
seven-node subterm, with both candidate answers displayed next to each other.
Not "read a 60-node temporal formula".

## Reproducing it

```bash
target/release/semi-persistent autoformalization/dogwood/repair.egg
autoformalization/dogwood/validate.sh          # needs the dogwood CLI
python3 autoformalization/dogwood/ablate.py    # chapter 8
```

`validate.sh` shells out to the real `dogwood` binary for the validator and
replay output above; it is the one step in this book that depends on a tool
outside the repository. The anti-unification result does not.

There is also a self-contained interactive page,
`autoformalization/dogwood/repair.html`, built by `make_repair_page.py`, where
the two `Variants` nodes are clickable and the table above updates to name the
completion you selected. `check_repair.js` runs that page's own script under
Node so a broken picker fails a check rather than sitting in a browser console.
