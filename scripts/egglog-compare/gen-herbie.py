#!/usr/bin/env python3
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0
"""Generate the herbie benchmark's three configurations from egglog's original.

Source: <egglog>/tests/web-demo/herbie.egg at 7b1adf2.

The original carries an interval analysis (`hi`/`lo`, two `:merge` lattice
functions) and a `non-zero` relation derived from it. Neither is in the
intersection set: we have no lattice functions and no datalog relations, and
`:when` on our side takes patterns only, so a relation guard has nothing to
compile to. The analysis is therefore stripped from *all three* configurations,
along with the rewrites it gates and the two test blocks whose goals are
reachable only through them, so that the three programs are the same problem.

Five constant-folding rewrites go too: they need `pow`, `log`, `ceil`, `floor`
and `round` on rationals, which our RBig primitive set does not have (it has
+ - * / neg abs min max and the comparisons). Two of the five are additionally
guarded by primitive definedness (`:when ((= res (pow a b)))`), which is a
partiality test we cannot express either.

Writes herbie.egglog.egg, herbie.rules.egg and the dropped-form listing that
herbie.deviations.md cites. See that ledger for the counted consequence.
"""

import re
import os
import sys
from collections import Counter
from pathlib import Path

SRC = Path(sys.argv[1] if len(sys.argv) > 1 else os.path.expanduser("~/tools/egglog/tests/web-demo/herbie.egg"))
OUT = Path(__file__).resolve().parent


def top_level_forms(src):
    """Split into top-level s-expressions, keeping preceding comments attached."""
    forms, buf, depth, instr, i = [], "", 0, False, 0
    while i < len(src):
        c = src[i]
        if instr:
            buf += c
            if c == '"':
                instr = False
            i += 1
            continue
        if c == ";":
            j = src.find("\n", i)
            j = len(src) if j < 0 else j
            buf += src[i:j + 1]
            i = j + 1
            continue
        if c == '"':
            instr = True
            buf += c
            i += 1
            continue
        if c == "(":
            depth += 1
        if c == ")":
            depth -= 1
        buf += c
        i += 1
        if depth == 0 and buf.strip() and c == ")":
            forms.append(buf)
            buf = ""
    if buf.strip():
        forms.append(buf)
    return forms


def strip_analysis(forms):
    """Drop the interval/non-zero analysis and the five unavailable-primitive folds."""
    kept, dropped = [], []
    for f in forms:
        body = re.sub(r";[^\n]*", "", f)
        if re.search(r"\(function (hi|lo) ", body) or re.search(r"\(relation non-zero", body):
            dropped.append(("lattice-decl", f))
        elif re.search(r"\bnon-zero\b", body):
            dropped.append(("non-zero-gated", f))
        elif re.search(r"\((lo|hi) ", body):
            dropped.append(("lattice-rule", f))
        elif re.search(r"\((pow|log|ceil|floor|round) ", body):
            dropped.append(("missing-primitive", f))
        else:
            kept.append(f)
    return kept, dropped


def drop_block(text, marker):
    """Remove the (push) … (pop) test block whose body contains `marker`."""
    i = text.find(marker)
    if i < 0:
        raise SystemExit(f"block marker {marker!r} not found")
    start = text.rfind("(push)", 0, i)
    end = text.find("(pop)", i) + len("(pop)")
    return text[:start] + text[end:]


# ── translation to our surface language ───────────────────────────────────────

def to_ours(text, stats_file, header):
    t = text
    # BigRat literals: (bigrat (bigint N) (bigint D)) -> N/D
    t = re.sub(r"\(bigrat\s*\(bigint\s*(-?\d+)\s*\)\s*\(bigint\s*(-?\d+)\s*\)\s*\)", r"\1/\2", t)
    # the BigRat sort itself
    t = re.sub(r"\bBigRat\b", "RBig", t)
    # bare primitive applications over rationals -> sort-qualified
    t = re.sub(r"\((\+|\-|\*|/)\s", lambda m: f"(RBig::{m.group(1)} ", t)
    t = re.sub(r"\((neg|abs)\s", lambda m: f"(RBig::{m.group(1)} ", t)
    # identifiers outside our lexical class: $r-zero -> rzero, $neg-one -> negone
    t = re.sub(r"\$([A-Za-z0-9_-]+)", lambda m: m.group(1).replace("-", ""), t)
    t = f"{header}\n{t.lstrip()}"
    t = t.rstrip() + f'\n(print-size)\n(print-stats :file "{stats_file}")\n'
    return t


def main():
    forms = top_level_forms(SRC.read_text())
    kept, dropped = strip_analysis(forms)
    text = "".join(kept)
    # $e10 = (Div (Mul x 3) x): provable only via the non-zero-gated Div rules.
    # $e14: needs the `pow` constant fold, which our RBig set lacks.
    text = drop_block(text, "$e10")
    text = drop_block(text, "$sqrt5")

    counts = Counter(k for k, _ in dropped)
    orig = re.sub(r";[^\n]*", "", SRC.read_text())
    cur = re.sub(r";[^\n]*", "", text)
    summary = {
        "rewrites": (len(re.findall(r"\(rewrite\s", orig)), len(re.findall(r"\(rewrite\s", cur))),
        "rules": (len(re.findall(r"\(rule\s", orig)), len(re.findall(r"\(rule\s", cur))),
        "blocks": (len(re.findall(r"\(push\)", orig)), len(re.findall(r"\(push\)", cur))),
        "checks": (len(re.findall(r"\(check\s", orig)), len(re.findall(r"\(check\s", cur))),
    }

    egglog_header = (
        ";; herbie, scoped to the intersection set. Generated by gen-herbie.py from\n"
        ";; egglog tests/web-demo/herbie.egg at 7b1adf2; see herbie.deviations.md.\n"
        ";; The interval lattice, the non-zero relation, the rewrites they gate and the\n"
        ";; five folds needing rational pow/log/ceil/floor/round are removed here too, so\n"
        ";; that all three configurations run the same problem."
    )
    egglog = f"{egglog_header}\n{text.lstrip()}".rstrip()
    egglog += '\n(print-size)\n(print-stats)\n(print-stats :file "herbie.egglog.stats.json")\n'
    (OUT / "herbie.egglog.egg").write_text(egglog)

    rules_header = (
        ";; TYPES: machine,bignum\n"
        ";; Translation of egglog tests/web-demo/herbie.egg (7b1adf2), scoped.\n"
        ";; Config: A/C supplied as explicit rewrite rules, their encoding.\n"
        ";; Generated by gen-herbie.py. See herbie.deviations.md.\n"
        ";; Renamings: BigRat -> RBig, (bigrat (bigint N) (bigint D)) -> N/D, bare rational\n"
        ";; operators sort-qualified to RBig::, and $x -> x with hyphens removed."
    )
    (OUT / "herbie.rules.egg").write_text(to_ours(text, "herbie.rules.stats.json", rules_header))

    (OUT / "herbie-dropped.txt").write_text(
        "Forms removed from egglog's herbie.egg by gen-herbie.py.\n"
        + "\n".join(f"\n=== [{k}]\n{v.strip()}" for k, v in dropped)
        + "\n\n=== [test-block] $e10 (Div (Mul x 3) x) = 3 — needs the non-zero-gated Div rules\n"
        + "=== [test-block] $e14 — needs the `pow` constant fold\n"
    )

    print("dropped forms:", dict(counts))
    for k, (a, b) in summary.items():
        print(f"{k}: {a} -> {b}")


if __name__ == "__main__":
    main()
