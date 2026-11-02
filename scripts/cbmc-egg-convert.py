#!/usr/bin/env python3
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0
"""Convert CBMC egg-format e-graph dumps into Semper programs.

Each dump holds two e-graphs, `base` (ebase_*) and `cong` (econg_*). Their leaves share
names (`leaf_5` in both), so loading both into one Semper program would hash-cons them
together; each becomes its own program, NAME.base.egg and NAME.cong.egg.

Encoding (one sort, `Term`):
- `leaf_N` with comment `const V` (hexadecimal) -> `(Const V N)`: the value is kept for
  rules, the leaf id keeps constants of different types apart (the dump has no widths).
- `leaf_N` with comment `const NULL`             -> `(Null N)`.
- any other `leaf_N` (SSA symbol, nondet, or an operator CBMC kept opaque) -> `(Leaf N)`.
- `type_N`                                         -> `(Type N)`.
- plus, mult, bitand, bitor, bitxor: `:assoc-comm` (associative and commutative on
  bit-vectors); equal: `:comm`; minus, neg, bitnot, typecast: positional.
- `(let eX expr)` and `(union eA eB)` keep their names; children are let-bound globals.
The comment of every let is kept, and the roles ([ASSUME], [ASSERT]) are collected.

The output is the corpus in egraph/tests/egg/cbmc/ (see its README).

Usage: cbmc-egg-convert.py DUMP_DIR OUT_DIR
"""

import json
import os
import re
import sys

LET = re.compile(r"^\(let (e(?:base|cong)_\d+) (.*?)\)\s*(?:;;\s*(.*))?$")
UNION = re.compile(r"^\(union (e(?:base|cong)_\d+) (e(?:base|cong)_\d+)\)")
ATOM = re.compile(r"^(leaf|type)_(\d+)$")
APP = re.compile(r"^\((\w+)((?: e(?:base|cong)_\d+)+)\)$")

OPS = {
    "plus": "Plus", "mult": "Mult", "bitand": "BitAnd", "bitor": "BitOr",
    "bitxor": "BitXor", "equal": "Equal", "minus": "Minus", "neg": "Neg",
    "bitnot": "BitNot", "typecast": "Typecast",
}

PRELUDE = """\
;; Converted from the CBMC e-graph dump {dump} by scripts/cbmc-egg-convert.py.
;; Source: cbmc-egg-dumps.tar.gz, provided by Michael Tautschnig; see egraph/tests/egg/cbmc/README.md.
(sort Term)
(function Leaf (IBig) Term)
(function Const (IBig IBig) Term)   ; value, leaf id
(function Null (IBig) Term)
(function Type (IBig) Term)
(function Plus (Term) Term :assoc-comm)
(function Mult (Term) Term :assoc-comm)
(function BitAnd (Term) Term :assoc-comm-idem)
(function BitOr (Term) Term :assoc-comm-idem)
(function BitXor (Term) Term :assoc-comm)
(function Equal (Term Term) Term :comm)
(function Minus (Term Term) Term)
(function Neg (Term) Term)
(function BitNot (Term) Term)
(function Typecast (Term Term) Term)
"""


def leaf(kind, n, comment):
    if kind == "type":
        return f"(Type {n})"
    first = comment.split(";;")[0].strip() if comment else ""
    if first == "const NULL":
        return f"(Null {n})"
    m = re.match(r"^const ([0-9A-Fa-f]+)$", first)
    if m:
        return f"(Const {int(m.group(1), 16)} {n})"
    return f"(Leaf {n})"


def convert(path):
    graphs = {"base": [], "cong": []}
    meta = {"base": {"roles": {}, "lets": 0, "unions": 0, "skipped": []},
            "cong": {"roles": {}, "lets": 0, "unions": 0, "skipped": []}}
    with open(path, encoding="utf-8") as fh:
        for no, line in enumerate(fh, 1):
            line = line.rstrip("\n")
            m = LET.match(line)
            if m:
                name, expr, comment = m.group(1), m.group(2).strip(), (m.group(3) or "")
                g = "base" if name.startswith("ebase") else "cong"
                a = ATOM.match(expr)
                if a:
                    term = leaf(a.group(1), a.group(2), comment)
                else:
                    ap = APP.match(expr)
                    if not ap or ap.group(1) not in OPS:
                        meta[g]["skipped"].append((no, line))
                        continue
                    term = f"({OPS[ap.group(1)]}{ap.group(2)})"
                for role in re.findall(r"\[([A-Z_]+)\]", comment):
                    meta[g]["roles"].setdefault(role, []).append(name)
                note = f"  ; {comment}" if comment else ""
                graphs[g].append(f"(let {name} {term}){note}")
                meta[g]["lets"] += 1
                continue
            u = UNION.match(line)
            if u:
                g = "base" if u.group(1).startswith("ebase") else "cong"
                graphs[g].append(f"(union {u.group(1)} {u.group(2)})")
                meta[g]["unions"] += 1
    return graphs, meta


def main():
    src, out = sys.argv[1], sys.argv[2]
    os.makedirs(out, exist_ok=True)
    report = {}
    for f in sorted(os.listdir(src)):
        if not f.endswith(".egg"):
            continue
        graphs, meta = convert(os.path.join(src, f))
        stem = f[:-4]
        for g in ("base", "cong"):
            with open(os.path.join(out, f"{stem}.{g}.egg"), "w", encoding="utf-8") as fh:
                fh.write(PRELUDE.replace("{dump}", f) + "\n" + "\n".join(graphs[g]) + "\n")
            report[f"{stem}.{g}"] = {
                "lets": meta[g]["lets"], "unions": meta[g]["unions"],
                "roles": {k: len(v) for k, v in meta[g]["roles"].items()},
                "skipped": meta[g]["skipped"][:5], "skipped_count": len(meta[g]["skipped"]),
            }
    with open(os.path.join(out, "manifest.json"), "w") as fh:
        json.dump(report, fh, indent=1, sort_keys=True)
        fh.write("\n")
    bad = {k: v for k, v in report.items() if v["skipped_count"]}
    print(f"{len(report)} programs; {len(bad)} with skipped lines")
    for k, v in list(bad.items())[:10]:
        print(k, v["skipped_count"], v["skipped"][:2])


if __name__ == "__main__":
    main()
