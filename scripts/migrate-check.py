#!/usr/bin/env python3
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0
"""Rewrite build-and-compare checks to `prove`, and ground run goals to `:goal`.

`check` takes egglog's query semantics and `:until` egglog's query goal; the semantics
both have today move to `prove` and `:goal` (doc: the command reference). This script
rewrites every program text in the repository so that it keeps its meaning:

- in `.egg` files, every `(check` that opens a command (followed by space or `(`);
- elsewhere (`.rs`, `.md`, `.py`), `(check` followed by `(`, by a format placeholder
  `{`, by `...)` or `…)`, or by a single identifier and `)`. That covers programs
  embedded in Rust strings and the commands quoted in documents, and leaves prose such
  as "(check 2)" alone;
- `:until` followed by `(`, in every file.

`(checkau` and `(check-` are other commands and stay, and so does `(check` right after
an identifier, a call such as `exit(check(...))`. Not rewritten:
`scripts/egglog-compare/`, whose programs are egglog's and move to the new `check`;
`egraph/tests/check_semantics.rs`, which tests both forms; this script.

A one-time migration: it was run once, before `check` took egglog's semantics, and a
second run then changed nothing. Since then `(check` in the tree is egglog's check, so
the script must not be run again. It prints each changed file with its counts, and every
`(check` it left unchanged outside the excluded paths, for review.

Usage: migrate-check.py [--dry-run]
"""

import re
import subprocess
import sys

EXCLUDE_PREFIX = ("scripts/egglog-compare/",)
EXCLUDE_FILES = {"egraph/tests/check_semantics.rs", "scripts/migrate-check.py"}
EXTS = (".egg", ".rs", ".md", ".py")

EGG_CHECK = re.compile(r"\(check(?=[\s(])")
# Not after an identifier character: `f(check(x))` is a call. `\n(check` in a Rust or
# Python string is a program line, so a backslash escape counts as a boundary.
TEXT_CHECK = re.compile(
    r"(?:(?<![A-Za-z0-9_.])|(?<=\\n))\(check(?=\s*[({]|\s*(?:\.\.\.|…)\)| +[A-Za-z_][A-Za-z0-9_-]*\))"
)
UNTIL = re.compile(r":until(?=\s*\()")
ANY_CHECK = re.compile(r"\(check(?![\w-])")


def main():
    dry = "--dry-run" in sys.argv
    files = subprocess.run(["git", "ls-files"], capture_output=True, text=True, check=True).stdout.split()
    total_c = total_u = 0
    left = []
    for path in files:
        if not path.endswith(EXTS) or path.startswith(EXCLUDE_PREFIX) or path in EXCLUDE_FILES:
            continue
        with open(path, encoding="utf-8") as fh:
            text = fh.read()
        pat = EGG_CHECK if path.endswith(".egg") else TEXT_CHECK
        new, nc = pat.subn("(prove", text)
        new, nu = UNTIL.subn(":goal", new)
        for m in ANY_CHECK.finditer(new):
            line = new.count("\n", 0, m.start()) + 1
            src = new.splitlines()[line - 1].strip()
            left.append(f"{path}:{line}: {src[:100]}")
        if nc or nu:
            total_c += nc
            total_u += nu
            print(f"{path}: {nc} check, {nu} :until")
            if not dry:
                with open(path, "w", encoding="utf-8") as fh:
                    fh.write(new)
    print(f"\n{total_c} check -> prove, {total_u} :until -> :goal")
    print(f"{len(left)} occurrences of (check left unchanged:")
    for item in left:
        print("  " + item)


if __name__ == "__main__":
    main()
