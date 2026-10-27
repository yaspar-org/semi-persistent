#!/usr/bin/env python3
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0
"""Rewrite `prove` to `check-eq` and `check-neq`.

`prove` was the build-and-compare check; it is renamed (doc: the command reference):

    (prove (= a b))    ->  (check-eq a b)
    (prove (!= a b))   ->  (check-neq a b)
    (prove ...)        ->  (check-eq ...)     in prose that elides the arguments

A `(prove t)` of one term builds `t` and tests nothing; the script does not guess its
replacement and lists it for review (the bare term, when `t` is an application).

The rewrite reads the s-expression: it finds the `(=` or `(!=` group by matching
parentheses, so its arguments may span lines and nest. A `(prove` right after an
identifier character is a call, not a command, and is left alone (a `\\n` escape
before it, in a Rust or Python string, is a program line). Double-quoted strings in
`.egg` files are skipped while matching.

Not rewritten: CHANGELOG.md, whose past entries name `prove` as it was;
scripts/migrate-check.py, the earlier migration; this script.

A one-time migration: run it once. It prints each changed file with its count, and
every `(prove` it left unchanged, for review.

Usage: migrate-prove.py [--dry-run]
"""

import re
import subprocess
import sys

EXCLUDE = {"CHANGELOG.md", "scripts/migrate-check.py", "scripts/migrate-prove.py"}
EXTS = (".egg", ".rs", ".md", ".py")
START = re.compile(r"(?:(?<![A-Za-z0-9_.])|(?<=\\n))\(prove(?=[\s(])")


def match_close(text, i, egg):
    """Index of the parenthesis closing the one at `i`, or None."""
    depth = 0
    j = i
    while j < len(text):
        c = text[j]
        if egg and c == '"':
            j += 1
            while j < len(text) and text[j] != '"':
                j += 2 if text[j] == "\\" else 1
        elif c == "(":
            depth += 1
        elif c == ")":
            depth -= 1
            if depth == 0:
                return j
        j += 1
    return None


def rewrite(text, egg):
    out, i, n, left = [], 0, 0, []
    for m in START.finditer(text):
        if m.start() < i:
            continue
        j = m.end()
        k = j
        while k < len(text) and text[k] in " \t\r\n":
            k += 1
        elided = re.match(r"(\.\.\.|…)\)", text[k:])
        if elided:
            out.append(text[i:m.start()] + "(check-eq")
            i = j
            n += 1
            continue
        inner = re.match(r"\(\s*(!=|=)(?=\s)", text[k:])
        if not inner:
            left.append(m.start())
            continue
        close_inner = match_close(text, k, egg)
        if close_inner is None:
            left.append(m.start())
            continue
        t = close_inner + 1
        while t < len(text) and text[t] in " \t\r\n":
            t += 1
        if t >= len(text) or text[t] != ")":
            left.append(m.start())
            continue
        name = "check-neq" if inner.group(1) == "!=" else "check-eq"
        args = text[k + inner.end():close_inner]
        out.append(text[i:m.start()] + "(" + name + args + text[close_inner + 1:t] + ")")
        i = t + 1
        n += 1
    out.append(text[i:])
    return "".join(out), n, left


def main():
    dry = "--dry-run" in sys.argv
    files = subprocess.run(["git", "ls-files"], capture_output=True, text=True, check=True).stdout.split()
    total = 0
    left_all = []
    for path in files:
        if not path.endswith(EXTS) or path in EXCLUDE:
            continue
        with open(path, encoding="utf-8") as fh:
            text = fh.read()
        new, n, left = rewrite(text, path.endswith(".egg"))
        for pos in left:
            line = text.count("\n", 0, pos) + 1
            left_all.append(f"{path}:{line}: {text.splitlines()[line - 1].strip()[:100]}")
        if n:
            total += n
            print(f"{path}: {n}")
            if not dry:
                with open(path, "w", encoding="utf-8") as fh:
                    fh.write(new)
    print(f"\n{total} prove -> check-eq / check-neq")
    print(f"{len(left_all)} occurrences of (prove left unchanged:")
    for item in left_all:
        print("  " + item)


if __name__ == "__main__":
    main()
