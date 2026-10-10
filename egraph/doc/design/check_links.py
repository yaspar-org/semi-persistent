#!/usr/bin/env python3
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0
"""Check relative markdown links and anchors in the design folder.

Every relative link must resolve to an existing file, and every `#anchor`
must match a heading slug in its target (GitHub-style slugs). Links into the
ltl-eqsat `doc/` tree are checked against `doc-draft/` during the draft
review; the link text itself is not rewritten.

Usage: python3 check_links.py [-v]
"""

import os
import re
import sys
import unicodedata

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.abspath(os.path.join(HERE, "../../../.."))  # ltl-eqsat root
DOC = os.path.join(REPO, "doc")
DOC_DRAFT = os.path.join(REPO, "doc-draft")

FENCE = re.compile(r"^\s*(```|~~~)")
INLINE_CODE = re.compile(r"`+[^`]*`+")
LINK = re.compile(r"!?\[(?:[^\[\]]|\[[^\]]*\])*\]\(\s*<?([^)\s>]+)>?(?:\s+\"[^\"]*\")?\s*\)")
REFDEF = re.compile(r"^\s{0,3}\[[^\]]+\]:\s*<?(\S+?)>?(?:\s+.*)?$")
HEADING = re.compile(r"^\s{0,3}(#{1,6})\s+(.*?)\s*#*\s*$")
HTML_ANCHOR = re.compile(r"<a\s+(?:name|id)=\"([^\"]+)\"")


def slugify(text):
    text = re.sub(r"!?\[([^\]]*)\]\([^)]*\)", r"\1", text)  # link text only
    text = re.sub(r"<[^>]+>", "", text)  # inline html
    text = text.strip().lower()
    out = []
    for ch in text:
        cat = unicodedata.category(ch)
        if ch in "-_" or cat[0] in "LMN":
            out.append(ch)
        elif ch == " ":
            out.append("-")
    return "".join(out)


def lines_outside_code(path):
    in_fence = False
    with open(path, encoding="utf-8") as fh:
        for no, line in enumerate(fh, 1):
            if FENCE.match(line):
                in_fence = not in_fence
                continue
            if not in_fence:
                yield no, line.rstrip("\n")


_anchor_cache = {}


def anchors(path):
    if path not in _anchor_cache:
        seen = {}
        result = set()
        for _, line in lines_outside_code(path):
            for m in HTML_ANCHOR.finditer(line):
                result.add(m.group(1))
            m = HEADING.match(line)
            if not m:
                continue
            base = slugify(m.group(2))
            n = seen.get(base, 0)
            seen[base] = n + 1
            result.add(base if n == 0 else f"{base}-{n}")
        _anchor_cache[path] = result
    return _anchor_cache[path]


def resolve(src, target):
    path = os.path.normpath(os.path.join(os.path.dirname(src), target))
    if path == DOC or path.startswith(DOC + os.sep):
        path = DOC_DRAFT + path[len(DOC):]
    return path


def check(verbose=False):
    checked = 0
    broken = []
    for name in sorted(os.listdir(HERE)):
        if not name.endswith(".md"):
            continue
        src = os.path.join(HERE, name)
        kept = dict(lines_outside_code(src))
        with open(src, encoding="utf-8") as fh:
            total = sum(1 for _ in fh)
        # Code-block lines become blank so offsets map back to line numbers;
        # joining lines lets link text span a line break.
        text = "\n".join(INLINE_CODE.sub("", kept.get(no, "")) for no in range(1, total + 1))
        found = [(m.start(), m.group(1)) for m in LINK.finditer(text)]
        offset = 0
        for line in text.split("\n"):
            m = REFDEF.match(line)
            if m:
                found.append((offset, m.group(1)))
            offset += len(line) + 1
        for pos, target in sorted(found):
            no = text.count("\n", 0, pos) + 1
            if re.match(r"^[a-z][a-z0-9+.-]*:", target, re.I):
                continue  # absolute URL (http, mailto, ...)
            checked += 1
            file_part, _, anchor = target.partition("#")
            dest = resolve(src, file_part) if file_part else src
            if not os.path.exists(dest):
                broken.append((name, no, target, "missing file"))
                continue
            if anchor and dest.endswith(".md") and anchor not in anchors(dest):
                broken.append((name, no, target, "missing anchor"))
            elif verbose:
                print(f"ok   {name}:{no}: {target}")
    for name, no, target, why in broken:
        print(f"{name}:{no}: {why}: {target}")
    print(f"checked {checked} links, {len(broken)} broken")
    return 1 if broken else 0


if __name__ == "__main__":
    sys.exit(check("-v" in sys.argv[1:]))
