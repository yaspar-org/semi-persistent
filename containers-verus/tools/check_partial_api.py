#!/usr/bin/env python3
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0
"""Gate: the public surface of containers-verus carries no partial function.

Two checks over src/*.rs:

1. Every public exec fn whose signature carries a `requires` clause must be
   named in the allowlist (partial-api-allowlist.txt). Verus erases `requires`
   at runtime, so a public partial function hands an unverified caller
   whatever the body does on violated preconditions. The allowlist is the
   drain list for the total-API plan (doc/future/total-api-plan.md); it may
   only shrink.
2. No public fn body may contain `unsafe` or `get_unchecked` — those live
   only in the enumerated pub(crate) external_body primitives.

"Public" = `pub` without a restriction (`pub(crate)`, `pub(super)`,
`pub(in ...)` are internal), plus any fn declared inside a `pub trait` block
(trait items inherit the trait's visibility). spec/proof fns are skipped:
spec fns are uncallable from exec code and proof fns are erased.

Line-oriented grep cannot do this — multi-line signatures and `==> { ... }`
groups inside ensures clauses defeat it (measured: 8 hits vs the ~130 real
ones). This parser brace/paren-matches instead.

Usage:
  check_partial_api.py <src-dir> <allowlist>            # gate (exit 1 on new)
  check_partial_api.py <src-dir> <allowlist> --update   # rewrite the allowlist
"""
import re
import sys
from pathlib import Path

FN_RE = re.compile(r'\bfn\s+([A-Za-z_][A-Za-z0-9_]*)')


def strip_comments_and_strings(text: str) -> str:
    """Blank out comments and string literals, preserving offsets/newlines."""
    out = []
    i, n = 0, len(text)
    while i < n:
        two = text[i:i + 2]
        if two == '//':
            j = text.find('\n', i)
            j = n if j == -1 else j
            out.append(' ' * (j - i))
            i = j
        elif two == '/*':
            j = text.find('*/', i + 2)
            j = n if j == -1 else j + 2
            out.append(''.join(c if c == '\n' else ' ' for c in text[i:j]))
            i = j
        elif text[i] == '"':
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == '\\' else 1
            j = min(j + 1, n)
            out.append('"' + ' ' * (j - i - 2) + '"' if j - i >= 2 else '"')
            i = j
        else:
            out.append(text[i])
            i += 1
    return ''.join(out)


def pub_trait_spans(text: str):
    """Byte ranges of `pub trait ... { ... }` bodies (fns inside are public)."""
    spans = []
    for m in re.finditer(r'\bpub\s+trait\b[^{;]*{', text):
        depth, i = 1, m.end()
        while i < len(text) and depth:
            depth += {'{': 1, '}': -1}.get(text[i], 0)
            i += 1
        spans.append((m.end(), i))
    return spans


def scan_file(path: Path):
    """Yield (name, line, has_requires, body_has_unsafe, public) per exec fn."""
    raw = path.read_text()
    text = strip_comments_and_strings(raw)
    trait_spans = pub_trait_spans(text)
    for m in FN_RE.finditer(text):
        start = m.start()
        # Modifiers on the line(s) before `fn`: look back to the previous
        # item boundary for visibility and spec/proof markers.
        lb = max(text.rfind(';', 0, start), text.rfind('}', 0, start),
                 text.rfind('{', 0, start))
        prefix = text[lb + 1:start]
        if re.search(r'\b(spec|proof)\s*(\(\s*checked\s*\))?\s*$|\bspec\b|\bproof\b', prefix):
            continue
        in_pub_trait = any(a <= start < b for a, b in trait_spans)
        vis = bool(re.search(r'\bpub\s*$|\bpub\s+(?:const\s+)?$', prefix)) or \
            bool(re.search(r'\bpub\s+(?:const\s+)?fn\s*$', text[lb + 1:m.end()][:-len(m.group(1))]))
        restricted = bool(re.search(r'\bpub\s*\(', prefix))
        public = (vis and not restricted) or (in_pub_trait and 'pub(' not in prefix)
        if not public:
            continue
        # Signature region: from after the arg list to the body '{' or ';',
        # treating `==> {` groups (spec groups in ensures) as nested.
        i = text.find('(', m.end())
        if i == -1:
            continue
        depth = 1
        i += 1
        while i < len(text) and depth:
            depth += {'(': 1, ')': -1}.get(text[i], 0)
            i += 1
        sig_start, depth = i, 0
        has_req = False
        while i < len(text):
            c = text[i]
            if c == '{':
                if depth == 0 and not text[:i].rstrip().endswith('==>'):
                    break
                depth += 1
            elif c == '}':
                depth -= 1
            elif c in '()':
                depth += 1 if c == '(' else -1
            elif c == ';' and depth == 0:
                break
            i += 1
        sig = text[sig_start:i]
        has_req = bool(re.search(r'\brequires\b', sig))
        if has_req:
            # wf-only requires are the type's self-invariant, upheld by every
            # constructor and mutator - a caller cannot violate them without
            # already holding a corrupted value. Not a partial function in
            # the caller-obligation sense (audit class (a)).
            rm = re.search(r'\brequires\b(.*?)(?=\bensures\b|\brecommends\b|$)', sig, re.S)
            clause = rm.group(1) if rm else ''
            residue = re.sub(r'(old\(self\)|self)\s*\.\s*wf\s*\(\s*\)', '', clause)
            residue = re.sub(r'[\s,]+', '', residue)
            if residue == '':
                has_req = False
        # Body scan for check 2 (only when a body exists).
        body_unsafe = False
        if i < len(text) and text[i] == '{':
            depth, j = 1, i + 1
            while j < len(text) and depth:
                depth += {'{': 1, '}': -1}.get(text[j], 0)
                j += 1
            body = text[i:j]
            body_unsafe = bool(re.search(r'\bunsafe\b|\bget_unchecked\b', body))
        line = raw[:start].count('\n') + 1
        yield (f'{path.name}::{m.group(1)}', line, has_req, body_unsafe)


def main():
    src = Path(sys.argv[1])
    allow_path = Path(sys.argv[2])
    update = '--update' in sys.argv
    partial, unsafe_pub = [], []
    for f in sorted(src.glob('*.rs')):
        for name, line, has_req, body_unsafe in scan_file(f):
            if has_req:
                partial.append((name, line))
            if body_unsafe:
                unsafe_pub.append((name, line))
    if update:
        allow_path.write_text(
            '# Public exec fns with a `requires` clause: the total-API plan\'s\n'
            '# drain list (doc/future/total-api-plan.md). May only shrink.\n'
            + ''.join(f'{n}\n' for n in sorted({n for n, _ in partial})))
        print(f'allowlist rewritten: {len(partial)} entries')
        return 0
    allowed = {l.strip() for l in allow_path.read_text().splitlines()
               if l.strip() and not l.startswith('#')}
    have = {n for n, _ in partial}
    new = sorted(have - allowed)
    drained = sorted(allowed - have)
    rc = 0
    if new:
        print(f'ERROR: {len(new)} public partial fn(s) not in the allowlist '
              f'({allow_path.name}). A new public fn must be total — see '
              'doc/future/total-api-plan.md. Offenders:')
        for n in new:
            print(f'  {n}')
        rc = 1
    if unsafe_pub:
        print(f'ERROR: {len(unsafe_pub)} public fn(s) contain unsafe/get_unchecked:')
        for n, l in unsafe_pub:
            print(f'  {n} (line {l})')
        rc = 1
    if drained:
        print(f'NOTE: {len(drained)} allowlist entr(ies) no longer partial — '
              'remove them (the list may only shrink):')
        for n in drained:
            print(f'  {n}')
    print(f'partial-api gate: {len(have)} public partial fns, '
          f'{len(allowed)} allowed, {len(new)} new, {len(unsafe_pub)} unsafe-public')
    return rc


if __name__ == '__main__':
    sys.exit(main())
