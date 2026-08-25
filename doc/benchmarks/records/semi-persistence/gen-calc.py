#!/usr/bin/env python3
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0
"""Cut calc.{egglog,native}.egg into cumulative prefixes, one per push/pop block.

Process-level wall clock cannot time a block inside a program, so block k is
timed as the difference between the program truncated after block k and the one
truncated after block k-1. Writes calc-p0.<engine>.egg (the prefix before the
first push) through calc-p4.<engine>.egg (the whole program).
"""

import os

HERE = os.path.dirname(os.path.abspath(__file__))


def cut(path, out_prefix):
    lines = open(path).read().splitlines(keepends=True)
    ends = [i for i, l in enumerate(lines) if l.strip() == "(pop)"]
    starts = [i for i, l in enumerate(lines) if l.strip() == "(push)"]
    assert len(ends) == len(starts) == 4, (path, len(starts), len(ends))
    # p0 stops before the first push; pk includes blocks 1..k and everything
    # between them (block 3's prefix declares aConst/bConst).
    bounds = [starts[0]] + [e + 1 for e in ends]
    for k, b in enumerate(bounds):
        with open(f"{out_prefix}-p{k}.egg", "w") as fh:
            fh.write("".join(lines[:b]))


def main():
    cut(os.path.join(HERE, "calc.egglog.egg"), os.path.join(HERE, "calc.egglog"))
    cut(os.path.join(HERE, "calc.native.egg"), os.path.join(HERE, "calc.native"))
    print("wrote calc.{egglog,native}-p0..p4.egg")


if __name__ == "__main__":
    main()
