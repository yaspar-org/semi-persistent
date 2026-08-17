#!/usr/bin/env python3
"""Measure the index build's span-table term, and gate the prototypes on the corpus.

Two jobs, one script, because they read the same binaries:

  --corpus    run every comparison program on each binary and compare the
              stdout and the stats tuple (nodes, classes, iterations,
              match_steps) against the first binary. Wall time is dropped: it is
              the thing being changed. A binary that fails this is not measuring
              the same computation and its timings mean nothing. --extra passes
              an engine flag through, so one invocation covers a scheduling
              mode; repeat the run per mode.

  --phases    run a program under EGRAPH_PHASE=1 (requires a binary built with
              --features phase-timing) and print the per-round phase split:
              index build against matching, and inside the index build, the walk
              that writes each family's stream against the container build that
              turns it into a span table.

  --wall      time a program end to end on each binary, minimum of N runs, which
              is the number that decides whether a cheaper build is a cheaper
              round (a sort-based span table moves cost from the build onto
              every probe).

Binaries are given as name=path pairs, e.g.

    python3 run-span-table.py --corpus \\
        --bin base=/tmp/sp-base --bin reuse=/tmp/sp-reuse

Build them with, from the workspace root:

    cargo build --release -p semi-persistent-egraph --bin semi-persistent \\
        --features phase-timing

Following comparison/methodology.md section 2 for the wall-clock numbers, with
the same registered divergence run-semipersistence.py takes: the reported
statistic is the minimum of the timed runs, not the median.
"""

import argparse
import json
import os
import re
import shutil
import subprocess
import tempfile
import time

HERE = os.path.dirname(os.path.abspath(__file__))
SP = os.path.join(HERE, "semi-persistence")

# The comparison corpus, both encodings, plus the E6 programs that exercise
# push/pop and the delta index. `--types machine` matches how the pilot and the
# E6 runner invoke them.
CORPUS = sorted(
    [os.path.join(HERE, f) for f in os.listdir(HERE) if f.endswith((".native.egg", ".rules.egg"))]
) + [
    os.path.join(SP, f"sp-t{t}.{v}.native.egg")
    for t in (880, 8900)
    for v in ("base", "cycles", "norun")
]

# Stats fields that must not move. `wall_time_ms` is excluded on purpose.
INVARIANT = ("nodes", "classes", "iterations", "match_steps", "saturated", "goal_met")


def run(binary, prog, extra=(), env=None, cwd=None):
    cmd = [binary, prog, "--types", "machine", *extra]
    e = dict(os.environ)
    if env:
        e.update(env)
    t0 = time.perf_counter()
    r = subprocess.run(cmd, capture_output=True, cwd=cwd, env=e)
    dt = (time.perf_counter() - t0) * 1000.0
    if r.returncode != 0:
        raise SystemExit(f"FAILED {' '.join(cmd)}\n{r.stdout.decode()[-3000:]}\n{r.stderr.decode()[-3000:]}")
    return r.stdout.decode(), r.stderr.decode(), dt


def fingerprint(binary, prog, semi, extra=()):
    """stdout plus the run-invariant stats fields, for every stats file written."""
    with tempfile.TemporaryDirectory() as d:
        # `(print-stats :file ...)` writes relative to the working directory, so
        # each run gets its own; the program itself is read by absolute path.
        flags = (("--use-semi-naive",) if semi else ()) + tuple(extra)
        out, _, _ = run(binary, prog, extra=flags, cwd=d)
        stats = {}
        for f in sorted(os.listdir(d)):
            if f.endswith(".json"):
                with open(os.path.join(d, f)) as fh:
                    s = json.load(fh)
                stats[f] = {k: s[k] for k in INVARIANT if k in s}
    return out, stats


def cmd_corpus(args, bins):
    ref_name, ref_bin = bins[0]
    bad = 0
    for prog in CORPUS:
        for semi in (False, True) if args.semi else (False,):
            tag = os.path.basename(prog) + (" [semi]" if semi else "")
            if args.extra:
                tag += " " + " ".join(args.extra)
            ref = fingerprint(ref_bin, prog, semi, args.extra)
            row = []
            for name, b in bins[1:]:
                got = fingerprint(b, prog, semi, args.extra)
                ok = got == ref
                bad += not ok
                row.append(f"{name}={'ok' if ok else 'DIFF'}")
                if not ok and args.verbose:
                    print(f"  ref   {ref[1]}")
                    print(f"  {name:5s} {got[1]}")
                    if got[0] != ref[0]:
                        print("  stdout differs")
            print(f"{tag:44s} {ref_name}=ref " + " ".join(row))
    print("\nCORPUS " + ("IDENTICAL" if bad == 0 else f"{bad} MISMATCHES"))
    return bad


PHASE_LINE = re.compile(r"^(\s*\S+)\s+([\d.]+)\s+(\d+)\s+([\d.]+)$")


def cmd_phases(args, bins):
    for name, b in bins:
        print(f"\n=== {name}: {os.path.basename(args.prog)}"
              + (" [semi]" if args.semi else "") + " ===")
        _, err, wall = run(
            b,
            args.prog,
            extra=(("--use-semi-naive",) if args.semi else ()),
            env={"EGRAPH_PHASE": args.detail},
        )
        print(err.strip())
        print(f"(process wall {wall:.1f} ms)")


def cmd_wall(args, bins):
    print(f"{'program':44s}" + "".join(f"{n:>14s}" for n, _ in bins))
    for prog in ([args.prog] if args.prog else CORPUS):
        cells = []
        for _, b in bins:
            extra = ("--use-semi-naive",) if args.semi else ()
            for _ in range(args.warmups):
                run(b, prog, extra=extra)
            cells.append(min(run(b, prog, extra=extra)[2] for _ in range(args.runs)))
        base = cells[0]
        print(
            f"{os.path.basename(prog):44s}"
            + "".join(f"{c:10.1f}{'':4s}" if i == 0 else f"{c:10.1f}{c / base:+5.2f}"
                      for i, c in enumerate(cells))
        )


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--bin", action="append", default=[], metavar="NAME=PATH")
    ap.add_argument("--corpus", action="store_true")
    ap.add_argument("--phases", action="store_true")
    ap.add_argument("--wall", action="store_true")
    ap.add_argument("--prog")
    ap.add_argument("--semi", action="store_true", help="run with --use-semi-naive")
    ap.add_argument("--detail", default="1", help="EGRAPH_PHASE value: 1 (totals) or rounds")
    ap.add_argument("--runs", type=int, default=3)
    ap.add_argument("--warmups", type=int, default=1)
    ap.add_argument("--verbose", action="store_true")
    ap.add_argument(
        "--extra",
        action="append",
        default=[],
        metavar="FLAG",
        help="extra engine flag, repeatable; e.g. --extra --runtime-scheduling",
    )
    args = ap.parse_args()

    bins = []
    for spec in args.bin:
        name, _, path = spec.partition("=")
        path = path or name
        if not shutil.which(path) and not os.path.exists(path):
            raise SystemExit(f"no such binary: {path}")
        bins.append((name, path))
    if not bins:
        raise SystemExit("at least one --bin NAME=PATH")

    if args.corpus:
        cmd_corpus(args, bins)
    if args.phases:
        if not args.prog:
            raise SystemExit("--phases needs --prog")
        cmd_phases(args, bins)
    if args.wall:
        cmd_wall(args, bins)


if __name__ == "__main__":
    main()
