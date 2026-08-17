#!/usr/bin/env python3
"""Process-level timing harness for the full egglog comparison set.

Generalizes run-pilot.py from three benchmarks to the whole translated set. Each
benchmark declares the type groups its translation needs and which of the two
encodings exist for it, because not every benchmark has a native-AC dual: see the
per-benchmark deviation ledgers.

Every row carries a `label`, and the output file is named after it, so that a
cheap smoke pass cannot be mistaken for the campaign. The campaign is
`--label final` at one pinned commit, per methodology.md section 6.

Usage:
    python3 run-full.py                                  # 2 warmups + 10 runs
    python3 run-full.py --label smoke --runs 1 --warmups 0
    python3 run-full.py --benchmark calc --benchmark until
    python3 run-full.py --ours PATH --egglog PATH
"""

import argparse
import csv
import json
import os
import re
import statistics
import subprocess
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))

# types: the --types groups our binary needs for this translation.
# encodings: which of our two encodings ship for this benchmark.
BENCHMARKS = {
    "eqsat-basic":         {"types": "machine",        "encodings": ("rules", "native")},
    "math-add-ac":         {"types": "machine",        "encodings": ("rules", "native")},
    "math-microbenchmark": {"types": "machine",        "encodings": ("rules", "native")},
    "calc":                {"types": "machine",        "encodings": ("rules", "native")},
    "until":               {"types": "machine",        "encodings": ("rules", "native")},
    "integer_math":        {"types": "machine",        "encodings": ("rules", "native")},
    "matrix":              {"types": "machine",        "encodings": ("rules", "native")},
    "bdd":                 {"types": "machine",        "encodings": ("rules", "native")},
    # herbie's and eqsolve's native-AC duals are not written; see their ledgers.
    "herbie":              {"types": "machine,bignum", "encodings": ("rules",)},
    "eqsolve":             {"types": "machine",        "encodings": ("rules",)},
}


def configs(benchmark, ours, egglog):
    """(config name, argv, stats file, stats flavour) for each configuration."""
    spec = BENCHMARKS[benchmark]
    yield (
        "egglog",
        [egglog, "-j", "1", "--mode", "no-messages", f"{benchmark}.egglog.egg"],
        f"{benchmark}.egglog.stats.json",
        "egglog",
    )
    for enc in spec["encodings"]:
        for strat, flag in (("naive", []), ("semi", ["--use-semi-naive"])):
            yield (
                f"ours-{enc}-{strat}",
                [ours, f"{benchmark}.{enc}.egg", "--types", spec["types"]] + flag,
                f"{benchmark}.{enc}.stats.json",
                "ours",
            )


def timed(argv):
    t0 = time.perf_counter()
    p = subprocess.run(argv, cwd=HERE, stdout=subprocess.DEVNULL,
                       stderr=subprocess.DEVNULL)
    ms = (time.perf_counter() - t0) * 1000.0
    if p.returncode != 0:
        sys.exit(f"FAILED (exit {p.returncode}): {' '.join(argv)}")
    return ms


def read_stats(path, flavour):
    """nodes, classes, iterations from the engine's stats file (None when absent)."""
    full = os.path.join(HERE, path)
    if not os.path.exists(full):
        return (None, None, None)
    with open(full) as fh:
        d = json.load(fh)
    if flavour == "ours":
        return (d["nodes"], d["classes"], d["iterations"])
    # egglog's RunReport: one entry per iteration, no node or class totals.
    return (None, None, len(d.get("iterations", [])))


def egglog_nodes(egglog, benchmark):
    """Total node count from egglog's own (print-size), summed over functions.

    Not comparable with ours: they print post-rebuild table cardinality, we count
    stored nodes plus one per interned literal (methodology.md section 3).
    """
    p = subprocess.run([egglog, "-j", "1", f"{benchmark}.egglog.egg"], cwd=HERE,
                       stdout=subprocess.PIPE, stderr=subprocess.DEVNULL, text=True)
    total = 0
    for line in p.stdout.splitlines():
        m = re.match(r"^\s*\(?\(([A-Za-z_][A-Za-z0-9_]*) (\d+)\)\)?\s*$", line)
        if m:
            total += int(m.group(2))
    return total or None


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--runs", type=int, default=10)
    ap.add_argument("--warmups", type=int, default=2)
    ap.add_argument("--label", default="full",
                    help="names the output file and tags every row; use 'final' "
                         "only for the pinned-commit campaign")
    ap.add_argument("--ours",
                    default=os.path.join(HERE, "..", "target", "release",
                                         "semi-persistent"))
    ap.add_argument("--egglog", default="/tmp/egglog/target/release/egglog")
    ap.add_argument("--benchmark", action="append", choices=sorted(BENCHMARKS),
                    help="restrict to one benchmark; repeatable, defaults to all")
    args = ap.parse_args()

    ours = os.path.abspath(args.ours)
    rows = []
    for b in (args.benchmark or list(BENCHMARKS)):
        for name, argv, stats_path, flavour in configs(b, ours, args.egglog):
            for _ in range(args.warmups):
                timed(argv)
            walls = [timed(argv) for _ in range(args.runs)]
            nodes, classes, iters = read_stats(stats_path, flavour)
            if flavour == "egglog":
                nodes = egglog_nodes(args.egglog, b)
            for i, ms in enumerate(walls, 1):
                rows.append({
                    "label": args.label, "benchmark": b, "config": name, "run": i,
                    "wall_ms": f"{ms:.3f}",
                    "nodes": nodes if nodes is not None else "",
                    "classes": classes if classes is not None else "",
                    "iterations": iters if iters is not None else "",
                })
            print(f"{b:22s} {name:20s} median {statistics.median(walls):9.1f} ms  "
                  f"nodes {nodes}  classes {classes}  iters {iters}", flush=True)

    out = os.path.join(HERE, f"{args.label}-results.csv")
    with open(out, "w", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=["label", "benchmark", "config", "run",
                                           "wall_ms", "nodes", "classes", "iterations"])
        w.writeheader()
        w.writerows(rows)
    print(f"\nwrote {out}")


if __name__ == "__main__":
    main()
