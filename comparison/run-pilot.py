#!/usr/bin/env python3
"""Process-level timing harness for the egglog comparison pilot.

Runs every (benchmark, config) pair 2 warmups + 10 timed runs, records wall time per
run, and collects node/class/iteration counts from the engines' own machine-readable
statistics.  Writes pilot-results.csv next to this script.

Usage:
    python3 run-pilot.py [--runs 10] [--warmups 2]
        [--ours PATH] [--egglog PATH] [--benchmark NAME]

Defaults assume the two release binaries at ../target/release/semi-persistent and
/tmp/egglog/target/release/egglog.
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

BENCHMARKS = ["eqsat-basic", "math-add-ac", "math-microbenchmark"]


def configs(ours, egglog):
    """(config name, argv, stats-file, stats-flavour) for each configuration."""
    def rows(b):
        yield (
            "egglog",
            [egglog, "-j", "1", "--mode", "no-messages", f"{b}.egglog.egg"],
            f"{b}.egglog.stats.json",
            "egglog",
        )
        for enc in ("rules", "native"):
            for strat, flag in (("naive", []), ("semi", ["--use-semi-naive"])):
                yield (
                    f"ours-{enc}-{strat}",
                    [ours, f"{b}.{enc}.egg", "--types", "machine"] + flag,
                    f"{b}.{enc}.stats.json",
                    "ours",
                )
    return rows


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
    """Total node count from egglog's own (print-size), summed over functions."""
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
    ap.add_argument("--ours",
                    default=os.path.join(HERE, "..", "target", "release",
                                         "semi-persistent"))
    ap.add_argument("--egglog", default="/tmp/egglog/target/release/egglog")
    ap.add_argument("--benchmark", action="append", choices=BENCHMARKS,
                    help="restrict to one benchmark; repeatable, defaults to all")
    args = ap.parse_args()

    rows = []
    summary = {}
    make = configs(os.path.abspath(args.ours), args.egglog)
    for b in (args.benchmark or BENCHMARKS):
        for name, argv, stats_path, flavour in make(b):
            for _ in range(args.warmups):
                timed(argv)
            walls = [timed(argv) for _ in range(args.runs)]
            nodes, classes, iters = read_stats(stats_path, flavour)
            if flavour == "egglog":
                nodes = egglog_nodes(args.egglog, b)
            for i, ms in enumerate(walls, 1):
                rows.append({
                    "benchmark": b, "config": name, "run": i,
                    "wall_ms": f"{ms:.3f}", "nodes": nodes if nodes is not None else "",
                    "classes": classes if classes is not None else "",
                    "iterations": iters if iters is not None else "",
                })
            summary[(b, name)] = (statistics.median(walls), nodes, classes, iters)
            print(f"{b:22s} {name:20s} median {statistics.median(walls):9.1f} ms  "
                  f"nodes {nodes}  classes {classes}  iters {iters}", flush=True)

    out = os.path.join(HERE, "pilot-results.csv")
    with open(out, "w", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=["benchmark", "config", "run", "wall_ms",
                                           "nodes", "classes", "iterations"])
        w.writeheader()
        w.writerows(rows)
    print(f"\nwrote {out}")


if __name__ == "__main__":
    main()
