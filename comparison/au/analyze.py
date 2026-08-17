#!/usr/bin/env python3
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0
"""Tables for the AU anytime/regret corpus (plan item B3).

Reads the CSV written by `egraph/tests/au_corpus_bench.rs::anytime_corpus`
(one row per instance x playout budget) and prints the four tables the
analysis doc records:

  a) simple regret (relative size gap) against the playout budget, with the
     zero mass reported separately from the mean among nonzero gaps;
  b) the same against wall clock normalized by the exact solver's time;
  c) certification fraction against the budget, and the knee prediction
     (certification at about sum A(v) playouts) tested per sum A(v) decade;
  d) time to optimum against exact's completion time.

Usage: analyze.py [corpus.csv] [--hard-ms 10] [--family FAMILY]
"""

import argparse
import collections
import csv
import math
import statistics
import sys


def load(path):
    rows = []
    with open(path, newline="") as f:
        for r in csv.DictReader(f):
            r["playouts"] = int(r["playouts"])
            r["exact_ms"] = float(r["exact_ms"])
            r["mcgs_ms"] = float(r["mcgs_ms"])
            r["exact_size"] = int(r["exact_size"])
            r["mcgs_size"] = int(r["mcgs_size"])
            r["exact_vmass"] = int(r["exact_vmass"])
            r["mcgs_vmass"] = int(r["mcgs_vmass"])
            r["certified"] = r["certified"] == "true"
            r["sum_a"] = int(r["sum_a"]) if r["sum_a"] else None
            r["or_states"] = int(r["or_states"]) if r["or_states"] else None
            r["sum_a_capped"] = r["sum_a_capped"] == "true"
            r["gap"] = (r["mcgs_size"] - r["exact_size"]) / r["exact_size"]
            rows.append(r)
    return rows


def quantile(xs, q):
    if not xs:
        return float("nan")
    xs = sorted(xs)
    if len(xs) == 1:
        return xs[0]
    pos = q * (len(xs) - 1)
    lo = math.floor(pos)
    hi = math.ceil(pos)
    return xs[lo] + (xs[hi] - xs[lo]) * (pos - lo)


def mean(xs):
    return statistics.fmean(xs) if xs else float("nan")


def by_instance(rows):
    out = collections.OrderedDict()
    for r in rows:
        out.setdefault(r["instance"], []).append(r)
    return out


def table_corpus(rows):
    inst = by_instance(rows)
    print("## Corpus")
    print()
    print(f"{len(inst)} instances, {len(rows)} rows.")
    print()
    print(f"{'family':>8} {'instances':>10} {'rows':>7} {'exact_ms p50':>13} "
          f"{'exact_ms p90':>13} {'>=10 ms':>8} {'median sum_A':>13}")
    fams = collections.OrderedDict()
    for name, rs in inst.items():
        fams.setdefault(rs[0]["family"], []).append(rs)
    for fam, groups in fams.items():
        es = [g[0]["exact_ms"] for g in groups]
        sa = [g[0]["sum_a"] for g in groups if g[0]["sum_a"] is not None]
        print(f"{fam:>8} {len(groups):>10} {sum(len(g) for g in groups):>7} "
              f"{quantile(es, 0.5):>13.2f} {quantile(es, 0.9):>13.2f} "
              f"{sum(1 for e in es if e >= 10.0):>8} "
              f"{quantile(sa, 0.5) if sa else float('nan'):>13.0f}")
    es = [g[0]["exact_ms"] for g in inst.values()]
    print(f"{'ALL':>8} {len(inst):>10} {len(rows):>7} {quantile(es, 0.5):>13.2f} "
          f"{quantile(es, 0.9):>13.2f} {sum(1 for e in es if e >= 10.0):>8}")
    print()


def table_regret(rows, label):
    print(f"## (a) Simple regret against the playout budget{label}")
    print()
    print(f"{'playouts':>9} {'n':>5} {'zero_frac':>10} {'mean_gap':>9} "
          f"{'median':>7} {'p90':>7} {'mean_gap>0':>11} {'max':>7}")
    budgets = sorted({r["playouts"] for r in rows})
    for b in budgets:
        at = [r for r in rows if r["playouts"] == b]
        gaps = [r["gap"] for r in at]
        nz = [g for g in gaps if g > 0]
        print(f"{b:>9} {len(at):>5} {1 - len(nz) / len(gaps):>10.3f} "
              f"{mean(gaps):>9.4f} {quantile(gaps, 0.5):>7.4f} "
              f"{quantile(gaps, 0.9):>7.4f} "
              f"{(mean(nz) if nz else 0.0):>11.4f} {max(gaps):>7.4f}")
    print()


def table_regret_by_family(rows):
    print("## (a2) Zero-gap fraction by family and budget")
    print()
    fams = sorted({r["family"] for r in rows})
    budgets = sorted({r["playouts"] for r in rows})
    print(f"{'playouts':>9} " + " ".join(f"{f:>9}" for f in fams))
    for b in budgets:
        cells = []
        for f in fams:
            at = [r for r in rows if r["playouts"] == b and r["family"] == f]
            cells.append(f"{sum(1 for r in at if r['gap'] == 0) / len(at):>9.3f}"
                         if at else f"{'-':>9}")
        print(f"{b:>9} " + " ".join(cells))
    print()


def table_wallclock(rows, hard_ms):
    """Gap against wall clock, normalized by the exact solver's time.

    For each instance and each time fraction, take the best (lowest-size)
    MCGS answer whose own wall time is within that fraction of exact's, which
    is what an anytime user gets by spending that much of the exact budget.
    """
    print(f"## (b) Regret against wall clock, on instances with exact >= {hard_ms} ms")
    print()
    inst = {k: v for k, v in by_instance(rows).items()
            if v[0]["exact_ms"] >= hard_ms}
    print(f"{len(inst)} instances.")
    print()
    cheapest = [min(r["mcgs_ms"] for r in rs) / rs[0]["exact_ms"]
                for rs in inst.values()]
    if cheapest:
        print(f"Cheapest MCGS run as a fraction of exact: p10 "
              f"{quantile(cheapest, 0.1):.4f}, p50 {quantile(cheapest, 0.5):.4f}, "
              f"p90 {quantile(cheapest, 0.9):.4f}.")
        print()
    fractions = [0.001, 0.01, 0.05, 0.1, 0.25, 0.5, 1.0]
    print(f"{'budget %':>9} {'n':>5} {'reached':>8} {'zero_frac':>10} "
          f"{'mean_gap':>9} {'p90':>7}")
    for frac in fractions:
        gaps = []
        reached = 0
        for rs in inst.values():
            budget_ms = rs[0]["exact_ms"] * frac
            within = [r for r in rs if r["mcgs_ms"] <= budget_ms]
            if not within:
                continue
            reached += 1
            gaps.append(min(r["gap"] for r in within))
        if not gaps:
            print(f"{frac * 100:>8.1f}% {len(inst):>5} {0:>8} {'-':>10} {'-':>9} {'-':>7}")
            continue
        zero = sum(1 for g in gaps if g == 0)
        print(f"{frac * 100:>8.1f}% {len(inst):>5} {reached:>8} "
              f"{zero / len(gaps):>10.3f} {mean(gaps):>9.4f} "
              f"{quantile(gaps, 0.9):>7.4f}")
    print()


def table_certification(rows):
    print("## (c) Certification against the playout budget")
    print()
    budgets = sorted({r["playouts"] for r in rows})
    print(f"{'playouts':>9} {'n':>5} {'certified':>10}")
    for b in budgets:
        at = [r for r in rows if r["playouts"] == b]
        print(f"{b:>9} {len(at):>5} "
              f"{sum(1 for r in at if r['certified']) / len(at):>10.3f}")
    print()
    print("### Knee against sum A(v)")
    print()
    print("Observed knee = the lowest ladder budget carrying Completion::Exact.")
    print("Predicted knee = sum A(v), the total action count of the search graph.")
    print()
    inst = by_instance(rows)
    capped = sum(1 for rs in inst.values() if rs[0]["sum_a_capped"])
    if capped:
        print(f"{capped} instances hit the census cap and are excluded: their "
              f"sum A(v) is a lower bound.")
        print()
    buckets = collections.OrderedDict()
    for name, rs in inst.items():
        sa = rs[0]["sum_a"]
        if sa is None or sa == 0 or rs[0]["sum_a_capped"]:
            continue
        decade = int(math.floor(math.log10(sa)))
        cert = [r["playouts"] for r in rs if r["certified"]]
        top = max(r["playouts"] for r in rs)
        buckets.setdefault(decade, []).append(
            (sa, min(cert) if cert else None, top, rs[0]["family"]))
    print(f"{'sum_A decade':>13} {'n':>5} {'certified':>10} {'median sum_A':>13} "
          f"{'median knee':>12} {'knee/sum_A p50':>15} {'ladder top < sum_A':>19}")
    for decade in sorted(buckets):
        entries = buckets[decade]
        got = [(sa, knee) for sa, knee, _, _ in entries if knee is not None]
        ratios = [knee / sa for sa, knee in got]
        unreachable = sum(1 for sa, _, top, _ in entries if top < sa)
        print(f"{'1e' + str(decade):>13} {len(entries):>5} "
              f"{len(got) / len(entries):>10.3f} "
              f"{quantile([e[0] for e in entries], 0.5):>13.0f} "
              f"{(quantile([k for _, k in got], 0.5) if got else float('nan')):>12.0f} "
              f"{(quantile(ratios, 0.5) if ratios else float('nan')):>15.2f} "
              f"{unreachable:>19}")
    print()


def table_knee_by_family(rows):
    print("### Knee against sum A(v), by family")
    print()
    inst = by_instance(rows)
    fams = collections.OrderedDict()
    for name, rs in inst.items():
        if rs[0]["sum_a"] is None or rs[0]["sum_a_capped"]:
            continue
        fams.setdefault(rs[0]["family"], []).append(rs)
    print(f"{'family':>8} {'certified':>10} {'median sum_A':>13} {'median knee':>12} "
          f"{'knee/sum_A p50':>15}")
    for fam, groups in fams.items():
        got = []
        for rs in groups:
            cert = [r["playouts"] for r in rs if r["certified"]]
            if cert:
                got.append((rs[0]["sum_a"], min(cert)))
        if not got:
            print(f"{fam:>8} {0:>10} {'-':>13} {'-':>12} {'-':>15}")
            continue
        print(f"{fam:>8} {len(got):>10} "
              f"{quantile([a for a, _ in got], 0.5):>13.0f} "
              f"{quantile([k for _, k in got], 0.5):>12.0f} "
              f"{quantile([k / a for a, k in got], 0.5):>15.2f}")
    print()


def table_knee_by_depth(rows):
    """Knee against sum A(v) by burial depth, on the families that carry one."""
    inst = by_instance(rows)
    buckets = collections.OrderedDict()
    for name, rs in inst.items():
        if rs[0]["family"] != "dec" or rs[0]["sum_a_capped"]:
            continue
        field = [p for p in rs[0]["params"].split(";") if p.startswith("d_b=")]
        if not field:
            continue
        depth = int(field[0].split("=")[1])
        cert = [r["playouts"] for r in rs if r["certified"]]
        buckets.setdefault(depth, []).append(
            (rs[0]["sum_a"], min(cert) if cert else None))
    if not buckets:
        return
    print("### Knee against burial depth, deceptive family")
    print()
    print(f"{'burial depth':>13} {'n':>5} {'certified':>10} {'median sum_A':>13} "
          f"{'median knee':>12} {'knee/sum_A p50':>15}")
    for depth in sorted(buckets):
        entries = buckets[depth]
        got = [(sa, k) for sa, k in entries if k is not None]
        print(f"{depth:>13} {len(entries):>5} {len(got) / len(entries):>10.3f} "
              f"{quantile([sa for sa, _ in entries], 0.5):>13.0f} "
              f"{(quantile([k for _, k in got], 0.5) if got else float('nan')):>12.0f} "
              f"{(quantile([k / sa for sa, k in got], 0.5) if got else float('nan')):>15.2f}")
    print()


def table_playouts_to_zero(rows):
    """Lowest budget at which MCGS reaches the optimum, by family, and for the
    deceptive family by burial depth and decoy count: the mechanism behind the
    knee, since a node behind a misranked action is reached only after UCT has
    spent enough budget on the arm that looks worse."""
    inst = by_instance(rows)
    print("## Playouts to gap zero")
    print()
    fams = collections.OrderedDict()
    for name, rs in inst.items():
        fams.setdefault(rs[0]["family"], []).append(rs)
    print(f"{'family':>8} {'n':>5} {'reaches 0':>10} {'p50':>8} {'p90':>8} {'max':>8}")
    for fam, groups in fams.items():
        got = []
        for rs in groups:
            zero = [r["playouts"] for r in rs if r["gap"] == 0]
            if zero:
                got.append(min(zero))
        if not got:
            print(f"{fam:>8} {len(groups):>5} {0.0:>10.3f} {'-':>8} {'-':>8} {'-':>8}")
            continue
        print(f"{fam:>8} {len(groups):>5} {len(got) / len(groups):>10.3f} "
              f"{quantile(got, 0.5):>8.0f} {quantile(got, 0.9):>8.0f} {max(got):>8}")
    print()

    buckets = collections.OrderedDict()
    for name, rs in inst.items():
        if rs[0]["family"] != "dec":
            continue
        p = dict(kv.split("=") for kv in rs[0]["params"].split(";"))
        zero = [r["playouts"] for r in rs if r["gap"] == 0]
        buckets.setdefault((int(p["d_b"]), int(p["k"])), []).append(
            min(zero) if zero else None)
    if not buckets:
        return
    print("### Deceptive family, by burial depth and decoy count")
    print()
    print(f"{'burial depth':>13} {'decoys':>7} {'n':>4} {'reaches 0':>10} "
          f"{'median playouts':>16}")
    for key in sorted(buckets):
        e = buckets[key]
        got = [x for x in e if x is not None]
        print(f"{key[0]:>13} {key[1]:>7} {len(e):>4} {len(got) / len(e):>10.3f} "
              f"{(quantile(got, 0.5) if got else float('nan')):>16.0f}")
    print()


def table_ttt(rows):
    print("## (d) Time to optimum against exact's completion")
    print()
    inst = by_instance(rows)
    print(f"{'family':>8} {'n':>5} {'gap0 ever':>10} {'gap0 before exact':>18} "
          f"{'median ms ratio at gap0':>24}")
    fams = collections.OrderedDict()
    for name, rs in inst.items():
        fams.setdefault(rs[0]["family"], []).append(rs)
    fams["ALL"] = list(inst.values())
    for fam, groups in fams.items():
        ever = 0
        before = 0
        ratios = []
        for rs in groups:
            zero = [r for r in rs if r["gap"] == 0]
            if not zero:
                continue
            ever += 1
            first = min(zero, key=lambda r: r["playouts"])
            ratios.append(first["mcgs_ms"] / rs[0]["exact_ms"])
            if first["mcgs_ms"] < rs[0]["exact_ms"]:
                before += 1
        n = len(groups)
        print(f"{fam:>8} {n:>5} {ever / n:>10.3f} {before / n:>18.3f} "
              f"{(quantile(ratios, 0.5) if ratios else float('nan')):>24.4f}")
    print()


def table_greedy(rows):
    print("## Greedy (one playout) against the optimum")
    print()
    inst = by_instance(rows)
    fams = collections.OrderedDict()
    for name, rs in inst.items():
        fams.setdefault(rs[0]["family"], []).append(rs)
    fams["ALL"] = list(inst.values())
    print(f"{'family':>8} {'n':>5} {'greedy wrong':>13} {'mean gap':>9} {'max gap':>8}")
    for fam, groups in fams.items():
        gaps = []
        for rs in groups:
            one = [r for r in rs if r["playouts"] == 1]
            if one:
                gaps.append(one[0]["gap"])
        if not gaps:
            continue
        wrong = sum(1 for g in gaps if g > 0)
        print(f"{fam:>8} {len(gaps):>5} {wrong / len(gaps):>13.3f} "
              f"{mean(gaps):>9.4f} {max(gaps):>8.4f}")
    print()


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("csv", nargs="?", default="corpus.csv")
    ap.add_argument("--hard-ms", type=float, default=10.0)
    ap.add_argument("--family", default=None)
    args = ap.parse_args()

    rows = load(args.csv)
    if args.family:
        rows = [r for r in rows if r["family"] == args.family]
    if not rows:
        sys.exit("no rows")

    table_corpus(rows)
    table_greedy(rows)
    table_regret(rows, "")
    table_regret_by_family(rows)
    hard = [r for r in rows if r["exact_ms"] >= args.hard_ms]
    if hard:
        table_regret(hard, f", instances with exact >= {args.hard_ms} ms")
    table_wallclock(rows, args.hard_ms)
    table_certification(rows)
    table_knee_by_family(rows)
    table_knee_by_depth(rows)
    table_playouts_to_zero(rows)
    table_ttt(rows)


if __name__ == "__main__":
    main()
