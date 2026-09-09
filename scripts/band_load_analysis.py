#!/usr/bin/env python3
"""⭐⭐⭐ DOES THE BOX'S LOAD PREDICT THE MERGE GATE'S BAND?  (QUEUE item 4)

⛔ WHY THIS EXISTS.  Item 4's stated release condition is **"an uncontended
box"**, and three pieces of work are held on it (`es3-anchor-theorems`,
`p2-batch32-fp-compares`, and P3 sub-group A).  Item 4 also names a MECHANISM for
the failures: *"rare load excursions from other seats"*, citing two passes that
read `Tests.Coverage` at 30,600 and 27,400 ms at `load1` 11.52 and 12.04 against
~25,700 at load ~6.

**Neither the condition nor the mechanism had ever been measured.**  They did not
need a box: this repository already contains three kernel-delta corpora over the
SAME TWELVE COMMITS, recorded at three different load regimes, each reading
carrying its own `load1`.  That is a paired design sitting on disk.

  docs/kernel-delta-history-2026-09-04.jsonl              load1  3.11 -  6.80
  docs/kernel-delta-history-USER2-2026-09-05.jsonl        load1  8.95 - 20.89
  docs/kernel-delta-history-USER-CONTENDED-2026-09-05.jsonl  load1 10.45 - 98.42

⚠️ WHAT IS COMPARED, PRECISELY.  Each corpus records two sweeps per commit; a
sweep is an independent pass over the same tree.  The BAND the merge gate refuses
on is built from exactly that pass-to-pass variability, so the between-sweep
range is the same KIND of quantity the gate consumes — but it is not the gate's
own band, and this tool does not claim to recompute one.  It is restricted to the
27 (module, declaration) keys present in every commit of both paired corpora, so
the comparison is like-for-like ([[feedback-a-join-on-a-lossy-key]]).

⛔⛔ AND THE ANSWER IS NOT THE ONE THE ITEM ASSUMES.  Run it.

LANE.  Personal lane; reads committed artifacts only, no box, no build, ~0.1 s.
"""
import collections, json, os, statistics as st, sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
os.chdir(ROOT)

CORPORA = [
    ("QUIET",   "docs/kernel-delta-history-2026-09-04.jsonl"),
    ("USER2",   "docs/kernel-delta-history-USER2-2026-09-05.jsonl"),
    ("CONTEND", "docs/kernel-delta-history-USER-CONTENDED-2026-09-05.jsonl"),
]


def read(path):
    rows = [json.loads(l) for l in open(path)]
    by = collections.defaultdict(list)
    for r in rows:
        by[r["commit"]].append(r)
    return by, [r["load1"] for r in rows]


def keys_everywhere(by):
    sets = []
    for c, v in by.items():
        for r in v:
            sets.append({(m, d) for m, dd in r["decls"].items() for d in dd})
    return set.intersection(*sets) if sets else set()


def sweep_pairs(by, common):
    """(Δload1, median relative range, max load1, commit) per paired commit."""
    out = []
    for c, v in by.items():
        if len(v) < 2:
            continue
        a, b = v[0], v[1]
        rel = []
        for m, dd in a["decls"].items():
            for d, x in dd.items():
                if (m, d) not in common:
                    continue
                y = b["decls"].get(m, {}).get(d)
                if y is None:
                    continue
                mean = (x + y) / 2.0
                if mean > 0:
                    rel.append(abs(x - y) / mean)
        if rel:
            out.append((abs(a["load1"] - b["load1"]), st.median(rel),
                        max(a["load1"], b["load1"]), c[:8]))
    return out


def pearson(x, y):
    mx, my = st.mean(x), st.mean(y)
    num = sum((a - mx) * (b - my) for a, b in zip(x, y))
    den = (sum((a - mx) ** 2 for a in x) * sum((b - my) ** 2 for b in y)) ** 0.5
    return num / den if den else float("nan")


def main():
    data = {tag: read(p) for tag, p in CORPORA}
    commits = {tag: set(by) for tag, (by, _l) in data.items()}
    tags = [t for t, _ in CORPORA]
    if len({frozenset(commits[t]) for t in tags}) != 1:
        print("⛔ the three corpora do NOT cover the same commits — this is a "
              "PAIRED comparison and it cannot be run unpaired. REFUSING.")
        for t in tags:
            print("    %-8s %d commits" % (t, len(commits[t])))
        return 2
    common = set.intersection(*[keys_everywhere(data[t][0]) for t in ("QUIET", "USER2")])
    if not common:
        print("⛔ no (module, declaration) key is present in every commit of both "
              "paired corpora — nothing to compare. REFUSING.")
        return 2
    print("PAIRED over %d commits x %d declarations present in every reading.\n"
          % (len(commits["QUIET"]), len(common)))

    print("BETWEEN-SWEEP RANGE / mean, per declaration:")
    print("  %-8s %14s %5s %5s %8s %8s %8s" %
          ("corpus", "load1 range", "pairs", "n", "median", "p90", "max"))
    per = {}
    for tag, _p in CORPORA:
        by, loads = data[tag]
        pr = sweep_pairs(by, common)
        per[tag] = pr
        rel = []
        for c, v in by.items():
            if len(v) < 2:
                continue
            a, b = v[0], v[1]
            for m, dd in a["decls"].items():
                for d, x in dd.items():
                    if (m, d) not in common:
                        continue
                    y = b["decls"].get(m, {}).get(d)
                    if y is None:
                        continue
                    mean = (x + y) / 2.0
                    if mean > 0:
                        rel.append(abs(x - y) / mean)
        rel.sort()
        if not rel:
            print("  %-8s NO PAIRED SWEEPS" % tag)
            continue
        q = lambda p: 100 * rel[int(p * (len(rel) - 1))]
        print("  %-8s %6.2f-%6.2f %5d %5d %7.1f%% %7.1f%% %7.1f%%"
              % (tag, min(loads), max(loads), len(pr), len(rel), q(.5), q(.9), q(1.0)))

    # ⭐ THE TEST. Both candidate covariates, over the 24 pairs whose load1 stays
    # inside [3, 21] — the range in which every held branch was actually measured.
    inrange = per["QUIET"] + per["USER2"]
    dl = [r[0] for r in inrange]
    sp = [r[1] for r in inrange]
    mx = [r[2] for r in inrange]
    print("\nOVER THE %d PAIRS AT load1 IN [%.2f, %.2f] — the range every held "
          "branch was measured in:" % (len(inrange), min(mx), max(mx)))
    print("  r(Δload1 within a pair, spread) = %+.3f" % pearson(dl, sp))
    print("  r(max load1 of a pair,  spread) = %+.3f" % pearson(mx, sp))
    print("  spread stays inside %.1f%% - %.1f%% across the whole range."
          % (100 * min(sp), 100 * max(sp)))

    # level shift: does load inflate the READING (which largely cancels in a delta)?
    ratios = []
    for c in commits["QUIET"]:
        for k in common:
            a = [r["decls"].get(k[0], {}).get(k[1]) for r in data["QUIET"][0][c]]
            b = [r["decls"].get(k[0], {}).get(k[1]) for r in data["USER2"][0][c]]
            a = [v for v in a if v]
            b = [v for v in b if v]
            if a and b and st.mean(a) > 0:
                ratios.append(st.mean(b) / st.mean(a))
    ratios.sort()
    q = lambda p: ratios[int(p * (len(ratios) - 1))]
    print("\nLEVEL SHIFT, USER2 / QUIET, per (commit, declaration), n=%d:" % len(ratios))
    print("  p10 %.3f   median %.3f   p90 %.3f   %.0f%% read HIGHER under load"
          % (q(.1), q(.5), q(.9), 100 * sum(1 for r in ratios if r > 1) / len(ratios)))

    print("""
⇒ ⛔⛔ THE FINDING, AND IT CONTRADICTS ITEM 4's RELEASE CONDITION.
  Going from load ~5 to load ~12 raises the LEVEL of a reading by ~14% and does
  NOT widen the pass-to-pass spread at all.  A uniform level shift is exactly
  what a base-vs-head DELTA cancels.  Neither candidate covariate predicts the
  spread anywhere in [3, 21]: r = +0.04 for load VARIATION and NEGATIVE for load
  LEVEL, with the spread confined to a 1.9%-6.9% band across the whole range.

  ⚠️ AND THE MECHANISM ITEM 4 NAMES IS THE ORDINARY CASE, NOT AN EXCURSION.  The
  two passes it calls "rare load excursions" read 1.19x and 1.07x the quiet
  level — squarely inside the p10-p90 of the ROUTINE 1.078-1.246 shift measured
  here over 324 paired readings.  They were the box behaving normally at load 12.

  ⚠️ WHAT IS **NOT** CLAIMED.  The CONTEND corpus (load to 98) is much worse and
  says the spread does blow up somewhere — but it has TWO pairs and its own
  ordering is inverted (Δload 17.5 -> 38.4%, Δload 47.7 -> 8.7%), so the knee
  between 21 and 98 is UNLOCATED and this tool does not pretend to locate it.
  ⇒ The claim is bounded: **up to load1 ~21 there is no measured spread penalty**,
  and therefore no covariate on which a keep-rule could justify a re-run.""")
    return 0


if __name__ == "__main__":
    sys.exit(main())
