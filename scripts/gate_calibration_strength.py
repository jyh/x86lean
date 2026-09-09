#!/usr/bin/env python3
"""HOW MUCH OF THE USABILITY GATE'S VERDICT IS THE BOUND'S OWN SAMPLING NOISE?

⚖️ **COMMISSIONED BY THE HELM, 2026-09-09 at council close.** Ruling (3) retired
D179 rule 4 as a discard criterion and left the usability gate governing alone.
The helm named the consequence in the same breath: *"the gate is calibrated at
n = 1 and knife-edge; strengthening that calibration is the next item."*

## THE PROBLEM, STATED EXACTLY

The gate is `MAX per-commit p95 <= B`, where **B is the quiet night's own
maximum**. So B is a single order statistic — the max of that night's twelve
per-commit p95 values. Deliberately no margin was invented, because deriving an
allowance from the thing being checked is how a gate stops being a gate
([[feedback-widening-a-gate-needs-a-second-source]]). The cost of that correct
choice is that **B carries the sampling variability of a maximum and nothing
records how large it is.**

⛔⛔ AND THE CAVEAT AS WRITTEN IS ITSELF AN OVER-BROAD CLAIM. Every site says
"the bound is n = 1 and knife-edge" about the gate AS A WHOLE. But the corpora
fail it at ratios spanning **1.10x to 3.89x**. A verdict at 3.89x survives any
plausible re-draw of B; a verdict at 1.10x may not survive a 10% one. ⇒ 🔑 **A
SINGLE CAVEAT ATTACHED TO A GATE IS A CLAIM ABOUT EVERY ROW IT JUDGES, AND THE
ROWS ARE NOT ALIKE.** [[feedback-a-category-is-a-hypothesis-about-its-members]]

## WHAT THIS TOOL DOES

Bootstraps B from the quiet night's OWN twelve per-commit p95 values (resample
with replacement, recompute the max), giving the interval B would have occupied
had that night's commits fallen differently. Then re-runs every corpus's verdict
at the LOW and HIGH ends and reports, PER ROW:

    ROBUST   the verdict is the same across the whole interval -- the n=1
             caveat does not reach this row
    FRAGILE  the verdict FLIPS inside the interval -- for this row, and only
             this row, the caveat is the finding

## ⛔ WHAT IT IS NOT

* **NOT a second night.** Resampling one night's commits cannot manufacture the
  between-night variance, which is the larger and unmeasured term. This bounds
  the WITHIN-night component ONLY, and that is a LOWER bound on the true
  uncertainty in B [[feedback-a-borrowed-denominator-invents-its-own-gap]].
* ⛔⛔ **AND THE INTERVAL IS ONE-SIDED, WHICH IS THE HALF THAT MATTERS LEAST.**
  A bootstrap of a MAXIMUM cannot exceed the observed maximum: every resample of
  the same values has a max <= B. So this measures only *"what if B were
  TIGHTER"* — and the direction that would turn a FAIL into a PASS is **B being
  LOOSER**, which this construction structurally cannot express.
  ⇒ 🔑 **THE ROBUSTNESS VERDICTS BELOW ARE THEREFORE NOT A CONFIDENCE STATEMENT.**
  What the bootstrap contributes is a SCALE: the width `B - lo` is how much this
  night's own max moves under resampling, and each row's excess over B is then
  reported IN UNITS OF THAT WIDTH. A row 1.7 widths above the bound and a row 46
  widths above are both "FAIL", and calling both knife-edge is the over-broad
  claim this tool exists to retire. **The upward question — how much would B have
  to grow for this row to pass — is answered exactly and without any resampling
  by the `vs B` ratio itself, which needs no interval at all.**
* **NOT a licence to widen the gate.** Nothing here proposes a new threshold.
  The shipped bound is unchanged; this only says which verdicts depend on it.
* **NOT applicable to the quiet night itself**, which defines B and passes by
  construction. It is reported as DEFINITIONAL, never as a pass.
"""
import argparse
import collections
import json
import os
import random
import statistics as st
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
QUIET = "docs/kernel-delta-history-2026-09-04.jsonl"
SEED = 20260909          # fixed: a bootstrap nobody can reproduce is an anecdote
DRAWS = 20000
LO_PCT, HI_PCT = 5.0, 95.0


def per_commit_p95(path):
    """(per-commit p95 dict, loads). Same definition as the shipped gate."""
    rows = [json.loads(l) for l in open(path, encoding="utf-8") if l.strip()]
    by = collections.defaultdict(list)
    for r in rows:
        by[r["commit"]].append(r)
    out, loads = {}, []
    for c, v in by.items():
        if len(v) < 2:
            continue
        a, b = v[0], v[1]
        rel = []
        for m, dd in a["decls"].items():
            for d, x in dd.items():
                y = b["decls"].get(m, {}).get(d)
                if y is None:
                    continue
                mn = (x + y) / 2
                if mn > 0:
                    rel.append(abs(x - y) / mn)
        if len(rel) >= 10:
            rel.sort()
            out[c[:8]] = rel[int(.95 * (len(rel) - 1))]
        loads += [r["load1"] for r in v]
    return out, loads


def bootstrap_bound(values, draws=DRAWS, seed=SEED):
    """The distribution of `max` under resampling the SAME night's commits.

    ⛔ WITH REPLACEMENT AND AT THE SAME n. Resampling at a smaller n would
    systematically lower a MAX and manufacture a fragility that is an artefact of
    the resample size, not of the bound [[feedback-a-normalisation-needs-its-denominator-to-vary-the-same-way]].
    """
    rng = random.Random(seed)
    n = len(values)
    return sorted(max(rng.choices(values, k=n)) for _ in range(draws))


def pct(sorted_vals, p):
    if not sorted_vals:
        raise ValueError("an empty bootstrap has no percentile — refused")
    i = min(len(sorted_vals) - 1, max(0, int(round(p / 100 * (len(sorted_vals) - 1)))))
    return sorted_vals[i]


def classify(worst, lo, hi):
    """ROBUST when the verdict is the same at both ends of the bound's interval."""
    v_lo = worst <= lo
    v_hi = worst <= hi
    if v_lo == v_hi:
        return "ROBUST", ("PASS" if v_lo else "FAIL")
    return "FRAGILE", "PASS at the high bound, FAIL at the low"


def selftest() -> int:
    bad = []

    def ok(cond, what):
        print(f"   {'ok  ' if cond else '⛔ FAIL'} {what}")
        if not cond:
            bad.append(what)

    # CONTROL FIRST: a degenerate night, every value equal, must give a bound with
    # ZERO width -- if the machinery invents spread here, every width below is noise.
    flat = bootstrap_bound([0.10] * 12, draws=500, seed=1)
    ok(pct(flat, LO_PCT) == pct(flat, HI_PCT) == 0.10,
       "CONTROL — a night with no spread yields a bound of ZERO width, not an invented one")

    # The bootstrap must actually MOVE on a night that has spread.
    spread = bootstrap_bound([0.05, 0.08, 0.10, 0.12, 0.14], draws=2000, seed=1)
    ok(pct(spread, LO_PCT) < pct(spread, HI_PCT),
       "a night WITH spread yields a bound interval of non-zero width")

    # ⛔ THE MAX IS THE CEILING: no resample can exceed the observed maximum, so
    #    the interval is one-sided by construction and the tool must not pretend
    #    otherwise. Asserted, because a reader will expect a symmetric interval.
    ok(pct(spread, HI_PCT) <= 0.14 and max(spread) == 0.14,
       "the bound's interval is bounded ABOVE by the observed max — one-sided by construction")

    # ⛔⛔ THE RESAMPLE SIZE, ASSERTED BY A SIGNATURE ONLY THE RIGHT SIZE HAS.
    #     The docstring warns that resampling at a SMALLER n systematically lowers a
    #     MAX and manufactures fragility — and a break-probe that did exactly that
    #     left this self-test GREEN, because no arm could see the size. A hazard
    #     named in prose and tested by nothing is an ungated claim
    #     [[feedback-a-citation-is-an-ungated-claim]].
    #     THE SIGNATURE: for n DISTINCT values, the share of resamples whose max
    #     equals the observed max is 1 - (1 - 1/n)^n — 0.648 at n=12, but 0.407 at
    #     n=6. The share is therefore a direct read on k, and nothing else here is.
    vals12 = [0.01 * i for i in range(1, 13)]
    dr = bootstrap_bound(vals12, draws=20000, seed=3)
    share = sum(1 for x in dr if x == max(vals12)) / len(dr)
    ok(0.60 <= share <= 0.70,
       f"the bootstrap resamples at the FULL n: share of draws hitting the observed "
       f"max is {share:.3f}, expected 0.648 for n=12 (0.407 if it resampled at n/2)")

    # ROBUST / FRAGILE must both be reachable, and must be decided by the RATIO.
    ok(classify(0.50, 0.10, 0.14)[0] == "ROBUST" and classify(0.50, 0.10, 0.14)[1] == "FAIL",
       "a verdict far above the whole interval is ROBUST-FAIL")
    ok(classify(0.05, 0.10, 0.14)[0] == "ROBUST" and classify(0.05, 0.10, 0.14)[1] == "PASS",
       "a verdict below the whole interval is ROBUST-PASS")
    ok(classify(0.12, 0.10, 0.14)[0] == "FRAGILE",
       "a verdict INSIDE the interval is FRAGILE — this is the row the n=1 caveat is about")
    ok(classify(0.10, 0.10, 0.14)[0] == "ROBUST",
       "a verdict exactly AT the low bound passes both ends — boundary, asserted not assumed")

    # DETERMINISM: a bootstrap nobody can reproduce is an anecdote.
    ok(bootstrap_bound([0.05, 0.09, 0.2], draws=300, seed=7)
       == bootstrap_bound([0.05, 0.09, 0.2], draws=300, seed=7),
       "the bootstrap is SEEDED and reproducible")
    ok(bootstrap_bound([0.05, 0.09, 0.2], draws=300, seed=7)
       != bootstrap_bound([0.05, 0.09, 0.2], draws=300, seed=8),
       "a different seed gives a different draw — the seed is real, not decorative")

    # An empty bootstrap must REFUSE, never return a number.
    try:
        pct([], 50)
        bad.append("an empty bootstrap must refuse, not return a percentile")
        print("   ⛔ FAIL an empty bootstrap must refuse")
    except ValueError:
        print("   ok   an empty bootstrap REFUSES rather than returning a percentile")

    for b in bad:
        pass
    if bad:
        return 1
    print("gate_calibration_strength SELF-TEST: OK (control first — zero spread gives zero "
          "width; interval one-sided at the observed max by construction; ROBUST and FRAGILE "
          "both reachable and the boundary asserted; bootstrap seeded, reproducible, and the "
          "seed shown to matter; RESAMPLE SIZE pinned by the 1-(1-1/n)^n signature, which reds "
          "in BOTH directions; empty bootstrap refuses)")
    return 0


def main() -> int:
    ap = argparse.ArgumentParser(description="how much of the usability verdict is the bound's own noise?")
    # ⛔ BOTH SPELLINGS — see ku_machine_independence.py for the measurement.
    # 26 of 30 scripts here say `--selftest`; a sweep that guesses gets a false
    # green from the scripts that ignore an unknown flag and run their main path.
    ap.add_argument("--self-test", "--selftest", dest="self_test",
                    action="store_true")
    args = ap.parse_args()
    if args.self_test:
        return selftest()

    os.chdir(ROOT)
    import glob
    qp95, _ = per_commit_p95(QUIET)
    vals = list(qp95.values())
    B = max(vals)
    draws = bootstrap_bound(vals)
    lo, hi = pct(draws, LO_PCT), pct(draws, HI_PCT)

    print(f"THE SHIPPED BOUND B = {100*B:.4f}%  (the quiet night's own MAX over "
          f"{len(vals)} commit-pairs, derived at run time)")
    print(f"BOOTSTRAP over that SAME night's commits ({DRAWS:,} draws, seed {SEED}): "
          f"B would lie in [{100*lo:.4f}%, {100*hi:.4f}%] at the {LO_PCT:.0f}-{HI_PCT:.0f} range,")
    print(f"  i.e. the low end is {100*(1-lo/B):.1f}% below the shipped bound. ⛔ The interval is "
          f"ONE-SIDED at the top: no resample of a MAX can exceed the observed maximum.")
    print()
    print("%-52s %8s %9s %8s %10s" % ("corpus", "MAX p95", "vs B", "widths", "ROBUSTNESS"))
    print("  `widths` = (this night's max - B) / (B - lo): the excess over the bound measured in "
          "units of\n  the bound's OWN within-night movement. It is a SCALE, not a probability.")
    fragile = []
    for f in sorted(glob.glob("docs/kernel-delta-history-*.jsonl")):
        if ".analysis." in f:
            continue
        pp, _ = per_commit_p95(f)
        if not pp:
            print("%-52s %8s  %s" % (os.path.basename(f), "-", "no completed pair — NOT SCORED"))
            continue
        worst = max(pp.values())
        if os.path.basename(f) == os.path.basename(QUIET):
            print("%-52s %7.2f%% %8.2fx  %s" % (os.path.basename(f), 100*worst, worst/B,
                  "DEFINITIONAL — this night IS the bound; not a pass"))
            continue
        kind, verdict = classify(worst, lo, hi)
        if kind == "FRAGILE":
            fragile.append(os.path.basename(f))
        widths = (worst - B) / (B - lo) if B > lo else float("inf")
        print("%-52s %7.2f%% %8.2fx %7.1fw  %s (%s)" % (os.path.basename(f), 100*worst,
              worst/B, widths, kind, verdict))
    print()
    if fragile:
        print("⛔ FRAGILE ROWS — for these, and ONLY these, the n=1 caveat is the finding:")
        for f in fragile:
            print(f"     {f}")
    else:
        print("✅ NO ROW'S VERDICT FLIPS inside the bound's own sampling interval.")
    print("⇒ The blanket caveat 'the bound is n=1 and knife-edge' is TRUE of the bound and "
          "NOT true of every verdict it issues. Quote it PER ROW, with the width figure.")
    print("⛔ TWO LIMITS, BOTH IN THE DIRECTION THAT WOULD WEAKEN THIS:")
    print("   (1) WITHIN-night only. Resampling one night's commits cannot produce the "
          "BETWEEN-night\n       variance, which is larger and still unmeasured. This is a "
          "LOWER bound on B's uncertainty.")
    print("   (2) ONE-SIDED. A bootstrap of a MAX cannot exceed the observed max, so this "
          "answers only\n       'what if B were TIGHTER'. The direction that would turn a FAIL "
          "into a PASS — B being\n       LOOSER — this construction cannot express. The "
          "ROBUST labels are a SCALE, not a confidence.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
