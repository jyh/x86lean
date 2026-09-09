#!/usr/bin/env python3
"""QUEUE 4f — PRICE THE TWO REPAIRS THAT CHANGE THE DELTA, NOT THE QUANTITY.

D152 closed the "which quantity" question (4a/4c/4d refuted; 4b survives owing a
budget from a second source and a second machine) and left a finding that
outlives every candidate: over the project's twelve-commit history, the pairs
clearing the noise floor are 0 of 102 at the worst same-tree spread, 49 at the
median, 99 at the best.  ⇒ **the gate is trying to resolve changes the same size
as its own noise.**  The two untried repairs do not pick another quantity; they
make the DELTA bigger relative to the noise:

  A.  MORE REPEATS A SIDE.  The gate's band is K standard errors of
      `median(head) - median(base)`, so it falls as 1/sqrt(n).  The gate already
      prints `~N repeats a side would decide it`.  What has never been done is
      to read that projection over the whole corpus and convert it to minutes.

  B.  GATE ACCUMULATED MULTI-BATCH DRIFT instead of one batch.  The band is a
      property of the two trees being compared and does NOT grow with the window
      length; the delta does.  So the signal-to-noise of a k-batch window rises
      with k at constant instrument cost.

⛔ WHY THIS TOOL IMPORTS THE GATE INSTEAD OF RESTATING IT.  A pricing tool that
carried its own copy of `resolution`, `effective` or `repeats_to_decide` would
agree with the gate today and diverge on the next ordinary append to either —
and it would diverge silently, in whichever direction nobody is looking.  Every
rule below is the merge gate's own, imported.  The only thing this file adds is
the WINDOW: which readings are handed to those rules as `base` and `head`.
[[feedback-a-duplicate-born-in-agreement]]

⭐⭐ AND THE CORPUS IS TWO INDEPENDENT WALKS OVER THE SAME TWELVE COMMITS.
`docs/kernel-delta-history-2026-09-04.jsonl` (09/04 22:02-22:29, load1 ~4.5) and
`docs/kernel-delta-history-USER2-2026-09-05.jsonl` (09/05 21:08-21:42, load1
~12.4) profile the SAME twelve trees, twenty-three hours apart, each as two
sweeps.  Every number this tool prints is therefore printed TWICE, once per
night, and the two nights are the check on each other.  A repair whose price
depends on which night measured it is not priced.
⚠️ They are two nights on ONE box with ONE instrument, not two independent
origins.  That is the strongest second source available without a second
machine, and it is weaker than a second machine.
[[feedback-two-readings-are-not-two-witnesses]] [[feedback-a-single-reading-is-about-its-run]]

Usage:
    delta_repair_price.py --walk FILE [--walk FILE] [--repair a|b|both]
    delta_repair_price.py --selftest
"""
import json, math, os, statistics, sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import kernel_delta as kd                                   # noqa: E402  the gate itself
import check_corpus_claims as _ccc                          # noqa: E402  the ROLE rule, one home

BUDGET_FILE = os.path.join(HERE, "kernel_delta_budget.txt")


# ⛔ A WALK IS A LIST OF READINGS, AND WHICH READINGS BELONG TO ONE TREE IS THE
# ONLY THING THIS FILE DECIDES.  The walk records `commit` and `sweep`; a tree's
# readings are every row carrying its commit.  The commit ORDER is taken from
# sweep 0, which walked the history forwards — reading it from a set would put
# the windows of repair B in an arbitrary order and the k-batch curve would be a
# curve about dictionary iteration.
def load_walk(path):
    rows = [json.loads(l) for l in open(path) if l.strip()]
    # ⛔⛔ THE ROLE IS MEASURED, NOT ASSUMED — and this refusal is the repair for
    # `b5d1522`.  Before it, this function ACCEPTED
    # `docs/deterministic-cost-history-2026-09-05.jsonl` and returned a
    # well-formed 12-commit walk: both corpora carry `commit` and `t`, which is
    # every key this loader touched.  A duck-typed loader cannot referee its own
    # contract, so feeding it the wrong corpus produced NUMBERS rather than an
    # error.  The rule is IMPORTED from the gate that owns it (D148 §2: a
    # referee invented beside a shipped rule disagrees in the flattering
    # direction).  [[feedback-only-the-contract-says-which-file]]
    role, why = _ccc.corpus_role(rows)
    if role != "walk":
        raise ValueError(
            f"{path} is not a kernel-delta walk: it measures as {role!r} ({why}). "
            f"A tool that accepts the wrong corpus reports numbers about the wrong "
            f"object; see scripts/check_corpus_claims.py.")
    order, seen = [], set()
    for r in sorted(rows, key=lambda r: (r.get("sweep", 0), r["t"])):
        if r["commit"] not in seen:
            seen.add(r["commit"])
            order.append(r["commit"])
    by = {}
    for r in rows:
        by.setdefault(r["commit"], []).append(r)
    return {"path": path, "order": order, "by": by, "rows": rows}


def unit_readings(walk, decl_map):
    """{commit: {unit: [ms, ...]}} — the readings, flattened by the GATE's rule."""
    out = {}
    for c, rows in walk["by"].items():
        per = {}
        for r in rows:
            for u, v in kd.units_of(r, decl_map).items():
                per.setdefault(u, []).append(v)
        out[c] = per
    return out


# ⭐ ONE WINDOW, JUDGED EXACTLY AS THE MERGE GATE JUDGES A MERGE.
#
# ⚠️ `budget_ms` is passed in rather than computed here, because repair B's
# allowance is not one budget: a k-batch window is k batches each of which was
# entitled to its own budget against its own base, so the accumulated allowance
# is the SUM of those k, not k times the first.  Computing it at the call site
# keeps that decision visible instead of buried in a helper.
# ⛔ MOVED INTO THE GATE (D154) AND DELEGATED HERE. This was the second copy of
# the three-way rule; `kernel_drift.py` would have been the third. The pricing
# tool must judge EXACTLY as the gate judges or its R numbers price a rule the
# repository does not merge on, so the delegation is the point and not a tidy-up.
judge = kd.judge_delta


def budget_for(unit, base_ms, default_ms, budgets, floor):
    return kd.effective(budgets.get(unit, default_ms), base_ms, floor)


# ⭐⭐⭐ THE ONE AXIS BOTH REPAIRS MOVE — RESOLVING POWER.
#
#     R = band / allowance
#
# R < 1 means the instrument can see a change the size of the change the gate is
# willing to permit.  R > 1 is D152's finding written as one number: the gate is
# trying to resolve changes the size of its own noise, so it cannot tell a
# batch that spends its whole allowance from a batch that spends nothing.
#
# ⛔⛔ AND R IS WHY THE OBVIOUS PRICE FOR REPAIR A IS THE WRONG ONE.  The gate's
# `~N repeats a side would decide it` divides by `|delta - budget|`, so a commit
# landing ON its budget needs an unbounded N — and that N is a fact about THE
# COMMIT, not about the instrument.  Measured on the 09/05 walk: the worst case
# asks for 587,413 repeats a side, and its margin is +4.4 ms against a budget of
# 1,695.6.  Quoting 587,413 as the price of repair A would price the noise with
# another quantity's number.  R has no margin in it: it asks how many repeats
# bring the band under the ALLOWANCE, which is the question that survives
# whatever the commit happened to cost.
# [[feedback-a-join-on-a-lossy-key]] [[feedback-a-wrong-models-score-is-a-joint-fact]]
#
# ⚠️ The arithmetic is `kd.repeats_to_decide`'s, called with the allowance in
# place of the margin, because it IS the same projection — `n*(K*se/target)^2`.
# A second copy differing only in what it divides by is the duplicate that
# diverges on the next append.
def resolving_power(band, allowance):
    if allowance <= 0:
        return None
    return band / allowance


# ══════════════════════════════════════════════════════════════════════════════
# REPAIR A — MORE REPEATS A SIDE
# ══════════════════════════════════════════════════════════════════════════════
#
# ⛔⛔ WHAT THIS SECTION CAN AND CANNOT SETTLE.  `repeats_to_decide` is a
# PROJECTION: `need = n * (K*se/margin)^2`, which reads this run's noise forward
# on the assumption that every further reading is an independent draw from the
# same distribution.  The corpus can price what the projection ASKS FOR.  It
# cannot check whether the projection is TRUE — for that the band has to be
# watched as n actually rises on one tree in one session, which is a measurement
# and not an analysis.  This tool prints the ask; `--repeat-scaling` reads the
# measurement.  Do not quote the ask as the price.
# [[feedback-a-citation-is-an-ungated-claim]]
def repair_a(walk, decl_map, default_ms, budgets, floor, secs_per_reading):
    ur = unit_readings(walk, decl_map)
    order = walk["order"]
    rows, unmeasurable, priced = [], 0, []
    for i in range(len(order) - 1):
        b, h = order[i], order[i + 1]
        for u in sorted(set(ur[b]) & set(ur[h])):
            bs, hs = ur[b][u], ur[h][u]
            bud = budget_for(u, statistics.median(bs), default_ms, budgets, floor)
            j = judge(bs, hs, bud)
            j.update(unit=u, base=b[:8], head=h[:8])
            # the margin-free pair: how far the band is from the allowance, and
            # how many repeats a side would close that gap
            j["R"] = resolving_power(j["band"], bud)
            # ⛔⛔ `repeats_to_decide` RETURNS `max(n + 1, ceil(need))`, so it can
            # never say "fewer than three" and it can never say "none".  Reading
            # its output over a corpus where most units are ALREADY resolved
            # therefore reports a median of 3 — which is the function's floor
            # wearing a price's clothes.  Asked only where repeats are actually
            # needed (R >= 1), the same column says something.
            # [[feedback-a-declared-list-inherits-its-default]]
            j["need_R"] = (kd.repeats_to_decide(j["n"], j["se"], bud)
                           if (j["R"] is not None and j["R"] >= 1.0) else None)
            rows.append(j)
            if j["verdict"] == "UNMEASURABLE":
                unmeasurable += 1
                if j["need"]:
                    priced.append(j["need"])
    return {"rows": rows, "n_cases": len(rows), "unmeasurable": unmeasurable,
            "priced": sorted(priced), "secs": secs_per_reading}


# ══════════════════════════════════════════════════════════════════════════════
# REPAIR B — GATE ACCUMULATED MULTI-BATCH DRIFT
# ══════════════════════════════════════════════════════════════════════════════
#
# ⭐ THE LEVER, STATED SO IT CAN BE REFUTED: the band is a property of the two
# trees compared and is INDEPENDENT of how many commits separate them, while the
# delta accumulates.  If that is right, the resolvable fraction rises with the
# window length k at ZERO extra instrument cost — the gate still profiles two
# trees, they are just further apart.
#
# ⛔ AND THE ALLOWANCE MUST ACCUMULATE TOO, or this is not a repair, it is a
# tighter gate wearing a repair's name.  A k-batch window is entitled to the sum
# of the k per-batch budgets, each computed against the base it would have had.
# A window judged against ONE batch's budget would "resolve" more simply by
# convicting more, and the extra convictions would be the design's own arithmetic.
# [[feedback-widening-a-gate-needs-a-second-source]]
def repair_b(walk, decl_map, default_ms, budgets, floor, kmax=None):
    ur = unit_readings(walk, decl_map)
    order = walk["order"]
    kmax = kmax or (len(order) - 1)
    per_k = {}
    for k in range(1, kmax + 1):
        cases = []
        for i in range(len(order) - k):
            b, h = order[i], order[i + k]
            for u in sorted(set(ur[b]) & set(ur[h])):
                bs, hs = ur[b][u], ur[h][u]
                # the accumulated allowance: each step's own budget, summed
                acc = 0.0
                for s in range(k):
                    step_base = statistics.median(ur[order[i + s]][u])
                    acc += budget_for(u, step_base, default_ms, budgets, floor)
                j = judge(bs, hs, acc)
                j.update(unit=u, k=k, base=b[:8], head=h[:8])
                j["R"] = resolving_power(j["band"], acc)
                # the DETECTION question, separate from the budget question:
                # can the instrument see this accumulated drift at all?
                j["detected"] = abs(j["d"]) > j["band"]
                cases.append(j)
        n = len(cases)
        Rs = [c["R"] for c in cases if c["R"] is not None and math.isfinite(c["R"])]
        per_k[k] = {
            "n": n,
            "unmeasurable": sum(1 for c in cases if c["verdict"] == "UNMEASURABLE"),
            "over": sum(1 for c in cases if c["verdict"] == "OVER"),
            "ok": sum(1 for c in cases if c["verdict"] == "ok"),
            "detected": sum(1 for c in cases if c["detected"]),
            "R_med": statistics.median(Rs) if Rs else None,
            "R_resolved": sum(1 for r in Rs if r < 1.0),
            "R_n": len(Rs),
            "cases": cases,
        }
    return per_k


# ══════════════════════════════════════════════════════════════════════════════
# THE SECOND SOURCE — DO THE TWO NIGHTS AGREE ON THE DELTA?
# ══════════════════════════════════════════════════════════════════════════════
#
# ⛔⛔ THIS IS THE CHECK BOTH REPAIRS REST ON AND NEITHER NAMES.  Both repairs
# assume the gate's band describes the reproducibility of `d`.  Two walks over
# the same twelve trees let that be TESTED rather than assumed: if the band is
# honest, `|d_A - d_B|` should sit inside the two bands combined about as often
# as a 2-sigma statement predicts.  If it sits outside far more often, the band
# understates and BOTH repairs are priced off a number that is too small —
# repair A's projection most of all, because it divides by that number squared.
#
# ⚠️ It is not a coverage test of a nominal rate: n is small and the two nights
# differ in load by 2.8x.  It is a direction and an order of magnitude.
def cross_night(walks, decl_map, default_ms, budgets, floor):
    a, b = walks[0], walks[1]
    ura, urb = unit_readings(a, decl_map), unit_readings(b, decl_map)
    order = [c for c in a["order"] if c in urb]
    out = []
    for i in range(len(order) - 1):
        cb, ch = order[i], order[i + 1]
        for u in sorted(set(ura[cb]) & set(ura[ch]) & set(urb[cb]) & set(urb[ch])):
            da = statistics.median(ura[ch][u]) - statistics.median(ura[cb][u])
            db = statistics.median(urb[ch][u]) - statistics.median(urb[cb][u])
            banda = kd.K_SIGMA * kd.resolution(ura[cb][u], ura[ch][u])
            bandb = kd.K_SIGMA * kd.resolution(urb[cb][u], urb[ch][u])
            comb = math.sqrt(banda ** 2 + bandb ** 2)
            out.append({"unit": u, "da": da, "db": db, "banda": banda,
                        "bandb": bandb, "comb": comb,
                        "inside": abs(da - db) <= comb,
                        "gap": abs(da - db)})
    return out


# ⭐ THE CACHED-ANCHOR VARIANT OF REPAIR B, PRICED SEPARATELY.
#
# Repair B has two spellings and they cost differently.  RE-PROFILE the anchor
# every run: the gate reads two trees in one session exactly as today, so a
# per-session offset (the box is slower tonight) lands on BOTH sides and largely
# cancels in the difference — same cost as today, no loss.  CACHE the anchor's
# reading and compare each new head against it: half the profiling, but base and
# head are now read on different nights and whatever cancelled no longer does.
# The two walks measure that difference directly, because the same twelve trees
# were read on both nights.
def cached_anchor(walks, decl_map, default_ms, budgets, floor):
    a, b = walks[0], walks[1]
    ura, urb = unit_readings(a, decl_map), unit_readings(b, decl_map)
    order = [c for c in a["order"] if c in urb]
    same, cross = [], []
    for i in range(len(order) - 1):
        cb, ch = order[i], order[i + 1]
        for u in sorted(set(ura[cb]) & set(ura[ch]) & set(urb[cb]) & set(urb[ch])):
            bud = budget_for(u, statistics.median(urb[cb][u]),
                             default_ms, budgets, floor)
            # same-session: both sides from walk B
            same.append(judge(urb[cb][u], urb[ch][u], bud))
            # cached anchor: base from walk A (last night), head from walk B
            cross.append(judge(ura[cb][u], urb[ch][u], bud))
    return same, cross


# ══════════════════════════════════════════════════════════════════════════════
# THE MEASUREMENT REPAIR A ACTUALLY NEEDS — DOES THE BAND FALL AS 1/sqrt(n)?
# ══════════════════════════════════════════════════════════════════════════════
#
# ⛔⛔ THE PROJECTION IS NOT THE PRICE.  `repeats_to_decide` assumes the band
# shrinks as 1/sqrt(n) without limit.  That is true of independent draws and
# false of anything with a per-session component: if part of a tree's spread is
# an offset that a whole session shares, repeats inside that session never see
# it and the band has a FLOOR the projection cannot express.  A projection that
# cannot express a floor will always name a finite N, however large — so "the
# gate names a remedy" is not evidence that the remedy exists.
#
# This reads a run of m readings of ONE frozen tree in ONE session and asks
# whether the observed spread of `median(first n) - median(next n)` falls the way
# the projection says.  A null delta is the right subject: the true value is
# zero, so everything the estimator reports IS its own noise.
# [[feedback-a-probe-must-create-its-condition]] [[feedback-conservative-is-a-direction-not-a-margin]]
def repeat_scaling(path, decl_map, units_wanted=None, order="block"):
    rows = [json.loads(l) for l in open(path) if l.strip()]
    rows.sort(key=lambda r: r.get("rep", r["t"]))
    per = {}
    for r in rows:
        for u, v in kd.units_of(r, decl_map).items():
            per.setdefault(u, []).append(v)
    m = len(rows)
    out = {}
    for u, xs in per.items():
        if units_wanted and u not in units_wanted:
            continue
        if len(xs) < 4 or statistics.median(xs) <= 0:
            continue
        rec = {"m": m, "level": statistics.median(xs), "readings": xs, "n": {}}
        for n in (1, 2, 3, 4, 6):
            if 2 * n > m:
                continue
            # every disjoint split of the m readings into two arms of n, taken in
            # ORDER: arm one is readings [j, j+n), arm two is [j+n, j+2n).  Using
            # adjacent blocks rather than random subsets keeps the two arms as
            # close in time as a real base/head pair is, which is the comparison
            # the gate makes.
            ds, bands, covered, ratios = [], [], 0, []
            for j in range(0, m - 2 * n + 1):
                # ⛔⛔ THE SPLIT ORDER IS NOT A DETAIL, IT IS THE SUBJECT.
                #
                # `block` puts one side's readings before the other's, which is
                # what a naive reading of a repeat run does — and under a box
                # that DRIFTS it maximises the between-side difference while
                # each side reports a tight internal spread.  Measured on the
                # frozen tree: base [13.0, 13.1] head [11.4, 11.5], a band of
                # 0.18 and a delta of -1.6.
                #
                # `alternate` is the order THE GATE ACTUALLY USES —
                # base,head,base,head — which is there precisely to cancel that
                # drift.  `kernel_delta.py`'s own docstring says the residual
                # inflates `se` and is therefore CONSERVATIVE; running both
                # orders over the same readings is what tests that sentence
                # instead of quoting it.
                # [[feedback-the-burden-is-on-the-departure]]
                if order == "alternate":
                    w = xs[j:j + 2 * n]
                    bs, hs = w[0::2], w[1::2]
                else:
                    bs, hs = xs[j:j + n], xs[j + n:j + 2 * n]
                d = statistics.median(hs) - statistics.median(bs)
                ds.append(d)
                se = kd.resolution(bs, hs)
                b = kd.K_SIGMA * se if se != float("inf") else None
                bands.append(b)
                # ⭐⭐ COVERAGE IS THE HONEST INSTRUMENT, NOT THE SHRINK RATE.
                # The true delta here is ZERO, so every |d| the estimator reports
                # is its own error and the band is its own claim about that
                # error.  How often the claim CONTAINS the error is the only
                # question that matters to a gate: a band that shrinks
                # beautifully and stops covering is worse than one that does not
                # shrink at all, because the gate CONVICTS outside the band.
                if b is not None and abs(d) <= b:
                    covered += 1
                if b:
                    ratios.append(abs(d) / b)
            rms = math.sqrt(sum(d * d for d in ds) / len(ds))
            bb = [b for b in bands if b is not None]
            # ⭐⭐ `max |d| / band` IS THE STATISTIC THAT SEPARATES A NOISY BAND
            # FROM A WRONG ONE, and COVERAGE is not.  Measured on the two
            # fixtures: independent noise reaches 1.45 at n=4, a per-session
            # offset reaches 465 — three orders of magnitude — while their
            # coverages are 89% and 86%, three points apart.  Coverage counts
            # HOW OFTEN the band is exceeded, and a block split can only straddle
            # an offset in a fixed small fraction of its windows; the magnitude
            # is where the offset lives.  A statistic that dilutes the thing it
            # is looking for reports agreement.
            # [[feedback-a-ratio-survives-a-doubling]]
            rec["n"][n] = {"splits": len(ds), "rms_d": rms,
                           "max_abs_d": max(abs(d) for d in ds),
                           "mean_band": (sum(bb) / len(bb)) if bb else None,
                           "covered": covered,
                           "coverage": (covered / len(bb)) if bb else None,
                           "max_ratio": max(ratios) if ratios else None,
                           "p90_ratio": (sorted(ratios)[int(0.9 * (len(ratios) - 1))]
                                         if ratios else None)}
        out[u] = rec
    return out


# ══════════════════════════════════════════════════════════════════════════════
def fmt_pct(x, y):
    return f"{x}/{y} ({100.0 * x / y:.0f}%)" if y else f"{x}/0 (—)"


def report(walks, decl_map, default_ms, budgets, floor, repeat_file=None):
    print("=" * 78)
    print("QUEUE 4f — PRICING THE TWO REPAIRS THAT CHANGE THE DELTA")
    print("=" * 78)
    for w in walks:
        secs = statistics.median([r.get("secs", 0.0) for r in w["rows"]])
        load = statistics.median([r.get("load1", -1.0) for r in w["rows"]])
        print(f"  corpus {os.path.basename(w['path'])}: {len(w['rows'])} readings, "
              f"{len(w['order'])} trees, median reading {secs:.0f}s, median load1 {load:.1f}")
    print()

    # ── THE FINDING, AS ONE NUMBER ────────────────────────────────────────────
    print("R = band / allowance — D152's finding as one number (R>1: the gate")
    print("cannot tell a batch spending its whole allowance from one spending none)")
    print("-" * 78)
    WATCH = ["Tests.Coverage", "Tests.Coverage @residue", "Tests.Anchors",
             "Tests.Coverage @decl memDestSweep",
             "Tests.Coverage @decl pre_states_have_a_returnable_frame",
             "Tests.Coverage @decl vectorCoverage", "X86.Theorems", "X86.Syntax"]
    for w in walks:
        secs = statistics.median([r.get("secs", 0.0) for r in w["rows"]])
        w["_ra"] = repair_a(w, decl_map, default_ms, budgets, floor, secs)
    print(f"  {'unit':<50}" + "".join(f"{os.path.basename(w['path'])[21:26]:>12}"
                                      for w in walks))
    for u in WATCH:
        cells = []
        for w in walks:
            rs = [r["R"] for r in w["_ra"]["rows"]
                  if r["unit"] == u and r["R"] is not None and math.isfinite(r["R"])]
            cells.append(f"{statistics.median(rs):.2f}" if rs else "—")
        print(f"  {u:<50}" + "".join(f"{c:>12}" for c in cells))
    for w in walks:
        rs = [r["R"] for r in w["_ra"]["rows"]
              if r["R"] is not None and math.isfinite(r["R"])]
        w["_Rall"] = rs
    print(f"  {'— median over all 23 gated units —':<50}"
          + "".join(f"{statistics.median(w['_Rall']):>12.2f}" for w in walks))
    print(f"  {'— units with R > 1 (cannot resolve their allowance) —':<50}"
          + "".join(f"{sum(1 for r in w['_Rall'] if r > 1) * 100.0 / len(w['_Rall']):>11.0f}%"
                    for w in walks))
    print()

    # ── REPAIR A ──────────────────────────────────────────────────────────────
    print("REPAIR A — MORE REPEATS A SIDE  (band falls as 1/sqrt(n): R needs n x 4")
    print("                                 for every halving, and the run costs n)")
    print("-" * 78)
    print(f"  {'corpus':<14}{'cases':>7}{'UNMEAS':>15}{'median N':>10}{'p90 N':>9}"
          f"{'worst N':>12}{'p90 cost/merge':>16}")
    for w in walks:
        ra = w["_ra"]
        pr = ra["priced"]
        med = f"{statistics.median(pr):.0f}" if pr else "—"
        p90v = pr[int(0.9 * (len(pr) - 1))] if pr else 0
        p90 = f"{p90v:,}" if pr else "—"
        worst = f"{max(pr):,}" if pr else "—"
        cost = f"{2 * p90v * ra['secs'] / 60.0:,.0f} min" if pr else "—"
        print(f"  {os.path.basename(w['path'])[21:35]:<14}{ra['n_cases']:>7}"
              f"{fmt_pct(ra['unmeasurable'], ra['n_cases']):>15}{med:>10}{p90:>9}"
              f"{worst:>12}{cost:>16}")
    print()
    # ⛔ AND THE SAME COLUMN, MARGIN-FREE.  `need` above divides by |delta -
    # budget| and is therefore a joint fact about the noise AND where the commit
    # happened to land.  `need_R` asks only how many repeats bring the band under
    # the allowance — the same projection, with the commit taken out of it.
    print("  the same question with the COMMIT taken out of it — repeats a side")
    print("  needed to bring the band under the unit's own allowance (R < 1):")
    print(f"  {'unit':<50}" + "".join(f"{os.path.basename(w['path'])[21:26]:>12}"
                                      for w in walks))
    for u in WATCH:
        cells = []
        for w in walks:
            ns = [r["need_R"] for r in w["_ra"]["rows"]
                  if r["unit"] == u and r["need_R"]]
            cells.append(f"{statistics.median(ns):,.0f}" if ns else "R<1 already")
        print(f"  {u:<50}" + "".join(f"{c:>12}" for c in cells))
    for w in walks:
        ns = [r["need_R"] for r in w["_ra"]["rows"] if r["need_R"]]
        w["_needR"] = sorted(ns)
        secs = w["_ra"]["secs"]
        if ns:
            p90 = w["_needR"][int(0.9 * (len(ns) - 1))]
            print(f"  {os.path.basename(w['path'])}: {len(ns)} of "
                  f"{w['_ra']['n_cases']} cases have R >= 1 at all; "
                  f"p90 = {p90:,} repeats a side ⇒ "
                  f"{2 * p90 * secs / 60.0:,.0f} min a merge")
        else:
            print(f"  {os.path.basename(w['path'])}: NO case has R >= 1 — "
                  f"every unit already resolves its own allowance at n=2")
    print()

    # ── REPAIR B ──────────────────────────────────────────────────────────────
    print("REPAIR B — GATE ACCUMULATED MULTI-BATCH DRIFT (band is k-independent)")
    print("-" * 78)
    for w in walks:
        pk = repair_b(w, decl_map, default_ms, budgets, floor)
        w["_rb"] = pk
        print(f"  {os.path.basename(w['path'])}")
        print(f"    {'k':>3}{'windows':>9}{'UNMEAS':>13}{'median R':>10}"
              f"{'R<1':>14}{'median band':>13}{'median allowance':>18}")
        for k in sorted(pk):
            s = pk[k]
            bands = [c["band"] for c in s["cases"] if c["band"] != float("inf")]
            allw = [c["budget"] for c in s["cases"]]
            mb = statistics.median(bands) if bands else float("nan")
            print(f"    {k:>3}{s['n']:>9}{fmt_pct(s['unmeasurable'], s['n']):>13}"
                  f"{s['R_med']:>10.2f}{fmt_pct(s['R_resolved'], s['R_n']):>14}"
                  f"{mb:>13.1f}{statistics.median(allw):>18.1f}")
        # ⛔ THE LEVER'S PREMISE, CHECKED RATHER THAN ASSUMED: "the band does not
        # move with k".  It does move — the trees at the ends of a longer window
        # sit further apart in LEVEL and the spread travels with the level — so
        # the honest claim is that the allowance grows FASTER than the band, not
        # that the band is constant.  Both columns are printed so the claim can
        # be read rather than taken.
        b1 = statistics.median([c["band"] for c in pk[1]["cases"]
                                if c["band"] != float("inf")])
        kx = max(pk)
        bk = statistics.median([c["band"] for c in pk[kx]["cases"]
                                if c["band"] != float("inf")])
        a1 = statistics.median([c["budget"] for c in pk[1]["cases"]])
        ak = statistics.median([c["budget"] for c in pk[kx]["cases"]])
        print(f"    ⇒ over k=1→{kx} the band moved {bk / b1:.2f}x and the "
              f"allowance {ak / a1:.2f}x ⇒ R fell {pk[kx]['R_med'] / pk[1]['R_med']:.2f}x")
        print()

    # ── THE HEAD-TO-HEAD, ON THE ONE AXIS ─────────────────────────────────────
    #
    # ⭐⭐⭐ BOTH REPAIRS MOVE R AND ONLY R, so they can be quoted in the same
    # unit: how much R falls, and what it costs.  Repair A buys 1/sqrt(n) for a
    # run cost of n — so every halving of R costs FOUR times the profiling.
    # Repair B buys ~1/k for no extra profiling at all, and pays in LATENCY: a
    # regression is caught k batches after it lands, and attributed to a window
    # rather than a commit.
    print("HEAD TO HEAD — the same fall in R, priced in each currency")
    print("-" * 78)
    print(f"  {'corpus':<14}{'k':>4}{'R(k)':>8}{'fall':>8}"
          f"{'repeats a side to match':>26}{'cost of that':>15}")
    for w in walks:
        pk = w["_rb"]
        secs = w["_ra"]["secs"]
        r1 = pk[1]["R_med"]
        for k in (2, 4, 8):
            if k not in pk:
                continue
            fall = r1 / pk[k]["R_med"]
            # R falls as 1/sqrt(n), so matching a fall f needs n = n0 * f^2
            n_match = math.ceil(2 * fall ** 2)
            print(f"  {os.path.basename(w['path'])[21:35]:<14}{k:>4}"
                  f"{pk[k]['R_med']:>8.2f}{fall:>7.1f}x{n_match:>26,}"
                  f"{2 * n_match * secs / 60.0:>12,.0f} min")
        print(f"  {'':<14}     ⇒ repair B pays 0 extra profiling and k batches of "
              f"LATENCY instead")
    print()

    # ── THE SECOND SOURCE ─────────────────────────────────────────────────────
    if len(walks) >= 2:
        print("THE SECOND SOURCE — DO THE TWO NIGHTS AGREE ON THE DELTA?")
        print("-" * 78)
        xs = cross_night(walks, decl_map, default_ms, budgets, floor)
        fin = [x for x in xs if x["comb"] not in (float("inf"), 0.0)]
        ins = sum(1 for x in fin if x["inside"])
        print(f"  {len(xs)} adjacent (unit, pair) deltas measured on BOTH nights; "
              f"{len(fin)} have a finite combined band")
        print(f"  |d_A - d_B| inside the two bands combined: {fmt_pct(ins, len(fin))}")
        if fin:
            ratios = sorted(x["gap"] / x["comb"] for x in fin if x["comb"] > 0)
            print(f"  gap / combined band — median {statistics.median(ratios):.2f}, "
                  f"p90 {ratios[int(0.9 * (len(ratios) - 1))]:.2f}, "
                  f"max {max(ratios):.2f}")
        print()

        print("REPAIR B's TWO SPELLINGS — re-profile the anchor, or cache it")
        print("-" * 78)
        same, cross = cached_anchor(walks, decl_map, default_ms, budgets, floor)
        print(f"  {'spelling':<38}{'OVER':>7}{'ok':>7}{'UNMEAS':>9}{'median |d|':>13}")
        for lbl, g in (("re-profiled (both sides one night)", same),
                       ("cached anchor (base last night)", cross)):
            print(f"  {lbl:<38}"
                  f"{sum(1 for c in g if c['verdict'] == 'OVER'):>7}"
                  f"{sum(1 for c in g if c['verdict'] == 'ok'):>7}"
                  f"{sum(1 for c in g if c['verdict'] == 'UNMEASURABLE'):>9}"
                  f"{statistics.median([abs(c['d']) for c in g]):>13.1f}")
        # ⛔⛔ THE COLUMN THAT DECIDES IT IS `OVER`, NOT `UNMEAS`.  A design that
        # REFUSES more is paying for its cheapness honestly; a design that
        # CONVICTS where the same-session comparison says `ok` is manufacturing
        # regressions out of the difference between two nights.  These are the
        # project's own twelve commits, and the re-profiled arm convicts none of
        # them.
        n_over = sum(1 for c in cross if c["verdict"] == "OVER")
        if n_over:
            print(f"  ⇒ caching the anchor manufactures {n_over} conviction(s) "
                  f"the same-session comparison calls `ok`. The cheap spelling "
                  f"of repair B is REFUTED; re-profile the anchor.")
        print()

    # ── THE MEASUREMENT ───────────────────────────────────────────────────────
    if repeat_file and os.path.exists(repeat_file):
        print("REPAIR A's PREMISE — DOES THE BAND FALL AS 1/sqrt(n)? (measured)")
        print("-" * 78)
        sc = repeat_scaling(repeat_file, decl_map)
        # ⭐⭐⭐ THE BEST-POWERED THING THIS RUN SAYS, AND IT IS NOT ABOUT SHRINK
        # RATE.  The tree is frozen, so the true delta is ZERO and every |d| the
        # gate computes is its own error.  The band is the gate's CLAIM about
        # that error.  How often the claim is wrong, at each n, is a statement
        # about the shipped gate at its default n=2 — not about either repair.
        print(f"  a frozen tree ⇒ the true delta is 0, so every |d| is the "
              f"gate's own error and every exceedance is a band that lied.")
        print(f"  A nominal 2-sigma band should be exceeded about 4.6% of the time.")
        print(f"  {'order':<12}{'n':>4}{'units':>7}{'obs':>7}{'|d| > band':>16}"
              f"{'worst |d|/band':>17}")
        # ⭐ BOTH ORDERS, because the gate ALTERNATES and a block split does not:
        # printing only one would be a measurement of an ordering the gate does
        # not use, quoted as a measurement of the gate.
        for order in ("block", "alternate"):
            so = (sc if order == "block"
                  else repeat_scaling(repeat_file, decl_map, order=order))
            for n in (2, 3, 4, 6):
                tot = exc = units = 0
                worst = 0.0
                for rec in so.values():
                    s = rec["n"].get(n)
                    if not s or s["max_ratio"] is None:
                        continue
                    units += 1
                    tot += s["splits"]
                    exc += s["splits"] - s["covered"]
                    worst = max(worst, s["max_ratio"])
                if tot:
                    print(f"  {order:<12}{n:>4}{units:>7}{tot:>7}"
                          f"{exc:>8} ({100.0 * exc / tot:5.1f}%){worst:>17.2f}")
        print()
        big = sorted(sc.items(), key=lambda kv: -kv[1]["level"])[:6]
        for u, rec in big:
            print(f"  {u}  (level {rec['level']:,.1f} ms, m={rec['m']} readings "
                  f"of ONE frozen tree)")
            print(f"    {'n':>3}{'splits':>8}{'rms |d|':>12}{'max |d|':>12}"
                  f"{'mean band':>12}{'rms vs 1/sqrt(n)':>19}")
            base = rec["n"].get(1, {}).get("rms_d")
            for n in sorted(rec["n"]):
                s = rec["n"][n]
                pred = f"{base / math.sqrt(n):,.1f}" if base else "—"
                mb = f"{s['mean_band']:,.1f}" if s["mean_band"] is not None else "—"
                # ⛔ A COLUMN WHOSE SPLIT COUNT HAS FALLEN TO ONE IS A READING,
                # NOT AN RMS, and it is printed with that said rather than left
                # to look like the rows above it.  m readings give m-2n+1 splits,
                # so the largest n a run supports is always its weakest column —
                # the one an eye goes to first.
                # [[feedback-a-single-reading-is-about-its-run]]
                flag = "  ⚠️ ONE SPLIT" if s["splits"] == 1 else ""
                print(f"    {n:>3}{s['splits']:>8}{s['rms_d']:>12,.1f}"
                      f"{s['max_abs_d']:>12,.1f}{mb:>12}{pred:>19}{flag}")
            print()


# ══════════════════════════════════════════════════════════════════════════════
# SELFTEST
# ══════════════════════════════════════════════════════════════════════════════
#
# ⛔⛔ THE CONTROL RUNS FIRST AND THE DISTINCT ARMS ARE COUNTED.  A plant probe
# whose harness is broken reds every plant and reports perfect coverage; the only
# thing that separates that from a working probe is an UNPLANTED run that comes
# out clean, and a count of how many DIFFERENT arms fired.  If one arm catches
# everything, suspect the harness rather than celebrating it.
# [[feedback-a-plant-probes-control-comes-first]]
def _synth(n_commits=12, reps=2, level=100000.0, step=0.0, noise=0.0):
    """A walk with a KNOWN truth AND A BAND IN CLOSED FORM.

    ⛔ THE SPREAD IS PLACED, NOT DRAWN.  Each tree reads `level ± noise/2` between
    the two sweeps — the shape `user_cost_budget._fake_rows` already uses — so the
    median of a side is exactly `level` and the gate's band is exactly
    `K * MEDIAN_SE_FACTOR * noise / sqrt(2)` = 1.772 x noise.  A plant sized
    against a band I have to estimate is a plant I cannot size; with the band in
    closed form every arm below states the k at which it must flip and why.
    [[feedback-size-the-plant-to-the-gate-not-the-phenomenon]]"""
    rows, t = [], 1.0
    for s in range(reps):
        sgn = 1.0 if s == 0 else -1.0
        for i in range(n_commits):
            v = level + step * i + sgn * noise / 2.0
            rows.append({"commit": f"{i:040x}", "sweep": s, "t": t,
                         "secs": 80.0, "load1": 4.0,
                         "modules": {"M": v}, "decls": {}})
            t += 1.0
    return rows


def _band_of(noise):
    """The band `_synth(noise=...)` produces, from the GATE's constants."""
    return kd.K_SIGMA * kd.MEDIAN_SE_FACTOR * noise / math.sqrt(2.0)


def selftest():
    import tempfile
    arms, fired = [], {}

    def arm(name, ok, caught_by=None):
        arms.append((name, ok))
        if caught_by:
            fired.setdefault(caught_by, 0)
            fired[caught_by] += 1
        print(("  ✔ " if ok else "  ✘ ") + name)
        return ok

    def walk_of(rows):
        fd, p = tempfile.mkstemp(suffix=".jsonl")
        with os.fdopen(fd, "w") as fh:
            for r in rows:
                fh.write(json.dumps(r) + "\n")
        return load_walk(p), p

    decl_map, default_ms, budgets, floor = {}, ("abs", 100.0), {}, None
    tmp = []

    print("CONTROL (unplanted) — the harness must be silent here:")
    # ⭐ THE CONTROL: a corpus with real growth well clear of its noise must be
    # DECIDED at k=1.  If this reds, every plant below is meaningless.
    w, p = walk_of(_synth(step=1000.0, noise=10.0)); tmp.append(p)  # band 17.7 << 900
    pk = repair_b(w, decl_map, default_ms, budgets, floor)
    ok_ctrl = arm("a corpus whose steps dwarf its noise is DECIDED at k=1",
                  pk[1]["unmeasurable"] == 0)
    ra = repair_a(w, decl_map, default_ms, budgets, floor, 80.0)
    ok_ctrl &= arm("...and repair A prices nothing, because nothing is refused",
                   ra["unmeasurable"] == 0)
    if not ok_ctrl:
        print("⛔ CONTROL RED — the harness is broken; no plant below carries "
              "information. [[feedback-a-plant-probes-control-comes-first]]")
        for p in tmp:
            os.unlink(p)
        return 1

    print("\nPLANTS — each must be caught, and by a NAMED arm:")

    # ⛔ PLANT 1 + ⭐ PLANT 2 — THE STAIRCASE, SIZED TO THE GATE'S BAND.
    #
    # noise 100 ⇒ band exactly 177.2 (closed form above).  step 180 against a
    # budget of 100 leaves a margin of 80 ms A BATCH, so the accumulated margin
    # is 80k against a band that does not move with k:
    #     k=1  margin  80  <  177.2   UNMEASURABLE   (plant 1: the project's condition)
    #     k=2  margin 160  <  177.2   UNMEASURABLE
    #     k=3  margin 240  >  177.2   OVER           (plant 2: the lever, if real)
    # ⇒ the flip is PREDICTED at k=3 before the run, not read off it.  A "best k"
    # search would have passed on any k at all and told me nothing about where.
    band = _band_of(100.0)
    w, p = walk_of(_synth(step=180.0, noise=100.0)); tmp.append(p)
    pk = repair_b(w, decl_map, default_ms, budgets, floor)
    arm(f"a step whose margin (80) sits under the band ({band:.1f}) is "
        f"UNMEASURABLE at k=1 and k=2",
        pk[1]["unmeasurable"] == pk[1]["n"] and pk[2]["unmeasurable"] == pk[2]["n"],
        "k=1 refusal")
    # ⭐⭐⭐ AND THE ARM ASKS FOR A CONVICTION, NOT MERELY A VERDICT.  "Decided"
    # would be satisfied by the window turning `ok`, which is the reassuring
    # direction and proves nothing about the lever.  This corpus really is over
    # budget every batch — 180 against 100 — and the per-batch gate can only
    # REFUSE it because 80 sits under the band.  The drift gate must CONVICT.
    #
    # ⛔⛔ AND THIS IS THE ONLY PLACE THE LEVER IS DEMONSTRATED AT ALL.  Both real
    # walks return zero OVER at every k (the twelve commits landed, so they are
    # all within budget), so the corpus measures REFUSAL and never DETECTION.
    # Without this plant the k-column would be a table about how often the gate
    # stops shrugging, quoted as if it were about catching regressions.
    # [[feedback-an-implied-assertion-is-not-a-second-gate]]
    arm(f"...and the SAME corpus is CONVICTED at exactly the predicted k=3 "
        f"(margin 240 > {band:.1f}): {pk[3]['over']} OVER of {pk[3]['n']}",
        pk[3]["unmeasurable"] == 0 and pk[3]["over"] == pk[3]["n"],
        "k>1 conviction")

    # ⛔ PLANT 3 — THE ACCUMULATED ALLOWANCE MUST ACCUMULATE.  A corpus growing
    # 40 ms a batch against a 100 ms budget is INSIDE budget forever.  Judged
    # against the accumulated allowance it must read `ok`; judged against ONE
    # batch's budget it starts convicting as soon as 40k - 100 clears the band,
    # i.e. at k=7 (180 > 177.2).  That conviction would be the design's own
    # arithmetic wearing a regression's name, which is the whole reason the
    # allowance is summed rather than fixed.
    w3, p = walk_of(_synth(step=40.0, noise=100.0)); tmp.append(p)
    pk3 = repair_b(w3, decl_map, default_ms, budgets, floor)
    ur = unit_readings(w3, decl_map)
    order = w3["order"]
    flat_over = 0
    for i in range(len(order) - 11):
        bs, hs = ur[order[i]]["M"], ur[order[i + 11]]["M"]
        j = judge(bs, hs, 100.0)        # ⛔ ONE batch's budget for an 11-batch window
        if j["verdict"] == "OVER":
            flat_over += 1
    acc_over = pk3[11]["over"]
    arm(f"an 11-batch window judged against ONE batch's budget CONVICTS "
        f"({flat_over}) where the accumulated allowance does not ({acc_over})",
        flat_over > 0 and acc_over == 0, "flat-allowance conviction")

    # ⛔ PLANT 4 — a unit read once per tree cannot estimate its noise, and must
    # be REFUSED rather than given a band of zero.  This is the hole D141 closed
    # in the gate; a pricing tool that re-opened it would price a corpus the gate
    # would refuse outright.
    w1, p = walk_of(_synth(reps=1, step=50.0, noise=4000.0)); tmp.append(p)
    pk1 = repair_b(w1, decl_map, default_ms, budgets, floor)
    arm("a walk with ONE reading a tree is UNMEASURABLE everywhere "
        "(infinite band), never silently decided",
        pk1[1]["unmeasurable"] == pk1[1]["n"], "single-reading refusal")

    # ⛔⛔ PLANT 5 AND 6 — THE READER'S TARGET IS THE GATE'S OWN CONSTANT, NOT MY
    # GUESS.  This pair first read "rms n=1 / rms n=4 must be ~2.0", which is the
    # ratio for a MEAN.  The estimator is a MEDIAN and the gate registers its
    # penalty itself as `MEDIAN_SE_FACTOR`, so the predicted ratio is
    # `sqrt(4)/1.2533 = 1.596` — and the reader's 1.50 was inside Monte-Carlo
    # error of the right answer while my arm called it a failure.  ⇒ an arm whose
    # target I invent tests my arithmetic, not the tool.  The target below is
    # computed FROM `kd.MEDIAN_SE_FACTOR`, so it moves if the gate's model does.
    # [[feedback-the-burden-is-on-the-departure]] [[feedback-a-control-can-share-the-blind-spot]]
    #
    # ⭐ And the deciding property is COVERAGE, not the shrink rate: the true
    # delta is zero, so the band's job is to contain the error it makes.
    import random
    predicted = 2.0 / kd.MEDIAN_SE_FACTOR

    def scaling_fixture(offset_at=None, sigma=100.0, m=64):
        fd, path = tempfile.mkstemp(suffix=".jsonl")
        tmp.append(path)
        with os.fdopen(fd, "w") as fh:
            for i in range(m):
                off = 0.0 if (offset_at is None or i < offset_at) else 3000.0
                fh.write(json.dumps({"rep": i, "t": float(i), "commit": "x" * 40,
                                     "modules": {"M": 10000.0 + off
                                                 + random.gauss(0, sigma)},
                                     "decls": {}}) + "\n")
        return repeat_scaling(path, {})["M"]

    random.seed(7)
    ind = scaling_fixture()
    ratio = ind["n"][1]["rms_d"] / ind["n"][4]["rms_d"]
    arm(f"on independent noise the reader recovers the gate's own model "
        f"(rms n=1 / rms n=4 = {ratio:.2f} vs predicted "
        f"sqrt(4)/MEDIAN_SE_FACTOR = {predicted:.2f})",
        abs(ratio - predicted) / predicted < 0.25, "scaling recovery")
    mr = ind["n"][4]["max_ratio"]
    arm(f"...and no split exceeds its band by more than a small factor "
        f"(worst |d|/band = {mr:.2f} at n=4)",
        mr is not None and mr < 5.0, "band honesty on independent noise")

    # ⛔ PLANT 6 — a spread that is a per-session OFFSET rather than independent
    # draws.  Repeats inside one session never see it, so the band must stop
    # covering: the splits that straddle the step report a huge |d| against a
    # band estimated from readings that all sit on one side of it.  This is the
    # failure mode that would let repair A's projection name a finite N for a
    # question that no N answers — the projection cannot express a floor, so it
    # always names one.
    random.seed(7)
    off = scaling_fixture(offset_at=32, sigma=5.0)
    r1b, r4b = off["n"][1]["rms_d"], off["n"][4]["rms_d"]
    arm(f"a per-session OFFSET does not shrink with n "
        f"(rms n=1 {r1b:,.0f} → n=4 {r4b:,.0f}; it must not fall)",
        r4b >= r1b, "offset floor")
    # ⛔ AND THE ARM READS THE MAGNITUDE, NOT THE RATE.  This pair first asserted
    # a COVERAGE collapse and read 86% against 89% — because only the block
    # splits that straddle the offset can fail, and that is a fixed small share
    # of the windows however wrong the band is.  The rate was diluted by design;
    # the magnitude was not.
    mrb = off["n"][4]["max_ratio"]
    arm(f"...and the band is exceeded by ORDERS OF MAGNITUDE when the spread is "
        f"an offset (worst |d|/band = {mrb:,.0f} at n=4, vs {mr:.2f} independent)",
        mrb is not None and mrb > 20.0, "band collapse on an offset")

    for p in tmp:
        try:
            os.unlink(p)
        except OSError:
            pass

    bad = [n for n, ok in arms if not ok]
    print(f"\n  {len(arms)} arms, {len(arms) - len(bad)} green; "
          f"{len(fired)} DISTINCT arms caught a plant: {', '.join(sorted(fired))}")
    if len(fired) < 7:
        print("  ⚠️ fewer than five distinct arms fired — suspect the harness "
              "before believing the coverage")
    if bad:
        for n in bad:
            print(f"  ⛔ {n}")
        return 1
    print("  delta_repair_price selftest: CLEAN")
    return 0


def main():
    if "--selftest" in sys.argv:
        return selftest()
    walks = []
    repeat_file = None
    for i, a in enumerate(sys.argv):
        if a == "--walk" and i + 1 < len(sys.argv):
            walks.append(load_walk(sys.argv[i + 1]))
        if a == "--repeat-scaling" and i + 1 < len(sys.argv):
            repeat_file = sys.argv[i + 1]
    if not walks:
        print(__doc__)
        return 2
    default_ms, budgets, floor = kd.read_budgets(BUDGET_FILE)
    decl_map = kd.gated_declarations()
    report(walks, decl_map, default_ms, budgets, floor, repeat_file)
    return 0


if __name__ == "__main__":
    sys.exit(main())
