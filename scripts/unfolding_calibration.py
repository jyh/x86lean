#!/usr/bin/env python3
"""QUEUE 4b — CALIBRATING THE KERNEL UNFOLDING COUNTER OVER WINDOWS, NOT PAIRS.

⚖️ **WHAT THIS ANSWERS.** D148 left item 4b with one blocker of its own making:
*"no budget has been derived: a calibration resting on ONE resolved pair is not a
second source. Do not gate on it before that."* The kernel reference resolved
**1 of 11 adjacent pairs** on the gate's own band, and the `ms per 1k unfoldings`
figure was therefore the single value **7.65**.

The drift gate (D154) supplies the missing ingredient for free: a window of k
batches has a delta that grows with k against a band that does not, so windows
resolve where adjacent pairs refuse. This reads the SAME committed walks over
windows instead of pairs and asks what the calibration looks like once more than
one window is allowed to speak.

## ⭐⭐⭐ THE FINDING: 7.65 IS THE k=1 NUMBER, AND k=1 IS THE MOST SELECTED REGIME

On the quiet night (09/04), module `Tests.Coverage`, ratios in ms per 1k unfoldings:

    k= 1  resolved  1/11   [7.65]                          <- D148's single value
    k= 2  resolved  3/10   [7.65 8.50]
    k= 3  resolved  4/ 9   [2.55 3.32 5.43 8.50]           <- low values start entering
    k= 4  resolved  6/ 8   [2.55 3.23 3.30 3.34 5.93 5.93]
    k= 8  resolved  4/ 4   [3.19 3.26 3.51 3.99]           <- UNSELECTED
    k= 9  resolved  3/ 3   [2.39 3.79 4.12]                <- UNSELECTED
    k=10  resolved  2/ 2   [3.22 3.89]                     <- UNSELECTED
    k=11  resolved  1/ 1   [3.18]                          <- UNSELECTED

⛔⛔ **A RATIO COMPUTED ONLY OVER THE WINDOWS THAT RESOLVED IS COMPUTED OVER THE
WINDOWS WITH THE BIGGEST DELTAS.** At k=1 exactly one window clears its band —
necessarily the one with the largest |delta| relative to it — and its ratio is
7.65. As k rises and the band stops dominating, the newly admitted windows carry
LOW ratios (2.55, 3.23, 3.30 …) and the median falls by half. At k>=8 EVERY
window resolves, so nothing is selected at all, and the calibration sits at
**2.39 - 4.12, median 3.38**.

⇒ **D148's 7.65 is roughly 2x the unselected value, and a budget set from it would
have been about twice too generous.** The number was not wrong as a reading; it
was a reading of the one case that survived a filter correlated with the thing
being measured. This tool prints the resolved FRACTION beside every ratio and
marks the rows where it is 1.0, because that fraction is the only thing that says
whether the ratio is a calibration or a selection.
[[feedback-a-landed-corpus-cannot-measure-detection]]

## ⛔ AND THE SECOND SOURCE STILL DOES NOT CONFIRM IT

The loaded night (09/05, load ~12) NEVER reaches full resolution — at k=11 it
resolves 0 of 1 — and its ratios span **-5.90 to +37.05**, including a SIGN
INVERSION at k=2 where kernel time falls while unfoldings rise. So:

    quiet night, unselected (k>=8)     2.39 - 4.12, 10 windows, median 3.38
    loaded night, best case (k=8)      3.96 - 13.23, 3 of 4 windows, NEVER unselected

⇒ The blocker's first half is lifted — there are now dozens of resolved windows
instead of one — and its second half is NOT: two nights on ONE box disagree by
more than a budget's margin, and machine independence remains unmeasured because
there is no second machine (Actions refuses every job on this account for
billing). **Do not gate on it.** The item's status is unchanged; its REASON is
now measured rather than assumed.

⚠️ **THE TEN UNSELECTED WINDOWS ARE NOT TEN INDEPENDENT MEASUREMENTS.** Over
twelve commits, the k=8..11 windows overlap heavily — they share most of their
span — so they are closer to one or two independent observations wearing nine
names. The tightness of [3.18 … 4.12] is therefore weaker evidence than its
spread suggests. [[feedback-two-readings-are-not-two-witnesses]]

## SCORING THE COUNTER AGAINST A NULL, ON THE SAME RESOLVED SET

D148's head-to-head was scored on a borrowed denominator — heartbeats judged over
the kernel counter's live set. Here all three predictors are scored over exactly
the same resolved windows. A predictor is good if its per-window ratio is
CONSTANT, so the figure of merit is the spread p90/p10:

                                   09/04 (quiet)   09/05 (loaded)
    ms per 1k unfoldings (ku)           2.66            5.42
    ms per 1k heartbeats (hb)        incoherent      incoherent     (p10 negative)
    ms per BATCH (the null)            11.02           26.94

⭐ The null is not a straw man: **`ms per batch` is exactly what the merge gate's
per-batch budget assumes**, so beating it by 4.1x / 5.0x is the claim that a
ku-based budget would predict kernel cost better than the allowance the
repository currently gates on. Heartbeats stay incoherent, which is D146's
refutation reproduced with a shared denominator.

usage:
  unfolding_calibration.py --walk <kernel-delta walk> [--walk ...]
                           --counters <deterministic-cost walk> [--module M]
  unfolding_calibration.py --selftest
"""
import json
import math
import os
import statistics
import sys

# ⛔ REFUSE AN UNKNOWN FLAG BEFORE ANY WORK HAPPENS. This script dispatched on
# `"--x" in sys.argv` and otherwise fell through to its main path, so a mistyped
# flag did not fail — it RAN. Measured 2026-09-09: `threads_ab.py` given a bogus
# flag started `lake env lean -D profiler=true`, saturated a core for 300+ s on a
# shared machine, and orphaned past its caller. See portable.strict_flags.
if __name__ == "__main__":
    import os as _os, sys as _sys
    _sys.path.insert(0, _os.path.dirname(_os.path.abspath(__file__)))
    from portable import strict_flags as _strict_flags
    _strict_flags(__file__)

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import kernel_delta as kd                                        # noqa: E402
import delta_repair_price as drp                                 # noqa: E402
import check_corpus_claims as _ccc                               # noqa: E402  the ROLE rule

DEFAULT_MODULE = "Tests.Coverage"


def flatten(counter, module, names):
    """A per-declaration counter dict, flattened by the GATE's own unit rule.

    ⛔ The same partition `kd.units_of` applies to milliseconds — module total,
    each gated declaration, and the RESIDUE — so that a ratio's numerator and
    denominator describe the same quantity. A counter summed over one partition
    and a time measured over another is a join on a lossy key."""
    total = sum(counter.values())
    out = {module: total}
    named = 0
    for n in names:
        out[f"{module} @decl {n}"] = counter.get(n, 0)
        named += counter.get(n, 0)
    out[f"{module} @residue"] = total - named
    return out


def load_counters(path, module, names):
    # ⛔⛔ THE ROLE IS MEASURED, NOT ASSUMED.  Before this check, handing this
    # function a kernel-delta walk returned `({}, {})` SILENTLY — no row carries
    # `module`, so the filter below dropped all of them and the caller saw an
    # empty answer rather than a refusal.  An empty result and a wrong-corpus
    # result are different facts and only one of them is recoverable.
    # [[feedback-an-unparseable-gate-file-reports-failure-not-absence]]
    rows = [json.loads(l) for l in open(path) if l.strip()]
    role, why = _ccc.corpus_role(rows)
    if role != "counters":
        raise ValueError(
            f"{path} is not a deterministic-cost corpus: it measures as {role!r} "
            f"({why}). This is the --walk/--counters mix-up b5d1522 made in prose; "
            f"see scripts/check_corpus_claims.py.")
    ku, hb = {}, {}
    for r in rows:
        if r.get("module") != module or r.get("error"):
            continue
        ku[r["commit"]] = flatten(r["ku"], module, names)
        hb[r["commit"]] = flatten(r["hb"], module, names)
    return ku, hb


def windows(walk, unit_readings, units, ku, hb):
    """Every (k, window, unit) case with the gate's own band attached."""
    order = walk["order"]
    out = []
    for k in range(1, len(order)):
        for i in range(len(order) - k):
            b, h = order[i], order[i + k]
            if b not in ku or h not in ku:
                continue
            for u in units:
                if u not in unit_readings[b] or u not in unit_readings[h]:
                    continue
                bs, hs = unit_readings[b][u], unit_readings[h][u]
                d = statistics.median(hs) - statistics.median(bs)
                band = kd.K_SIGMA * kd.resolution(bs, hs)
                out.append({
                    "k": k, "unit": u, "d": d, "band": band,
                    "resolved": bool(math.isfinite(band) and abs(d) > band),
                    "dku": ku[h][u] - ku[b][u], "dhb": hb[h][u] - hb[b][u],
                })
    return out


def by_k(cases, unit=None):
    """{k: {n, resolved, fraction, ratios, unselected}} — the fraction is the point."""
    out = {}
    for c in cases:
        if unit is not None and c["unit"] != unit:
            continue
        e = out.setdefault(c["k"], {"n": 0, "resolved": 0, "ratios": []})
        e["n"] += 1
        if c["resolved"]:
            e["resolved"] += 1
            if c["dku"]:
                e["ratios"].append(c["d"] / (c["dku"] / 1000.0))
    for e in out.values():
        e["fraction"] = e["resolved"] / e["n"] if e["n"] else 0.0
        # ⛔ THE ONLY THING THAT SAYS WHETHER A RATIO IS A CALIBRATION OR A
        # SELECTION. At fraction < 1 the ratios come from the windows that cleared
        # their band, which is a filter on the numerator.
        e["unselected"] = e["n"] > 0 and e["resolved"] == e["n"]
    return out


def spread(xs):
    xs = sorted(xs)
    if len(xs) < 4:
        return None
    p10, p90 = xs[int(0.1 * len(xs))], xs[int(0.9 * len(xs))]
    return {"n": len(xs), "median": statistics.median(xs), "p10": p10, "p90": p90,
            "ratio": (p90 / p10) if p10 > 0 else None}


def score_predictors(cases):
    """ku vs hb vs the per-batch null, over EXACTLY the same resolved windows."""
    res = [c for c in cases if c["resolved"]]
    return {
        "ms per 1k unfoldings (ku)": spread([c["d"] / (c["dku"] / 1000.0)
                                             for c in res if c["dku"]]),
        "ms per 1k heartbeats (hb)": spread([c["d"] / (c["dhb"] / 1000.0)
                                             for c in res if c["dhb"]]),
        "ms per BATCH (null)": spread([c["d"] / c["k"] for c in res]),
    }


def report(name, cases, module):
    print(f"\n=== {name} ===")
    print(f"  MODULE ONLY ({module}) — the denominator D148 used")
    print(f"  {'k':>3} {'cases':>6} {'resolved':>9} {'frac':>6}  ratios (ms per 1k unfoldings)")
    for k, e in sorted(by_k(cases, unit=module).items()):
        vs = " ".join(f"{v:.2f}" for v in sorted(e["ratios"]))
        tag = "  ← UNSELECTED" if e["unselected"] else ""
        print(f"  {k:>3} {e['n']:>6} {e['resolved']:>9} {e['fraction']:>6.2f}  [{vs}]{tag}")
    uns = [v for k, e in by_k(cases, unit=module).items() if e["unselected"]
           for v in e["ratios"]]
    if uns:
        print(f"  ⇒ UNSELECTED calibration: {len(uns)} windows, "
              f"{min(uns):.2f} - {max(uns):.2f}, median {statistics.median(uns):.2f}")
        print(f"    ⚠️  these windows OVERLAP and are not independent observations")
    else:
        print("  ⇒ no k reaches full resolution: every ratio here is SELECTED")
    # ⛔⛔ THE SIGN-INVERSION STATISTIC HAS ONLY ONE DIRECTION, AND IT MUST SAY SO.
    # D148 §1 already caught this shape in the sign-AGREEMENT statistic: Δproxy is
    # positive on every live pair, so "sign agreement" was `sum(Δkernel > 0)` under
    # another name. **The INVERSION statistic has the identical defect and nobody had
    # noticed.** Measured 2026-09-09 (D181): among resolved cases with a non-zero Δku,
    # **Δku > 0 in 96 of 96 on the quiet night and 106 of 106 on the loaded one — Δku
    # is NEVER negative**, because this corpus only ever accumulates work. So an
    # "inversion" can only ever be `Δms < 0`, and the count is a count of windows
    # where the NOISY side read negative. It carries nothing about agreement.
    # ⇒ The line now prints its own denominator problem rather than reading as a
    # two-sided disagreement rate. [[feedback-a-claim-the-vectors-cannot-distinguish]]
    res_nz = [c for c in cases if c["resolved"] and c["dku"]]
    neg = sum(1 for c in res_nz if (c["d"] / c["dku"]) < 0)
    dku_neg = sum(1 for c in res_nz if c["dku"] < 0)
    print(f"  sign inversions (Δms and Δku disagree): {neg} of {len(res_nz)} resolved cases")
    if res_nz and dku_neg == 0:
        ks = sorted({c["k"] for c in res_nz if (c["d"] / c["dku"]) < 0})
        print(f"    ⚠️  Δku < 0 in 0 of {len(res_nz)} of them, so an inversion can ONLY be "
              f"Δms < 0: this is a count of windows where the NOISY side read negative, "
              f"NOT a two-sided disagreement rate"
              + (f" (all at k={ks}, where the true delta is smallest)" if ks else ""))
    print(f"  PREDICTORS over the same resolved set (figure of merit: p90/p10, lower is better)")
    for nm, s in score_predictors(cases).items():
        if s is None:
            print(f"    {nm:<28}   (too few)")
        elif s["ratio"] is None:
            print(f"    {nm:<28} n={s['n']:>3} median={s['median']:>9.2f}  "
                  f"p10={s['p10']:>10.2f}  INCOHERENT (p10 <= 0)")
        else:
            print(f"    {nm:<28} n={s['n']:>3} median={s['median']:>9.2f}  "
                  f"p90/p10={s['ratio']:>7.2f}")


# ══════════════════════════════════════════════════════════════════════════════
# SELFTEST
# ══════════════════════════════════════════════════════════════════════════════
def _walk(levels, reps=2, jitter=0.0, unit="M"):
    """A synthetic kernel-delta walk: levels[i] is commit i's true reading."""
    order = [f"{i:040x}" for i in range(len(levels))]
    by = {}
    for i, c in enumerate(order):
        by[c] = [{"modules": {unit: levels[i] + (jitter if r % 2 else -jitter)},
                  "decls": {}} for r in range(reps)]
    return {"order": order, "by": by, "path": "synthetic"}


def _ur(walk, unit="M"):
    return {c: {unit: [r["modules"][unit] for r in rows]}
            for c, rows in walk["by"].items()}


def _sign_warn_fires(cases):
    """True iff report() would print the one-direction warning for `cases`."""
    res = [c for c in cases if c["resolved"] and c["dku"]]
    return bool(res) and sum(1 for c in res if c["dku"] < 0) == 0


def selftest():
    fails, caught, arms = [], [], []

    def ok(cond, what, plant=None):
        print(f"  {'✔' if cond else '✘'} {what}")
        arms.append(what)
        if not cond:
            fails.append(what)
        elif plant:
            caught.append(plant)

    U = "M"
    # ── CONTROL FIRST: ms EXACTLY proportional to unfoldings, no noise.
    print("CONTROL — a corpus where ms = 5.0 x (ku/1000) exactly:")
    # ku_i = 1000*i, so Δku/1000 = Δi; ms_i = 5.0*i makes the ratio exactly 5.0.
    # ⛔ The first spelling asserted 5.0 against a corpus whose true constant was
    # 5000 — the arm was wrong, not the tool, and it went red on the first run.
    n = 8
    kus = [1000 * i for i in range(n)]
    lv = [5.0 * i for i in range(n)]                   # 5 ms per 1k unfoldings
    w = _walk([1000.0 + v for v in lv], jitter=0.01)
    ku = {c: {U: kus[i]} for i, c in enumerate(w["order"])}
    hb = {c: {U: kus[i] * 3} for i, c in enumerate(w["order"])}
    cs = windows(w, _ur(w), [U], ku, hb)
    s = score_predictors(cs)["ms per 1k unfoldings (ku)"]
    ok(s is not None and abs(s["median"] - 5.0) < 1e-6 and abs(s["ratio"] - 1.0) < 1e-6,
       f"the constant is recovered exactly (median {s['median']:.3f}, spread "
       f"{s['ratio']:.3f}) and nothing is flagged selected")
    ok(all(e["unselected"] for e in by_k(cs, U).values()),
       "...and with a negligible band EVERY window resolves, so every row is UNSELECTED")

    # ── THE SELECTION ARM: the finding this tool exists to make visible.
    print("\nSELECTION — one window with a huge delta, the rest inside the band:")
    # eleven steps of +1 ms each (invisible), and ONE step of +900 ms.
    lv2 = [0.0] * 9
    lv2[4] = 900.0
    levels, acc = [], 1000.0
    for d in lv2:
        levels.append(acc)
        acc += d
    levels.append(acc)
    w2 = _walk(levels, jitter=60.0)          # band ~ 100 ms, so only the big step shows
    # unfoldings rise EVENLY: the big ms step is NOT matched by a big ku step, so
    # the selected window's ratio is far above the truth.
    ku2 = {c: {U: 1000 * i} for i, c in enumerate(w2["order"])}
    hb2 = {c: {U: 1000 * i} for i, c in enumerate(w2["order"])}
    cs2 = windows(w2, _ur(w2), [U], ku2, hb2)
    tab = by_k(cs2, U)
    k1 = tab[1]
    ok(k1["fraction"] < 1.0 and not k1["unselected"],
       f"at k=1 only {k1['resolved']} of {k1['n']} windows resolve, and the row is "
       f"NOT marked unselected", plant="selection flagged")
    wide = [e for k, e in tab.items() if e["unselected"]]
    ok(len(wide) > 0, "...while a wide enough window reaches full resolution and IS "
                      "marked unselected", plant="unselected flagged")
    if k1["ratios"] and wide and wide[-1]["ratios"]:
        ok(statistics.median(k1["ratios"]) > statistics.median(wide[-1]["ratios"]),
           f"...and the SELECTED k=1 ratio ({statistics.median(k1['ratios']):.1f}) sits "
           f"ABOVE the unselected one ({statistics.median(wide[-1]['ratios']):.1f}) — the "
           f"defect D148 banked as a calibration", plant="selection inflates the ratio")

    # ── THE NULL MUST BE ABLE TO WIN, or "ku beats the null" is a fact about the
    # scoring and not about the counter. [[feedback-score-the-null-model]]
    print("\nTHE NULL CAN WIN — a corpus where cost is per-BATCH and ku is noise:")
    lv3 = [1000.0 + 100.0 * i for i in range(9)]         # exactly 100 ms per batch
    w3 = _walk(lv3, jitter=0.01)
    scatter = [1, 97, 13, 61, 7, 89, 23, 53, 3]
    ku3 = {c: {U: 1000 * scatter[i]} for i, c in enumerate(w3["order"])}
    cs3 = windows(w3, _ur(w3), [U], ku3, ku3)
    sc = score_predictors(cs3)
    # an INCOHERENT spread (p10 <= 0, so the ratio is None) is the worst outcome,
    # not a missing one: `None` must compare as infinitely bad rather than crash.
    def badness(x):
        return float("inf") if (x is None or x["ratio"] is None) else x["ratio"]
    nb, kb = badness(sc["ms per BATCH (null)"]), badness(sc["ms per 1k unfoldings (ku)"])
    ok(nb < kb,
       f"the null WINS where cost really is per-batch (null spread {nb:.2f} < ku "
       f"{'incoherent' if kb == float('inf') else format(kb, '.2f')}) — so 'ku beats "
       f"the null' on the real corpus is a fact about the counter, not the scoring",
       plant="null can win")

    # ── a side with one reading cannot estimate its noise ⇒ nothing resolves.
    print("\nTHE BAND — one reading a side:")
    w4 = _walk([1000.0, 2000.0], reps=1)
    cs4 = windows(w4, _ur(w4), [U], {c: {U: 1000} for c in w4["order"]},
                  {c: {U: 1000} for c in w4["order"]})
    ok(cs4 and not any(c["resolved"] for c in cs4),
       "nothing resolves with one reading a side (infinite band), so no ratio is "
       "computed from an unmeasurable delta", plant="single-reading refusal")

    print()
    if fails:
        print(f"⛔ unfolding-calibration selftest: {len(fails)} FAILED")
        for f in fails:
            print(f"   ✘ {f}")
        return 1
    print(f"  {len(arms)} arms, {len(arms) - len(fails)} green; {len(caught)} DISTINCT "
          f"arms caught a plant: {', '.join(caught)}")
    # ⛔ D181's arm: the one-direction warning must fire when Δku is single-signed
    # and must NOT fire when it is not. Without the second drive the warning would be
    # an assertion no input can contradict [[feedback-an-implied-assertion-is-not-a-second-gate]].
    _one = [{"resolved": True, "dku": +5, "d": -1.0, "k": 2, "band": 0.1},
            {"resolved": True, "dku": +7, "d": +9.0, "k": 3, "band": 0.1}]
    _two = _one + [{"resolved": True, "dku": -3, "d": +2.0, "k": 4, "band": 0.1}]
    _a = _sign_warn_fires(_one)
    _b = _sign_warn_fires(_two)
    print(("  \u2714 " if _a else "  \u2716 ") +
          "RED-FIRST — a single-signed Δku set RAISES the one-direction warning, so "
          "the inversion count is never read as a two-sided disagreement rate")
    print(("  \u2714 " if not _b else "  \u2716 ") +
          "CONTROL — a set containing a NEGATIVE Δku does NOT raise it, so the warning "
          "is a measurement and not a constant")
    if not _a or _b:
        return 1

    print("unfolding-calibration selftest: CLEAN — the SELECTION rule and the "
          "predictor scoring only; no walk is read and no tree is profiled.")
    return 0


def walk_origins(path):
    """What machines a walk says it came from — from the DATA, never assumed.

    Two signals, in order of strength:
      * `origin`      — added 2026-09-09; walks written before it lack the field.
      * `load_source` — an ALL-None load column cannot have been produced on a
                        POSIX box, because `os.getloadavg()` exists on every one.
                        D185 §3: the field added to record an absence honestly
                        turned out to be a provenance signature.
    """
    out = set()
    rows = [json.loads(l) for l in open(path, encoding="utf-8") if l.strip()]
    named = {r["origin"] for r in rows if r.get("origin")}
    if named:
        return named
    if rows and all(r.get("load1") is None for r in rows):
        out.add("unnamed, non-POSIX (all-None load column)")
    elif rows:
        out.add("unnamed, POSIX (load column present)")
    return out


def provenance_note(origins):
    """⛔⛔ THIS REPLACED A HARD-CODED SENTENCE THAT WAS FALSE BY THE TIME IT MATTERED.

    Until 2026-09-09 `main()` ended with an unconditional
        "One box, arm64. Machine independence is UNMEASURED and remains item 4b's
         standing blocker; this tool cannot address it."
    printed regardless of which walk had just been read. It was written when it was
    true, and D183 (a plant) then D185 (the corpus: 1,236 declaration readings, 12
    of 12 commits, exact integer equality across arm64-macOS and x86_64-Windows)
    made both halves wrong — while the tool went on asserting the blocker that the
    runs beneath it existed to help clear.
    ⇒ 🔑 **A TOOL'S OUTPUT IS READ BY PEOPLE WHO WILL NOT READ ITS SOURCE, SO A
    STALE SENTENCE IN A FOOTER IS QUOTED WHERE A STALE COMMENT IS NOT.**
    So this one is DERIVED from the walks actually read, and the part that is still
    a standing claim is stated as what it is.
    """
    who = ", ".join(sorted(origins)) or "no walk read"
    return (f"\n📌 walk provenance, from the data: {who}"
            f"\n⚠️  WHAT THIS TOOL STILL CANNOT ADDRESS, and it is not machine"
            f" independence:\n"
            f"    machine independence is MEASURED (D183 plant; D185 corpus, 1,236"
            f" readings, exact\n"
            f"    equality across arm64-macOS and x86_64-Windows). Item 4b's"
            f" remaining blockers are\n"
            f"    (a) no budget from a second SOURCE — a second USABLE calibration"
            f" night — and\n"
            f"    (b) no evidence that the counter TRACKS KERNEL TIME, which is the"
            f" claim 4b rests on.\n"
            f"    A band printed above is a reading from THIS walk; it is neither"
            f" of those two things.")


def main():
    if "--selftest" in sys.argv:
        return selftest()
    counters = kd.arg("--counters")
    walks = [sys.argv[i + 1] for i, a in enumerate(sys.argv) if a == "--walk"]
    if not counters or not walks:
        print(__doc__)
        return 2
    module = kd.arg("--module", DEFAULT_MODULE)
    decl_map = kd.gated_declarations()
    names = decl_map.get(module, [])
    ku, hb = load_counters(counters, module, names)
    if not ku:
        print(f"⛔ no usable rows for module {module!r} in {counters}. A calibration "
              f"with no counters is not a calibration; check --module.")
        return 2
    units = [module] + [f"{module} @decl {n}" for n in names] + [f"{module} @residue"]
    origins = set()
    for path in walks:
        w = drp.load_walk(path)
        origins |= walk_origins(path)
        cs = windows(w, drp.unit_readings(w, decl_map), units, ku, hb)
        report(os.path.basename(path), cs, module)
    print(provenance_note(origins))
    return 0


if __name__ == "__main__":
    sys.exit(main())
