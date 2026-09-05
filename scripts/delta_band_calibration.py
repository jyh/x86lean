#!/usr/bin/env python3
"""THE MEASUREMENT THAT CHOSE `K_SIGMA`, KEPT RUNNABLE (D141).

`scripts/kernel_delta.py` refuses a verdict when its uncertainty band straddles
the budget, and the width of that band is `K_SIGMA` standard errors. K is the one
free number in the rule, and a free number in a gate is exactly the kind that
gets chosen by what it says about the commit in front of the person choosing.

⛔ SO IT WAS NOT CHOSEN THAT WAY, AND THIS FILE IS WHY THAT CLAIM IS CHECKABLE.
K was fixed by the two error rates it delivers, swept over a per-reading noise
from a quiet box to a loud one, against a commit whose TRUE delta is known
because this harness generates it. No reading here comes from any tree.

⭐ AND IT IS A GATE, NOT A TABLE. `--check` asserts the bounds the docstring of
`kernel_delta.py` quotes, so the prose cannot drift away from the arithmetic it
describes: a paragraph naming a rate reads AS the rate, and nothing was checking
this one. The seed is fixed, so `--check` is deterministic.

usage: delta_band_calibration.py --table    the full sweep, all three rules
       delta_band_calibration.py --check    assert the quoted bounds (CI)
"""
import math, random, statistics, sys, os

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
_kd = os.path.join(os.path.dirname(os.path.abspath(__file__)), "kernel_delta.py")

# ⛔ THE CONSTANTS COME FROM THE GATE, NOT FROM A COPY OF THEM. Two lists that
# agree today diverge on the next ordinary edit to one of them, and this file's
# whole job is to be about the shipped rule.
_src = open(_kd).read()
def _const(name):
    for line in _src.splitlines():
        if line.startswith(name + " ="):
            return float(line.split("=")[1].split("#")[0].strip())
    print(f"⛔ {name} is no longer a module-level constant of kernel_delta.py, so "
          f"this calibration is not about the shipped rule. Refusing.")
    sys.exit(2)
K_SIGMA        = _const("K_SIGMA")
MEDIAN_SE_FACTOR = _const("MEDIAN_SE_FACTOR")

BUDGET, BASE, TRIALS, SEED = 1778.4, 24700.0, 4000, 11
SIGMAS = (200.0, 1000.0, 2000.0)
NS     = (3, 6, 10, 16, 24)
TRUTHS = (("0 (harmless)", 0.0), ("0.5x budget", 0.5), ("1x (on the line)", 1.0),
          ("2x budget", 2.0))


def se(bs, hs):
    return MEDIAN_SE_FACTOR * math.sqrt(statistics.variance(bs) / len(bs) +
                                        statistics.variance(hs) / len(hs))

def v_range(bs, hs):
    """The rule this gate shipped until D141: refuse on the within-side RANGE."""
    sp = max(max(bs) - min(bs), max(hs) - min(hs))
    if BUDGET < sp:
        return "REFUSE"
    return "FAIL" if statistics.median(hs) - statistics.median(bs) > BUDGET else "ok"

def v_band(bs, hs, k):
    d, u = statistics.median(hs) - statistics.median(bs), se(bs, hs)
    if d - k * u > BUDGET: return "FAIL"
    if d + k * u < BUDGET: return "ok"
    return "REFUSE"

RULES = [("OLD range", v_range),
         ("BAND K=1", lambda b, h: v_band(b, h, 1.0)),
         (f"BAND K={K_SIGMA:g}", lambda b, h: v_band(b, h, K_SIGMA))]


def cell(rule, n, sigma, true_delta):
    rng = random.Random(SEED)          # identical draws for every rule
    c = {"ok": 0, "FAIL": 0, "REFUSE": 0}
    for _ in range(TRIALS):
        bs = [rng.gauss(BASE, sigma) for _ in range(n)]
        hs = [rng.gauss(BASE + true_delta, sigma) for _ in range(n)]
        c[rule(bs, hs)] += 1
    return {k: v / TRIALS for k, v in c.items()}


def sweep():
    out = {}
    for nm, rule in RULES:
        for sigma in SIGMAS:
            for tname, mult in TRUTHS:
                for n in NS:
                    out[(nm, sigma, tname, n)] = cell(rule, n, sigma, mult * BUDGET)
    return out


def table(res):
    print(f"budget {BUDGET:.1f} ms on a {BASE:.0f} ms base · {TRIALS} trials a cell · "
          f"seed {SEED} · identical draws for every rule")
    for sigma in SIGMAS:
        print(f"\n=== per-reading sigma {sigma:.0f} ms")
        print(f"{'true delta':>17}{'n':>4}" +
              "".join(f"{nm + '  ok/FAIL/REFUSE':>30}" for nm, _ in RULES))
        for tname, _ in TRUTHS:
            for n in NS:
                row = f"{tname:>17}{n:>4}"
                for nm, _ in RULES:
                    c = res[(nm, sigma, tname, n)]
                    row += (f"{c['ok']*100:>11.0f}%{c['FAIL']*100:>8.0f}%"
                            f"{c['REFUSE']*100:>8.0f}%")
                print(row)


# ⛔⛔ THE BOUNDS THE GATE'S OWN DOCSTRING QUOTES. Each is checked in BOTH
# directions where both exist: a rule that refused everything would satisfy every
# "false pass" bound trivially, so the liveness bounds below are not decoration —
# they are what stops the safe answer from being the empty one.
def check(res):
    band = f"BAND K={K_SIGMA:g}"
    # ⛔ THE COUNT IS DERIVED, NOT TYPED. `.github/workflows/ci.yml` carries this
    # repository's own ruling on it — a step label said "seven planted bugs" for
    # seven batches while there were thirty-eight (D41) — and the first draft of
    # THIS file said "9 bounds" as a literal in two places, in a file written to
    # stop a number drifting away from what produces it.
    asserted, bad = [], []
    def want(cond, msg):
        print(("  ✔ " if cond else "  ⛔ ") + msg)
        asserted.append(msg)
        if not cond: bad.append(msg)

    fp = max(res[(band, s, "2x budget", n)]["ok"] for s in SIGMAS for n in NS)
    want(fp <= 0.01, f"a FALSE PASS on a commit truly at 2x its budget: "
                     f"{fp*100:.1f}% ≤ 1.0% over every sigma and n")
    fr = max(res[(band, s, "0 (harmless)", n)]["FAIL"] for s in SIGMAS for n in NS)
    want(fr <= 0.01, f"a FALSE RED on a commit truly at zero: {fr*100:.1f}% ≤ 1.0%")
    onln = min(res[(band, s, "1x (on the line)", n)]["REFUSE"] for s in SIGMAS for n in NS)
    want(onln >= 0.85, f"a commit exactly ON its budget REFUSES at least "
                       f"{onln*100:.0f}% of the time (≥ 85%), instead of being called")

    # ⭐ LIVENESS, WHICH IS THE HALF A REFUSING GATE PASSES FOR FREE.
    q = res[(band, 200.0, "0 (harmless)", 3)]["ok"]
    want(q >= 0.99, f"on a QUIET box a harmless commit is CLEAN at three repeats: "
                    f"{q*100:.0f}% ≥ 99%")
    conv = [res[(band, 1000.0, "0 (harmless)", n)]["ok"] for n in NS]
    want(all(x <= y + 1e-9 for x, y in zip(conv, conv[1:])) and conv[-1] >= 0.95,
         f"and BUYING REPEATS BUYS A VERDICT — {' → '.join(f'{x*100:.0f}%' for x in conv)} "
         f"clean over n = {NS}, monotone and ≥ 95% at the end")

    # ⛔⛔ THE COMPARISON THAT IS THE WHOLE REASON D141 EXISTS: the OLD rule's
    # refusal rate RISES with the repeats it told the operator to buy, and ends
    # at certainty. If this ever stops being true of the old rule, the finding
    # this file records was wrong and the paragraph quoting it must go.
    old = [res[("OLD range", 1000.0, "0 (harmless)", n)]["REFUSE"] for n in NS]
    want(all(x <= y + 1e-9 for x, y in zip(old, old[1:])) and old[-1] >= 0.99,
         f"the OLD range rule goes the other way: {' → '.join(f'{x*100:.0f}%' for x in old)} "
         f"REFUSED over the same n — monotone UP, to certainty")
    oldflip = res[("OLD range", 200.0, "1x (on the line)", 3)]
    want(oldflip["REFUSE"] == 0 and 0.4 <= oldflip["ok"] <= 0.6,
         f"and on a quiet box it called a commit ON its budget by coin flip: "
         f"ok {oldflip['ok']*100:.0f}% / FAIL {oldflip['FAIL']*100:.0f}% / "
         f"refused {oldflip['REFUSE']*100:.0f}%")

    # ⛔⛔ AND D141's HEADLINE TABLE, WHICH WAS PROSE NOTHING RE-DERIVED. The
    # decision record prints a range that GROWS with n beside an estimate whose
    # sd FALLS with n, and that opposition is the entire finding; a paragraph is
    # where a claim's negation gets written, so the two directions are asserted
    # here from the same draws the rest of this file uses.
    # ⚠️ AND THESE TWO BOUNDS ARE ABOUT THE STATISTICS, NOT ABOUT THE SHIPPED
    # RULE. Nothing in them calls `kernel_delta.py`; a green here says the table
    # in D141 §1 is re-derivable, and says nothing whatever about whether the
    # gate implements the band correctly. The seven bounds above are the ones
    # that read the shipped constant. Kept apart on purpose, because a suite
    # whose arms mean different things is read as if they all meant the strongest
    # one.
    import statistics as _st
    rng_of, sd_of = [], []
    for n in NS:
        r = random.Random(SEED)
        ranges, ests = [], []
        for _ in range(TRIALS // 4):
            bs = [r.gauss(BASE, 1400.0) for _ in range(n)]
            hs = [r.gauss(BASE + 1000.0, 1400.0) for _ in range(n)]
            ranges.append(max(max(bs) - min(bs), max(hs) - min(hs)))
            ests.append(_st.median(hs) - _st.median(bs))
        rng_of.append(_st.mean(ranges))
        sd_of.append(_st.stdev(ests))
    want(all(x < y for x, y in zip(rng_of, rng_of[1:])),
         "the READINGS' range RISES with the repeats: "
         + " → ".join(f"{x:.0f}" for x in rng_of))
    want(all(x > y for x, y in zip(sd_of, sd_of[1:])),
         "while the sd of the GATED ESTIMATE falls: "
         + " → ".join(f"{x:.0f}" for x in sd_of)
         + "  ⇒ the two move in opposite directions, which is D141")

    if bad:
        print(f"\n⛔ delta-band calibration: FAIL ({len(bad)} of {len(asserted)} bounds) — the rule no "
              f"longer delivers what kernel_delta.py's docstring says it does.")
        return 1
    print(f"\ndelta-band calibration: PASS ({len(asserted)} bounds, K_SIGMA={K_SIGMA:g} read from "
          f"the shipped gate, no measurement of any tree in this run)")
    return 0


if __name__ == "__main__":
    res = sweep()
    if "--check" in sys.argv:
        sys.exit(check(res))
    table(res)
    if "--table" not in sys.argv:
        print("\n(--check asserts the bounds; --table is this printout)")
