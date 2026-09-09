#!/usr/bin/env python3
"""THE DELTA GATE — the only kernel-time verdict this box can honestly reach.

⚖️ **RULED BY THE HELM, 2026-09-04 21:42**, on the evidence of D111, D121 and
D122: *"the absolute ceilings are retired as a MERGE GATE and kept as READINGS
printed beside every merge (the two numbers, box-stamped); D111's delta method is
the gate — you set the per-batch delta budget from your own batch history, print
the last ten batches' deltas, budget = a stated multiple of their median with the
reason, register it in the repo's CI as the check that runs, red-first driven (a
planted constructor that doubles the delta must fail)."*

## WHY THE ABSOLUTE CEILINGS COULD NOT STAY THE GATE

`scripts/kernel_ceilings.txt` holds absolute millisecond ceilings, and on this
machine the UNCHANGED PARENT of the batch under test was already over two of them
(D122): `Tests.Coverage`'s residue on master, in band, and `X86.Syntax` at 198 of
200 — a **two-millisecond margin**, which the next AST constructor of any kind
crosses. A gate no commit can pass reports the same red for a good batch and a
bad one, and the across-session shift at ONE commit was measured at 11% while the
margin was 6% (D111).

⇒ 🔑 **A CEILING WHOSE MARGIN IS UNDER THE MACHINE'S OWN SPREAD REPORTS THE
MACHINE, NOT THE CODE.** The absolutes are still printed here, box-stamped, as
readings — a reading is not a verdict, and this file is careful never to let one
read as the other.

## WHAT THIS GATE MEASURES

The CHANGE in kernel (type-checking) time that a commit introduces, between two
trees profiled in ONE session on ONE box, with the passes ALTERNATED
(base, head, base, head, …) so that a load that drifts through the run biases
both sides equally instead of one of them.

The gated units are every module's kernel total, plus — for a module that gates
declarations in `kernel_ceilings.txt` — each of those declarations and the
RESIDUE (module total minus them). Every unit is gated: a unit named in
`scripts/kernel_delta_budget.txt` gets its own budget, and a unit that is not
named falls to the file's `@default`. ⛔ There is no third case — a unit with
neither is an ERROR, because a declared list's gaps all fall the way its default
points and that direction is the one nobody polices.

## THE THREE VERDICTS, AND WHY THE MIDDLE ONE EXISTS

* **CLEAN** — every unit's delta is within its budget.
* **FAILED** (rc 1) — some unit's delta exceeds its budget. The code got more
  expensive to check by more than the batch history says a batch costs.
* **UNMEASURABLE** (rc 3) — the run's own uncertainty BAND around the delta
  straddles the budget, so this run cannot tell which side of it the commit is
  on. That is not a verdict about the commit and must not be reported as one.

⭐ The third verdict is what replaces `kernel_cost.py`'s load-average band, and it
is strictly better evidence: that band is a HEURISTIC about the machine calibrated
on four readings months of batches ago, while this is the machine's noise
MEASURED IN THE SAME RUN, on the same trees, by the same profiler. A gate that
can measure its own noise does not need to guess at it from `uptime`.

## ⛔⛔ D141 — THE REFUSAL TEST THIS FILE SHIPPED FOR ITS FIRST NINE BATCHES, AND
## WHY IT WAS A GATE THAT COULD ONLY DIE

Until 2026-09-05 the refusal was `budget < spread`, where `spread` was the worst
WITHIN-SIDE RANGE (`max - min`) of the repeats — and the refusal printed the
advice *"re-run with more `--repeats` or on a quieter box"*.

⛔ A RANGE GROWS WITH THE NUMBER OF READINGS. The gated quantity — a difference
of MEDIANS — gets BETTER with more readings, at 1/sqrt(n). So of the two remedies
the gate offered, the one under the seat's own control made the refusal STRICTLY
MORE LIKELY, and only the one outside its control could ever help. Measured
through this file's own `verdict()`, on synthetic readings with a true delta of
1,000 ms, per-reading sigma 1,400 ms, against the real 1,778 ms budget:

    n:                        2      3      4      6      8     10     16     24
    REFUSE rate:            60%    84%    96%   100%   100%   100%   100%   100%
    mean spread (max-min): 2257   3053   3528   4210   4579   4915   5501   6024
    sd of the gated estimate:1445  1313   1035    946    846    748    613    504

⇒ 🔑 **THE INSTRUMENT GOT MONOTONICALLY BETTER AND THE GATE GOT MONOTONICALLY
MORE CERTAIN THAT IT COULD NOT SEE.** Batch 32 sat on a branch for a day and a
half against a refusal whose only stated escape was a quiet box that never came.

⛔ AND THE SECOND HALF, WHICH IS WORSE, BECAUSE IT IS A FALSE VERDICT RATHER THAN
NO VERDICT. On a QUIET box (sigma 200 ms) the old rule refused nothing — and on a
commit sitting exactly ON its budget it returned `ok` 50% of the time and
`OVER BUDGET` 49%, a COIN FLIP delivered as a verdict, on precisely the commits
the gate exists to judge. A range that is small says the readings agreed; it
never said the delta was far enough from the budget to call.

## THE RULE NOW: A BAND, NOT A THRESHOLD

Every unit's delta carries the uncertainty of its own estimator, computed from
this run's readings alone:

    se(unit) = 1.2533 * sqrt( s_base^2 / n_base  +  s_head^2 / n_head )

(`1.2533` is the asymptotic ratio of the median's standard error to the mean's
for a normal sample; it is CONSERVATIVE for the small n this gate runs at — the
true ratio at n=3 is 1.16.) The verdict is then the three-way question the three
verdicts were always describing:

    delta - K*se > budget          ⇒ FAILED       (over, beyond this run's noise)
    delta + K*se < budget          ⇒ ok           (under, beyond this run's noise)
    otherwise                      ⇒ UNMEASURABLE (this run cannot tell)

with **K = 2**, a stated convention and the more conservative of the two levels
measured. ⛔ K WAS NOT CHOSEN BY WHAT IT SAYS ABOUT ANY BATCH — deriving it from
the commit under test is the one move this file already forbids for the budget.
It was chosen on the two error rates, swept over sigma in {200, 1000, 2000} ms
and n in {3, 6, 10, 16, 24}, 4,000 trials a cell, identical draws for every rule:

    a FALSE PASS  (`ok` on a commit truly at 2x its budget):  K=2 0.5%, K=1 2.7%
    a FALSE RED   (`FAILED` on a commit truly at zero):       K=2 0.5%, K=1 3.0%
    on a commit exactly ON the budget:  K=2 refuses 92-96%; the OLD rule refused
                                        0% on a quiet box and split 50/49.

⛔ THOSE FOUR FIGURES ARE THE WORST CELL OF THE SWEEP, NOT A ROUNDING OF IT. The
first draft of this paragraph read "K=2 ≤ 0%, K=1 ≤ 2%" — copied off a probe that
printed integer percentages, before `delta_band_calibration.py` computed them
exactly, and never reconciled with it. Both were over-claims by the width of the
truncation, in the file the calibration exists to describe. The gate asserts
≤ 1.0% on the two K=2 figures; run it rather than trusting this line.

⭐ AND THE REMEDY IS NOW REAL AND PRICED. `se` falls as 1/sqrt(n), so a refusal
names the number of repeats that would decide the question and this gate prints
it. The old rule's cost to a verdict was infinite; this one's is arithmetic.

⚠️ The drift the alternated passes exist to cancel INFLATES the within-side `s`,
so `se` over-states the uncertainty of a delta the alternation already protected.
That is the conservative direction and it is stated rather than corrected: a
correction would need the paired differences, and with the passes ordered
base,head,base,head each pair carries a one-pass bias that the medians do not.

## WHAT IT DOES NOT DO

⛔ It does not touch the working tree. Both sides are detached worktrees under
`TMPDIR`, removed at the end. A probe that writes the repository makes
`git add -A` a race, and that race pushed a planted defect to both remotes once
already (D75).

⛔ It does not derive any budget from the commit under test. The budget comes
from `scripts/kernel_delta_budget.txt`, whose numbers are the measured deltas of
the TEN PRECEDING BATCHES (`scripts/kernel_delta_history.py`), and the commit
under test contributes nothing to its own allowance.

usage:
  kernel_delta.py [--base REV] [--head REV] [--repeats N] [--budget FILE]
  kernel_delta.py --readings FILE            re-run the VERDICT over saved readings
  kernel_delta.py --selftest                 the comparison arms (seconds)
  kernel_delta.py --selftest-measure         the two arms that need real trees
"""
import os, re, sys, math, json, time, shutil, socket, platform, statistics, subprocess, tempfile, random

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

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
KCOST = os.path.join(ROOT, "scripts", "kernel_cost.py")
BUDGET_FILE = os.environ.get("X86LEAN_DELTA_BUDGET",
                             os.path.join(ROOT, "scripts", "kernel_delta_budget.txt"))
CEIL_FILE = os.path.join(ROOT, "scripts", "kernel_ceilings.txt")
DEFAULT_TAG = "@default"
FLOOR_TAG   = "@floor"


def arg(name, default=None):
    for i, a in enumerate(sys.argv):
        if a == name and i + 1 < len(sys.argv):
            return sys.argv[i + 1]
    return default


def git(*a, cwd=ROOT, check=True):
    r = subprocess.run(["git"] + list(a), cwd=cwd, capture_output=True, text=True)
    if check and r.returncode != 0:
        print(f"⛔ git {' '.join(a)} failed in {cwd}:\n{r.stdout}\n{r.stderr}")
        sys.exit(2)
    return r.stdout.strip()


# ⭐ THE GATED DECLARATIONS COME FROM THE CEILING FILE, so the delta gate and the
# reading gate are talking about the SAME declarations. Two lists that agree
# today diverge on the next ordinary append to one of them, and the divergence is
# silent in whichever direction nobody is looking.
def gated_declarations():
    """{module: [decl, …]} exactly as `kernel_ceilings.txt` gates them."""
    out = {}
    if os.path.exists(CEIL_FILE):
        for line in open(CEIL_FILE):
            p = line.split("#")[0].strip().split()
            if len(p) == 4 and p[1] == "@decl":
                out.setdefault(p[0], []).append(p[2])
    return out


# ⭐⭐⭐ A BUDGET MAY BE ABSOLUTE OR RELATIVE, AND THE RELATIVE ONE IS THE PORTABLE
# HALF.  This is the whole reason the delta method can be registered on a runner
# when the absolute ceilings could not.
#
# `.github/workflows/ci.yml` records why the ceilings cannot travel: the same
# tree profiled on a GitHub runner and locally differs by a factor that VARIES
# PER MODULE — 1.7x on `memDestSweep`, 3.1x on `vectorCoverage`, 2.1x overall —
# so no single calibration constant exists and raising the ceilings to fit would
# leave them ~2x slack where batches are developed.
#
# ⇒ 🔑 THE VERY FACT THAT REFUTES A PORTABLE CEILING IS WHAT MAKES A PORTABLE
# RATIO WORK.  That factor is a property of (machine, unit); a RATIO of two
# readings of the SAME unit on the SAME machine divides it out exactly, whatever
# its value, because it appears in the numerator and the denominator.
#
# ⚠️ AND THAT IS A PREDICTION, NOT A MEASUREMENT.  It follows from the factor
# being multiplicative and stable within one session, which the CI table supports
# for ABSOLUTE readings but which nothing has yet tested for a matched DELTA on
# two machines — this account has no runner (GitHub Actions refuses every job for
# billing, desk FH). The first delta this gate prints on a runner is that test,
# and it is the reading to compare with the local one, not to trust.
#
# ⛔ A RATIO IS MEANINGLESS ON A UNIT TOO SMALL TO MEASURE.  `X86.Flags` reads
# 2.4 ms; 8% of it is 0.2 ms, well under the run-to-run spread of anything. So a
# relative budget is floored by `@floor`, an absolute number, and a unit whose
# floor still cannot beat the measured spread REFUSES rather than passing.
def read_budgets(path):
    """(default, {unit: budget}, floor_ms) where a budget is ("abs"|"rel", value).

    ⛔ THE BUDGET IS THE LAST FIELD AND THE UNIT IS EVERYTHING BEFORE IT, because
    a unit name legitimately contains spaces (`Tests.Coverage @decl memDestSweep`)
    and a positional split would bet that it never grows another word."""
    if not os.path.exists(path):
        print(f"⛔ no budget file at {path}. A delta gate with no allowance is not "
              f"a gate; run scripts/kernel_delta_history.py and register one.")
        sys.exit(2)
    default, per, floor = None, {}, None
    for line in open(path):
        line = line.split("#")[0].strip()
        if not line:
            continue
        parts = line.rsplit(None, 1)
        if len(parts) != 2:
            print(f"⛔ unparseable budget line: {line!r}")
            sys.exit(2)
        unit, val = parts[0].strip(), parts[1]
        kind = "rel" if val.endswith("%") else "abs"
        try:
            v = float(val[:-1] if kind == "rel" else val)
        except ValueError:
            print(f"⛔ budget line does not end in a number or a percentage: {line!r}")
            sys.exit(2)
        if unit == FLOOR_TAG:
            if kind != "abs":
                print(f"⛔ {FLOOR_TAG} must be absolute milliseconds: {line!r}")
                sys.exit(2)
            floor = v
        elif unit == DEFAULT_TAG:
            default = (kind, v)
        else:
            per[unit] = (kind, v)
    if floor is None and (default and default[0] == "rel"
                          or any(k == "rel" for k, _ in per.values())):
        print(f"⛔ a relative budget is registered but no {FLOOR_TAG}. A percentage "
              f"of a two-millisecond module is not an allowance, it is a rounding "
              f"error, and a gate whose budget is under its own noise reports the "
              f"machine.")
        sys.exit(2)
    return default, per, floor


def effective(budget, base, floor):
    """A budget's value in milliseconds for one unit's base reading."""
    kind, v = budget
    return v if kind == "abs" else max(v / 100.0 * base, floor or 0.0)


def units_of(reading, decl_map):
    """The gateable quantities of ONE reading, flattened to {unit: ms}."""
    out = dict(reading["modules"])
    for mod, names in decl_map.items():
        total = reading["modules"].get(mod)
        if total is None:
            continue
        got = reading.get("decls", {}).get(mod, {})
        named = 0.0
        for n in names:
            if n in got:
                out[f"{mod} @decl {n}"] = got[n]
                named += got[n]
        out[f"{mod} @residue"] = total - named
    return out


# ⭐⭐⭐ THE UNCERTAINTY OF THE QUANTITY THE GATE ACTUALLY TESTS (D141).
#
# ⛔ NOT the spread of the readings — the spread of the ESTIMATE. The gate does
# not compare a reading to a budget, it compares `median(head) - median(base)`,
# and that number's noise falls as 1/sqrt(n) while the readings' RANGE rises. A
# refusal test built on the range therefore gets more certain as the instrument
# gets better, which is how this gate spent its ninth batch refusing everything.
#
# ⛔ A SIDE WITH FEWER THAN TWO READINGS CANNOT ESTIMATE ITS OWN NOISE and this
# returns infinity, so the gate REFUSES. The old range statistic returned 0.0
# there — `max - min` of one reading — so `--repeats 1` could never refuse and
# the gate delivered a verdict off a single pass per side with nothing at all
# said about its noise. That hole is closed by the same change that opens the
# remedy, and it is the direction nobody was looking.
K_SIGMA = 2.0
MEDIAN_SE_FACTOR = 1.2533   # SE(median)/SE(mean), normal, asymptotic; conservative at small n


def resolution(bs, hs):
    """The standard error of `median(hs) - median(bs)`, from these readings alone.

    A unit present on ONE side only is a real change and not a paired
    measurement: the absent side contributes no variance, and the delta is the
    whole of the present reading. Refusing there would put a flag the gate is
    right to raise behind a noise test it cannot satisfy."""
    var = 0.0
    for xs in (bs, hs):
        if not xs:
            continue
        if len(xs) < 2:
            return float("inf")
        var += statistics.variance(xs) / len(xs)
    return MEDIAN_SE_FACTOR * math.sqrt(var)


# ⭐⭐⭐ THE CUT-OFF FOR THE *IDENTICAL-TREES* TEST, WHICH IS NOT `K_SIGMA` (D171).
#
# ⛔⛔ WHAT WAS WRONG, MEASURED RATHER THAN ARGUED. `selftest_measure`'s bias arm
# asked `|d| > K_SIGMA * se` of EVERY unit and red the whole job if ANY unit
# fired. Two things make that not a ±2σ test:
#
#   (a) `se` is ESTIMATED FROM THE SAME TWO READINGS. At `--repeats 2` there are
#       two samples a side, so the noise estimate has one degree of freedom and a
#       normal critical value is wildly anti-conservative — the textbook
#       t(0.975, 1) is 12.7, not 2. The per-unit false-positive rate on identical
#       trees is **12.91%**, not the 4.55% the "±2σ" language implies.
#   (b) IT IS ASKED OF 23 UNITS AND COMBINED WITH `OR`. A per-unit rate of 12.91%
#       over the 23 units this repository profiles is a family-wise **95.8%**.
#
#   ⇒ the job `ci_local --job kernel-delta-redfirst` reds on a PERFECTLY QUIET BOX,
#     with two identical trees, 95.8% of the time. It passed 4.2% of the time, and
#     nobody had ever run it. The four units that fired on 09/06 are exactly what
#     the null predicts (2.97 expected, P(>=4) = 34.5%), in mixed signs, at ratios
#     of 1.17x and 2.8x the band — the shape of a marginal false positive, not of
#     a bias. [[feedback-inherited-diagnosis-is-a-hypothesis]]
#
# 📊 AND IT IS MEASURED, NOT ONLY DERIVED. Arm 1 was run for real at `c61d7f5`,
# `--repeats 4`, 23 units (log: 8 passes, load 9.0-21.6). Re-judging THOSE SAME
# READINGS both ways:
#     --repeats 4   OLD rule fires on 1 of 23 (`X86.State` +5.6 ms at 2.59x se)
#                   ⇒ RED.   NEW rule fires on 0 ⇒ passes.
#     --repeats 2   all 36 sub-samples of the same readings: OLD reds 29/36 = 81%,
#                   NEW reds 2/36 = 6% against its 5% target.
# ⚠️ The 81% is a resampling of ONE run, so it says what THIS run would have told
# the CI job at its own `--repeats 2` — it is not 36 independent afternoons, and it
# is quoted as the smaller claim it is.
#
# 🔑 A PER-UNIT BAND IS NOT A RUN-WIDE CLAIM. The sentence the arm prints —
# "identical trees produced no difference THE RUN cannot explain" — quantifies
# over every unit, so its threshold has to as well. A gate that asks one question
# 21 times and reds on any answer has 21 chances to be wrong and one to be right.
#
# ⭐ AND THE NULL IS EXACT AT n = 2, WHICH IS THE REPEAT COUNT CI USES. With two
# readings a side the median IS the mean, so with b, h iid:
#       d = mean(h) - mean(b) ~ N(0, sigma^2)
#       se = F * sqrt(u^2 + v^2) / 2,   u = b1-b2, v = h1-h2 ~ N(0, 2 sigma^2)
#   and d is independent of (u, v) because cov(x1+x2, x1-x2) = 0. Writing
#   c = K*F/sqrt(2), the fire condition is |Z| > c*sqrt(X) with X ~ chi2_2, and
#       P(fire) = INT 2*Phi(-c*sqrt(x)) * (1/2) e^(-x/2) dx = 1 - c/sqrt(1+c^2)
#   by parts. That inverts in closed form, so the cut is DERIVED, not tuned.
# ⛔ THE SECOND SOURCE IS THE GATE. The closed form is checked against a Monte
# Carlo over the SHIPPED `resolution()` in `--selftest`, and their agreement is
# the arm — a threshold derived from the thing it thresholds would be the defect
# this file already records three times.
# [[feedback-widening-a-gate-needs-a-second-source]]
# [[feedback-two-readings-are-not-two-witnesses]]
BIAS_ALPHA = 0.05           # family-wise, over ALL units, per run
_BIAS_CUT_CACHE = {}


def bias_cut(n, units, alpha=BIAS_ALPHA):
    """The `|d| / se` cut-off whose FAMILY-WISE false-positive rate over `units`
    units is `alpha`, on identical trees, at `n` readings a side.

    Exact at n = 2 (the closed form above). For n > 2 the median is not the mean
    and there is no closed form, so the quantile is taken from a SEEDED Monte
    Carlo over `resolution()` itself — deterministic run to run, and checked
    against the closed form at n = 2 by `--selftest`."""
    if units < 1 or n < 2:
        return float("inf")
    key = (n, units, round(alpha, 6))
    if key in _BIAS_CUT_CACHE:
        return _BIAS_CUT_CACHE[key]
    q = 1.0 - (1.0 - alpha) ** (1.0 / units)      # Sidak, per unit
    if n == 2:
        c = (1.0 - q) / math.sqrt(q * (2.0 - q))
        cut = c * math.sqrt(2.0) / MEDIAN_SE_FACTOR
    else:
        cut = _bias_null_quantile(n, 1.0 - q)
    _BIAS_CUT_CACHE[key] = cut
    return cut


def _bias_null_draws(n, trials, seed, shift=0.0):
    """|d|/se on identical trees (plus an optional true bias), through the
    SHIPPED statistic. The ratio is location- and scale-free, so standard
    normals are not an assumption about milliseconds."""
    rng = random.Random(seed)
    out = []
    for _ in range(trials):
        bs = [rng.gauss(0.0, 1.0) for _ in range(n)]
        hs = [rng.gauss(0.0, 1.0) + shift for _ in range(n)]
        se = resolution(bs, hs)
        if se in (0.0, float("inf")):
            continue
        out.append(abs(statistics.median(hs) - statistics.median(bs)) / se)
    return out


def _bias_null_quantile(n, p, trials=120000, seed=20260906):
    xs = sorted(_bias_null_draws(n, trials, seed))
    return xs[min(len(xs) - 1, int(math.ceil(p * len(xs))) - 1)]


# ⛔ A SAFETY BOUND IS FREE TO A GATE THAT NEVER SPEAKS, so the arm carries its
# LIVENESS bound too and prints it. `bias_detectable` is the smallest true bias,
# in units of one pass's standard deviation, that the calibrated cut catches with
# probability `power` at `n` repeats. Measured over the same generator as the
# cut. MEASURED, not guessed, and it refuted the figure this comment first
# carried: at n = 2 the answer is **30.6x** one pass's own spread, where the
# draft said ~17. The CI job's `--repeats 2` buys an arm
# that cannot see anything, and a green from a blind arm is a VOID, not a pass.
# [[feedback-measure-a-gates-error-rates]]
def bias_detectable(n, cut, power=0.90, trials=20000, seed=71):
    lo, hi = 0.0, 1.0
    def hit(d):
        xs = _bias_null_draws(n, trials, seed, shift=d)
        return sum(1 for x in xs if x > cut) / max(1, len(xs))
    for _ in range(40):
        if hit(hi) >= power:
            break
        lo, hi = hi, hi * 2.0
        if hi > 4096.0:
            return float("inf")
    for _ in range(18):
        mid = (lo + hi) / 2.0
        if hit(mid) >= power:
            hi = mid
        else:
            lo = mid
    return hi


def repeats_to_decide(n, se, margin):
    """How many repeats a side would need for K*se to clear `margin`.

    ⚠️ A PROJECTION AND LABELLED ONE. It reads this run's noise forward on the
    assumption that the next run's is the same, which is exactly the assumption a
    loaded box breaks. It is a price, not an allowance: the re-run measures its
    own noise afresh and may refuse again."""
    if se in (0.0, float("inf")) or margin <= 0 or n < 2:
        return None
    need = n * (K_SIGMA * se / margin) ** 2
    return max(n + 1, int(math.ceil(need)))


# ⭐⭐⭐ THE THREE-WAY VERDICT FOR **ONE** UNIT, IN ONE PLACE (D154).
#
# `verdict()` below judges a whole readings blob and prints a report; this is the
# rule it applies, per unit, with nothing printed. It is factored out because the
# repository now has THREE callers of the same six lines — this gate, the pricing
# tool (`delta_repair_price.judge`), and the DRIFT gate (`kernel_drift.py`) — and
# a third copy would have been born in agreement with the other two and diverged
# on the next ordinary append.
# [[feedback-a-duplicate-born-in-agreement]]
#
# ⛔ THE MIDDLE VERDICT IS NOT A ROUNDING CASE. `UNMEASURABLE` means the band
# straddles the allowance, so THIS RUN cannot say which side the delta is on. It
# must never be collapsed into either neighbour: reported as `ok` it is a pass
# nobody measured, and reported as `OVER` it is a conviction built out of noise.
def judge_delta(bs, hs, budget_ms):
    """One unit's verdict: {d, se, band, budget, verdict, need, n, margin} or None.

    `budget_ms` is passed IN rather than computed here, because the accumulated
    allowance of a k-batch window is not one budget and the decision of what a
    window is entitled to belongs at the call site, where it can be read."""
    if not bs or not hs:
        return None
    d = statistics.median(hs) - statistics.median(bs)
    se = resolution(bs, hs)
    band = K_SIGMA * se
    if d - band > budget_ms:
        v = "OVER"
    elif d + band < budget_ms:
        v = "ok"
    else:
        v = "UNMEASURABLE"
    n_side = min(len(bs), len(hs))
    return {"d": d, "se": se, "band": band, "budget": budget_ms, "verdict": v,
            "need": repeats_to_decide(n_side, se, abs(d - budget_ms)),
            "n": n_side, "margin": d - budget_ms}


def profile(worktree, decl_mods):
    r = subprocess.run([sys.executable, KCOST, "--emit-json", "--root", worktree,
                        "--decl-modules", ",".join(decl_mods)],
                       capture_output=True, text=True)
    if r.returncode != 0:
        # ⛔ A GATE THAT REFUSES MUST SAY WHAT IT SAW (D94): a refusal with no
        # reading attached turns a remote failure into a local re-run, and for a
        # TIMING gate the local re-run answers a different question.
        print(f"⛔ the profiler failed on {worktree}:\n{r.stdout}\n{r.stderr}")
        sys.exit(2)
    for line in reversed(r.stdout.splitlines()):
        if line.startswith("{"):
            return json.loads(line)
    print(f"⛔ the profiler produced no JSON for {worktree}:\n{r.stdout}\n{r.stderr}")
    sys.exit(2)


# ⭐ THE BASE IS "THE TREE THIS CHANGE IS A CHANGE TO", and which commit that is
# depends on where the head sits: a branch's base is where it left the trunk, a
# trunk commit's base is its parent.
#
# ⛔ AND THE TRUNK MAY NOT BE A LOCAL BRANCH.  `actions/checkout` leaves a runner
# with a detached HEAD and no local `master`, so a gate that only knows the name
# `master` reports a git error on the machine it was registered for.  The
# candidates are tried in order and the one that RESOLVES is used; if none does,
# the gate refuses rather than inventing a base.
def resolve_base(head):
    trunk = None
    for cand in ("master", "origin/master", "refs/remotes/origin/master"):
        if subprocess.run(["git", "rev-parse", "--verify", "--quiet", cand],
                          cwd=ROOT, capture_output=True).returncode == 0:
            trunk = cand
            break
    if trunk is None:
        print("⛔ no `master` or `origin/master` in this clone, so the base of "
              "this change cannot be resolved. Pass --base explicitly; a gate "
              "that guessed one would be comparing against a tree nobody chose.")
        sys.exit(2)
    on_trunk = subprocess.run(["git", "merge-base", "--is-ancestor", head, trunk],
                              cwd=ROOT, capture_output=True).returncode == 0
    return git("rev-parse", f"{head}^") if on_trunk else git("merge-base", trunk, head)


def box_stamp():
    try:
        la1, la5, la15 = os.getloadavg()
        load = f"{la1:.2f}/{la5:.2f}/{la15:.2f}"
    except OSError:
        load = "unavailable"
    return (f"BOX {socket.gethostname()} · {platform.platform()} · "
            f"{os.cpu_count()} cpus · load(1/5/15) {load} · "
            f"{time.strftime('%Y-%m-%d %H:%M:%S %Z')}")


def measure(base_rev, head_rev, repeats, keep=None, plant=None):
    """Alternating passes over two detached worktrees. Returns a readings dict.

    ⚠️ THE ALTERNATION IS THE METHOD AND NOT A FLOURISH. Profiling one tree three
    times and then the other three times measures the difference between the
    first half of the run and the second half as surely as it measures the
    difference between the trees.

    ⛔⛔ AND `ABAB` DOES NOT CANCEL A MONOTONE DRIFT — this docstring said it did,
    for as long as the function has existed, and it is arithmetically false. Under
    ABAB the base sits at passes 1, 3, ..., 2n-1 and the head at 2, 4, ..., 2n, so
    the head's median is exactly ONE PASS later than the base's at EVERY repeat
    count: a drift of s ms per pass lands as a bias of exactly s ms, which no
    number of repeats reduces. Driven with the noise switched off, the old order
    returned -30.00 ms against a -30.00 ms/pass drift. The order is now ABBA —
    the pair reverses every repeat — which cancels a LINEAR drift exactly (0.00 ms
    on the same probe) and a curved one only partly. That limit is stated rather
    than implied: this is a reduction, not an immunity.
    ⭐ The repo already knew: `kernel_delta_history.py` sweeps forward then REVERSE
    for this exact reason, and has since it was written. Two tools, one repo, and
    the one with the wrong design carried the sentence asserting the right one.
    [[feedback-a-citation-is-an-ungated-claim]]"""
    decl_map = gated_declarations()
    decl_mods = sorted(decl_map)
    tmp = keep or tempfile.mkdtemp(prefix="x86lean-delta-")
    base_wt, head_wt = os.path.join(tmp, "base"), os.path.join(tmp, "head")
    made = []
    try:
        for wt, rev in ((base_wt, base_rev), (head_wt, head_rev)):
            if not os.path.exists(wt):
                git("worktree", "add", "--detach", wt, rev)
                made.append(wt)
        if plant:
            plant(head_wt)
        readings = {"base": [], "head": []}
        pair = (("base", base_wt), ("head", head_wt))
        for rep in range(repeats):
            for side, wt in (pair if rep % 2 == 0 else pair[::-1]):
                t0 = time.time()
                r = profile(wt, decl_mods)
                r["secs"] = round(time.time() - t0, 1)
                # ⛔ THE GLOBAL PASS INDEX, STAMPED RATHER THAN RECONSTRUCTED
                # (D171). `readings` is grouped BY SIDE, so the wall-clock order
                # across the two sides is not recoverable from it without knowing
                # this loop's ordering rule — and that rule just changed from ABAB
                # to ABBA. A consumer that re-derived it would have been silently
                # wrong for every run written before the change.
                # [[feedback-an-unrecorded-rule-cannot-be-audited]]
                r["pass"] = len(readings["base"]) + len(readings["head"]) + 1
                r["side"] = side
                readings[side].append(r)
                print(f"  pass {side:<4} load1={r['load1']:.2f}  {r['secs']:>4.0f}s  "
                      f"Tests.Coverage={r['modules'].get('Tests.Coverage', 0):.0f}  "
                      f"X86.Syntax={r['modules'].get('X86.Syntax', 0):.1f}", flush=True)
        return {"base_rev": git("rev-parse", base_rev),
                "head_rev": git("rev-parse", head_rev),
                "planted": bool(plant), "box": box_stamp(),
                "decl_map": decl_map, "readings": readings}
    finally:
        if keep is None:
            for wt in made:
                subprocess.run(["git", "worktree", "remove", "--force", wt],
                               cwd=ROOT, capture_output=True, text=True)
            shutil.rmtree(tmp, ignore_errors=True)


# ⭐⭐ THE CONDITIONS A ROW HAS TO CARRY, AND WHY MEDIANS ARE NOT ENOUGH (D171).
#
# A ledger row keeps `base_ms` (the medians) and ONE `box` stamp taken when the row
# was written. Neither can tell a later reader whether the run was quiet or loud,
# and NEITHER CAN SHOW A DRIFT — which is the failure this same session found: over
# one 8-pass run, 20 of 23 units sloped the same way, the largest at +295 ms/pass,
# and under the old ABAB order that landed as a standing bias inside every delta.
# The only reason it was visible at all is that the raw readings happened to be
# saved to a scratch file. A row that outlives the readings must carry the shape.
# [[feedback-a-measurement-without-its-conditions]]
# [[feedback-a-counterbalance-must-be-symmetric]]
def pass_conditions(data):
    """Per-pass (pass, side, load1, secs) plus the run's drift, compactly.

    ⚠️ Per-pass PER-UNIT milliseconds are deliberately NOT stored: 23 units x 8
    passes x every row is a ledger nobody opens. The drift statistic is the part a
    reader acts on, and it is stored with the unit it belongs to — a slope with no
    unit name is a number a reader cannot act on."""
    rs = sorted([r for side in ("base", "head") for r in data["readings"][side]],
                key=lambda r: r.get("pass", 0))
    if not rs or any("pass" not in r for r in rs):
        # ⛔ ABSENT, NOT ZERO. Readings taken before the pass stamp existed cannot
        # have their order recovered, and a fabricated order would produce a drift
        # figure that looks measured.
        return {"passes": None, "why": "readings carry no pass index (pre-D171)"}
    out = {"passes": [{"pass": r["pass"], "side": r["side"],
                       "load1": round(r.get("load1", 0.0), 2),
                       "secs": r.get("secs")} for r in rs]}
    units, slopes = {}, []
    for r in rs:
        for u, v in units_of(r, data["decl_map"]).items():
            units.setdefault(u, []).append((r["pass"], v))
    for u, pts in units.items():
        if len(pts) < 3:
            continue
        mx = statistics.mean([p for p, _ in pts])
        my = statistics.mean([v for _, v in pts])
        den = sum((p - mx) ** 2 for p, _ in pts)
        if den:
            slopes.append((u, sum((p - mx) * (v - my) for p, v in pts) / den, my))
    if slopes:
        worst = max(slopes, key=lambda t: abs(t[1]))
        up = sum(1 for _, sl, _ in slopes if sl > 0)
        # 3 dp, not 2: the arm that checks this compares against the STORED value,
        # and at 2 dp a slope of 4.762 stores as 4.76 — a rounding the first form
        # of that arm hid inside a tolerance wide enough to also hide a wrong
        # prediction. The precision is now part of the contract.
        out["drift"] = {"worst_unit": worst[0], "ms_per_pass": round(worst[1], 3),
                        "pct_of_median": round(100 * worst[1] / worst[2], 3) if worst[2] else None,
                        "units_sloping_up": up, "units": len(slopes)}
    return out


def verdict(data, default_ms, budgets, floor=None, quiet=False):
    """(rc, lines) — the whole comparison, over readings that are already taken.

    Split out from `measure` so that every failure mode of the COMPARISON can be
    driven red in seconds against saved readings, instead of only after a
    seven-minute measurement that would make the probe too expensive to run."""
    L = []
    def p(s=""):
        L.append(s)
        if not quiet:
            print(s)
    decl_map = data["decl_map"]
    sides = {s: [units_of(r, decl_map) for r in data["readings"][s]] for s in ("base", "head")}
    p(data["box"])
    p(f"base {data['base_rev'][:9]}   head {data['head_rev'][:9]}"
      + ("   ⚠️ PLANTED HEAD — this run is a PROBE" if data.get("planted") else ""))
    p(f"repeats per side: {len(sides['base'])} (passes alternated base/head)")
    p(f"loads: " + " ".join(f"{r['load1']:.2f}" for s in ("base", "head")
                            for r in data["readings"][s]))
    all_units = sorted(set().union(*[set(u) for u in sides["base"] + sides["head"]]))
    p()
    p(f"{'UNIT':<56}{'base':>10}{'head':>10}{'delta':>10}{'+-K*se':>9}"
      f"{'range':>9}{'budget':>9}  VERDICT")
    fail, refuse, defaulted, flags, unresolved = False, False, [], [], []
    for u in all_units:
        bs = [x[u] for x in sides["base"] if u in x]
        hs = [x[u] for x in sides["head"] if u in x]
        if not bs:
            flags.append(f"NEW unit in head: {u}")
        if not hs:
            flags.append(f"unit GONE from head: {u} "
                         f"(renamed, deleted, or below the profiler threshold)")
        b = statistics.median(bs) if bs else 0.0
        h = statistics.median(hs) if hs else 0.0
        d = h - b
        # ⚠️ TWO NUMBERS, AND ONLY ONE OF THEM IS THE TEST. `band` is K standard
        # errors of the DELTA and it is what decides; `rng` is the readings'
        # within-side range, kept because it is the plainest description of what
        # the box did during the run — a READING beside a verdict, which is this
        # file's standing habit and the reason D141 was findable at all.
        se = resolution(bs, hs)
        band = K_SIGMA * se
        rng = max((max(bs) - min(bs)) if len(bs) > 1 else 0.0,
                  (max(hs) - min(hs)) if len(hs) > 1 else 0.0)
        bandtxt = "inf" if band == float("inf") else f"{band:.1f}"
        if u in budgets:
            bud = effective(budgets[u], b, floor)
        elif default_ms is not None:
            bud = effective(default_ms, b, floor)
            defaulted.append(u)
        else:
            p(f"{u:<56}{b:>10.1f}{h:>10.1f}{d:>+10.1f}{bandtxt:>9}"
              f"{rng:>9.1f}{'-':>9}  NO BUDGET ⛔")
            fail = True
            continue
        # ⛔ THE THREE-WAY QUESTION, IN THIS ORDER. A delta is over budget only
        # when it is over by more than this run can have invented, and under it
        # only when it is under by more than that; everything between is the
        # instrument saying it cannot tell, which is a thing to print and not a
        # thing to break in one direction because a verdict was wanted.
        if d - band > bud:
            v = "OVER BUDGET ⛔"
            fail = True
        elif d + band < bud:
            v = "ok"
        else:
            v = "UNMEASURABLE ⛔"
            refuse = True
            n_side = min(len(bs) or 10**9, len(hs) or 10**9)
            need = repeats_to_decide(n_side, se, abs(d - bud))
            unresolved.append((u, d, bud, band, need))
        p(f"{u:<56}{b:>10.1f}{h:>10.1f}{d:>+10.1f}{bandtxt:>9}"
          f"{rng:>9.1f}{bud:>9.1f}  {v}")
    p()
    if defaulted:
        # ⛔ A DEFAULT THAT IS NOT LISTED IS A LIST WITH INVISIBLE GAPS. Every
        # unit that fell to it is named, so that a unit quietly inheriting an
        # allowance nobody chose for it is visible in the gate's own output.
        p(f"⚠️  {len(defaulted)} unit(s) fell to {DEFAULT_TAG} "
          f"{default_ms[1]:g}{'%' if default_ms[0] == 'rel' else ' ms'}"
          + (f" (floor {floor:g} ms)" if default_ms[0] == "rel" else "") + ": "
          + ", ".join(defaulted))
    for f in flags:
        p(f"⚠️  {f}")
    if refuse:
        p(f"⛔ delta gate UNMEASURABLE — for the unit(s) below, this run's own "
          f"uncertainty band straddles the budget, so the readings above do NOT "
          f"say which side of it this commit is on. They are printed, and they "
          f"are not a verdict.")
        # ⭐ THE PRICE OF AN ANSWER, PER UNIT, BECAUSE A REFUSAL THAT NAMES NO
        # REMEDY IS A WALL. The projection is `n * (K*se / |delta - budget|)^2`:
        # the band falls as 1/sqrt(n), so the repeats needed rise as the SQUARE
        # of how close the delta sits to its budget. A commit near the line is
        # expensive to judge and that is a fact about the commit, not the gate.
        for u, d, bud, band, need in unresolved:
            margin = d - bud
            # ⛔ THREE CAUSES, NAMED SEPARATELY. A single "no remedy" sentence
            # covering all of them is the shape where a missing case reads as
            # empty: "cannot estimate its noise" and "sits exactly on the line"
            # are different facts and want different acts from the reader.
            if band == float("inf"):
                price = ("this run has a side with fewer than two readings, so it "
                         "cannot estimate its own noise at all — re-run with "
                         "--repeats 2 or more")
            elif margin == 0:
                price = "no number of repeats decides a delta sitting exactly ON its budget"
            elif need:
                price = f"~{need} repeats a side would decide it"
            else:
                price = "the readings carry no spread at all, so nothing here is noise"
            p(f"   · {u}: delta {d:+.1f} vs budget {bud:.1f} "
              f"(margin {margin:+.1f}), band ±{band:.1f} ⇒ {price}")
        p(f"⛔ DO NOT WIDEN THE BUDGET. That would derive the allowance from the "
          f"noise it exists to see through. Buy repeats, quiet the box, or make "
          f"the commit cheaper — the third is the one a refusal most often means.")
    # ⛔⛔ THE PRECEDENCE, AND IT INVERTED WITH THE RULE (D141). While the refusal
    # read `budget < spread` it was a property of the RUN — the box's noise
    # swamped the allowance — so a refusal anywhere meant no verdict anywhere,
    # and "a REFUSAL outranks an over-budget red" was right.
    #
    # Under the band it is a property of ONE UNIT and its distance from ITS
    # budget: a unit marked OVER BUDGET was convicted BEYOND this run's noise,
    # which is exactly what the refused unit says it could not establish. A
    # refusal on a second unit adds no doubt to the first, and reporting
    # UNMEASURABLE there would file a commit that certainly breaks its budget
    # under "we could not tell" — the reassuring direction, and the wrong one.
    #
    # ⇒ FAILED outranks UNMEASURABLE outranks CLEAN. Both messages still print,
    # so a refusal is never swallowed by a conviction; only the exit code ranks.
    if fail:
        p("⛔ delta gate FAILED (a unit's delta is over its budget by more than "
          "this run's own noise, or has no budget at all)."
          + (" A unit above is also UNMEASURABLE; that is printed and does not "
             "soften this — the convicted unit was decided beyond the same noise."
             if refuse else ""))
        return 1, L
    if refuse:
        return 3, L
    p("delta gate: CLEAN")
    return 0, L


# ⭐⭐ THE READINGS THE HELM ORDERED TO RIDE BESIDE EVERY MERGE.  The absolute
# ceilings are retired as a gate and kept as READINGS, box-stamped — printed
# here so that a merge's record carries both numbers without either of them
# being able to read as a verdict.
def absolute_readings(data):
    ceil = {}
    for line in open(CEIL_FILE):
        p = line.split("#")[0].strip().split()
        if len(p) == 4 and p[1] == "@decl":
            ceil[f"{p[0]} @decl {p[2]}"] = float(p[3])
        elif len(p) == 3 and p[1] == "@tail":
            ceil[f"{p[0]} @residue"] = float(p[2])
        elif len(p) == 2:
            ceil[p[0]] = float(p[1])
    print("\n--- ABSOLUTE READINGS (RETIRED AS A GATE, 09/04 21:42; box-stamped)")
    print(f"{'UNIT':<56}{'base':>10}{'head':>10}{'ceiling':>10}   base/head")
    # ⛔ THE CLOSING SENTENCE USED TO SAY "the unchanged parent was already over
    # TWO of them" — a literal, in a tool that is reading the very numbers that
    # would say so. Prose in a gate's own output is prose, and a count in it goes
    # stale exactly like a count in a comment (D41, D65, D94). It is DERIVED now,
    # and it names the units rather than counting them.
    over_base, over_head = [], []
    ub = [units_of(r, data["decl_map"]) for r in data["readings"]["base"]]
    uh = [units_of(r, data["decl_map"]) for r in data["readings"]["head"]]
    for u in sorted(set().union(*[set(x) for x in ub + uh])):
        if u not in ceil:
            continue
        b = statistics.median([x[u] for x in ub if u in x]) if any(u in x for x in ub) else float("nan")
        h = statistics.median([x[u] for x in uh if u in x]) if any(u in x for x in uh) else float("nan")
        if b > ceil[u]:
            over_base.append(u)
        if h > ceil[u]:
            over_head.append(u)
        print(f"{u:<56}{b:>10.1f}{h:>10.1f}{ceil[u]:>10.1f}   "
              f"{'over' if b > ceil[u] else 'under'}/"
              f"{'over' if h > ceil[u] else 'under'}")
    print(f"⚠️ These are READINGS, not a verdict. The BASE — the tree this change "
          f"is a change to, with none of it applied — is over "
          f"{len(over_base)} of these ceilings"
          + (": " + ", ".join(over_base) if over_base else "") + "; the head is over "
          f"{len(over_head)}" + (": " + ", ".join(over_head) if over_head else "")
          + ". A ceiling the parent already exceeds is an instrument scoped to the "
          "box, not to the commit (D111, D122).")


# ───────────────────────────── the probes ──────────────────────────────────

def _synthetic(base_vals, head_vals, repeats=2, jitter=0.0):
    """Readings with no measurement in them, for driving the COMPARISON red."""
    def side(vals, k):
        return [{"modules": {m: v + (jitter if i else 0.0) for m, v in vals.items()},
                 "decls": {}, "load1": 1.0, "load5": 1.0}
                for i in range(k)]
    return {"base_rev": "0" * 40, "head_rev": "1" * 40, "planted": False,
            "box": "BOX synthetic — no measurement in this run",
            "decl_map": {}, "readings": {"base": side(base_vals, repeats),
                                         "head": side(head_vals, repeats)}}


def _explicit(base_vals, head_vals, unit="M"):
    """Readings from EXPLICIT per-pass values — for the arms that need a
    dispersion held fixed while the number of repeats changes, which
    `_synthetic`'s single step-jitter cannot express."""
    def side(vals):
        return [{"modules": {unit: v}, "decls": {}, "load1": 1.0} for v in vals]
    return {"base_rev": "0" * 40, "head_rev": "1" * 40, "planted": False,
            "box": "BOX synthetic — no measurement in this run", "decl_map": {},
            "readings": {"base": side(base_vals), "head": side(head_vals)}}


# ⭐⭐ THE MEASURED SELFTEST'S JUDGEMENT, DRIVEN WITHOUT ITS FOUR BUILDS.
#
# ⛔ `selftest_measure` runs in its own CI job because it needs real trees, and
# that job has NEVER COMPLETED on any machine (Actions refuses every job on this
# account for billing, desk FH). So its own decision logic — what arm 1 accepts,
# what it rejects, what it merely reports — is the least-exercised code in this
# file, and D141 changed it. A gate whose judgement is only reachable through an
# expensive path is a judgement nobody drives.
#
# ⇒ `measure` is stubbed, so nothing is profiled. These arms say nothing about
# whether the profiler can see a code change; they say what arm 1 DOES with the
# three verdicts it can be handed. [[feedback-make-the-probe-cheap]]
def _stub_readings(base_vals, head_vals, syn=250.0):
    def side(vals):
        return [{"modules": {"Tests.Coverage": v, "X86.Syntax": syn}, "decls": {},
                 "load1": 9.0, "load5": 9.0, "secs": 70.0} for v in vals]
    return {"base_rev": "0" * 40, "head_rev": "0" * 40, "planted": False,
            "box": "BOX stub — no measurement in this run", "decl_map": {},
            "readings": {"base": side(base_vals), "head": side(head_vals)}}


def selftest_measure_judgement():
    """(names, bad) — arm 1's verdict on each of the three things it can be told."""
    import io, contextlib
    global measure
    real, names, bad = measure, [], []
    # ⛔⛔ EACH CASE DECLARES THE VERDICT IT MUST PRODUCE, NOT ONLY THE ANSWER IT
    # MUST GET. Driven red first: quietly replacing the loud-box readings with
    # quiet ones left this suite GREEN while the rc-3 branch stopped being
    # covered at all — an arm whose NAME says "REFUSED" testing the CLEAN path.
    # The declared verdict is the arm creating its own condition.
    # [[feedback-a-probe-must-create-its-condition]]
    cases = [
        # ⛔ THE ONE THAT MUST RED: identical trees have a true delta of exactly
        # zero, so a conviction there would make every red this gate ever printed
        # suspect. It is the only outcome arm 1 may reject.
        ("identical trees CONVICTED must fail arm 1", "FAILED", "worst unit delta",
         _stub_readings([24700, 24710, 24690], [40000, 40010, 39990]), True),
        ("identical trees CLEAN passes arm 1", "CLEAN", "clears every unit's budget",
         _stub_readings([24700, 24710, 24690], [24700, 24705, 24695]), False),
        # ⚠️ AND THE ONE D141 CHANGED. A refusal on identical trees is a fact
        # about the BOX at that many repeats, not a defect in the gate; requiring
        # rc 0 here made the arm red whenever another seat was building, and an
        # arm that reds for a reason outside the code is an arm nobody reads.
        ("identical trees REFUSED reports the box and passes arm 1", "UNMEASURABLE",
         "statement about THIS BOX",
         _stub_readings([24700, 21000, 28000], [24700, 20500, 28500]), False),
        # ⛔⛔ THE BIAS ARM (D145). A +200 ms difference between two copies of one
        # commit, with a band of ±20: far under the 1,778 ms budget, so the gate
        # says CLEAN and arm 1's verdict check is happy — and the run has still
        # produced a systematic difference its own noise cannot explain, which
        # rides inside every delta this gate reports. That is the case the old
        # arm could not see, because it only ever compared the rc.
        ("a BIAS on identical trees reds arm 1 even when the gate says CLEAN",
         "CLEAN", "a systematic difference between two copies of ONE commit",
         _stub_readings([24700, 24710, 24690], [24900, 24910, 24890]), True),
        # ⚠️ AND THE OTHER DIRECTION, WHICH MUST NOT RED: an invented delta of
        # −2,000 ms — over the 1,778 ms budget — but inside a ±5,500 band. The box
        # is loud, not biased. It prints a SCOPE line and passes, because redding
        # here is the defect D141 removed from this same arm.
        # ⚠️ DECLARED `CLEAN` IN THE FIRST DRAFT AND THE CONDITION CHECK REFUSED
        # IT: a ±5,524 band around −2,000 straddles a 1,778 budget, so the gate
        # returns UNMEASURABLE, not CLEAN. The arm was testing a branch its name
        # did not describe — the same defect this case list was given the verdict
        # column to prevent, caught on the case that introduced it.
        ("a LOUD box scopes arm 1 rather than redding it",
         "UNMEASURABLE", "SCOPE, not a failure",
         _stub_readings([22000, 24700, 27400], [20000, 22700, 25400]), False),
    ]
    for name, want_verdict, want_line, data, want_bad in cases:
        measure = lambda *a, **k: data
        argv = sys.argv[:]
        sys.argv = ["kernel_delta.py", "--selftest-measure", "--repeats", "3", "--plant", "1"]
        buf = io.StringIO()
        try:
            with contextlib.redirect_stdout(buf):
                selftest_measure()
        finally:
            sys.argv, measure = argv, real
        out = buf.getvalue()
        # ⛔ THE WHOLE ARM-1 BLOCK, not only its verdict line: the bias check and
        # the scope line are arm 1's output too, and a case that drove one of them
        # would have gone unread by a filter that keeps only the ⇒ line.
        arm1 = [l for l in out.splitlines()
                if "identical trees" in l or "invented" in l]
        got_bad = any(l.startswith("  ⛔") for l in arm1)
        made_it = any(want_verdict in l for l in arm1)
        # ⛔ AND THE LINE THE CASE EXISTS TO PRODUCE. The scope list and the bias
        # message are arm 1's real output; a case that stopped producing one would
        # otherwise stay green on its rc alone, which is exactly how the verdict
        # column came to be needed one edit earlier.
        said_it = want_line in out
        ok = got_bad == want_bad and made_it and said_it
        names.append(name)
        print(("  ✔ " if ok else "  ⛔ ") + name +
              ("" if ok else
               (f"   (these readings produced no {want_verdict}, so the arm tested "
                f"another branch under this name)" if not made_it else
               f"   (arm 1 never printed {want_line!r}, so the behaviour this case "
               f"is named for did not happen)" if not said_it else
                f"   (arm 1 said {'⛔' if got_bad else '✔'}, wanted "
                f"{'⛔' if want_bad else '✔'})")))
        if not ok:
            bad.append(name)
            for l in arm1:
                print("      " + l.strip())
    return names, bad


# ⭐⭐⭐ THE ARMS FOR THE IDENTICAL-TREES CUT (D171). NO MEASUREMENT IN ANY OF THEM:
# they drive the SHIPPED `resolution()` and the SHIPPED median difference over
# generated draws, so a green here is about the RULE and says nothing about the
# profiler. The order matters — the control comes first, because a broken
# generator reds every arm after it and the reds would read as findings.
# [[feedback-a-plant-probes-control-comes-first]]
def bias_cut_arms(units=23, trials=40000):
    names, bad = [], []

    def arm(name, ok, detail):
        names.append(name)
        print(("  ✔ " if ok else "  ⛔ ") + name + " — " + detail)
        if not ok:
            bad.append(name)

    def famrate(xs, cut):
        per = sum(1 for x in xs if x > cut) / max(1, len(xs))
        return 1.0 - (1.0 - per) ** units

    # ── CONTROL. One generator, drawn once, feeding BOTH rules and every arm
    #    below: the comparison must not be two experiments.
    null2 = _bias_null_draws(2, trials, seed=31337)
    null6 = _bias_null_draws(6, trials, seed=31338)
    cut2, cut6 = bias_cut(2, units), bias_cut(6, units)
    cal2 = famrate(null2, cut2)
    arm("CONTROL: the calibrated cut hits its stated family-wise rate",
        0.030 <= cal2 <= 0.075,
        f"{cal2:.1%} of runs red on identical trees at --repeats 2, "
        f"target {BIAS_ALPHA:.0%} (cut {cut2:.2f})")

    # ── RED-FIRST: the rule this replaced, over the SAME draws. If this ever
    #    goes quiet the defect has been reintroduced and the arm above cannot
    #    tell — a calibrated rule and a broken one both pass a 5% check.
    ship2 = famrate(null2, K_SIGMA)
    arm("RED-FIRST: the OLD rule (K_SIGMA) reds on a quiet box, on the same draws",
        ship2 >= 0.80,
        f"{ship2:.1%} of runs red with two identical trees and no box noise at "
        f"all — that is the `kernel-delta-redfirst` job as it shipped, and it is "
        f"why it had never been seen to pass")

    # ── LIVENESS. A safety bound is free to a gate that never speaks.
    hit6 = sum(1 for x in _bias_null_draws(6, trials, seed=31339, shift=4.0)
               if x > cut6) / max(1, trials)
    arm("LIVENESS: the calibrated rule still catches a real 4x-spread bias",
        hit6 >= 0.90,
        f"caught {hit6:.1%} of the time at --repeats 6 (cut {cut6:.2f})")

    # ── TWO ROUTES, and their agreement IS the arm. The shipped cut at n = 2 is
    #    a closed form; the check is a Monte Carlo through `resolution()` itself.
    q = 1.0 - (1.0 - BIAS_ALPHA) ** (1.0 / units)
    mc2 = _bias_null_quantile(2, 1.0 - q, trials=trials, seed=31340)
    agree = abs(mc2 - cut2) / cut2
    arm("TWO ROUTES: the closed form and a Monte Carlo agree at n = 2",
        agree < 0.08,
        f"closed form {cut2:.2f} vs Monte Carlo {mc2:.2f} ({agree:.1%} apart)")

    # ── THE VOID RULE FIRES, AND IS NOT ALWAYS ON. A probe must create its
    #    condition in both directions, or it is reporting its default.
    d2, d6 = bias_detectable(2, cut2, trials=8000), bias_detectable(6, cut6, trials=8000)
    arm("the VOID rule fires at --repeats 2 and stays silent at --repeats 6",
        d2 > 8.0 and d6 <= 8.0,
        f"smallest catchable bias {d2:.1f}x spread at n=2 (VOID) vs {d6:.1f}x at "
        f"n=6 (live)")

    # ⚠️ `units` here is the count this repository profiled on 09/06 and the arms
    # are about the RULE, not about that number: the shipped gate calls
    # `bias_cut(repeats, len(keys))` with the count the run actually saw. So the
    # arm that matters is the DIRECTION — a bigger family must buy a bigger cut,
    # or the correction is decorative.
    arm("the cut RISES with the family size, so the correction is not decorative",
        bias_cut(2, 1) < bias_cut(2, 8) < bias_cut(2, 23) < bias_cut(2, 100),
        f"cut at --repeats 2: {bias_cut(2,1):.1f} (1 unit) → {bias_cut(2,8):.1f} (8) "
        f"→ {bias_cut(2,23):.1f} (23) → {bias_cut(2,100):.1f} (100)")

    # ── THE ORDERING, driven on the shipped statistic. ABAB leaves exactly one
    #    pass of a linear drift; ABBA leaves none. The no-drift control comes
    #    with it so a zero here cannot be the probe failing to drift at all.
    def lay(order, reps):
        seq = []
        for r in range(reps):
            seq += ["base", "head"] if (order == "ABAB" or r % 2 == 0) else ["head", "base"]
        return seq

    def delta(order, reps, drift):
        v = {"base": [], "head": []}
        for p, side in enumerate(lay(order, reps), 1):
            v[side].append(1000.0 + drift * p)
        return statistics.median(v["head"]) - statistics.median(v["base"])

    ctl = max(abs(delta(o, r, 0.0)) for o in ("ABAB", "ABBA") for r in (2, 4, 6))
    abab = [delta("ABAB", r, -30.0) for r in (2, 3, 4, 6)]
    abba = [abs(delta("ABBA", r, -30.0)) for r in (2, 4, 6)]
    arm("ORDERING control: with NO drift both orders return exactly zero",
        ctl < 1e-9, f"worst |delta| {ctl:.2e} ms")
    arm("ORDERING: ABAB leaves exactly ONE pass of a monotone drift, at every n",
        all(abs(d + 30.0) < 1e-9 for d in abab),
        "deltas " + ", ".join(f"{d:+.2f}" for d in abab) +
        " ms against a -30.00 ms/pass drift")
    arm("ORDERING: ABBA — what `measure()` now does — cancels it exactly",
        all(d < 1e-9 for d in abba),
        "worst |delta| " + f"{max(abba):.2e} ms on the same drift")
    return names, bad


def selftest():
    """⛔ EVERY WAY THE COMPARISON COULD STOP LOOKING, DRIVEN SEPARATELY.

    These arms carry NO measurement: they feed the verdict function readings it
    cannot tell from real ones. That is deliberate and it is also the limit of
    what they prove — a green here says the comparison is sound and says NOTHING
    about whether the profiler can see a code change. `--selftest-measure` is the
    arm that creates that condition, and it is the one the helm asked for."""
    arms, bad = [], []

    def run(name, data, default_ms, budgets, want_rc, want_text=None, floor=None):
        rc, lines = verdict(data, default_ms, budgets, floor, quiet=True)
        out = "\n".join(lines)
        ok = rc == want_rc and (want_text is None or want_text in out)
        arms.append(name)
        print(("  ✔ " if ok else "  ⛔ ") + name +
              ("" if ok else f"   (rc={rc}, wanted {want_rc} / {want_text!r})"))
        if not ok:
            bad.append(name)
            for l in lines:
                print("      " + l)

    # ⭐ THE CONTROL COMES FIRST: four reds prove the comparison can fail; only
    # this proves it can pass, and an arm suite with no green arm is a suite that
    # would also pass if the gate refused everything.
    run("control: a delta inside its budget is CLEAN",
        _synthetic({"M": 100.0}, {"M": 110.0}), None, {"M": ("abs", 50.0)}, 0, "ok")
    run("a delta OVER its budget FAILS",
        _synthetic({"M": 100.0}, {"M": 200.0}), None, {"M": ("abs", 50.0)}, 1, "OVER BUDGET")
    run("a unit with NO budget and no @default FAILS",
        _synthetic({"M": 100.0}, {"M": 101.0}), None, {}, 1, "NO BUDGET")
    run("a unit with no budget but a @default is gated AND LISTED",
        _synthetic({"M": 100.0}, {"M": 101.0}), ("abs", 50.0), {}, 0, "fell to @default")
    run("a @default that does not cover the delta still FAILS",
        _synthetic({"M": 100.0}, {"M": 400.0}), ("abs", 50.0), {}, 1, "OVER BUDGET")
    # ⛔ THE ARM THAT MATTERS MOST FOR HONESTY: a budget under the run's own
    # measured spread is not a verdict about the commit, and must not be reported
    # as one — in EITHER direction.
    run("a budget under this run's own uncertainty REFUSES, not passes",
        _synthetic({"M": 100.0}, {"M": 105.0}, jitter=80.0), None, {"M": ("abs", 50.0)},
        3, "UNMEASURABLE")
    # ⛔⛔ THIS ARM USED TO SAY `_synthetic({"M":100},{"M":900}, jitter=80)` MUST
    # REFUSE, against a 50 ms budget — a delta of +800 on a box whose noise is
    # ±142, sixteen times its allowance and five bands clear of it. The old rule
    # refused it because the readings' RANGE (80) exceeded the BUDGET (50), and
    # the arm's name made that sound like a principle. It is a principle only
    # when the run genuinely cannot tell. ⇒ THE PAIR NOW SPLITS THE TWO CASES,
    # and the second one is D141's red-first: a gate that cannot convict a
    # commit sixteen times over its budget is not being careful, it is blind.
    run("a REFUSAL outranks an over-budget red WHEN THE BAND STRADDLES",
        _synthetic({"M": 100.0}, {"M": 160.0}, jitter=80.0), None, {"M": ("abs", 50.0)},
        3, "UNMEASURABLE")
    run("a delta far over budget is CONVICTED even though the box's noise "
        "exceeds that budget",
        _synthetic({"M": 100.0}, {"M": 900.0}, jitter=80.0), None, {"M": ("abs", 50.0)},
        1, "OVER BUDGET")
    # ⭐⭐⭐ D141's OWN RED-FIRST, AND IT IS THE ARM THE OLD STATISTIC COULD NOT
    # HAVE PASSED. The SAME per-reading dispersion, four times the repeats: the
    # readings' RANGE is identical (600.0 in both runs, printed in the `range`
    # column), so the old rule's verdict could not move — its stated remedy,
    # "re-run with more --repeats", was arithmetically a no-op at best and, with
    # real draws instead of a repeating pattern, strictly counter-productive
    # (measured: 84% refusal at n=3 rising to 100% at n=6 and every n above).
    # The band falls as 1/sqrt(n), so buying repeats buys a verdict.
    PATTERN = [-300.0, 0.0, +300.0]
    b3 = [1000.0 + x for x in PATTERN]
    h3 = [1120.0 + x for x in PATTERN]
    run("the remedy is a NO-OP at three repeats: the band still straddles",
        _explicit(b3, h3), None, {"M": ("abs", 500.0)}, 3, "UNMEASURABLE")
    run("…and the SAME dispersion at twelve repeats DECIDES it — the range is "
        "unchanged, the band is not",
        _explicit(b3 * 4, h3 * 4), None, {"M": ("abs", 500.0)}, 0, "ok")
    # ⛔ THE ARM THAT PROVES THE TWO RUNS REALLY DID SHARE A DISPERSION. Without
    # it the pair above is two unrelated runs and proves nothing about the
    # remedy; the whole claim is that ONE number moved and the other did not.
    r3 = max(max(b3) - min(b3), max(h3) - min(h3))
    r12 = max(max(b3 * 4) - min(b3 * 4), max(h3 * 4) - min(h3 * 4))
    se3, se12 = resolution(b3, h3), resolution(b3 * 4, h3 * 4)
    same_range, band_fell = (r3 == r12), (se12 < se3)
    arms.append("the range is blind to the repeats the band spends")
    print(("  ✔ " if (same_range and band_fell) else "  ⛔ ") +
          f"the range is blind to the repeats the band spends "
          f"(range {r3:.0f} → {r12:.0f}; band ±{K_SIGMA*se3:.0f} → ±{K_SIGMA*se12:.0f})")
    if not (same_range and band_fell):
        bad.append("the range is blind to the repeats the band spends")

    # ⛔ THE COIN FLIP THE OLD RULE DELIVERED AS A VERDICT. A commit sitting
    # exactly on its budget cannot be called by any run with noise in it, and on
    # a quiet box the old rule called it anyway — measured 50% `ok` / 49% `OVER
    # BUDGET` over 4,000 trials, which is not a gate, it is a toss.
    run("a delta sitting exactly ON its budget REFUSES rather than tossing a coin",
        _explicit([1000.0, 1010.0, 990.0], [1100.0, 1110.0, 1090.0]),
        None, {"M": ("abs", 100.0)}, 3, "exactly ON its budget")

    # ⛔ THE PRECEDENCE ARM. One unit convicted beyond the run's noise, one unit
    # straddling: the commit certainly breaks a budget, and filing that under
    # "could not tell" because a DIFFERENT unit was unresolved is the direction
    # that reads as caution and lands the batch.
    run("a unit convicted beyond the noise outranks a refusal on ANOTHER unit",
        {"base_rev": "0"*40, "head_rev": "1"*40, "planted": False,
         "box": "BOX synthetic — no measurement in this run", "decl_map": {},
         "readings": {"base": [{"modules": {"A": 1000.0, "B": 1000.0}, "decls": {}, "load1": 1.0},
                               {"modules": {"A": 1010.0, "B": 1010.0}, "decls": {}, "load1": 1.0},
                               {"modules": {"A":  990.0, "B":  990.0}, "decls": {}, "load1": 1.0}],
                      "head": [{"modules": {"A": 2000.0, "B": 1100.0}, "decls": {}, "load1": 1.0},
                               {"modules": {"A": 2010.0, "B": 1110.0}, "decls": {}, "load1": 1.0},
                               {"modules": {"A": 1990.0, "B": 1090.0}, "decls": {}, "load1": 1.0}]}},
        None, {"A": ("abs", 100.0), "B": ("abs", 100.0)}, 1, "does not soften this")

    # ⛔ THE HOLE THE RANGE LEFT OPEN AT THE OTHER END: `max - min` of ONE reading
    # is 0.0, so `--repeats 1` could never refuse and the gate returned a verdict
    # off a single pass a side with nothing said about its noise. A run that
    # cannot estimate its own noise has no verdict to give.
    run("one reading a side REFUSES — a run that cannot estimate its noise has "
        "no verdict",
        _explicit([1000.0], [1010.0]), None, {"M": ("abs", 100.0)},
        3, "fewer than two readings")

    # ⛔ a unit present on one side only: silence here would report "no change"
    # about the one direction that is certainly a change.
    run("a unit NEW in head is flagged",
        {"base_rev": "0"*40, "head_rev": "1"*40, "planted": False, "box": "BOX synthetic",
         "decl_map": {}, "readings": {"base": [{"modules": {}, "decls": {}, "load1": 1.0}] * 2,
                                      "head": [{"modules": {"N": 10.0}, "decls": {}, "load1": 1.0}] * 2}},
        ("abs", 1000.0), {}, 0, "NEW unit in head")
    run("a unit GONE from head is flagged",
        {"base_rev": "0"*40, "head_rev": "1"*40, "planted": False, "box": "BOX synthetic",
         "decl_map": {}, "readings": {"base": [{"modules": {"N": 10.0}, "decls": {}, "load1": 1.0}] * 2,
                                      "head": [{"modules": {}, "decls": {}, "load1": 1.0}] * 2}},
        ("abs", 1000.0), {}, 0, "GONE from head")

    # ⭐⭐ THE RELATIVE FORM, DRIVEN IN BOTH DIRECTIONS.  A percentage budget is
    # the half of this file that is supposed to survive a change of machine, and
    # an untested portable claim is the kind this repository keeps paying for.
    run("a RELATIVE budget scales with the base reading (small base ⇒ tight)",
        _synthetic({"M": 100.0}, {"M": 120.0}), None, {"M": ("rel", 10.0)}, 1,
        "OVER BUDGET", floor=1.0)
    run("the same 10% on a ten-times-larger base PASSES the same delta",
        _synthetic({"M": 1000.0}, {"M": 1020.0}), None, {"M": ("rel", 10.0)}, 0,
        "ok", floor=1.0)
    # ⛔ AND THE FLOOR, WHICH IS WHAT STOPS A PERCENTAGE OF A TINY MODULE FROM
    # BEING A ROUNDING ERROR WEARING A GATE'S NAME.
    run("@floor lifts a percentage that is smaller than it",
        _synthetic({"M": 2.4}, {"M": 20.0}), None, {"M": ("rel", 10.0)}, 0,
        "ok", floor=50.0)
    run("@floor does NOT lift a delta above the floor",
        _synthetic({"M": 2.4}, {"M": 80.0}), None, {"M": ("rel", 10.0)}, 1,
        "OVER BUDGET", floor=50.0)
    # ⛔⛔ AND THE BUDGET FILE'S OWN FAILURE MODES, WHICH THE ARMS ABOVE CANNOT
    # REACH.  Everything above hands `verdict` budgets that were already parsed;
    # the parser's refusals are `sys.exit` and can only be observed in a CHILD.
    # A gate whose configuration file is unparseable must REFUSE — an
    # unparseable gate file that read as "no budgets" would report a clean run
    # about a file it could not read.
    probe = tempfile.mkdtemp(prefix="x86lean-budgetprobe-")
    saved = os.path.join(probe, "readings.json")
    json.dump(_synthetic({"M": 100.0}, {"M": 110.0}), open(saved, "w"))
    file_arms = [
        ("control: a well-formed budget file gives a verdict",
         "@floor 5\nM 50\n", 0, "delta gate: CLEAN"),
        ("a RELATIVE budget with no @floor REFUSES",
         "M 10%\n", 2, "no @floor"),
        ("a line whose last field is not a number REFUSES",
         "@floor 5\nM plenty\n", 2, "does not end in a number"),
        ("a one-word line REFUSES rather than being skipped",
         "@floor 5\nM\n", 2, "unparseable budget line"),
    ]
    for name, text, want_rc, want in file_arms:
        bf = os.path.join(probe, "budget.txt")
        open(bf, "w").write(text)
        r = subprocess.run([sys.executable, os.path.abspath(__file__),
                            "--readings", saved],
                           capture_output=True, text=True,
                           env=dict(os.environ, X86LEAN_DELTA_BUDGET=bf))
        out = r.stdout + r.stderr
        ok = r.returncode == want_rc and want in out
        arms.append(name)
        print(("  ✔ " if ok else "  ⛔ ") + name +
              ("" if ok else f"   (rc={r.returncode}, wanted {want_rc} / {want!r})"))
        if not ok:
            bad.append(name)
            for l in out.splitlines():
                print("      " + l)
    # ⛔ AND A MISSING FILE, WHICH IS THE ONE THAT LOOKS LIKE ABSENCE RATHER THAN
    # FAILURE: 0 budgets read as "nothing to gate" unless the gate refuses.
    r = subprocess.run([sys.executable, os.path.abspath(__file__), "--readings", saved],
                       capture_output=True, text=True,
                       env=dict(os.environ,
                                X86LEAN_DELTA_BUDGET=os.path.join(probe, "absent.txt")))
    ok = r.returncode == 2 and "no budget file" in (r.stdout + r.stderr)
    arms.append("a MISSING budget file REFUSES, it does not read as 'nothing to gate'")
    print(("  ✔ " if ok else "  ⛔ ") + arms[-1] +
          ("" if ok else f"   (rc={r.returncode})"))
    if not ok:
        bad.append(arms[-1])
    shutil.rmtree(probe, ignore_errors=True)

    # ── THE ARGUMENT READER (D173): an ignored flag started a profiling run ────
    def argv_arm(av, want_rc, name, plant=None):
        rc, _ = check_argv(av)
        arms.append(name)
        print(("  ✔ " if rc == want_rc else "  ⛔ ") + name +
              ("" if rc == want_rc else f"   (rc={rc}, wanted {want_rc})"))
        if rc != want_rc:
            bad.append(name)

    argv_arm(["--selftest"], 0, "CONTROL — a known flag is accepted")
    argv_arm(["--repeats", "6"], 0,
             "CONTROL — a value-taking flag's VALUE is not read as a flag "
             "(`--repeats 6`), which is how this guard breaks a correct call")
    argv_arm(["--head", "--selftest"], 0,
             "...and a value that LOOKS like a flag is still consumed as a value")
    argv_arm(["--list-jobs"], 2,
             "RED-FIRST — an unknown flag REFUSES instead of falling through to "
             "the two-worktree profiling run")
    argv_arm(["--repeats"], 2,
             "RED-FIRST — a value-taking flag with NO value refuses rather than "
             "silently using the default")
    argv_arm(["build"], 2,
             "RED-FIRST — a bare positional refuses; this tool takes none, so a "
             "bare word is a mistyped flag or an expanded glob")

    bn, bb = bias_cut_arms()
    arms.extend(bn)
    bad.extend(bb)

    jn, jb = selftest_measure_judgement()
    arms.extend(jn)
    bad.extend(jb)

    if bad:
        print(f"delta-gate selftest: FAIL ({len(bad)} of {len(arms)} arms)")
        return 1
    print(f"delta-gate selftest: PASS ({len(arms)} arms — the COMPARISON and the "
          f"BUDGET FILE only, with NO measurement in any of them. That is stated "
          f"rather than implied: a green here says nothing about whether the "
          f"profiler can see a code change. --selftest-measure is that arm.)")
    return 0


# ⭐⭐⭐ THE PLANT.  The helm asked for *"a planted constructor that doubles the
# delta"*, and this is literally that, with one constraint stated rather than
# quietly worked around.
#
# ⛔ A CONSTRUCTOR CANNOT BE PLANTED IN `Op`.  Adding one there leaves
# `opOperands`, `Op.anyLocked` and `Op.mnemonic` non-exhaustive in
# `X86/Syntax.lean` and breaks a further ~30 match sites in five other files —
# the tree would not compile, and a probe whose subject does not build measures
# nothing.
#
# ⭐ `PrefetchHint` IS THE ONE INDUCTIVE THAT CAN CARRY IT.  It is matched in
# exactly one place in the whole repository (`PrefetchHint.mnemonic`, and grep
# says so), so N constructors plus their N arms compile, change no other module,
# and put their entire cost in `X86.Syntax` — the unit whose real margin was two
# milliseconds. The plant is a REAL constructor addition to a REAL inductive,
# which is why it is preferred to a synthetic block of `decide` theorems.
def plant_constructors(n):
    def go(worktree):
        p = os.path.join(worktree, "X86", "Syntax.lean")
        s = open(p).read()
        ctors = "".join(f"  | plant{i}\n" for i in range(n))
        arms = "".join(f'  | .plant{i} => "prefetchplant{i}"\n' for i in range(n))
        s2 = s.replace("  | t0\n", "  | t0\n" + ctors, 1)
        s2 = s2.replace('  | .nta => "prefetchnta" | .t0 => "prefetcht0"\n',
                        '  | .nta => "prefetchnta" | .t0 => "prefetcht0"\n' + arms, 1)
        if s2 == s or ctors not in s2 or arms not in s2:
            print("⛔ the plant did not apply — X86/Syntax.lean's `PrefetchHint` no "
                  "longer has the shape this probe edits. A probe that silently "
                  "fails to create its condition reports the gate as sound.")
            sys.exit(2)
        open(p, "w").write(s2)
    return go


def selftest_measure():
    """⛔ THE TWO ARMS THAT NEED REAL TREES, AND THEY ARE THE POINT.

    Arm 1 is the NEGATIVE control and it is the one that could quietly invalidate
    everything: base and head at the SAME commit. Whatever this gate reports
    there is pure instrument — if it is not CLEAN with a delta near zero, every
    green it has ever printed was a green about the machine.

    Arm 2 is the helm's: a planted constructor. It is sized from arm 1's own
    measured spread rather than from a number I liked, so the arm cannot pass by
    being large enough to beat a budget that was never resolvable."""
    repeats = int(arg("--repeats", "2"))
    default_ms, budgets, floor = read_budgets(arg("--budget", BUDGET_FILE))
    head = arg("--head", "HEAD")
    bad = []

    # ⭐ THE ARMS' RAW READINGS ARE SAVED WHEN ASKED, because a measurement that
    # took eleven minutes should be re-judgeable against a changed budget in
    # seconds. `--readings` replays the VERDICT over them without re-measuring —
    # which is also the only honest way to re-judge, since a second measurement
    # would be a different afternoon.
    save = arg("--save-readings")
    print("── arm 1 (NEGATIVE CONTROL): base and head are the SAME commit")
    d0 = measure(head, head, repeats)
    if save:
        json.dump(d0, open(os.path.join(save, "arm1-identical.json"), "w"))
    rc0, lines0 = verdict(d0, default_ms, budgets, floor, quiet=True)
    us = {s: [units_of(r, d0["decl_map"]) for r in d0["readings"][s]] for s in ("base", "head")}
    keys = set(us["base"][0]) & set(us["head"][0])
    # ⛔ NAME THE UNIT, DO NOT ONLY SIZE IT. "worst unit delta 350 ms" is a number
    # a reader cannot act on; the unit is what says whether the instrument's noise
    # lands where the gate is tight or where it is loose.
    per_unit = {k: statistics.median([x[k] for x in us["head"]]) -
                   statistics.median([x[k] for x in us["base"]]) for k in keys}
    worst_unit = max(per_unit, key=lambda k: abs(per_unit[k]))
    worst = abs(per_unit[worst_unit])
    # ⛔⛔ WHAT THIS ARM MAY AND MAY NOT REQUIRE, AFTER D141. Identical trees have
    # a true delta of exactly zero, so a FAILED here (rc 1) is the arm's real
    # red: the gate convicted a commit that changed nothing, and every red it
    # has ever printed would be suspect. But rc 3 is NOT a defect in the gate —
    # it is the gate saying this box was too loud at this many repeats to certify
    # even a zero, which is a fact about the AFTERNOON and the arm reports it as
    # one with its price attached. Requiring rc 0 here would make the arm fail
    # whenever the box is busy, and an arm that reds for a reason outside the
    # code is an arm whose reds stop being read.
    ok0 = rc0 != 1
    verdicts = {0: "CLEAN", 1: "FAILED ⛔", 3: "UNMEASURABLE"}
    print(("  ✔ " if ok0 else "  ⛔ ") +
          f"identical trees ⇒ {verdicts.get(rc0, rc0)}; worst unit delta {worst:.1f} ms "
          f"on `{worst_unit}` — that is what this box invents between two copies "
          f"of one commit, and every budget has to clear it")
    if rc0 == 3:
        print("      ⚠️  a refusal on identical trees is a statement about THIS BOX "
              "at --repeats " f"{repeats}, not about the gate. The unit lines below "
              "carry the repeats that would decide it.")
        for l in lines0:
            if "·" in l or "UNMEASURABLE" in l:
                print("      " + l)

    # ⭐⭐⭐ THE NUMBER THIS ARM PRINTED FOR NINE BATCHES AND NOBODY CHECKED (D142).
    # Arm 1 has always said "worst unit delta N ms — that is what this box invents
    # between two copies of one commit, and every budget has to clear it", and
    # then nothing compared N with any budget. On 2026-09-05 N was 2,150 ms on
    # `Tests.Coverage` against a 1,980 ms budget, and the arm passed.
    #
    # ⛔ TWO DIFFERENT THINGS ARE DONE WITH IT, and conflating them is what made
    # the old line inert:
    #
    #  (a) AN ASSERTION, and it is about the CODE rather than the box. Identical
    #      trees have a true delta of exactly zero, so the invented delta must sit
    #      inside the run's OWN band. |delta| > K*se means this run produced a
    #      difference its own noise model cannot explain — a BIAS between the two
    #      sides, which no amount of load can excuse and which would sit inside
    #      every verdict the gate prints. That is box-independent, so it can red.
    #
    #  (b) A SCOPE STATEMENT, printed and not asserted: the budgets this box's
    #      invented delta does NOT clear today. Those are the units whose verdicts
    #      this afternoon are worth exactly as much as the box is quiet, and a
    #      reader of any CLEAN the gate prints should see that list beside it.
    #      Asserting it would red on a busy box, which is the defect D141 took out
    #      of this same arm. [[feedback-a-machine-calibrated-gate-belongs-where-it-is-calibrated]]
    biased, unclear = [], []
    cut = bias_cut(repeats, len(keys))
    detectable = bias_detectable(repeats, cut)
    for k in sorted(keys):
        bs = [x[k] for x in us["base"]]
        hs = [x[k] for x in us["head"]]
        d, se = per_unit[k], resolution(bs, hs)
        if se not in (float("inf"),) and abs(d) > cut * se:
            biased.append((k, d, cut * se))
        bud = effective(budgets.get(k, default_ms), statistics.median(bs), floor) \
            if (k in budgets or default_ms is not None) else None
        if bud is not None and abs(d) > bud:
            unclear.append((k, d, bud))
    ok_bias = not biased
    # ⛔ NOT A TASTE THRESHOLD. "Is this arm informative?" is answered against the
    # BUDGET FILE — a second source — and not against a number I liked: the arm
    # polices unit u only if the smallest bias it would report there, `cut * se_u`,
    # is SMALLER than the allowance the gate hands that unit. Where it is larger,
    # a bias big enough to flip a verdict would have passed this arm in silence.
    # [[feedback-widening-a-gate-needs-a-second-source]]
    unpoliced = []
    for k in sorted(keys):
        bs = [x[k] for x in us["base"]]
        se_k = resolution(bs, [x[k] for x in us["head"]])
        bud_k = effective(budgets.get(k, default_ms), statistics.median(bs), floor) \
            if (k in budgets or default_ms is not None) else None
        if bud_k is not None and (se_k == float("inf") or cut * se_k > bud_k):
            unpoliced.append((k, cut * se_k, bud_k))
    blind = len(unpoliced) == len([k for k in keys
                                   if k in budgets or default_ms is not None])
    print(("  ✔ " if ok_bias else "  ⛔ ") +
          f"the invented delta sits inside this run's own band on all "
          f"{len(keys)} units — identical trees produced no difference the run "
          f"cannot explain as its own noise")
    # ⛔ THE ARM MUST SAY WHAT IT COULD HAVE SEEN. Its cut is family-wise over
    # every unit, so it is NOT K_SIGMA, and at small `--repeats` it is enormous.
    # Printing the cut without the power beside it would be the same ungated
    # reassurance the old ±2σ wording was.
    print(f"      ℹ️  cut |d| > {cut:.2f}·se per unit (NOT K_SIGMA={K_SIGMA}): "
          f"family-wise {BIAS_ALPHA:.0%} over {len(keys)} units at --repeats "
          f"{repeats}; this arm catches a real bias of "
          + (f"{detectable:.1f}× one pass's own spread at 90% power"
             if detectable != float("inf") else "NO size at 90% power")
          + ".")
    if unpoliced:
        print(f"      {'⚠️  VOID, NOT A PASS' if blind else '⚠️  PARTIAL'}: on "
              f"{len(unpoliced)} unit(s) the smallest bias this arm would report "
              f"is LARGER than that unit's own allowance, so a bias big enough to "
              f"flip a verdict passes it in silence"
              + (". EVERY budgeted unit is in that state, so the ✔ above is the "
                 "arm saying nothing." if blind else ":"))
        for k, thr, bud in unpoliced[:6]:
            print(f"         · {k}: would report only a bias above "
                  f"±{thr:.1f} ms, against a {bud:.1f} ms allowance")
        if len(unpoliced) > 6:
            print(f"         · … and {len(unpoliced)-6} more")
        print(f"      ⇒ raise --repeats (the cut falls {bias_cut(repeats, len(keys)):.1f} "
              f"→ {bias_cut(max(repeats*2, 4), len(keys)):.1f} at "
              f"--repeats {max(repeats*2, 4)}), or read this arm as unrun.")
    if not ok_bias:
        bad.append("identical-trees BIAS")
        for k, d, band in biased:
            print(f"      ⛔ {k}: invented {d:+.1f} ms against a family-wise cut of "
                  f"±{band:.1f} "
                  f"— a systematic difference between two copies of ONE commit, "
                  f"which rides inside every delta this gate reports")
    if unclear:
        print(f"      ⚠️  SCOPE, not a failure: this box's invented delta exceeds "
              f"{len(unclear)} unit(s) own budget today, so a verdict on those "
              f"units is worth what the box is quiet:")
        for k, d, bud in unclear:
            print(f"         · {k}: invented {d:+.1f} ms against a {bud:.1f} ms budget")
    else:
        # ⛔ THIS ✔ SITS DIRECTLY UNDER THE UNPOLICED LIST AND MUST NOT READ AS
        # CANCELLING IT. They are different quantities: this one says the delta
        # the run OBSERVED is small, the list above says the smallest delta the
        # arm COULD HAVE REPORTED is large. A reassuring line beside a warning is
        # how the warning stops being read.
        # [[feedback-ungated-prose-overclaims]]
        print(f"      ✔ and the invented delta this run OBSERVED clears every "
              f"unit's budget — which is NOT the claim above it: that the arm "
              f"could SEE a bias worth that budget. This line is about what "
              f"happened; that one is about what would have been reported.")
    if not ok0:
        bad.append("identical-trees control")
        for l in lines0:
            print("      " + l)

    print("── arm 2 (THE HELM'S RED-FIRST): a planted constructor must FAIL")
    # ⚠️ SIZED FROM ARM 1, NOT FROM TASTE. The plant has to exceed the budget of
    # the unit it lands in by a margin larger than the instrument's own noise,
    # and arm 1 is where that noise was just measured on these very trees.
    syn_base = statistics.median([units_of(r, d0["decl_map"])["X86.Syntax"]
                                  for r in d0["readings"]["base"]])
    syn_budget = effective(budgets.get("X86.Syntax", default_ms), syn_base, floor)
    # ⛔⛔ THE PLANT SIZE IS CALIBRATED, AND THE FIRST SIZE WAS TOO SMALL TO CREATE
    # THE CONDITION — MEASURED, and the arm FAILED rather than passing quietly.
    # 48 planted constructors moved `X86.Syntax` **+16.0 ms** (0.33 ms each)
    # against a 27.4 ms budget: rc 0 where 1 was wanted. The arm would otherwise
    # have reported the gate sound while planting something the gate is right to
    # ignore ([[feedback-a-probe-must-create-its-condition]]).
    # ⚠️ AND THE FIRST FIGURE I READ FOR IT WAS +6 ms, off two single passes of a
    # four-pass run before the medians existed. The arm's own summary line is the
    # reading; a pass line is not ([[feedback-read-what-the-instrument-measured]]).
    #
    # ⇒ 🔑 A CONSTRUCTOR ON A FRESH INDUCTIVE COSTS A THIRD OF A MILLISECOND; A
    # REAL `Op` CONSTRUCTOR COSTS EIGHT. The difference is not the constructor —
    # it is three total match functions over a ~200-constructor inductive each
    # growing an arm, and a roster row. Measuring that gap is what the first
    # plant bought, and it is why a plant sized to a real constructor would not
    # have cleared the budget either.
    #
    # The plant must clear the BUDGET, not a real constructor: the budget is ~40 ms
    # because that is what this box can resolve.
    #
    # ⭐⭐ AND THE LINEAR ESTIMATE BEHIND 512 WAS WRONG BY 4.3x, WHICH IS EXACTLY
    # WHY THE ARM PRINTS ITS MEASURED DELTA. At 0.33 ms a constructor the
    # prediction was ~170 ms; measured, 512 constructors cost **+723.0 ms** —
    # 1.41 ms each. 10.7x the constructors bought 45x the cost, so the match
    # compiler is SUPER-LINEAR in the arm count and a plant sized by extrapolation
    # is a plant sized by a model nobody checked. The over-shoot (18x the budget)
    # is the right direction for a probe and it is stated rather than trimmed.
    n = int(arg("--plant", "512"))
    d1 = measure(head, head, repeats, plant=plant_constructors(n))
    if save:
        json.dump(d1, open(os.path.join(save, "arm2-planted.json"), "w"))
    rc1, lines1 = verdict(d1, default_ms, budgets, floor, quiet=True)
    us1 = {s: [units_of(r, d1["decl_map"]) for r in d1["readings"][s]] for s in ("base", "head")}
    dsyn = (statistics.median([x["X86.Syntax"] for x in us1["head"]]) -
            statistics.median([x["X86.Syntax"] for x in us1["base"]]))
    ok1 = rc1 == 1 and "OVER BUDGET" in "\n".join(lines1)
    print(("  ✔ " if ok1 else "  ⛔ ") +
          f"{n} planted constructors ⇒ rc {rc1} (wanted 1); X86.Syntax delta "
          f"{dsyn:+.1f} ms against a {syn_budget:.1f} ms budget and a {worst:.1f} ms "
          f"control spread")
    if not ok1:
        bad.append("planted-constructor arm")
        for l in lines1:
            print("      " + l)

    if bad:
        print(f"delta-gate measured selftest: FAIL ({len(bad)} of 2 arms)")
        return 1
    print("delta-gate measured selftest: PASS (2 arms — the identical-trees "
          "control and the planted constructor)")
    return 0


# ⛔⛔ THE SAME UNKNOWN-FLAG DEFECT AS `ci_local.py`, AND HERE THE DEFAULT PATH IS
# A TWO-TREE PROFILING RUN (D173). `arg()` ignores what it does not know, so
# `kernel_delta.py --help` fell straight through to the merge gate and began
# profiling two worktrees — minutes to an hour — in answer to a request for the
# usage text. `--help` is the first thing a relit head types.
# ⛔ THE VALUE-TAKING FLAGS MUST BE LISTED, or their VALUE is read as an unknown
# flag and a correct invocation refuses. Both halves are driven in --selftest.
# [[feedback-a-gate-that-refuses-must-say-what-it-saw]]
KNOWN_FLAGS = {"--selftest", "--selftest-measure", "--budget", "--readings",
               "--head", "--base", "--repeats", "--out", "--save-readings",
               "--plant", "--help", "-h"}
VALUED_FLAGS = {"--budget", "--readings", "--head", "--base", "--repeats",
                "--out", "--save-readings", "--plant"}


def check_argv(argv=None):
    """(rc, message) — 0 and None when every argument is recognised."""
    av = sys.argv[1:] if argv is None else argv
    bad, dangling, skip = [], None, False
    for a in av:
        if skip:
            skip = False
            continue
        if a in VALUED_FLAGS:
            skip = True
            dangling = a          # cleared by the next argument, if there is one
            continue
        dangling = None
        if a in KNOWN_FLAGS:
            continue
        bad.append(a)
    if skip:
        # ⛔ FOUND BY THIS GUARD'S OWN RED-FIRST ARM, which is why it is here:
        # `--repeats` with nothing after it passed the first form of this check,
        # and `arg()` then returned the DEFAULT. A flag whose value went missing
        # is the same silent-default defect one level in.
        return 2, (f"⛔ {dangling!r} takes a value and none follows it. "
                   f"`arg()` would have returned this flag's DEFAULT, so the run "
                   f"would have used a setting you did not ask for and said "
                   f"nothing.")
    if bad:
        return 2, (f"⛔ unrecognised argument(s): "
                   f"{', '.join(repr(b) for b in bad)}.\n"
                   f"   This gate's DEFAULT path profiles two worktrees, so an "
                   f"ignored flag would have started a run of minutes, not "
                   f"answered you. Known: {', '.join(sorted(KNOWN_FLAGS))}.")
    return 0, None


def main():
    rc, msg = check_argv()
    if rc:
        print(msg)
        return rc
    if "--help" in sys.argv or "-h" in sys.argv:
        print(__doc__)
        return 0
    if "--selftest" in sys.argv:
        return selftest()
    if "--selftest-measure" in sys.argv:
        return selftest_measure()
    default_ms, budgets, floor = read_budgets(arg("--budget", BUDGET_FILE))
    saved = arg("--readings")
    if saved:
        data = json.load(open(saved))
        rc, _ = verdict(data, default_ms, budgets, floor)
        absolute_readings(data)
        return rc
    head = arg("--head", "HEAD")
    base = arg("--base") or resolve_base(head)
    print(f"── measuring the delta {base[:9]} → {git('rev-parse', head)[:9]}")
    data = measure(base, head, int(arg("--repeats", "3")))
    out = arg("--out")
    if out:
        json.dump(data, open(out, "w"))
        print(f"readings → {out}")
    rc, _ = verdict(data, default_ms, budgets, floor)
    absolute_readings(data)
    return rc


# ⛔ GUARDED 2026-09-05 (D148) SO THIS GATE CAN BE IMPORTED RATHER THAN COPIED.
# `deterministic_cost.py` needs the SAME resolution rule this gate applies, and
# the repository already carries one copy of the band arithmetic beside the
# original (`delta_band_calibration.v_band`). A third copy would have been born
# in agreement and diverged on the next ordinary edit
# ([[feedback-a-duplicate-born-in-agreement]]). Run as a script this is
# unchanged: `python3 scripts/kernel_delta.py ...` still enters `main()`.
if __name__ == "__main__":
    sys.exit(main())
