#!/usr/bin/env python3
"""HOW BIG CAN THE NEXT VECTOR BATCH BE — measured on a plant, not divided out
of one batch's quotient.

WHY THIS EXISTS.  `docs/QUEUE.md` item 2a and two consecutive banks carried the
same sizing rule, in the same words: *"`vectorCoverage` affords ~24 vectors a
batch at ~11 ms each against a 260.6 ms allowance; batch 34 spent 21, so the
move half at both operand shapes is 30+ vectors and will not fit."*  Every
number in that sentence is a real reading and the conclusion it reaches is
right, and the rule is still wrong in the way that matters, because it is keyed
to the WRONG QUANTITY.  It was obtained by dividing ONE batch's delta by the
count of the thing that batch visibly added.

⭐⭐ WHAT THE DECLARATION ACTUALLY COSTS.  `X86.Tests.vectorCoverage` is not a
sweep over vectors.  Read its four conjuncts (`Tests/Coverage.lean`):

    mnemonicRuns == vectorRunIdx.map (fun i => tableMnemonics.getD i "")
    && (List.range rosterSize).all (fun i => vectorRunIdx.contains i)
    && vectorRunIdx.all (fun i => i < rosterSize)
    && (vectorRunIdx.eraseDups.length == rosterSize)

Conjunct 2 is `rosterSize` membership tests over a list of `runs` — O(rows x
runs).  Conjunct 4's `eraseDups` is O(runs^2).  Conjunct 1's `getD` is O(rows)
per run.  The VECTORS enter once, linearly, through `collapseAdjacent`, and
that term is the one the shipped kernel barely charges for.  ⇒ the growth law is
QUADRATIC IN (rows x runs) AND FLAT IN VECTORS, and a per-vector price is a
per-mnemonic price wearing the denominator of whatever vectors-per-mnemonic
ratio the batch it was divided out of happened to have.

📊 MEASURED, and the two models predict OPPOSITE SIGNS so the run can lose:

    arm                        Δ vs base     per-vector model   per-row model
    +30 vectors, +0 mnemonics     −10 ms        predicts +330      predicts +160
    +15 mnemonics, +15 vectors   +370 ms        predicts +165      predicts +340

  ⇒ vectors cost 0.0 ms.  A new MNEMONIC costs ~25 ms, which is also what batch
    34 paid (230/9 = 25.6) and what the twelve-commit history pays (22.5 by
    least squares, 27.3 by endpoints).  The per-ROW figure reproduces across
    three independent routes; the per-VECTOR figure does not survive a change of
    mix.  [[feedback-match-the-gate-units-to-the-growth-law]]
    [[feedback-a-total-cannot-see-its-parts]]

⭐ The positive control is the second witness to the law: doubling every
dimension reads 4.13x, not 2x.  A quadratic instrument announcing itself.

⛔⛔ AND THE ALLOWANCE IS NOT 260.6 ms.  `scripts/kernel_delta_budget.txt` sets
`Tests.Coverage @decl vectorCoverage 15.7%` — a PERCENTAGE OF THE BASE.  260.6
was that percentage times one particular base, quoted onward as a constant.  It
matters in a direction nobody would guess: the marginal cost of a mnemonic grows
like R while a percentage budget grows like R^2, so

    k_max ≈ 0.157 · R·U / (U + 2R)  ≈  0.074 · R      (at U ≈ 1.8R)

THE AFFORDABLE BATCH GROWS WITH THE ROSTER — ~10 mnemonics at R=144, ~15 at
R=200, ~22 at R=300.  Read with the fixed 260.6, the same arithmetic says batch
sizes shrink toward zero and the gate must be redesigned soon.  That conclusion
is an artefact of freezing a percentage into a number.
[[feedback-a-citation-is-an-ungated-claim]]

WHAT IS DERIVED AND WHAT IS DECLARED.  The shape of the theorem is COPIED from
the shipped one and the budget is READ from `kernel_delta_budget.txt`.  The
plant's data is synthetic, so its absolute level is its own; only its RATIOS
transfer.  `--calibrate` is what licenses that: it replays P2 batch 34's real
transition (134/239/954 -> 144/260/977) and requires the plant to reproduce the
+230.0 ms that `kernel_delta.py` actually measured.  Two runs read +210 and
+240 against that +230.  [[feedback-a-ratio-travels-where-a-ceiling-cannot]]

⛔ WHAT THIS DOES NOT PROVE.  The plant is not the shipped declaration: its
strings are `m0..mN` and it carries no other declaration.  It predicts a DELTA
and it has been checked against exactly one real batch.  Treat a number here as
a batch-sizing estimate, never as a merge verdict — the merge gate is
`kernel_delta.py` and nothing here replaces it.
"""
import argparse, os, re, statistics, subprocess, sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
BUDGET_FILE = os.path.join(ROOT, "scripts", "kernel_delta_budget.txt")
UNIT = "Tests.Coverage @decl vectorCoverage"

# today's shipped shape, read by --shape rather than pinned here
SHIPPED_DEFAULT = (144, 260, 977)
# P2 batch 34's real transition and the delta `kernel_delta.py` measured for it
B34_PRE, B34_POST, B34_DELTA = (134, 239, 954), (144, 260, 977), 230.0


def read_budget_pct():
    """The unit's budget, READ from the gate's own file, never pinned here."""
    for ln in open(BUDGET_FILE):
        ln = ln.strip()
        if ln.startswith(UNIT + " ") and ln.endswith("%"):
            return float(ln[len(UNIT):-1])
    raise SystemExit("⛔ REFUSING: no budget line for %r in %s" % (UNIT, BUDGET_FILE))


def shipped_shape():
    """rows/runs/vectors read from the tree, so a stale literal cannot survive."""
    cov = open(os.path.join(ROOT, "Tests", "Coverage.lean")).read()
    rows = int(re.search(r"roster_size_is_(\d+)", cov).group(1))
    vecs = int(re.search(r"vector_count_is_(\d+)", cov).group(1))
    runsrc = open(os.path.join(ROOT, "Tests", "VectorRuns.lean")).read()
    body = re.search(r"def vectorRunIdx[^\[]*\[(.*?)\]", runsrc, re.S).group(1)
    runs = len([x for x in body.replace("\n", " ").split(",") if x.strip()])
    return rows, runs, vecs


def build(rows, runs, vectors):
    assert runs >= rows and vectors >= runs
    idx, i = list(range(rows)), 0
    while len(idx) < runs:
        v = i % rows
        if v == idx[-1]:
            v = (v + 1) % rows
        idx.append(v)
        i += 1
    per = [vectors // runs] * runs
    for k in range(vectors - sum(per)):
        per[k] += 1
    vec = []
    for r, n in zip(idx, per):
        vec.extend(["m%d" % r] * n)
    return idx, vec


def emit(rows, runs, vectors, path, lie=False):
    """`lie=True` writes a plant whose theorem is FALSE — conjunct 2 asks for a
    row index no run names — so a run that does not REFUSE it is a run in which
    nothing was being kernel-checked at all."""
    idx, vec = build(rows, runs, vectors)
    q = lambda xs, s: "[" + ", ".join(('"%s"' % x) if s else str(x) for x in xs) + "]"
    open(path, "w").write('''-- GENERATED PLANT — rows=%d runs=%d vectors=%d%s
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000
namespace Plant

def collapseAdjacent : List String → List String
  | [] => []
  | [a] => [a]
  | a :: b :: t => if a == b then collapseAdjacent (b :: t) else a :: collapseAdjacent (b :: t)

def rosterSize : Nat := %d
def tableMnemonics : List String := %s
def vecMnemonics : List String := %s
def mnemonicRuns : List String := collapseAdjacent vecMnemonics
def vectorRunIdx : List Nat := %s

theorem plantCoverage :
    (mnemonicRuns == vectorRunIdx.map (fun i => tableMnemonics.getD i "")
     && (List.range rosterSize).all (fun i => vectorRunIdx.contains i)
     && vectorRunIdx.all (fun i => i < rosterSize)
     && (vectorRunIdx.eraseDups.length == rosterSize)) = true := by decide

end Plant
''' % (rows, runs, vectors, "  (LYING PLANT — must be REFUSED)" if lie else "",
       rows + (1 if lie else 0),
       q(["m%d" % i for i in range(rows + (1 if lie else 0))], True),
       q(vec, True), q(idx, False)))


def profile(shape, path, lie=False):
    emit(*shape, path, lie=lie)
    la = os.getloadavg()[0]
    r = subprocess.run(["lake", "env", "lean", "-D", "profiler=true",
                        "-D", "profiler.threshold=1", path],
                       capture_output=True, text=True, cwd=ROOT)
    out = r.stderr + r.stdout
    if r.returncode != 0:
        return None, la
    cum = out.split("cumulative profiling times:")[-1]
    m = re.search(r"^\s*type checking ([\d.]+)(ms|s)\s*$", cum, re.M)
    if not m:
        return None, la
    return float(m.group(1)) * (1000.0 if m.group(2) == "s" else 1.0), la


def med(shape, path, n):
    vs, ls = [], []
    for _ in range(n):
        v, la = profile(shape, path)
        ls.append(la)
        if v is not None:
            vs.append(v)
    if not vs:
        raise SystemExit("⛔ REFUSING: the plant produced no reading at %r" % (shape,))
    return statistics.median(vs), vs, ls


def tmp(name="p2_batch_size_plant.lean"):
    return os.path.join(os.environ.get("TMPDIR", "/tmp"), name)


def cmd_size(args):
    path = tmp()
    pct = read_budget_pct()
    shape = shipped_shape() if not args.shape else tuple(int(x) for x in args.shape.split("/"))
    print("SHIPPED SHAPE (read from the tree): %d rows / %d runs / %d vectors" % shape)
    print("BUDGET (read from kernel_delta_budget.txt): %.1f%% of the base\n" % pct)
    base, vs, ls = med(shape, path, args.repeats)
    print("plant base %.0f ms   readings %s" % (base, [round(x) for x in vs]))
    print("⚠️  the plant's LEVEL is its own; only the RATIO below transfers.\n")
    print("  each new mnemonic at BOTH operand shapes = +1 row, +2 runs, +2 vectors")
    print("  (batch 34's runs grew by exactly its vector count: each vector its own run)\n")
    print("  %9s %18s %10s %9s   %s" % ("mnemonics", "shape", "plant Δ", "ratio", "verdict"))
    allls = list(ls)
    for k in args.ks:
        sh = (shape[0] + k, shape[1] + 2 * k, shape[2] + 2 * k)
        v, _, l2 = med(sh, path, args.repeats)
        allls += l2
        d = v - base
        ratio = 100.0 * d / base
        # a CLEAN `ok` needs delta + K*se < budget; K=2 and the band batch 34
        # actually saw was ±39.2 ms on a ~1730 ms base = 2.3 percentage points.
        verdict = ("✅ clean" if ratio + 2.3 < pct else
                   "⚠️  UNMEASURABLE (band straddles)" if ratio < pct else "⛔ OVER")
        print("  %9d %18s %+10.0f %8.1f%%   %s"
              % (k, "%d/%d/%d" % sh, d, ratio, verdict))
    print("\nCONDITIONS: load1 %.2f-%.2f over %d passes" % (min(allls), max(allls), len(allls)))
    R, U = shape[0], shape[1]
    print("MODEL: k_max ≈ %.1f mnemonics  (0.%03d · R·U/(U+2R), R=%d U=%d)"
          % (pct / 100.0 * R * U / (U + 2 * R), int(pct * 10), R, U))


def cmd_calibrate(args):
    path = tmp()
    print("CALIBRATION — does the plant reproduce a REAL measured batch delta?")
    print("  P2 batch 34 moved %d/%d/%d -> %d/%d/%d and kernel_delta.py measured %+.1f ms\n"
          % (B34_PRE + B34_POST + (B34_DELTA,)))
    pre, vpre, _ = med(B34_PRE, path, args.repeats)
    post, vpost, _ = med(B34_POST, path, args.repeats)
    d = post - pre
    print("  plant PRE  %d/%d/%d  %7.0f ms  %s" % (B34_PRE + (pre, [round(x) for x in vpre])))
    print("  plant POST %d/%d/%d  %7.0f ms  %s" % (B34_POST + (post, [round(x) for x in vpost])))
    print("  plant Δ = %+.0f ms   vs the real %+.1f ms   ratio %.2fx" % (d, B34_DELTA, d / B34_DELTA))
    ok = 0.75 <= d / B34_DELTA <= 1.35
    print("  %s" % ("✅ the plant tracks the shipped declaration" if ok else
                    "⛔ THE PLANT DOES NOT TRACK THE SHIPPED DECLARATION — do not size on it"))
    return 0 if ok else 1


def cmd_check():
    """The CI-cheap half: the three arms that need no Lean toolchain.

    ⛔ These are the arms that would have caught the defect this file exists for.
    It was never a wrong measurement — it was PROSE: a rule keyed to the wrong
    quantity, sitting in the most-read planning doc, reproduced verbatim into two
    banks because it read like arithmetic.  The queue's own law is *"a row's
    PRICE is a derived number or it is absent, and prices name the tool that
    prints them"*; arm 3 is that law made enforceable for this one price.
    [[feedback-ungated-prose-overclaims]] [[feedback-a-citation-is-an-ungated-claim]]
    """
    bad = []
    try:
        pct = read_budget_pct()
        print("✅ the budget line is present and parseable: %s %.1f%%" % (UNIT, pct))
    except SystemExit as e:
        print("⛔ %s" % e)
        bad.append("budget")
    try:
        print("✅ the shipped shape is readable from the tree: %d/%d/%d" % shipped_shape())
    except Exception as e:
        print("⛔ the shipped shape is unreadable (%s) — a moved literal" % e)
        bad.append("shape")
    q = os.path.join(ROOT, "docs", "QUEUE.md")
    txt = open(q).read() if os.path.exists(q) else ""
    if "p2_batch_size.py" in txt:
        print("✅ docs/QUEUE.md names the tool that prints the batch-size price")
    else:
        print("⛔ docs/QUEUE.md states a batch size without naming the tool that derives it")
        bad.append("queue-price-unsourced")
    print("\ncheck: %d/3 arms green" % (3 - len(bad)))
    return 1 if bad else 0


def selftest():
    """Control first, then arms that can each fail on their own."""
    path, fails = tmp("p2_batch_size_selftest.lean"), []
    shape = SHIPPED_DEFAULT

    # ARM 0 — THE CONTROL, FIRST.  A broken harness reds every arm below it.
    base, vs, _ = med(shape, path, 2)
    if base <= 0:
        print("⛔ CONTROL FAILED — no reading; every arm below would be noise.")
        return 1
    print("✅ arm 0 CONTROL: baseline reads %.0f ms — the instrument responds." % base)

    # ARM 1 — the LYING plant must be REFUSED.  Without this, a run in which the
    # kernel checked nothing would time out at a plausible-looking number.
    v, _ = profile(shape, path, lie=True)
    if v is None:
        print("✅ arm 1 the lying plant is REFUSED — the theorem is really kernel-checked.")
    else:
        print("⛔ arm 1 A FALSE THEOREM WAS ACCEPTED (%.0f ms) — timings measure nothing." % v)
        fails.append("lying-plant-accepted")

    # ARM 2 — positive control: doubling every dimension must move it, a lot.
    dbl, _, _ = med((shape[0] * 2, shape[1] * 2, shape[2] * 2), path, 1)
    if dbl / base >= 2.0:
        print("✅ arm 2 positive control: doubling reads %.2fx (quadratic, >= 2x)." % (dbl / base))
    else:
        print("⛔ arm 2 doubling read only %.2fx — the instrument stopped responding." % (dbl / base))
        fails.append("positive-control-flat")

    # ARM 3 — THE FINDING, as a gate: +vectors must cost LESS than +mnemonics.
    # If this ever flips, the growth law changed and the sizing rule is void.
    dv, _, _ = med((shape[0], shape[1], shape[2] + 30), path, 2)
    dr, _, _ = med((shape[0] + 15, shape[1] + 15, shape[2] + 15), path, 2)
    if (dr - base) > (dv - base):
        print("✅ arm 3 mnemonics dominate vectors: Δrows %+.0f > Δvectors %+.0f."
              % (dr - base, dv - base))
    else:
        print("⛔ arm 3 THE GROWTH LAW FLIPPED: Δrows %+.0f <= Δvectors %+.0f."
              % (dr - base, dv - base))
        fails.append("growth-law-flipped")

    # ARM 4 — the budget is READ, and a missing line must refuse rather than default.
    try:
        pct = read_budget_pct()
        print("✅ arm 4 budget read from the gate's own file: %.1f%%." % pct)
    except SystemExit:
        print("⛔ arm 4 could not read the budget.")
        fails.append("budget-unreadable")

    # ARM 5 — the shipped shape is READ from the tree, not pinned.
    try:
        sh = shipped_shape()
        print("✅ arm 5 shipped shape read from the tree: %d/%d/%d." % sh)
    except Exception as e:
        print("⛔ arm 5 could not read the shipped shape: %s" % e)
        fails.append("shape-unreadable")

    print("\nselftest: %d/%d arms green" % (6 - len(fails), 6))
    return 1 if fails else 0


if __name__ == "__main__":
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--selftest", action="store_true", help="run the arms and exit")
    ap.add_argument("--check", action="store_true",
                    help="the three arms that need no Lean toolchain (CI)")
    ap.add_argument("--calibrate", action="store_true",
                    help="replay P2 batch 34 and require the plant to reproduce its real delta")
    ap.add_argument("--shape", help="rows/runs/vectors override (default: read from the tree)")
    ap.add_argument("--ks", type=int, nargs="+", default=[2, 4, 6, 8, 10, 12, 15],
                    help="mnemonic counts to price")
    ap.add_argument("--repeats", type=int, default=3,
                    help="passes per shape (⛔ D153: the spread SATURATES at n≈3-4)")
    a = ap.parse_args()
    if a.check:
        sys.exit(cmd_check())
    if a.selftest:
        sys.exit(selftest())
    if a.calibrate:
        sys.exit(cmd_calibrate(a))
    sys.exit(cmd_size(a) or 0)
