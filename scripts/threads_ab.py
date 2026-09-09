#!/usr/bin/env python3
"""QUEUE item 4c — IS THE GATED NUMBER A WALL-CLOCK READING TAKEN UNDER LEAN'S
OWN PARALLELISM, AND DOES SERIALISING THE ELABORATOR REDUCE ITS VARIANCE?

⭐⭐ WHY THIS EXISTS.  The kernel-delta gate (`scripts/kernel_delta.py`) is built
on the profiler's cumulative `type checking` time, and D141/D142 measured what
that instrument can resolve: the SAME COMMIT on both sides invented a −2,150 ms
delta on a unit with a 1,980 ms budget and returned `ok`.  QUEUE item 4's object
is therefore not "widen a budget" but **reduce the variance of the measurement,
or gate a quantity that has less of it**.  D146 refuted route 4b's first
candidate (heartbeats) and left route 4c RECORDED AND UNMEASURED:

  the profiler's cumulative block reads `tactic execution 47.8s` against
  `type checking 26.2s`, and `user` is ~2x `real` ⇒ Lean elaborates this module
  on several threads, and EVERY number the gate reads is a per-task WALL-CLOCK
  reading taken under contention.  `scripts/kernel_cost.py` never passes
  `lean -j/--threads`, so it takes the default.

`--threads 1` changes HOW THE SAME QUANTITY IS MEASURED rather than WHICH
quantity is gated, which is why it is cheap: no budget is re-derived from the
thing it checks, no second machine is needed, and the two arms differ in exactly
one flag.  [[feedback-widening-a-gate-needs-a-second-source]]

## WHAT THIS SCRIPT MEASURES, AND WHAT IT CANNOT

MEASURED, per reading: the profiler's cumulative `type checking` ms (the gate's
own parse, copied from `kernel_cost.kernel_ms`), the child's `real`/`user`/`sys`
from `getrusage(RUSAGE_CHILDREN)` deltas, and the machine's 1-minute load either
side.  A tool that prints a timing without its conditions hands on a number
nobody can compare.  [[feedback-a-measurement-without-its-conditions]]

NOT MEASURED: anything about a second machine, and anything about the DELTA gate
end to end — this measures the variance of ONE tree's reading, which is what
drives the delta's band.  A change of arm would require every budget in
`scripts/kernel_ceilings.txt` and `scripts/kernel_delta_budget.txt` to be
re-derived from a second source before it could be gated.

## ⛔ THE ARM ORDER IS ALTERNATED, AND WHY THAT IS NOT FUSSINESS

The box this runs on carries other seats' builds; its load moved 39 -> 52 while
this file was being written.  A block of A readings followed by a block of B
readings measures the HOUR as much as the flag.  Rounds alternate A,B / B,A so a
monotone drift falls on both arms equally, and every reading carries its own
load so the drift is visible rather than assumed away.
[[feedback-a-single-reading-is-about-its-run]]

## ⛔⛔ THE POSITIVE CONTROL, IN THE SAME RUN

A quiet arm is what a broken instrument prints.  If `--threads 1` reduced the
variance because the reading stopped responding to the work, the CV table would
look like a triumph.  So each round also profiles a PLANT whose only change is
the size of the DATA the kernel reduces (D146 §2's shape: `bigList` and a
`decide` over it), at two sizes, IN BOTH ARMS.  The control FAILS unless both
arms report the bigger plant as bigger by a comparable factor.
[[feedback-a-probe-must-create-its-condition]]

usage: threads_ab.py [--rounds N] [--out FILE] [--units "a.lean b.lean"]
       threads_ab.py --selftest
"""

import json, os, re, statistics, subprocess, sys, tempfile, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from portable import child_cpu, sub_cpu  # noqa: E402
import scratch  # scratch dirs that get removed (591 MB leak, 2026-09-09)

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

# The gated units.  `Tests/Coverage.lean` is the unit every batch waits on;
# the other three are the small units whose bands moved 3-5x between two runs an
# hour apart (D142), which is the disagreement item 4 exists to settle.
UNITS = ["Tests/Coverage.lean", "X86/Basic.lean", "X86/Semantics.lean",
         "X86/Value.lean"]

# The plant's two data sizes.  D146 measured 82 ms at N=2000 and 460 ms at
# N=8000 for this shape, so the control costs well under a second per reading.
PLANT_SMALL, PLANT_BIG = 2000, 8000
PLANT_MIN_RATIO = 2.0    # the big plant must read at least this much bigger


def arg(name, default=None):
    return sys.argv[sys.argv.index(name) + 1] if name in sys.argv else default


# ⛔ THE PARSE IS THE GATE'S OWN, COPIED AND NOT RE-INVENTED.  A measurement of
# the gated quantity that parses it differently is a measurement of something
# else.  The refusals are copied with it: a run with no cumulative block at all
# is a FAILED READING, never a zero.  [[feedback-verify-what-the-build-command-builds]]
def parse_type_checking(blob):
    m = re.search(r'^\s*type checking\s+([\d.]+)(ms|s)\s*$', blob, re.M)
    if not m:
        if "cumulative profiling times" in blob:
            return 0.0
        return None
    v = float(m.group(1))
    return v * 1000 if m.group(2) == "s" else v


def loadavg():
    return os.getloadavg()[0]


# ⛔⛔ A LOAD AVERAGE IS THE WRONG CONDITIONS METRIC ON THIS BOX (D149).  Measured
# tonight: a 1-minute load of 282 with `top` reading 0.0% idle, 44% user and 55%
# SYSTEM, and exactly one `lean` at 160% CPU — the number was dominated by
# short-lived runnable processes, not by compute.  A reading taken at "load 282"
# and one taken at "load 40" can describe the same machine.  IDLE PERCENT is the
# quantity a wall-clock reading actually competes with, so it rides beside the
# load in every record this tool writes.  `kernel_cost.py` still records load
# alone; porting this is QUEUE item 7.
# [[feedback-a-measurement-without-its-conditions]]
def idle_pct():
    """CPU idle % over a 1-second sample, or None if it cannot be read.

    ⚠️ Returns None rather than a default: a conditions field that silently
    reads 0.0 when the instrument failed is worse than an absent one, because a
    reader cannot tell a busy box from a broken probe."""
    try:
        r = subprocess.run(["top", "-l", "2", "-n", "0", "-s", "1"],
                           capture_output=True, text=True, timeout=20)
        vals = re.findall(r"CPU usage:.*?([\d.]+)% idle", r.stdout)
        return float(vals[-1]) if vals else None
    except Exception:
        return None


def profile(path, threads, cwd=ROOT):
    """One profiler pass.  Returns the reading dict, or raises on a failed read."""
    cmd = ["lake", "env", "lean"]
    if threads is not None:
        cmd += ["--threads", str(threads)]
    cmd += ["-D", "profiler=true", "-D", "profiler.threshold=100000", path]
    l0, idle0 = loadavg(), idle_pct()
    ru0 = child_cpu()          # (user_s, sys_s, source) — absent off POSIX
    t0 = time.time()
    r = subprocess.run(cmd, capture_output=True, text=True, cwd=cwd)
    wall = time.time() - t0
    ru1 = child_cpu()
    l1 = loadavg()
    if r.returncode != 0:
        raise RuntimeError("%s did not compile under %r:\n%s\n%s"
                           % (path, cmd, r.stdout[-2000:], r.stderr[-2000:]))
    ms = parse_type_checking(r.stdout + "\n" + r.stderr)
    if ms is None:
        raise RuntimeError("%s: the profiler produced no cumulative block at all "
                           "under %r. A missing reading is not a zero." % (path, cmd))
    return {"path": path, "threads": threads, "type_checking_ms": ms,
            "real_s": wall,
            "user_s": sub_cpu(ru0[0], ru1[0]),
            "sys_s": sub_cpu(ru0[1], ru1[1]),
            "load_before": l0, "load_after": l1, "idle_before": idle0}


PLANT_SRC = """\
-- QUEUE item 4c's positive control (D146 §2's shape).  The kernel reduces
-- `List.range N` and folds a predicate over it, so the reading is linear in the
-- DATA.  Unlike D146's two-module form this keeps the size in the source: the
-- control's question is only whether the reading still MOVES with the work, and
-- a reading that moves cannot be a frozen instrument.
-- ⛔ `maxRecDepth` is REQUIRED and its absence is not a small thing: without it
-- the elaborator aborts with "maximum recursion depth has been reached", the
-- profiler still prints a cumulative block with a `type checking` line of
-- 0.227ms, and a parse that only looked for that line would have recorded the
-- FAILURE as a tiny reading.  `profile()` refuses on a non-zero exit, which is
-- why this surfaced as an error instead of as a very quiet control.
set_option maxRecDepth 200000
def bigList : List Nat := List.range %d

theorem scan : bigList.all (fun n => n < 1000000) = true := by decide
"""


def plant_dir():
    """⛔ The plant lives outside the project but is COMPILED FROM IT: `lake env`
    resolves against the working directory, so the paths handed to `profile()`
    are absolute and the cwd stays `ROOT`. A control that runs in a different
    environment from the units is not a control for them."""
    d = scratch.mkdtemp(prefix="x86lean-threads-ab-")
    out = {}
    for n, tag in ((PLANT_SMALL, "small"), (PLANT_BIG, "big")):
        f = os.path.join(d, "Plant_%s.lean" % tag)
        open(f, "w").write(PLANT_SRC % n)
        out[tag] = f
    return d, out


def stats(xs):
    if not xs:
        return {}
    return {"n": len(xs), "median": statistics.median(xs),
            "mean": statistics.fmean(xs), "min": min(xs), "max": max(xs),
            "range": max(xs) - min(xs),
            "stdev": statistics.stdev(xs) if len(xs) > 1 else 0.0,
            "cv_pct": (statistics.stdev(xs) / statistics.fmean(xs) * 100
                       if len(xs) > 1 and statistics.fmean(xs) else 0.0)}


def run(rounds, units, out_path):
    plant, plant_files = plant_dir()
    readings = []
    print("QUEUE item 4c — %d rounds, arms {default, --threads 1}, alternated.\n"
          "units: %s\nplant: %s (N=%d, N=%d)\nload at start: %.2f\n"
          % (rounds, " ".join(units), plant, PLANT_SMALL, PLANT_BIG, loadavg()))
    for rd in range(rounds):
        arms = [None, 1] if rd % 2 == 0 else [1, None]
        for th in arms:
            label = "default" if th is None else "threads=%d" % th
            for u in units:
                r = profile(u, th)
                r.update(round=rd, arm=label, kind="unit")
                readings.append(r)
                print("  r%d %-11s %-24s %8.0f ms  real %6.2fs  user %6.2fs  "
                      "u/r %4.2f  load %5.1f  idle %s"
                      % (rd, label, u, r["type_checking_ms"], r["real_s"],
                         r["user_s"], r["user_s"] / max(r["real_s"], 1e-9),
                         r["load_before"],
                         "n/a" if r["idle_before"] is None
                         else "%5.1f%%" % r["idle_before"]))
                sys.stdout.flush()
            for tag in ("small", "big"):
                r = profile(plant_files[tag], th)
                r.update(round=rd, arm=label, kind="plant:" + tag)
                readings.append(r)
                print("  r%d %-11s %-24s %8.0f ms  real %6.2fs   [control]"
                      % (rd, label, "plant:" + tag, r["type_checking_ms"],
                         r["real_s"]))
                sys.stdout.flush()
    with open(out_path, "w") as f:
        for r in readings:
            f.write(json.dumps(r) + "\n")
    print("\nreadings written to %s" % out_path)
    return readings


# ⭐⭐ THREE QUANTITIES, NOT ONE, FROM THE SAME PASSES.  The gate reads the
# profiler's `type checking` — a SUM OF PER-TASK WALL-CLOCK readings.  The same
# invocation also yields the child's total `user` CPU time and its `real` wall
# time, at no extra cost, and `kernel_cost.py` profiles ONE MODULE PER `lean`
# PROCESS, so `user` is already a PER-UNIT quantity.  If it carries materially
# less variance than the gated number, that is a fifth route for item 4 that
# this run measures for free — and if it does not, that is worth knowing before
# anyone proposes it.  [[feedback-a-total-cannot-see-its-parts]]
FIELDS = [("type_checking_ms", "the GATED quantity (profiler `type checking`)"),
          ("user_s", "child CPU time (rusage `user`)"),
          ("real_s", "child wall time")]


def report(readings, fields=None):
    fields = fields or [f for f in FIELDS if any(f[0] in r for r in readings)]
    arms = ["default", "threads=1"]
    keys = []
    for r in readings:
        k = (r["kind"], r["path"])
        if k not in keys:
            keys.append(k)
    table = {}
    ok = True
    for field, blurb in fields:
        print("\n=== %s — %s" % (field, blurb))
        print("%-26s %-11s %5s %11s %11s %11s %7s" %
              ("unit", "arm", "n", "median", "range", "stdev", "CV%"))
        for kind, path in keys:
            for a in arms:
                xs = [r[field] for r in readings
                      if r["kind"] == kind and r["path"] == path
                      and r["arm"] == a and field in r]
                st = stats(xs)
                table[(field, kind, path, a)] = st
                if st:
                    print("%-26s %-11s %5d %11.3f %11.3f %11.3f %7.2f"
                          % (path if kind == "unit" else kind, a, st["n"],
                             st["median"], st["range"], st["stdev"], st["cv_pct"]))
        print("%-26s %12s %12s %10s" % ("  ratio B/A:", "median", "CV", "verdict"))
        for kind, path in keys:
            a = table.get((field, kind, path, "default"))
            b = table.get((field, kind, path, "threads=1"))
            if not a or not b or not a["median"] or not a["cv_pct"]:
                continue
            mr, cr = b["median"] / a["median"], b["cv_pct"] / a["cv_pct"]
            print("%-26s %12.3f %12.3f %10s"
                  % (path if kind == "unit" else kind, mr, cr,
                     "quieter" if cr < 1 else "noisier"))
    # ⭐⭐ THE PAIRED VIEW, AND WHY IT IS THE ONE TO READ ON A SHARED BOX.
    # Arm medians compare two SETS of readings and therefore compare the hours
    # they were taken in as much as the flag. The box this runs on held 0.0-0.1%
    # idle all evening on other seats' builds (D149), so slow drift is the
    # dominant term. Two estimators that survive it:
    #   * the per-ROUND ratio B/A, which cancels anything common to the pair;
    #   * the median |difference between CONSECUTIVE rounds| within one arm, a
    #     dispersion estimate that ignores a slow trend the way a plain stdev
    #     cannot. [[feedback-a-single-reading-is-about-its-run]]
    print("\n=== PAIRED BY ROUND (drift-robust): B/A per round, and each arm's")
    print("    median |consecutive-round difference| as %% of its own median")
    print("%-26s %-22s %11s %11s %11s" %
          ("unit", "field", "median B/A", "step%% A", "step%% B"))
    for field, _blurb in fields:
        for kind, path in keys:
            byround = {}
            for r in readings:
                if (r["kind"] == kind and r["path"] == path and field in r
                        and "round" in r):
                    byround.setdefault(r["round"], {})[r["arm"]] = r[field]
            rounds = sorted(byround)
            ratios = [byround[i]["threads=1"] / byround[i]["default"]
                      for i in rounds
                      if "default" in byround[i] and "threads=1" in byround[i]
                      and byround[i]["default"]]
            def step(arm):
                xs = [byround[i][arm] for i in rounds if arm in byround[i]]
                if len(xs) < 2:
                    return None
                d = [abs(b - a) for a, b in zip(xs, xs[1:])]
                m = statistics.median(xs)
                return (statistics.median(d) / m * 100) if m else None
            sa, sb = step("default"), step("threads=1")
            if not ratios and sa is None and sb is None:
                continue
            print("%-26s %-22s %11s %11s %11s"
                  % (path if kind == "unit" else kind, field,
                     "%.3f" % statistics.median(ratios) if ratios else "n/a",
                     "%.2f" % sa if sa is not None else "n/a",
                     "%.2f" % sb if sb is not None else "n/a"))
            if ratios and len(ratios) > 1:
                print("%-26s %-22s   ratios: %s"
                      % ("", "", " ".join("%.3f" % x for x in ratios)))

    # ⛔ THE CONTROL, SCORED PER ARM ON THE GATED QUANTITY — a quiet arm that
    # stopped responding to the work is not a win, and its CV column would look
    # exactly like one.
    print("")
    # ⛔ THE CONTROL IS LOOKED UP BY KIND, NOT BY PATH. The plant lives in a
    # temporary directory whose name changes every run, so a path-keyed lookup
    # would miss silently and print "CONTROL INCOMPLETE" for a control that ran.
    # A lookup that cannot find its subject must not be able to look like one
    # that found nothing to say. [[feedback-a-positional-index-bets-the-record-wont-grow]]
    # ⛔⛔ THE CONTROL SCORES EVERY FIELD, NOT ONLY THE GATED ONE. This run's
    # whole result is that a DIFFERENT field (`user_s`) is far quieter than the
    # gated one — and "quieter" is what a field that stopped responding also
    # looks like. A control that covers only the incumbent quantity leaves the
    # candidate uncontrolled, which is exactly the position the incumbent was in
    # before anyone measured it. [[feedback-a-probe-must-create-its-condition]]
    kindpath = {k: pth for k, pth in keys}
    for field, _blurb in fields:
        for a in arms:
            sm = table.get((field, "plant:small", kindpath.get("plant:small"), a))
            bg = table.get((field, "plant:big", kindpath.get("plant:big"), a))
            if not sm or not bg or not sm["median"]:
                print("  \u26a0 CONTROL INCOMPLETE for %s / arm %s — no verdict "
                      "is available" % (field, a))
                ok = False
                continue
            ratio = bg["median"] / sm["median"]
            if ratio < PLANT_MIN_RATIO:
                print("  \u2716 CONTROL FAILED for %s / arm %s: the %dx plant "
                      "reads only %.2fx bigger — this field is not tracking the "
                      "work, so its variance says nothing"
                      % (field, a, PLANT_BIG // PLANT_SMALL, ratio))
                ok = False
            else:
                print("  \u2714 control %-18s %-11s the %dx plant reads %.2fx "
                      "bigger (>= %.1f)"
                      % (field, a, PLANT_BIG // PLANT_SMALL, ratio,
                         PLANT_MIN_RATIO))
    loads = [r["load_before"] for r in readings if "load_before" in r]
    idles = [r["idle_before"] for r in readings if r.get("idle_before") is not None]
    if loads:
        print("\nCONDITIONS: 1-minute load over the run %.1f - %.1f (median %.1f), "
              "%d readings" % (min(loads), max(loads), statistics.median(loads),
                               len(readings)))
    if idles:
        print("            CPU idle %% %.1f - %.1f (median %.1f) over %d of %d "
              "readings" % (min(idles), max(idles), statistics.median(idles),
                            len(idles), len(readings)))
    elif loads:
        print("            \u26a0 idle %% could not be read on ANY reading — the "
              "conditions are load-only, which D149 says is not enough")
    return ok


def selftest():
    ok = True

    def arm(name, cond):
        nonlocal ok
        print(("  \u2714 " if cond else "  \u2716 ") + name)
        ok = ok and cond

    arm("a `type checking` in ms is read",
        parse_type_checking("  type checking 1234.5ms\n") == 1234.5)
    arm("a `type checking` in SECONDS is scaled to ms",
        parse_type_checking("  type checking 26.2s\n") == 26200.0)
    arm("a cumulative block with no `type checking` is a real zero",
        parse_type_checking("cumulative profiling times:\n  elaboration 1s\n") == 0.0)
    arm("NO cumulative block at all is a FAILED READING, not a zero",
        parse_type_checking("some unrelated output\n") is None)
    # ⭐ the control's own red arm: a FROZEN instrument must be caught.  Without
    # this, `report`'s control could print a tick for an arm that reads the same
    # number at both plant sizes.  [[feedback-a-probe-must-create-its-condition]]
    # ⭐ the control's own red arms.  Without these, `report`'s control could
    # print a tick for an arm that reads the same number at both plant sizes.
    # The fixtures carry BOTH arms, because "no control for this arm" is itself
    # a refusal and would otherwise be the thing under test.
    # [[feedback-a-probe-must-create-its-condition]]
    def fixture(small, big):
        out = []
        for a in ("default", "threads=1"):
            for tag, path, v in (("plant:small", "Plant_small.lean", small),
                                 ("plant:big", "Plant_big.lean", big)):
                for i in range(2):
                    out.append({"kind": tag, "path": path, "arm": a,
                                "type_checking_ms": v + i, "load_before": 1.0})
        return out

    arm("the control CATCHES an arm whose plant reading does not move",
        report(fixture(80.0, 80.0)) is False)
    arm("and PASSES the same shape when the plant reading does move",
        report(fixture(80.0, 460.0)) is True)
    # ⭐ and an arm with NO control at all must refuse rather than pass in
    # silence: an unmeasured arm's variance is not evidence about the flag.
    arm("an arm with no control reading REFUSES",
        report([r for r in fixture(80.0, 460.0) if r["arm"] == "default"]) is False)
    # ⭐ the plant source must actually differ in its data size, or the control
    # is two names for one measurement. [[feedback-two-arms-that-agree-to-the-case]]
    # ⭐ the PAIRED view is the one a busy box makes readable, so it carries its
    # own arm: a drifting pair whose per-round RATIO is constant must report that
    # ratio, not the ratio of the two arms' medians.
    drift = []
    for i, base in enumerate((100.0, 200.0, 400.0, 800.0)):
        for a, mult in (("default", 1.0), ("threads=1", 0.5)):
            drift.append({"kind": "unit", "path": "U.lean", "arm": a, "round": i,
                          "type_checking_ms": base * mult, "load_before": 1.0})
    import io, contextlib
    buf = io.StringIO()
    with contextlib.redirect_stdout(buf):
        report(drift + fixture(80.0, 460.0))
    arm("the paired view reports the per-round ratio through an 8x drift",
        "0.500" in buf.getvalue())

    arm("the two plant sources differ",
        (PLANT_SRC % PLANT_SMALL) != (PLANT_SRC % PLANT_BIG))
    print("\n%s threads_ab selftest" % ("\u2705" if ok else "\u274c"))
    return 0 if ok else 1


# ⭐ A MEASUREMENT THAT COST TWENTY MINUTES MUST BE RE-JUDGEABLE IN SECONDS.
# D146 §8 is the seat's own scar: a delta run that omitted `--out` could not be
# re-judged against a changed rule and had to be re-measured on a different
# afternoon, on a different box state. Every reading here is written to JSONL and
# `--analyse` re-runs the whole report over it with no `lean` invoked.
# [[feedback-a-gate-that-refuses-must-say-what-it-saw]]
def main():
    if "--selftest" in sys.argv:
        return selftest()
    if "--analyse" in sys.argv:
        path = arg("--analyse")
        rs = [json.loads(l) for l in open(path) if l.strip().startswith("{")]
        if not rs:
            print("⛔ %s holds no readings." % path)
            return 2
        print("re-judging %d saved readings from %s (no measurement taken)"
              % (len(rs), path))
        return 0 if report(rs) else 1
    rounds = int(arg("--rounds", "5"))
    units = arg("--units", " ".join(UNITS)).split()
    out = arg("--out", os.path.join(ROOT, "docs",
                                    "threads-ab-%s.jsonl" % time.strftime("%Y-%m-%d")))
    readings = run(rounds, units, out)
    return 0 if report(readings) else 1


if __name__ == "__main__":
    sys.exit(main())
