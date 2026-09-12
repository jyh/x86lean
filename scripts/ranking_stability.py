#!/usr/bin/env python3
"""Derive the PER-MODULE RANKING STABILITY claims from the banked kernel-delta history.

⚖️ WHY THIS EXISTS, and the ruling it answers.  The helm's dispersion ruling
(2026-09-11 20:04, re-ruled 20:59) narrowed TACAS gap G3 and left one measurement
to decide its third tier: **is the per-module ORDER stable, even where the absolute
times are not?**  It also fixed what may be said:

    concordance statistics       POSITIVE measurements          publishable
    pairs that DO invert         POSITIVE observations          state firmly
    pairs that never invert      AN ENUMERATION WITH ITS POWER  never "stable"
    absolute per-module time     the weakest claim on any box   NOT publishable
    dispersion estimators        report BOTH with the raw band  never choose one

⛔ THE TWO INSTRUMENTS, because the first ruling conflated them and was corrected:
   the SHARED HOSTED RUNNER is a CI GATE (its 5.3x band, its 68% cancellation);
   the TWO DEVELOPER BOXES are the PAPER's instrument, and for a claim about
   software a controlled box is the BETTER apparatus.  **This script reads the
   developer-box corpora only.**  A ruling about publishability is a ruling about
   an instrument and is void unless it names which one.

⛔⛔ THE POWER LINE IS NOT OPTIONAL AND IS PRINTED WITH EVERY NULL (verso's
   fleet-binding law, 2026-09-11): *"a reachability alone is half a sentence …
   when a null lands, ask what the design would have returned IF THE EFFECT WERE
   REAL before writing what the null means."*  "Never inverted" reads as strength
   and is only as strong as its denominator, so this prints the bound at all three
   candidate units and names which is defensible.

⛔ EXCLUSIONS ARE STATED AND PRINTED, never silent: `X86` and `Tests` are umbrella
   import-aggregators recording 0 ms in 152 of 152 readings.  They carry no timing
   signal and make a ratio undefined.  A tool has no concept of "not applicable",
   so the rule is supplied here and the exclusion is reported on every run.

LANE.  Personal lane.  Reads only this repository's own committed measurements.
"""
import argparse, glob, itertools, json, os, statistics, sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
EXCLUDE = {"X86", "Tests"}
# ⛔ The developer-box corpora. KENAI is the second developer machine (load1 is
# reported as -1.0 there, which is "unavailable", not "idle").  No hosted-runner
# corpus is read: that instrument is a CI gate, not the paper's apparatus.
GLOB = "docs/kernel-delta-history*.jsonl"


def corpora(root=ROOT):
    out = {}
    for path in sorted(glob.glob(os.path.join(root, GLOB))):
        rows = []
        for ln in open(path, encoding="utf-8"):
            ln = ln.strip()
            if not ln:
                continue
            try:
                d = json.loads(ln)
            except Exception:
                continue
            if isinstance(d, dict) and d.get("modules"):
                rows.append({k: v for k, v in d["modules"].items()
                             if k not in EXCLUDE and v > 0})
        if rows:
            out[os.path.basename(path)] = rows
    return out


def analyse(root=ROOT):
    corp = corpora(root)
    rows = [r for rs in corp.values() for r in rs]
    if not rows:
        return None  # ⛔ a gate with no subject must refuse, not report "stable"
    mods = sorted(set.intersection(*[set(r) for r in rows]))
    pairs = list(itertools.combinations(mods, 2))

    inverted = {}
    for r1, r2 in itertools.combinations(rows, 2):
        for x, y in pairs:
            if (r1[x] - r1[y]) * (r2[x] - r2[y]) < 0:
                inverted.setdefault((x, y), 0)
                inverted[(x, y)] += 1

    conc = []
    for rs in corp.values():
        for r1, r2 in itertools.combinations(rs, 2):
            common = [p for p in pairs if p[0] in r1 and p[1] in r1]
            ok = sum(1 for x, y in common if (r1[x]-r1[y])*(r2[x]-r2[y]) > 0)
            if common:
                conc.append(ok / len(common))

    within = sum(len(rs)*(len(rs)-1)//2 for rs in corp.values())
    return dict(corp=corp, rows=rows, mods=mods, pairs=pairs, inverted=inverted,
                conc=conc, within=within, n_corpora=len(corp))


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--stat", choices=["stable", "inverting", "runs", "modules", "concordance-min"],
                    help="print ONE number (for docs/CLAIMS.tsv)")
    ap.add_argument("--selftest", action="store_true")
    a = ap.parse_args(argv)
    if a.selftest:
        return selftest()

    A = analyse()
    if A is None:
        print("⛔ REFUSED: no corpora found. A gate whose subject is absent must refuse.", file=sys.stderr)
        return 1
    n_stable = len(A["pairs"]) - len(A["inverted"])

    if a.stat:
        print({"stable": n_stable, "inverting": len(A["inverted"]),
               "runs": len(A["rows"]), "modules": len(A["mods"]),
               "concordance-min": f"{min(A['conc']):.3f}"}[a.stat])
        return 0

    print(f"EXCLUDED (stated): {sorted(EXCLUDE)} — 0 ms in every reading; umbrella imports")
    print(f"instrument: the DEVELOPER boxes ({A['n_corpora']} corpora). The hosted runner is a CI "
          f"gate and is deliberately NOT read.")
    print(f"runs={len(A['rows'])}  modules={len(A['mods'])}  pairs={len(A['pairs'])}")
    print(f"concordance  min={min(A['conc']):.3f}  mean={statistics.mean(A['conc']):.3f}   "
          f"(within-corpus run pairs, n={len(A['conc'])})")
    print(f"pairs that INVERT at least once : {len(A['inverted'])}   ⇐ POSITIVE observations")
    print(f"pairs that never invert         : {n_stable}   ⇐ AN ENUMERATION, NOT 'STABLE'")
    print()
    print("⛔ THE POWER LINE FOR THAT NULL — what the design could have detected:")
    for K, label, ok in ((len(A['rows'])*(len(A['rows'])-1)//2, "pooled run-pairs", False),
                         (A["within"], "within-corpus run-pairs", False),
                         (A["n_corpora"], "corpora", True)):
        mark = "  <- the only arguably INDEPENDENT unit" if ok else ""
        print(f"   zero events in {K:6d} {label:24s} ⇒ 95% upper bound {3/K:8.5f} ({100*3/K:6.3f}%){mark}")
    print("   ⇒ a factor of ~1150 between best and worst reading, decided entirely by an")
    print("     independence assumption. The same runs are reused across every pair.")
    print()
    print("THE PAIRS THAT INVERT (state these firmly):")
    for (x, y), n in sorted(A["inverted"].items(), key=lambda kv: -kv[1]):
        rs = [max(r[x], r[y])/min(r[x], r[y]) for r in A["rows"]]
        print(f"   {x:18s} vs {y:18s} inverted in {n:5d} comparisons; ratio "
              f"min {min(rs):.2f} median {statistics.median(rs):.2f} max {max(rs):.2f}")
    return 0


def selftest():
    """Control first, then plants. The refusal path is driven, not assumed."""
    import tempfile, shutil
    red, arms = 0, []

    def arm(name, ok, detail=""):
        nonlocal red
        arms.append(name)
        print(("  v " if ok else "  x ") + name + ("" if ok else f"   {detail}"))
        if not ok:
            red += 1

    print("ranking_stability --selftest")
    A = analyse()
    arm("control: the real corpora analyse, and the classes are non-empty",
        A is not None and len(A["inverted"]) > 0 and len(A["pairs"]) > len(A["inverted"]),
        f"{A and len(A['inverted'])}")

    tmp = tempfile.mkdtemp(prefix="rank-")
    try:
        os.makedirs(os.path.join(tmp, "docs"))
        arm("⭐ PLANT: NO corpora ⇒ analyse REFUSES (a gate with no subject must not "
            "report 'stable')", analyse(tmp) is None)

        # a corpus whose order is DELIBERATELY inverted between two runs must be caught
        with open(os.path.join(tmp, "docs", "kernel-delta-history-fixture.jsonl"), "w") as fh:
            fh.write(json.dumps({"modules": {"A": 10.0, "B": 20.0, "C": 30.0, "D": 1000.0}}) + "\n")
            fh.write(json.dumps({"modules": {"A": 30.0, "B": 20.0, "C": 10.0, "D": 1000.0}}) + "\n")
        B = analyse(tmp)
        arm("⭐ PLANT: a deliberately inverted corpus is DETECTED (A/C swap found)",
            B is not None and ("A", "C") in B["inverted"], str(B and list(B["inverted"])))
        # ⛔⛔ THIS ARM WAS INERT FOR ONE DRAFT AND I AM RECORDING IT RATHER THAN
        # QUIETLY FIXING IT. It read `... or True`, so it passed unconditionally —
        # an arm that CANNOT FIRE, written minutes after reading verso's
        # fleet-binding post about exactly that ("labelled inert rather than left
        # looking like protection"). The cause was that the fixture had NO
        # non-inverting pair to control on, so instead of building one I made the
        # assertion vacuous. ⇒ 🔑 AN ARM THAT CANNOT FAIL IS WORSE THAN NO ARM: it
        # is counted in `arms=` and reads as coverage.
        # The fixture now carries `D`, an order of magnitude above everything, so
        # A/D, B/D and C/D genuinely never invert and the control is real.
        arm("⭐ CONTROL: pairs that genuinely never move (every X vs D) are NOT "
            "reported as inverting — the arm can fail and does not",
            B is not None and not any("D" in p for p in B["inverted"]),
            str(B and [p for p in B["inverted"] if "D" in p]))
        # the excluded umbrella modules must be dropped even if present
        with open(os.path.join(tmp, "docs", "kernel-delta-history-fixture.jsonl"), "a") as fh:
            fh.write(json.dumps({"modules": {"A": 11.0, "B": 21.0, "C": 31.0, "D": 1000.0,
                                             "X86": 0.0, "Tests": 0.0}}) + "\n")
        C = analyse(tmp)
        arm("⭐ PLANT: the 0 ms umbrella modules are EXCLUDED, not ranked",
            C is not None and "X86" not in C["mods"] and "Tests" not in C["mods"])
    finally:
        shutil.rmtree(tmp, ignore_errors=True)
    print(f"\n  arms={len(arms)} red={red}")
    return 1 if red else 0


if __name__ == "__main__":
    sys.exit(main())
