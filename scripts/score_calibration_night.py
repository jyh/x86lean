"""Score the third calibration night against the SEALED gate, in the sealed order:
   (1) the usability gate on a covariate — judged FIRST, before the band exists;
   (2) only then the calibration band.
Refuses to print the band if the gate fails, because seeing it is the selection
D179 forbids."""
import json, collections, statistics as st, subprocess, sys, os
os.chdir("/Users/jyh/projects/claude/x86lean")

# ⭐⭐ `--early PATH` — THE CHEAP FORM OF THIS GATE, EVALUABLE WHILE THE RUN IS IN
# FLIGHT.  The third night's seal said the remedy in its own post-mortem: "a gate
# that can only fire after the experiment has finished is a VERDICT, not a gate …
# declare TWO forms of every usability condition, a cheap one evaluable early on a
# covariate and the full one at the end."
#
# ⭐ AND THE POINT THAT MAKES THIS SOUND RATHER THAN A SECOND, LOOSER TEST: the
# AMENDED statistic is a MAX, and a max is MONOTONE in the readings seen so far.
# Once any completed commit-pair exceeds the bound, no later reading can bring the
# final max back under it.  So the early form is not a new test with its own error
# rate — it is the SAME test, evaluated as soon as it is decidable, and asking it
# after every commit adds no multiplicity whatever
# ([[feedback-a-per-unit-threshold-asked-n-times]] does not bite here, and the
# reason it does not is worth stating rather than assuming).
# ⛔⛔ UNDER THE ORIGINALLY SEALED STATISTIC — the MEDIAN — THIS WOULD BE FALSE. A
# running median can fall as data arrives, so an early median gate WOULD be a
# different test carrying real multiplicity.  ⇒ 🔑 THE AMENDMENT THAT FIXED THE
# GATE ALSO MADE IT EARLY-STOPPABLE, AND NOTHING NOTICED AT THE TIME.
# ⛔ THE FORM IS ONE-SIDED AND SAYS SO: it can return a definite FAIL and never a
# definite PASS. "NOT YET FAILED" is the only other answer it is entitled to.
WALK = sys.argv[-1]
EARLY = "--early" in sys.argv
# ⛔⛔ AMENDED 2026-09-09, BEFORE THE SUBJECT'S DATA EXISTED (walk at 2 of 24) AND
# ON A CONTROL RUN AGAINST OTHER NIGHTS — NOT on anything the third night produced.
# THE SEALED GATE WAS "MEDIAN per-commit p95 <= 14.2%" AND IT COULD NOT FAIL THE
# NIGHT IT WAS BUILT TO EXCLUDE: the loaded night's MEDIAN is 8.7%, BELOW the quiet
# night's own 12.0%, so it PASSED. Its MAX is 50.6% against the quiet night's 14.2%.
# ⇒ 🔑 I BUILT A TAIL-GATE OUT OF A MEDIAN — the fourth instance today of the same
#   shape, and the first one caught BEFORE the data landed, by controlling the gate
#   against a night whose answer was already known.
# ⇒ THE STATISTIC IS NOW THE MAX, which is what discriminates: quiet 14.2%,
#   loaded 50.6%, a factor of 3.6.
# ⚠️ NO MARGIN IS INVENTED. The bound is the quiet night's own maximum, so the quiet
#   night passes only by EQUALITY and the gate is knife-edge strict. That is
#   deliberate: inventing a 1.2x allowance would derive the gate from the thing it
#   checks ([[feedback-widening-a-gate-needs-a-second-source]]), and a FAIL here
#   means "this night is UNUSABLE", never "the counter is refuted" — so strictness
#   is conservative in the safe direction.
# ⛔⛔ AND THE BOUND IS DERIVED FROM THE QUIET NIGHT'S FILE AT RUN TIME, NOT TYPED.
#   Typed as the rounded literal `0.142` it FAILED THE QUIET NIGHT ITSELF — whose
#   true max is fractionally above 0.142 and only prints as "14.2%". A gate stated
#   to 3 significant figures cannot express "<= this night's own maximum", and the
#   night that DEFINED the bound was the first thing it rejected.
#   ⇒ 🔑 A ROUNDED LITERAL IS A DIFFERENT THRESHOLD FROM THE QUANTITY IT WAS ROUNDED
#     FROM, and at a knife-edge bound that difference is the whole gate. Caught by
#     the control that required the quiet night to PASS — an arm that existed only
#     because a gate must be probed for silence as well as for noise.
QUIET = "docs/kernel-delta-history-2026-09-04.jsonl"
STAT = "max"

def per_commit_p95(path):
    rows = [json.loads(l) for l in open(path)]
    by = collections.defaultdict(list)
    for r in rows: by[r["commit"]].append(r)
    out, loads = {}, []
    for c, v in by.items():
        if len(v) < 2: continue
        a, b = v[0], v[1]; rel = []
        for m, dd in a["decls"].items():
            for d, x in dd.items():
                y = b["decls"].get(m, {}).get(d)
                if y is None: continue
                mn = (x + y) / 2
                if mn > 0: rel.append(abs(x - y) / mn)
        if len(rel) >= 10:
            rel.sort(); out[c[:8]] = rel[int(.95 * (len(rel) - 1))]
        loads += [r["load1"] for r in v]
    return out, loads

def selftest(gate):
    """Arms for the EARLY form. No box, no build: the committed corpora only."""
    sys.path.insert(0, os.path.join(os.getcwd(), "scripts"))
    import kernel_delta_history as kdh
    bad = []

    def ok(cond, what, plant=None):
        print(f"   {'ok  ' if cond else '⛔ FAIL'} [{'RED ' if plant else 'CTRL'}] {what}")
        if not cond:
            bad.append(what)

    NIGHT3 = "docs/kernel-delta-history-DISCARDED-night3-2026-09-09.jsonl"
    n3, _ = per_commit_p95(NIGHT3)
    ok(max(n3.values()) > gate,
       "CONTROL — night 3 exceeds the bound at all; without that every arm below "
       "would pass by being unreachable [[feedback-a-plant-probes-control-comes-first]]")
    ok(max(qp95.values()) <= gate,
       "CONTROL — the QUIET night, which DEFINES the bound, does not exceed it. A "
       "gate must be probed for silence as well as noise "
       "[[feedback-probe-gates-both-ways]]")

    # monotonicity — the property that makes an early abort sound
    vals = list(n3.values())
    prefixes_ok = all(max(vals[:k]) <= max(vals) for k in range(1, len(vals) + 1))
    ok(prefixes_ok,
       "the running MAX over any prefix is <= the final MAX, so an early FAIL can "
       "never be a false one. This is the whole licence for aborting early",
       plant="max-monotone")
    med_can_fall = any(st.median(vals[:k]) > st.median(vals)
                       for k in range(1, len(vals) + 1))
    ok(med_can_fall,
       "RED-FIRST — a running MEDIAN over this same night DOES fall as data "
       "arrives, so the ORIGINALLY SEALED statistic would NOT have licensed an "
       "early abort. The amendment is what made the gate early-stoppable",
       plant="median-not-monotone")

    k_il, c_il, tot = first_fail(NIGHT3, gate, lambda C: kdh.visit_order(C, 2, True))
    k_sw, c_sw, _ = first_fail(NIGHT3, gate, lambda C: kdh.visit_order(C, 2, False))
    ok(k_il is not None and k_sw is not None and k_il < k_sw,
       f"ON THE REAL NIGHT-3 READINGS: the gate could first fire at reading {k_il} "
       f"of {tot} interleaved ({c_il}) against reading {k_sw} ({c_sw}) under the "
       f"default order. Same readings, different arrival order",
       plant="order-buys-earliness")
    ok(k_sw > tot // 2,
       "CONTROL — under the default order the first possible fire is past the "
       "HALFWAY point of the run, which is the cost the interleave removes")
    print("SELFTEST " + ("⛔ FAILED" if bad else "ok"))
    return 1 if bad else 0


def first_fail(path, gate, order):
    """(reading index, commit) at which `order` first completes a pair over `gate`.

    The readings are FIXED; only the order in which they arrive changes.  This is
    what the walk order buys, computed rather than asserted."""
    p95, _l = per_commit_p95(path)
    rows = sorted([json.loads(l) for l in open(path)], key=lambda r: r["t"])
    commits = [r["commit"] for r in rows if r["sweep"] == 0]
    seen = collections.Counter()
    for k, (_s, c) in enumerate(order(commits), 1):
        seen[c] += 1
        if seen[c] == 2 and p95.get(c[:8], 0) > gate:
            return k, c[:8], len(rows)
    return None, None, len(rows)


qp95, _ql = per_commit_p95(QUIET)
GATE = max(qp95.values())          # the quiet night's OWN maximum, at full precision

if "--selftest" in sys.argv:
    sys.exit(selftest(GATE))

p95, loads = per_commit_p95(WALK)
if EARLY:
    if not p95:
        print("⛔ no commit has a completed pair yet — the early gate has NOTHING to "
              "read. That is not a pass.")
        sys.exit(2)
    worst_c = max(p95, key=p95.get)
    worst = p95[worst_c]
    print("EARLY USABILITY GATE — %d commit-pair(s) complete so far, load1 median %.2f"
          % (len(p95), st.median(loads)))
    print("  running MAX per-commit p95: %.2f%%  (worst so far: %s)  bound %.4f%%"
          % (100 * worst, worst_c, 100 * GATE))
    if worst > GATE:
        print("  ⛔ FAILED, AND THE FAIL IS FINAL: the statistic is a MAX, so no later")
        print("     reading can bring it back under the bound. ABORT IS SOUND HERE.")
        sys.exit(1)
    print("  ~ NOT YET FAILED. ⛔ THIS IS NOT A PASS — the form is ONE-SIDED and only")
    print("    the full gate over every commit can pass a night.")
    sys.exit(0)

if len(p95) < 12:
    print("⛔ only %d commits have paired sweeps — the walk is INCOMPLETE. Not scored." % len(p95))
    sys.exit(2)
worst = max(p95.values())   # the MAX, per the amendment above
print("THIRD NIGHT — %d commit-pairs, load1 %.2f-%.2f (median %.2f)"
      % (len(p95), min(loads), max(loads), st.median(loads)))
print("  per-commit p95 spread: min %.1f%%  median %.1f%%  MAX %.1f%%"
      % (100 * min(p95.values()), 100 * st.median(list(p95.values())), 100 * worst))
print()
print("⚖️ THE USABILITY GATE (amended pre-data) — MAX per-commit p95 <= %.4f%% "
      "(the quiet night's own maximum, DERIVED not typed)" % (100 * GATE))
if worst > GATE:
    print("  ⛔ FAILED (%.1f%% > %.1f%%). THE NIGHT IS UNUSABLE and is discarded ON THE COVARIATE."
          % (100 * worst, 100 * GATE))
    print("  ⛔ THE CALIBRATION BAND IS NOT COMPUTED AND NOT LOOKED AT. Seeing it now is exactly")
    print("     the selection-on-outcome D179 rule 3 forbids, and the gate was sealed to prevent it.")
    sys.exit(1)
print("  ✅ PASSED (%.1f%% <= %.1f%%). The night is usable; scoring the band."
      % (100 * worst, 100 * GATE))
print()
r = subprocess.run([sys.executable, "scripts/unfolding_calibration.py",
                    "--counters", "docs/deterministic-cost-history-2026-09-05.jsonl",
                    "--walk", WALK], capture_output=True, text=True)
for line in r.stdout.splitlines():
    if any(k in line for k in ("UNSELECTED", "no k reaches", "k  cases", "⚠️")) or line.strip()[:1].isdigit():
        print("  " + line.strip())
print()
print("SEALED P2: the k>=8 unselected band lands INSIDE or OVERLAPPING 2.39-4.12 (median 3.38).")
print("SEALED P3: a PASS buys a SECOND USABLE NIGHT ON ONE MACHINE. 4b's machine-independence")
print("           half is UNTOUCHED and this is not '4b unblocked'.")
