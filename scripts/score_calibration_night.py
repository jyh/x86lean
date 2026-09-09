"""Score the third calibration night against the SEALED gate, in the sealed order:
   (1) the usability gate on a covariate — judged FIRST, before the band exists;
   (2) only then the calibration band.
Refuses to print the band if the gate fails, because seeing it is the selection
D179 forbids."""
import json, collections, statistics as st, subprocess, sys, os
os.chdir("/Users/jyh/projects/claude/x86lean")
WALK = sys.argv[1]
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

qp95, _ql = per_commit_p95(QUIET)
GATE = max(qp95.values())          # the quiet night's OWN maximum, at full precision
p95, loads = per_commit_p95(WALK)
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
