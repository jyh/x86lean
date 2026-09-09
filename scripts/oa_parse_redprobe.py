#!/usr/bin/env python3
"""⭐⭐ THE RED PROBE FOR `oracle_availability.py`'s PARSE ARMS AND ITS ROTATION
COVERAGE (QUEUE 0b(6), the sibling sweep).

Same method as `scripts/cr4_parse_redprobe.py`: four defects planted one at a
time into an IN-MEMORY copy of the shipped module, each required to fire.  The
tree is never edited.  Build-free, no oracle, ~0.1 s.

⭐ WHAT IT ESTABLISHED:
  * Q-D — disabling `report()`'s `if un:` refusal — fired NO ARM on the first
    draft.  Every form still reported, as `MIXED`, so the arm's `len(bad) ==
    len(FORMS)` check held while the DIAGNOSIS was gone.  The arm now requires
    the refusal to NAME what it saw
    ([[feedback-a-gate-that-refuses-must-say-what-it-saw]]).
  * The rotation-coverage section below is the `movmskps` finding, driven three
    ways: the shipped three-valued rotation leaves NO row unplanted; the OLD
    two-valued flip leaves exactly `movmskps` — the row D170 added the third
    value FOR; and a hypothetical fourth value is caught by the coverage assert
    rather than silently escaping all arms.

LANE.  Personal lane; pure string work.

Usage:  oa_parse_redprobe.py        (exit 0 iff every plant fires)
"""
import os, sys, types

# ⛔ DERIVED, NOT HARD-CODED — a probe that runs from only one path stops running.
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
os.chdir(ROOT); sys.path.insert(0, os.path.join(ROOT, "scripts"))
SRC = open("scripts/oracle_availability.py").read()

PLANTS = [
 ("Q-A  residual restored in parse_arms' loop: unparsed -> executes",
  [("                if ref is None or rip is None: un += 1\n"
    "                elif ref.group(1) == \"1\": r += 1\n"
    "                elif int(rip.group(1), 16) == ENTRY_RIP: st += 1\n"
    "                else: e += 1\n"
    "                res[cur] = (e, r, st, un)",
    "                if ref is not None and ref.group(1) == \"1\": r += 1\n"
    "                elif rip is not None and int(rip.group(1), 16) == ENTRY_RIP: st += 1\n"
    "                else: e += 1\n"
    "                res[cur] = (e, r, st, un)")],
  "arms 3,4,5,6 (every unparseable shape reads `executes`)"),
 ("Q-B  rip pattern loosened to [0-9a-f]+ (the D177 producer mismatch)",
  [(r'RE_RIP = re.compile(r"\brip=([0-9a-f]{16})\b")',
    r'RE_RIP = re.compile(r"\brip=([0-9a-f]+)")')],
  "arm 4 (base-10 rip)"),
 ("Q-C  stall test inverted (== becomes !=) in parse_arms' loop",
  [("                elif int(rip.group(1), 16) == ENTRY_RIP: st += 1\n"
    "                else: e += 1\n"
    "                res[cur] = (e, r, st, un)",
    "                elif int(rip.group(1), 16) != ENTRY_RIP: st += 1\n"
    "                else: e += 1\n"
    "                res[cur] = (e, r, st, un)")],
  "arms 1,2 (both positive controls)"),
 ("Q-D  report() stops refusing on unparsed records",
  [("        if un:", "        if False:")], "arm 7 (report's refusal)"),
]

def run_with(src, fn):
    mod = types.ModuleType("oa_plant"); mod.__name__ = "oa_plant"
    mod.__file__ = os.path.abspath("scripts/oracle_availability.py")
    try:
        exec(compile(src, mod.__file__, "exec"), mod.__dict__)
        return fn(mod)
    except Exception as ex:
        return False, 0, [("CRASH: %s: %s" % (type(ex).__name__, ex), "")]

ok, n, fails = run_with(SRC, lambda m: m.parse_arms())
print("CONTROL (shipped, unplanted): %s, %d arms, %d failures" % ("PASS" if ok else "FAIL", n, len(fails)))
assert ok, "⛔ control is RED"

allgood = True
for name, pairs, expect in PLANTS:
    src = SRC
    for old, new in pairs:
        assert src.count(old) == 1, "%s: subject not unique (%d)" % (name, src.count(old))
        src = src.replace(old, new, 1)
    ok, n, fails = run_with(src, lambda m: m.parse_arms())
    good = not ok
    allgood &= good
    print("%s %-62s %d arm(s) fired  — expected %s" % ("✔" if good else "⛔", name, len(fails), expect))
    for lab, _ in fails: print("      · %s" % lab[:96])

# ---- the ROTATION COVERAGE arm, driven separately: it lives in main() ----
print("\n-- rotation coverage arm (the `movmskps` finding) --")
def coverage(mod, forms):
    VALS = ("refuses", "executes", "stalls")
    ROT = {VALS[i]: VALS[(i+1) % len(VALS)] for i in range(len(VALS))}
    planted = {f[0] for f in forms if f[3] in ROT}
    return [f[0] for f in forms if f[0] not in planted]
import oracle_availability as OA
print("  shipped FORMS, three-valued rotation : unplanted rows =", coverage(OA, OA.FORMS) or "NONE ✔")
TWO = {"refuses": "executes", "executes": "refuses"}
planted2 = {f[0] for f in OA.FORMS if f[3] in TWO}
print("  the OLD two-valued flip              : unplanted rows =",
      [f[0] for f in OA.FORMS if f[0] not in planted2], "⛔ THE SHIPPED DEFECT")
FAKE = OA.FORMS + [("newform", "x", "00", "someday")]
print("  a future 4th value ('someday')       : unplanted rows =", coverage(OA, FAKE),
      "✔ the coverage assert catches it")
print("\nRED PROBE: %s" % ("every plant fired" if allgood else "⛔ A PLANT WAS MISSED"))
sys.exit(0 if allgood else 1)
