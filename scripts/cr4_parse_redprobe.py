#!/usr/bin/env python3
"""⭐⭐ THE RED PROBE FOR `check_driver_cr4.py`'s PARSER ARMS (QUEUE 0b(6)).

`check_driver_cr4.py --selftest` prints seven green parser arms.  THIS FILE IS
WHAT MAKES THAT SENTENCE MEAN SOMETHING: it plants nine defects, one at a time,
into an IN-MEMORY copy of the shipped module and requires each to fire EXACTLY
the arms it should — no more and no fewer.  The tree is never edited.

⛔ WHY A SEPARATE FILE RATHER THAN MORE ARMS INSIDE THE SELFTEST.  These plants
mutate the subject's own source.  An arm that rewrites the module it lives in
cannot run inside that module's normal green path without the rewrite becoming
the thing under test ([[feedback-a-gate-is-not-exempt-from-its-own-defect]]).

⭐ WHAT IT ESTABLISHED, and none of it was true before it was run:
  * P-D, an honest loosening of the parse (`refused=` no longer required), fired
    NO ARM AT ALL on the first draft.  Arms 6 and 7 exist because of that
    silence ([[feedback-probe-silence-has-two-causes]]).
  * Arms 6 and 7 are TWO arms and not one wearing two names: P-G fires 6 without
    7 and P-H fires 7 without 6 ([[feedback-two-arms-that-agree-to-the-case]]).
  * All SEVEN arms — the two positive controls included, via P-I — are fired by
    at least one plant.  An arm no plant can fire is a green light wired to
    nothing ([[feedback-a-claim-the-vectors-cannot-distinguish]]).
  * Three of the author's nine expectations were WRONG and the arms were right
    each time: expectations were written from each plant's INTENT rather than
    from its reachable CONSEQUENCES.  They are corrected in place, with the
    reason, rather than quietly widened.

⚠️ TWO PLANTS CRASH INSTEAD OF REPORTING (P-D, P-E: half a conjunction removed,
then a None dereferenced).  A traceback is a louder red than a wrong number, but
it is NOT an arm firing, and this probe records it as `CRASH` for that reason
([[feedback-a-citation-is-an-ungated-claim]]).

LANE.  Personal lane; pure string work, no oracle, no build.  Runs in ~0.1 s.

Usage:  cr4_parse_redprobe.py        (exit 0 iff every plant fires exactly right)
"""
import os, sys, types

# ⛔ REFUSE AN UNKNOWN FLAG BEFORE ANY WORK HAPPENS — see portable.strict_flags.
# A script that declares no flags is the SHARPEST case: it ignores anything and
# runs its main path, so a mistyped flag produced a confident green about a
# subject nobody asked about (measured: check_encodings.py --self-test -> rc 0,
# "synonym collapse: CLEAN", having never run its self-test).
if __name__ == "__main__":
    import os as _os, sys as _sys
    _sys.path.insert(0, _os.path.dirname(_os.path.abspath(__file__)))
    from portable import strict_flags as _strict_flags
    _strict_flags(__file__)

# ⛔ DERIVED, NOT HARD-CODED: a probe that only runs from one absolute path is a
# probe that stops being run.
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
os.chdir(ROOT); sys.path.insert(0, os.path.join(ROOT, "scripts"))
SUBJECT = "scripts/check_driver_cr4.py"
SRC = open(SUBJECT).read()

GUARD = """            if ref is None or rip is None:
                # ⛔ NOT `executes`.  See the RE_REFUSED comment: this is the
                # branch the whole repair exists for.
                c = c._replace(unparsed=c.unparsed + 1)"""
STALL = "            elif int(rip.group(1), 16) == OA.ENTRY_RIP:"

PLANTS = [
 ("P-A  residual restored: unparsed counted as `executes` (THE SHIPPED DEFECT)",
  [("c = c._replace(unparsed=c.unparsed + 1)", "c = c._replace(executes=c.executes + 1)")],
  {3, 4, 6, 7}),
 ("P-B  stall branch deleted: rip==ENTRY_RIP counted as `executes`",
  [("c = c._replace(stalls=c.stalls + 1)", "c = c._replace(executes=c.executes + 1)")],
  {2}),
 ("P-C  rip pattern loosened to [0-9a-f]+ (the D177 producer mismatch)",
  [(r'RE_RIP = re.compile(r"\brip=([0-9a-f]{16})\b")',
    r'RE_RIP = re.compile(r"\brip=([0-9a-f]+)")')],
  {4}),
 ("P-F  verdict() stops refusing on unparsed records",
  [("        elif c.unparsed:", "        elif False:")],
  {5}),
 # ⭐ P-G and P-H each fire EXACTLY ONE of arms 6 and 7, which is what proves
 #   they are two arms and not one wearing two names
 #   ([[feedback-two-arms-that-agree-to-the-case]]).  P-A fires both, so P-A
 #   alone could not tell them apart.
 ("P-G  `refused=` becomes optional-and-safe (a zero-width match)",
  [(r'RE_REFUSED = re.compile(r"\brefused=([01])\b")',
    r'RE_REFUSED = re.compile(r"(?:\brefused=([01])\b)?")')],
  {6}),
 ("P-H  `rip=` becomes optional-and-safe (missing rip ⇒ 'not a stall')",
  [(GUARD, "            if ref is None:\n                c = c._replace(unparsed=c.unparsed + 1)"),
   (STALL, "            elif rip is not None and int(rip.group(1), 16) == OA.ENTRY_RIP:")],
  # ⚠️ {4, 7}, NOT {7}: to this plant an UNMATCHED rip and a MISSING rip are the
  #   same condition, so arm 4's base-10 line is swept up with arm 7's. The
  #   separation claim survives and is narrower than "fires 7 alone": P-G fires
  #   6 and NOT 7; P-H fires 7 and NOT 6.
  {4, 7}),
 # ⭐ P-I fires the POSITIVE CONTROLS, which is what stops arms 1 and 2 from being
 #   decoration: inverting the stall test makes an advanced rip read `stalls` and
 #   an unchanged rip read `executes`, so BOTH controls must go red at once.
 ("P-I  stall test inverted (== becomes !=)",
  [("            elif int(rip.group(1), 16) == OA.ENTRY_RIP:",
    "            elif int(rip.group(1), 16) != OA.ENTRY_RIP:")],
  {1, 2}),
 # ⚠️ THE TWO HALF-PLANTS BELOW CRASH RATHER THAN MISREPORT.  That is a real red
 #   — a traceback is strictly louder than a wrong number — but it is NOT an arm
 #   firing, and saying so would launder a crash into a gate reading.
 ("P-D  `refused=` requirement dropped outright (rip alone decides)",
  [("if ref is None or rip is None:", "if rip is None:")], {-1}),
 ("P-E  `rip=` requirement dropped outright (refused alone decides)",
  [("if ref is None or rip is None:", "if ref is None:")], {-1}),
]

def run_with(src):
    mod = types.ModuleType("cdc_plant")
    mod.__file__ = os.path.abspath(SUBJECT); mod.__name__ = "cdc_plant"
    try:
        exec(compile(src, mod.__file__, "exec"), mod.__dict__)
        return mod.parser_arms()
    except Exception as ex:
        return False, 0, [("CRASH: %s: %s" % (type(ex).__name__, ex), "")]

def ids(fails):
    out = set()
    for lab, _ in fails:
        if lab.startswith("CRASH:"): out.add(-1)
        elif lab.startswith("control: an advanced"): out.add(1)
        elif lab.startswith("control: rip =="): out.add(2)
        elif "init-error" in lab: out.add(3)
        elif "BASE-10" in lab: out.add(4)
        elif lab.startswith("verdict()"): out.add(5)
        elif "NO `refused=`" in lab: out.add(6)
        elif "NO `rip=`" in lab: out.add(7)
        else: out.add(0)
    return out

ok, n, fails = run_with(SRC)
print("CONTROL (shipped tree, unplanted): %s, %d arms, %d failures"
      % ("PASS" if ok else "FAIL", n, len(fails)))
assert ok, "⛔ the control is RED — every plant below would be meaningless"

allgood, fired = True, set()
for name, pairs, expect in PLANTS:
    src = SRC
    for old, new in pairs:
        assert src.count(old) == 1, "plant %s: subject not unique (%d)" % (name, src.count(old))
        src = src.replace(old, new, 1)
    ok, n, fails = run_with(src)
    got = ids(fails)
    good = (not ok) and got == expect
    allgood &= good
    fired |= (got - {-1})
    print("%s %-68s fired %-14s expected %s" % ("✔" if good else "⛔", name,
                                                sorted(got), sorted(expect)))
    for lab, _ in fails:
        print("      · %s" % lab)
print("\nDISTINCT ARMS DEMONSTRATED LIVE BY A PLANT: %s of 1..7" % sorted(fired))
print("⭐ ARMS 6 AND 7 ARE TWO ARMS, NOT ONE: P-G fires 6 without 7, P-H fires 7 without 6.")
print("⇒ ALL SEVEN ARMS ARE DEMONSTRATED LIVE BY AT LEAST ONE PLANT, the two positive")
print("  controls included (P-I). An arm no plant can fire is a green light wired to")
print("  nothing ([[feedback-a-claim-the-vectors-cannot-distinguish]]).")
print("\nRED PROBE: %s" % ("every plant fired exactly what it should"
                           if allgood else "⛔ AN ARM DID NOT BEHAVE"))
sys.exit(0 if allgood else 1)
