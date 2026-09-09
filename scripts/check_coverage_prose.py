#!/usr/bin/env python3
"""THE PER-BATCH NARRATIVE IN docs/COVERAGE.md, GATED.

WHY THIS EXISTS.  `docs/COVERAGE.md` is GENERATED, and the generator carries two
hand-maintained claims side by side: the count ("N of the 525 forms") and the
per-batch sentence ("1 — ...; 2 — ...").  The count has a comment beside it in
`Main.lean` stating the counting rule and an `awk` line that checks it, and it
survived thirteen batches intact.  The sentence had neither.

⛔ P1 BATCH 14 FOUND IT A WHOLE BATCH STALE: it stopped at "12 — the near-free
four" while the count already read 396, which includes batch 13.  Batch 13
updated the number and not the prose, every gate stayed green, and the published
coverage document described a model one batch older than the one it tabulated.
⇒ A COLUMN — OR A SENTENCE — NO GATE READS IS WRONG WHEREVER NOBODY LOOKED.

⭐⭐ P2 ITEM 1 (BATCH 22) WIDENED THE GLOB FROM `P1` TO `P<p>`.  Read literally,
this gate would have gone on reporting "CLEAN — all 21 P1 batches" for ever
while naming not one P2 batch: its subject was named by a LITERAL, so renaming
the work made the work invisible and the gate answered about the part it could
still see.  That is not silence, it is a positive report of agreement about a
region nobody observed ([[unobserved-regions-report-agreement]]).

THE ANCHOR, AND WHY IT CANNOT DRIFT IN STEP.  The batches are counted from
`docs/DIFFERENTIAL-P<p>-BATCH<n>.md`: one file per batch, written for a different
purpose (the differential run's record) by a different step of the work.  A gate
whose two sides are maintained by the same edit is a gate that agrees with
itself; these two are not.

WHAT THIS DOES NOT CHECK: that the sentence for batch N describes batch N
correctly.  It checks that a marker for every batch is PRESENT.  The limit is
stated rather than left for a reader to find.
"""
import os, re, sys, glob

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

root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
os.chdir(root)

found = {}
for f in glob.glob("docs/DIFFERENTIAL-P*-BATCH*.md"):
    mm = re.search(r'DIFFERENTIAL-P(\d+)-BATCH(\d+)\.md$', f)
    if mm:
        found.setdefault(int(mm.group(1)), set()).add(int(mm.group(2)))
if not found:
    print("⛔ no docs/DIFFERENTIAL-P<p>-BATCH<n>.md files found. A gate that cannot "
          "find its anchor reports a pass; this one reports a failure.")
    sys.exit(2)

doc = open("docs/COVERAGE.md").read()
total_expected = 0
for phase in sorted(found):
    expected = list(range(1, max(found[phase]) + 1))
    missing_files = [n for n in expected if n not in found[phase]]
    if missing_files:
        print(f"⛔ P{phase} batch record(s) missing from docs/: {missing_files}")
        sys.exit(1)
    m = re.search(rf'P{phase} has added, by batch:(.*?)\n', doc, re.S)
    if not m:
        print(f"⛔ could not find the per-batch narrative for P{phase} in "
              f"docs/COVERAGE.md. A missing subject is not a pass.")
        sys.exit(2)
    narrative = m.group(1)
    missing = [n for n in expected if not re.search(rf'(?:^|[;:])\s*{n} —', narrative)]
    if missing:
        print(f"⛔ docs/COVERAGE.md's P{phase} per-batch narrative is STALE: no "
              f"entry for batch(es) {missing}, but "
              f"docs/DIFFERENTIAL-P{phase}-BATCH<N>.md exists for each. Update "
              f"the sentence in Main.lean and regenerate.")
        sys.exit(1)
    total_expected += len(expected)

n_records = sum(len(v) for v in found.values())
print(f"coverage-prose gate: CLEAN — the narratives name all {total_expected} "
      f"batches across {len(found)} phase(s), matching the {n_records} "
      f"differential records in docs/")
