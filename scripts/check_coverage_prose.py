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

THE ANCHOR, AND WHY IT CANNOT DRIFT IN STEP.  The batches are counted from
`docs/DIFFERENTIAL-P1-BATCH<N>.md`: one file per batch, written for a different
purpose (the differential run's record) by a different step of the work.  A gate
whose two sides are maintained by the same edit is a gate that agrees with
itself; these two are not.

WHAT THIS DOES NOT CHECK: that the sentence for batch N describes batch N
correctly.  It checks that a marker for every batch is PRESENT.  The limit is
stated rather than left for a reader to find.
"""
import os, re, sys, glob

root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
os.chdir(root)

batches = sorted(int(re.search(r'BATCH(\d+)\.md$', f).group(1))
                 for f in glob.glob("docs/DIFFERENTIAL-P1-BATCH*.md"))
if not batches:
    print("⛔ no docs/DIFFERENTIAL-P1-BATCH<N>.md files found. A gate that cannot "
          "find its anchor reports a pass; this one reports a failure.")
    sys.exit(2)

expected = list(range(1, max(batches) + 1))
missing_files = [n for n in expected if n not in batches]
if missing_files:
    print(f"⛔ batch record(s) missing from docs/: {missing_files}")
    sys.exit(1)

doc = open("docs/COVERAGE.md").read()
m = re.search(r'P1 has added, by batch:(.*?)\n', doc, re.S)
if not m:
    print("⛔ could not find the per-batch narrative in docs/COVERAGE.md. "
          "A missing subject is not a pass.")
    sys.exit(2)
narrative = m.group(1)

missing = [n for n in expected if not re.search(rf'(?:^|[;:])\s*{n} —', narrative)]
if missing:
    print(f"⛔ docs/COVERAGE.md's per-batch narrative is STALE: no entry for "
          f"batch(es) {missing}, but docs/DIFFERENTIAL-P1-BATCH<N>.md exists for "
          f"each. Update the sentence in Main.lean and regenerate.")
    sys.exit(1)

print(f"coverage-prose gate: CLEAN — the narrative names all {len(expected)} "
      f"P1 batches, matching the {len(batches)} differential records in docs/")
