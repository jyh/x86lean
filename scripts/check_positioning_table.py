#!/usr/bin/env python3
"""Gate the G1 positioning table's PROVENANCE MARKERS and its OWED count.

WHY THIS EXISTS.  `docs/TACAS-G1-POSITIONING.md` is built on one rule: every cell
comparing x86lean against another x86 semantics is MEASURED, RECORDED, or OWED,
and **no cell is estimated**.  A positioning table is the one place a referee can
check our claims about someone else's system against the source and we cannot, so
an unmarked cell there is the most expensive kind of unmarked cell in the campaign.

The rule was PROSE, and prose does not refuse.  On 2026-09-11 the file's own §2
said "Five OWED cells" and named seven, while the table carried FIFTEEN.  The
mechanism was not carelessness: §1b filled four cells and wrote the fills into
**§1b's narrative**, leaving the TABLE's cells reading OWED; §2 was then kept in
step with §1b rather than with the table.  Three registers, one of them
load-bearing, and the debt list tracked the wrong one.

  ==> A FILL WRITTEN INTO PROSE DOES NOT REACH THE TABLE.
  ==> AND EVERY ERROR RAN THE SAME WAY: UNDER-REPORTING THE DEBT.  A
      hand-maintained list of what is missing decays toward "less is missing".

WHAT THIS DOES, in two arms.

  ARM 1 (markers).  Every data cell of every non-exempt row must carry at least
  one marker from the declared vocabulary.  A cell with none is a FINDING: it is
  a claim about another project with no provenance, which is exactly the thing
  the file promises it does not contain.

  ARM 2 (the count).  The file declares `OWED-CELLS-NOW: <n>` once.  This script
  derives the count from the TABLE and refuses if they disagree.  The declared
  literal and the table are two sources; their agreement is the gate.  Nothing
  here is derived from the prose that the literal lives in.

EXEMPTIONS ARE DECLARED AND PRINTED, NEVER SILENT.  The `role here` row says what
each system is TO US ("primary differential oracle"), not what it IS; it makes no
claim about another project and carries no marker by design.  A tool has no
concept of "not applicable", so the rule is supplied here and the tool prints
what it excluded on every run.

LANE.  Personal lane.  Reads one file in this repository and nothing else.
"""
import argparse, re, sys, pathlib

DOC = pathlib.Path(__file__).resolve().parent.parent / "docs" / "TACAS-G1-POSITIONING.md"
COLUMNS = ["x86lean", "x86isa", "K", "Sail"]

# The declared marker vocabulary.  A cell must carry at least one of these.
MARKERS = ("MEASURED", "RECORDED", "OWED")

# Declared exemptions: row label -> why.  Printed on every run.
EXEMPT_ROWS = {
    "role here": "says what each system is TO US, not what it IS; makes no claim about another project",
}

DECL_RE = re.compile(r"^\s*OWED-CELLS-NOW:\s*(\d+)\s*$", re.M)


def table_rows(text):
    """Yield (row_label, [cell, ...]) for each data row of the §1 table."""
    for line in text.split("\n"):
        if not line.startswith("| **") or line.count("|") < 5:
            continue
        cells = [c.strip() for c in line.strip().strip("|").split("|")]
        label = re.sub(r"\*", "", cells[0]).strip()
        yield label, cells[1:5]


def scan(text):
    owed, unmarked, exempted = [], [], []
    for label, cells in table_rows(text):
        if label in EXEMPT_ROWS:
            exempted.append(label)
            continue
        for col, cell in zip(COLUMNS, cells):
            if "OWED" in cell:
                owed.append((col, label))
            if not any(m in cell for m in MARKERS):
                unmarked.append((col, label, cell[:60]))
    return owed, unmarked, exempted


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--count", action="store_true", help="print the derived OWED count and exit 0")
    ap.add_argument("--selftest", action="store_true", help="drive both arms with planted defects")
    ap.add_argument("--doc", default=str(DOC))
    a = ap.parse_args(argv)

    if a.selftest:
        return selftest()

    text = pathlib.Path(a.doc).read_text(encoding="utf-8")
    owed, unmarked, exempted = scan(text)

    if a.count:
        print(len(owed))
        return 0

    print(f"positioning table: {a.doc}")
    for r in exempted:
        print(f"  EXCLUDED row '{r}' -- {EXEMPT_ROWS[r]}")
    print(f"  derived OWED cells: {len(owed)}")
    for col, label in owed:
        print(f"    OWED  {col:8s} {label}")

    rc = 0
    if unmarked:
        rc = 1
        print(f"\n  FINDING: {len(unmarked)} cell(s) carry no {'/'.join(MARKERS)} marker:")
        for col, label, snippet in unmarked:
            print(f"    UNMARKED  {col:8s} {label}: {snippet!r}")

    m = DECL_RE.search(text)
    if not m:
        print("\n  FINDING: no 'OWED-CELLS-NOW: <n>' declaration in the document")
        return 1
    declared = int(m.group(1))
    if declared != len(owed):
        print(f"\n  FINDING: declared OWED-CELLS-NOW: {declared} but the TABLE carries {len(owed)}")
        return 1
    print(f"  declared OWED-CELLS-NOW: {declared} == table: {len(owed)}  ok")
    return rc


# --------------------------------------------------------------------------
# THE SELFTEST DRIVES BOTH DIRECTIONS.  A gate that has only been watched
# passing has been probed for noise and not for silence: an arm that cannot
# fire is indistinguishable from an arm that found nothing.
# --------------------------------------------------------------------------
def selftest():
    import tempfile, os
    base = DOC.read_text(encoding="utf-8")
    arms, red = [], 0

    def run(name, text, expect_rc, expect_sub=None):
        nonlocal red
        with tempfile.NamedTemporaryFile("w", suffix=".md", delete=False, encoding="utf-8") as fh:
            fh.write(text); path = fh.name
        import io, contextlib
        buf = io.StringIO()
        with contextlib.redirect_stdout(buf):
            rc = main(["--doc", path])
        os.unlink(path)
        out = buf.getvalue()
        ok = (rc == expect_rc) and (expect_sub is None or expect_sub in out)
        arms.append((name, ok, rc, expect_rc))
        if not ok:
            red += 1
            print(f"  x {name}: rc={rc} expected {expect_rc}; output:\n{out}")
        else:
            print(f"  v {name}: rc={rc}")
        return rc

    print("check_positioning_table --selftest")

    # ---- CONTROL FIRST.  A broken harness reds every plant, and a plant probe
    # whose control has not run tells you nothing about the plants.
    run("control: the real document passes", base, 0, "ok")

    # ---- ARM 1: an unmarked cell is caught.
    marked = "| **decode** |"
    i = base.index(marked)
    j = base.index("\n", i)
    row = base[i:j]
    cells = row.strip().strip("|").split("|")
    # cells[0] is the row label, so cells[1] is the x86lean column.  WHICH column
    # is immaterial to this arm -- what it proves is that a cell carrying no
    # marker is caught wherever it sits.
    cells[1] = " a thing, roughly "                # provenance marker stripped
    plant1 = base[:i] + "|" + "|".join(cells) + "|" + base[j:]
    run("PLANT 1: a cell with no marker is a FINDING", plant1, 1, "UNMARKED")

    # ---- ARM 2: a declared count that disagrees with the table is caught,
    # in BOTH directions -- over-declared and under-declared.
    plant2 = base.replace("OWED-CELLS-NOW: 0", "OWED-CELLS-NOW: 3", 1)
    run("PLANT 2a: over-declared count is a FINDING", plant2, 1, "but the TABLE carries")

    # under-declared: put a real OWED back in the table, leave the literal at 0
    k = base.index("| **decode** |")
    l = base.index("\n", k)
    row2 = base[k:l]
    c2 = row2.strip().strip("|").split("|")
    c2[2] = " **OWED** "   # cells[0]=label, so this is the x86isa column
    plant3 = base[:k] + "|" + "|".join(c2) + "|" + base[l:]
    run("PLANT 2b: under-declared count is a FINDING", plant3, 1, "but the TABLE carries")

    # ---- ARM 3: a missing declaration is a FINDING, not a silent pass.
    plant4 = base.replace("OWED-CELLS-NOW: 0", "OWED-CELLS: nil", 1)
    run("PLANT 3: a missing declaration is a FINDING", plant4, 1, "no 'OWED-CELLS-NOW")

    # ---- ARM 4: the EXEMPTION is real -- the exempt row is unmarked in the
    # live document, so if the exemption were dropped the control would red.
    # Prove the exemption is load-bearing rather than decorative.
    saved = EXEMPT_ROWS.copy()
    EXEMPT_ROWS.clear()
    run("PLANT 4: without the declared exemption the real doc REDS "
        "(the exemption is load-bearing, not decorative)", base, 1, "UNMARKED")
    EXEMPT_ROWS.update(saved)

    print(f"\n  arms={len(arms)} red={red}")
    return 1 if red else 0


if __name__ == "__main__":
    sys.exit(main())
