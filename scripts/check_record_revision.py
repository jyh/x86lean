#!/usr/bin/env python3
"""Refuse a differential record that does not name the reference model's pinned revision.

WHY (D218, D219).  No differential record written before 2026-09-12 names the ACL2 / x86isa commit it
ran against, so every agreement figure in them is agreement with an unnamed model.  The revision is now
pinned (`scripts/oracle_revision.txt`) and `run_differential.sh` prints `reference-model: acl2@<sha>`.
A record is still written by hand from that output, so the line can be left out; this refuses that.

THE RULE.  Every `docs/DIFFERENTIAL-*.md` and `docs/REFERENCE-PIN-RUN-*.md` must carry at least one
`reference-model: acl2@<40 hex>` line, and every such line must equal the pin — EXCEPT the records that
PREDATE THE PIN, which are listed below by explicit bounds rather than by a default, so a new record can
never fall into the exemption by accident.  An exempt record that does carry the line is still checked.
Each listed exempt record must exist, so the list cannot rot silently.

Exit 0 clean; 1 on a finding; 2 when it cannot find its subject.  `--selftest` plants each failure.
"""
import argparse, glob, os, re, sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
LINE = re.compile(r"reference-model:\s+acl2@([0-9a-f]{40})\b")
LOOSE = re.compile(r"reference-model:")

# The records that predate the pin (D218). Bounds, not a pattern: P0, P1 batches 1-21, P2 batches 1-22.
PREDATES_PIN = (["DIFFERENTIAL-P0.md"]
                + [f"DIFFERENTIAL-P1-BATCH{n}.md" for n in range(1, 22)]
                + [f"DIFFERENTIAL-P2-BATCH{n}.md" for n in range(1, 23)])


def pin(root=ROOT):
    path = os.path.join(root, "scripts", "oracle_revision.txt")
    vals = [l.strip() for l in open(path, encoding="utf-8") if l.strip() and not l.strip().startswith("#")]
    return vals[0] if vals and re.fullmatch(r"[0-9a-f]{40}", vals[0]) else None


def check(records, want, exempt=PREDATES_PIN):
    """records: {basename: text}. Returns findings."""
    f = []
    if not want:
        return ["scripts/oracle_revision.txt carries no 40-hex pin -- nothing to check records against"]
    if not records:
        return ["no differential records found -- a gate with no subject refuses"]
    for name in exempt:
        if name not in records:
            f.append(f"exempt record {name} does not exist -- the predates-the-pin list has rotted")
    for name, text in sorted(records.items()):
        shas = LINE.findall(text)
        if not shas:
            if name in exempt:
                continue
            hint = " (a `reference-model:` line is present but malformed)" if LOOSE.search(text) else ""
            f.append(f"{name}: names no reference-model revision{hint}; quote run_differential.sh's "
                     f"`reference-model: acl2@<sha>` line")
            continue
        bad = sorted({s for s in shas if s != want})
        if bad:
            f.append(f"{name}: reference-model acl2@{bad[0]} is not the pin acl2@{want}")
    return f


def load(root=ROOT):
    paths = glob.glob(os.path.join(root, "docs", "DIFFERENTIAL-*.md")) + \
            glob.glob(os.path.join(root, "docs", "REFERENCE-PIN-RUN-*.md"))
    return {os.path.basename(p): open(p, encoding="utf-8").read() for p in paths}


def selftest():
    red = 0

    def arm(name, ok, detail=""):
        nonlocal red
        print(("  v " if ok else "  x ") + name + ("" if ok else f"   {detail}"))
        red += 0 if ok else 1

    real, want = load(), pin()
    f = check(real, want)
    arm("control: the real records pass", not f, str(f)[:200])
    arm("control: at least one record carries the line (the rule has a live subject)",
        any(LINE.search(t) for t in real.values()))
    plant = dict(real, **{"DIFFERENTIAL-P2-BATCH23.md": "cases=1 matched=1\n"})
    f = check(plant, want)
    arm("PLANT: a NEW batch record without the line is refused, naming it",
        any("DIFFERENTIAL-P2-BATCH23.md" in x and "names no" in x for x in f), str(f)[:200])
    other = "0" * 39 + "1"
    plant = dict(real, **{"DIFFERENTIAL-P2-BATCH23.md": f"reference-model: acl2@{other}\n"})
    f = check(plant, want)
    arm("PLANT: a record at ANOTHER revision is refused, naming both",
        any(other in x and want in x for x in f), str(f)[:200])
    plant = dict(real, **{"DIFFERENTIAL-P2-BATCH23.md": "reference-model: acl2@c8897a34\n"})
    f = check(plant, want)
    arm("PLANT: a short or malformed line is refused as malformed, not accepted",
        any("malformed" in x for x in f), str(f)[:200])
    plant = {k: v for k, v in real.items() if k != "DIFFERENTIAL-P1-BATCH7.md"}
    f = check(plant, want)
    arm("PLANT: an exempt record that vanished is refused (the list cannot rot)",
        any("DIFFERENTIAL-P1-BATCH7.md" in x and "rotted" in x for x in f), str(f)[:200])
    plant = dict(real, **{"DIFFERENTIAL-P1-BATCH7.md": real["DIFFERENTIAL-P1-BATCH7.md"]
                          + f"\nreference-model: acl2@{other}\n"})
    f = check(plant, want)
    arm("PLANT: an EXEMPT record that carries a wrong line is still refused",
        any("DIFFERENTIAL-P1-BATCH7.md" in x and other in x for x in f), str(f)[:200])
    arm("PLANT: an empty record set refuses", bool(check({}, want)))
    print(f"\n  red={red}")
    return 1 if red else 0


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--selftest", action="store_true")
    a = ap.parse_args(argv)
    if a.selftest:
        return selftest()
    want = pin()
    recs = load()
    if not want or not recs:
        for x in check(recs, want):
            print("⛔ check_record_revision: " + x)
        return 2
    f = check(recs, want)
    if f:
        print(f"⛔ check_record_revision: FAIL — {len(f)} finding(s)")
        for x in f:
            print("   " + x)
        return 1
    named = sum(1 for t in recs.values() if LINE.search(t))
    print(f"check_record_revision: CLEAN — {named} record(s) name acl2@{want[:8]}; "
          f"{len(PREDATES_PIN)} predate the pin and are exempt by explicit bounds")
    return 0


if __name__ == "__main__":
    sys.exit(main())
